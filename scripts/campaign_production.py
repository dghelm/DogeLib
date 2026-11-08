"""Replay a saved signed-spend failure through Core's production path.

Design record 0009, section 9.1, defines the levels:

- L1 sends the stored requests unchanged to a harness build. The harness calls
  `VerifyScript` and `SignatureHash`, the production functions.
- L3 rebuilds the case on an isolated regtest node. The node needs real
  previous outputs, so the replay funds them, signs the spend again with the
  same plan, and submits it to the mempool and in a block.

Section 9.2 labels each result with the Core commit of its builds. Section 9.4
keeps every request and response in the uncommitted saved failure: this module
prints labels only.

All Core citations refer to commit e0a1c157791544e818c901bd9341896965afbf9d.
"""

import base64
import copy
import hashlib
import http.client
import json
import os
import pathlib
import re
import secrets
import socket
import struct
import subprocess
import tempfile
import time

import campaign
from campaign_generator import materialize, mutated, scripts, signing_requests, transaction
from campaign_reduce import stored_plan
from oracle_script import push

# D14, chainparams.cpp, CRegTestParams: BIP66Height 1251 and BIP65Height 1351.
# AuxPoW blocks start at height 20, and legacy blocks end there.
LEGACY_BLOCKS = 19
FUNDED_HEIGHT = 1352
# D36, validation.cpp, ConnectBlock, lines 1892 to 1917: P2SH always, DERSIG from
# BIP66Height, CHECKLOCKTIMEVERIFY from BIP65Height. CHECKSEQUENCEVERIFY needs
# the BIP9 deployment, which is not active at these heights, and
# IsWitnessEnabled returns false, so neither WITNESS nor NULLDUMMY applies.
BLOCK_FLAGS = 1 | 4 | 512
# Commitment-mode mutations that replace an outpoint by one that no regtest
# output can match.
UNFUNDABLE = ('own_outpoint', 'other_outpoint', 'input_count')
# At the pin, the functional test framework uses ports 11000 to 20999
# (qa/rpc-tests/test_framework/util.py, lines 36 to 105), and the default RPC
# ports are 22555, 44555 and 18332 (D39, src/chainparamsbase.cpp). The node's P2P
# port is its RPC port plus 100, and the node does not listen on it.
RPC_PORTS = range(24440, 24480)

# D99, script/script_error.cpp, ScriptErrorString, lines 12 to 90, mapped to
# the names of harness/core/script_error_names.inc.
SCRIPT_ERROR_TEXT = {
    'No error': 'OK',
    'Script evaluated without error but finished with a false/empty top stack element': 'EVAL_FALSE',
    'Script failed an OP_VERIFY operation': 'VERIFY',
    'Script failed an OP_EQUALVERIFY operation': 'EQUALVERIFY',
    'Script failed an OP_CHECKMULTISIGVERIFY operation': 'CHECKMULTISIGVERIFY',
    'Script failed an OP_CHECKSIGVERIFY operation': 'CHECKSIGVERIFY',
    'Script failed an OP_NUMEQUALVERIFY operation': 'NUMEQUALVERIFY',
    'Script is too big': 'SCRIPT_SIZE',
    'Push value size limit exceeded': 'PUSH_SIZE',
    'Operation limit exceeded': 'OP_COUNT',
    'Stack size limit exceeded': 'STACK_SIZE',
    'Signature count negative or greater than pubkey count': 'SIG_COUNT',
    'Pubkey count negative or limit exceeded': 'PUBKEY_COUNT',
    'Opcode missing or not understood': 'BAD_OPCODE',
    'Attempted to use a disabled opcode': 'DISABLED_OPCODE',
    'Operation not valid with the current stack size': 'INVALID_STACK_OPERATION',
    'Operation not valid with the current altstack size': 'INVALID_ALTSTACK_OPERATION',
    'OP_RETURN was encountered': 'OP_RETURN',
    'Invalid OP_IF construction': 'UNBALANCED_CONDITIONAL',
    'Negative locktime': 'NEGATIVE_LOCKTIME',
    'Locktime requirement not satisfied': 'UNSATISFIED_LOCKTIME',
    'Signature hash type missing or not understood': 'SIG_HASHTYPE',
    'Non-canonical DER signature': 'SIG_DER',
    'Data push larger than necessary': 'MINIMALDATA',
    'Only non-push operators allowed in signatures': 'SIG_PUSHONLY',
    'Non-canonical signature: S value is unnecessarily high': 'SIG_HIGH_S',
    'Dummy CHECKMULTISIG argument must be zero': 'SIG_NULLDUMMY',
    'OP_IF/NOTIF argument must be minimal': 'MINIMALIF',
    'Signature must be zero for failed CHECK(MULTI)SIG operation': 'NULLFAIL',
    'NOPx reserved for soft-fork upgrades': 'DISCOURAGE_UPGRADABLE_NOPS',
    'Witness version reserved for soft-fork upgrades': 'DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM',
    'Public key is neither compressed or uncompressed': 'PUBKEYTYPE',
    'Witness program has incorrect length': 'WITNESS_PROGRAM_WRONG_LENGTH',
    'Witness program was passed an empty witness': 'WITNESS_PROGRAM_WITNESS_EMPTY',
    'Witness program hash mismatch': 'WITNESS_PROGRAM_MISMATCH',
    'Witness requires empty scriptSig': 'WITNESS_MALLEATED',
    'Witness requires only-redeemscript scriptSig': 'WITNESS_MALLEATED_P2SH',
    'Witness provided for non-witness script': 'WITNESS_UNEXPECTED',
    'Using non-compressed keys in segwit': 'WITNESS_PUBKEYTYPE',
    'unknown error': 'UNKNOWN_ERROR',
}
# D97, validation.cpp, CheckInputs, lines 1503 and 1512.
SCRIPT_REJECTION = re.compile(r'(non-mandatory-script-verify-flag|mandatory-script-verify-flag-failed) \((.*)\)$')


def sha256d(raw):
    """Double SHA-256 in internal byte order."""
    return hashlib.sha256(hashlib.sha256(raw).digest()).digest()


def build_identity(program, stamp, revision):
    """Require a build stamp that names `revision` on its first line, and keep the program's hash."""
    program = pathlib.Path(program).resolve()
    stamp = pathlib.Path(stamp)
    if not stamp.is_file():
        raise ValueError(f'{program} has no build stamp {stamp.name}: production replay needs a real build')
    text = stamp.read_text()
    first = text.splitlines()[0].split() if text else []
    if len(first) != 2 or first[0] not in ('pin', 'revision'):
        raise ValueError(f'{stamp} does not name a Core commit')
    if revision is not None and first[1] != revision:
        raise ValueError(f'{stamp} names {first[1]}, not --revision {revision}')
    return dict(revision=first[1], program=str(program), stamp=text,
                sha256=hashlib.sha256(program.read_bytes()).hexdigest())


def harness_identity(harness, revision):
    """Identify an unchanged harness build and check its own --version label."""
    identity = build_identity(harness, pathlib.Path(harness).resolve().parent / 'core.stamp', revision)
    capture = {}
    try:
        version = json.loads(campaign.run_captured(harness, ['--version'], '', 10, capture))
    except campaign.RunError as error:
        raise ValueError(f'{harness} --version failed: {error}') from error
    if version.get('core_revision', campaign.PIN) != identity['revision']:
        raise ValueError(f'{harness} --version names another Core commit')
    identity['version'] = version
    return identity


def target_revision(args, identity):
    """Check the label of section 9.2: the pin is e0a1c15, and upstream is any named commit."""
    if args.target == 'pin' and identity['revision'] != campaign.PIN:
        raise ValueError(f"--target pin needs a build at {campaign.PIN}, not {identity['revision']}")
    return identity['revision']


def saved_case(record):
    """Accept one generated signed-spend case with its stored plan and expectation."""
    plan = stored_plan(record)
    if record['plan']['mode'] != 'generated' or record['failing_side'] == 'signer':
        raise ValueError('production replay needs a saved failure of one generated signed-spend case')
    return plan, record['plan']['inputs'][0]['expected']


def replay_l1(record, args):
    """L1: the stored requests, unchanged, through a labelled harness build."""
    identity = harness_identity(args.harness, args.revision)
    revision = target_revision(args, identity)
    runs, results = campaign.resend(record, args.oracle, args.harness)
    matching = [r for _, r in results if (r[0], r[1]) == (record['class'], record['failing_side'])]
    spend = runs['core'].get('responses', [{}])[-1].get('ok') if 'error' not in runs['core'] else None
    return dict(level='L1', target=args.target, revision=revision, harness=identity,
                responses=runs, results=[list(r) for _, r in results], core_spend=spend,
                outcome='reproduced' if matching else 'not-reproduced')


class RPCError(ValueError):
    """A JSON-RPC error from the node, such as a rejected transaction."""

    def __init__(self, error):
        self.error = error
        super().__init__(f"node RPC error {error.get('code')}: {error.get('message')}")


class Node:
    """An isolated regtest dogecoind that stops on every exit path.

    The data directory is new and temporary. The node binds RPC to 127.0.0.1 on
    the first free port of RPC_PORTS, and it neither listens nor connects to
    peers.
    """

    def __init__(self, binary, directory, mempool_flags, timeout):
        self.binary, self.directory, self.timeout = str(binary), pathlib.Path(directory), timeout
        self.mempool_flags = mempool_flags
        self.user, self.password = 'replay', secrets.token_hex(24)
        self.process = self.port = self.log = None

    def rpc(self, method, *params):
        """Call one method and return its result, or raise RPCError."""
        auth = base64.b64encode(f'{self.user}:{self.password}'.encode()).decode()
        connection = http.client.HTTPConnection('127.0.0.1', self.port, timeout=self.timeout)
        try:
            connection.request('POST', '/', json.dumps(dict(id=1, method=method, params=list(params))),
                               {'Authorization': 'Basic ' + auth, 'Content-Type': 'application/json'})
            payload = json.loads(connection.getresponse().read())
        finally:
            connection.close()
        if payload.get('error'):
            raise RPCError(payload['error'])
        return payload['result']

    def __enter__(self):
        for port in RPC_PORTS:
            with socket.socket() as probe:
                try:
                    probe.bind(('127.0.0.1', port))
                except OSError:
                    continue
            self.port = port
            break
        if self.port is None:
            raise OSError(f'no free RPC port in {RPC_PORTS.start}..{RPC_PORTS.stop - 1}')
        config = self.directory / 'dogecoin.conf'
        config.write_text(f'rpcuser={self.user}\nrpcpassword={self.password}\n')
        config.chmod(0o600)
        self.log = (self.directory / 'stdout.log').open('w')
        # D97: on regtest, RequireStandard() is false (D14), so
        # -promiscuousmempoolflags sets the script flags of AcceptToMemoryPool.
        arguments = [self.binary, '-regtest', '-server', '-datadir=' + str(self.directory),
                     '-listen=0', '-connect=0', '-dnsseed=0', '-discover=0', '-printtoconsole=0', '-par=1',
                     '-rpcbind=127.0.0.1', '-rpcallowip=127.0.0.1', f'-rpcport={self.port}',
                     f'-port={self.port + 100}', f'-promiscuousmempoolflags={self.mempool_flags}']
        try:
            self.process = subprocess.Popen(arguments, stdout=self.log, stderr=subprocess.STDOUT,
                                            stdin=subprocess.DEVNULL)
            deadline = time.monotonic() + self.timeout
            while True:
                if self.process.poll() is not None:
                    raise OSError(f'regtest node exited during startup with status {self.process.returncode}')
                try:
                    self.rpc('getblockcount')
                    return self
                except (OSError, RPCError, http.client.HTTPException):
                    if time.monotonic() > deadline:
                        raise OSError('regtest node did not answer RPC before the timeout')
                    time.sleep(0.2)
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def __exit__(self, *_):
        if self.process is not None and self.process.poll() is None:
            try:
                self.rpc('stop')
            except (OSError, ValueError, http.client.HTTPException):
                self.process.terminate()
            try:
                self.process.wait(timeout=30)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        if self.log is not None:
            self.log.close()

    def debug_log(self, limit=65536):
        """The end of the node's debug.log."""
        path = self.directory / 'regtest' / 'debug.log'
        return path.read_bytes()[-limit:].decode(errors='replace') if path.exists() else ''


def l3_plan(plan):
    """The plan that L3 funds and signs, and the changes that a node needs.

    In preserve mode the signer signs the mutated transaction, so the
    flattened plan with its mutations applied is the same case. In commitment
    mode the signatures cover the unmutated transaction, so the mutations must
    stay, and none of them may name an outpoint that no output can match.

    CheckTransaction rejects a transaction without outputs (D90, validation.cpp,
    line 533). The reducer removes every output that a property does not need,
    so L3 then adds one zero-value OP_TRUE output and records the change. The caller compares the
    property, verdict, error and digest relation of the changed case with the
    saved ones before it compares verdicts.
    """
    if plan['mode'] == 'preserve':
        result = mutated(plan)
        result['mutations'] = []
    else:
        unfundable = sorted({m['field'] for m in plan['mutations'] if m['field'] in UNFUNDABLE})
        if unfundable:
            raise ValueError(f"L3 cannot fund commitment-mode mutations of {', '.join(unfundable)}")
        result = copy.deepcopy(plan)
    changes = []
    if not mutated(result)['tx']['outputs']:
        result['tx']['outputs'].append(dict(value=0, script='51'))
        changes.append('added one zero-value OP_TRUE output, because CheckTransaction rejects a transaction without outputs')
    return result, changes


def fund(node, plan):
    """Mine to the BIP65 height, then confirm one output for each input of the plan.

    Input n gets the P2SH output of the spend's redeem script. Every other
    input gets a bare OP_TRUE output, which its stored scriptSig satisfies.
    The amounts do not enter a legacy signature hash.

    D95: decodescript gives the P2SH address of OP_TRUE, and sendrawtransaction
    reports a rejection as "<code>: <reason>". D96: generatetoaddress mines
    legacy blocks with auxpow 0 and AuxPoW blocks with auxpow 1.
    """
    anyone = node.rpc('decodescript', '51')['p2sh']
    node.rpc('generatetoaddress', LEGACY_BLOCKS, anyone, 1000000, 0)
    node.rpc('generatetoaddress', FUNDED_HEIGHT - LEGACY_BLOCKS, anyone, 1000000, 1)
    coinbase = node.rpc('getblock', node.rpc('getblockhash', 1))['tx'][0]
    available = round(node.rpc('gettxout', coinbase, 0)['value'] * 100000000)
    _, spk = scripts(mutated(plan))
    count = len(plan['tx']['inputs'])
    paid = sum(o['value'] for o in mutated(plan)['tx']['outputs'])
    each = max(10 ** 9, -(-(paid + 10 ** 8) // count))
    if each * count + 10 ** 8 > available:
        raise ValueError('the regtest coinbase does not cover the outputs of the plan')
    funding = dict(n=0, tx=dict(version=1, lock_time=0,
                                inputs=[dict(outpoint=bytes.fromhex(coinbase)[::-1].hex() + '00000000',
                                             sequence=0xffffffff)],
                                outputs=[dict(value=each, script=spk if i == plan['n'] else '51')
                                         for i in range(count)]))
    raw = transaction(funding, push(b'\x51'))
    txid = node.rpc('sendrawtransaction', raw, True)
    node.rpc('generatetoaddress', 1, anyone, 1000000, 1)
    if node.rpc('gettxout', txid, 0)['confirmations'] < 1:
        raise ValueError('the funding transaction did not confirm')
    rebased = copy.deepcopy(plan)
    outpoints = []
    for i, item in enumerate(rebased['tx']['inputs']):
        outpoints.append(dict(original=item['outpoint'], funded=bytes.fromhex(txid)[::-1].hex() + struct.pack('<I', i).hex()))
        item['outpoint'] = outpoints[-1]['funded']
    return rebased, dict(height=node.rpc('getblockcount'), funding_tx=raw, funding_txid=txid,
                         amount_each=each, outpoints=outpoints)


def candidate_block(node, spend_hex):
    """An AuxPoW block with a zero-value coinbase and the spend, for submitblock (D96).

    D55, auxpow.cpp, CAuxPow::initAuxPow, lines 209 to 245, builds the same
    parent: one coinbase whose input script pushes the block hash, 1 and seven
    zero bytes, with empty Merkle branches. The parent's scrypt hash must meet
    the block's target. Core checks every block and transaction rule itself.
    """
    tip = node.rpc('getblock', node.rpc('getbestblockhash'))
    height = tip['height'] + 1
    # Regtest DigiShield retargets every block with a timespan of one second
    # and clamps the change to a factor of one (D14, and D6, src/dogecoin.cpp,
    # CalculateDogecoinNextWorkRequired), so the next block keeps the tip's bits.
    bits = int(tip['bits'], 16)
    # Later than the median time past, and well before the two-hour future limit.
    stamp = max(tip['time'], int(time.time())) + 3
    coinbase = dict(n=0, tx=dict(version=1, lock_time=0,
                                 inputs=[dict(outpoint='00' * 32 + 'ffffffff', sequence=0xffffffff)],
                                 outputs=[dict(value=0, script='51')]))
    height_bytes = height.to_bytes((height.bit_length() + 7) // 8, 'little')
    coinbase_raw = bytes.fromhex(transaction(coinbase, push(height_bytes)))
    spend = bytes.fromhex(spend_hex)
    merkle = sha256d(sha256d(coinbase_raw) + sha256d(spend))
    # Version 4 with chain ID 0x62 and the AuxPoW flag 0x100 (D14, nAuxpowChainId).
    header = (struct.pack('<I', 0x620104) + bytes.fromhex(tip['hash'])[::-1] + merkle +
              struct.pack('<III', stamp, bits, 0))
    parent_coinbase = copy.deepcopy(coinbase)
    parent_coinbase['tx']['outputs'] = []
    parent_raw = bytes.fromhex(transaction(parent_coinbase, push(sha256d(header)[::-1] + b'\x01' + bytes(7))))
    prefix = struct.pack('<I', 1) + bytes(32) + sha256d(parent_raw) + struct.pack('<II', 0, 0)
    target = (bits & 0x7fffff) << (8 * ((bits >> 24) - 3))
    for nonce in range(1 << 20):
        parent = prefix + struct.pack('<I', nonce)
        if int.from_bytes(hashlib.scrypt(parent, salt=parent, n=1024, r=1, p=1, dklen=32), 'little') <= target:
            break
    else:
        raise ValueError('no parent nonce met the regtest target')
    auxpow = parent_raw + bytes(32) + b'\x00' + bytes(4) + b'\x00' + bytes(4) + parent
    return (header + auxpow + b'\x02' + coinbase_raw + spend).hex(), sha256d(header)[::-1].hex()


def node_result(reason):
    """Map a node's rejection to a Script verdict, or mark it as not comparable."""
    if reason is None:
        return dict(result='accepted')
    match = SCRIPT_REJECTION.search(reason)
    if match:
        return dict(result='rejected', script_error=SCRIPT_ERROR_TEXT.get(match[2], 'UNMAPPED'),
                    nonmandatory=match[1] == 'non-mandatory-script-verify-flag', reason=reason)
    return dict(result='not-comparable', reason=reason)


def agrees(result, expected):
    """The node's Script verdict satisfies the expected verdict of the property."""
    if result['result'] != expected['verdict']:
        return False
    return result['result'] == 'accepted' or 'script_error' not in expected or \
        result['script_error'] == expected['script_error']


def outcome(mempool, saved, rebuilt):
    """Compare the node's mempool verdict, under the plan's flags, with the saved expectation.

    The rebuilt case must keep the saved property, verdict, error and digest
    relation. Otherwise the regtest spend is a different case, and its verdict
    says nothing about the candidate.
    """
    same_case = all(rebuilt.get(k) == saved.get(k) for k in ('property', 'verdict', 'script_error', 'relation'))
    if not same_case or mempool['result'] == 'not-comparable':
        return 'not-comparable'
    return 'not-reproduced' if agrees(mempool, saved) else 'reproduced'


def run_l3(plan, expected, programs, timeout):
    """Fund, re-sign and submit one plan on an isolated regtest node.

    `programs` holds the oracle, the harness, the signer and dogecoind. The
    mempool checks the spend with the plan's own flags. A block then checks it
    with the consensus flags of its height, BLOCK_FLAGS.
    """
    plan, changes = l3_plan(plan)
    base = campaign.ROOT / 'build/campaign'
    base.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='regtest-', dir=base) as directory:
        with Node(programs['node'], directory, plan['flags'], timeout) as regtest:
            rebased, funding = fund(regtest, plan)
            requests = signing_requests(rebased, 'production-0')
            signed = campaign.execute_signer(programs['signer'], requests, timeout)
            if 'error' in signed or any('ok' not in r for r in signed['responses']):
                raise ValueError('the signer failed or refused a funded signing request')
            entries = [dict(request=r, response=s) for r, s in zip(requests, signed['responses'])]
            case = materialize(rebased, 'production-0', entries)
            # The digest checks of section 5.1, and the harness verdict on the same bytes.
            runs = {side: campaign.execute(programs[side], case['requests'], timeout) for side in ('lean', 'core')}
            property_failures = [list(r) for _, r in campaign.assess_cases([case], runs)]
            spend = case['requests'][-1]['tx_hex']
            try:
                mempool = dict(txid=regtest.rpc('sendrawtransaction', spend, True), **node_result(None))
            except RPCError as error:
                mempool = dict(error=error.error, **node_result(error.error.get('message', '')))
            block_hex, block_hash = candidate_block(regtest, spend)
            reason = regtest.rpc('submitblock', block_hex)
            accepted = reason is None and regtest.rpc('getbestblockhash') == block_hash
            block = dict(block_hash=block_hash, flags=BLOCK_FLAGS, submitblock=reason,
                         **node_result(None if accepted else reason or 'not connected'))
            chain = regtest.rpc('getblockchaininfo')
            log = regtest.debug_log()
    harness_spend = runs['core'].get('responses', [{}])[-1].get('ok') if 'error' not in runs['core'] else None
    return dict(plan=rebased, changes=changes, funding=funding, signer=entries, requests=case['requests'],
                expected=case['expected'], responses=runs, property_failures=property_failures,
                harness_spend=harness_spend, mempool_flags=plan['flags'], mempool=mempool, block=block,
                policy_only=mempool['result'] == 'rejected' and block['result'] == 'accepted',
                chain=dict(height=chain.get('blocks'), softforks=chain.get('softforks'),
                           bip9_softforks=chain.get('bip9_softforks')),
                node_log_tail=log, seconds=round(time.monotonic() - started, 2),
                outcome=outcome(mempool, expected, case['expected']))


def replay_l3(record, args, timeout):
    """L3: the saved case, re-signed on regtest by labelled builds of one Core commit."""
    if not args.signer or not args.node:
        raise ValueError('--level L3 needs --signer and --node')
    harness = harness_identity(args.harness, args.revision)
    revision = target_revision(args, harness)
    node_dir = pathlib.Path(args.node).resolve()
    node = build_identity(node_dir / 'core/src/dogecoind', node_dir / 'node.stamp', revision)
    signer = build_identity(args.signer, pathlib.Path(args.signer).resolve().parent / 'core.stamp', revision)
    plan, expected = saved_case(record)
    evidence = run_l3(plan, expected, dict(lean=args.oracle, core=args.harness, signer=args.signer,
                                           node=node['program']), timeout)
    return dict(level='L3', target=args.target, revision=revision, harness=harness, node=node,
                signer_build=signer, **evidence)


def classification(record):
    """Summarize the production evidence by level, target and commit.

    `reproduced`: some replay reproduced the candidate on a production path.
    `harness-fault`: a verdict or digest failure on the Core side that the
    unchanged harness at the pin does not reproduce at L1, and, for a verdict,
    that the node at the pin does not reproduce at L3 either.
    `undetermined`: any other combination, such as a missing level.
    """
    evidence = record['production']['replays']
    rows = [dict(level=e['level'], target=e['target'], revision=e['revision'], outcome=e['outcome'])
            for e in evidence]
    pin = {r['level']: r['outcome'] for r in rows if r['target'] == 'pin'}
    core_side = record['failing_side'] in ('core', 'both', 'undetermined')
    if any(r['outcome'] == 'reproduced' for r in rows):
        label = 'reproduced'
    elif (core_side and record['class'] in ('verdict', 'digest') and pin.get('L1') == 'not-reproduced' and
          (record['class'] == 'digest' or pin.get('L3') == 'not-reproduced')):
        label = 'harness-fault'
    else:
        label = 'undetermined'
    return dict(label=label, replays=rows)


def replay(args):
    """Append one production replay to an uncommitted saved failure, and print labels only."""
    path = pathlib.Path(args.failure).resolve()
    if not path.is_relative_to(campaign.ROOT / 'build/campaign'):
        raise ValueError("production evidence stays under this worktree's build/campaign/ (design record 0009, section 9.4)")
    record = json.loads(path.read_text())
    if record.get('format') != campaign.FORMAT:
        raise ValueError('unsupported saved-failure format')
    if args.revision is not None and not re.fullmatch(r'[0-9a-f]{40}', args.revision):
        raise ValueError('--revision must be a full lowercase commit hash')
    saved_case(record)
    if args.level == 'L1':
        evidence = replay_l1(record, args)
    else:
        evidence = replay_l3(record, args, max(record['timeout'], 60))
    evidence['recorded'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    production = record.setdefault('production', dict(replays=[]))
    production['replays'].append(evidence)
    production['classification'] = classification(record)
    # Replace the file only after a complete replay, so that an interruption keeps it intact.
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    os.replace(temporary, path)
    summary = dict(level=evidence['level'], target=evidence['target'], revision=evidence['revision'],
                   outcome=evidence['outcome'], classification=production['classification']['label'])
    if evidence['level'] == 'L3':
        summary.update(mempool=evidence['mempool']['result'], block=evidence['block']['result'],
                       policy_only=evidence['policy_only'])
    print(json.dumps(summary))
    return 0 if evidence['outcome'] == 'reproduced' else 1
