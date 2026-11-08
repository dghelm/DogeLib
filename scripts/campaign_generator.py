"""Construct the signed recovery family from plans and a hand-derived field table."""

import copy
import hashlib
import json
import pathlib
import random

from oracle_script import push

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFINED = (1, 129, 2, 130, 3, 131)
HASH_TYPES = (*DEFINED, 0, 4, 33, 132, 255)
LOCK_TIMES = (0, 999999, 1000000, 1000001, 499999999, 500000000, 0xffffffff)
SEQUENCES = (0, 0xfffffffe, 0xffffffff)
TRUE = ('01', '02', '81')
FALSE = ('', '00', '80', '0000')
ONE = '01' + '00' * 31

# Design record 0009 §6.3, derived by hand from pinned interpreter.cpp
# 1054–1143 and 1225–1246 (D3). Columns: ALL, ALL|ACP, NONE,
# NONE|ACP, SINGLE, SINGLE|ACP. No implementation supplies this data.
# ACP serializes only input n (1097–1098, 1131). SINGLE serializes n+1
# outputs and null outputs before n (1117–1123, 1136). Output counts under
# SINGLE are open only while both counts exceed n. The fixed digest is excluded.
FIELDS = {
    'version':       (1, 1, 1, 1, 1, 1),
    'lock_time':     (1, 1, 1, 1, 1, 1),
    'own_outpoint':  (1, 1, 1, 1, 1, 1),
    'own_sequence':  (1, 1, 1, 1, 1, 1),
    'script_code':   (1, 1, 1, 1, 1, 1),
    'hash_type':     (1, 1, 1, 1, 1, 1),
    'script_sig':    (0, 0, 0, 0, 0, 0),
    'other_outpoint':(1, 0, 1, 0, 1, 0),
    'other_sequence':(1, 0, 0, 0, 0, 0),
    'input_count':   (1, 0, 1, 0, 1, 0),
    'position':      (1, 0, 1, 0, 1, 1),
    'own_output':    (1, 1, 0, 0, 1, 1),
    'other_output':  (1, 1, 0, 0, 0, 0),
    'output_count':  (1, 1, 0, 0, 0, 0),
}


def column(hash_type):
    """Classify undefined bytes as ALL unless their low five bits are 2 or 3."""
    base = hash_type & 31
    return (2 if base == 2 else 4 if base == 3 else 0) + bool(hash_type & 128)


def compact(n):
    """Encode the bounded counts used by the generator."""
    return bytes([n]) if n < 253 else b'\xfd' + n.to_bytes(2, 'little')


def transaction(plan, unlocking=b''):
    """Serialize a base transaction with the plan's exact fields."""
    tx = plan['tx']
    data = tx['version'].to_bytes(4, 'little') + compact(len(tx['inputs']))
    for i, item in enumerate(tx['inputs']):
        script = unlocking if i == plan['n'] else bytes.fromhex(item['script_sig'])
        data += (bytes.fromhex(item['outpoint']) + compact(len(script)) + script +
                 item['sequence'].to_bytes(4, 'little'))
    data += compact(len(tx['outputs']))
    for item in tx['outputs']:
        script = bytes.fromhex(item['script'])
        data += item['value'].to_bytes(8, 'little') + compact(len(script)) + script
    return (data + tx['lock_time'].to_bytes(4, 'little')).hex()


def base_plan(rng):
    """Draw a plan independently of all program responses."""
    count = rng.randint(1, 4)
    branch = rng.choice(('ordinary', 'recovery'))
    h = rng.choice(HASH_TYPES)
    flags = rng.choice((1, 3, 5, 9, 17, 513, 1025, 1567))
    if h not in DEFINED:
        flags &= ~2
    return dict(mode='preserve', branch=branch, n=rng.randrange(count),
                key_ids=rng.choice(([1, 2], [1, 3], [2, 3])) if branch == 'ordinary' else [4],
                hash_types=[h, h] if branch == 'ordinary' else [h], flags=flags,
                selector=rng.choice(TRUE if branch == 'ordinary' else FALSE),
                signature_mutation='none', mutations=[],
                tx=dict(version=rng.choice((1, 2)), lock_time=rng.choice(LOCK_TIMES),
                        inputs=[dict(outpoint=rng.randbytes(36).hex(), sequence=rng.choice(SEQUENCES),
                                     script_sig='') for _ in range(count)],
                        outputs=[dict(value=rng.randrange(100000001), script='51')
                                 for _ in range(rng.randrange(6))]))


def accepted(plan):
    """Keep CLTV and encodings inside the ordinary acceptance domain."""
    plan['tx']['lock_time'] = 1000000
    plan['tx']['inputs'][plan['n']]['sequence'] = 0xfffffffe
    plan['flags'] &= ~2 if any(h not in DEFINED for h in plan['hash_types']) else 0xffffffff
    return plan


def plans(seed, count):
    """Enumerate boundaries, then draw seeded plans and table-field mutations."""
    rng = random.Random(seed)
    boundaries = []
    # Each axis is enumerated independently, so no random draw can omit a boundary.
    for h in HASH_TYPES:
        for n in range(4):
            for outputs in range(6):
                boundaries.append(('shape', (h, n, outputs)))
    for branch in ('ordinary', 'recovery'):
        for lock in LOCK_TIMES:
            for seq in SEQUENCES:
                for mode in ('preserve', 'commitment'):
                    boundaries.append(('lock', (branch, lock, seq, mode)))
    for selector in (*TRUE, *FALSE):
        boundaries.append(('selector', selector))
    for flag in (2, 4, 8, 16, 512, 1024):
        for enabled in (False, True):
            boundaries.append(('flag', (flag, enabled)))
    for h in HASH_TYPES:
        for field in FIELDS:
            boundaries.append(('field', (h, field)))
    for mutation in ('high_s', 'hash_byte', 'reverse', 'padding'):
        boundaries.append(('signature', mutation))
    boundaries.append(('unsupported', None))
    rng.shuffle(boundaries)
    for i in range(count):
        p = base_plan(rng)
        kind, value = boundaries[i] if i < len(boundaries) else rng.choice(boundaries)
        if kind == 'shape':
            h, n, outputs = value
            p['n'], p['hash_types'] = n, [h] * len(p['key_ids'])
            p['tx']['inputs'] = [dict(outpoint=rng.randbytes(36).hex(), sequence=rng.choice(SEQUENCES),
                                      script_sig='') for _ in range(max(n + 1, rng.randint(1, 4)))]
            p['tx']['outputs'] = [dict(value=j + 1, script='51') for j in range(outputs)]
            accepted(p)
            p['flags'] |= 2 if h in DEFINED else 0
        elif kind == 'lock':
            branch, lock, seq, mode = value
            p.update(branch=branch, selector='01' if branch == 'ordinary' else '',
                     key_ids=[1, 2] if branch == 'ordinary' else [4], mode=mode,
                     hash_types=[1, 1] if branch == 'ordinary' else [1])
            p['flags'] |= 512
            p['tx']['lock_time'] = lock
            p['tx']['inputs'][p['n']]['sequence'] = seq
            if mode == 'commitment':
                p['mutations'] = [dict(field='version', value=3)]
        elif kind == 'selector':
            p.update(branch='ordinary' if value in TRUE else 'recovery', selector=value)
            p['key_ids'] = [1, 2] if value in TRUE else [4]
            p['hash_types'] = [1] * len(p['key_ids'])
            accepted(p)
        elif kind == 'flag':
            accepted(p)
            flag, enabled = value
            p['hash_types'] = [1] * len(p['key_ids'])
            p['flags'] = (1567 if enabled else 1567 & ~flag)
        elif kind == 'field':
            h, field = value
            p['hash_types'] = [h] * len(p['key_ids'])
            p['n'] = 1
            p['tx']['inputs'] = [dict(outpoint=rng.randbytes(36).hex(), sequence=0xfffffffe,
                                      script_sig='') for _ in range(3)]
            p['tx']['outputs'] = [dict(value=j + 1, script='51') for j in range(3)]
            p['mode'] = 'commitment'
            p['mutations'] = [dict(field=field, value=2)]
            accepted(p)
        elif kind == 'signature':
            accepted(p)
            p.update(branch='ordinary', selector='01', key_ids=[1, 2], hash_types=[1, 1],
                     signature_mutation=value, flags=543)
        elif kind == 'unsupported':
            accepted(p)
            p['flags'] |= 64
        if p['hash_types'][0] not in DEFINED:
            p['flags'] &= ~2
        p['boundary'] = kind
        describe_mutations(p)
        yield p


def mutated(plan):
    """Apply named plan changes without consulting an implementation."""
    p = copy.deepcopy(plan)
    tx, n = p['tx'], p['n']
    for mutation in p['mutations']:
        field, value = mutation['field'], mutation['value']
        other = 0 if n else 1
        if field in ('version', 'lock_time'):
            tx[field] += value if field == 'version' else 1
        elif field in ('own_outpoint', 'other_outpoint'):
            item = tx['inputs'][n if field.startswith('own') else other]
            raw = bytearray.fromhex(item['outpoint'])
            raw[0] ^= 1
            item['outpoint'] = raw.hex()
        elif field in ('own_sequence', 'other_sequence'):
            tx['inputs'][n if field.startswith('own') else other]['sequence'] = value
        elif field in ('own_output', 'other_output'):
            tx['outputs'][n if field.startswith('own') else other]['value'] += value
        elif field == 'input_count':
            tx['inputs'].append(dict(outpoint='ab' * 36, sequence=0, script_sig=''))
        elif field == 'output_count':
            tx['outputs'].append(dict(value=value, script='51'))
        elif field == 'position':
            tx['inputs'][0], tx['inputs'][n] = tx['inputs'][n], tx['inputs'][0]
            p['n'] = 0
        elif field == 'script_sig':
            # Keep input n's unlocking stack, as Q5 requires.
            tx['inputs'][other]['script_sig'] = '51'
        elif field == 'script_code':
            p['code_suffix'] = '61'  # OP_NOP preserves execution.
        elif field == 'hash_type':
            p['hash_types'] = [h ^ 0x20 for h in p['hash_types']]
            p['flags'] &= ~2
        else:
            raise ValueError(f'unknown mutation field: {field}')
    return p


def describe_mutations(plan):
    """Record replacement values beside each operator's construction argument."""
    after = mutated(plan)
    tx, n = after['tx'], after['n']
    other = 0 if n else 1
    for m in plan['mutations']:
        field = m['field']
        if field in ('version', 'lock_time'):
            value = tx[field]
        elif field in ('own_outpoint', 'other_outpoint', 'own_sequence', 'other_sequence'):
            value = tx['inputs'][n if field.startswith('own') else other][field.split('_', 1)[1]]
        elif field in ('own_output', 'other_output'):
            value = tx['outputs'][n if field.startswith('own') else other]
        elif field == 'script_sig':
            value = tx['inputs'][other]['script_sig']
        elif field in ('input_count', 'output_count'):
            value = len(tx['inputs' if field == 'input_count' else 'outputs'])
        elif field == 'position':
            value = n
        elif field == 'hash_type':
            value = after['hash_types']
        else:
            value = scripts(after)[0]
        m['new_value'] = value


def scripts(plan):
    """Use only fixture template bytes, never fixture verdicts or digests."""
    record = json.loads((ROOT / 'tests/script/signed-spends/recovery.jsonl').read_text().splitlines()[0])
    code = bytes.fromhex(record['redeem_script_hex'] + plan.get('code_suffix', ''))
    digest = hashlib.new('ripemd160', hashlib.sha256(code).digest()).digest()
    return code.hex(), (b'\xa9\x14' + digest + b'\x87').hex()


def signing_requests(plan, prefix):
    """Request one digest and signature for each key and hash-type pair."""
    signing = mutated(plan) if plan['mode'] == 'preserve' else plan
    code, _ = scripts(signing)
    return [dict(id=f'{prefix}-sign-{i}', tx_hex=transaction(signing), input_index=signing['n'],
                 script_code_hex=code, hash_type=h, key_ids=[key])
            for i, (key, h) in enumerate(zip(signing['key_ids'], signing['hash_types']))]


def high_s(signature):
    """Replace DER S by n-S while retaining the hash-type byte."""
    order = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
    rsize = signature[3]
    offset = 6 + rsize
    s = order - int.from_bytes(signature[offset:-1], 'big')
    raw = s.to_bytes((s.bit_length() + 7) // 8, 'big')
    raw = (b'\x00' if raw[0] & 128 else b'') + raw
    return (bytes([48, 4 + rsize + len(raw), 2, rsize]) + signature[4:4 + rsize] +
            bytes([2, len(raw)]) + raw + signature[-1:])


def expectation(plan, spend):
    """Derive verdict and digest relations from §4, §6.3 and Q1–Q7."""
    n, tx = spend['n'], spend['tx']
    fixed = all(h & 31 == 3 and n >= len(tx['outputs']) for h in spend['hash_types'])
    early = (tx['lock_time'] < 1000000 or tx['lock_time'] >= 500000000 or
             tx['inputs'][n]['sequence'] == 0xffffffff)
    recovery = spend['branch'] == 'recovery'
    result = dict(property='Q2' if recovery else 'Q1', verdict='accepted', relation=None, known=None)
    if recovery and spend['flags'] & 512 and early:
        result.update(property='Q3', verdict='rejected', script_error='UNSATISFIED_LOCKTIME')
        return result
    if plan['mode'] == 'commitment' and plan['mutations']:
        fields = [m['field'] for m in plan['mutations']]
        committed = any(FIELDS[f][column(h)] for f in fields for h in plan['hash_types'])
        result.update(property='Q4' if committed else 'Q5', relation='changed' if committed else 'equal',
                      verdict='rejected' if committed else 'accepted')
    if fixed:
        result.update(property='Q7', relation='fixed', verdict='accepted', known='single-fixed-digest')
    elif recovery and not spend['flags'] & 512 and early:
        result['known'] = 'recovery-without-cltv'
    mutation = plan['signature_mutation']
    if mutation != 'none':
        result.update(property='Q1-encoding', verdict='rejected', known=None)
        if mutation == 'high_s':
            result['script_error'] = 'SIG_HIGH_S'
        elif mutation == 'padding':
            result['script_error'] = 'SIG_DER'
    return result


def materialize(plan, prefix, signer):
    """Build exact replay requests after independently checked signing digests."""
    spend = mutated(plan)
    signing = mutated(plan) if plan['mode'] == 'preserve' else plan
    code, spk = scripts(spend)
    signatures = [bytes.fromhex(item['response']['ok']['signatures_hex'][0]) for item in signer]
    if any(m['field'] == 'hash_type' for m in plan['mutations']):
        signatures = [sig[:-1] + bytes([h]) for sig, h in zip(signatures, spend['hash_types'])]
    change = plan['signature_mutation']
    if change == 'high_s':
        signatures[0] = high_s(signatures[0])
    elif change == 'hash_byte':
        signatures[0] = signatures[0][:-1] + bytes([signatures[0][-1] ^ 32])
        spend['flags'] &= ~2
    elif change == 'reverse':
        signatures.reverse()
    elif change == 'padding':
        sig = signatures[0]
        signatures[0] = bytes([48, sig[1] + 1, 2, sig[3] + 1, 0]) + sig[4:]
    unlocking = b'\x00' if plan['branch'] == 'ordinary' else b''
    unlocking += b''.join(push(sig) for sig in signatures)
    unlocking += push(bytes.fromhex(plan['selector'])) + push(bytes.fromhex(code))
    requests = []
    for i, (entry, h) in enumerate(zip(signer, spend['hash_types'])):
        req = dict(entry['request'])
        req.pop('key_ids')
        req.update(op='sighash.legacy', id=f'{prefix}-before-{i}')
        requests.append(req)
        requests.append(dict(req, id=f'{prefix}-after-{i}', tx_hex=transaction(spend),
                             input_index=spend['n'], hash_type=h, script_code_hex=code))
    requests.append(dict(op='script.verify_legacy', id=f'{prefix}-spend', tx_hex=transaction(spend, unlocking),
                         input_index=spend['n'], prevout_script_hex=spk, flags=spend['flags'],
                         checker='transaction'))
    return dict(plan=plan, expected=expectation(plan, spend), signer=signer, requests=requests,
                input='generated', source_index=int(prefix.rsplit('-', 1)[-1]))


def property_result(case, runs):
    """Check each side against a property, keeping Q6 agreement separate."""
    expected = case['expected']
    violations = []
    for side, run in runs.items():
        responses = run['responses']
        spend = responses[-1].get('ok', {})
        if spend.get('result') == 'unsupported':
            continue
        kind = None
        for i, entry in enumerate(case['signer']):
            before = responses[2 * i].get('ok', {})
            after = responses[2 * i + 1].get('ok', {})
            if before.get('digest_hex') != entry['response']['ok']['digest_hex']:
                kind = 'digest'
            relation = expected['relation']
            if relation == 'fixed' and any(r.get('plan') != 'fixed_digest' or r.get('digest_hex') != ONE
                                           for r in (before, after)):
                kind = 'digest'
            if relation in ('equal', 'changed'):
                # Mixed types require equality for each open signature. A committed
                # signature changes only when its own table column says so.
                changed = any(FIELDS[m['field']][column(case['plan']['hash_types'][i])]
                              for m in case['plan']['mutations'])
                if (before.get('digest_hex') != after.get('digest_hex')) != changed:
                    kind = 'digest'
                if side == 'lean' and ((before.get('preimage_hex') != after.get('preimage_hex')) != changed):
                    kind = 'digest'
        if kind is None and (spend.get('result') != expected['verdict'] or
                             ('script_error' in expected and spend.get('script_error') != expected['script_error'])):
            kind = 'verdict'
        if kind:
            violations.append((side, kind))
    if violations:
        sides = 'both' if len(violations) == 2 else violations[0][0]
        return violations[0][1], sides, f"{expected['property']} property violation", expected['property']
    return None
