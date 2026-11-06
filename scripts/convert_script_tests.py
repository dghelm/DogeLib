#!/usr/bin/env python3
"""Normalize the pinned Core script corpus without Script execution.

Assembly and fixture interpretation adapt Dogecoin Core at
e0a1c157791544e818c901bd9341896965afbf9d:
src/core_read.cpp (ParseScript), src/script/script.cpp (GetOpName),
src/script/script.h (CScript pushes), src/test/script_tests.cpp and
src/test/transaction_tests.cpp (flags and per-input expectations),
src/primitives/transaction.h (UnserializeTransaction), src/serialize.h
(ReadCompactSize), src/validation.cpp (CheckTransaction), src/amount.h
and src/consensus/consensus.h (limits).
Adaptation: pure Python conversion, source locations, context bytes,
per-input records and conservative classification without Script execution.
Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2011-2016 The Bitcoin Core developers
Copyright (c) 2021-2022 The Dogecoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Copyright (c) 2018-2022 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
The licence text is in LICENSES/dogecoin-core-MIT.txt.
"""

import argparse
from collections import Counter
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / 'tests/script/corpus'
PIN = 'e0a1c157791544e818c901bd9341896965afbf9d'
# GetOpName exposes these names for consecutive opcodes 0x61 through 0xb9.
NAMES = '''NOP VER IF NOTIF VERIF VERNOTIF ELSE ENDIF VERIFY RETURN
TOALTSTACK FROMALTSTACK 2DROP 2DUP 3DUP 2OVER 2ROT 2SWAP IFDUP DEPTH
DROP DUP NIP OVER PICK ROLL ROT SWAP TUCK CAT SUBSTR LEFT RIGHT SIZE
INVERT AND OR XOR EQUAL EQUALVERIFY RESERVED1 RESERVED2 1ADD 1SUB 2MUL
2DIV NEGATE ABS NOT 0NOTEQUAL ADD SUB MUL DIV MOD LSHIFT RSHIFT BOOLAND
BOOLOR NUMEQUAL NUMEQUALVERIFY NUMNOTEQUAL LESSTHAN GREATERTHAN
LESSTHANOREQUAL GREATERTHANOREQUAL MIN MAX WITHIN RIPEMD160 SHA1 SHA256
HASH160 HASH256 CODESEPARATOR CHECKSIG CHECKSIGVERIFY CHECKMULTISIG
CHECKMULTISIGVERIFY NOP1 CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY NOP4
NOP5 NOP6 NOP7 NOP8 NOP9 NOP10'''.split()
OPCODES = {name: i + 0x61 for i, name in enumerate(NAMES)}
OPCODES['RESERVED'] = 0x50
OPCODES.update({'OP_' + name: value for name, value in list(OPCODES.items())})
FLAG_NAMES = '''P2SH STRICTENC DERSIG LOW_S NULLDUMMY SIGPUSHONLY
MINIMALDATA DISCOURAGE_UPGRADABLE_NOPS CLEANSTACK CHECKLOCKTIMEVERIFY
CHECKSEQUENCEVERIFY WITNESS DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM
MINIMALIF NULLFAIL WITNESS_PUBKEYTYPE'''.split()
FLAGS = {name: 1 << i for i, name in enumerate(FLAG_NAMES)}
FLAGS['NONE'] = 0
APPROVED = set('P2SH STRICTENC DERSIG LOW_S NULLDUMMY CHECKLOCKTIMEVERIFY CHECKSEQUENCEVERIFY'.split())
ERRORS = set('''OK UNKNOWN_ERROR EVAL_FALSE OP_RETURN SCRIPT_SIZE PUSH_SIZE
OP_COUNT STACK_SIZE SIG_COUNT PUBKEY_COUNT VERIFY EQUALVERIFY
CHECKMULTISIGVERIFY CHECKSIGVERIFY NUMEQUALVERIFY BAD_OPCODE DISABLED_OPCODE
INVALID_STACK_OPERATION INVALID_ALTSTACK_OPERATION UNBALANCED_CONDITIONAL
NEGATIVE_LOCKTIME UNSATISFIED_LOCKTIME SIG_HASHTYPE SIG_DER MINIMALDATA
SIG_PUSHONLY SIG_HIGH_S SIG_NULLDUMMY PUBKEYTYPE CLEANSTACK MINIMALIF NULLFAIL
DISCOURAGE_UPGRADABLE_NOPS DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM
WITNESS_PROGRAM_WRONG_LENGTH WITNESS_PROGRAM_WITNESS_EMPTY
WITNESS_PROGRAM_MISMATCH WITNESS_MALLEATED WITNESS_MALLEATED_P2SH
WITNESS_UNEXPECTED WITNESS_PUBKEYTYPE'''.split())


def push(data):
    """Encode CScript's vector insertion, without small-integer substitution."""
    n = len(data)
    if n < 76:
        prefix = bytes([n])
    elif n <= 255:
        prefix = b'\x4c' + bytes([n])
    elif n <= 65535:
        prefix = b'\x4d' + n.to_bytes(2, 'little')
    else:
        prefix = b'\x4e' + n.to_bytes(4, 'little')
    return prefix + data


def number(n):
    """Encode CScript's int64 insertion with small-integer opcodes."""
    if n == -1 or 1 <= n <= 16:
        return bytes([n + 0x50])
    magnitude = abs(n)
    data = bytearray()
    while magnitude:
        data.append(magnitude & 255)
        magnitude >>= 8
    if data and data[-1] & 128:
        data.append(128 if n < 0 else 0)
    elif data and n < 0:
        data[-1] |= 128
    return push(bytes(data))


def assemble(text):
    """Follow ParseScript tokenization and names at the pinned revision."""
    result = bytearray()
    for token in re.split('[ \t\n]+', text):
        if not token:
            continue
        if re.fullmatch(r'-?[0-9]*', token):
            # atoi64 uses strtoll: '-' gives zero, overflow saturates int64.
            n = int(token) if token != '-' else 0
            n = max(-(1 << 63), min((1 << 63) - 1, n))
            if n == -(1 << 63):
                raise ValueError('INT64_MIN invokes undefined negation in Core')
            result.extend(number(n))
        elif re.fullmatch('0x(?:[0-9a-fA-F]{2})+', token):
            result.extend(bytes.fromhex(token[2:]))
        elif len(token) >= 2 and token[0] == token[-1] == "'":
            result.extend(push(token[1:-1].encode('utf-8')))
        elif token in OPCODES:
            result.append(OPCODES[token])
        else:
            raise ValueError(f'script parse error: {token!r}')
    return bytes(result)


def parse_flags(text):
    """Return the flag mask with the runner's comma-separated syntax."""
    mask = 0
    for name in text.split(',') if text else []:
        mask |= FLAGS[name]
    return mask


def flag_set(mask):
    return sorted(name for name, bit in FLAGS.items() if bit & mask)


def source_records(text):
    """Read top-level JSON values with their one-based opening line."""
    if not isinstance(json.loads(text, parse_float=Decimal), list):
        raise ValueError('expected a top-level JSON array')
    decoder = json.JSONDecoder(parse_float=Decimal)
    pos = re.match(r'\s*\[', text).end()
    while True:
        pos = re.compile(r'\s*').match(text, pos).end()
        if text[pos] == ']':
            if text[pos + 1:].strip():
                raise ValueError('trailing JSON data')
            return
        start = pos
        record, pos = decoder.raw_decode(text, pos)
        yield text.count('\n', 0, start) + 1, record
        pos = re.compile(r'\s*').match(text, pos).end()
        if text[pos] == ',':
            pos += 1
        elif text[pos] != ']':
            raise ValueError('missing record separator')


def opcodes(script):
    """Scan instruction bytes only, and stop at the first truncated push."""
    pos = 0
    while pos < len(script):
        opcode = script[pos]
        pos += 1
        yield opcode
        size = opcode if opcode < 76 else 0
        if 76 <= opcode <= 78:
            width = 1 << (opcode - 76)
            if pos + width > len(script):
                return
            size = int.from_bytes(script[pos:pos + width], 'little')
            pos += width
        if pos + size > len(script):
            return
        pos += size


def classify(sig, pub, flags, witness):
    """Estimate the earliest cumulative stage without executing Script."""
    reasons = ['flag:' + name for name in flag_set(flags) if name not in APPROVED]
    if witness:
        reasons.append('nonempty_witness')
    if reasons:
        return {'milestone': 'outside', 'reasons': reasons, 'estimated_stage': None,
                'stage_features': []}
    ops = set(opcodes(sig)) | set(opcodes(pub))
    features = []
    if ops & {0xac, 0xad, 0xae, 0xaf}:
        features.append('signatures')
    if flags & FLAGS['P2SH'] and len(pub) == 23 and pub[:2] == b'\xa9\x14' and pub[-1] == 0x87:
        features.append('p2sh')
    for opcode, name in ((0xb1, 'CHECKLOCKTIMEVERIFY'), (0xb2, 'CHECKSEQUENCEVERIFY')):
        if opcode in ops and flags & FLAGS[name]:
            features.append(name)
    stage = 4 if any(x != 'signatures' for x in features) else 3 if features else 2
    return {'milestone': 'inside', 'reasons': [], 'estimated_stage': stage,
            'stage_features': features}


def compact(n):
    if n < 253:
        return bytes([n])
    for tag, width in ((253, 2), (254, 4), (255, 8)):
        if n < 1 << (width * 8):
            return bytes([tag]) + n.to_bytes(width, 'little')
    raise ValueError('CompactSize overflow')


def context(sig, pub, amount):
    """Build the runner's base transactions for int-representable amounts."""
    if not 0 <= amount < (1 << 31):
        raise ValueError('credit amount exceeds the portable Core int domain')
    value = amount.to_bytes(8, 'little', signed=True)
    prefix = b'\x01\x00\x00\x00\x01'
    sequence = b'\xff' * 4
    credit = (prefix + bytes(32) + sequence + b'\x02\x00\x00' + sequence +
              b'\x01' + value + compact(len(pub)) + pub + bytes(4))
    txid = hashlib.sha256(hashlib.sha256(credit).digest()).digest()
    spend = (prefix + txid + bytes(4) + compact(len(sig)) + sig + sequence +
             b'\x01' + value + b'\x00' + bytes(4))
    return {'crediting_tx_base_hex': credit.hex(), 'spending_tx_base_hex': spend.hex(),
            'input_index': 0, 'amount_satoshis': amount}


def convert(text):
    records = []
    for index, (line, row) in enumerate(source_records(text)):
        if not isinstance(row, list):
            raise ValueError(f'non-array at line {line}')
        if len(row) == 1 and isinstance(row[0], str):
            continue
        offset = int(bool(row) and isinstance(row[0], list))
        if len(row) not in (4 + offset, 5 + offset) or not all(isinstance(x, str) for x in row[offset:]):
            raise ValueError(f'bad record at line {line}')
        witness = []
        amount = 0
        if offset:
            witness = [bytes.fromhex(item).hex() for item in row[0][:-1]]
            if not row[0] or any(not isinstance(item, str) or not re.fullmatch(r'(?:[0-9a-fA-F]{2})*', item) for item in row[0][:-1]):
                raise ValueError(f'bad witness at line {line}')
            coins = Decimal(row[0][-1]) * 100000000
            if coins != coins.to_integral_value() or not 0 <= coins <= 10000000000 * 100000000:
                raise ValueError(f'bad amount at line {line}')
            amount = int(coins)
        sig, pub = map(assemble, row[offset:offset + 2])
        original = parse_flags(row[offset + 2])
        effective = original
        if original & FLAGS['CLEANSTACK']:
            effective |= FLAGS['P2SH'] | FLAGS['WITNESS']
        error = row[offset + 3]
        if error not in ERRORS:
            raise ValueError(f'unknown ScriptError at line {line}: {error}')
        records.append({'source_index': index, 'source_line': line,
                        'scriptSig_hex': sig.hex(), 'scriptPubKey_hex': pub.hex(),
                        'flags': flag_set(original), 'flags_mask': original,
                        'effective_flags': flag_set(effective), 'effective_flags_mask': effective,
                        'expected_error': error, 'comment': row[offset + 4] if len(row) > offset + 4 else '',
                        'witness': witness, 'witness_context_present': bool(offset),
                        'context': context(sig, pub, amount),
                        'classification': classify(sig, pub, effective, witness)})
    return records


# Limits at the pin: amount.h:18,32 and consensus/consensus.h:17.
MAX_MONEY = 10000000000 * 100000000
MAX_BLOCK_BASE_SIZE = 1000000
RUNNER = 'src/test/transaction_tests.cpp'


def read_transaction(tx_hex):
    """Read a witness-allowed prefix as UnserializeTransaction does at the pin.

    This independent Python adaptation only extracts corpus context.
    It does not call DogeLib or execute Script.
    """
    if not re.fullmatch(r'(?:[0-9a-fA-F]{2})*', tx_hex):
        raise ValueError('bad transaction hex')
    data = bytes.fromhex(tx_hex)
    pos = 0

    def take(n):
        nonlocal pos
        if pos + n > len(data):
            raise ValueError('truncated transaction')
        result = data[pos:pos + n]
        pos += n
        return result

    def size():
        tag = take(1)[0]
        if tag < 253:
            return tag
        width = 1 << (tag - 252)
        n = int.from_bytes(take(width), 'little')
        if n < {253: 253, 254: 65536, 255: 4294967296}[tag]:
            raise ValueError('noncanonical CompactSize')
        if n > 0x02000000:
            raise ValueError('CompactSize above MAX_SIZE')
        return n

    def blob():
        return take(size())

    def inputs():
        result = []
        for _ in range(size()):
            txid = take(32)[::-1].hex()
            n = int.from_bytes(take(4), 'little')
            sig = blob()
            take(4)  # nSequence does not affect the classification.
            result.append({'prevout_txid': txid, 'prevout_n': n,
                           'scriptSig_hex': sig.hex(), 'witness': []})
        return result

    take(4)  # nVersion is preserved in tx_hex.
    vin = inputs()
    flags = take(1)[0] if not vin else 0
    body_start = pos if not vin else 4
    if flags:
        vin = inputs()
    vout = []
    if vin or flags:
        for _ in range(size()):
            amount = int.from_bytes(take(8), 'little', signed=True)
            vout.append((amount, blob()))
    body_end = pos
    if flags & 1:
        for txin in vin:
            txin['witness'] = [blob().hex() for _ in range(size())]
    if flags & ~1:
        raise ValueError('unknown transaction optional data')
    take(4)  # nLockTime is preserved in tx_hex.
    # Base reserialization excludes marker, flags, witness and trailing bytes.
    base_size = 8 + body_end - body_start if flags or vin else 10
    return {'inputs': vin, 'outputs': vout, 'base_size': base_size,
            'consumed': pos, 'trailing_bytes': len(data) - pos}


def estimate_check_transaction(tx):
    """Estimate the first rejection in validation.cpp:527–574 at the pin."""
    vin, vout = tx['inputs'], tx['outputs']
    reason = None
    if not vin:
        reason = 'bad-txns-vin-empty'
    elif not vout:
        reason = 'bad-txns-vout-empty'
    elif tx['base_size'] > MAX_BLOCK_BASE_SIZE:
        reason = 'bad-txns-oversize'
    else:
        total = 0
        for amount, _ in vout:
            total += amount
            if amount < 0:
                reason = 'bad-txns-vout-negative'
            elif amount > MAX_MONEY:
                reason = 'bad-txns-vout-toolarge'
            elif total > MAX_MONEY:
                reason = 'bad-txns-txouttotal-toolarge'
            if reason:
                break
        outpoints = [(i['prevout_txid'], i['prevout_n']) for i in vin]
        null = ('00' * 32, 0xffffffff)
        if reason is None and len(set(outpoints)) != len(outpoints):
            reason = 'bad-txns-inputs-duplicate'
        if reason is None:
            if outpoints == [null]:
                if not 2 <= len(bytes.fromhex(vin[0]['scriptSig_hex'])) <= 100:
                    reason = 'bad-cb-length'
            elif null in outpoints:
                reason = 'bad-txns-prevout-null'
    return {'estimated': True, 'rejects_before_script': reason is not None,
            'reason': reason, 'source': 'src/validation.cpp:527-574'}


def convert_transactions(text, source_file, expectation):
    """Join each serialized input to Core's prevout maps, without a verdict.

    Return spend records and transaction counts, including zero-input cases.
    Comments are source context, which the pinned runner ignores.
    """
    if expectation not in ('valid', 'invalid'):
        raise ValueError('unknown transaction expectation')
    records = []
    comments = []
    previous_was_comment = False
    transactions = 0
    zero_input = 0
    rejections = Counter()
    for index, (line, row) in enumerate(source_records(text)):
        if isinstance(row, list) and len(row) == 1 and isinstance(row[0], str):
            comments = comments + row if previous_was_comment else row[:]
            previous_was_comment = True
            continue
        previous_was_comment = False
        if (not isinstance(row, list) or len(row) != 3 or
                not isinstance(row[0], list) or
                not all(isinstance(x, str) for x in row[1:])):
            raise ValueError(f'bad transaction record at line {line}')
        scripts, amounts = {}, {}
        for prevout in row[0]:
            if (not isinstance(prevout, list) or len(prevout) not in (3, 4) or
                    not isinstance(prevout[0], str) or
                    not re.fullmatch(r'[0-9a-fA-F]{64}', prevout[0]) or
                    type(prevout[1]) is not int or not -(1 << 31) <= prevout[1] < (1 << 31) or
                    not isinstance(prevout[2], str)):
                raise ValueError(f'bad prevout at line {line}')
            key = (prevout[0].lower(), prevout[1] & 0xffffffff)
            scripts[key] = assemble(prevout[2])
            if len(prevout) == 4:
                if type(prevout[3]) is not int or not -(1 << 63) <= prevout[3] < (1 << 63):
                    raise ValueError(f'bad prevout amount at line {line}')
                amounts[key] = prevout[3]
        flags = parse_flags(row[2])
        tx = read_transaction(row[1])
        estimate = estimate_check_transaction(tx)
        transactions += 1
        zero_input += not tx['inputs']
        rejections[estimate['reason'] or 'no_rejection_found'] += 1
        for i, txin in enumerate(tx['inputs']):
            key = (txin['prevout_txid'], txin['prevout_n'])
            if key not in scripts:
                raise ValueError(f'missing prevout for input {i} at line {line}')
            pub = scripts[key]
            classification = classify(bytes.fromhex(txin['scriptSig_hex']), pub,
                                      flags, txin['witness'])
            classification['check_transaction'] = estimate
            record = {'source_file': source_file, 'source_index': index,
                      'source_line': line, 'input_index': i, 'tx_hex': row[1],
                      **txin, 'prevout_scriptPubKey_hex': pub.hex(),
                      'flags': flag_set(flags), 'flags_mask': flags,
                      'test_expectation': expectation, 'comment': comments[:],
                      'per_input_expectation': 'accept' if expectation == 'valid' else None,
                      'per_input_expectation_source': RUNNER + (
                          ':155-176' if expectation == 'valid' else ':239-261'),
                      'per_input_expectation_reason': (
                          'The runner requires VerifyScript acceptance for every input.'
                          if expectation == 'valid' else
                          'CheckTransaction or an earlier input can fail. The transaction expectation identifies no individual input outcome.'),
                      'classification': classification}
            if key in amounts:
                record['prevout_amount'] = amounts[key]
            records.append(record)
    return records, {'transactions': transactions, 'inputs': len(records),
                     'zero_input_transactions': zero_input,
                     'estimated_check_transaction': dict(sorted(rejections.items()))}


def transaction_outputs():
    """Build the transaction spend manifest and its separate summary."""
    records, sources = [], {}
    for expectation in ('valid', 'invalid'):
        name = f'tx_{expectation}.json'
        source = (CORPUS / name).read_bytes()
        converted, counts = convert_transactions(source.decode('utf-8'), name, expectation)
        records.extend(converted)
        sources[name] = {**counts, 'source_file': 'src/test/data/' + name,
                         'source_sha256': hashlib.sha256(source).hexdigest()}
    inside = [r for r in records if r['classification']['milestone'] == 'inside']
    summary = {
        'source_commit': PIN, 'sources': sources,
        'converter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'records': len(records), 'inside_milestone': len(inside),
        'outside_milestone': len(records) - len(inside),
        'per_input_expectations': dict(sorted(Counter(
            r['per_input_expectation'] or 'unknown' for r in records).items())),
        'exclusion_reasons_nonexclusive': dict(sorted(Counter(
            reason for r in records for reason in r['classification']['reasons']).items())),
        'estimated_earliest_stage': dict(sorted(Counter(
            str(r['classification']['estimated_stage']) for r in inside).items())),
        'stage_estimate_method': 'Instruction scan only. No Script execution.',
        'check_transaction_method': 'Estimated from pinned CheckTransaction in source order. No Core execution.',
    }
    return {'tx_spends.jsonl': ''.join(json.dumps(r, sort_keys=True, ensure_ascii=True,
                separators=(',', ':')) + '\n' for r in records).encode(),
            'tx_spends.summary.json': (json.dumps(summary, indent=2, sort_keys=True) + '\n').encode()}


def outputs():
    source = (CORPUS / 'script_tests.json').read_bytes()
    records = convert(source.decode('utf-8'))
    exact = Counter(str(r['classification']['estimated_stage']) for r in records
                    if r['classification']['milestone'] == 'inside')
    summary = {'source_commit': PIN, 'source_file': 'src/test/data/script_tests.json',
               'source_sha256': hashlib.sha256(source).hexdigest(),
               'converter_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'stage_estimate_method': 'conservative instruction scan; cumulative counts are lower bounds for completed stages',
               'records': len(records), 'inside_milestone': sum(exact.values()),
               'outside_milestone': sum(r['classification']['milestone'] == 'outside' for r in records),
               'exclusion_reasons_nonexclusive': dict(sorted(Counter(reason for r in records for reason in r['classification']['reasons']).items())),
               'estimated_earliest_stage': dict(sorted(exact.items())),
               'estimated_cumulative_stages': {str(s): sum(n for stage, n in exact.items() if int(stage) <= s) for s in (2, 3, 4)}}
    return {**transaction_outputs(), 'script_tests.jsonl': ''.join(json.dumps(r, sort_keys=True, ensure_ascii=True, separators=(',', ':')) + '\n' for r in records).encode(),
            'summary.json': (json.dumps(summary, indent=2, sort_keys=True) + '\n').encode()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare outputs without writes')
    args = parser.parse_args()
    stale = []
    for name, data in outputs().items():
        path = CORPUS / name
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                stale.append(name)
        else:
            path.write_bytes(data)
    if stale:
        parser.exit(1, 'stale corpus output: ' + ', '.join(stale) + '\n')
    print('Script corpus outputs match' if args.check else 'Script corpus outputs written')


if __name__ == '__main__':
    main()
