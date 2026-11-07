#!/usr/bin/env python3
"""Reproduce synthetic header bytes and explicit, hand-derived sequence verdicts."""

import argparse
import hashlib
import json
import struct
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'tests/block/regtest-header-sequences'
PIN = 'e0a1c157791544e818c901bd9341896965afbf9d'
LIMIT = 0x207fffff
TIME = 1296688602


def sha256d(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def pow_value(data):
    return int.from_bytes(hashlib.scrypt(data[:80], salt=data[:80], n=1024, r=1, p=1, dklen=32), 'little')


def target(bits):
    return (bits & 0x7fffff) << (8 * ((bits >> 24) - 3))


def generate(seed):
    headers = {}
    genesis = (struct.pack('<I', 1) + bytes(32)
               + bytes.fromhex('5b2a3f53f605d62c53e62932dac6925e3d74afa5a4b459745c36d42d0ed26a69')[::-1]
               + struct.pack('<III', TIME, LIMIT, 2))
    headers['genesis'] = genesis
    assert sha256d(genesis)[::-1].hex() == '3d2160a3b5dc4a9d62e7e66a295f70313ac808440ef7400d6c0772171ce973a5'

    def mine(name, prev, timestamp, bits=LIMIT, version=0x00620004, passing=True):
        predecessor = sha256d(headers[prev][:80]) if prev in headers else bytes.fromhex(prev)
        merkle = hashlib.sha256((seed + ':' + name).encode('ascii')).digest()
        prefix = struct.pack('<I', version) + predecessor + merkle + struct.pack('<II', timestamp, bits)
        for nonce in range(2**32):
            data = prefix + struct.pack('<I', nonce)
            if (pow_value(data) <= target(bits)) == passing:
                headers[name] = data
                return
        raise ValueError('nonce space exhausted')

    mine('a', 'genesis', TIME + 3)
    mine('b', 'a', TIME + 6)
    mine('c', 'b', TIME + 9)
    mine('branch', 'genesis', TIME + 4)
    mine('branch_child', 'branch', TIME + 7)
    mine('unknown', '11' * 32, TIME + 12)
    # Change only the nonce of b, keeping the first nonce that fails scrypt.
    for nonce in range(2**32):
        data = headers['b'][:76] + struct.pack('<I', nonce)
        if pow_value(data) > target(LIMIT):
            headers['bad_nonce'] = data
            break
    mine('wrong_bits', 'a', TIME + 6, LIMIT - 1)
    mine('over_limit', 'a', TIME + 6, LIMIT + 1, passing=False)
    mine('hard_anchor', 'genesis', TIME + 1, LIMIT - 1)
    mine('hard_prefix', 'hard_anchor', TIME + 2, LIMIT - 1)
    mine('bits_plus_one', 'hard_prefix', TIME + 3)
    mine('old_time', 'b', TIME + 3)
    mine('future_time', 'b', TIME + 20000)
    mine('anchor_child', 'b', TIME + 9)
    # A known AuxPoW header needs only a structural payload: step 1 skips step 2.
    mine('known_aux', 'genesis', TIME + 3, version=0x00620104)
    coinbase = (struct.pack('<I', 1) + b'\x01' + bytes(32) + bytes.fromhex('ffffffff')
                + b'\x01\x00' + bytes.fromhex('ffffffff') + b'\x01' + bytes(8) + b'\x00' + bytes(4))
    payload = coinbase + bytes(32) + b'\x00' + bytes(4) + b'\x00' + bytes(4) + genesis
    headers['known_aux'] += payload
    headers['known_aux_changed'] = headers['known_aux'][:-1] + bytes([headers['known_aux'][-1] ^ 1])

    def key(name):
        return sha256d(headers[name][:80])[::-1].hex()

    def entry(name, height, **flags):
        result = dict(header_hex=headers[name][:80].hex(), height=height, anchor=False,
                      failed_valid=False, failed_child=False, scripts_valid=False)
        result.update(flags)
        return result

    cases = []

    def case(name, index, sequence, added, note, *, failure=None, marks=(), failed=(), compare_marks=True):
        # These expectations transcribe source branches, not an execution model.
        valid = failure is None
        position, reason, dos, code = failure if failure else (None, None, None, None)
        expected = dict(valid=valid, failed_at=position, reject_reason=reason, dos=dos, reject_code=code,
                        last_hash=key(sequence[-1]) if valid and sequence else None,
                        added=[dict(hash=key(item), height=height) for item, height in added],
                        marked_failed_child=[key(item) for item in marks])
        cases.append(dict(name=name,
                          request=dict(network='regtest', mode='base', adjusted_time=TIME + 100,
                                       checkpoints_enabled=False, index=index,
                                       failed_blocks=[key(item) for item in failed],
                                       headers=[headers[item].hex() for item in sequence]),
                          expected=expected, compare_marked_failed_child=compare_marks, derivation=note))

    g = entry('genesis', 0)
    a = entry('a', 1)
    b = entry('b', 2)
    accept = 'src/validation.cpp:3224-3259,3274-3282: mined work, known unflagged predecessor, required bits, increasing median and bounded time pass; each unknown header enters the index.'
    case('linear-extension', [g], ['a', 'b', 'c'], [('a', 1), ('b', 2), ('c', 3)], accept)
    case('empty', [g], [], [], 'src/validation.cpp:3274-3284: the empty loop accepts and adds nothing; the fixture represents the unchanged output pointer as null.')
    case('unknown-first', [g], ['unknown'], [], 'src/validation.cpp:3224-3231: work passes, then predecessor lookup misses.', failure=(0, 'bad-prevblk', 10, 0))
    case('unknown-middle', [g], ['a', 'unknown', 'b'], [('a', 1)], 'src/validation.cpp:3229-3231,3274-3277: a remains inserted, lookup fails at position 1 and b never runs.', failure=(1, 'bad-prevblk', 10, 0))
    case('nonce-failure', [g, a], ['bad_nonce', 'c'], [], 'src/dogecoin.cpp:101-108; src/pow.cpp:127-129; src/validation.cpp:2927-2934,3274-3277: the changed nonce exceeds the target; c never runs.', failure=(0, 'high-hash', 50, 16))
    case('wrong-bits-middle', [g], ['a', 'wrong_bits', 'c'], [('a', 1)], 'src/pow.cpp:54-62; src/validation.cpp:3088-3090,3274-3277: the three-second delay requires limit bits, but the mined candidate uses limit minus one; c never runs.', failure=(1, 'bad-diffbits', 100, 16))
    case('bits-plus-one-middle', [g, entry('hard_anchor', 1)], ['hard_prefix', 'bits_plus_one', 'c'], [('hard_prefix', 2)], 'src/pow.cpp:54-69; src/validation.cpp:3088-3090: one-second gaps return the preceding non-limit bits, 0x207ffffe; plus one passes work but fails the raw bits comparison.', failure=(1, 'bad-diffbits', 100, 16))
    case('limit-plus-one', [g], ['a', 'over_limit'], [('a', 1)], 'src/pow.cpp:121-125; src/validation.cpp:2934,3224: 0x20800000 has its sign bit set and zero mantissa, so work fails before contextual checking.', failure=(1, 'high-hash', 50, 16))
    case('duplicate-in-call', [g], ['a', 'a', 'b'], [('a', 1), ('b', 2)], 'src/validation.cpp:3214-3221: the second a returns its existing entry without checks or insertion; b extends it.')
    for flag in ('failed_valid', 'failed_child'):
        case('duplicate-' + flag, [g, entry('a', 1, **{flag: True})], ['a'], [], 'src/validation.cpp:3214-3220; src/consensus/validation.h:50-53: either failure flag rejects a known hash with Invalid, zero score and zero code.', failure=(0, 'duplicate', 0, 0))
        case('predecessor-' + flag, [g, entry('a', 1, **{flag: True})], ['b'], [], 'src/validation.cpp:3233-3234: either predecessor failure flag rejects after work, before the contextual check.', failure=(0, 'bad-prevblk', 100, 16))
    case('flagged-genesis', [entry('genesis', 0, failed_valid=True, failed_child=True)], ['genesis'], [], 'src/validation.cpp:3212,3258-3259,2757-2761: genesis skips duplicate and validation checks; insertion returns the existing flagged entry.')
    case('genesis-insertion', [], ['genesis'], [('genesis', 0)], 'src/validation.cpp:3212,3258-3259,2772-2781: genesis bypasses validation and enters at height zero without a predecessor.')
    case('known-invalid-work', [g, a, entry('bad_nonce', 2)], ['bad_nonce'], [], 'src/validation.cpp:3214-3221: the known unflagged hash returns before its failing work is checked.')
    case('known-changed-auxpow', [g, entry('known_aux', 1)], ['known_aux_changed'], [], 'src/validation.cpp:3209-3221: identical pure bytes give the known key despite a changed parent nonce in the AuxPoW payload; step 2 is skipped.')
    failed_a = entry('a', 1, failed_valid=True)
    case('failed-grandparent', [g, failed_a, b], ['c'], [], 'src/validation.cpp:3238-3253: contextual checks pass, a is an ancestor in the failed list, and the walk marks b but excludes a.', failure=(0, 'bad-prevblk', 100, 16), marks=['b'], failed=['a'])
    case('scripts-valid-bypass', [g, failed_a, entry('b', 2, scripts_valid=True)], ['c'], [('c', 3)], 'src/validation.cpp:3241-3256: scripts-valid b skips the failed-list walk, even with a in the list.', failed=['a'])
    case('failed-flag-outside-list', [g, failed_a, b], ['c'], [('c', 3)], 'src/validation.cpp:3233-3234,3241-3256: b has no failure flag and the list is empty; the flag on a alone does not reject c.')
    case('context-before-failed-ancestor', [g, failed_a, b], ['old_time'], [], 'src/validation.cpp:3102-3104,3238-3241: median(genesis,a,b) is genesis time plus 3; equality fails before the failed-list walk and leaves all marks unchanged.', failure=(0, 'time-too-old', 0, 16), failed=['a'])
    for order in (['genesis', 'a'], ['a', 'genesis']):
        marks = ['b', 'a'] if order[0] == 'genesis' else ['b']
        case('two-failed-' + '-'.join(order), [entry('genesis', 0, failed_valid=True), failed_a, b], ['c'], [], 'src/validation.cpp:3242-3253: the first failed ancestor terminates the walk; the listed marks follow fixture visit order. Design 0008 section 8.3 excludes marks from the Core comparison for both orders.', failure=(0, 'bad-prevblk', 100, 16), marks=marks, failed=order, compare_marks=False)
    case('two-branches', [g], ['a', 'branch', 'branch_child', 'b'], [('a', 1), ('branch', 1), ('branch_child', 2), ('b', 2)], 'src/validation.cpp:3229,3274-3282: each lookup uses the whole index; branch_child extends branch and b extends the earlier a, not the preceding header.')
    case('future-time', [g, a, b], ['future_time'], [], 'src/validation.cpp:3106-3108: candidate time exceeds adjusted_time plus 7200, with passing work, bits and median.', failure=(0, 'time-too-new', 0, 16))
    case('short-anchor-view', [entry('b', 5, anchor=True)], ['anchor_child'], [], 'Design 0008 sections 5.3 and 7.1; design 0006 section 4, item 16: the height-6 candidate has only one of six required median predecessors. Core has no truncated-chain state. Expected adapter error shortView, not a Core reject.', failure=(0, None, None, None))
    cases[-1]['expected']['adapter_error'] = 'shortView'
    # Additional regtest contexts use trusted anchors, never a height relabelled as genesis.
    previous = 'genesis'
    for height in range(1, 23):
        name = f'height_{height}'
        mine(name, previous, TIME + height * 3)
        previous = name
    case('digishield-transition', [g] + [entry(f'height_{h}', h) for h in range(1, 9)],
         ['height_9', 'height_10', 'height_11'], [(f'height_{h}', h) for h in range(9, 12)],
         'src/chainparams.cpp:425-428; src/pow.cpp:49-87; src/dogecoin.cpp:50-86: candidate 10 selects interval one. The three-second spacing gives 1 + trunc((3 - 1)/8) = 1, so target and required bits stay at the limit.')
    case('auxpow-transition-nonlegacy', [g] + [entry(f'height_{h}', h) for h in range(1, 19)],
         ['height_19', 'height_20', 'height_21'], [(f'height_{h}', h) for h in range(19, 22)],
         'src/chainparams.cpp:430-432; src/validation.cpp:3072-3086: nonlegacy chain-ID version without the AuxPoW flag remains allowed across height 20. Required work remains at the limit with three-second spacing.')
    for height in (19, 20):
        name = f'legacy_{height}'
        mine(name, f'height_{height - 1}', TIME + height * 3, version=1)
        case(name, [g] + [entry(f'height_{h}', h) for h in range(1, height)], [name],
             [(name, height)] if height == 19 else [],
             'src/chainparams.cpp:430-432; src/validation.cpp:3072-3077: legacy version 1 passes at height 19 and fails at the activation height 20.',
             failure=None if height == 19 else (0, 'late-legacy-block', 100, 16))
    for activation, old_version in ((1251, 2), (1351, 3)):
        context = []
        previous = '22' * 32
        for height in range(activation - 12, activation - 1):
            name = f'context_{height}'
            mine(name, previous, TIME + height * 3)
            context.append(entry(name, height, anchor=(height == activation - 12)))
            previous = name
        before = f'old_before_{activation}'
        rejected = f'old_at_{activation}'
        accepted = f'upgraded_at_{activation}'
        mine(before, previous, TIME + (activation - 1) * 3, version=0x00620000 | old_version)
        mine(rejected, before, TIME + activation * 3, version=0x00620000 | old_version)
        mine(accepted, before, TIME + activation * 3)
        note = ('src/chainparams.cpp:390-391; src/validation.cpp:3113-3116: base version '
                + str(old_version) + ' passes immediately below the threshold, then fails at it. '
                + 'Eleven predecessors supply the median and retarget context; three-second spacing keeps limit bits.')
        case(f'version-boundary-{activation}', context, [before, rejected], [(before, activation - 1)], note,
             failure=(1, f'bad-version(0x{old_version:08x})', 0, 17))
        case(f'version-upgraded-{activation}', context, [before, accepted], [(before, activation - 1), (accepted, activation)], note)
    return dict(reference_revision=PIN, seed=seed,
                headers={name: dict(header_hex=data.hex(), hash=key(name), scrypt_hex=pow_value(data).to_bytes(32, 'little').hex()) for name, data in headers.items()},
                cases=cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare regenerated bytes without writing fixtures')
    args = parser.parse_args()
    seed = DIRECTORY.joinpath('seed.txt').read_text().strip()
    encoded = (json.dumps(generate(seed), indent=2) + '\n').encode()
    path = DIRECTORY / 'sequences.json'
    if args.check:
        if path.read_bytes() != encoded:
            raise SystemExit('header sequence fixture differs from regeneration')
        print('Synthetic header sequences: exact regeneration passed')
    else:
        path.write_bytes(encoded)
        print(f'Wrote {path.relative_to(ROOT)}')


if __name__ == '__main__':
    main()
