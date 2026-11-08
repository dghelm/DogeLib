"""Header sequences from design 0008 fixtures and independent integer arithmetic."""
import copy
import hashlib
import json
import pathlib
import random
import struct

ROOT = pathlib.Path(__file__).resolve().parent.parent
SEED = 20261110
EXPECTATIONS = {}
FIELDS = {'valid', 'failed_at', 'reject_reason', 'dos', 'reject_code', 'last_hash',
          'added', 'marked_failed_child'}


def well_shaped(ok):
    """The declared sequence response types, including nested entry fields."""
    def magnitude(value):
        return isinstance(value, str) and len(value) == 64 and all(c in '0123456789abcdef' for c in value)
    def natural(value):
        return type(value) is int and value >= 0
    if set(ok) != FIELDS or type(ok['valid']) is not bool:
        return False
    if ok['valid']:
        if any(ok[k] is not None for k in ['failed_at', 'reject_reason', 'dos', 'reject_code']):
            return False
        if ok['last_hash'] is not None and not magnitude(ok['last_hash']):
            return False
    elif (not natural(ok['failed_at']) or not isinstance(ok['reject_reason'], str) or
          not ok['reject_reason'] or not natural(ok['dos']) or not natural(ok['reject_code']) or
          ok['last_hash'] is not None):
        return False
    if not isinstance(ok['added'], list) or not isinstance(ok['marked_failed_child'], list):
        return False
    return (all(isinstance(e, dict) and set(e) == {'hash', 'height', 'chain_work'} and
                magnitude(e['hash']) and natural(e['height']) and e['height'] < 2147483647 and
                magnitude(e['chain_work']) for e in ok['added']) and
            all(magnitude(h) for h in ok['marked_failed_child']))


def key(req):
    return json.dumps({k: v for k, v in req.items() if k != 'id'}, sort_keys=True)


def digest(raw):
    return hashlib.sha256(hashlib.sha256(bytes.fromhex(raw)[:80]).digest()).digest()[::-1].hex()


def block_proof(raw):
    """D35 chain.cpp:150-162, evaluated with independent Python integers."""
    bits = struct.unpack_from('<I', bytes.fromhex(raw), 72)[0]
    size, word = bits >> 24, bits & 0x7fffff
    target = word >> (8 * (3-size)) if size <= 3 else word << (8 * (size-3))
    overflow = word != 0 and (size > 34 or (word > 0xff and size > 33) or (word > 0xffff and size > 32))
    return 0 if target == 0 or bits & 0x800000 or overflow else 2**256 // (target+1)


def entry(raw, height, work=0, anchor=False):
    return dict(header_hex=raw[:160], height=height, anchor=anchor, failed_valid=False,
                failed_child=False, scripts_valid=False, chain_work=f'{work:064x}')


def request(index, headers, enabled=True):
    return dict(op='block.header_sequence', network='mainnet', mode='base',
                adjusted_time=max([struct.unpack_from('<I', bytes.fromhex(r), 68)[0] for r in headers] or [0]),
                checkpoints_enabled=enabled, index=index, failed_blocks=[], headers=headers)


def acceptance(req):
    """Chain acceptance fixes validity. Sum D35 proofs from supplied anchor work."""
    work = {digest(e['header_hex']): (e['height'], int(e['chain_work'], 16)) for e in req['index']}
    added = []
    for raw in req['headers']:
        h = digest(raw)
        if h in work:
            continue
        prev = bytes.fromhex(raw)[4:36][::-1].hex()
        height, total = work[prev] if prev in work else (-1, 0)
        total = (total + block_proof(raw)) % 2**256
        work[h] = (height+1, total)
        added.append(dict(hash=h, height=height+1, chain_work=f'{total:064x}'))
    return dict(valid=True, failed_at=None, reject_reason=None, dos=None, reject_code=None,
                last_hash=digest(req['headers'][-1]) if req['headers'] else None,
                added=added, marked_failed_child=[])


def regtest_cases():
    data = json.loads((ROOT / 'tests/block/regtest-header-sequences/sequences.json').read_text())
    cases = []
    for case in data['cases']:
        req = dict(op='block.header_sequence', **case['request'])
        expected = copy.deepcopy(case['expected'])
        if 'adapter_error' in expected:
            expected = {'error': {'kind': 'work_view', 'reason': 'short_view'}}
        else:
            expected['marked_failed_child'].sort()
        EXPECTATIONS[key(req)] = expected
        cases.append(req)
    return cases


def mainnet_cases():
    directories = ['work/mainnet-genesis-headers', 'work/mainnet-headers',
                   'block/mainnet-auxpow-activation-full-headers',
                   'block/mainnet-bip66-full-headers', 'block/mainnet-bip65-full-headers']
    cases, ranges = [], []
    for directory in directories:
        rows = [(int(h), raw) for h, raw in (line.split() for line in
                (ROOT / 'tests' / directory / 'headers.txt').read_text().splitlines())]
        index = [entry(raw, h, anchor=i == 0) for i, (h, raw) in enumerate(rows[:11])]
        req = request([] if rows[0][0] == 0 else index,
                      [raw for _, raw in (rows if rows[0][0] == 0 else rows[11:])])
        EXPECTATIONS[key(req)] = acceptance(req)
        cases.append(req)
        ranges.append(rows)
    # Pure-header fixtures supply checked initial state. Their missing AuxPoW
    # payloads cannot serve as unknown full candidates (D80-D82 READMEs).
    for directory in ['block/mainnet-auxpow-activation-headers', 'block/mainnet-bip66-headers',
                      'block/mainnet-bip65-headers']:
        rows = [(int(h), raw) for h, raw in (line.split() for line in
                (ROOT / 'tests' / directory / 'headers.txt').read_text().splitlines())]
        req = request([entry(raw, h, anchor=i == 0) for i, (h, raw) in enumerate(rows)], [])
        EXPECTATIONS[key(req)] = acceptance(req)
        cases.append(req)
    # D33:3093-3100,3238-3239: checkpoint 145000 enters during this call.
    rows = ranges[1]
    genesis = ranges[0]
    prefix = [raw for h, raw in rows if 144730 <= h <= 145000]
    index = [entry(raw, h, anchor=i == 0) for i, (h, raw) in enumerate(rows[:11])]
    index += [entry(raw, h) for h, raw in genesis[:11]]
    for enabled in [True, False]:
        req = request(index, prefix + [genesis[11][1]], enabled)
        expected = acceptance(req)
        if enabled:
            expected.update(valid=False, failed_at=271, reject_reason='bad-fork-prior-to-checkpoint',
                            dos=100, reject_code=67, last_hash=None)
            expected['added'].pop()
        EXPECTATIONS[key(req)] = expected
        cases.append(req)
    # Anchor guards: the median has too few entries, or retarget 144960
    # needs height 144719 below the raised anchor (pow.cpp:78-85).
    for start, end in [(144720, 144721), (144731, 144960)]:
        lower = 144719 if start == 144720 else 144720
        index = [entry(raw, h, anchor=h == lower) for h, raw in rows if lower <= h < start]
        req = request(index, [raw for h, raw in rows if start <= h <= end])
        EXPECTATIONS[key(req)] = {'error': {'kind': 'work_view', 'reason': 'short_view' if start == 144720 else 'missing_ancestor'}}
        cases.append(req)
    # Version mutations use the hand derivations in KnownAnswers/HeaderSequence.lean:
    # changing committed version bytes breaks step 2 before contextual checks.
    for rows, height, version in [(ranges[2],371337,0x00620002),
                                  (ranges[3],1034383,0x00620102),
                                  (ranges[4],3464751,0x00620103)]:
        before = [(h, r) for h, r in rows if height-11 <= h < height]
        index = [entry(r, h, anchor=i == 0) for i, (h, r) in enumerate(before)]
        raw = bytearray.fromhex(dict(rows)[height]); struct.pack_into('<I', raw, 0, version)
        if height == 371337: raw = raw[:80]
        req = request(index, [raw.hex()])
        EXPECTATIONS[key(req)] = dict(valid=False, failed_at=0, reject_reason='high-hash', dos=50,
                                     reject_code=16, last_hash=None, added=[], marked_failed_child=[])
        cases.append(req)
    return cases


def exclude_marks(req):
    """Decision 12: two distinct failed members are ancestors of one predecessor.

    Include predecessors supplied by earlier request headers, on any branch.
    This predicate depends on ancestry, never on fixture names or response marks.
    """
    index = {digest(e['header_hex']): (None if e['anchor'] or e['height'] == 0 else
             bytes.fromhex(e['header_hex'])[4:36][::-1].hex()) for e in req['index']}
    failed = {h.lower() for h in req['failed_blocks']}
    for raw in req['headers']:
        prev = bytes.fromhex(raw)[4:36][::-1].hex()
        seen = set()
        while prev in index and prev not in seen:
            seen.add(prev)
            prev = index[prev]
        if len(seen & failed) >= 2:
            return True
        index.setdefault(digest(raw), bytes.fromhex(raw)[4:36][::-1].hex())
    return False


def boundary_cases(regtest):
    """D33:3241-3253: retain prefix insertions, report every marking-loop visit, stop at anchors."""
    data = json.loads((ROOT / 'tests/block/regtest-header-sequences/sequences.json').read_text())
    raw = {k: v['header_hex'] for k, v in data['headers'].items()}
    genesis, a, b = [entry(raw[n], h, 2*(h+1)) for h, n in enumerate(['genesis', 'a', 'b'])]
    genesis['failed_valid'] = True
    a['scripts_valid'] = True
    req = dict(op='block.header_sequence', network='regtest', mode='base', adjusted_time=1296688702,
               checkpoints_enabled=False, index=[genesis, a], failed_blocks=[digest(raw['genesis'])],
               headers=[raw['b'], raw['c']])
    expected = dict(valid=False, failed_at=1, reject_reason='bad-prevblk', dos=100, reject_code=16,
                    last_hash=None, added=[dict(hash=digest(raw['b']),height=2,chain_work=f'{6:064x}')],
                    marked_failed_child=sorted([digest(raw['a']), digest(raw['b'])]))
    EXPECTATIONS[key(req)] = expected
    cases = [req]
    req = copy.deepcopy(req)
    req['index'][1]['scripts_valid'] = False
    req['index'][1]['failed_child'] = True
    req['index'].append(b)
    req['headers'] = [raw['c']]
    EXPECTATIONS[key(req)] = dict(expected, failed_at=0, added=[])
    cases.append(req)
    fixture = next(c for c in data['cases'] if c['name'] == 'version-upgraded-1351')
    req = dict(op='block.header_sequence', **copy.deepcopy(fixture['request']))
    req['index'].append(genesis)
    req['failed_blocks'] = [digest(raw['genesis'])]
    EXPECTATIONS[key(req)] = copy.deepcopy(fixture['expected'])
    cases.append(req)
    return cases


def sequence_sets():
    regtest = regtest_cases()
    mainnet = mainnet_cases()
    boundaries = boundary_cases(regtest)
    rng = random.Random(SEED)
    mutations = []
    pool = [r for r in regtest if 'error' not in EXPECTATIONS[key(r)]]
    for i in range(200):
        req = copy.deepcopy(rng.choice(pool))
        field = ['order', 'bits', 'time', 'prev', 'flags', 'failed'][i % 6]
        if field == 'order':
            rng.shuffle(req['headers'])
        elif field in ('flags', 'failed') and req['index']:
            e = rng.choice(req['index'])
            if field == 'flags':
                e[rng.choice(['failed_valid', 'failed_child', 'scripts_valid'])] = True
            else:
                e['failed_valid'] = True
                req['failed_blocks'] = list(dict.fromkeys(req['failed_blocks'] + [digest(e['header_hex'])]))
                rng.shuffle(req['failed_blocks'])
        elif req['headers']:
            pos = rng.randrange(len(req['headers']))
            raw = bytearray.fromhex(req['headers'][pos])
            if field == 'prev': raw[4:36] = rng.randbytes(32)
            else: struct.pack_into('<I', raw, 72 if field == 'bits' else 68, rng.getrandbits(32))
            req['headers'][pos] = raw.hex()
        mutations.append(req)
    return [('header sequence regtest 34', regtest), ('header sequence mainnet', mainnet),
            ('header sequence state boundaries', boundaries),
            (f'header sequence mutations seed {SEED}', mutations)]
