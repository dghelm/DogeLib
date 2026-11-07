"""Contextual header requests with chain and hand-derived expectations (design 0006)."""
import copy
import hashlib
import pathlib
import random
import struct

ROOT = pathlib.Path(__file__).resolve().parent.parent
SEED = 20261109
EXPECTATIONS = {}


def key(req):
    import json
    return json.dumps({k: v for k, v in req.items() if k != 'id'}, sort_keys=True)


def change(req, **fields):
    out = copy.deepcopy(req)
    raw = bytearray.fromhex(out['bytes_hex'])
    for name, offset in [('version', 0), ('time', 68), ('bits', 72)]:
        if name in fields:
            struct.pack_into('<I', raw, offset, fields.pop(name) & 0xffffffff)
    out['bytes_hex'] = raw.hex()
    out.update(fields)
    return out


def request(raw, chain, network='mainnet'):
    return dict(op='block.contextual_check', bytes_hex=raw.hex(), network=network,
                chain=chain, adjusted_time=struct.unpack_from('<I', raw, 68)[0],
                checkpoints_enabled=True, known_checkpoints=[])


def fixture_cases():
    """Chain acceptance fixes verdicts. Chosen node context passes checks 4 and 6."""
    cases = []
    for directory in ['work/mainnet-genesis-headers', 'work/mainnet-headers',
                      'block/mainnet-auxpow-activation-headers', 'block/mainnet-bip66-headers',
                      'block/mainnet-bip65-headers']:
        rows = [(int(h), bytes.fromhex(raw)) for h, raw in
                (line.split() for line in (ROOT / 'tests' / directory / 'headers.txt').read_text().splitlines())]
        for i, (height, raw) in enumerate(rows):
            if i == 0 or (rows[0][0] != 0 and i < 11):
                continue
            # Existing fixtures already pin anchors. Check predecessor links here too.
            assert raw[4:36] == hashlib.sha256(hashlib.sha256(rows[i-1][1]).digest()).digest()
            view = [dict(height=h, time=struct.unpack_from('<I', r, 68)[0],
                         bits=struct.unpack_from('<I', r, 72)[0]) for h, r in reversed(rows[:i])]
            cases.append((request(raw, view), None))
    assert len(cases) == 2231
    return cases


def synthetic(network, height, version=0x00620004, delay=60, bits=None):
    limit = 0x207fffff if network == 'regtest' else 0x1e0ffff0
    view = [dict(height=h, time=1000000 + 60*h, bits=limit)
            for h in range(height-1, max(-1, height-12), -1)]
    raw = struct.pack('<I', version) + bytes(64) + struct.pack('<III', view[0]['time']+delay,
                                                           limit if bits is None else bits, 0)
    return request(raw, view, network)


def boundary_cases(fixtures):
    """Expectations follow D33's ordered conditions and stage 3's hand derivations."""
    cases = []
    def add(req, reason=None):
        cases.append((req, reason))
    by_height = {r['chain'][0]['height']+1: r for r, _ in fixtures}
    for height in range(1, 13):
        r = by_height[height]
        times = sorted(e['time'] for e in r['chain'][:11])
        median = times[len(times)//2]
        add(change(r, time=median), 'time-too-old')
        add(change(r, time=median+1))
    for net, activation in [('mainnet', 371337), ('testnet', 158100), ('regtest', 20)]:
        for h in [activation-1, activation]:
            r = by_height[h] if net == 'mainnet' else synthetic(net, h)
            for version in [1, 2, 0x00620002, 0x00620102]:
                reason = ('late-legacy-block' if h == activation and version in [1, 2] else
                          'early-auxpow-block' if h < activation and version & 256 else None)
                add(change(r, version=version), reason)
                if reason:
                    add(change(r, version=version, bits=0), reason)
    r = by_height[371337]
    bits = struct.unpack_from('<I', bytes.fromhex(r['bytes_hex']), 72)[0]
    for b in [bits-1, bits+1]:
        add(change(r, bits=b), 'bad-diffbits')
    add(change(r, known_checkpoints=[371337]))
    add(change(by_height[371336], known_checkpoints=[371337]), 'bad-fork-prior-to-checkpoint')
    add(change(r, known_checkpoints=[0, 145000, 450000]), 'bad-fork-prior-to-checkpoint')
    add(change(r, known_checkpoints=[450000], checkpoints_enabled=False))
    add(change(r, known_checkpoints=[450000], bits=bits+1), 'bad-diffbits')
    add(change(r, known_checkpoints=[450000], time=0), 'bad-fork-prior-to-checkpoint')
    t = r['adjusted_time']
    for adjusted, reason in [(t-7200, None), (t-7201, 'time-too-new'), (-1, 'time-too-new'),
                             (-2**63, 'time-too-new'), (2**63-1-7200, None)]:
        add(change(r, adjusted_time=adjusted), reason)
    for net, bip66, bip65 in [('mainnet',1034383,3464751), ('testnet',708658,1854705), ('regtest',1251,1351)]:
        for threshold, minimum in [(bip66,3), (bip65,4)]:
            for h in [threshold-1, threshold]:
                r = by_height[h] if net == 'mainnet' else synthetic(net,h)
                for version in [0x00620000+minimum-1, minimum, 0x00620100+minimum-1, 0x80000003, 0x80000000]:
                    signed = version if version < 2**31 else version-2**32
                    base = signed % 256 if signed >= 0 else -((-signed) % 256)
                    required = 4 if h >= bip65 else 3 if h >= bip66 else None
                    reason = f'bad-version(0x{base & 0xffffffff:08x})' if required is not None and base < required else None
                    add(change(r, version=version), reason)
        r = by_height[bip66] if net == 'mainnet' else synthetic(net,bip66)
        add(change(r, version=0x00620102, time=0), 'time-too-old')
        add(change(r, version=0x00620102, adjusted_time=r['adjusted_time']-7201), 'time-too-new')
    for height in [100001,157500,157501]:
        for delay in [119,120,121]:
            required = 0x1e0fffff if delay > 120 and height != 157500 else 0x1e0ffff0
            for bits in [0x1e0ffff0,0x1e0fffff]:
                add(synthetic('testnet',height,delay=delay,bits=bits),
                    None if bits == required else 'bad-diffbits')
    # The minimum-difficulty recovery walk skips two limit entries (D17, lines 65-69).
    r = synthetic('testnet',100001,version=2,delay=120)
    r['chain'][0]['bits'] = r['chain'][1]['bits'] = 0x1e0fffff
    add(r)
    add(change(r,bits=0x1e0fffff), 'bad-diffbits')
    r = by_height[371337]
    add(change(r,time=0,adjusted_time=-2**63), 'time-too-old')
    for h in range(1,12):
        add(synthetic('regtest',h,version=1))
    r = synthetic('mainnet',100,version=1)
    for entry in r['chain']:
        entry['bits'] = 0x1c7fff00
    add(change(r,bits=0x1c7fff00))
    add(change(r,bits=0x1d007fff), 'bad-diffbits')
    for entry, time in zip(r['chain'], [50,1000,30,900,70,800,10,700,90,600,20]):
        entry['time'] = time
    add(change(r,bits=0x1c7fff00,time=90), 'time-too-old')
    add(change(r,bits=0x1c7fff00,time=91))
    return cases


def contextual_sets():
    fixtures = fixture_cases()
    boundaries = boundary_cases(fixtures)
    for req, reason in fixtures + boundaries:
        EXPECTATIONS[key(req)] = dict(valid=reason is None, reject_reason=reason)
    rng = random.Random(SEED)
    mutations = []
    pool = [r for r, _ in fixtures + boundaries]
    for _ in range(500):
        req = rng.choice(pool)
        field = rng.choice(['version','time','bits','adjusted_time','known_checkpoints'])
        value = (rng.choice([[],[0]]) if field == 'known_checkpoints' else
                 rng.choice([-2**63,-1,0,2**63-7201]) if field == 'adjusted_time' else rng.getrandbits(32))
        mutations.append(change(req, **{field:value}))
    return [('contextual fixtures',[r for r,_ in fixtures]),
            ('contextual boundaries',[r for r,_ in boundaries]),
            (f'contextual mutations seed {SEED}', mutations)]
