"""Public-key comparison inputs, independent of DogeLib's verifier.

The generated points use affine integer arithmetic only to construct inputs.
Core supplies every comparison verdict, including high-S Wycheproof cases.
"""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
P = 2**256 - 2**32 - 977
N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
G = (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
     0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)


def add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    x, y = a
    u, v = b
    if x == u and (y + v) % P == 0:
        return None
    slope = ((3*x*x) * pow(2*y, -1, P) if a == b else (v-y) * pow(u-x, -1, P)) % P
    z = (slope*slope-x-u) % P
    return z, (slope*(x-z)-y) % P


def mul(k, q):
    result = None
    while k:
        if k & 1:
            result = add(result, q)
        q = add(q, q)
        k >>= 1
    return result


def key(q, prefix=4):
    x, y = q
    return bytes([prefix]) + x.to_bytes(32, 'big') + (y.to_bytes(32, 'big') if prefix >= 4 else b'')


def der(r, s):
    def integer(n):
        b = n.to_bytes(max(1, (n.bit_length()+7)//8), 'big')
        if b[0] & 128:
            b = b'\0' + b
        return b'\x02' + bytes([len(b)]) + b
    payload = integer(r) + integer(s)
    return b'\x30' + bytes([len(payload)]) + payload


def request(pub, sig, digest):
    return dict(op='pubkey.verify', pubkey_hex=pub.hex(), sig_hex=sig.hex(), digest_hex=digest.hex())


def pubkey_sets():
    source = ROOT / 'tests/cryptography/secp256k1/bitcoin/ecdsa_secp256k1_sha256_bitcoin_test.json'
    wycheproof = []
    for group in json.loads(source.read_text())['testGroups']:
        pub = bytes.fromhex(group['publicKey']['uncompressed'])
        for test in group['tests']:
            wycheproof.append(request(pub, bytes.fromhex(test['sig']), hashlib.sha256(bytes.fromhex(test['msg'])).digest()))
    signed = [json.loads(line) for line in (ROOT / 'tests/cryptography/secp256k1/core/requests.jsonl').read_text().splitlines()]
    # Reverse the digest one to detect storage/display byte-order confusion.
    signed += [{**r, 'digest_hex': bytes.fromhex(r['digest_hex'])[::-1].hex()} for r in signed if r['digest_hex'] == '01' + '00'*31]
    parsing = []
    example = signed[0]
    compressed = bytes.fromhex(example['pubkey_hex'])
    qx = int.from_bytes(compressed[1:], 'big')
    qy = pow((qx**3+7) % P, (P+1)//4, P)
    if qy % 2 != compressed[0] % 2:
        qy = P-qy
    q = qx, qy
    sig = bytes.fromhex(example['sig_hex'])
    digest = bytes.fromhex(example['digest_hex'])
    pubs = [key(q), key(q, 2), key(q, 3), key(q, 6), key(q, 7), b'', b'\x05' + key(q)[1:],
            b'\x02' + P.to_bytes(32, 'big'), b'\x04' + P.to_bytes(32, 'big') + G[1].to_bytes(32, 'big'),
            b'\x04' + G[0].to_bytes(32, 'big') + P.to_bytes(32, 'big'), key((G[0], G[1]+1))]
    # Find a compressed x with no square root.
    x = next(x for x in range(100) if pow((x**3+7) % P, (P-1)//2, P) == P-1)
    pubs.append(b'\x02' + x.to_bytes(32, 'big'))
    for pub in pubs:
        parsing.append(request(pub, sig, digest))
    for signature in [b'', b'\x30', der(0, 1), der(1, 0), der(N, 1), der(1, N), der(1, N-1), sig+b'\xff']:
        parsing.append(request(key(q), signature, digest))
    infinity = []
    # Q=dG, e=-rd mod n makes u1 G + u2 Q infinity for every nonzero S.
    for d in (1, 2, 3, N-1):
        q = mul(d, G)
        for r in (1, 2, N-1):
            for s in (1, 2, N-1):
                infinity.append(request(key(q), der(r, s), ((-r*d) % N).to_bytes(32, 'big')))
    high_x = []
    mismatched_r = []
    # Choose R with n <= x < p. Q=r^-1(sR-eG) makes the verification point R.
    x = N
    while len(high_x) < 24:
        rhs = (x**3+7) % P
        y = pow(rhs, (P+1)//4, P)
        if y*y % P == rhs:
            r = x-N
            if r:
                for e in (0, 1, 2**248):
                    s = 2
                    q = mul(pow(r, -1, N), add(mul(s, (x, y)), mul((-e) % N, G)))
                    high_x.append(request(key(q), der(r, s), e.to_bytes(32, 'big')))
                    # Keep R above n, but claim a different R scalar in the signature.
                    r2 = r+1
                    q2 = mul(pow(r2, -1, N), add(mul(s, (x, y)), mul((-e) % N, G)))
                    mismatched_r.append(request(key(q2), der(r2, s), e.to_bytes(32, 'big')))
        x += 1
    # The generated R integers fit a one-byte DER length. Preserve R and replace S.
    high_x += [{**r, 'sig_hex': (bytes.fromhex(r['sig_hex'])[:-1] + b'\x03').hex()} for r in high_x]
    high_x += mismatched_r
    return [('pubkey Wycheproof bitcoin', wycheproof), ('pubkey Core signatures', signed),
            ('pubkey parser boundaries', parsing), ('pubkey infinity', infinity), ('pubkey x above order', high_x)]


def signature_spends():
    """All signed recovery-template fixtures, rechecked by Lean and live Core."""
    records = [json.loads(line) for line in (ROOT / 'tests/script/signed-spends/recovery.jsonl').read_text().splitlines()]
    return [dict(op='script.verify_legacy', tx_hex=r['tx_hex'], input_index=r['input_index'],
                 prevout_script_hex=r['script_pubkey_hex'], flags=r['flags'], checker='transaction')
            for r in records]
