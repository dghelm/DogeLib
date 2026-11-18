"""Requests for `block.validate`, their expectations, and the comparison of the two programs.

Design record 0010, section 5, sets the exit conditions: agreement on real blocks from the
genesis block, digests included, and on mutations, at least one for each reject reason that
`ConnectBlock` can reach.

A request supplies the state before its first block, and each program carries the coin set
through the blocks (docs/oracle.md, "Block validation"). A block that the checks reject changes
nothing, so one request can hold several candidates for one height: the rejected ones first, and
then an accepted one.

The mutation requests use no download. They start from the genesis block, or from a committed
rule-change block of `tests/block/mainnet-blocks/rule-changes`, whose header gives a real
context: the request keeps the header, replaces the transactions and the Merkle root, and clears
`check_pow`. The supplied coins are synthetic.

Every expectation is written here from Core's text, and no program supplies one. `Model` computes
each digest a third time, from the definition in docs/oracle.md. It takes the verdicts from the
expectations and decides nothing about validity.

The module signs with the private key 1, which is public test data. Never send funds to it.
"""

import hashlib
import json
import pathlib

import fetch_release_blocks
import fetch_version_bits_headers
from oracle_block_check import (COIN, MAX_MONEY, NULL_PREVOUT, BlockAssets, block, compact_size, fixture_blocks,
                                genesis_block, le, root_of, same, sha256d, split_block, transaction, txin, txout)
from oracle_contextual_body import RULE_DIR, VERSION_BITS_HEADERS, body_chain, script_num

LABEL = "BLOCK_VALIDATE"
ADJUSTED_TIME = 4102444800  # 2100-01-01, after every block time
BIP34_HEIGHT = 1034383
# BIP34Hash of src/chainparams.cpp, line 85, in internal byte order.
BIP34_HASH = bytes.fromhex("80d1364201e5df97e696c03bdd24dc885e8617b9de51e453c10a4f629b1e797a")[::-1]
SET_DIGEST_INTERVAL = 1000
REJECT_INVALID, REJECT_NONSTANDARD = 16, 64

# The reasons that ConnectBlock can reach beyond stage 0010a (design record 0010, section 5),
# with the score and the code of Core's text. The two script reasons carry a text in brackets.
CONNECT_REASONS = {
    "bad-txns-BIP30": (100, REJECT_INVALID),
    "bad-txns-inputs-missingorspent": (100, REJECT_INVALID),
    "bad-txns-premature-spend-of-coinbase": (0, REJECT_INVALID),
    "bad-txns-inputvalues-outofrange": (100, REJECT_INVALID),
    "bad-txns-in-belowout": (100, REJECT_INVALID),
    "bad-blk-sigops": (100, REJECT_INVALID),
    "bad-cb-amount": (100, REJECT_INVALID),
    "mandatory-script-verify-flag-failed": (100, REJECT_INVALID),
    "non-mandatory-script-verify-flag": (0, REJECT_NONSTANDARD),
}
# Reasons of the four earlier checks that the order cases reach.
EARLIER_REASONS = {
    "bad-diffbits": (100, REJECT_INVALID),
    "bad-txnmrklroot": (100, REJECT_INVALID),
    "bad-txns-inputs-duplicate": (100, REJECT_INVALID),
    "bad-txns-nonfinal": (10, REJECT_INVALID),
}
EVAL_FALSE = "Script evaluated without error but finished with a false/empty top stack element"
SIG_DER = "Non-canonical DER signature"
BAD_OPCODE = "Opcode missing or not understood"
SIG_PUSHONLY = "Only non-push operators allowed in signatures"
UNSATISFIED_LOCKTIME = "Locktime requirement not satisfied"
OP_RETURN_TEXT = "OP_RETURN was encountered"
BLOCK_FIELDS = {"height", "hash_hex", "hash_display", "valid", "reject_reason", "dos", "reject_code",
                "changes_digest_hex", "spent", "created", "set_digest_hex"}
OK_FIELDS = {"blocks", "out_of_domain_at", "set_digest_hex", "set_coins"}

EXPECTATIONS = {}


def key(req: dict) -> str:
    text = json.dumps({k: v for k, v in req.items() if k != "id"}, sort_keys=True)
    return hashlib.sha256(text.encode()).hexdigest()


# ---------------------------------------------------------------------------
# Hashes and signatures


def ripemd160(data: bytes) -> bytes:
    """RIPEMD-160, written out because hashlib has it only with some OpenSSL builds."""
    def rol(x, n):
        return ((x << n) | (x >> (32 - n))) & 0xffffffff
    fs = [lambda x, y, z: x ^ y ^ z, lambda x, y, z: (x & y) | (~x & z), lambda x, y, z: (x | ~y) ^ z,
          lambda x, y, z: (x & z) | (y & ~z), lambda x, y, z: x ^ (y | ~z)]
    kl = [0x00000000, 0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xa953fd4e]
    kr = [0x50a28be6, 0x5c4dd124, 0x6d703ef3, 0x7a6d76e9, 0x00000000]
    rl = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
          3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12, 1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
          4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]
    rr = [5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12, 6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
          15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13, 8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
          12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]
    sl = [11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8, 7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13,
          12, 11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5, 11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6,
          5, 12, 9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]
    sr = [8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6, 9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13,
          11, 9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5, 15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5,
          15, 8, 8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]
    state = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]
    padded = data + b"\x80" + bytes((55 - len(data)) % 64) + le(8 * len(data), 8)
    for start in range(0, len(padded), 64):
        words = [int.from_bytes(padded[start + 4 * i:start + 4 * i + 4], "little") for i in range(16)]
        a, b, c, d, e = state
        a2, b2, c2, d2, e2 = state
        for j in range(80):
            t = (rol((a + fs[j // 16](b, c, d) + words[rl[j]] + kl[j // 16]) & 0xffffffff, sl[j]) + e) & 0xffffffff
            a, e, d, c, b = e, d, rol(c, 10), b, t
            t = (rol((a2 + fs[4 - j // 16](b2, c2, d2) + words[rr[j]] + kr[j // 16]) & 0xffffffff, sr[j]) + e2) & 0xffffffff
            a2, e2, d2, c2, b2 = e2, d2, rol(c2, 10), b2, t
        t = (state[1] + c + d2) & 0xffffffff
        state = [t, (state[2] + d + e2) & 0xffffffff, (state[3] + e + a2) & 0xffffffff,
                 (state[4] + a + b2) & 0xffffffff, (state[0] + b + c2) & 0xffffffff]
    return b"".join(le(x, 4) for x in state)


assert ripemd160(b"abc").hex() == "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"


def hash160(data: bytes) -> bytes:
    return ripemd160(hashlib.sha256(data).digest())


FIELD = 2**256 - 2**32 - 977
ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GENERATOR = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
             0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)


def point_add(p, q):
    """The sum of two points of secp256k1 in affine coordinates. None is the point at infinity."""
    if p is None:
        return q
    if q is None:
        return p
    if p[0] == q[0] and (p[1] + q[1]) % FIELD == 0:
        return None
    if p == q:
        slope = 3 * p[0] * p[0] * pow(2 * p[1], -1, FIELD) % FIELD
    else:
        slope = (q[1] - p[1]) * pow(q[0] - p[0], -1, FIELD) % FIELD
    x = (slope * slope - p[0] - q[0]) % FIELD
    return x, (slope * (p[0] - x) - p[1]) % FIELD


def point_mul(k: int, p):
    result = None
    while k:
        if k & 1:
            result = point_add(result, p)
        p = point_add(p, p)
        k >>= 1
    return result


PRIVATE_KEY = 1
PUBLIC_KEY = bytes([2 + (GENERATOR[1] & 1)]) + GENERATOR[0].to_bytes(32, "big")


def der_integer(n: int, pad: int = 0) -> bytes:
    body = n.to_bytes((n.bit_length() + 8) // 8 or 1, "big")
    body = bytes(pad) + body
    return b"\x02" + bytes([len(body)]) + body


def sign(digest: bytes, strict: bool = True) -> bytes:
    """An ECDSA signature of a 32-byte digest by the private key 1, with a low S and the byte SIGHASH_ALL.

    Core reads the digest as a big-endian number (src/pubkey.cpp, D50). With `strict` false, R has
    one more leading zero byte. Core's lax parser reads the same R, and the strict DER test of
    SCRIPT_VERIFY_DERSIG rejects the encoding (src/script/interpreter.cpp, IsValidSignatureEncoding)."""
    z = int.from_bytes(digest, "big")
    nonce = int.from_bytes(hashlib.sha256(b"dogelib nonce" + digest).digest(), "big") % ORDER or 1
    r = point_mul(nonce, GENERATOR)[0] % ORDER
    s = pow(nonce, -1, ORDER) * (z + r * PRIVATE_KEY) % ORDER
    assert r and s
    s = min(s, ORDER - s)
    body = der_integer(r, 0 if strict else 1) + der_integer(s)
    return b"\x30" + bytes([len(body)]) + body + b"\x01"


# ---------------------------------------------------------------------------
# Scripts and transactions

OP_0, OP_PUSHDATA1, OP_PUSHDATA2, OP_1, OP_16 = 0x00, 0x4c, 0x4d, 0x51, 0x60
OP_NOP, OP_IF, OP_ENDIF, OP_RETURN, OP_DROP = 0x61, 0x63, 0x68, 0x6a, 0x75
OP_EQUAL, OP_HASH160, OP_CHECKSIG, OP_CHECKMULTISIG, OP_CLTV = 0x87, 0xa9, 0xac, 0xae, 0xb1
TRUE = bytes([OP_1])
FALSE = bytes([OP_0])


def push(data: bytes) -> bytes:
    """The shortest push of `data`."""
    if len(data) < OP_PUSHDATA1:
        return bytes([len(data)]) + data
    if len(data) < 256:
        return bytes([OP_PUSHDATA1, len(data)]) + data
    return bytes([OP_PUSHDATA2]) + le(len(data), 2) + data


P2PK = push(PUBLIC_KEY) + bytes([OP_CHECKSIG])


def p2sh(redeem: bytes) -> bytes:
    return bytes([OP_HASH160]) + push(hash160(redeem)) + bytes([OP_EQUAL])


def unexecuted(body: bytes) -> bytes:
    """A script that pushes true and never runs `body`, whose signature operations still count."""
    return bytes([OP_0, OP_IF]) + body + bytes([OP_ENDIF, OP_1])


def outpoint(txid: bytes, n: int = 0) -> bytes:
    assert len(txid) == 32
    return txid + le(n, 4)


def coin_id(tag: int) -> bytes:
    """A synthetic transaction ID for a supplied coin."""
    return hashlib.sha256(b"dogelib supplied coin %d" % tag).digest()


def spend(prevouts: list[bytes], outputs: list[bytes], scripts: list[bytes] | None = None, lock: int = 0,
          sequence: int = 0xffffffff) -> bytes:
    scripts = scripts or [b""] * len(prevouts)
    return transaction([txin(p, s, sequence) for p, s in zip(prevouts, scripts)], outputs, lock=lock)


def signed_spend(prevouts: list[bytes], outputs: list[bytes], code: bytes, strict: bool = True,
                 wrong: bool = False, lock: int = 0, sequence: int = 0xffffffff) -> bytes:
    """A transaction whose first input has a signature by the private key 1 for the script code `code`.

    The digest is the legacy signature hash with SIGHASH_ALL (D3, lines 1211 to 1251): the transaction
    with `code` as the script of the signed input and empty scripts elsewhere, then the hash type.
    With `wrong`, the signature is for another digest."""
    scripts = [code] + [b""] * (len(prevouts) - 1)
    digest = sha256d(spend(prevouts, outputs, scripts, lock, sequence) + le(1, 4))
    if wrong:
        digest = sha256d(digest)
    return spend(prevouts, outputs, [push(sign(digest, strict))] + [b""] * (len(prevouts) - 1), lock, sequence)


def coinbase_tx(height: int, value: int = 0, script: bytes = TRUE, tag: bytes = b"") -> bytes:
    """A coinbase. From BIP34Height its scriptSig starts with the push of the height."""
    script_sig = (push(script_num(height)) if height >= BIP34_HEIGHT else b"") + b"\x51\x51" + tag
    assert 2 <= len(script_sig) <= 100
    return transaction([txin(NULL_PREVOUT, script_sig)], [txout(value, script)])


def subsidy(height: int) -> int:
    """The mainnet subsidy from height 145,000 (src/dogecoin.cpp, lines 138 to 148)."""
    assert height >= 145000
    return (500000 * COIN) >> (height // 100000) if height < 600000 else 10000 * COIN


# ---------------------------------------------------------------------------
# Contexts and requests


class Coins:
    """Supplied coins, grouped by transaction ID as the request holds them."""

    def __init__(self):
        self.entries = {}

    def add(self, txid: bytes, n: int, value: int, script: bytes = TRUE, height: int = 100000,
            coinbase: bool = False) -> bytes:
        entry = self.entries.setdefault(txid, {"coinbase": coinbase, "height": height, "outputs": {}})
        assert entry["coinbase"] == coinbase and entry["height"] == height and n not in entry["outputs"]
        entry["outputs"][n] = (value, script)
        return outpoint(txid, n)

    def json(self) -> list[dict]:
        return [{"txid_hex": txid.hex(), "coinbase": e["coinbase"], "height": e["height"],
                 "outputs": [{"n": n, "value": str(value), "script_hex": script.hex()}
                             for n, (value, script) in e["outputs"].items()]}
                for txid, e in self.entries.items()]


_fixtures = None


def fixtures() -> tuple[dict[int, bytes], dict[int, bytes]]:
    """Height -> header for the version-bits runs and the rule-change blocks, and height -> rule-change block."""
    global _fixtures
    if _fixtures is None:
        headers = dict(fetch_version_bits_headers.load_fixture(VERSION_BITS_HEADERS))
        blocks = {record["height"]: raw for record, raw in fixture_blocks(RULE_DIR)}
        headers.update({height: raw[:80] for height, raw in blocks.items()})
        _fixtures = headers, blocks
    return _fixtures


class Base:
    """The context of a committed rule-change block: its header, its chain view and its predecessor."""

    def __init__(self, height: int):
        headers, blocks = fixtures()
        self.height = height
        self.header, _ = split_block(blocks[height])
        self.chain = body_chain(height, headers)
        self.ancestor = sha256d(blocks[BIP34_HEIGHT][:80]) if height > BIP34_HEIGHT else None

    def block(self, txs: list[bytes], root: bytes | None = None, bits: int | None = None) -> bytes:
        """The transactions under the real header, with their Merkle root in it."""
        pure = self.header[:36] + (root_of(txs) if root is None else root) + self.header[68:80]
        if bits is not None:
            pure = pure[:72] + le(bits, 4) + pure[76:]
        return block(txs, header=pure + self.header[80:])

    def coinbase(self, value: int = 0, script: bytes = TRUE, tag: bytes = b"") -> bytes:
        return coinbase_tx(self.height, value, script, tag)

    def request(self, blocks: list[bytes], coins: Coins | None = None, ancestor=False) -> dict:
        ancestor = self.ancestor if ancestor is False else ancestor
        return request(blocks, self.chain, coins, ancestor)


def request(blocks: list[bytes], chain: list[dict] | None = None, coins: Coins | None = None,
            ancestor: bytes | None = None, check_pow: bool = False, mode: str = "base") -> dict:
    return {"op": "block.validate", "mode": mode, "check_pow": check_pow, "check_merkle_root": True,
            "adjusted_time": ADJUSTED_TIME, "chain": chain or [],
            "bip34_ancestor_hex": None if ancestor is None else ancestor.hex(),
            "coins": coins.json() if coins else [], "blocks_hex": [b.hex() for b in blocks]}


def script_reason(mandatory: bool, text: str) -> str:
    return ("mandatory-script-verify-flag-failed" if mandatory else "non-mandatory-script-verify-flag") + f" ({text})"


def verdict_of(reason: str | None):
    """The reason, score and code of a rejection, from Core's text, or None for an accepted block."""
    if reason is None:
        return None
    score, code = {**CONNECT_REASONS, **EARLIER_REASONS}[reason.split(" (")[0]]
    return reason, score, code


def expect(req: dict, reasons: list, out_of_domain_at: int | None = None, error: dict | None = None) -> dict:
    """Record the expectation of a request: the reject reason of each block, or None for an accepted one.

    With `out_of_domain_at`, the oracle ends the range at that block, and `reasons` covers the blocks
    before it. With `error`, both programs return that error."""
    expectation = {"error": error}
    if error is None:
        model = Model(req)
        records = []
        for raw, reason in zip([bytes.fromhex(b) for b in req["blocks_hex"]], reasons):
            records.append(model.record(raw, verdict_of(reason)))
        assert len(reasons) == (len(req["blocks_hex"]) if out_of_domain_at is None else out_of_domain_at)
        digest, count = model.set_digest()
        expectation.update({"blocks": records, "out_of_domain_at": out_of_domain_at,
                            "set_digest_hex": digest.hex(), "set_coins": count})
    EXPECTATIONS[key(req)] = expectation
    return req


# ---------------------------------------------------------------------------
# The digests, from the definition in docs/oracle.md


def parse_transaction(data: bytes, pos: int) -> tuple[bytes, list[bytes], list[tuple[int, bytes]], int]:
    """The base bytes, the outpoints and the outputs of a transaction in the base format, and the end."""
    start = pos
    count, pos = read_size(data, pos + 4)
    inputs = []
    for _ in range(count):
        inputs.append(data[pos:pos + 36])
        pos += 36
        size, pos = read_size(data, pos)
        pos += size + 4
    count, pos = read_size(data, pos)
    outputs = []
    for _ in range(count):
        value = int.from_bytes(data[pos:pos + 8], "little")
        size, end = read_size(data, pos + 8)
        outputs.append((value, data[end:end + size]))
        pos = end + size
    pos += 4
    return data[start:pos], inputs, outputs, pos


def read_size(data: bytes, pos: int) -> tuple[int, int]:
    first = data[pos]
    if first < 0xfd:
        return first, pos + 1
    width = {0xfd: 2, 0xfe: 4, 0xff: 8}[first]
    return int.from_bytes(data[pos + 1:pos + 1 + width], "little"), pos + 1 + width


def unspendable(script: bytes) -> bool:
    """CScript::IsUnspendable (src/script/script.h, lines 635 to 638)."""
    return script[:1] == bytes([OP_RETURN]) or len(script) > 10000


def coin_record(tag: int, point: bytes, height: int, coinbase: bool, value: int, script: bytes) -> bytes:
    return bytes([tag]) + point + le(height, 4) + bytes([int(coinbase)]) + le(value, 8) + compact_size(len(script)) + script


GENESIS_HASH = bytes.fromhex("1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691")[::-1]


class Model:
    """The coin set of a request, changed by each block that the expectation accepts.

    It follows the definition of the digests only. It checks no rule."""

    def __init__(self, req: dict):
        self.coins = {}  # outpoint -> (height, coinbase, value, script)
        for entry in req["coins"]:
            for output in entry["outputs"]:
                point = bytes.fromhex(entry["txid_hex"]) + le(output["n"], 4)
                self.coins[point] = (entry["height"], entry["coinbase"], int(output["value"]),
                                     bytes.fromhex(output["script_hex"]))
        self.height = req["chain"][0]["height"] + 1 if req["chain"] else 0

    def set_digest(self) -> tuple[bytes, int]:
        digest = bytes(32)
        # The order of the transaction IDs as byte strings, and then of the output indexes.
        for point in sorted(self.coins, key=lambda p: (p[:32], int.from_bytes(p[32:], "little"))):
            digest = sha256d(digest + coin_record(2, point, *self.coins[point]))
        return digest, len(self.coins)

    def record(self, raw: bytes, verdict) -> dict:
        header, txs = split_block(raw)
        block_hash = sha256d(raw[:80])
        record = {"height": self.height, "hash_hex": block_hash.hex(), "hash_display": block_hash[::-1].hex(),
                  "valid": verdict is None, "reject_reason": None, "dos": None, "reject_code": None,
                  "changes_digest_hex": None, "spent": None, "created": None, "set_digest_hex": None}
        if verdict is not None:
            record.update(zip(("reject_reason", "dos", "reject_code"), verdict))
            return record
        digest, spent, created = bytes(32), 0, 0
        # The genesis block changes nothing.
        for index, tx in enumerate(txs if block_hash != GENESIS_HASH else []):
            base, inputs, outputs, end = parse_transaction(tx, 0)
            assert end == len(tx)
            txid = sha256d(base)
            for point in inputs if index else []:
                digest = sha256d(digest + coin_record(0, point, *self.coins.pop(point)))
                spent += 1
            # The new entry replaces every earlier coin of the transaction ID.
            for point in [p for p in self.coins if p[:32] == txid]:
                del self.coins[point]
            for n, (value, script) in enumerate(outputs):
                if not unspendable(script):
                    self.coins[txid + le(n, 4)] = (self.height, index == 0, value, script)
                    digest = sha256d(digest + coin_record(1, txid + le(n, 4), self.height, index == 0, value, script))
                    created += 1
        record.update({"changes_digest_hex": digest.hex(), "spent": spent, "created": created})
        if self.height % SET_DIGEST_INTERVAL == 0:
            record["set_digest_hex"] = self.set_digest()[0].hex()
        self.height += 1
        return record


# ---------------------------------------------------------------------------
# Cases

TIME = 1386325540
BITS = 0x1e0ffff0
MISSING = "bad-txns-inputs-missingorspent"
PREMATURE = "bad-txns-premature-spend-of-coinbase"


def genesis_chain_cases() -> list[dict]:
    """A chain of made blocks from the real genesis block, with the state carried through 34 heights.

    Below height 145,000 the subsidy is at least 2 coins, so a coinbase that pays 1 coin passes."""
    genesis = genesis_block()
    prev = [sha256d(genesis[:80])]

    def made(height: int, txs: list[bytes]) -> bytes:
        # Height 1 to 239 has no retarget, so the bits are those of the genesis block.
        return block(txs, version=1, prev=prev[0], time=TIME + 60 * height, bits=BITS)

    def accept(height: int, txs: list[bytes]) -> bytes:
        data = made(height, txs)
        prev[0] = sha256d(data[:80])
        return data

    def cb(height: int, value: int = 0) -> bytes:
        return coinbase_tx(height, value, tag=le(height, 2))

    blocks, reasons = [genesis], [None]
    first = cb(1, COIN)
    first_coin = outpoint(sha256d(first))
    blocks.append(accept(1, [first]))
    reasons.append(None)
    for height in range(2, 30):
        blocks.append(accept(height, [cb(height)]))
        reasons.append(None)
    # Maturity 30: at height 30 the coinbase of height 1 has depth 29.
    blocks.append(made(30, [cb(30), spend([first_coin], [txout(COIN)])]))
    reasons.append(PREMATURE)
    blocks.append(accept(30, [cb(30)]))
    reasons.append(None)
    # At height 31 the depth is 30. The outputs are three coins, a false script, a script that
    # reaches OP_RETURN, and two unspendable scripts, which never enter the set.
    fan = spend([first_coin], [txout(1000), txout(1000), txout(1000), txout(1000, FALSE),
                               txout(1000, bytes([OP_1, OP_RETURN])), txout(0, bytes([OP_RETURN])),
                               txout(0, TRUE * 10001)])
    fan_id = sha256d(fan)
    blocks.append(accept(31, [cb(31), fan]))
    reasons.append(None)
    a0, a1, a2 = (outpoint(fan_id, n) for n in range(3))
    candidates = [
        # The genesis block adds no coin, so its coinbase output is not in the set.
        ([spend([outpoint(sha256d(split_block(genesis)[1][0]))], [txout(1)])], MISSING),
        # Unspendable outputs: OP_RETURN first, and a script above MAX_SCRIPT_SIZE.
        ([spend([outpoint(fan_id, 5)], [txout(0)])], MISSING),
        ([spend([outpoint(fan_id, 6)], [txout(0)])], MISSING),
        # An index after the outputs, and a transaction ID with no entry.
        ([spend([outpoint(fan_id, 7)], [txout(0)])], MISSING),
        ([spend([outpoint(coin_id(1))], [txout(0)])], MISSING),
        # A double spend within the block: the second transaction finds the coin spent.
        ([spend([a0], [txout(1)]), spend([a0], [txout(2)])], MISSING),
        # A spend of an output that the block creates later.
        ([spend([outpoint(sha256d(spend([a0], [txout(7)])))], [txout(7)]), spend([a0], [txout(7)])], MISSING),
        # The second input is missing after the first is found.
        ([spend([a0, outpoint(coin_id(2))], [txout(1)])], MISSING),
        ([spend([a0], [txout(1001)])], "bad-txns-in-belowout"),
        ([spend([a0, a1], [txout(2001)])], "bad-txns-in-belowout"),
        # Without DERSIG and CLTV, CheckInputs runs each script once, and every failure is mandatory.
        ([spend([outpoint(fan_id, 3)], [txout(1)])], script_reason(True, EVAL_FALSE)),
        ([spend([outpoint(fan_id, 4)], [txout(1)])], script_reason(True, OP_RETURN_TEXT)),
        ([spend([a0], [txout(1)], [bytes([OP_PUSHDATA1, 5, 1])])], script_reason(True, BAD_OPCODE)),
        # The first failing input in input order gives the reason.
        ([spend([a0, outpoint(fan_id, 4), outpoint(fan_id, 3)], [txout(1)])], script_reason(True, OP_RETURN_TEXT)),
    ]
    for txs, reason in candidates:
        blocks.append(made(32, [cb(32)] + txs))
        reasons.append(reason)
    # A chain within the block: the second transaction spends an output of the first.
    step = spend([a0], [txout(600), txout(300)])
    blocks.append(accept(32, [cb(32, COIN), step, spend([outpoint(sha256d(step)), a1], [txout(1500)])]))
    reasons.append(None)
    # The coin of the block before is spent, and the new coins are not.
    blocks.append(made(33, [cb(33), spend([a0], [txout(1)])]))
    reasons.append(MISSING)
    blocks.append(made(33, [cb(33), spend([a1], [txout(1)])]))
    reasons.append(MISSING)
    blocks.append(accept(33, [cb(33), spend([outpoint(sha256d(step), 1), a2], [txout(1300)])]))
    reasons.append(None)
    return [expect(request(blocks), reasons),
            # The genesis block alone, with its real proof of work.
            expect(request([genesis], check_pow=True), [None])]


def maturity_cases() -> list[dict]:
    """Coinbase maturity at both values. Core selects the value by the height of the coin (line 1433)."""
    requests = []
    for height, coin_height, mature in ((145000, 144970, True), (145000, 144971, False),
                                        # A coin below height 145,000 keeps maturity 30 at a later spend height.
                                        (145001, 144971, True), (145001, 145000, False),
                                        (371337, 371097, True), (371337, 371098, False),
                                        # A height above the spend height gives a negative depth.
                                        (145000, 200000, False)):
        base = Base(height)
        coins = Coins()
        young = coins.add(coin_id(1), 0, COIN, height=coin_height, coinbase=True)
        # A coin that is not a coinbase has no maturity.
        other = coins.add(coin_id(2), 0, COIN, height=coin_height)
        if mature:
            blocks = [base.block([base.coinbase(), spend([young], [txout(COIN)]), spend([other], [txout(COIN)])])]
        else:
            blocks = [base.block([base.coinbase(), spend([young], [txout(COIN)])]),
                      base.block([base.coinbase(), spend([other], [txout(COIN)])])]
        requests.append(expect(base.request(blocks, coins), [None] if mature else [PREMATURE, None]))
    return requests


def value_cases() -> list[dict]:
    """The value checks of CheckTxInputs and the coinbase limit."""
    requests = []
    base = Base(145000)
    coins = Coins()
    big = [coins.add(coin_id(n), 0, 6 * MAX_MONEY // 10) for n in range(2)]
    whole = coins.add(coin_id(2), 0, MAX_MONEY)
    small = coins.add(coin_id(3), 0, 5000)
    requests.append(expect(base.request([
        # Two coins whose sum is above MAX_MONEY.
        base.block([base.coinbase(), spend(big, [txout(1)])]),
        base.block([base.coinbase(), spend([small], [txout(5001)])]),
        # The whole of MAX_MONEY in one coin and one output.
        base.block([base.coinbase(), spend([whole], [txout(MAX_MONEY)]), spend([small], [txout(5000)])]),
    ], coins), ["bad-txns-inputvalues-outofrange", "bad-txns-in-belowout", None]))
    # A coinbase that claims one koinu too much, at three subsidy values.
    for height in (145000, 599999, 600000):
        base = Base(height)
        coins = Coins()
        paying = coins.add(coin_id(1), 0, 50000)
        fee_tx = spend([paying], [txout(37655)])
        limit = subsidy(height) + 12345
        requests.append(expect(base.request([
            base.block([base.coinbase(limit + 1), fee_tx]),
            base.block([base.coinbase(limit), fee_tx]),
        ], coins), ["bad-cb-amount", None]))
        # Without the fee the limit is the subsidy.
        requests.append(expect(base.request([
            base.block([base.coinbase(subsidy(height) + 1)]),
            base.block([base.coinbase(subsidy(height))]),
        ]), ["bad-cb-amount", None]))
    return requests


def domain_cases() -> list[dict]:
    """The arithmetic domain of design record 0010, section 3."""
    base = Base(145000)
    requests = []
    # Nine transactions that each pay MAX_MONEY as a fee stay below 2^63.
    coins = Coins()
    points = [coins.add(coin_id(n), 0, MAX_MONEY) for n in range(10)]
    payers = [spend([p], [txout(0)]) for p in points]
    requests.append(expect(base.request([base.block([base.coinbase()] + payers[:9])], coins), [None]))
    # The tenth fee leaves the range (line 1974).
    requests.append(expect(base.request([base.block([base.coinbase()] + payers)], coins), [], out_of_domain_at=0))
    # Ten coins of MAX_MONEY in one transaction: GetValueIn leaves the range (src/coins.cpp, line 279).
    requests.append(expect(base.request([base.block([base.coinbase(), spend(points, [txout(0)])])], coins),
                           [], out_of_domain_at=0))
    # The range ends at the block. The record of the block before it stays.
    requests.append(expect(base.request([base.block([base.coinbase(subsidy(145000) + 1)]),
                                         base.block([base.coinbase()] + payers)], coins),
                           ["bad-cb-amount"], out_of_domain_at=1))
    # A supplied amount above MAX_MONEY is an error of the adapter.
    coins = Coins()
    coins.add(coin_id(1), 0, MAX_MONEY + 1)
    requests.append(expect(base.request([base.block([base.coinbase()])], coins), [],
                           error={"kind": "block_validate", "reason": "coin_value_out_of_range"}))
    return requests


def sigop_cases() -> list[dict]:
    """The P2SH count and the combined limit of 20,000 signature operations (lines 1961 to 1969)."""
    base = Base(145000)
    multisig = bytes([OP_CHECKMULTISIG])
    heavy = unexecuted(multisig * 100)                 # 100 times 20
    sixteen = unexecuted(bytes([OP_16]) + multisig)    # the accurate count reads OP_16
    one = unexecuted(bytes([OP_1]) + multisig)
    accurate = unexecuted((bytes([OP_16]) + multisig) * 100)   # 1,600, and 2,000 in the inaccurate count
    quarter = unexecuted(multisig * 20)                # 400
    coins = Coins()
    heavies = [coins.add(coin_id(n), 0, 1000, p2sh(heavy)) for n in range(11)]
    extra = {name: coins.add(coin_id(100 + n), 0, 1000, p2sh(script))
             for n, (name, script) in enumerate((("sixteen", sixteen), ("one", one), ("accurate", accurate),
                                                 ("quarter", quarter)))}
    plain = coins.add(coin_id(200), 0, 1000)
    full = [push(heavy)] * 10

    def tx(points, scripts, outputs=None):
        return spend(points, outputs or [txout(1)], scripts)

    cases = [
        # Exactly 20,000 is accepted.
        ([tx(heavies[:10], full)], None),
        ([tx(heavies[:10] + [extra["one"]], full + [push(one)])], "bad-blk-sigops"),
        # The count is cumulative over the transactions of the block.
        ([tx(heavies[:10], full), tx([extra["one"]], [push(one)])], "bad-blk-sigops"),
        # The limit applies to legacy and P2SH operations together: one OP_CHECKSIG in an output,
        # and one in the coinbase.
        ([tx(heavies[:10], full, [txout(1, bytes([OP_CHECKSIG]))])], "bad-blk-sigops"),
        ([tx(heavies[:10], full)], "bad-blk-sigops"),
        # The accurate count: 18,000 and 1,600 and 400 make 20,000. The inaccurate count would make 20,400.
        ([tx(heavies[:9] + [extra["accurate"], extra["quarter"]], full[:9] + [push(accurate), push(quarter)])], None),
        ([tx(heavies[:9] + [extra["accurate"], extra["quarter"], extra["sixteen"]],
             full[:9] + [push(accurate), push(quarter), push(sixteen)])], "bad-blk-sigops"),
        # A scriptSig whose last instruction pushes nothing counts 0: the redeem script is empty.
        ([tx(heavies, full + [push(heavy) + bytes([OP_1])])], script_reason(True, EVAL_FALSE)),
        # A malformed scriptSig counts 0, so the block passes the limit and fails at the script.
        ([tx(heavies, full + [push(heavy)[:-1]])], script_reason(True, BAD_OPCODE)),
        # So does a scriptSig with an opcode above OP_16.
        ([tx(heavies, full + [bytes([OP_NOP]) + push(heavy)])], script_reason(True, SIG_PUSHONLY)),
        # A coin that is not P2SH counts nothing for its scriptSig's last push.
        ([tx(heavies[:10] + [plain], full + [push(heavy)])], None),
    ]
    # The rejected candidates and the first accepted one share a request. Each other accepted
    # block has its own.
    blocks = [base.block([base.coinbase(script=bytes([OP_CHECKSIG]) if index == 4 else TRUE)] + txs)
              for index, (txs, _) in enumerate(cases)]
    rejected = [index for index, (_, reason) in enumerate(cases) if reason is not None]
    accepted = [index for index, (_, reason) in enumerate(cases) if reason is None]
    requests = [expect(base.request([blocks[i] for i in rejected] + [blocks[accepted[0]]], coins),
                       [cases[i][1] for i in rejected] + [None])]
    requests += [expect(base.request([blocks[i]], coins), [None]) for i in accepted[1:]]
    return requests


def script_cases() -> list[dict]:
    """The classification of script failures at the heights of DERSIG and CHECKLOCKTIMEVERIFY (lines 1488 to 1512)."""
    requests = []

    def signature_blocks(base, coins):
        point = coins.add(coin_id(1), 0, 1000, P2PK)
        out = [txout(900)]
        return [base.block([base.coinbase(), signed_spend([point], out, P2PK, strict=False)]),
                base.block([base.coinbase(), signed_spend([point], out, P2PK, strict=False, wrong=True)]),
                base.block([base.coinbase(), signed_spend([point], out, P2PK, wrong=True)]),
                base.block([base.coinbase(), signed_spend([point], out, P2PK)])]

    # Below BIP66Height the flags are P2SH alone: a signature that is not strict DER passes.
    base, coins = Base(1034382), Coins()
    blocks = signature_blocks(base, coins)
    requests.append(expect(base.request([blocks[1], blocks[2], blocks[0]], coins),
                           [script_reason(True, EVAL_FALSE), script_reason(True, EVAL_FALSE), None]))
    # From BIP66Height the encoding fails. The script passes without DERSIG, so the failure is not
    # mandatory. With a wrong signature it fails both runs, and the reason has the first error.
    # At 1,034,384 the predecessor is the block at BIP34Height, and at 3,464,751 the chain is above it.
    for height in (1034383, 1034384, 3464751):
        base, coins = Base(height), Coins()
        requests.append(expect(base.request(signature_blocks(base, coins), coins),
                               [script_reason(False, SIG_DER), script_reason(True, SIG_DER),
                                script_reason(True, EVAL_FALSE), None]))
    # CHECKLOCKTIMEVERIFY is a NOP below BIP65Height. From it, a lock time below the script's value
    # fails, and the script passes without the flag.
    locked = push(script_num(100)) + bytes([OP_CLTV, OP_DROP, OP_1])
    for height, reasons in ((3464750, [None]), (3464751, [script_reason(False, UNSATISFIED_LOCKTIME)]),
                            (3464752, [script_reason(False, UNSATISFIED_LOCKTIME)])):
        base, coins = Base(height), Coins()
        point = coins.add(coin_id(1), 0, 1000, locked)
        requests.append(expect(base.request([base.block([base.coinbase(), spend([point], [txout(1)], sequence=0)])],
                                            coins), reasons))
    # A satisfied lock time passes at BIP65Height.
    base, coins = Base(3464751), Coins()
    point = coins.add(coin_id(1), 0, 1000, locked)
    requests.append(expect(base.request([base.block([base.coinbase(), spend([point], [txout(1)], lock=100, sequence=0)])],
                                        coins), [None]))
    return requests


def bip30_cases() -> list[dict]:
    """BIP30, and Core's skip of it when the ancestor at BIP34Height has the hash BIP34Hash (lines 1869 to 1887)."""
    requests = []
    base = Base(145000)
    coinbase = base.coinbase()
    other = spend([outpoint(coin_id(9))], [txout(1)])
    for collide in (coinbase, other):
        coins = Coins()
        coins.add(sha256d(collide), 3, 1000)
        # The test covers every transaction of the block, before any input is read.
        requests.append(expect(base.request([base.block([coinbase, other])], coins), ["bad-txns-BIP30"]))
    base = Base(3464751)
    coinbase = base.coinbase()
    coins = Coins()
    coins.add(sha256d(coinbase), 0, 1000)
    coins.add(sha256d(coinbase), 5, 2000)
    blocks = [base.block([coinbase])]
    requests.append(expect(base.request(blocks, coins), ["bad-txns-BIP30"]))
    # On mainnet the ancestor never has that hash (design record 0010, section 2). With it, Core
    # skips the test, and the new coinbase entry replaces both earlier coins.
    requests.append(expect(base.request(blocks, coins, ancestor=BIP34_HASH), [None]))
    return requests


def order_cases() -> list[dict]:
    """The five checks run in Core's order: an earlier check gives the reason."""
    base = Base(145000)
    missing = outpoint(coin_id(1))
    bits = int.from_bytes(base.header[72:76], "little")
    txs = [base.coinbase(), spend([missing], [txout(1)])]
    return [expect(base.request([
        # ContextualCheckBlockHeader: other bits.
        base.block(txs, bits=bits + 1),
        # CheckBlock: a wrong Merkle root, and two equal inputs.
        base.block(txs, root=bytes(32)),
        base.block([base.coinbase(), spend([missing, missing], [txout(1)])]),
        # ContextualCheckBlock: a lock time at the height of the block, with a sequence that is not final.
        base.block([base.coinbase(), spend([missing], [txout(1)], lock=base.height, sequence=0)]),
        # ConnectBlock.
        base.block(txs),
    ]), ["bad-diffbits", "bad-txnmrklroot", "bad-txns-inputs-duplicate", "bad-txns-nonfinal", MISSING])]


def adapter_cases() -> list[dict]:
    """Errors of the request: a block that does not read, and blocks that do not form a chain."""
    base = Base(145000)
    good = base.block([base.coinbase()])
    return [
        expect(base.request([good[:-1]]), [], error={"kind": "read", "reason": "truncated", "index": 0}),
        expect(base.request([good, good + b"\x00"]), [],
               error={"kind": "trailing_bytes", "count": 1, "index": 1}),
        # The second block must extend the first, which was accepted.
        expect(base.request([good, good]), [], error={"kind": "block_validate", "reason": "not_linked", "index": 1}),
        expect(base.request([genesis_block()]), [],
               error={"kind": "block_validate", "reason": "genesis_after_start", "index": 0}),
        expect(request([good]), [], error={"kind": "block_validate", "reason": "no_predecessor", "index": 0}),
    ]


_sets = None


def block_validate_sets() -> list[tuple[str, list[dict]]]:
    global _sets
    if _sets is None:
        _sets = [
            ("block.validate genesis chain", genesis_chain_cases()),
            ("block.validate coinbase maturity", maturity_cases()),
            ("block.validate values and coinbase limit", value_cases()),
            ("block.validate arithmetic domain", domain_cases()),
            ("block.validate signature operations", sigop_cases()),
            ("block.validate script failures", script_cases()),
            ("block.validate BIP30", bip30_cases()),
            ("block.validate order and adapter errors", order_cases() + adapter_cases()),
        ]
    return _sets


# The sets of the comparator's --quick run: accepted and rejected blocks, a block outside the
# int64 range, and the adapter errors.
QUICK_SETS = ("block.validate genesis chain", "block.validate arithmetic domain",
              "block.validate order and adapter errors")


# ---------------------------------------------------------------------------
# Real blocks

GENESIS_RANGE = "genesis-10000"


def mainnet_validate_sets(directory) -> list[tuple[str, list[dict]]]:
    """One request with every block of the genesis-to-10,000 range, from the empty coin set.

    The blocks keep their real proof of work, so `check_pow` is set. The request has no expectation
    for the digests: the two programs must agree, and every block must be accepted."""
    try:
        release = fetch_release_blocks.load_release()
    except fetch_release_blocks.AssetError as error:
        raise BlockAssets(str(error)) from None
    entry = next(e for e in release["ranges"] if e["name"] == GENESIS_RANGE)
    blocks = fixture_blocks(pathlib.Path(directory) / GENESIS_RANGE, fetch_release_blocks.sums_text(entry))
    if [record["height"] for record, _ in blocks] != list(range(entry["first"], entry["last"] + 1)) or entry["first"]:
        raise BlockAssets(f"{directory}: the range {GENESIS_RANGE} does not have the heights of release.json")
    req = request([raw for _, raw in blocks], check_pow=True, mode="allow_witness")
    EXPECTATIONS[key(req)] = {"error": None, "accepted": [record["hash"] for record, _ in blocks]}
    return [(f"block.validate mainnet {GENESIS_RANGE}", [req])]


def mainnet_validate_counts() -> dict[str, int]:
    return {"block.validate": 1}


# ---------------------------------------------------------------------------
# Requests that name a file


def file_record(height: int, raw: bytes) -> bytes:
    """One record of a `blocks.bin` file: the height and the length as 4-byte little-endian integers, then the block."""
    return height.to_bytes(4, "little") + len(raw).to_bytes(4, "little") + raw


def file_request(req: dict, path) -> dict:
    """The request `req` with `blocks_file` in the place of `blocks_hex`."""
    return {**{k: v for k, v in req.items() if k != "blocks_hex"}, "blocks_file": str(path)}


def file_twins(requests: list[dict], responses: list[dict], directory) -> list[tuple[dict, dict]]:
    """For each request with one record for each block: the same request with its blocks in a file, and the `ok` object to expect.

    The heights of the records come from the response to `req`, so a rejected candidate and the
    block after it have one height. The expected object is that response's, so the two ways to
    supply the blocks must give one result."""
    twins = []
    for number, (req, response) in enumerate(zip(requests, responses)):
        ok = response.get("ok")
        if not isinstance(ok, dict) or ok.get("out_of_domain_at") is not None or len(ok["blocks"]) != len(req["blocks_hex"]):
            continue
        path = pathlib.Path(directory) / f"twin-{number}.bin"
        path.write_bytes(b"".join(file_record(record["height"], bytes.fromhex(raw))
                                  for record, raw in zip(ok["blocks"], req["blocks_hex"])))
        twins.append((file_request(req, path), ok))
    return twins


def file_faults(directory) -> list[tuple[dict, dict]]:
    """Requests whose file or arguments are faulty, each with the expected error. `{"kind": "request"}` stands for any request error."""
    directory = pathlib.Path(directory)
    genesis = genesis_block()
    example = request([])

    def case(name: str, content: bytes | None) -> dict:
        path = directory / f"fault-{name}.bin"
        if content is not None:
            path.write_bytes(content)
        return file_request(example, path)

    def failure(reason: str, index: int | None = None) -> dict:
        return {"kind": "block_validate", "reason": reason, **({} if index is None else {"index": index})}

    good = file_record(0, genesis)
    return [
        (case("missing", None), failure("file_unreadable")),
        (case("short-head", good + b"\x00" * 5), failure("file_truncated", 1)),
        (case("short-block", good[:-1]), failure("file_truncated", 0)),
        (case("too-long", (0).to_bytes(4, "little") + (0x02000001).to_bytes(4, "little")), failure("file_record_too_long", 0)),
        (case("height", file_record(1, genesis)), failure("file_height", 0)),
        (case("twice", good + file_record(1, genesis)), failure("genesis_after_start", 1)),
        ({**case("both", good), "blocks_hex": []}, {"kind": "request"}),
        ({**file_request(example, ""), "blocks_file": 1}, {"kind": "request"}),
        ({k: v for k, v in case("no-mode", good).items() if k != "mode"}, {"kind": "request"}),
    ]


# ---------------------------------------------------------------------------
# Comparison


def harness_request(req: dict, ours: dict) -> dict:
    """The request that the harness gets: without the block that the oracle found outside the `int64_t` range.

    Core's sums are undefined on that block, so the comparison ends the range before it on both
    sides (design record 0010, section 3)."""
    ok = ours.get("ok")
    if req["op"] != "block.validate" or not isinstance(ok, dict):
        return req
    end = ok.get("out_of_domain_at")
    # A request with `blocks_file` has no list to shorten. `compare` fails it when the oracle ends the range.
    if "blocks_hex" not in req or type(end) is not int or not 0 <= end < len(req["blocks_hex"]):
        return req
    return {**req, "blocks_hex": req["blocks_hex"][:end]}


def is_digest(value) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def malformed(req: dict, ok, oracle: bool) -> str | None:
    """A fault in the form of an `ok` object, or None. The oracle alone has `diagnostic` in each block."""
    if not isinstance(ok, dict) or set(ok) != OK_FIELDS or not isinstance(ok["blocks"], list):
        return "must return exactly the fields " + ", ".join(sorted(OK_FIELDS))
    if not is_digest(ok["set_digest_hex"]) or type(ok["set_coins"]) is not int or ok["set_coins"] < 0:
        return "has a malformed digest of the set"
    end = ok["out_of_domain_at"]
    if oracle:
        if end is not None and (type(end) is not int or end != len(ok["blocks"])):
            return "has an out_of_domain_at that is not the number of its blocks"
        if end is None and "blocks_hex" in req and len(ok["blocks"]) != len(req["blocks_hex"]):
            return "does not have one record for each block"
        if end is not None and "blocks_file" in req:
            return "reports a block of a file outside the domain, and the harness cannot stop before it"
    elif end is not None:
        return "is the harness and reports a block outside the domain"
    fields = BLOCK_FIELDS | ({"diagnostic"} if oracle else set())
    for record in ok["blocks"]:
        if not isinstance(record, dict) or set(record) != fields or type(record["valid"]) is not bool:
            return "has a malformed block record"
        if record["valid"]:
            if any(record[f] is not None for f in ("reject_reason", "dos", "reject_code")):
                return "has a rejection field in an accepted block"
            if not is_digest(record["changes_digest_hex"]) or type(record["spent"]) is not int or type(record["created"]) is not int:
                return "has an accepted block without its changes"
            if (record["set_digest_hex"] is not None) != (record["height"] % SET_DIGEST_INTERVAL == 0):
                return f"has the digest of the set at the wrong heights (height {record['height']})"
        else:
            reason = record["reject_reason"]
            if not isinstance(reason, str) or type(record["dos"]) is not int or type(record["reject_code"]) is not int:
                return "has a rejected block without a reason, a score and a code"
            known = CONNECT_REASONS.get(reason.split(" (")[0])
            if known is not None and (record["dos"], record["reject_code"]) != known:
                return f"returned score {record['dos']} and code {record['reject_code']} for {reason}, and Core's text gives {known[0]} and {known[1]}"
            if any(record[f] is not None for f in ("changes_digest_hex", "spent", "created", "set_digest_hex")):
                return "has a change in a rejected block"
            if oracle and not isinstance(record["diagnostic"], str):
                return "has no Lean diagnostic for a rejection"
    return None


def without_diagnostic(ok: dict) -> dict:
    return {**ok, "out_of_domain_at": None,
            "blocks": [{k: v for k, v in record.items() if k != "diagnostic"} for record in ok["blocks"]]}


def unexpected(req: dict, ours: dict, expected: dict) -> str | None:
    """How the oracle's response differs from the recorded expectation, or None."""
    if expected["error"] is not None:
        if not same(ours.get("error"), expected["error"]):
            return f"expected the error {json.dumps(expected['error'], sort_keys=True)}"
        return None
    if "ok" not in ours:
        return "expected verdicts"
    ok = ours["ok"]
    if "accepted" in expected:
        hashes = [record["hash_display"] for record in ok["blocks"] if record["valid"]]
        if ok["out_of_domain_at"] is not None or hashes != expected["accepted"]:
            first = next((r for r in ok["blocks"] if not r["valid"]), None)
            return f"expected every block to be accepted, and the first rejection is {json.dumps(first)[:300]}"
        if [record["height"] for record in ok["blocks"]] != list(range(len(hashes))):
            return "expected the heights from 0"
        return None
    if ok["out_of_domain_at"] != expected["out_of_domain_at"]:
        return f"expected out_of_domain_at {expected['out_of_domain_at']!r}, got {ok['out_of_domain_at']!r}"
    projected = without_diagnostic(ok)
    for index, (got, want) in enumerate(zip(projected["blocks"], expected["blocks"])):
        for field in sorted(BLOCK_FIELDS):
            if not same(got[field], want[field]):
                return f"block {index}: expected {field} {want[field]!r}, got {got[field]!r}"
    for field in ("set_digest_hex", "set_coins"):
        if not same(ok[field], expected[field]):
            return f"expected {field} {expected[field]!r}, got {ok[field]!r}"
    return None


def compare(req: dict, ours: dict, core: dict, peer: str = "core") -> tuple[str, str] | None:
    """None when both programs give the same result, else a failure code and a message.

    `core` is the harness's response to `harness_request(req, ours)`. The comparison covers every
    field except the oracle's `diagnostic` and `out_of_domain_at`. A recorded expectation must also hold."""
    for side, response in (("oracle", ours), (peer, core)):
        if set(response) - {"id"} not in ({"ok"}, {"error"}):
            return LABEL, f"{side} must return ok or error"
        if "ok" in response:
            fault = malformed(req, response["ok"], side == "oracle")
            if fault:
                return LABEL, f"{side} {fault}"
        elif not isinstance(response["error"], dict) or response["error"].get("kind") not in (
                "read", "trailing_bytes", "block_validate"):
            return LABEL, f"{side} returned an error outside the contract: {json.dumps(response['error'])[:300]}"
    if ("ok" in ours) != ("ok" in core):
        return LABEL, f"one program returned verdicts and the other an error: oracle {json.dumps(ours)[:300]}, {peer} {json.dumps(core)[:300]}"
    if "ok" in ours:
        a, b = without_diagnostic(ours["ok"]), core["ok"]
        for index, (x, y) in enumerate(zip(a["blocks"], b["blocks"])):
            for field in sorted(BLOCK_FIELDS):
                if not same(x[field], y[field]):
                    return LABEL, f"block {index} (height {x['height']}), {field}: oracle {x[field]!r}, {peer} {y[field]!r}"
        if len(a["blocks"]) != len(b["blocks"]):
            return LABEL, f"oracle has {len(a['blocks'])} block records, {peer} has {len(b['blocks'])}"
        for field in ("set_digest_hex", "set_coins"):
            if not same(a[field], b[field]):
                return LABEL, f"{field}: oracle {a[field]!r}, {peer} {b[field]!r}"
    elif not same(ours["error"], core["error"]):
        return LABEL, f"error: oracle {json.dumps(ours['error'], sort_keys=True)}, {peer} {json.dumps(core['error'], sort_keys=True)}"
    expected = EXPECTATIONS.get(key(req))
    if expected is not None:
        fault = unexpected(req, ours, expected)
        if fault:
            return LABEL, f"both programs disagree with the independent expectation: {fault}"
    return None


# ---------------------------------------------------------------------------
# Report


def reasons_reached(requests: list[dict], responses: list[dict]) -> dict[str, int]:
    """Reject reason -> the number of block records of `block.validate` with it, without the text in brackets."""
    counts = {}
    for req, response in zip(requests, responses):
        ok = response.get("ok")
        if req["op"] != "block.validate":
            continue
        if not isinstance(ok, dict):
            error = response.get("error", {})
            name = "error " + str(error.get("reason", error.get("kind")))
            counts[name] = counts.get(name, 0) + 1
            continue
        for record in ok.get("blocks", []):
            name = "valid" if record.get("valid") is True else str(record.get("reject_reason")).split(" (")[0]
            counts[name] = counts.get(name, 0) + 1
    return counts


def reasons_missing(counts: dict[str, int]) -> list[str]:
    """The reachable reasons of design record 0010, section 5, that no block record has."""
    return [f"block.validate {reason}" for reason in CONNECT_REASONS if not counts.get(reason)]
