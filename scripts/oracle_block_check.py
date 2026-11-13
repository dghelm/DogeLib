"""tx.check and block.check requests and their expectations (design record 0010, stage 0010a).

The module builds the requests of the Core comparison and of the oracle test.
No expectation comes from DogeLib. Each one names a reject reason, or none,
that a reader finds in Core's text at the pin (SOURCES.md D106):

- CheckTransaction, src/validation.cpp, lines 527 to 574.
- CheckBlockHeader and CheckBlock, src/validation.cpp, lines 2927 to 3000.
- GetLegacySigOpCount, src/validation.cpp, lines 475 to 487, and
  CScript::GetSigOpCount, src/script/script.cpp, lines 156 to 177.
- ComputeMerkleRoot, src/consensus/merkle.cpp, lines 46 to 137.
- CheckAuxPowProofOfWork, src/dogecoin.cpp, lines 89 to 125, and
  CheckProofOfWork, src/pow.cpp, lines 115 to 129.

The comment before each group of cases gives the lines that fix its reasons.
The module computes transaction IDs, Merkle roots and block hashes with
hashlib, and scrypt digests with hashlib.scrypt.

The blocks are the mainnet genesis block, synthetic blocks, and synthetic
transaction lists after the real full headers of
tests/block/mainnet-auxpow-activation-full-headers.

The module also reads real mainnet blocks from fixtures of
scripts/fetch_blocks.py: the committed blocks at the rule changes, in
tests/block/mainnet-blocks/rule-changes, and the two ranges that
scripts/fetch_release_blocks.py restores from a GitHub release. The main
chain holds each of these blocks, so each one must pass CheckBlock with both
flags. That expectation comes from the chain, and the hash, the size and the
number of transactions of each block come from the fixture's manifest.
"""
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks  # noqa: E402
import fetch_release_blocks  # noqa: E402

FULL_HEADERS = ROOT / "tests/block/mainnet-auxpow-activation-full-headers/headers.txt"
MAINNET_BLOCKS = ROOT / "tests/block/mainnet-blocks"
RULE_CHANGES = MAINNET_BLOCKS / "rule-changes"

COIN = 100000000
# src/amount.h, lines 18 and 32: MAX_MONEY is 10,000,000,000 coins.
MAX_MONEY = 10000000000 * COIN
# src/consensus/consensus.h, lines 17 and 19, and WITNESS_SCALE_FACTOR 4:
# a block holds at most 80,000 / 4 legacy signature operations.
MAX_BLOCK_BASE_SIZE = 1000000
MAX_BLOCK_SIGOPS = 20000
# src/serialize.h: the largest count that ReadCompactSize returns.
MAX_SIZE = 0x02000000
REJECT_INVALID = 16
INT64_MIN = -2**63
INT64_MAX = 2**63 - 1

# Reject reason -> the score of its state.DoS call (lines 531 to 570).
TX_REASONS = {
    "bad-txns-vin-empty": 10,
    "bad-txns-vout-empty": 10,
    "bad-txns-oversize": 100,
    "bad-txns-vout-negative": 100,
    "bad-txns-vout-toolarge": 100,
    "bad-txns-txouttotal-toolarge": 100,
    "bad-txns-inputs-duplicate": 100,
    "bad-cb-length": 100,
    "bad-txns-prevout-null": 10,
}
# Reject reason -> the score and the corruption flag of its state.DoS call
# (lines 2934 to 2994). A failed transaction keeps the score of
# CheckTransaction, because line 2985 calls state.Invalid, which adds no score.
BLOCK_REASONS = {
    "high-hash": (50, False),
    "bad-txnmrklroot": (100, True),
    "bad-txns-duplicate": (100, True),
    "bad-blk-length": (100, False),
    "bad-cb-missing": (100, False),
    "bad-cb-multiple": (100, False),
    "bad-blk-sigops": (100, False),
    **{reason: (score, False) for reason, score in TX_REASONS.items()},
}
# The block size test (line 2972) comes before the transaction loop, and a
# block holds each of its transactions. So CheckBlock never returns this reason.
UNREACHABLE_IN_BLOCK = {"bad-txns-oversize"}

LABELS = {"tx.check": "TX_CHECK", "block.check": "BLOCK_CHECK"}
VERDICT_FIELDS = {"valid", "reject_reason", "dos", "reject_code"}
OK_FIELDS = {
    "tx.check": VERDICT_FIELDS | {"legacy_sigops", "base_size"},
    "block.check": VERDICT_FIELDS | {"corruption_possible", "legacy_sigops", "base_size", "transactions",
                                     "hash_hex", "hash_display"},
}
TRUNCATED = {"kind": "read", "reason": "truncated"}
NON_CANONICAL = {"kind": "read", "reason": "non_canonical"}
TOO_LARGE = {"kind": "read", "reason": "too_large"}
UNKNOWN_OPTIONAL_DATA = {"kind": "read", "reason": "unknown_optional_data"}
BOTH_MODES = ("base", "allow_witness")
ALL_FLAGS = ((False, False), (False, True), (True, False), (True, True))


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def le(n: int, size: int) -> bytes:
    return n.to_bytes(size, "little")


def compact_size(n: int) -> bytes:
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + le(n, 2)
    if n <= 0xffffffff:
        return b"\xfe" + le(n, 4)
    return b"\xff" + le(n, 8)


# ---------------------------------------------------------------------------
# Transactions

NULL_PREVOUT = bytes(32) + b"\xff" * 4


def prevout(tag: int, index: int = 0) -> bytes:
    """An outpoint that is not null: 32 equal nonzero bytes and an index."""
    assert 0 < tag < 256
    return bytes([tag]) * 32 + le(index, 4)


def txin(prev: bytes, script: bytes = b"", sequence: int = 0xffffffff) -> bytes:
    return prev + compact_size(len(script)) + script + le(sequence, 4)


def txout(amount: int, script: bytes = b"\x51") -> bytes:
    """An output. The amount is an int64 in two's complement."""
    return le(amount % 2**64, 8) + compact_size(len(script)) + script


def transaction(inputs: list[bytes], outputs: list[bytes], version: int = 1, lock: int = 0) -> bytes:
    """A transaction in the base format."""
    return (le(version % 2**32, 4) + compact_size(len(inputs)) + b"".join(inputs) +
            compact_size(len(outputs)) + b"".join(outputs) + le(lock, 4))


class Extended:
    """A transaction in the extended format: its bytes in a block, and its base bytes."""

    def __init__(self, inputs: list[bytes], outputs: list[bytes], stacks: list[list[bytes]], flags: int = 1):
        witness = b"".join(compact_size(len(stack)) + b"".join(compact_size(len(item)) + item for item in stack)
                           for stack in stacks)
        self.wire = (le(1, 4) + bytes([0, flags]) + compact_size(len(inputs)) + b"".join(inputs) +
                     compact_size(len(outputs)) + b"".join(outputs) + witness + bytes(4))
        self.base = transaction(inputs, outputs)


def wire_of(tx) -> bytes:
    return tx.wire if isinstance(tx, Extended) else tx


def base_of(tx) -> bytes:
    return tx.base if isinstance(tx, Extended) else tx


def coinbase(script: bytes = b"\x51\x51", outputs: list[bytes] | None = None) -> bytes:
    """A transaction with one input, whose outpoint is null."""
    return transaction([txin(NULL_PREVOUT, script)], [txout(50 * COIN)] if outputs is None else outputs)


def spend(tag: int, script: bytes = b"", outputs: list[bytes] | None = None) -> bytes:
    """A transaction with one input, whose outpoint is `prevout(tag)`."""
    return transaction([txin(prevout(tag), script)], [txout(1)] if outputs is None else outputs)


def padded(build, size: int, measure=len):
    """`build(n)` for the `n` that gives exactly `size` bytes."""
    n = size - measure(build(0))
    for guess in range(n, n - 10, -1):
        if guess >= 0 and measure(build(guess)) == size:
            return build(guess)
    raise AssertionError(f"no padding gives {size} bytes")


def one_push(n: int) -> bytes:
    """A script of one instruction: OP_PUSHDATA4 with `n` zero bytes. It has no signature operation.

    The oracle needs time that grows with the square of the number of instructions in a script.
    One large push keeps a script of a megabyte fast in both programs."""
    return b"\x4e" + le(n, 4) + bytes(n)


def spend_of_size(size: int, outputs: list[bytes] | None = None) -> bytes:
    """A spend of `size` bytes. Its scriptSig is one push."""
    return padded(lambda n: spend(0xee, one_push(n), outputs), size)


def extended_spend_of_size(size: int) -> Extended:
    """An extended spend whose base form has `size` bytes, with a witness stack of two items."""
    return padded(lambda n: Extended([txin(prevout(0xee), one_push(n))], [txout(1)], [[bytes(1000), bytes(996)]]),
                  size, lambda tx: len(tx.base))


def coinbase_of_size(size: int) -> bytes:
    """A coinbase of `size` bytes. Its output script is one push."""
    return padded(lambda n: coinbase(outputs=[txout(50 * COIN, one_push(n))]), size)


# ---------------------------------------------------------------------------
# Blocks

TIME = 1386325540
BITS = 0x1e0ffff0


def merkle(leaves: list[bytes]) -> tuple[bytes, bool]:
    """The Merkle root of `leaves` and the mutation flag (src/consensus/merkle.cpp, lines 46 to 137).

    Core sets the flag when it joins two equal hashes that are both in the tree.
    A hash that Core joins with itself at the odd end of a level does not set it."""
    if not leaves:
        return bytes(32), False
    level, mutated = list(leaves), False
    while len(level) > 1:
        mutated = mutated or any(level[i] == level[i + 1] for i in range(0, len(level) - 1, 2))
        if len(level) % 2:
            level.append(level[-1])
        level = [sha256d(level[i] + level[i + 1]) for i in range(0, len(level), 2)]
    return level[0], mutated


def root_of(txs: list) -> bytes:
    return merkle([sha256d(base_of(tx)) for tx in txs])[0]


def is_mutated(txs: list) -> bool:
    return merkle([sha256d(base_of(tx)) for tx in txs])[1]


def pure_header(root: bytes, version: int = 1, prev: bytes = bytes(32), time: int = TIME, bits: int = BITS,
                nonce: int = 0) -> bytes:
    assert len(root) == 32 and len(prev) == 32
    return le(version, 4) + prev + root + le(time, 4) + le(bits, 4) + le(nonce, 4)


def block(txs: list, root: bytes | None = None, header: bytes | None = None, count: bytes | None = None,
          **fields) -> bytes:
    """A block. Without `root` or `header`, the header holds the Merkle root of `txs`."""
    if header is None:
        header = pure_header(root_of(txs) if root is None else root, **fields)
    return header + (compact_size(len(txs)) if count is None else count) + b"".join(wire_of(tx) for tx in txs)


def target_of(bits: int) -> int:
    """The target of a compact value with a positive mantissa and no overflow."""
    size, word = bits >> 24, bits & 0x007fffff
    assert word and not bits & 0x00800000 and size <= 32
    return word >> 8 * (3 - size) if size <= 3 else word << 8 * (size - 3)


def scrypt_of(header: bytes) -> int:
    """The scrypt digest of an 80-byte header, as the integer that Core compares with the target."""
    assert len(header) == 80
    return int.from_bytes(hashlib.scrypt(header, salt=header, n=1024, r=1, p=1, dklen=32), "little")


def without_work(header: bytes, bits: int = BITS) -> bytes:
    """The header, after a check that its scrypt digest is above the target of `bits`."""
    assert scrypt_of(header[:80]) > target_of(bits)
    return header


def genesis_block() -> bytes:
    """The mainnet genesis block (src/chainparams.cpp, lines 20 to 57 and 155 to 158)."""
    script_sig = bytes.fromhex("04ffff001d0104") + b"\x08" + b"Nintondo"
    script_pubkey = bytes.fromhex(
        "41040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b"
        "51850b4acf21b179c45070ac7b03a9ac")
    tx = transaction([txin(NULL_PREVOUT, script_sig)], [txout(88 * COIN, script_pubkey)])
    data = block([tx], time=1386325540, bits=0x1e0ffff0, nonce=99943)
    # Core asserts this hash at line 158.
    assert sha256d(data[:80])[::-1].hex() == "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
    assert scrypt_of(data[:80]) <= target_of(0x1e0ffff0)
    return data


def full_headers() -> list[tuple[int, bytes]]:
    """The real full headers of mainnet heights 371,320 to 371,340, each with its AuxPoW payload if it has one."""
    rows = [line.split(" ") for line in FULL_HEADERS.read_text().splitlines()]
    assert len(rows) == 21
    return [(int(height), bytes.fromhex(data)) for height, data in rows]


# ---------------------------------------------------------------------------
# Requests and expectations

EXPECTATIONS = {}


def key(req: dict) -> str:
    """A digest of a request without its id. Some requests have two megabytes of hexadecimal digits."""
    text = json.dumps({k: v for k, v in req.items() if k != "id"}, sort_keys=True)
    return hashlib.sha256(text.encode()).hexdigest()


def expect(req: dict, verdict, **fields) -> dict:
    """Record the expectation of a request, and return the request.

    `verdict` is None for a valid object, a reject reason, or an `error` object.
    `fields` are further expected fields of `ok`.
    Two sets can hold one request. Their expectations must agree, and the record keeps the fields of both."""
    assert verdict is None or isinstance(verdict, dict) or verdict in BLOCK_REASONS
    expected = {"verdict": verdict, **fields}
    recorded = EXPECTATIONS.setdefault(key(req), expected)
    assert all(recorded.get(field, value) == value for field, value in expected.items())
    recorded.update(expected)
    return req


def tx_request(data: bytes, mode: str = "base", duplicates: bool = True) -> dict:
    return {"op": "tx.check", "tx_hex": data.hex(), "mode": mode, "check_duplicate_inputs": duplicates}


def block_request(data: bytes, mode: str = "base", pow: bool = False, merkle_root: bool = True) -> dict:
    return {"op": "block.check", "block_hex": data.hex(), "mode": mode, "check_pow": pow,
            "check_merkle_root": merkle_root}


def by_flags(data: bytes, verdicts: dict, mode: str = "base", **fields) -> list[dict]:
    """One block.check request for each (check_pow, check_merkle_root) pair of `verdicts`."""
    return [expect(block_request(data, mode, pow, merkle_root), verdict, **(fields if verdict is None else {}))
            for (pow, merkle_root), verdict in verdicts.items()]


SAME = object()


def tx_case(data: bytes, verdict, without=SAME, coinbase: bool = False, modes=BOTH_MODES) -> dict:
    """A transaction with its verdict under check_duplicate_inputs true, and under false when that differs.

    `coinbase` says that the transaction has exactly one input, whose outpoint is null."""
    return {"data": data, "verdict": verdict, "without": verdict if without is SAME else without,
            "coinbase": coinbase, "modes": modes}


A, B, C = prevout(0xa1), prevout(0xb2), prevout(0xc3)
OUT = txout(1)
CB = coinbase()
CB2 = coinbase(b"\x52\x52")
TX_A, TX_B, TX_C, TX_D, TX_E = (spend(tag) for tag in (1, 2, 3, 4, 5))


def transaction_cases() -> list[dict]:
    """Transactions for each statement of CheckTransaction (lines 527 to 574), in source order."""
    half = MAX_MONEY // 2
    cases = [
        # Lines 530 and 531: no inputs. In base mode the byte after the version is the input count.
        tx_case(transaction([], [OUT]), "bad-txns-vin-empty", modes=("base",)),
        # The 10-byte form: no inputs and no outputs. In witness mode the two zero bytes
        # are the empty input list and a flags byte of 0, which leaves the outputs empty.
        tx_case(transaction([], []), "bad-txns-vin-empty"),
        # The input test comes before every output test.
        tx_case(transaction([], [txout(-1)]), "bad-txns-vin-empty", modes=("base",)),
        tx_case(transaction([], [txout(MAX_MONEY + 1)]), "bad-txns-vin-empty", modes=("base",)),
        # Lines 532 and 533: no outputs. The test comes before the duplicate and coinbase tests.
        tx_case(transaction([txin(A)], []), "bad-txns-vout-empty"),
        tx_case(transaction([txin(A), txin(A)], []), "bad-txns-vout-empty"),
        tx_case(transaction([txin(NULL_PREVOUT)], []), "bad-txns-vout-empty", coinbase=True),
        tx_case(transaction([txin(NULL_PREVOUT), txin(A)], []), "bad-txns-vout-empty"),
        # Lines 542 and 543: a negative output, at any position.
        tx_case(transaction([txin(A)], [txout(-1)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(A)], [txout(INT64_MIN)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(A)], [OUT, txout(-1)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(A)], [OUT, OUT, txout(INT64_MIN)]), "bad-txns-vout-negative"),
        # The sign test of an output comes before its two bound tests.
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(-1)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(A)], [txout(-1), txout(MAX_MONEY + 1)]), "bad-txns-vout-negative"),
        # The output loop comes before the duplicate, coinbase and null tests.
        tx_case(transaction([txin(A), txin(A)], [txout(-1)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(NULL_PREVOUT)], [txout(-1)]), "bad-txns-vout-negative", coinbase=True),
        tx_case(transaction([txin(A), txin(NULL_PREVOUT)], [txout(-1)]), "bad-txns-vout-negative"),
        # Lines 544 and 545: an output above MAX_MONEY. MAX_MONEY itself passes.
        tx_case(transaction([txin(A)], [txout(MAX_MONEY)]), None),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(A)], [txout(INT64_MAX)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(A)], [txout(0), txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY + 1), txout(-1)]), "bad-txns-vout-toolarge"),
        # The bound of one output comes before the bound of the sum.
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(A), txin(A)], [txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(NULL_PREVOUT, b"")], [txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge",
                coinbase=True),
        # Lines 546 to 548: the sum of the outputs so far is above MAX_MONEY. A sum of MAX_MONEY passes.
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(0)]), None),
        tx_case(transaction([txin(A)], [txout(half), txout(half)]), None),
        tx_case(transaction([txin(A)], [txout(0), txout(0), txout(0)]), None),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(1)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A)], [txout(half), txout(half + 1)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A)], [txout(1), txout(MAX_MONEY)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(MAX_MONEY)]), "bad-txns-txouttotal-toolarge"),
        # The loop returns at the second output, and never reads the third.
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(1), txout(0)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(1), txout(-1)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(1), txout(MAX_MONEY + 1)]),
                "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A), txin(A)], [txout(MAX_MONEY), txout(1)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(NULL_PREVOUT, b"\x51")], [txout(MAX_MONEY), txout(1)]),
                "bad-txns-txouttotal-toolarge", coinbase=True),
        # Lines 552 to 558: two inputs with one outpoint, only with the flag.
        tx_case(transaction([txin(A), txin(A)], [OUT]), "bad-txns-inputs-duplicate", None),
        tx_case(transaction([txin(A), txin(B), txin(A)], [OUT]), "bad-txns-inputs-duplicate", None),
        tx_case(transaction([txin(A), txin(B), txin(B)], [OUT]), "bad-txns-inputs-duplicate", None),
        # The set compares outpoints only. The scripts and the sequences differ here.
        tx_case(transaction([txin(A, b"\x51", 0), txin(A, b"\x52", 1)], [OUT]), "bad-txns-inputs-duplicate", None),
        # An equal hash with another index, and an equal index with another hash, are not duplicates.
        tx_case(transaction([txin(prevout(0xa1, 0)), txin(prevout(0xa1, 1))], [OUT]), None),
        tx_case(transaction([txin(A), txin(B), txin(C)], [OUT]), None),
        # The duplicate test comes before the null test. Two inputs are never a coinbase.
        tx_case(transaction([txin(NULL_PREVOUT), txin(NULL_PREVOUT)], [OUT]),
                "bad-txns-inputs-duplicate", "bad-txns-prevout-null"),
        tx_case(transaction([txin(NULL_PREVOUT), txin(A), txin(NULL_PREVOUT)], [OUT]),
                "bad-txns-inputs-duplicate", "bad-txns-prevout-null"),
        # Lines 561 to 564: the scriptSig of a coinbase has 2 to 100 bytes.
        tx_case(coinbase(b""), "bad-cb-length", coinbase=True),
        tx_case(coinbase(b"\x51"), "bad-cb-length", coinbase=True),
        tx_case(coinbase(b"\x51" * 2), None, coinbase=True),
        tx_case(coinbase(b"\x51" * 100), None, coinbase=True),
        tx_case(coinbase(b"\x51" * 101), "bad-cb-length", coinbase=True),
        tx_case(coinbase(b"\x51" * 1000), "bad-cb-length", coinbase=True),
        # Lines 566 to 570: a null outpoint in a transaction that is not a coinbase, at each position.
        tx_case(transaction([txin(NULL_PREVOUT), txin(A)], [OUT]), "bad-txns-prevout-null"),
        tx_case(transaction([txin(A), txin(NULL_PREVOUT)], [OUT]), "bad-txns-prevout-null"),
        tx_case(transaction([txin(A), txin(B), txin(NULL_PREVOUT)], [OUT]), "bad-txns-prevout-null"),
        # The length rule of a coinbase does not apply to it.
        tx_case(transaction([txin(NULL_PREVOUT, b""), txin(A, b"")], [OUT]), "bad-txns-prevout-null"),
        # COutPoint::IsNull needs a zero hash and the index 0xffffffff (src/primitives/transaction.h, line 41).
        tx_case(transaction([txin(bytes(32) + le(0, 4))], [OUT]), None),
        tx_case(transaction([txin(bytes(32) + le(0xfffffffe, 4))], [OUT]), None),
        tx_case(transaction([txin(prevout(0xff, 0xffffffff))], [OUT]), None),
        tx_case(transaction([txin(A), txin(bytes(32) + le(0, 4)), txin(prevout(0xff, 0xffffffff))], [OUT]), None),
        # No statement reads the version, the lock time or a sequence.
        tx_case(transaction([txin(A, b"", 0)], [OUT], version=0, lock=0xffffffff), None),
        tx_case(transaction([txin(A)], [OUT], version=-1), None),
        tx_case(transaction([txin(A)], [OUT], version=2, lock=500000000), None),
    ]
    return cases


def tx_reason_requests(cases: list[dict]) -> list[dict]:
    """Each case through tx.check, with and without the duplicate test, in each of its modes."""
    return [expect(tx_request(c["data"], mode, duplicates), c["verdict"] if duplicates else c["without"],
                   base_size=len(c["data"]))
            for c in cases for mode in c["modes"] for duplicates in (True, False)]


def tx_in_block_requests(cases: list[dict]) -> list[dict]:
    """Each case inside a block with a correct Merkle root and no proof-of-work check.

    A coinbase case is the only transaction. Any other case follows a valid coinbase,
    and again a valid coinbase and a valid spend. The block passes every test before the
    transaction loop (lines 2972 to 2980), and CheckBlock calls CheckTransaction with the
    duplicate test (line 2984). So the block gets the verdict of the case with the flag."""
    requests = []
    for c in cases:
        lists = [[c["data"]]] if c["coinbase"] else [[CB, c["data"]], [CB, TX_A, c["data"]]]
        for txs in lists:
            for mode in c["modes"]:
                requests.append(expect(block_request(block(txs), mode), c["verdict"], transactions=len(txs)))
    return requests


def known_answers() -> list[dict]:
    """The genesis block, and one small request for each reachable reason of both functions."""
    genesis = genesis_block()
    genesis_tx = genesis[81:]
    display = "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
    requests = []
    # Core's own genesis block passes every test. Its output script is a push of 65 bytes and
    # OP_CHECKSIG, and its scriptSig holds three pushes, so it has one signature operation.
    for mode in BOTH_MODES:
        requests += by_flags(genesis, dict.fromkeys(ALL_FLAGS), mode, legacy_sigops=1, base_size=len(genesis),
                             transactions=1, hash_display=display)
        requests.append(expect(tx_request(genesis_tx, mode), None, legacy_sigops=1, base_size=len(genesis_tx)))
    # Lines 2933 and 2934: another nonce gives a scrypt digest above the target.
    worse = without_work(genesis[:76] + le(99944, 4)) + genesis[80:]
    requests += by_flags(worse, {(True, True): "high-hash", (True, False): "high-hash",
                                 (False, True): None, (False, False): None})
    # Line 2955: the header holds another root. The changed header has no work either.
    flipped = without_work(genesis[:36] + bytes([genesis[36] ^ 1]) + genesis[37:80]) + genesis[80:]
    requests += by_flags(flipped, {(True, True): "high-hash", (False, True): "bad-txnmrklroot",
                                   (False, False): None})
    # The genesis header has work, so the test of the root follows the header test.
    other = genesis[:80] + block([CB, TX_A])[80:]
    requests += by_flags(other, {(True, True): "bad-txnmrklroot", (True, False): None})
    # Lines 2961 and 2962: [CB, a, b, b] has the root of [CB, a, b], and Core joins b with b.
    assert root_of([CB, TX_A, TX_B, TX_B]) == root_of([CB, TX_A, TX_B])
    requests += by_flags(block([CB, TX_A, TX_B, TX_B]), {(False, True): "bad-txns-duplicate", (False, False): None})
    # Line 2972: no transactions. The Merkle root of an empty list is zero (merkle.cpp, lines 48 to 52).
    requests += by_flags(block([]), {(False, True): "bad-blk-length", (False, False): "bad-blk-length"})
    # Line 2976: the first transaction is not a coinbase.
    requests.append(expect(block_request(block([TX_A])), "bad-cb-missing"))
    # Lines 2978 to 2980: a later transaction is a coinbase.
    requests.append(expect(block_request(block([CB, CB2])), "bad-cb-multiple"))
    # Line 2993: 20,001 signature operations. 20,000 pass.
    for count, verdict in ((MAX_BLOCK_SIGOPS, None), (MAX_BLOCK_SIGOPS + 1, "bad-blk-sigops")):
        data = block([coinbase(outputs=[txout(COIN, b"\xac" * count)])])
        requests.append(expect(block_request(data), verdict, legacy_sigops=count))
    minimal = [
        tx_case(transaction([], [OUT]), "bad-txns-vin-empty", modes=("base",)),
        tx_case(transaction([txin(A)], []), "bad-txns-vout-empty"),
        tx_case(transaction([txin(A)], [txout(-1)]), "bad-txns-vout-negative"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY + 1)]), "bad-txns-vout-toolarge"),
        tx_case(transaction([txin(A)], [txout(MAX_MONEY), txout(1)]), "bad-txns-txouttotal-toolarge"),
        tx_case(transaction([txin(A), txin(A)], [OUT]), "bad-txns-inputs-duplicate", None),
        tx_case(coinbase(b"\x51"), "bad-cb-length", coinbase=True),
        tx_case(transaction([txin(A), txin(NULL_PREVOUT)], [OUT]), "bad-txns-prevout-null"),
        tx_case(TX_A, None),
        tx_case(CB, None, coinbase=True),
    ]
    requests += [expect(tx_request(c["data"], "base", duplicates), c["verdict"] if duplicates else c["without"],
                        legacy_sigops=0, base_size=len(c["data"]))
                 for c in minimal for duplicates in (True, False)]
    requests += [expect(block_request(block([c["data"]] if c["coinbase"] else [CB, c["data"]])), c["verdict"],
                        legacy_sigops=0)
                 for c in minimal]
    # Reader errors, as tx.decode_witness reports them.
    requests.append(expect(tx_request(TX_A[:-1]), TRUNCATED))
    requests.append(expect(tx_request(TX_A + b"\x00"), {"kind": "trailing_bytes", "count": 1}))
    requests.append(expect(block_request(genesis[:-1]), TRUNCATED))
    requests.append(expect(block_request(genesis + b"\x00\x00"), {"kind": "trailing_bytes", "count": 2}))
    return requests


def block_reason_requests() -> list[dict]:
    """Blocks for each statement of CheckBlock (lines 2939 to 3000), in source order."""
    genesis = genesis_block()
    requests = []
    high = {(True, True): "high-hash", (True, False): "high-hash"}

    def synthetic(txs, verdict, without_merkle=SAME, mode="base", **fields):
        """A block without work: `verdict` with the Merkle test, and `high-hash` with the header test."""
        data = block(txs, **fields)
        without_work(data[:80])
        return by_flags(data, {(False, True): verdict,
                               (False, False): verdict if without_merkle is SAME else without_merkle, **high}, mode)

    # Valid lists. Each block passes without the header test, and has no work.
    for txs in ([CB], [CB, TX_A], [CB, TX_A, TX_B], [CB, TX_A, TX_B, TX_C, TX_D, TX_E]):
        for mode in BOTH_MODES:
            requests += synthetic(txs, None, mode=mode)
    # Lines 2933 and 2934, with CheckProofOfWork (src/pow.cpp, lines 124 and 125): a target that is
    # negative, zero, an overflow or above the mainnet limit fails for every digest.
    # The limit is 2^236 - 1 (src/chainparams.cpp, line 88), and 0x1e100000 gives 2^236.
    for bits in (0x207fffff, 0x1e100000, 0x1f00ffff, 0, 0x1e000000, 0x1e80ffff, 0x23000001, 0xff7fffff):
        data = block([CB, TX_A], bits=bits)
        requests += by_flags(data, {**high, (False, True): None, (False, False): None})
    # The header test comes before every other test.
    for txs, root in (([], bytes(32)), ([TX_A], None), ([CB, CB2], None), ([CB, TX_A, TX_B, TX_B], None),
                      ([CB, TX_A], bytes(32))):
        data = block(txs, root=root)
        without_work(data[:80])
        requests += by_flags(data, high)
    # The genesis header has work. With it, each later test decides.
    for txs, verdicts in (
            ([], {(True, True): "bad-txnmrklroot", (True, False): "bad-blk-length"}),
            ([TX_A], {(True, True): "bad-txnmrklroot", (True, False): "bad-cb-missing"}),
            ([CB, CB2], {(True, True): "bad-txnmrklroot", (True, False): "bad-cb-multiple"}),
            ([CB, TX_A, TX_B], {(True, True): "bad-txnmrklroot", (True, False): None}),
            ([coinbase(b"")], {(True, True): "bad-txnmrklroot", (True, False): "bad-cb-length"})):
        requests += by_flags(block(txs, header=genesis[:80]), verdicts)

    # Lines 2952 to 2956: the root of the header is not the root of the list.
    good = root_of([CB, TX_A])
    for root in (bytes(32), bytes([0xff]) * 32, good[::-1], bytes([good[0] ^ 1]) + good[1:],
                 good[:31] + bytes([good[31] ^ 0x80]), root_of([CB]), root_of([TX_A, CB]), sha256d(CB),
                 root_of([CB, TX_A, TX_A])):
        assert root != good
        requests += synthetic([CB, TX_A], "bad-txnmrklroot", None, root=root)
    # The test of the root comes before the mutation test and before every later test.
    for txs, later in (([CB, TX_A, TX_B, TX_B], None), ([], "bad-blk-length"), ([TX_A], "bad-cb-missing"),
                       ([CB, CB2], "bad-cb-multiple"), ([CB, coinbase(b"")], "bad-cb-multiple"),
                       ([coinbase(b"")], "bad-cb-length"), ([CB, transaction([txin(A)], [])], "bad-txns-vout-empty"),
                       ([coinbase(outputs=[txout(0, b"\xac" * 20001)])], "bad-blk-sigops")):
        requests += synthetic(txs, "bad-txnmrklroot", later, root=bytes([0x77]) * 32)

    # Lines 2958 to 2962: the mutation of CVE-2012-2459. Each pair of lists has one root.
    # Core joins two equal hashes in the longer list, and none in the shorter.
    for short, long in (([CB, TX_A, TX_B], [CB, TX_A, TX_B, TX_B]),
                        ([CB, TX_A, TX_A], [CB, TX_A, TX_A, TX_A]),
                        ([CB, TX_A, TX_B, TX_C, TX_D], [CB, TX_A, TX_B, TX_C, TX_D, TX_D]),
                        ([CB, TX_A, TX_B, TX_C, TX_D, TX_E], [CB, TX_A, TX_B, TX_C, TX_D, TX_E, TX_D, TX_E]),
                        ([CB, TX_A, TX_B, TX_C, TX_D], [CB, TX_A, TX_B, TX_C, TX_D, TX_D, TX_D, TX_D])):
        assert root_of(short) == root_of(long) and not is_mutated(short) and is_mutated(long)
        requests += synthetic(short, None)
        # Without the Merkle test the longer list passes: no later statement compares transactions.
        requests += synthetic(long, "bad-txns-duplicate", None)
    # [CB, a] and [CB, a, a] have different roots, so the second is not a mutation of the first.
    assert root_of([CB, TX_A]) != root_of([CB, TX_A, TX_A]) and not is_mutated([CB, TX_A, TX_A])
    requests += synthetic([CB, TX_A, TX_A], "bad-txnmrklroot", None, root=root_of([CB, TX_A]))
    # Two equal hashes in one pair set the flag at any position, also under the block's own root.
    for txs, later in (([CB, CB], "bad-cb-multiple"), ([TX_A, TX_A], "bad-cb-missing"),
                       ([CB, TX_A, TX_B, TX_B, TX_C], None), ([CB, TX_A, TX_B, TX_B, TX_C, TX_D], None),
                       ([CB, TX_A, CB, TX_A], "bad-cb-multiple"),
                       ([CB, TX_A, transaction([txin(A)], []), transaction([txin(A)], [])], "bad-txns-vout-empty")):
        assert is_mutated(txs)
        requests += synthetic(txs, "bad-txns-duplicate", later)
    # Equal transactions in different pairs do not set the flag.
    for txs in ([CB, TX_A, TX_A, TX_B], [CB, TX_A, TX_B, TX_A], [CB, TX_A, TX_A]):
        assert not is_mutated(txs)
        requests += synthetic(txs, None)

    # Lines 2971 to 2973: no transactions. The Merkle root of an empty list is zero.
    for mode in BOTH_MODES:
        requests += synthetic([], "bad-blk-length", mode=mode)
    requests += synthetic([], "bad-txnmrklroot", "bad-blk-length", root=bytes([1]) * 32)

    # Lines 2976 and 2977: the first transaction is not a coinbase. The test comes before lines 2978 to 2986.
    not_coinbase = [
        TX_A,
        transaction([txin(bytes(32) + le(0, 4))], [OUT]),
        transaction([txin(prevout(0xff, 0xffffffff))], [OUT]),
        transaction([txin(NULL_PREVOUT), txin(A)], [OUT]),
        transaction([txin(NULL_PREVOUT), txin(NULL_PREVOUT)], [OUT]),
        transaction([txin(A)], [txout(-1)]),
        transaction([txin(A)], []),
    ]
    for first in not_coinbase:
        for rest in ([], [TX_B], [CB], [CB, CB2]):
            requests += synthetic([first, *rest], "bad-cb-missing")
    # A first transaction with no inputs, in base mode.
    requests += synthetic([transaction([], [OUT])], "bad-cb-missing")
    requests += synthetic([transaction([], [OUT]), CB], "bad-cb-missing")

    # Lines 2978 to 2980: a later coinbase, at each position. IsCoinBase does not read the scriptSig,
    # and the test comes before the transaction loop.
    for txs in ([CB, CB2], [CB, TX_A, CB2], [CB, CB2, TX_A], [CB, TX_A, TX_B, CB2], [CB, coinbase(b"")],
                [coinbase(b""), CB], [coinbase(b"\x51" * 101), coinbase(b"")],
                [CB, transaction([txin(A)], [txout(-1)]), CB2],
                [CB, coinbase(outputs=[])], [CB, CB2, coinbase(b"\x53\x53")]):
        requests += synthetic(txs, "bad-cb-multiple")

    # Lines 2983 to 2986: the first failing transaction decides, and the loop comes before the sigop test.
    negative = transaction([txin(A)], [txout(-1)])
    duplicate = transaction([txin(B), txin(B)], [OUT])
    empty = transaction([txin(C)], [])
    many = coinbase(outputs=[txout(0, b"\xac" * 20001)])
    for txs, verdict in (([CB, negative, duplicate], "bad-txns-vout-negative"),
                         ([CB, duplicate, negative], "bad-txns-inputs-duplicate"),
                         ([CB, empty, negative, duplicate], "bad-txns-vout-empty"),
                         ([CB, TX_A, duplicate, empty], "bad-txns-inputs-duplicate"),
                         ([coinbase(b""), negative], "bad-cb-length"),
                         ([coinbase(b"\x51" * 101), duplicate, negative], "bad-cb-length"),
                         ([many, negative], "bad-txns-vout-negative"),
                         ([many, TX_A, empty], "bad-txns-vout-empty"),
                         ([coinbase(b"", outputs=[txout(0, b"\xac" * 20001)])], "bad-cb-length"),
                         ([many], "bad-blk-sigops"),
                         ([many, TX_A], "bad-blk-sigops")):
        requests += synthetic(txs, verdict)
    return requests


# Script -> signature operations, by CScript::GetSigOpCount(false) (src/script/script.cpp, lines 156
# to 177) and GetOp (src/script/script.h, lines 496 to 552).
# OP_CHECKSIG (ac) and OP_CHECKSIGVERIFY (ad) count 1. OP_CHECKMULTISIG (ae) and
# OP_CHECKMULTISIGVERIFY (af) count 20 with fAccurate false, whatever opcode comes before.
# GetOp skips the data of a push, and fails when a length field or the data is short.
# The loop then stops and keeps its count.
SIGOP_SCRIPTS = {
    "": 0,
    "ac": 1, "ad": 1, "ae": 20, "af": 20,
    "acadaeaf": 42, "acacacac": 4, "aeae": 40, "afaf": 40, "aeafaeaf": 80,
    # OP_0, OP_1NEGATE and OP_1 to OP_16 before each multisig opcode.
    "00ae": 20, "4fae": 20, "00af": 20,
    **{f"{0x50 + n:02x}ae": 20 for n in range(1, 17)},
    **{f"{0x50 + n:02x}af": 20 for n in range(1, 17)},
    "5152ae": 20, "51ac52ae": 21, "605160ae60af": 40,
    # A standard 1-of-2 multisig script: OP_1, two pushes of 33 bytes, OP_2, OP_CHECKMULTISIG.
    "5121" + "02" * 33 + "21" + "03" * 33 + "52ae": 20,
    # Pay to public key hash: OP_DUP OP_HASH160, a push of 20 bytes, OP_EQUALVERIFY OP_CHECKSIG.
    "76a914" + "ac" * 20 + "88ac": 1,
    # Opcodes that fail in execution are still read: OP_RETURN, OP_RESERVED, OP_VER, an undefined opcode.
    "6aac": 1, "50ac": 1, "62ac": 1, "ffac": 1, "baae": 20, "6a6aaeac": 21,
    # Sigop bytes inside push data are not counted.
    "01ac": 0, "02acac": 0, "01ae": 0, "04acadaeaf": 0, "4b" + "ac" * 75: 0,
    "4c03acacac": 0, "4c00": 0, "4d0300aeaeae": 0, "4d0000": 0, "4e03000000afafaf": 0, "4e00000000": 0,
    "4c" + "ff" + "ae" * 255: 0,
    "4d0001" + "ac" * 256: 0,
    # The opcodes after a complete push are counted.
    "01acac": 1, "02acacae": 20, "4c03acacacac": 1, "4d0300aeaeaeae": 20, "4e03000000afafafad": 1,
    "4c00ac": 1, "4d0000ac": 1, "4e00000000ac": 1, "ac01acac": 2,
    # A direct push with short data hides the bytes after it.
    "02ac": 0, "05acacacac": 0, "4bacac": 0, "ac02ac": 1, "ae05acacacac": 20, "acac4b" + "ac" * 74: 2,
    # PUSHDATA1, PUSHDATA2 and PUSHDATA4 with no length field, a short length field, and short data.
    "4c": 0, "4d": 0, "4e": 0, "4d01": 0, "4e01": 0, "4e0100": 0, "4e010000": 0,
    "4c05acac": 0, "4c01": 0, "4d0500acac": 0, "4d0100": 0, "4e05000000acac": 0, "4e01000000": 0,
    "4cffacacac": 0, "4dffffacacac": 0, "4effffffffacacac": 0, "4e00000080acac": 0,
    "ac4c": 1, "ac4d01": 1, "ac4e010000": 1, "ae4c05acac": 20, "acad4d0500acac": 2, "af4e05000000acac": 20,
    "ac4cffacacac": 1, "acae4effffffffacacac": 21,
}


def sigop_requests() -> list[dict]:
    """Signature operation counts through both operations, and the limit of a block (lines 2988 to 2994)."""
    requests = []
    for text, count in SIGOP_SCRIPTS.items():
        script = bytes.fromhex(text)
        # GetLegacySigOpCount adds every scriptSig and every output script (lines 478 to 485).
        as_input = spend(1, script)
        as_output = spend(1, b"", [txout(1, script)])
        both = transaction([txin(A, script), txin(B, script)], [txout(1, script), txout(0), txout(2, script)])
        requests.append(expect(tx_request(as_input), None, legacy_sigops=count))
        requests.append(expect(tx_request(as_output, "allow_witness"), None, legacy_sigops=count))
        requests.append(expect(tx_request(both), None, legacy_sigops=4 * count))
        requests.append(expect(block_request(block([CB, as_input, as_output, both])), None,
                               legacy_sigops=6 * count, transactions=4))
        # The scriptSig of a coinbase counts too. It has 2 to 100 bytes.
        if 2 <= len(script) <= 100:
            requests.append(expect(tx_request(coinbase(script)), None, legacy_sigops=count))
            requests.append(expect(block_request(block([coinbase(script), as_output])), None,
                                   legacy_sigops=2 * count))
    # CheckTransaction has no sigop limit.
    requests.append(expect(tx_request(spend(1, b"\xac" * 20001)), None, legacy_sigops=20001))
    requests.append(expect(tx_request(spend(1, b"\xae" * 5000)), None, legacy_sigops=100000))

    def limit(txs, count, mode="base"):
        """A block with `count` signature operations: valid up to 20,000 (line 2993)."""
        verdict = None if count <= MAX_BLOCK_SIGOPS else "bad-blk-sigops"
        return by_flags(block(txs), {(False, True): verdict, (False, False): verdict}, mode, legacy_sigops=count)

    def cb(script):
        return coinbase(outputs=[txout(COIN, script)])

    # One output script of a coinbase.
    for script, count in ((b"\xac" * 19999, 19999), (b"\xac" * 20000, 20000), (b"\xac" * 20001, 20001),
                          (b"\xad" * 20000, 20000), (b"\xad" * 20001, 20001),
                          (b"\xae" * 999, 19980), (b"\xae" * 1000, 20000), (b"\xae" * 1000 + b"\xac", 20001),
                          (b"\xae" * 1001, 20020), (b"\xaf" * 1000, 20000), (b"\xaf" * 1001, 20020),
                          # With an accurate count OP_1 or OP_16 before each opcode would give 1,000 or 16,000.
                          (b"\x51\xae" * 1000, 20000), (b"\x51\xae" * 1001, 20020),
                          (b"\x60\xaf" * 1000, 20000), (b"\x60\xaf" * 1000 + b"\xad", 20001),
                          # A truncated push hides the bytes that would pass the limit.
                          (b"\xac" * 20000 + b"\x4c\xff" + b"\xac" * 10, 20000),
                          (b"\xac" * 20000 + b"\x4d\xff" + b"\xac", 20000),
                          (b"\xac" * 20000 + b"\x4e\xff\xff\xff" + b"\xae", 20000),
                          (b"\xac" * 20000 + b"\x02\xac", 20000),
                          (b"\xac" * 20000 + b"\x4b" + b"\xae" * 74, 20000),
                          # Complete push data does not count, and the opcode after it does.
                          (b"\xac" * 20000 + b"\x02\xac\xac", 20000),
                          (b"\xac" * 20000 + b"\x02\xac\xac\xac", 20001),
                          (b"\x4c\x05" + b"\xac" * 5 + b"\xac" * 20000, 20000),
                          (b"\x4c\x04" + b"\xac" * 5 + b"\xac" * 20000, 20001)):
        requests += limit([cb(script)], count)
    for mode in BOTH_MODES:
        requests += limit([cb(b"\xac" * 20000)], 20000, mode)
        requests += limit([cb(b"\xac" * 20001)], 20001, mode)
    # The scriptSig of the coinbase: 100 bytes of OP_CHECKSIG, and of OP_CHECKMULTISIG.
    requests += limit([coinbase(b"\xac" * 100)], 100)
    requests += limit([coinbase(b"\xae" * 100)], 2000)
    requests += limit([coinbase(b"\xac" * 100, [txout(COIN, b"\xac" * 19900)])], 20000)
    requests += limit([coinbase(b"\xac" * 100, [txout(COIN, b"\xac" * 19901)])], 20001)
    requests += limit([coinbase(b"\xae" * 100, [txout(COIN, b"\xae" * 900)])], 20000)
    requests += limit([coinbase(b"\xae" * 100, [txout(COIN, b"\xae" * 900 + b"\xad")])], 20001)
    # Several outputs, and scriptSig and output scripts of several transactions.
    requests += limit([coinbase(outputs=[txout(1, b"\xac" * 10000), txout(1, b"\xad" * 10000)])], 20000)
    requests += limit([coinbase(outputs=[txout(1, b"\xac" * 10000), txout(1, b"\xad" * 10000), txout(1, b"\xac")])],
                      20001)
    split = [coinbase(b"\xac" * 100, [txout(COIN, b"\xac" * 9900)]),
             transaction([txin(A, b"\xac" * 5000)], [txout(1, b"\xac" * 4999)])]
    requests += limit(split, 19999)
    requests += limit([*split, spend(2, b"\xac")], 20000)
    requests += limit([*split, spend(2, b"\xac"), spend(3, b"", [txout(1, b"\xad")])], 20001)
    requests += limit([*split, spend(2, b"\xae")], 20019)
    quarter = [spend(tag, b"\xac" * 2500, [txout(1, b"\xae" * 125)]) for tag in (1, 2, 3)]
    requests += limit([coinbase(b"\xac" * 100, [txout(COIN, b"\xac" * 4900)]), *quarter], 20000)
    requests += limit([coinbase(b"\xac" * 100, [txout(COIN, b"\xac" * 4901)]), *quarter], 20001)
    thousand = [transaction([txin(prevout(1, n), b"\xae")], [OUT]) for n in range(1000)]
    requests += limit([CB, *thousand], 20000)
    requests += limit([CB, *thousand, spend(2, b"\xad")], 20001)
    return requests


def reader_requests() -> list[dict]:
    """Blocks and transactions that Core's stream code rejects, and blocks with witness data."""
    requests = []
    small = block([CB, TX_A])
    # A coinbase and a spend in the extended format, each with one witness stack.
    witness_cb = Extended([txin(NULL_PREVOUT, b"\x51\x51")], [txout(50 * COIN)], [[bytes(32)]])
    witness_spend = Extended([txin(A)], [OUT], [[b"\x30" * 71, b"\x02" * 33]])
    witness_block = block([witness_cb, witness_spend])
    stacks = len(witness_block) - len(block([witness_cb.base, witness_spend.base]))
    assert stacks == (2 + 34) + (2 + 1 + 72 + 34)
    without_work(witness_block[:80])

    # Every proper prefix ends inside a field, so Core's reader reports the end of the data.
    requests += [expect(block_request(small[:n]), TRUNCATED) for n in range(len(small))]
    requests += [expect(block_request(witness_block[:n], "allow_witness"), TRUNCATED)
                 for n in range(len(witness_block))]
    requests += [expect(block_request(small[:n], "allow_witness", True, False), TRUNCATED)
                 for n in (0, 1, 79, 80, 81, len(small) - 1)]
    # Bytes after the block.
    for mode in BOTH_MODES:
        for tail in (b"\x00", b"\x01", bytes(5), small):
            requests.append(expect(block_request(small + tail, mode), {"kind": "trailing_bytes", "count": len(tail)}))
    requests.append(expect(block_request(witness_block + b"\xff", "allow_witness"),
                           {"kind": "trailing_bytes", "count": 1}))
    # An empty list with bytes after it: the reader stops after the count.
    requests.append(expect(block_request(block([]) + CB), {"kind": "trailing_bytes", "count": len(CB)}))

    # The transaction count (src/serialize.h, ReadCompactSize): above MAX_SIZE, and not canonical.
    header = small[:80]
    for mode in BOTH_MODES:
        for count in (MAX_SIZE + 1, 0xffffffff, 2**32, 2**64 - 1):
            requests.append(expect(block_request(header + compact_size(count) + CB, mode), TOO_LARGE))
        for count in (b"\xfd\x01\x00", b"\xfd\xfc\x00", b"\xfe\x01\x00\x00\x00", b"\xfe\xff\xff\x00\x00",
                      b"\xff\x01" + bytes(7), b"\xff\xff\xff\xff\xff" + bytes(4), b"\xfd\x00\x00", b"\xff" + bytes(8)):
            requests.append(expect(block_request(header + count + CB, mode), NON_CANONICAL))
        # A count that the reader accepts, with fewer transactions than it promises.
        for count in (2, 0xfc, 0xfd, 0xffff, 0x10000, MAX_SIZE):
            requests.append(expect(block_request(header + compact_size(count) + CB, mode), TRUNCATED))
        # More transactions than the count promises.
        requests.append(expect(block_request(header + compact_size(1) + CB + TX_A, mode),
                               {"kind": "trailing_bytes", "count": len(TX_A)}))
    # A count of 253 in its canonical three-byte form, with 253 transactions.
    spends = [spend(1 + n % 250, b"", [txout(n)]) for n in range(252)]
    requests.append(expect(block_request(block([CB, *spends])), None, transactions=253))
    requests.append(expect(block_request(block([CB, *spends[:251]])), None, transactions=252))

    # Witness data in a block. CheckBlock reads no witness stack, and the base size has none.
    requests += by_flags(witness_block, {(False, True): None, (False, False): None, (True, True): "high-hash"},
                         "allow_witness", base_size=len(witness_block) - stacks, transactions=2, legacy_sigops=0)
    mixed = block([CB, witness_spend, TX_B])
    requests += by_flags(mixed, {(False, True): None}, "allow_witness", base_size=len(mixed) - (2 + 1 + 72 + 34),
                         transactions=3)
    # The Merkle root uses transaction IDs, which do not cover the witness.
    other_stack = Extended([txin(A)], [OUT], [[b"\x01"]])
    assert other_stack.base == witness_spend.base and other_stack.wire != witness_spend.wire
    requests += by_flags(block([CB, other_stack], root=root_of([CB, witness_spend])), {(False, True): None},
                         "allow_witness", transactions=2)
    # Two transactions with one ID and different witnesses are a mutation.
    requests += by_flags(block([CB, TX_C, witness_spend, other_stack]),
                         {(False, True): "bad-txns-duplicate", (False, False): None}, "allow_witness")
    # CheckTransaction and the block tests read the base fields of an extended transaction.
    faulty = [(Extended([txin(A)], [txout(-1)], [[b"\x01"]]), "bad-txns-vout-negative"),
              (Extended([txin(A), txin(A)], [OUT], [[b"\x01"], []]), "bad-txns-inputs-duplicate"),
              (Extended([txin(A), txin(NULL_PREVOUT)], [OUT], [[], [b"\x01"]]), "bad-txns-prevout-null")]
    for tx, reason in faulty:
        requests.append(expect(tx_request(tx.wire, "allow_witness"), reason, base_size=len(tx.base)))
        requests += by_flags(block([CB, tx]), {(False, True): reason}, "allow_witness")
    for tx, reason in ((Extended([txin(NULL_PREVOUT, b"\x51")], [txout(1)], [[bytes(32)]]), "bad-cb-length"),
                       (witness_cb, None)):
        requests.append(expect(tx_request(tx.wire, "allow_witness"), reason, base_size=len(tx.base)))
        requests += by_flags(block([tx]), {(False, True): reason}, "allow_witness")
    requests += by_flags(block([witness_spend]), {(False, True): "bad-cb-missing"}, "allow_witness")
    # This coinbase has another scriptSig than CB, so the two transaction IDs differ.
    second_cb = Extended([txin(NULL_PREVOUT, b"\x52\x52")], [txout(50 * COIN)], [[bytes(32)]])
    requests += by_flags(block([CB, second_cb]), {(False, True): "bad-cb-multiple"}, "allow_witness")
    # The witness coinbase has the base fields of CB. The equal IDs are a mutation, which comes first.
    assert witness_cb.base == CB
    requests += by_flags(block([CB, witness_cb]), {(False, True): "bad-txns-duplicate", (False, False): "bad-cb-multiple"},
                         "allow_witness")
    requests.append(expect(tx_request(witness_spend.wire, "allow_witness"), None,
                           base_size=len(witness_spend.base), legacy_sigops=0))
    # Signature operation bytes in a witness stack are not counted (lines 478 to 485 read no witness).
    signing = Extended([txin(A)], [OUT], [[b"\xac" * 30000]])
    requests.append(expect(tx_request(signing.wire, "allow_witness"), None, legacy_sigops=0))
    requests += by_flags(block([CB, signing]), {(False, True): None}, "allow_witness", legacy_sigops=0)

    # The same bytes in base mode: the marker byte is an empty input list. Core supplies the result.
    for data in (witness_block, mixed, block([witness_spend])):
        requests.append(block_request(data, "base"))
        requests.append(block_request(data, "base", False, False))
    for tx in (witness_cb, witness_spend, other_stack, signing):
        requests.append(tx_request(tx.wire, "base"))
    # A base transaction with no inputs, read in witness mode. Core supplies the result.
    for data in (transaction([], [OUT]), transaction([], [txout(-1)]), transaction([], [OUT, OUT])):
        requests.append(tx_request(data, "allow_witness"))
        requests.append(block_request(block([CB, data]), "allow_witness"))

    # Unknown optional data: a flags byte with a bit other than bit 0 (src/primitives/transaction.h,
    # lines 231 to 241). The reader fails after the outputs, or after the stacks when bit 0 is set.
    for flags, stacks_of in ((2, []), (3, [[b"\x01"]]), (0x80, []), (0xff, [[]])):
        tx = Extended([txin(A)], [OUT], stacks_of, flags)
        requests.append(expect(tx_request(tx.wire, "allow_witness"), UNKNOWN_OPTIONAL_DATA))
        requests.append(expect(block_request(block([CB, tx.wire]), "allow_witness"), UNKNOWN_OPTIONAL_DATA))
        requests.append(expect(block_request(block([CB, tx.wire, TX_B]), "allow_witness", True, False),
                               UNKNOWN_OPTIONAL_DATA))
        requests.append(tx_request(tx.wire, "base"))
        requests.append(block_request(block([CB, tx.wire]), "base"))
    # Flags 1 with an empty stack for every input. Core supplies the result.
    bare = Extended([txin(A)], [OUT], [[]])
    requests.append(tx_request(bare.wire, "allow_witness"))
    requests.append(block_request(block([CB, bare]), "allow_witness"))

    # Reader errors of tx.check, as tx.decode_witness reports them.
    for mode in BOTH_MODES:
        requests += [expect(tx_request(TX_A[:n], mode), TRUNCATED) for n in range(len(TX_A))]
        for tail in (b"\x00", bytes(4), TX_A):
            requests.append(expect(tx_request(TX_A + tail, mode), {"kind": "trailing_bytes", "count": len(tail)}))
        requests.append(expect(tx_request(le(1, 4) + compact_size(MAX_SIZE + 1), mode), TOO_LARGE))
        requests.append(expect(tx_request(le(1, 4) + b"\xfd\x01\x00" + txin(A) + b"\x01" + OUT + bytes(4), mode),
                               NON_CANONICAL))
    requests += [expect(tx_request(witness_spend.wire[:n], "allow_witness"), TRUNCATED)
                 for n in range(len(witness_spend.wire))]
    requests.append(expect(tx_request(witness_spend.wire + b"\x00", "allow_witness"),
                           {"kind": "trailing_bytes", "count": 1}))
    return requests


def auxpow_requests() -> list[dict]:
    """Synthetic transaction lists after real full headers, with the header test and no Merkle test.

    The headers are from the main chain, so CheckAuxPowProofOfWork accepts each one
    (src/dogecoin.cpp, lines 89 to 125). The base size of the block holds the AuxPoW payload."""
    requests = []
    payloads = 0
    for height, header in full_headers():
        bits = int.from_bytes(header[72:76], "little")
        has_payload = len(header) > 80
        payloads += has_payload
        # The header whose scrypt digest carries the work: the parent header ends the payload.
        work = header[-80:]
        assert scrypt_of(work) <= target_of(bits)
        assert has_payload == bool(int.from_bytes(header[:4], "little") & 0x100)
        display = sha256d(header[:80])[::-1].hex()
        for mode in BOTH_MODES:
            requests += by_flags(block([CB], header=header), {(True, False): None, (False, False): None,
                                                               (True, True): "bad-txnmrklroot"},
                                 mode, base_size=len(header) + 1 + len(CB), transactions=1, hash_display=display,
                                 legacy_sigops=0)
        # With the header test passed, each later test decides.
        requests += by_flags(block([CB, TX_A, TX_B], header=header), {(True, False): None},
                             base_size=len(header) + 1 + len(CB + TX_A + TX_B), transactions=3)
        requests += by_flags(block([], header=header), {(True, False): "bad-blk-length"})
        requests += by_flags(block([TX_A], header=header), {(True, False): "bad-cb-missing"})
        requests += by_flags(block([CB, CB2], header=header), {(True, False): "bad-cb-multiple"})
        requests += by_flags(block([CB, transaction([txin(A)], [])], header=header),
                             {(True, False): "bad-txns-vout-empty"})
        requests += by_flags(block([coinbase(outputs=[txout(0, b"\xac" * 20001)])], header=header),
                             {(True, False): "bad-blk-sigops"})
        # Another nonce in the header that carries the work: its digest is above the target.
        spoiled = header[:-4] + le((int.from_bytes(header[-4:], "little") + 1) % 2**32, 4)
        assert scrypt_of(spoiled[-80:]) > target_of(bits)
        for mode in BOTH_MODES:
            requests += by_flags(block([CB], header=spoiled), {(True, False): "high-hash", (True, True): "high-hash",
                                                                (False, False): None}, mode)
        if has_payload:
            # Another nonce in the 80-byte header changes the block hash, which the payload commits to
            # (src/auxpow.cpp, CAuxPow::check). The parent header keeps its work.
            unbound = header[:76] + le((int.from_bytes(header[76:80], "little") + 1) % 2**32, 4) + header[80:]
            requests += by_flags(block([CB], header=unbound), {(True, False): "high-hash", (False, False): None})
        else:
            # A version without the AuxPoW bit has no payload, so the list starts after 80 bytes.
            requests.append(expect(block_request(header + compact_size(1) + CB + b"\x00", "base", True, False),
                                   {"kind": "trailing_bytes", "count": 1}))
    # The fixture holds heights before and after the first AuxPoW block.
    assert 0 < payloads < 21
    return requests


def size_requests() -> list[dict]:
    """The size limits of both functions, on objects of about one megabyte.

    CheckTransaction rejects a base size above 1,000,000 bytes (lines 535 and 536), and CheckBlock
    does the same for a block (lines 2971 to 2973). Both sizes leave out witness data."""
    limit = MAX_BLOCK_BASE_SIZE
    requests = []
    # tx.check: 1,000,000 bytes pass the test, and 1,000,001 fail it.
    exact, over = spend_of_size(limit), spend_of_size(limit + 1)
    requests.append(expect(tx_request(exact), None, base_size=limit, legacy_sigops=0))
    requests.append(expect(tx_request(over), "bad-txns-oversize", base_size=limit + 1))
    # The output test of line 532 comes before the size test, and the size test before the output loop.
    requests.append(expect(tx_request(spend_of_size(limit + 1, [])), "bad-txns-vout-empty"))
    requests.append(expect(tx_request(spend_of_size(limit + 1, [txout(-1)])), "bad-txns-oversize"))
    requests.append(expect(tx_request(spend_of_size(limit, [txout(-1)])), "bad-txns-vout-negative"))
    # The witness does not count: the base size decides.
    for size, verdict in ((limit, None), (limit + 1, "bad-txns-oversize")):
        tx = extended_spend_of_size(size)
        assert len(tx.base) == size < len(tx.wire)
        requests.append(expect(tx_request(tx.wire, "allow_witness"), verdict, base_size=size))

    # block.check: a block of 1,000,000 bytes passes, and one of 1,000,001 fails.
    for size, verdict in ((limit, None), (limit + 1, "bad-blk-length")):
        data = block([coinbase_of_size(size - 81)])
        assert len(data) == size
        requests.append(expect(block_request(data), verdict, base_size=size, transactions=1))
    # A transaction that passes or fails its own size test makes its block too large.
    # The block test comes first, so CheckBlock never returns bad-txns-oversize.
    requests.append(expect(block_request(block([CB, exact])), "bad-blk-length"))
    requests.append(expect(block_request(block([CB, over]), "base", False, False), "bad-blk-length"))
    # The size test comes before the coinbase tests.
    requests.append(expect(block_request(block([spend_of_size(limit - 80)]), "base", False, False),
                           "bad-blk-length"))
    # Two transactions that fill the block exactly.
    filled = block([CB, spend_of_size(limit - 81 - len(CB))])
    assert len(filled) == limit
    requests.append(expect(block_request(filled), None, base_size=limit, transactions=2))
    # A block whose base form has 1,000,000 bytes, with witness data after it in the count.
    tx = extended_spend_of_size(limit - 81 - len(CB))
    data = block([CB, tx])
    assert len(data) > limit and len(block([CB, tx.base])) == limit
    requests.append(expect(block_request(data, "allow_witness"), None, base_size=limit, transactions=2))
    # The AuxPoW payload counts in the base size. The header is the first real one with a payload.
    header = next(h for _, h in full_headers() if len(h) > 80)
    for size, verdict in ((limit, None), (limit + 1, "bad-blk-length")):
        data = block([coinbase_of_size(size - len(header) - 1)], header=header)
        assert len(data) == size
        requests.append(expect(block_request(data, "base", True, False), verdict, base_size=size))
    return requests


# ---------------------------------------------------------------------------
# Real mainnet blocks


class BlockAssets(Exception):
    """A fixture of real blocks is absent, or differs from its committed hashes or from its manifest."""


def fixture_blocks(directory, sums: str | None = None) -> list[tuple[dict, bytes]]:
    """The manifest record and the bytes of each block of a `dogelib-blocks/1` fixture.

    The two files must have the hashes of the fixture's SHA256SUMS file. With `sums`, that file
    must have exactly this text, which the caller takes from a committed file.
    Each block must have the height, the size and the header hash of its manifest record.
    scripts/fetch_blocks.py --check makes the other checks of a fixture."""
    directory = pathlib.Path(directory)
    names = (fetch_blocks.BLOCKS_FILE, fetch_blocks.MANIFEST_FILE)
    try:
        if sums is not None and (directory / fetch_blocks.SUMS_FILE).read_text() != sums:
            raise BlockAssets(f"{directory}: SHA256SUMS does not have the committed hashes")
        fetch_blocks.check_sums(directory, names)
        manifest = json.loads((directory / fetch_blocks.MANIFEST_FILE).read_text())
        blocks = list(fetch_blocks.read_blocks(directory / fetch_blocks.BLOCKS_FILE))
    except (OSError, ValueError, fetch_blocks.FetchError) as error:
        detail = str(error) if isinstance(error, fetch_blocks.FetchError) else type(error).__name__
        raise BlockAssets(f"{directory}: cannot read the fixture: {detail}") from None
    records = manifest.get("blocks") if isinstance(manifest, dict) else None
    if manifest.get("format") != fetch_blocks.FORMAT or not isinstance(records, list) or len(records) != len(blocks):
        raise BlockAssets(f"{directory}: the manifest does not match the blocks")
    for record, (height, raw) in zip(records, blocks):
        if (record.get("height") != height or record.get("size") != len(raw)
                or record.get("hash") != sha256d(raw[:80])[::-1].hex()
                or record.get("auth") not in ("pinned", "linked") or not is_count(record.get("transactions"))):
            raise BlockAssets(f"{directory}: the manifest record of height {height} does not match its block")
    return [(record, raw) for record, (_, raw) in zip(records, blocks)]


def witness_size(tx: bytes) -> int:
    """The bytes of a parsed transaction that its base serialization leaves out.

    They are the marker, the flags and the witness stacks of the extended format
    (src/primitives/transaction.h, lines 211 to 243)."""
    if tx[4:6] != b"\x00\x01":
        return 0
    reader = fetch_blocks.Reader(tx)
    reader.take(6)
    inputs = reader.compact_size()
    for _ in range(inputs):
        reader.take(36)
        reader.take(reader.compact_size())
        reader.take(4)
    for _ in range(reader.compact_size()):
        reader.take(8)
        reader.take(reader.compact_size())
    start = reader.pos
    for _ in range(inputs):
        for _ in range(reader.compact_size()):
            reader.take(reader.compact_size())
    assert reader.pos + 4 == len(tx)
    return 2 + reader.pos - start


def parent_coinbase(raw: bytes) -> bytes:
    """The coinbase transaction of the parent block in the AuxPoW payload, or no bytes without a payload."""
    if not int.from_bytes(raw[:4], "little") & 0x100:
        return b""
    reader = fetch_blocks.Reader(raw)
    reader.take(80)
    fetch_blocks.read_transaction(reader)
    return raw[80:reader.pos]


def real_request(record: dict, raw: bytes, mode: str) -> dict:
    """block.check with both flags on a block of the main chain.

    The parent coinbase of an AuxPoW payload can be in the extended format, because the parent
    chain allows witness data. The base size of the block leaves those bytes out. The expected
    size assumes that no transaction of the block itself has witness data. A block with such a
    transaction fails the comparison."""
    return expect(block_request(raw, mode, True, True), None,
                  base_size=record["size"] - witness_size(parent_coinbase(raw)),
                  transactions=record["transactions"], hash_display=record["hash"])


def split_block(raw: bytes) -> tuple[bytes, list[bytes]]:
    """The full header of a block, with its AuxPoW payload if it has one, and its transactions."""
    reader = fetch_blocks.Reader(raw)
    version = int.from_bytes(reader.take(80)[:4], "little")
    if version & 0x100:
        # CAuxPow (src/auxpow.h): the coinbase transaction, the block hash, two branches with
        # their indexes, and the parent header.
        fetch_blocks.read_transaction(reader)
        reader.take(32)
        reader.hashes()
        reader.take(4)
        reader.hashes()
        reader.take(4)
        reader.take(80)
    header = raw[:reader.pos]
    txs = []
    for _ in range(reader.compact_size()):
        start = reader.pos
        fetch_blocks.read_transaction(reader)
        txs.append(raw[start:reader.pos])
    assert reader.pos == len(raw) and block(txs, header=header) == raw
    return header, txs


def merkle_duplication(txs: list[bytes]) -> list[bytes] | None:
    """A longer list with the root of `txs`, in which Core joins two equal hashes, or None.

    The list repeats the last 2^k transactions, for the least k that keeps the root (CVE-2012-2459)."""
    count = 1
    while count <= len(txs):
        longer = txs + txs[-count:]
        if root_of(longer) == root_of(txs) and is_mutated(longer):
            return longer
        count *= 2
    return None


def rule_change_requests() -> list[dict]:
    """The real blocks at and next to the rule changes of design record 0010, and mutations of them.

    Each block has real work and its own Merkle root. So a mutation reaches `bad-txns-duplicate`
    with both flags, which a synthetic block reaches only without the header test."""
    requests = []
    duplications = 0
    blocks = fixture_blocks(RULE_CHANGES)
    assert [record["height"] for record, _ in blocks] == [
        144998, 144999, 145000, 145001, 371336, 371337, 371338, 599998, 599999, 600000, 600001,
        1034382, 1034383, 1034384, 3464750, 3464751, 3464752]
    for record, raw in blocks:
        for mode in BOTH_MODES:
            requests.append(real_request(record, raw, mode))
        header, txs = split_block(raw)
        assert not is_mutated(txs) and root_of(txs) == raw[36:68]
        # Lines 2952 to 2956: another lock time in the last transaction changes its ID, and the
        # header has work. CheckTransaction does not read the lock time.
        changed = raw[:-1] + bytes([raw[-1] ^ 1])
        requests += by_flags(changed, {(True, True): "bad-txnmrklroot", (True, False): None},
                             transactions=len(txs), base_size=len(raw), hash_display=record["hash"])
        # Lines 2958 to 2962: a longer list with the same root, under real work.
        longer = merkle_duplication(txs)
        if longer is not None:
            duplications += 1
            data = block(longer, header=header)
            assert len(data) <= MAX_BLOCK_BASE_SIZE
            requests += by_flags(data, {(True, True): "bad-txns-duplicate", (True, False): None},
                                 transactions=len(longer), hash_display=record["hash"])
        # Lines 2933 and 2934: another nonce in the header that carries the work. With a payload
        # that is the parent header, which ends the payload.
        bits = int.from_bytes(raw[72:76], "little")
        assert scrypt_of(header[-80:]) <= target_of(bits)
        spoiled = header[:-4] + le((int.from_bytes(header[-4:], "little") + 1) % 2**32, 4)
        assert scrypt_of(spoiled[-80:]) > target_of(bits)
        requests += by_flags(spoiled + raw[len(header):], {(True, True): "high-hash", (False, True): None},
                             transactions=len(txs), base_size=len(raw))
        # The reader takes the whole block and nothing more.
        requests.append(expect(block_request(raw[:-1], "base", True, True), TRUNCATED))
        requests.append(expect(block_request(raw + b"\x00", "base", True, True),
                               {"kind": "trailing_bytes", "count": 1}))
    # Blocks with one transaction have no such list.
    assert 0 < duplications < len(blocks)
    return requests


def mainnet_range_sets(directory) -> list[tuple[str, list[dict]]]:
    """One set for each range of tests/block/mainnet-blocks/release.json: every block, with both flags.

    `directory` holds the fixtures that scripts/fetch_release_blocks.py writes. Each file must have
    its committed hash. The mode is `allow_witness`, in which Core reads a block from the network."""
    try:
        release = fetch_release_blocks.load_release()
    except fetch_release_blocks.AssetError as error:
        raise BlockAssets(str(error)) from None
    sets = []
    for entry in release["ranges"]:
        blocks = fixture_blocks(pathlib.Path(directory) / entry["name"], fetch_release_blocks.sums_text(entry))
        heights = [record["height"] for record, _ in blocks]
        if heights != list(range(entry["first"], entry["last"] + 1)) or len(heights) != entry["blocks"]:
            raise BlockAssets(f"{directory}: the range {entry['name']} does not have the heights of release.json")
        sets.append((f"block.check mainnet {entry['name']}",
                     [real_request(record, raw, "allow_witness") for record, raw in blocks]))
    return sets


def mainnet_range_counts() -> dict[str, int]:
    """Operation -> the number of requests of `mainnet_range_sets`, from release.json."""
    release = fetch_release_blocks.load_release()
    return {"block.check": sum(entry["blocks"] for entry in release["ranges"])}


def corpus_requests(base: list[bytes], witness: list[bytes]) -> list[dict]:
    """Core's transaction corpus through tx.check, with the duplicate test. Core supplies the results.

    `base` holds the records in the base format, and `witness` holds every record."""
    return ([tx_request(data, "base") for data in base] +
            [tx_request(data, "allow_witness") for data in witness])


QUICK_SET = "check known answers"
_sets = None


def block_check_sets() -> list[tuple[str, list[dict]]]:
    global _sets
    if _sets is None:
        cases = transaction_cases()
        _sets = [
            (QUICK_SET, known_answers()),
            ("tx.check reasons", tx_reason_requests(cases)),
            ("block.check transaction reasons", tx_in_block_requests(cases)),
            ("block.check reasons", block_reason_requests()),
            ("check signature operations", sigop_requests()),
            ("check readers and witness data", reader_requests()),
            ("block.check real full headers", auxpow_requests()),
            ("check size limits", size_requests()),
            ("block.check mainnet rule changes", rule_change_requests()),
        ]
    return _sets


# ---------------------------------------------------------------------------
# Comparison


def same(a, b) -> bool:
    """Equality of JSON values, in which `true` is not `1`."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def is_count(value) -> bool:
    return type(value) is int and value >= 0


def malformed(req: dict, ok, oracle: bool) -> str | None:
    """A fault in the form of an `ok` object, or None.

    The oracle alone has `diagnostic`, the Lean error. It is a string exactly when the verdict is a rejection."""
    op = req["op"]
    fields = OK_FIELDS[op] | ({"diagnostic"} if oracle else set())
    if not isinstance(ok, dict) or set(ok) != fields:
        return "must return exactly the fields " + ", ".join(sorted(fields))
    if type(ok["valid"]) is not bool or not is_count(ok["legacy_sigops"]) or not is_count(ok["base_size"]):
        return "has a field of the wrong type"
    block_op = op == "block.check"
    reason = ok["reject_reason"]
    if ok["valid"]:
        if any(ok[field] is not None for field in fields - {"valid", "legacy_sigops", "base_size", "transactions",
                                                           "hash_hex", "hash_display"}):
            return "has a rejection field in a valid verdict"
    else:
        known = BLOCK_REASONS if block_op else {r: (s, False) for r, s in TX_REASONS.items()}
        if not isinstance(reason, str) or reason not in known:
            return f"returned the reason {reason!r}, which Core's function does not have"
        score, corruption = known[reason]
        if type(ok["dos"]) is not int or ok["dos"] != score or type(ok["reject_code"]) is not int or ok["reject_code"] != REJECT_INVALID:
            return f"returned score {ok['dos']!r} and code {ok['reject_code']!r} for {reason}, and Core's text gives {score} and {REJECT_INVALID}"
        if block_op and ok["corruption_possible"] is not corruption:
            return f"returned corruption_possible {ok['corruption_possible']!r} for {reason}"
        if oracle and not isinstance(ok["diagnostic"], str):
            return "has no Lean diagnostic for a rejection"
    data = bytes.fromhex(req["block_hex" if block_op else "tx_hex"])
    # Core's readers accept only canonical counts, so a base-mode read keeps every byte in the base size.
    if ok["base_size"] > len(data) or (req["mode"] == "base" and ok["base_size"] != len(data)):
        return f"returned base size {ok['base_size']} for {len(data)} bytes in mode {req['mode']}"
    if block_op:
        digest = sha256d(data[:80])
        if not is_count(ok["transactions"]):
            return "has a field of the wrong type"
        if ok["hash_hex"] != digest.hex() or ok["hash_display"] != digest[::-1].hex():
            return "returned a hash that is not the double SHA-256 of the first 80 bytes"
    return None


def unexpected(response: dict, expected: dict) -> str | None:
    """How a response differs from a recorded expectation, or None."""
    verdict = expected["verdict"]
    if isinstance(verdict, dict):
        return None if same(response.get("error"), verdict) else f"expected the error {json.dumps(verdict, sort_keys=True)}"
    ok = response.get("ok")
    if not isinstance(ok, dict):
        return f"expected the verdict {verdict or 'valid'}"
    if ok.get("valid") is not (verdict is None) or ok.get("reject_reason") != verdict:
        return f"expected the verdict {verdict or 'valid'}, got {ok.get('reject_reason') or ('valid' if ok.get('valid') else None)}"
    for field, value in expected.items():
        if field != "verdict" and not same(ok.get(field), value):
            return f"expected {field} {value!r}, got {ok.get(field)!r}"
    return None


def compare(req: dict, ours: dict, core: dict, peer: str = "core") -> tuple[str, str] | None:
    """None when both programs give the same result, else a failure code and a message.

    The comparison covers every field of `ok` except the oracle's `diagnostic`, and every field of `error`.
    A recorded expectation must also hold."""
    label = LABELS[req["op"]]
    for side, response in (("oracle", ours), (peer, core)):
        if set(response) - {"id"} not in ({"ok"}, {"error"}):
            return label, f"{side} must return ok or error"
        if "ok" in response:
            fault = malformed(req, response["ok"], side == "oracle")
            if fault:
                return label, f"{side} {fault}"
        elif not isinstance(response["error"], dict) or response["error"].get("kind") not in ("read", "trailing_bytes"):
            return label, f"{side} returned an error that is not a read error"
    if ("ok" in ours) != ("ok" in core):
        return label, f"one program returned a verdict and the other an error: oracle {json.dumps(ours)[:200]}, {peer} {json.dumps(core)[:200]}"
    if "ok" in ours:
        for field in sorted(OK_FIELDS[req["op"]]):
            if not same(ours["ok"][field], core["ok"][field]):
                return label, f"{field}: oracle {ours['ok'][field]!r}, {peer} {core['ok'][field]!r}"
    elif not same(ours["error"], core["error"]):
        return label, f"error: oracle {json.dumps(ours['error'], sort_keys=True)}, {peer} {json.dumps(core['error'], sort_keys=True)}"
    expected = EXPECTATIONS.get(key(req))
    if expected is not None:
        fault = unexpected(ours, expected)
        if fault:
            return label, f"both programs disagree with the independent expectation: {fault}"
    return None


# ---------------------------------------------------------------------------
# Report


def reasons_reached(requests: list[dict], responses: list[dict]) -> dict[str, dict[str, int]]:
    """Operation -> reject reason -> the number of responses with it. A valid verdict counts as `valid`."""
    counts = {op: {} for op in LABELS}
    for req, response in zip(requests, responses):
        if req["op"] in counts:
            ok = response.get("ok")
            if isinstance(ok, dict):
                name = "valid" if ok.get("valid") is True else str(ok.get("reject_reason"))
            else:
                error = response.get("error", {})
                name = "error " + str(error.get("reason", error.get("kind")))
            counts[req["op"]][name] = counts[req["op"]].get(name, 0) + 1
    return counts


def reasons_missing(counts: dict[str, dict[str, int]]) -> list[str]:
    """The reachable reasons of design record 0010, section 4, that no response has.

    tx.check must reach every reason of CheckTransaction. block.check must reach every reason of
    CheckBlock, and every reason of CheckTransaction except the one that the block size test hides."""
    missing = [f"tx.check {reason}" for reason in TX_REASONS if not counts["tx.check"].get(reason)]
    missing += [f"block.check {reason}" for reason in BLOCK_REASONS
                if reason not in UNREACHABLE_IN_BLOCK and not counts["block.check"].get(reason)]
    return missing
