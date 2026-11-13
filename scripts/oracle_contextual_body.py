"""block.contextual_check_body requests and their expectations (design record 0010, stage 0010a).

The module builds the requests of the Core comparison and of the oracle test for the
body of Core's ContextualCheckBlock on mainnet. No expectation comes from DogeLib.
Each reject reason comes from a reader of Core's text at the pin (SOURCES.md D33,
src/validation.cpp, lines 3121 to 3203):

- bad-txns-nonfinal, score 10 (line 3141), from IsFinalTx (lines 258 to 269).
- bad-cb-height, score 100 (line 3150), the BIP34 coinbase height from 1,034,383.
- unexpected-witness, score 100 (line 3186).
- bad-blk-weight, score 100 (line 3198), reachable when the body runs alone.

The request carries the block and a contiguous chain from the predecessor, newest first,
reaching the aligned version-bits boundary and its predecessors. The boundary's median
time selects the version-bits case: below the CSV start (2016-05-01) both deployments are
DEFINED, and at or after the CSV timeout (2017-05-01) the harness installs FAILED. On
mainnet neither state is ever ACTIVE, so the body's version-bits branches never fire.

The height boundaries 1,034,382 and 1,034,383 (BIP34) and 3,464,750 and 3,464,751 (BIP65)
use a contiguous chain back to the aligned boundary. The other cases use a candidate at a
period boundary, so the chain is the boundary and its ten predecessors.
"""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
import sys
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_block_check import (block, coinbase, transaction, txin, txout, spend, Extended,
                                NULL_PREVOUT, COIN, genesis_block, one_push, padded, TIME, BITS)

PERIOD = 10080  # nMinerConfirmationWindow on mainnet (D14, line 101)
BIP34_HEIGHT = 1034383  # D14, line 84
BIP65_HEIGHT = 3464751  # D14, line 86
# Median times on either side of the CSV window (D14, lines 105 and 106).
CSV_START = 1462060800
CSV_TIMEOUT = 1493596800
TIME_BEFORE_CSV = 1450000000   # 2015-12, below the CSV start: version bits DEFINED
TIME_AFTER_CSV = 1500000000    # 2017-07, at or after the CSV timeout: harness seeds FAILED

BODY_REASONS = {"bad-txns-nonfinal": 10, "bad-cb-height": 100, "unexpected-witness": 100,
                "bad-blk-weight": 100}
REJECT_INVALID = 16
OK_FIELDS = {"valid", "reject_reason", "dos", "reject_code"}
EXPECTATIONS = {}


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def script_num(n: int) -> bytes:
    """CScriptNum::serialize for n > 0 (D24, lines 319 to 351)."""
    assert n > 0
    out = bytearray()
    x = n
    while x:
        out.append(x & 0xff)
        x >>= 8
    if out[-1] & 0x80:
        out.append(0)
    return bytes(out)


def coinbase_with_height(height: int, tail: bytes = b"\x00") -> bytes:
    """A coinbase whose scriptSig starts with the BIP34 push of the serialized height."""
    s = script_num(height)
    script = bytes([len(s)]) + s + tail
    return transaction([txin(NULL_PREVOUT, script)], [txout(50 * COIN)])


def chain_entry(height: int, time: int, bits: int = BITS) -> dict:
    return {"height": height, "time": time, "bits": bits}


def aligned_boundary(prev_height: int) -> int:
    return prev_height - ((prev_height + 1) % PERIOD)


def chain_to_boundary(prev_height: int, time: int) -> list[dict]:
    """A contiguous chain from `prev_height` down to the aligned boundary and its ten predecessors."""
    boundary = aligned_boundary(prev_height)
    low = max(0, boundary - 10)
    return [chain_entry(h, time) for h in range(prev_height, low - 1, -1)]


def period_boundary_chain(candidate_height: int, time: int) -> list[dict]:
    """The chain for a candidate at a period boundary: the predecessor and its ten predecessors."""
    assert candidate_height % PERIOD == 0
    prev = candidate_height - 1
    low = max(0, prev - 10)
    return [chain_entry(h, time) for h in range(prev, low - 1, -1)]


def short_chain(prev_height: int, time: int = TIME_BEFORE_CSV) -> list[dict]:
    """The chain for a candidate below the first period: the predecessor alone suffices (boundary null)."""
    assert prev_height + 1 < PERIOD
    return [chain_entry(prev_height, time)]


def key(req: dict) -> str:
    text = json.dumps({k: v for k, v in req.items() if k != "id"}, sort_keys=True)
    return hashlib.sha256(text.encode()).hexdigest()


def expect(req: dict, verdict) -> dict:
    """Record the expectation of a request. `verdict` is None for a valid block, or a reject reason."""
    assert verdict is None or verdict in BODY_REASONS
    EXPECTATIONS[key(req)] = verdict
    return req


def body_request(block_bytes: bytes, chain: list[dict], mode: str = "allow_witness") -> dict:
    return {"op": "block.contextual_check_body", "block_hex": block_bytes.hex(), "mode": mode, "chain": chain}


# ---------------------------------------------------------------------------
# Transactions for the finality check

A = (1).to_bytes(32, "little")[::-1]  # a nonzero 32-byte hash as an outpoint prefix


def nonfinal_tx(lock: int, sequence: int = 0) -> bytes:
    """A transaction with one input whose sequence is not final, and the given lock time."""
    return transaction([txin(bytes([7]) * 32 + (0).to_bytes(4, "little"), b"", sequence)], [txout(1)], lock=lock)


def final_by_sequence_tx(lock: int) -> bytes:
    """A transaction with a nonzero lock time but a final sequence, so it is final."""
    return transaction([txin(bytes([7]) * 32 + (0).to_bytes(4, "little"), b"", 0xffffffff)], [txout(1)], lock=lock)


# ---------------------------------------------------------------------------
# Request sets


def valid_cases() -> list[dict]:
    """Blocks that the body accepts, at the genesis position and below the first period."""
    out = []
    g = genesis_block()
    out.append(expect(body_request(g, []), None))
    # A block below the first period: version bits DEFINED, the body accepts a final block.
    out.append(expect(body_request(block([coinbase()]), short_chain(5000)), None))
    out.append(expect(body_request(block([coinbase(), spend(9)]), short_chain(5000)), None))
    return out


def finality_cases() -> list[dict]:
    """The finality check, bad-txns-nonfinal (lines 3139 to 3143)."""
    out = []
    chain = short_chain(5000)
    # A time-based lock time above the block time, with a non-final sequence: not final.
    out.append(expect(body_request(block([coinbase(), nonfinal_tx(TIME + 100)]), chain), "bad-txns-nonfinal"))
    # A height-based lock time above the candidate height, with a non-final sequence: not final.
    out.append(expect(body_request(block([coinbase(), nonfinal_tx(5001)]), chain), "bad-txns-nonfinal"))
    # A non-final lock time whose only input is final: the transaction is final.
    out.append(expect(body_request(block([coinbase(), final_by_sequence_tx(TIME + 100)]), chain), None))
    # A lock time of 0 is final.
    out.append(expect(body_request(block([coinbase(), nonfinal_tx(0)]), chain), None))
    # The coinbase is checked too: a non-final coinbase rejects.
    out.append(expect(body_request(
        block([transaction([txin(NULL_PREVOUT, b"\x51\x51", 0)], [txout(50 * COIN)], lock=TIME + 100)]),
        chain), "bad-txns-nonfinal"))
    return out


def coinbase_height_cases() -> list[dict]:
    """The BIP34 coinbase height, bad-cb-height (lines 3146 to 3152), at and around the activation height."""
    out = []
    bad_cb = coinbase(b"\x51\x51")  # a scriptSig that is not a height
    # At a period boundary at or after BIP34: the reason is reachable with an 11-entry chain.
    mult = ((BIP34_HEIGHT // PERIOD) + 1) * PERIOD  # 1,038,240
    out.append(expect(body_request(block([bad_cb]), period_boundary_chain(mult, TIME_BEFORE_CSV)),
                      "bad-cb-height"))
    out.append(expect(body_request(block([coinbase_with_height(mult)]),
                                   period_boundary_chain(mult, TIME_BEFORE_CSV)), None))
    # The exact activation boundary. The candidate height is the predecessor's height plus one.
    # At candidate 1,034,382 the check is off, and at 1,034,383 it is on.
    out.append(expect(body_request(block([bad_cb]), chain_to_boundary(BIP34_HEIGHT - 2, TIME_BEFORE_CSV)), None))
    out.append(expect(body_request(block([bad_cb]), chain_to_boundary(BIP34_HEIGHT - 1, TIME_BEFORE_CSV)),
                      "bad-cb-height"))
    out.append(expect(body_request(block([coinbase_with_height(BIP34_HEIGHT)]),
                                   chain_to_boundary(BIP34_HEIGHT - 1, TIME_BEFORE_CSV)), None))
    # A coinbase whose scriptSig is one byte short of the height still rejects, at candidate 1,034,383.
    short = script_num(BIP34_HEIGHT)
    out.append(expect(body_request(
        block([transaction([txin(NULL_PREVOUT, bytes([len(short)]) + short[:-1])], [txout(50 * COIN)])]),
        chain_to_boundary(BIP34_HEIGHT - 1, TIME_BEFORE_CSV)), "bad-cb-height"))
    # The BIP65 boundary: the body has no check there, so a correct-height block stays valid.
    for cand in (BIP65_HEIGHT - 1, BIP65_HEIGHT):
        out.append(expect(body_request(block([coinbase_with_height(cand)]),
                                       chain_to_boundary(cand - 1, TIME_AFTER_CSV)), None))
    return out


def witness_cases() -> list[dict]:
    """The witness check, unexpected-witness (lines 3183 to 3188)."""
    out = []
    chain = short_chain(5000)
    ext = Extended([txin(bytes([8]) * 32 + (0).to_bytes(4, "little"))], [txout(1)], [[b"\x01\x02\x03"]])
    out.append(expect(body_request(block([coinbase(), ext]), chain), "unexpected-witness"))
    # A coinbase with witness data is also unexpected.
    cb_ext = Extended([txin(NULL_PREVOUT, b"\x51\x51")], [txout(50 * COIN)], [[b"\x00" * 32]])
    out.append(expect(body_request(block([cb_ext]), chain), "unexpected-witness"))
    return out


def weight_cases() -> list[dict]:
    """The weight check, bad-blk-weight (line 3198), reachable when the body runs alone."""
    out = []
    chain = short_chain(5000)
    limit = 1000000  # MAX_BLOCK_WEIGHT / WITNESS_SCALE_FACTOR, the largest base size with weight <= MAX_BLOCK_WEIGHT

    def coinbase_of_size(size: int) -> bytes:
        return padded(lambda n: coinbase(outputs=[txout(50 * COIN, one_push(n))]), size)

    # A block of 1,000,000 base bytes has weight 4,000,000 and passes; 1,000,001 fails.
    for base, verdict in ((limit, None), (limit + 1, "bad-blk-weight")):
        data = block([coinbase_of_size(base - 81)])
        assert len(data) == base
        out.append(expect(body_request(data, chain), verdict))
    return out


def version_bits_cases() -> list[dict]:
    """Version-bits case 1 (DEFINED) and case 2 (seeded FAILED) at period boundaries."""
    out = []
    # Case 1: a boundary below the CSV start. Both states DEFINED, so not active.
    out.append(expect(body_request(block([coinbase()]), period_boundary_chain(PERIOD, TIME_BEFORE_CSV)), None))
    # Case 2: a boundary at or after the CSV timeout. The harness seeds FAILED; the state is not active.
    # The candidate is above BIP34, so the coinbase carries the height.
    mult = 180 * PERIOD  # 1,814,400
    out.append(expect(body_request(block([coinbase_with_height(mult)]),
                                   period_boundary_chain(mult, TIME_AFTER_CSV)), None))
    return out


def mainnet_body_sets(directory) -> list[tuple[str, list[dict]]]:
    """`block.contextual_check_body` on the real mainnet blocks below the first period.

    Only the genesis-to-10000 range is feasible from the committed fixtures: below height
    10,080 the aligned version-bits boundary is null, so the chain is the predecessor alone.
    The recent range and the rule-change blocks would need the predecessor headers back to each
    block's version-bits boundary, which the fixtures do not hold, so this set omits them.
    """
    import struct
    import fetch_release_blocks
    from oracle_block_check import fixture_blocks
    release = fetch_release_blocks.load_release()
    sets = []
    for entry in release["ranges"]:
        if entry["last"] >= PERIOD:
            continue
        blocks = fixture_blocks(pathlib.Path(directory) / entry["name"], fetch_release_blocks.sums_text(entry))
        requests, prev = [], None
        for record, raw in blocks:
            h = record["height"]
            if h == 0:
                chain = []
            else:
                chain = [chain_entry(h - 1, struct.unpack_from("<I", prev, 68)[0],
                                     struct.unpack_from("<I", prev, 72)[0])]
            requests.append(expect(body_request(raw, chain), None))
            prev = raw
        sets.append((f"block.contextual_check_body mainnet {entry['name']}", requests))
    return sets


def mainnet_body_counts() -> dict[str, int]:
    """Operation -> the number of `mainnet_body_sets` requests, for the operation-count check."""
    import fetch_release_blocks
    release = fetch_release_blocks.load_release()
    count = sum(entry["blocks"] for entry in release["ranges"] if entry["last"] < PERIOD)
    return {"block.contextual_check_body": count} if count else {}


_sets = None


def contextual_body_sets() -> list[tuple[str, list[dict]]]:
    global _sets
    if _sets is None:
        _sets = [
            ("contextual body valid", valid_cases()),
            ("contextual body finality", finality_cases()),
            ("contextual body coinbase height", coinbase_height_cases()),
            ("contextual body witness", witness_cases()),
            ("contextual body weight", weight_cases()),
            ("contextual body version bits", version_bits_cases()),
        ]
    return _sets


# ---------------------------------------------------------------------------
# Comparison


def same(a, b) -> bool:
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def malformed(ok, oracle: bool) -> str | None:
    fields = OK_FIELDS | ({"diagnostic"} if oracle else set())
    if not isinstance(ok, dict) or set(ok) != fields:
        return "must return exactly the fields " + ", ".join(sorted(fields))
    if type(ok["valid"]) is not bool:
        return "valid must be a boolean"
    if ok["valid"]:
        if ok["reject_reason"] is not None or ok["dos"] is not None or ok["reject_code"] is not None:
            return "a valid verdict has null rejection fields"
    else:
        reason = ok["reject_reason"]
        if reason not in BODY_REASONS:
            return f"returned the reason {reason!r}, which the body does not have"
        if ok["dos"] != BODY_REASONS[reason] or ok["reject_code"] != REJECT_INVALID:
            return f"returned score {ok['dos']!r} and code {ok['reject_code']!r} for {reason}"
    if oracle and not ok["valid"] and not isinstance(ok["diagnostic"], str):
        return "a rejection has no Lean diagnostic"
    return None


def compare(req: dict, ours: dict, core: dict, peer: str = "core") -> tuple[str, str] | None:
    """None when both programs give the same verdict, else a failure code and a message."""
    for side, response in (("oracle", ours), (peer, core)):
        if set(response) - {"id"} != {"ok"}:
            return "CONTEXTUAL_BODY", f"{side} must return a verdict"
        fault = malformed(response["ok"], side == "oracle")
        if fault:
            return "CONTEXTUAL_BODY", f"{side} {fault}"
    projected = {k: v for k, v in ours["ok"].items() if k != "diagnostic"}
    if not same(projected, core["ok"]):
        return "CONTEXTUAL_BODY", f"oracle {json.dumps(projected, sort_keys=True)}, {peer} {json.dumps(core['ok'], sort_keys=True)}"
    k = key(req)
    if k in EXPECTATIONS:  # membership, not the stored value: None is an expected acceptance
        expected = EXPECTATIONS[k]
        got = None if projected["valid"] else projected["reject_reason"]
        if got != expected:
            return "CONTEXTUAL_BODY", f"both disagree with the independent expectation {expected!r}, got {got!r}"
    return None


def reasons_reached(requests: list[dict], responses: list[dict]) -> dict[str, int]:
    counts = {}
    for req, response in zip(requests, responses):
        if req["op"] == "block.contextual_check_body":
            ok = response.get("ok")
            name = ("valid" if ok.get("valid") else str(ok.get("reject_reason"))) if isinstance(ok, dict) else "error"
            counts[name] = counts.get(name, 0) + 1
    return counts


def reasons_missing(counts: dict[str, int]) -> list[str]:
    return [f"block.contextual_check_body {reason}" for reason in BODY_REASONS if not counts.get(reason)]
