"""Compare the proposed revision RelativeLockTime with Core's own dormant code (design record 0012, section 10.2).

Usage: python3 -I scripts/compare_csv_forced.py [--mainnet-blocks DIR] [--made-only]
           <dogelib-oracle> <dogelib-proposal-oracle> <core-oracle>

The label of this evidence is: Core at `e0a1c15` with the CSV state forced to `ACTIVE`.
This state does not occur on mainnet (`csv_never_lockedIn`).

The harness takes the argument `force_csv_active` for `block.contextual_check_body` and for
`block.validate`. With it, the harness seeds THRESHOLD_ACTIVE for CSV in the version-bits cache.
Core's own ContextualCheckBlock then takes the median-time branch (SOURCES.md D110,
src/validation.cpp, lines 3127 to 3140), and Core's own ConnectBlock sets
SCRIPT_VERIFY_CHECKSEQUENCEVERIFY (D114, lines 1906 to 1911). No line of Core's source changes.
The proposal executable answers the same request with the argument `revision`, and the
comparison reads its `revised` object.

Agreement shows that the Lean revision equals Core's dormant code on these requests. It is not a
Core comparison of the baseline, it is not evidence about mainnet, and it does not show that the
rule is right for Dogecoin. The run covers the three rules of the revision: the cutoff of BIP 113
(parts 2 to 6), the opcode of BIP 112 (part 7) and the sequence locks of BIP 68 (parts 8 and 9).

The run has these parts:

1. Refusals. `dogelib-oracle` refuses both arguments, and each other program refuses the
   argument of the other.
2. Made blocks for each boundary of the cutoff. Each expectation is derived by hand from
   IsFinalTx (lines 258 to 269) and from lines 3127 to 3140, and from BIP 113 (SOURCES.md, P3).
   No expectation comes from DogeLib. The blocks have no proof of work.
3. The harness state. In one stream, a request without the argument follows each request with
   it, and gets the baseline result.
4. The 11,018 mainnet blocks of `block.contextual_check_body`, each with CSV forced active.
   The two programs must agree on each forced result. The run does not require acceptance.
5. The cutoff count. A block is *changed* when the baseline accepts it and the forced run
   rejects it. The changed blocks must be exactly the candidate blocks of the committed list,
   tests/proposals/relative-lock-time/cutoff-candidates.json.
6. A self-test. The comparison must fail when the Lean side runs with the revision inactive on
   a made block whose two verdicts differ, and when the harness runs without the seed.

7. `block.validate` with CSV forced active, on made blocks for the opcode of BIP 112. The harness
   runs each block twice on the state before it: with the seed, for the object `forced` of the
   block record, and without it. Each expectation is derived by hand from Core's code of the
   opcode (D3, src/script/interpreter.cpp, lines 392 to 427 and 1310 to 1354), from the two script
   runs of CheckInputs (D101, lines 1488 to 1512) and from BIP 112 (SOURCES.md, P2). The made
   blocks must reach `non-mandatory-script-verify-flag` through the opcode. The forced run must
   leave the rest of the response as it is without the argument. The comparison must fail on each
   planted fault, as in part 6.

8. `block.validate` with CSV forced active, on made blocks for the sequence locks of BIP 68. Each
   expectation is derived by hand from CalculateSequenceLocks and EvaluateSequenceLocks (D114,
   src/validation.cpp, lines 309 to 384) and from BIP 68 (SOURCES.md, P1). A time lock reads
   median times past, which this script computes from the header times of the request by the
   definition of GetMedianTimePast (D18). The made blocks must reach `bad-txns-nonfinal` through a
   sequence lock. Three kinds of block are outside the model of the revision (design record 0012,
   section 6.3). For them the harness does not run Core's ConnectBlock with the seed, and the
   field `unsupported` of `forced` names the reason. The `revised` object must then have the
   verdict `unsupported` with the same reason. The comparison must fail on each planted fault.
9. Mainnet heights 0 to 10,000 in one `block.validate` request, from the empty coin set. The
   harness runs each block twice on the state before it: with the seed and without it. Only the
   run without the seed carries the state. The two programs must agree on the forced result of
   each block. The run does not require acceptance.

With --made-only the run skips parts 4, 5 and 9, and needs no downloaded block.
"""
import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import relative_lock_time_candidates as lister
from compare_core import RunError, run_stream
from oracle_block_check import (NULL_PREVOUT, COIN, BITS, block, coinbase, genesis_block, sha256d, transaction, txin,
                                txout)
from oracle_block_validate import (EVAL_FALSE, Base, BlockAssets, Coins, coin_id, mainnet_validate_sets, outpoint, p2sh,
                                   push, script_reason)
from oracle_contextual_body import (PERIOD, TIME_AFTER_CSV, TIME_BEFORE_CSV, body_request, chain_entry,
                                    coinbase_with_height, final_by_sequence_tx, nonfinal_tx, period_boundary_chain)

REVISION = {"name": "RelativeLockTime", "variant": None, "activation_height": 1}
INACTIVE = {"name": "RelativeLockTime", "variant": None, "activation_height": None}
NONFINAL = ("bad-txns-nonfinal", 10, 16)  # reason, score and code of line 3141
GENESIS_TIME = 1386325540  # SOURCES.md D9, src/chainparams.cpp, line 155
BATCH_BYTES = 64 * 1024 * 1024


def check(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def run_batches(program: str, requests: list[dict], timeout: float) -> list[dict]:
    """The responses of `program`, with the requests sent in batches of bounded size."""
    responses, batch, size = [], [], 0
    for req in requests:
        weight = len(req.get("block_hex", "")) + 48 * len(req.get("chain", []))
        if batch and size + weight > BATCH_BYTES:
            responses += run_stream(program, batch, timeout)
            batch, size = [], 0
        batch.append(req)
        size += weight
    if batch:
        responses += run_stream(program, batch, timeout)
    return responses


def with_ids(requests: list[dict]) -> list[dict]:
    return [dict(req, id=i) for i, req in enumerate(requests)]


# ---------------------------------------------------------------------------
# Made blocks


def spaced_chain(prev_height: int, newest: int, count: int = 11, order=None) -> list[dict]:
    """A chain of `count` entries from `prev_height` down, newest first.

    Without `order`, entry i has the time `newest - 60 * i`. With it, entry i has the time
    `newest - 60 * order[i]`, so the times are not sorted along the chain."""
    order = list(range(count)) if order is None else order
    return [chain_entry(prev_height - i, newest - 60 * order[i]) for i in range(count)]


def made_cases() -> list[dict]:
    """Made blocks with hand-derived verdicts: `baseline` without CSV, and `forced` with CSV active.

    A verdict is None for an acceptance, or NONFINAL. IsFinalTx accepts a transaction whose lock
    time is 0, or below the cutoff, or whose inputs all have SEQUENCE_FINAL. For a lock time of at
    least 500,000,000 the cutoff is a time: the block time without CSV, and the median time past of
    the predecessor with CSV. The median of n times, n at most 11, is the sorted time at index n / 2."""
    cases = []

    def case(label, data, chain, baseline, forced):
        cases.append({"label": label, "block": data, "chain": chain, "baseline": baseline, "forced": forced})

    # Eleven predecessors at heights 4999 down to 4989, below the first period. Their times are
    # T0, T0 - 60, ..., T0 - 600. The sorted time at index 5 is T0 - 300: the median M.
    t0 = 1400000000
    median, block_time = t0 - 300, t0 + 60
    chain = spaced_chain(4999, t0)

    def one(lock, sequence=0):
        return block([coinbase(), nonfinal_tx(lock, sequence)], time=block_time)

    case("lock time one below the median cutoff", one(median - 1), chain, None, None)
    case("lock time equal to the median cutoff", one(median), chain, None, NONFINAL)
    case("lock time one above the median cutoff", one(median + 1), chain, None, NONFINAL)
    case("lock time one below the block time", one(block_time - 1), chain, None, NONFINAL)
    case("lock time equal to the block time", one(block_time), chain, NONFINAL, NONFINAL)
    case("lock time above the block time", one(block_time + 1), chain, NONFINAL, NONFINAL)
    case("sequence 0xfffffffe at the median cutoff", one(median, 0xfffffffe), chain, None, NONFINAL)
    case("final sequence at the median cutoff",
         block([coinbase(), final_by_sequence_tx(median)], time=block_time), chain, None, None)
    case("final sequence at the block time",
         block([coinbase(), final_by_sequence_tx(block_time)], time=block_time), chain, None, None)
    case("lock time 0", one(0), chain, None, None)
    # A lock time below 500,000,000 is a height. The candidate height is 5000, with and without CSV.
    case("height lock time below the height", one(4999), chain, None, None)
    case("height lock time equal to the height", one(5000), chain, NONFINAL, NONFINAL)
    case("largest height lock time", one(499999999), chain, NONFINAL, NONFINAL)
    # The coinbase is tested too. Its only input has the sequence 0 here.
    locked_coinbase = lambda lock: transaction([txin(NULL_PREVOUT, b"\x51\x51", 0)], [txout(50 * COIN)], lock=lock)
    case("coinbase at the median cutoff", block([locked_coinbase(median)], time=block_time), chain, None, NONFINAL)
    case("coinbase one below the median cutoff", block([locked_coinbase(median - 1)], time=block_time), chain,
         None, None)
    # Two inputs, one of them final: the transaction is not final by its sequences.
    mixed = transaction([txin(bytes([7]) * 32 + bytes(4), b"", 0xffffffff), txin(bytes([7]) * 32 + b"\x01" + bytes(3), b"", 5)],
                        [txout(1)], lock=median)
    case("one final and one other sequence at the median cutoff", block([coinbase(), mixed], time=block_time),
         chain, None, NONFINAL)
    # The second of two locked transactions fails.
    case("second transaction at the median cutoff",
         block([coinbase(), nonfinal_tx(median - 1), nonfinal_tx(median)], time=block_time), chain, None, NONFINAL)

    # The same times in another order along the chain. GetMedianTimePast sorts them.
    shuffled = spaced_chain(4999, t0, order=[7, 0, 10, 3, 5, 1, 9, 2, 8, 4, 6])
    case("unsorted times, lock time one below the median", one(median - 1), shuffled, None, None)
    case("unsorted times, lock time equal to the median", one(median), shuffled, None, NONFINAL)

    # A block time below the median. ContextualCheckBlockHeader rejects such a header with
    # time-too-old, and this operation runs no header check. The cutoff with CSV is then the
    # later one, so the forced run accepts a lock time that the baseline rejects.
    early = median - 100
    case("block time below the median, lock time between them",
         block([coinbase(), nonfinal_tx(early + 50)], time=early), chain, NONFINAL, None)
    case("block time below the median, lock time at the median",
         block([coinbase(), nonfinal_tx(median)], time=early), chain, NONFINAL, NONFINAL)

    # Height 1: the predecessor is the genesis block, and the median is its time.
    first = [chain_entry(0, GENESIS_TIME, 0x1e0ffff0)]
    at = lambda lock, time: block([coinbase(), nonfinal_tx(lock)], time=time)
    case("height 1, lock time one below the genesis time", at(GENESIS_TIME - 1, GENESIS_TIME + 60), first, None, None)
    case("height 1, lock time equal to the genesis time", at(GENESIS_TIME, GENESIS_TIME + 60), first, None, NONFINAL)
    # Height 3: three predecessors with the times G + 120, G + 60 and G. The sorted time at index 1 is G + 60.
    three = [chain_entry(2, GENESIS_TIME + 120), chain_entry(1, GENESIS_TIME + 60), chain_entry(0, GENESIS_TIME)]
    case("height 3, lock time one below the median", at(GENESIS_TIME + 59, GENESIS_TIME + 180), three, None, None)
    case("height 3, lock time equal to the median", at(GENESIS_TIME + 60, GENESIS_TIME + 180), three, None, NONFINAL)
    # Height 2: two predecessors with the times G + 60 and G. The sorted time at index 1 is G + 60, the later one.
    two = [chain_entry(1, GENESIS_TIME + 60), chain_entry(0, GENESIS_TIME)]
    case("height 2, lock time one below the median", at(GENESIS_TIME + 59, GENESIS_TIME + 120), two, None, None)
    case("height 2, lock time equal to the median", at(GENESIS_TIME + 60, GENESIS_TIME + 120), two, None, NONFINAL)
    # Height 11 has eleven predecessors down to height 0, and height 12 leaves height 0 out.
    eleven = spaced_chain(10, t0)
    case("height 11, lock time equal to the median", one(median), eleven, None, NONFINAL)
    twelve = spaced_chain(11, t0, count=12)
    case("height 12, lock time equal to the median", one(median), twelve, None, NONFINAL)
    case("height 12, lock time one below the median", one(median - 1), twelve, None, None)

    # A candidate at a period boundary: the aligned boundary is the predecessor, and its eleven
    # entries have one time, which is the median. Below the CSV start both states are DEFINED.
    for start, label in ((TIME_BEFORE_CSV, "before the CSV start"), (TIME_AFTER_CSV, "after the CSV timeout")):
        height = PERIOD if start == TIME_BEFORE_CSV else 180 * PERIOD
        boundary = period_boundary_chain(height, start)
        cb = coinbase() if start == TIME_BEFORE_CSV else coinbase_with_height(height)
        case(f"period boundary {label}, lock time one below the median",
             block([cb, nonfinal_tx(start - 1)], time=start + 60), boundary, None, None)
        case(f"period boundary {label}, lock time equal to the median",
             block([cb, nonfinal_tx(start)], time=start + 60), boundary, None, NONFINAL)

    # The genesis block is not applicable: without a predecessor, and by its hash with one.
    case("genesis block without a predecessor", genesis_block(), [], None, None)
    case("genesis block on a made chain", genesis_block(), chain, None, None)
    # A made block without a predecessor is not applicable either: the cutoff is its own time.
    case("made block without a predecessor", block([coinbase(), nonfinal_tx(block_time - 1)], time=block_time), [],
         None, None)
    return cases


def expected_fields(verdict) -> dict:
    if verdict is None:
        return {"valid": True, "reject_reason": None, "dos": None, "reject_code": None}
    reason, dos, code = verdict
    return {"valid": False, "reject_reason": reason, "dos": dos, "reject_code": code}


# ---------------------------------------------------------------------------
# Comparison


def core_fields(response: dict) -> dict | None:
    ok = response.get("ok")
    if not isinstance(ok, dict) or set(ok) != {"valid", "reject_reason", "dos", "reject_code"}:
        return None
    return ok


def revised_fields(response: dict) -> dict | None:
    """The `revised` object of a proposal response in the shape of a Core response, or None when it has no verdict."""
    revised = response.get("ok", {}).get("revised") if isinstance(response.get("ok"), dict) else None
    if not isinstance(revised, dict) or revised.get("verdict") not in ("accepted", "rejected"):
        return None
    return {"valid": revised["verdict"] == "accepted", "reject_reason": revised["reject_reason"],
            "dos": revised["dos"], "reject_code": revised["reject_code"]}


def baseline_fields(response: dict) -> dict | None:
    ok = response.get("ok")
    if not isinstance(ok, dict):
        return None
    return {k: ok.get(k) for k in ("valid", "reject_reason", "dos", "reject_code")}


def compare_forced(lean: dict, core: dict) -> str | None:
    """None when the `revised` object of the proposal executable and the forced result of Core agree."""
    ours, theirs = revised_fields(lean), core_fields(core)
    if ours is None:
        return f"the proposal executable gave no revised verdict: {json.dumps(lean)[:300]}"
    if theirs is None:
        return f"the harness gave no verdict: {json.dumps(core)[:300]}"
    if ours != theirs:
        return f"revised {json.dumps(ours, sort_keys=True)}, Core forced {json.dumps(theirs, sort_keys=True)}"
    return None


def refusals(oracle: str, proposal: str, harness: str, timeout: float) -> int:
    """`dogelib-oracle` refuses both arguments, and each other program refuses the argument of the other."""
    base = body_request(genesis_block(), [])
    probes = [(oracle, dict(base, revision=REVISION)), (oracle, dict(base, force_csv_active=True)),
              (proposal, dict(base, force_csv_active=True)), (harness, dict(base, revision=REVISION)),
              (harness, dict(base, force_csv_active=1))]
    for program, req in probes:
        response = run_stream(program, with_ids([req]), timeout)[0]
        kind = response.get("error", {}).get("kind") if isinstance(response.get("error"), dict) else None
        check(kind == "request", f"{program} did not refuse {sorted(set(req) - set(base))}: {json.dumps(response)[:300]}")
    return len(probes)


def made_run(proposal: str, harness: str, timeout: float) -> tuple[int, dict[str, int]]:
    cases = made_cases()
    requests = [body_request(c["block"], c["chain"]) for c in cases]
    lean = run_stream(proposal, with_ids([dict(r, revision=REVISION) for r in requests]), timeout)
    # Part 3: each forced request is followed by the same request without the argument.
    stream = []
    for r in requests:
        stream += [dict(r, force_csv_active=True), r, dict(r, force_csv_active=False)]
    core = run_stream(harness, with_ids(stream), timeout)
    reasons: dict[str, int] = {}
    for i, c in enumerate(cases):
        forced, plain, explicit = core[3 * i], core[3 * i + 1], core[3 * i + 2]
        label = c["label"]
        check(core_fields(forced) == expected_fields(c["forced"]),
              f"{label}: Core forced gave {json.dumps(forced)[:300]}, expected {expected_fields(c['forced'])}")
        check(core_fields(plain) == expected_fields(c["baseline"]),
              f"{label}: Core after a forced request gave {json.dumps(plain)[:300]}, expected the baseline "
              f"{expected_fields(c['baseline'])}")
        check(core_fields(explicit) == core_fields(plain), f"{label}: force_csv_active false differs from no argument")
        check(baseline_fields(lean[i]) == expected_fields(c["baseline"]),
              f"{label}: the baseline fields of the proposal executable are {json.dumps(lean[i])[:300]}")
        fault = compare_forced(lean[i], forced)
        check(fault is None, f"{label}: {fault}")
        # The candidate lister, on the same hand-derived expectation.
        _, _, _, found = lister.cutoff_transactions(c["block"], c["chain"])
        changed = c["baseline"] is None and c["forced"] is not None
        check(bool(found) == changed or c["baseline"] is not None,
              f"{label}: the candidate lister found {found}, and the verdicts change: {changed}")
        name = "valid" if c["forced"] is None else c["forced"][0]
        reasons[name] = reasons.get(name, 0) + 1
    check(reasons.get(NONFINAL[0]), "no made block reaches bad-txns-nonfinal from the cutoff")
    return len(cases), reasons


def self_test(proposal: str, harness: str, timeout: float) -> int:
    """The comparison fails on each planted fault: an inactive revision, and a harness run without the seed."""
    differing = [c for c in made_cases() if c["baseline"] != c["forced"]]
    check(len(differing) >= 10, "too few made blocks with two verdicts")
    requests = [body_request(c["block"], c["chain"]) for c in differing]
    active = run_stream(proposal, with_ids([dict(r, revision=REVISION) for r in requests]), timeout)
    inactive = run_stream(proposal, with_ids([dict(r, revision=INACTIVE) for r in requests]), timeout)
    forced = run_stream(harness, with_ids([dict(r, force_csv_active=True) for r in requests]), timeout)
    plain = run_stream(harness, with_ids(requests), timeout)
    for i, c in enumerate(differing):
        check(compare_forced(active[i], forced[i]) is None, f"self-test control {c['label']}: the comparison fails")
        check(compare_forced(inactive[i], forced[i]) is not None,
              f"self-test {c['label']}: the comparison passes with the revision inactive")
        check(compare_forced(active[i], plain[i]) is not None,
              f"self-test {c['label']}: the comparison passes without the forced seed")
    return 2 * len(differing)


def mainnet_run(directory, proposal: str, harness: str, timeout: float) -> list[dict]:
    listing = lister.load()
    committed = {g["name"]: g for g in listing["groups"]}
    summary = []
    for name, rows in lister.block_groups(directory):
        requests = [body_request(raw, chain) for _, raw, chain in rows]
        lean = run_batches(proposal, with_ids([dict(r, revision=REVISION) for r in requests]), timeout)
        core = run_batches(harness, with_ids([dict(r, force_csv_active=True) for r in requests]), timeout)
        accepted, rejected, changed = 0, 0, []
        for (record, _, _), ours, theirs in zip(rows, lean, core):
            fault = compare_forced(ours, theirs)
            check(fault is None, f"{name} height {record['height']}: {fault}")
            baseline, revised = baseline_fields(ours), revised_fields(ours)
            check(baseline is not None, f"{name} height {record['height']}: no baseline verdict")
            accepted += revised["valid"]
            rejected += not revised["valid"]
            if baseline["valid"] and not revised["valid"]:
                changed.append(record["height"])
            # relativeLockTime_restricts is about validateBlock. Here the body runs alone, and the
            # real blocks passed the header check, so a change still goes from accepted to rejected.
            check(baseline["valid"] or not revised["valid"],
                  f"{name} height {record['height']}: the forced run accepts a block that the baseline rejects")
        group = committed.get(name)
        check(group is not None and group["blocks"] == len(rows),
              f"{name}: the committed candidate list does not have this group with {len(rows)} blocks")
        candidates = [c["height"] for c in group["candidates"]]
        check(changed == candidates,
              f"{name}: changed blocks {changed[:20]} differ from the committed candidates {candidates[:20]}")
        summary.append({"name": name, "blocks": len(rows), "forced_accepted": accepted, "forced_rejected": rejected,
                        "changed": len(changed), "candidates": len(candidates),
                        "cutoff_transactions": group["cutoff_transactions"]})
    check(sum(g["blocks"] for g in summary) == listing["blocks"], "the groups do not have the blocks of the list")
    return summary


# ---------------------------------------------------------------------------
# block.validate: the opcode of BIP 112

# Core's texts of the script errors (src/script/script_error.cpp).
UNSATISFIED_LOCKTIME = "Locktime requirement not satisfied"
NEGATIVE_LOCKTIME = "Negative locktime"
UNKNOWN_ERROR = "unknown error"
INVALID_STACK_OPERATION = "Operation not valid with the current stack size"
CSV, OP_0, OP_1, OP_2, OP_1NEGATE, OP_IF, OP_ELSE, OP_ENDIF, OP_DROP = 0xb2, 0x00, 0x51, 0x52, 0x4f, 0x63, 0x67, 0x68, 0x75
TYPE_FLAG, DISABLE_FLAG = 1 << 22, 1 << 31


def not_mandatory(text: str) -> tuple:
    """A script failure that passes without the flags that are not mandatory: score 0 and REJECT_NONSTANDARD (D101, lines 1500 to 1503)."""
    return script_reason(False, text), 0, 64


def mandatory(text: str) -> tuple:
    """A script failure that also fails the second run: score 100 and REJECT_INVALID (D101, line 1511)."""
    return script_reason(True, text), 100, 16


def validate_cases() -> list[dict]:
    """Made blocks for `block.validate`: `baseline` without CSV, and `forced` with CSV active.

    Each block has a coinbase and one transaction, which spends one supplied coin. Without the CSV
    flag, opcode 0xb2 is OP_NOP3. With it, OP_CHECKSEQUENCEVERIFY reads the top item n and never
    pops it. An empty stack, an item above five bytes and a negative n fail. Bit 31 of n makes the
    opcode a NOP. Otherwise CheckSequence fails for a transaction version below 2 as an unsigned
    value, for bit 31 of the input's sequence, for unequal bits 22, and for a masked n above the
    masked sequence. The mask is 0x0040ffff. The flag is not mandatory, so a failure through the
    opcode alone has the reason `non-mandatory-script-verify-flag`.

    The supplied coin has the height 100,000, far below the block. A version 2 input whose sequence
    is a height lock of n blocks therefore passes the sequence lock of BIP 68, in Core and in the
    revision. One case has a time lock of 0 on a coin one block below the block, which passes too.
    No case rejects through BIP 68."""
    cases = []
    for height in (1034382, 3464751):
        base = Base(height)

        def case(label, script, version, sequence, baseline, forced, script_sig=b"", coin_height=100000):
            coins = Coins()
            point = coins.add(coin_id(1), 0, 1000, bytes(script), height=coin_height)
            tx = transaction([txin(point, bytes(script_sig), sequence)], [txout(1)], version=version)
            cases.append({"label": f"height {height}, {label}", "baseline": baseline, "forced": forced,
                          "request": base.request([base.block([base.coinbase(), tx])], coins)})

        unsatisfied = not_mandatory(UNSATISFIED_LOCKTIME)
        # OP_1 CSV: a height lock of 1 against the sequence 1 is met exactly.
        case("operand 1, sequence 1, version 2", [OP_1, CSV], 2, 1, None, None)
        # OP_2 CSV: a height lock of 2 against the sequence 1 is one short.
        case("operand 2, sequence 1, version 2", [OP_2, CSV], 2, 1, None, unsatisfied)
        case("operand 1, sequence 1, version 1", [OP_1, CSV], 1, 1, None, unsatisfied)
        # Version -1 is 0xffffffff as an unsigned value, which is at least 2.
        case("operand 1, sequence 1, version -1", [OP_1, CSV], -1, 1, None, None)
        case("operand 1, sequence with bit 31", [OP_1, CSV], 2, DISABLE_FLAG | 1, None, unsatisfied)
        # Bits of the sequence outside the mask do not count: 0x00010001 is 1 under the mask.
        case("operand 1, sequence 0x00010001", [OP_1, CSV], 2, 0x00010001, None, None)
        case("operand 2, sequence 0x00010001", [OP_2, CSV], 2, 0x00010001, None, unsatisfied)
        # The operand 00 00 40 is 0x400000: a time lock of 0.
        time_operand = [0x03, 0x00, 0x00, 0x40, CSV]
        case("time operand, height sequence", time_operand, 2, 1, None, unsatisfied)
        case("time operand, time sequence", time_operand, 2, TYPE_FLAG, None, None, coin_height=height - 1)
        # The operand 00 00 00 80 00 is 0x80000000: bit 31 makes the opcode a NOP, also for version 1.
        case("operand with bit 31, version 1", [0x05, 0x00, 0x00, 0x00, 0x80, 0x00, CSV], 1, 0, None, None)
        case("operand -1", [OP_1NEGATE, CSV], 2, 1, None, not_mandatory(NEGATIVE_LOCKTIME))
        # A push of six bytes. The item is true, and its decode fails.
        case("operand of six bytes", [0x06, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, CSV], 2, 1, None,
             not_mandatory(UNKNOWN_ERROR))
        case("empty stack", [CSV, OP_1], 2, 1, None, not_mandatory(INVALID_STACK_OPERATION))
        # OP_1 OP_IF OP_1 OP_ELSE OP_0 CSV OP_ENDIF: the opcode is in a branch that does not execute.
        case("opcode in a skipped branch, version 1", [OP_1, OP_IF, OP_1, OP_ELSE, OP_0, CSV, OP_ENDIF], 1, 1, None, None)
        # OP_1 CSV OP_DROP OP_0 leaves a false item: a mandatory failure with and without the flag.
        false_result = mandatory(EVAL_FALSE)
        case("false result", [OP_1, CSV, OP_DROP, OP_0], 2, 1, false_result, false_result)
        # The opcode in the scriptSig, against the scriptPubKey OP_1.
        case("opcode in the scriptSig, version 1", [OP_1], 1, 1, None, unsatisfied, script_sig=[OP_1, CSV])
        # The opcode in a P2SH redeem script OP_1 CSV. The scriptSig is the push of the redeem script.
        redeem = bytes([OP_1, CSV])
        case("opcode in a redeem script, version 1", p2sh(redeem), 1, 1, None, unsatisfied, script_sig=push(redeem))
        case("opcode in a redeem script, version 2", p2sh(redeem), 2, 1, None, None, script_sig=push(redeem))
    return cases


VERDICT_KEYS = ("valid", "reject_reason", "dos", "reject_code")


def validate_record(response: dict) -> dict | None:
    """The one block record of a `block.validate` response."""
    ok = response.get("ok")
    if not isinstance(ok, dict) or not isinstance(ok.get("blocks"), list) or len(ok["blocks"]) != 1:
        return None
    return ok["blocks"][0]


FORCED_KEYS = {*VERDICT_KEYS, "changes_digest_hex", "spent", "created", "unsupported"}
REASON_PREFIX = "RelativeLockTime: "
REASONS = ("ancestorOutsideView", "coinAboveBlock", "heightOutOfDomain")


def forced_record_fields(forced) -> dict | None:
    """The verdict fields, the digest of the changes and the reason outside the model of an object `forced`.

    With a reason, the harness did not run ConnectBlock with the seed, and every other field is null."""
    if not isinstance(forced, dict) or set(forced) != FORCED_KEYS:
        return None
    if forced["unsupported"] is not None:
        if forced["unsupported"] not in REASONS or any(forced[k] is not None for k in FORCED_KEYS - {"unsupported"}):
            return None
    return {k: forced[k] for k in (*VERDICT_KEYS, "changes_digest_hex", "unsupported")}


def revised_record_fields(revised) -> dict | None:
    """An object `revised` of the proposal record, in the shape of `forced_record_fields`.

    An unsupported result of the sequence locks has the reason of the revision. Another unsupported
    result has no counterpart in Core, and gives None."""
    if not isinstance(revised, dict):
        return None
    if revised.get("verdict") == "unsupported":
        reason = revised.get("reason")
        if not isinstance(reason, str) or not reason.startswith(REASON_PREFIX):
            return None
        return {**{k: None for k in (*VERDICT_KEYS, "changes_digest_hex")}, "unsupported": reason[len(REASON_PREFIX):]}
    if revised.get("verdict") not in ("accepted", "rejected"):
        return None
    return {"valid": revised["verdict"] == "accepted", "reject_reason": revised["reject_reason"],
            "dos": revised["dos"], "reject_code": revised["reject_code"],
            "changes_digest_hex": revised["changes_digest_hex"], "unsupported": None}


def forced_validate_fields(response: dict) -> dict | None:
    """The object `forced` of the harness record: its verdict fields and the digest of its changes."""
    record = validate_record(response)
    forced = record.get("forced") if record else None
    return forced_record_fields(forced)


def revised_validate_fields(response: dict) -> dict | None:
    """The object `revised` of the proposal record, in the shape of `forced_validate_fields`."""
    record = validate_record(response)
    revised = record.get("revised") if record else None
    return revised_record_fields(revised)


def compare_forced_validate(lean: dict, core: dict) -> str | None:
    """None when the `revised` object of the proposal executable and the `forced` object of Core agree."""
    ours, theirs = revised_validate_fields(lean), forced_validate_fields(core)
    if ours is None:
        return f"the proposal executable gave no revised verdict: {json.dumps(lean)[:300]}"
    if theirs is None:
        return f"the harness gave no forced object: {json.dumps(core)[:300]}"
    if ours != theirs:
        return f"revised {json.dumps(ours, sort_keys=True)}, Core forced {json.dumps(theirs, sort_keys=True)}"
    return None


def without_forced(response: dict) -> dict:
    """The response without the object `forced` of each block record."""
    ok = response.get("ok")
    if not isinstance(ok, dict) or not isinstance(ok.get("blocks"), list):
        return response
    return {**response, "ok": {**ok, "blocks": [{k: v for k, v in b.items() if k != "forced"} for b in ok["blocks"]]}}


def validate_refusals(oracle: str, proposal: str, harness: str, timeout: float) -> int:
    """Each program refuses the argument of the other for `block.validate`."""
    base = Base(1034382)
    coins = Coins()
    point = coins.add(coin_id(1), 0, 1000, bytes([OP_1]))
    plain = base.request([base.block([base.coinbase(), transaction([txin(point, b"", 1)], [txout(1)], version=2)])], coins)
    probes = [(oracle, dict(plain, force_csv_active=True)), (proposal, dict(plain, force_csv_active=True)),
              (harness, dict(plain, revision=REVISION)), (harness, dict(plain, force_csv_active=1))]
    for program, req in probes:
        response = run_stream(program, with_ids([req]), timeout)[0]
        kind = response.get("error", {}).get("kind") if isinstance(response.get("error"), dict) else None
        check(kind == "request", f"{program} did not refuse a block.validate request: {json.dumps(response)[:300]}")
    return len(probes)


def validate_run(proposal: str, harness: str, timeout: float) -> tuple[int, dict[str, int], int]:
    cases = validate_cases()
    requests = [c["request"] for c in cases]
    lean = run_stream(proposal, with_ids([dict(r, revision=REVISION) for r in requests]), timeout)
    inactive = run_stream(proposal, with_ids([dict(r, revision=INACTIVE) for r in requests]), timeout)
    # Each forced request is followed by the same request without the argument, in one stream.
    stream = []
    for r in requests:
        stream += [dict(r, force_csv_active=True), r, dict(r, force_csv_active=False)]
    core = run_stream(harness, with_ids(stream), timeout)
    reasons: dict[str, int] = {}
    planted = 0

    def verdict(fields):
        return None if fields is None else {k: fields[k] for k in VERDICT_KEYS}

    for i, c in enumerate(cases):
        forced, plain, explicit = core[3 * i], core[3 * i + 1], core[3 * i + 2]
        label = c["label"]
        check(verdict(forced_validate_fields(forced)) == expected_fields(c["forced"]),
              f"{label}: Core forced gave {json.dumps(forced)[:400]}, expected {expected_fields(c['forced'])}")
        record = validate_record(plain)
        check(record is not None and {k: record[k] for k in VERDICT_KEYS} == expected_fields(c["baseline"]),
              f"{label}: Core without the seed gave {json.dumps(plain)[:400]}, expected {expected_fields(c['baseline'])}")
        # The forced run changes no carried state, and leaves no seed.
        same = {k: v for k, v in without_forced(forced).items() if k != "id"} == {k: v for k, v in plain.items() if k != "id"}
        check(same, f"{label}: the response with the argument differs from the response without it, apart from `forced`")
        check({k: v for k, v in explicit.items() if k != "id"} == {k: v for k, v in plain.items() if k != "id"},
              f"{label}: force_csv_active false differs from no argument")
        # An accepted forced run has the changes of the accepted run without the seed.
        if c["forced"] is None and c["baseline"] is None:
            check(forced_validate_fields(forced)["changes_digest_hex"] == record["changes_digest_hex"],
                  f"{label}: the forced run and the run without the seed have different changes")
        ours = validate_record(lean[i])
        check(ours is not None and {k: ours[k] for k in VERDICT_KEYS} == expected_fields(c["baseline"]),
              f"{label}: the baseline fields of the proposal executable are {json.dumps(lean[i])[:400]}")
        fault = compare_forced_validate(lean[i], forced)
        check(fault is None, f"{label}: {fault}")
        # relativeLockTime_restricts: a block that the revision accepts, the baseline accepts.
        check(c["forced"] is not None or c["baseline"] is None, f"{label}: the expectation relaxes the baseline")
        # The self-test: with the revision inactive, or without the seed, the comparison fails on a block with two verdicts.
        if c["baseline"] != c["forced"]:
            check(compare_forced_validate(inactive[i], forced) is not None,
                  f"self-test {label}: the comparison passes with the revision inactive")
            # The record without the seed, in the place of `forced`: the response keeps its shape,
            # so the comparison must fail on the verdict.
            unseeded = {**forced, "ok": {**forced["ok"], "blocks": [
                {**validate_record(forced), "forced": {**{k: record[k] for k in (*VERDICT_KEYS, "changes_digest_hex",
                                                                                "spent", "created")},
                                                       "unsupported": None}}]}}
            check(forced_validate_fields(unseeded) is not None, f"self-test {label}: the unseeded record has no shape")
            fault = compare_forced_validate(lean[i], unseeded)
            check(fault is not None and fault.startswith("revised "),
                  f"self-test {label}: the comparison passes without the forced seed")
            fault = compare_forced_validate(inactive[i], forced)
            check(fault is not None and fault.startswith("revised "),
                  f"self-test {label}: the inactive revision fails on the shape, not on the verdict")
            planted += 2
        name = "valid" if c["forced"] is None else c["forced"][0].split(" (")[0]
        reasons[name] = reasons.get(name, 0) + 1
    check(reasons.get("non-mandatory-script-verify-flag"),
          "no made block reaches non-mandatory-script-verify-flag through the opcode")
    check(planted >= 20, "too few made blocks with two verdicts")
    return len(cases), reasons, planted


# ---------------------------------------------------------------------------
# block.validate: the sequence locks of BIP 68

SEQUENCE_NONFINAL = ("bad-txns-nonfinal", 100, 16)  # reason, score and code of lines 1956 to 1958


def median_time_past(chain: list[dict], height: int) -> int:
    """GetMedianTimePast of the chain entry at `height` (D18, src/chain.h, lines 286 to 298): the sorted time at index n / 2 of the entry and of up to ten predecessors."""
    times = {e["height"]: e["time"] for e in chain}
    span = sorted(times[h] for h in range(height - 10, height + 1))
    return span[len(span) // 2]


def sequence_cases() -> list[dict]:
    """Made blocks for the sequence locks: `forced` with CSV active is a verdict, or the name of a reason outside the model.

    Each block has a coinbase and one or two transactions. The spent coin has the script OP_1, so
    every script passes, and the baseline accepts every block: it has no sequence lock.
    SequenceLocks applies to a transaction whose version is at least 2 as an unsigned value. An
    input whose sequence has bit 31 clear has a lock. Let n be its low 16 bits, c the height of its
    coin and H the height of the block. With bit 22 clear the transaction fails unless
    c + n <= H. With bit 22 set it fails unless t + 512 * n <= m, where m is the median time past
    of the predecessor and t that of the ancestor at max(c - 1, 0). A failure is
    `bad-txns-nonfinal` with the score 100. A coin that the block itself creates has c = H."""
    cases = []
    for height in (1034382, 3464751):
        base = Base(height)

        def case(label, forced, sequence, coin_height, version=2, same_block=False):
            coins = Coins()
            point = coins.add(coin_id(1), 0, 1000, bytes([OP_1]), height=coin_height)
            txs = []
            if same_block:
                # A first transaction with a final sequence creates the coin in the block.
                first = transaction([txin(point, b"", 0xffffffff)], [txout(1, bytes([OP_1]))])
                txs.append(first)
                point = outpoint(sha256d(first))
            txs.append(transaction([txin(point, b"", sequence)], [txout(1)], version=version))
            cases.append({"label": f"height {height}, {label}", "forced": forced,
                          "request": base.request([base.block([base.coinbase()] + txs)], coins)})

        # Height locks, on a coin 10 blocks below the block.
        case("height lock met exactly", None, 10, height - 10)
        case("height lock one block short", SEQUENCE_NONFINAL, 11, height - 10)
        case("height lock on a coin one block higher", SEQUENCE_NONFINAL, 10, height - 9)
        # The version is compared as an unsigned value: 1 is below 2, and -1 is 0xffffffff.
        case("short height lock, version 1", None, 11, height - 10, version=1)
        case("short height lock, version -1", SEQUENCE_NONFINAL, 11, height - 10, version=-1)
        case("met height lock, version -1", None, 10, height - 10, version=-1)
        # Bit 31 turns the lock of the input off.
        case("short height lock with bit 31", None, DISABLE_FLAG | 11, height - 10)
        # Bits 16 to 21 and 23 to 30 are outside the mask 0x0040ffff: 0x7fbf000a is a height lock of 10.
        case("bits outside the mask, lock met", None, 0x7fbf000a, height - 10)
        case("bits outside the mask, lock short", SEQUENCE_NONFINAL, 0x7fbf000b, height - 10)
        # A coin of the same block has the height of the block. Its time lock reads the predecessor.
        case("coin of the same block, height lock 0", None, 0, 100000, same_block=True)
        case("coin of the same block, height lock 1", SEQUENCE_NONFINAL, 1, 100000, same_block=True)
        case("coin of the same block, time lock 0", None, TYPE_FLAG, 100000, same_block=True)
        case("coin of the same block, time lock 1", SEQUENCE_NONFINAL, TYPE_FLAG | 1, 100000, same_block=True)
        # A time lock on a coin 20 blocks below the block. The lock of n units is met exactly when
        # t + 512 * n <= m, so the largest n that passes is the whole number of units in m - t.
        m, t = median_time_past(base.chain, height - 1), median_time_past(base.chain, height - 21)
        check(0 <= m - t < 512 * 0xffff, f"height {height}: the medians {m} and {t} give no time lock in range")
        units = (m - t) // 512
        case(f"time lock of {units} units, the largest that is met", None, TYPE_FLAG | units, height - 20)
        case(f"time lock of {units + 1} units, one unit more", SEQUENCE_NONFINAL, TYPE_FLAG | (units + 1), height - 20)
        case("short time lock, version 1", None, TYPE_FLAG | (units + 1), height - 20, version=1)
        # A height lock on a coin one block above the block reads no ancestor: (H + 1) + 0 - 1 is not below H.
        case("coin above the block, height lock 0", SEQUENCE_NONFINAL, 0, height + 1)
        # Outside the model of the revision. The harness does not run ConnectBlock with the seed.
        case("coin above the block, time lock", "coinAboveBlock", TYPE_FLAG, height + 1)
        case("coin two blocks above the block, time lock", "coinAboveBlock", TYPE_FLAG, height + 2)
        # The ancestor at height 99,999 is below the chain of the request.
        case("time lock on a coin below the chain", "ancestorOutsideView", TYPE_FLAG, 100000)
        # Core's sum c + 65535 does not fit `int` from this coin height.
        case("coin height 2^31 - 65535, height lock", "heightOutOfDomain", 1, 2**31 - 65535)
        case("coin height 2^31 - 65535, time lock", "heightOutOfDomain", TYPE_FLAG, 2**31 - 65535)
        # With bit 31 the input has no lock, so no read is outside the model.
        case("coin height 2^31 - 65535, bit 31", None, DISABLE_FLAG, 2**31 - 65535)
    return cases


def expected_sequence_fields(forced) -> dict:
    """The verdict fields and the reason of an expectation of `sequence_cases`."""
    if isinstance(forced, str):
        return {**{k: None for k in VERDICT_KEYS}, "unsupported": forced}
    return {**expected_fields(forced), "unsupported": None}


def sequence_run(proposal: str, harness: str, timeout: float) -> tuple[int, dict[str, int], int]:
    cases = sequence_cases()
    requests = [c["request"] for c in cases]
    lean = run_stream(proposal, with_ids([dict(r, revision=REVISION) for r in requests]), timeout)
    inactive = run_stream(proposal, with_ids([dict(r, revision=INACTIVE) for r in requests]), timeout)
    # Each forced request is followed by the same request without the argument, in one stream.
    stream = []
    for r in requests:
        stream += [dict(r, force_csv_active=True), r]
    core = run_stream(harness, with_ids(stream), timeout)
    results: dict[str, int] = {}
    planted = 0
    for i, c in enumerate(cases):
        forced, plain, label = core[2 * i], core[2 * i + 1], c["label"]
        want = expected_sequence_fields(c["forced"])
        got = forced_validate_fields(forced)
        check(got is not None and {k: got[k] for k in want} == want,
              f"{label}: Core forced gave {json.dumps(forced)[:400]}, expected {want}")
        # The baseline has no sequence lock: Core without the seed and the proposal executable accept.
        record = validate_record(plain)
        check(record is not None and record["valid"] is True, f"{label}: Core without the seed gave {json.dumps(plain)[:400]}")
        same = {k: v for k, v in without_forced(forced).items() if k != "id"} == {k: v for k, v in plain.items() if k != "id"}
        check(same, f"{label}: the response with the argument differs from the response without it, apart from `forced`")
        if c["forced"] is None:
            check(got["changes_digest_hex"] == record["changes_digest_hex"],
                  f"{label}: the forced run and the run without the seed have different changes")
        ours = validate_record(lean[i])
        check(ours is not None and ours["valid"] is True,
              f"{label}: the baseline fields of the proposal executable are {json.dumps(lean[i])[:400]}")
        fault = compare_forced_validate(lean[i], forced)
        check(fault is None, f"{label}: {fault}")
        # The self-test: with the revision inactive, the comparison fails on every block that the
        # forced run does not accept, on the verdict and not on the shape.
        if c["forced"] is not None:
            fault = compare_forced_validate(inactive[i], forced)
            check(fault is not None and fault.startswith("revised "),
                  f"self-test {label}: the comparison passes with the revision inactive")
            # The record without the seed, in the place of `forced`.
            unseeded = {**forced, "ok": {**forced["ok"], "blocks": [
                {**validate_record(forced), "forced": {**{k: record[k] for k in (*VERDICT_KEYS, "changes_digest_hex",
                                                                                "spent", "created")},
                                                       "unsupported": None}}]}}
            fault = compare_forced_validate(lean[i], unseeded)
            check(fault is not None and fault.startswith("revised "),
                  f"self-test {label}: the comparison passes without the forced seed")
            planted += 2
        name = "valid" if c["forced"] is None else c["forced"] if isinstance(c["forced"], str) else c["forced"][0]
        results[name] = results.get(name, 0) + 1
    for name in ("bad-txns-nonfinal", *REASONS):
        check(results.get(name), f"no made block reaches {name} through a sequence lock")
    return len(cases), results, planted


def mainnet_validate_run(directory: str, proposal: str, harness: str, timeout: float) -> dict[str, int]:
    """Heights 0 to 10,000 of mainnet in one request, with CSV forced active for each block (section 10.2, item 1)."""
    [(_, [req])] = mainnet_validate_sets(directory)
    lean = run_batches(proposal, with_ids([dict(req, revision=REVISION)]), timeout)[0]
    core = run_batches(harness, with_ids([dict(req, force_csv_active=True)]), timeout)[0]
    ours = lean.get("ok", {}).get("blocks") if isinstance(lean.get("ok"), dict) else None
    theirs = core.get("ok", {}).get("blocks") if isinstance(core.get("ok"), dict) else None
    check(isinstance(ours, list) and isinstance(theirs, list) and len(ours) == len(theirs) == len(req["blocks_hex"]),
          f"the replay has no record for each block: {json.dumps(lean)[:200]} and {json.dumps(core)[:200]}")
    counts = {"blocks": len(ours), "forced_accepted": 0, "forced_rejected": 0, "forced_unsupported": 0, "changed": 0}
    for mine, yours in zip(ours, theirs):
        height = mine.get("height")
        check(height == yours.get("height") and mine.get("hash_hex") == yours.get("hash_hex"),
              f"the two replays differ at a block: {height} and {yours.get('height')}")
        # The baseline run carries the state, so both programs must accept each block of mainnet.
        check(mine.get("valid") is True and yours.get("valid") is True, f"height {height}: the baseline run rejects the block")
        revised, forced = revised_record_fields(mine.get("revised")), forced_record_fields(yours.get("forced"))
        check(revised is not None, f"height {height}: no revised verdict: {json.dumps(mine)[:300]}")
        check(forced is not None, f"height {height}: no forced object: {json.dumps(yours)[:300]}")
        check(revised == forced,
              f"height {height}: revised {json.dumps(revised, sort_keys=True)}, Core forced {json.dumps(forced, sort_keys=True)}")
        # The genesis block is not applicable: its forced result is the result without the seed.
        check(height != 0 or (mine["revised"].get("active") is False and forced["valid"] is True),
              "height 0: the genesis block does not have the baseline result")
        if forced["unsupported"] is not None:
            counts["forced_unsupported"] += 1
        elif forced["valid"]:
            counts["forced_accepted"] += 1
        else:
            counts["forced_rejected"] += 1
            counts["changed"] += 1
    return counts


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--mainnet-blocks", default=str(ROOT / "build/mainnet-blocks"))
    parser.add_argument("--made-only", action="store_true", help="skip the mainnet blocks and the cutoff count")
    parser.add_argument("--timeout", type=float, default=3600.0)
    parser.add_argument("oracle")
    parser.add_argument("proposal")
    parser.add_argument("harness")
    args = parser.parse_args()
    print("Core at e0a1c15 with the CSV state forced to ACTIVE, against the proposed revision RelativeLockTime "
          "(the BIP 113 cutoff, the BIP 112 opcode and the BIP 68 sequence locks).")
    try:
        refused = refusals(args.oracle, args.proposal, args.harness, args.timeout)
        print(f"refusals: {refused} requests refused")
        made, reasons = made_run(args.proposal, args.harness, args.timeout)
        print(f"made blocks: {made} agree with the hand-derived verdicts, with and without the seed ("
              + ", ".join(f"{name} {count}" for name, count in sorted(reasons.items())) + ")")
        planted = self_test(args.proposal, args.harness, args.timeout)
        print(f"self-test: the comparison fails on {planted} planted faults")
        refused = validate_refusals(args.oracle, args.proposal, args.harness, args.timeout)
        print(f"block.validate refusals: {refused} requests refused")
        made, reasons, planted = validate_run(args.proposal, args.harness, args.timeout)
        print(f"block.validate made blocks: {made} agree with the hand-derived verdicts, with and without the seed ("
              + ", ".join(f"{name} {count}" for name, count in sorted(reasons.items())) + ")")
        print(f"block.validate self-test: the comparison fails on {planted} planted faults")
        made, results, planted = sequence_run(args.proposal, args.harness, args.timeout)
        print(f"sequence locks, made blocks: {made} agree with the hand-derived results ("
              + ", ".join(f"{name} {count}" for name, count in sorted(results.items())) + ")")
        print(f"sequence locks, self-test: the comparison fails on {planted} planted faults")
        if not args.made_only:
            total = 0
            for group in mainnet_run(args.mainnet_blocks, args.proposal, args.harness, args.timeout):
                total += group["blocks"]
                print(f"{group['name']}: {group['blocks']} blocks agree; forced accepted {group['forced_accepted']}, "
                      f"forced rejected {group['forced_rejected']}, changed {group['changed']}, "
                      f"candidates {group['candidates']}, cutoff transactions {group['cutoff_transactions']}")
            print(f"mainnet blocks: {total} agree, and the changed blocks are the committed candidates")
            counts = mainnet_validate_run(args.mainnet_blocks, args.proposal, args.harness, args.timeout)
            print(f"block.validate, mainnet heights 0 to {counts['blocks'] - 1}: {counts['blocks']} forced results agree; "
                  f"accepted {counts['forced_accepted']}, rejected {counts['forced_rejected']}, "
                  f"outside the model {counts['forced_unsupported']}, changed {counts['changed']}")
    except (RuntimeError, RunError, BlockAssets) as error:
        print(f"FAIL: {error}")
        return 1
    print("This state does not occur on mainnet (csv_never_lockedIn).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
