"""Compare the proposed revision RelativeLockTime with Core's own dormant code (design record 0012, section 10.2).

Usage: python3 -I scripts/compare_csv_forced.py [--mainnet-blocks DIR] [--made-only]
           <dogelib-oracle> <dogelib-proposal-oracle> <core-oracle>

The label of this evidence is: Core at `e0a1c15` with the CSV state forced to `ACTIVE`.
This state does not occur on mainnet (`csv_never_lockedIn`).

The harness takes the argument `force_csv_active` for `block.contextual_check_body`. With it, the
harness seeds THRESHOLD_ACTIVE for CSV in the version-bits cache, and Core's own
ContextualCheckBlock takes the median-time branch (SOURCES.md D110, src/validation.cpp, lines
3127 to 3140). No line of Core's source changes. The proposal executable answers the same
request with the argument `revision`, and the comparison reads its `revised` object.

Agreement shows that the Lean revision equals Core's dormant code on these requests. It is not a
Core comparison of the baseline, it is not evidence about mainnet, and it does not show that the
rule is right for Dogecoin. The revision is partial: this run covers the rule of BIP 113 alone.

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

With --made-only the run skips parts 4 and 5, and needs no downloaded block.
"""
import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import relative_lock_time_candidates as lister
from compare_core import RunError, run_stream
from oracle_block_check import NULL_PREVOUT, COIN, BITS, block, coinbase, genesis_block, transaction, txin, txout
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
          "(BIP 113 cutoff alone).")
    try:
        refused = refusals(args.oracle, args.proposal, args.harness, args.timeout)
        print(f"refusals: {refused} requests refused")
        made, reasons = made_run(args.proposal, args.harness, args.timeout)
        print(f"made blocks: {made} agree with the hand-derived verdicts, with and without the seed ("
              + ", ".join(f"{name} {count}" for name, count in sorted(reasons.items())) + ")")
        planted = self_test(args.proposal, args.harness, args.timeout)
        print(f"self-test: the comparison fails on {planted} planted faults")
        if not args.made_only:
            total = 0
            for group in mainnet_run(args.mainnet_blocks, args.proposal, args.harness, args.timeout):
                total += group["blocks"]
                print(f"{group['name']}: {group['blocks']} blocks agree; forced accepted {group['forced_accepted']}, "
                      f"forced rejected {group['forced_rejected']}, changed {group['changed']}, "
                      f"candidates {group['candidates']}, cutoff transactions {group['cutoff_transactions']}")
            print(f"mainnet blocks: {total} agree, and the changed blocks are the committed candidates")
    except (RuntimeError, RunError) as error:
        print(f"FAIL: {error}")
        return 1
    print("This state does not occur on mainnet (csv_never_lockedIn).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
