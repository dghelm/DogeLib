#!/usr/bin/env python3
"""Self-test of scripts/impact_candidates.py and scripts/impact_run.py.

Usage: python3 -I scripts/test_impact.py <dogelib-proposal-oracle>

It needs no Dogecoin Core and no download. The checks:

1. Candidates on made blocks. Each case is one block with a stated script, transaction or coin,
   and a candidate set that this file states by hand from the definitions of
   scripts/impact_candidates.py. A byte `0xb9` inside push data and an opcode after a truncated
   push are not instructions. A P2SH redeem script and a missing coin make a candidate. The
   sequence and cutoff cases sit at each boundary of their definitions.
2. The checks of a run, on made responses: a correct response passes, and each planted fault
   fails. The faults are a changed block outside the list, a change from rejected to accepted, an
   acceptance with other coin changes, a revised object with the wrong `active`, a revised object
   that differs with no activation, a block that the baseline rejects, another baseline response,
   and a candidate with another expected verdict.
3. A list that git does not track is refused.
4. The proposal executable, through its snapshot path, on five made blocks: one change of each
   kind of candidate. They are a negative operand of `OP_NOP10`, of `OP_NOP4` and of `OP_CSV`, a
   sequence lock that is one block short, and a lock time at the median time past. The candidate
   scan lists each block. The run check passes with that list, and fails with the empty list.
   With no activation height, case 1 passes.

Every made block is a range request with a `blocks_file` and a `coins_file`, so the scan reads it
through `listing`, the code path of the ranges.
"""

import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import impact_candidates as cands
import impact_run
import replay_blocks
from oracle_block_check import transaction, txin, txout
from oracle_block_validate import Base, Coins, coin_id, file_record, p2sh, push, snapshot_of, snapshot_request, spend

OP_0, OP_1, OP_1NEGATE, OP_NOP10, OP_NOP4, OP_CSV, OP_DROP = 0x00, 0x51, 0x4f, 0xb9, 0xb3, 0xb2, 0x75
VV, FL, RLT = "ExampleVersionVerify", "ExampleFaultyLocktime", "RelativeLockTime"
HEIGHT = 1034382
failures = []


def check(condition: bool, message: str) -> bool:
    print(("ok:   " if condition else "FAIL: ") + message)
    if not condition:
        failures.append(message)
    return condition


def made(directory: Path, name: str, txs: list[bytes], coins: Coins, height: int = HEIGHT,
         version: int | None = None) -> dict:
    """A range request with one block of the transactions on the rule-change block at `height`.

    The request has the form of a range request of scripts/impact_run.py: the block in a
    `blocks_file`, the coins in a `dogelib-coins/1` snapshot as `coins_file`, and the chain view of
    the committed block. So the scan reads it through `listing`, the code path of the ranges."""
    base = Base(height)
    raw = base.block([base.coinbase()] + txs)
    blocks = directory / f"{name}.bin"
    blocks.write_bytes(file_record(height, raw))
    snapshot = directory / f"{name}.coins"
    snapshot.write_bytes(snapshot_of(coins.json()))
    return snapshot_request(base.request([raw], coins), blocks, snapshot)


def candidate_rules(request: dict) -> dict:
    """The rules of the candidate reasons of the block, for each revision, from `listing`."""
    value = cands.listing("made", request)
    return {name: sorted({r["rule"] for c in entry["candidates"] for r in c["reasons"]})
            for name, entry in value["revisions"].items()}


def candidate_cases(directory: Path) -> None:
    def case(name, expected, script_sig=b"", script=bytes([OP_1]), *, coin=True, version=1, lock=0,
             sequence=0xffffffff):
        coins = Coins()
        point = coins.add(coin_id(1), 0, 1000, script) if coin else coin_id(2) + bytes(4)
        if not coin:
            coins.add(coin_id(3), 0, 1000)
        tx = transaction([txin(point, script_sig, sequence)], [txout(1)], version=version, lock=lock)
        got = candidate_rules(made(directory, name.replace(" ", "-").replace(",", ""), [tx], coins))
        want = {VV: [], FL: [], RLT: [], **expected}
        check(got == want, f"candidates: {name}: {got}")

    case("no rule", {})
    case("OP_NOP10 in the scriptSig", {VV: ["opcode 0xb9"]}, script_sig=bytes([OP_1, OP_NOP10]))
    case("0xb9 inside push data", {}, script_sig=push(bytes([OP_NOP10, OP_NOP4, OP_CSV])))
    case("OP_NOP4 in the scriptPubKey", {FL: ["opcode 0xb3"]}, script=bytes([OP_1, OP_NOP4]))
    case("OP_NOP10 after a truncated push", {}, script=bytes([0x05, OP_NOP10]))
    case("OP_NOP10 after a truncated PUSHDATA1", {}, script=bytes([0x4c]))
    case("OP_NOP10 before a truncated push", {VV: ["opcode 0xb9"]}, script=bytes([OP_NOP10, 0x05, 0x01]))
    redeem = bytes([OP_1, OP_CSV, OP_DROP, OP_1])
    case("OP_CSV in a P2SH redeem script", {RLT: ["opcode 0xb2"]}, script_sig=push(b"\x01") + push(redeem),
         script=p2sh(redeem))
    case("a redeem script after a non-push opcode", {}, script_sig=bytes([OP_1, OP_DROP]) + push(redeem),
         script=p2sh(redeem))
    case("a missing coin", {VV: ["missing coin"], FL: ["missing coin"], RLT: ["missing coin"]}, coin=False)
    case("version 2, sequence 0", {RLT: ["sequence"]}, version=2, sequence=0)
    case("version 2, sequence with bit 31 set", {}, version=2, sequence=0x80000000)
    case("version 1, sequence 0", {}, version=1, sequence=0)
    case("version 0xffffffff, sequence 0", {RLT: ["sequence"]}, version=0xffffffff, sequence=0)
    base = Base(HEIGHT)
    median = cands.median_time_past([e["time"] for e in sorted(base.chain, key=lambda e: e["height"])])
    block_time = int.from_bytes(base.header[68:72], "little")
    check(median < block_time, f"the made block's time {block_time} is above the median {median}")
    case("lock time at the median", {RLT: ["cutoff"]}, lock=median, sequence=0)
    case("lock time one below the block time", {RLT: ["cutoff"]}, lock=block_time - 1, sequence=0)
    case("lock time at the block time", {}, lock=block_time, sequence=0)
    case("lock time one below the median", {}, lock=median - 1, sequence=0)
    case("lock time at the median, final sequence", {}, lock=median, sequence=0xffffffff)
    # An output that holds OP_CSV, spent by a later transaction of the same block.
    coins = Coins()
    first = spend([coins.add(coin_id(1), 0, 1000)], [txout(1, bytes([OP_1, OP_CSV]))])
    created = cands.parse_tx(first)["txid"] + bytes(4)
    second = spend([created], [txout(1)])
    result = cands.listing("made", made(directory, "opcode-output", [first, second], coins))
    outputs = result["opcode_outputs"]
    check(len(outputs) == 1 and outputs[0]["spent_at"] == HEIGHT and result["counts"]["opcode_spends"] == 1
          and [c["height"] for c in result["revisions"][RLT]["candidates"]] == [HEIGHT],
          f"candidates: an opcode output that the block spends: {outputs}, {result['counts']['opcode_spends']} spends")


def record(height, valid=True, verdict="accepted", active=True, digest="aa", revised_digest=None, reason=None):
    revised = {"active": active, "verdict": verdict, "step": None if verdict == "accepted" else "ConnectBlock",
               "reject_reason": reason, "tx": None, "input": None, "script_error": None, "mandatory": None,
               "reason": None, "changes_digest_hex": (digest if revised_digest is None else revised_digest)
               if verdict == "accepted" else None}
    return {"height": height, "hash_display": f"{height:064x}", "valid": valid, "reject_reason": None,
            "changes_digest_hex": digest, "revised": revised}


def response(records):
    return {"id": "x", "ok": {"blocks": records, "set_digest_hex": "dd", "set_coins": 1}}


def run_checks() -> None:
    active = {"name": VV, "variant": None, "activation_height": 0}
    inactive = {**active, "activation_height": None}
    listed = {"candidates": [{"height": 2, "hash": "", "reasons": []}]}
    empty = {"candidates": []}
    request = {}

    def outcome(answer, revision, candidates, baseline=None):
        try:
            impact_run.check_response(answer, request, revision, candidates, baseline)
            return None
        except impact_run.ImpactError as error:
            return str(error)

    good = response([record(1), record(2, verdict="rejected", reason="x")])
    check(outcome(good, active, listed) is None, "run check: a change of a candidate passes")
    check(outcome(good, active, empty) is not None, "run check: a changed block outside the list fails")
    relaxed = response([record(1), record(2, valid=False, verdict="accepted")])
    check(outcome(relaxed, active, listed) is not None, "run check: a change from rejected to accepted fails")
    other = response([record(1, revised_digest="bb")])
    check(outcome(other, active, empty) is not None, "run check: an acceptance with other coin changes fails")
    check(outcome(response([record(1, active=False)]), active, empty) is not None,
          "run check: a revised object with the wrong active fails")
    plain = response([record(1, active=False), record(2, active=False)])
    check(outcome(plain, inactive, empty) is None, "run check: case 1 passes when each revised object agrees")
    differs = response([record(1, active=False), record(2, active=False, verdict="rejected", reason="x")])
    check(outcome(differs, inactive, listed) is not None, "run check: case 1 fails on a revised object that differs")
    check(outcome(response([record(1, valid=False, verdict="rejected", active=False)]), inactive, empty) is not None,
          "run check: a block that the baseline rejects fails")
    baseline = {"ok": {**good["ok"], "blocks": [{k: v for k, v in r.items() if k != "revised"} for r in good["ok"]["blocks"]]}}
    check(outcome(good, active, listed, baseline) is None, "run check: the recorded baseline response passes")
    changed_baseline = json.loads(json.dumps(baseline))
    changed_baseline["ok"]["set_digest_hex"] = "ee"
    check(outcome(good, active, listed, changed_baseline) is not None, "run check: another baseline response fails")
    expected = {"candidates": [{"height": 2, "hash": "", "reasons": [], "expected": {"verdict": "accepted"}}]}
    check(outcome(good, active, expected) is not None, "run check: a candidate with another expected verdict fails")


def tracked_check(directory: Path) -> None:
    stray = ROOT / "build" / "test-impact-untracked.json"
    stray.parent.mkdir(exist_ok=True)
    stray.write_text("{}\n")
    try:
        impact_run.committed(stray)
        check(False, "a list that git does not track is refused")
    except impact_run.ImpactError:
        check(True, "a list that git does not track is refused")
    finally:
        stray.unlink()


def proposal_run(directory: Path, proposal: str) -> None:
    """Each kind of candidate in a made block that the revision rejects, through the snapshot path of the proposal executable.

    Each expected change is stated by hand from the rule. `OP_1NEGATE OP_NOP10 OP_1` and
    `OP_1NEGATE OP_NOP4 OP_1` give the negative operand of each example. `OP_1NEGATE OP_CSV OP_1`
    gives the negative operand of BIP 112. A version-2 spend with the sequence 2 of a coin at the
    height below the block is one block short of its lock (BIP 68). A lock time at the median time
    past, with an input that is not final, is final at the baseline cutoff, the block time, and not
    final at the revised cutoff, the median (BIP 113)."""
    base = Base(HEIGHT)
    median = cands.median_time_past([e["time"] for e in sorted(base.chain, key=lambda e: e["height"])])

    def planted(name, revision, script=bytes([OP_1]), *, version=1, lock=0, sequence=0xffffffff, coin_height=100000):
        coins = Coins()
        point = coins.add(coin_id(1), 0, 1000, script, height=coin_height)
        tx = transaction([txin(point, b"", sequence)], [txout(1)], version=version, lock=lock)
        return name, revision, made(directory, name, [tx], coins)

    cases = [planted("nop10", VV, bytes([OP_1NEGATE, OP_NOP10, OP_1])),
             planted("nop4", FL, bytes([OP_1NEGATE, OP_NOP4, OP_1])),
             planted("csv", RLT, bytes([OP_1NEGATE, OP_CSV, OP_1])),
             planted("sequence", RLT, version=2, sequence=2, coin_height=HEIGHT - 1),
             planted("cutoff", RLT, lock=median, sequence=0)]
    variants = {VV: None, FL: "corrected", RLT: None}
    for name, revision_name, request in cases:
        listing = cands.listing(name, request)["revisions"][revision_name]["candidates"]
        check([c["height"] for c in listing] == [HEIGHT], f"proposal run {name}: the scan lists the made block")
        for activation, candidates, passes, what in ((0, listing, True, "a listed change"),
                                                     (0, [], False, "the same change without the list fails"),
                                                     (None, [], True, "case 1 with no activation height")):
            revision = {"name": revision_name, "variant": variants[revision_name], "activation_height": activation}
            answer, _ = replay_blocks.run(proposal, {**request, "id": "made", "revision": revision},
                                          directory / "response.json", 600)
            try:
                report = impact_run.check_response(answer, request, revision, {"candidates": candidates}, None)
                check(passes and report["changed_blocks"] == (1 if activation is not None else 0),
                      f"proposal run {name}: {what}: {report['changed']}")
            except impact_run.ImpactError as error:
                check(not passes, f"proposal run {name}: {what} ({error})")


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.split("\n\n")[1])
        return 2
    with tempfile.TemporaryDirectory() as name:
        directory = Path(name)
        candidate_cases(directory)
        run_checks()
        tracked_check(directory)
        proposal_run(directory, sys.argv[1])
    if failures:
        print(f"{len(failures)} failure(s)")
        return 1
    print("impact tools: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
