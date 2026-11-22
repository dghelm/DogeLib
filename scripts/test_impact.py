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
4. The proposal executable on a made block whose coin holds `OP_1NEGATE OP_NOP10 OP_1`, the
   negative operand of `ExampleVersionVerify`. The candidate scan lists the block. The run check
   passes with that list, and fails with the empty list. With no activation height, case 1 passes.
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
from oracle_block_validate import Base, Coins, coin_id, file_record, p2sh, push, spend

OP_0, OP_1, OP_1NEGATE, OP_NOP10, OP_NOP4, OP_CSV, OP_DROP = 0x00, 0x51, 0x4f, 0xb9, 0xb3, 0xb2, 0x75
VV, FL, RLT = "ExampleVersionVerify", "ExampleFaultyLocktime", "RelativeLockTime"
HEIGHT = 1034382
failures = []


def check(condition: bool, message: str) -> bool:
    print(("ok:   " if condition else "FAIL: ") + message)
    if not condition:
        failures.append(message)
    return condition


def made(directory: Path, name: str, txs: list[bytes], coins: Coins, height: int = HEIGHT) -> tuple[dict, dict]:
    """A request with one block of the transactions on the rule-change block at `height`, and its coin map."""
    base = Base(height)
    raw = base.block([base.coinbase()] + txs)
    blocks = directory / f"{name}.bin"
    blocks.write_bytes(file_record(height, raw))
    request = {k: v for k, v in base.request([raw], coins).items() if k != "blocks_hex"}
    request["blocks_file"] = str(blocks)
    coin_map = {bytes.fromhex(e["txid_hex"]) + o["n"].to_bytes(4, "little"): bytes.fromhex(o["script_hex"])
                for e in request["coins"] for o in e["outputs"]}
    return request, coin_map


def candidate_rules(request: dict, coin_map: dict) -> dict:
    """The rules of the candidate reasons of the block, for each revision."""
    result = cands.scan(request, coin_map)
    return {name: sorted({r["rule"] for c in found for r in c["reasons"]}) for name, found in result["candidates"].items()}


def candidate_cases(directory: Path) -> None:
    def case(name, expected, script_sig=b"", script=bytes([OP_1]), *, coin=True, version=1, lock=0,
             sequence=0xffffffff, extra=None):
        coins = Coins()
        point = coins.add(coin_id(1), 0, 1000, script) if coin else coin_id(2) + bytes(4)
        tx = transaction([txin(point, script_sig, sequence)], [txout(1)], version=version, lock=lock)
        request, coin_map = made(directory, name.replace(" ", "-"), [tx] + (extra or []), coins)
        got = candidate_rules(request, coin_map)
        want = {VV: [], FL: [], RLT: [], **expected}
        check(got == want, f"candidates: {name}: {got}")
        return request, coin_map

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
    request, coin_map = made(directory, "opcode-output", [first, second], coins)
    result = cands.scan(request, coin_map)
    outputs = result["opcode_outputs"]
    check(len(outputs) == 1 and outputs[0]["spent_at"] == HEIGHT and result["counts"]["opcode_spends"] == 1
          and [c["height"] for c in result["candidates"][RLT]] == [HEIGHT],
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
    coins = Coins()
    point = coins.add(coin_id(1), 0, 1000, bytes([OP_1NEGATE, OP_NOP10, OP_1]))
    request, coin_map = made(directory, "negative-operand", [spend([point], [txout(1)])], coins)
    listing = cands.scan(request, coin_map)["candidates"][VV]
    check([c["height"] for c in listing] == [HEIGHT], f"proposal run: the scan lists the made block: {listing}")
    for activation, candidates, passes, what in ((0, listing, True, "the made block is a listed change"),
                                                 (0, [], False, "the same change without the list fails"),
                                                 (None, [], True, "case 1 with no activation height")):
        revision = {"name": VV, "variant": None, "activation_height": activation}
        answer, _ = replay_blocks.run(proposal, {**request, "id": "made", "revision": revision},
                                      directory / "response.json", 600)
        try:
            report = impact_run.check_response(answer, request, revision, {"candidates": candidates}, None)
            check(passes and report["changed_blocks"] == (1 if activation is not None else 0), f"proposal run: {what}")
        except impact_run.ImpactError as error:
            check(not passes, f"proposal run: {what} ({error})")


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
