"""Test of `dogelib-proposal-oracle`, the proposal executable of design record 0011, section 10.2.

Usage: python3 -I scripts/test_proposal_oracle.py [--mainnet-blocks DIR] [--snapshot-request FILE] [--timeout SECONDS]
           <dogelib-oracle> <dogelib-proposal-oracle>

It needs no Dogecoin Core. The checks:

1. Baseline. Without the argument `revision`, the proposal executable writes the bytes that
   `dogelib-oracle` writes, on every `block.validate` request of the full comparison
   (`block_validate_sets` of scripts/oracle_block_validate.py), and on the same requests with
   `blocks_file` (stage 6, exit condition 2), and on the requests with one record for each block
   with their coins in a `coins_file`. A request with a revision gives the same `revised` objects
   with `coins_file` as with `coins`. With --snapshot-request it adds one range request with
   `coins_file`, such as the short range of scripts/impact_run.py, heights 9,001 to 10,000 from the
   snapshot at 9,000. With --mainnet-blocks it adds the replay of mainnet
   from the genesis block to height 10,000, which takes each program several minutes.
2. `dogelib-oracle` refuses the argument `revision` with a request error.
3. Request errors of the argument: each malformed `revision` gives a request error.
4. No activation height. For each named revision, each response is the baseline response with a
   `revised` object in each block record. Each `revised` object has `active` false and the verdict
   and the reject reason of the baseline record, as `validateBlockWith_inactive` states.
5. Active from height 0, on the same requests. Each response is again the baseline response with
   `revised` objects, so the revision changes no state. For the two soft forks, no block goes from
   rejected to accepted. This check is a property test on the comparison requests. It is not the
   range run of section 10.3, case 2.
   The request whose five blocks fail the five checks in Core's order gives the step and the
   transaction of each rejection, with and without an activation height.
6. Made blocks. Each block stands on a committed rule-change block, with a synthetic coin whose
   script holds the rule, as section 10.3, case 3, describes. Each expected `revised` object is
   written here by hand from the text of the rule in the module documentation of the example and
   from the flags of the height. No program supplies one.
   Three more blocks are for the sequence locks of `RelativeLockTime` (BIP 68): a lock that is met,
   a lock that is one block short, and a time lock on a coin above the block, which is outside the
   model of the revision.

7. `block.contextual_check_body`. Without `revision`, the proposal executable writes the bytes of
   `dogelib-oracle` on the requests of the comparison (`contextual_body_sets` of
   scripts/oracle_contextual_body.py). With a revision and no activation height, each response is
   the baseline response with a `revised` object that has `active` false and the baseline verdict.
   The examples change no lock-time argument, so the same holds for them with activation height 0.
   scripts/compare_csv_forced.py checks the `revised` objects of `RelativeLockTime` against Core's
   own code, which this script does not run.

The script signs nothing and uses no private key.
"""

import argparse
import json
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_block_check import transaction, txin, txout
from oracle_contextual_body import contextual_body_sets
from oracle_block_validate import (EVAL_FALSE, Base, Coins, block_validate_sets, coin_id, file_twins,
                                   mainnet_validate_sets, script_reason, snapshot_twins, spend)

# The number of `block.validate` requests of the full comparison (EXPECTED_COUNTS of scripts/compare_core.py).
FULL_COMPARISON_REQUESTS = 42

REVISIONS = [("ExampleFaultyLocktime", "corrected"), ("ExampleFaultyLocktime", "faulty"),
             ("ExampleVersionVerify", None), ("RelativeLockTime", None)]
# The revisions with a restriction theorem (`corrected_block_restricts`, `example_block_restricts` and
# `relativeLockTime_restricts`).
SOFT_FORKS = [("ExampleFaultyLocktime", "corrected"), ("ExampleVersionVerify", None), ("RelativeLockTime", None)]

OP_1NEGATE, OP_1, OP_2, OP_EQUAL, OP_NOP4, OP_NOP10 = 0x4f, 0x51, 0x52, 0x87, 0xb3, 0xb9
NEGATIVE_LOCKTIME = "Negative locktime"
NEGATIVE_OPERAND = "ExampleVersionVerify: negative operand"
VERSION_TOO_LOW = "ExampleVersionVerify: version too low"

failures = []


def check(condition: bool, message: str) -> bool:
    if not condition:
        failures.append(message)
        print(f"FAIL: {message}")
    return condition


def run(program: str, requests: list[dict], timeout: float) -> bytes:
    """The bytes that `program` writes for `requests`, one line for each request."""
    data = "".join(json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n" for r in requests).encode()
    result = subprocess.run([program], input=data, capture_output=True, timeout=timeout)
    if result.returncode != 0:
        raise SystemExit(f"{program} exited with status {result.returncode}: {result.stderr[-500:]!r}")
    return result.stdout


def responses(program: str, requests: list[dict], timeout: float) -> list[dict]:
    lines = run(program, requests, timeout).splitlines()
    if len(lines) != len(requests):
        raise SystemExit(f"{program}: {len(lines)} responses to {len(requests)} requests")
    return [json.loads(line) for line in lines]


def numbered(requests: list[dict], prefix: str) -> list[dict]:
    return [{**r, "id": f"{prefix}-{i}"} for i, r in enumerate(requests)]


def revision(name: str, variant: str | None, height: int | None) -> dict:
    return {"name": name, "variant": variant, "activation_height": height}


def label(name: str, variant: str | None) -> str:
    return name if variant is None else f"{name} ({variant})"


def without_revised(response: dict) -> dict:
    """The response without the `revised` object of each block record."""
    ok = response.get("ok")
    if not isinstance(ok, dict):
        return response
    return {**response, "ok": {**ok, "blocks": [{k: v for k, v in b.items() if k != "revised"} for b in ok["blocks"]]}}


def block_records(response: dict) -> list[dict]:
    ok = response.get("ok")
    return ok["blocks"] if isinstance(ok, dict) else []


def revised_fields(active: bool, verdict: str, reason: str | None = None, tx: int | None = None,
                   input_: int | None = None, script_error: str | None = None, mandatory: bool | None = None) -> dict:
    """The fields of a `revised` object that the made blocks fix, for a result of `ConnectBlock` or an acceptance."""
    return {"active": active, "verdict": verdict, "step": None if verdict == "accepted" else "ConnectBlock",
            "reject_reason": reason, "tx": tx, "input": input_, "script_error": script_error,
            "mandatory": mandatory, "reason": None}


def script_failure(text: str) -> dict:
    """A script failure of input 0 of the transaction at 1, which fails both script runs."""
    return revised_fields(True, "rejected", script_reason(True, text), 1, 0, text, True)


def made_blocks() -> list[tuple[str, dict, tuple, dict, bool]]:
    """Made blocks: a name, the request without `revision`, the revision, the expected `revised` fields, and the baseline verdict.

    Each request has one block with a coinbase and one transaction, which spends a supplied coin with
    an empty `scriptSig`. The scripts are in the comments. Each expectation follows from the rule of
    the example with `active` true, and from the baseline rule that the two opcodes are NOPs.
    """
    cases = []

    def case(name, height, script, rev, expected, baseline_valid, lock=0, sequence=0xffffffff):
        base, coins = Base(height), Coins()
        point = coins.add(coin_id(1), 0, 1000, bytes(script))
        tx = spend([point], [txout(1)], lock=lock, sequence=sequence)
        cases.append((name, base.request([base.block([base.coinbase(), tx])], coins), rev, expected, baseline_valid))

    version_verify = ("ExampleVersionVerify", None)
    corrected, faulty = ("ExampleFaultyLocktime", "corrected"), ("ExampleFaultyLocktime", "faulty")
    # OP_1NEGATE OP_NOP10 OP_1. Baseline: OP_NOP10 is a NOP, and the top item is true. Revision: the
    # operand -1 is negative, which is the error `negativeOperand`. The second run has the same
    # `active`, so it fails too, and the failure is mandatory. At 1,034,382 the flags are P2SH alone,
    # so there is no second run, and the failure is mandatory as well.
    for height in (1034382, 3464751):
        case(f"version-verify negative operand at {height}", height, [OP_1NEGATE, OP_NOP10, OP_1], version_verify,
             script_failure(NEGATIVE_OPERAND), True)
    # OP_2 OP_NOP10. The made transaction has version 1, which is below the operand 2: `versionTooLow`.
    case("version-verify version too low", 1034382, [OP_2, OP_NOP10], version_verify,
         script_failure(VERSION_TOO_LOW), True)
    # OP_1 OP_NOP10. The version 1 is at least the operand 1, so the rule runs and passes.
    case("version-verify satisfied", 1034382, [OP_1, OP_NOP10], version_verify, revised_fields(True, "accepted"), True)
    # OP_1NEGATE OP_NOP4 OP_1. Baseline accepts. Both variants run the lock-time check, whose operand
    # is negative: NEGATIVE_LOCKTIME.
    for rev in (corrected, faulty):
        case(f"locktime negative operand, {rev[1]}", 1034382, [OP_1NEGATE, OP_NOP4, OP_1], rev,
             script_failure(NEGATIVE_LOCKTIME), True)
    # OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL, the counterexample of the faulty variant. The transaction has
    # the lock time 2 and a sequence that is not final, so the lock-time check of the operand 2
    # passes. Baseline and corrected variant: the stack ends 1, 2 = 1, which is false: EVAL_FALSE.
    # Faulty variant: the check pops the operand, the stack ends 1 = 1, and the spend is accepted.
    counterexample = [OP_1, OP_2, OP_NOP4, OP_1, OP_EQUAL]
    case("locktime counterexample, corrected", 1034382, counterexample, corrected, script_failure(EVAL_FALSE), False,
         lock=2, sequence=0)
    case("locktime counterexample, faulty", 1034382, counterexample, faulty, revised_fields(True, "accepted"), False,
         lock=2, sequence=0)

    # The sequence locks of `RelativeLockTime` (BIP 68). The spending transaction has version 2 and
    # one input, and the coin has the script OP_1. The baseline has no sequence lock, so it accepts
    # each block. The block is at height 1,034,382.
    def lock_case(name, coin_height, sequence, expected):
        base, coins = Base(1034382), Coins()
        point = coins.add(coin_id(1), 0, 1000, bytes([OP_1]), height=coin_height)
        tx = transaction([txin(point, b"", sequence)], [txout(1)], version=2)
        cases.append((name, base.request([base.block([base.coinbase(), tx])], coins), ("RelativeLockTime", None),
                      expected, True))

    # Sequence 1: a height lock of one block on the coin of the predecessor. 1,034,381 + 1 is the
    # height of the block, so the lock is met.
    lock_case("sequence lock met", 1034381, 1, revised_fields(True, "accepted"))
    # Sequence 2: the lock is one block short. Core's reason is bad-txns-nonfinal of ConnectBlock,
    # with the score 100 and the code REJECT_INVALID, for the transaction at 1.
    lock_case("sequence lock one block short", 1034381, 2,
              {**revised_fields(True, "rejected", "bad-txns-nonfinal", 1), "dos": 100, "reject_code": 0x10})
    # Sequence 0x00400000: a time lock of 0 units on a coin above the block. The revision gives no
    # verdict (`coinAboveBlock`), and the result is not a rejection.
    lock_case("sequence lock on a coin above the block", 1034383, 0x00400000,
              {**revised_fields(True, "unsupported"), "reason": "RelativeLockTime: coinAboveBlock"})
    return cases


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--mainnet-blocks", metavar="DIR",
                        help="also compare the replay of mainnet to height 10,000 from the fixtures under DIR")
    parser.add_argument("--snapshot-request", metavar="FILE",
                        help="also compare one range request with coins_file, such as the short range")
    parser.add_argument("--timeout", type=float, default=3600.0)
    parser.add_argument("oracle")
    parser.add_argument("proposal_oracle")
    args = parser.parse_args()
    oracle, proposal, timeout = args.oracle, args.proposal_oracle, args.timeout

    version = json.loads(subprocess.run([proposal, "--version"], capture_output=True, check=True).stdout)
    baseline_version = json.loads(subprocess.run([oracle, "--version"], capture_output=True, check=True).stdout)
    check(version == {**baseline_version, "program": "dogelib-proposal-oracle"},
          f"--version: {version} is not the oracle's format with the program name")

    # 1. Baseline: byte equality on the requests of the full comparison.
    requests = numbered([r for _, group in block_validate_sets() for r in group], "validate")
    check(len(requests) == FULL_COMPARISON_REQUESTS,
          f"{len(requests)} block.validate requests, expected {FULL_COMPARISON_REQUESTS}")
    ours = run(oracle, requests, timeout)
    theirs = run(proposal, requests, timeout)
    if check(ours == theirs, "the two programs differ on a block.validate request of the full comparison"):
        print(f"ok:   {len(requests)} block.validate requests of the full comparison: the same bytes")
    baseline = [json.loads(line) for line in ours.splitlines()]
    with tempfile.TemporaryDirectory() as directory:
        twins = numbered([req for req, _ in file_twins(requests, baseline, directory)], "file")
        if check(run(oracle, twins, timeout) == run(proposal, twins, timeout),
                 "the two programs differ on a blocks_file request"):
            print(f"ok:   {len(twins)} blocks_file requests: the same bytes")
        # The hook also runs on the file path: one made request with a revision, in both forms.
        name, req, rev, expected, _ = made_blocks()[0]
        hex_request = {**req, "id": "made-file", "revision": revision(*rev, 0)}
        hex_response = responses(proposal, [hex_request], timeout)[0]
        file_request = file_twins([req], [without_revised(hex_response)], directory)[0][0]
        file_response = responses(proposal, [{**file_request, "id": "made-file", "revision": revision(*rev, 0)}], timeout)[0]
        if check(file_response == hex_response and block_records(hex_response)[0].get("revised") is not None,
                 "blocks_file and blocks_hex differ on a request with a revision"):
            print("ok:   a request with a revision has one response for blocks_file and blocks_hex")
        # The snapshot path: the requests with their coins in a `coins_file` (design record 0011, section 3.3).
        snapshots = numbered([req for req, _ in snapshot_twins(requests, baseline, directory)], "snapshot")
        if check(snapshots and run(oracle, snapshots, timeout) == run(proposal, snapshots, timeout),
                 "the two programs differ on a coins_file request"):
            print(f"ok:   {len(snapshots)} coins_file requests: the same bytes")
        twin = snapshot_twins([req], [without_revised(hex_response)], directory)[0][0]
        snap_response = responses(proposal, [{**twin, "id": "made-file", "revision": revision(*rev, 0)}], timeout)[0]
        if check([b.get("revised") for b in block_records(snap_response)] ==
                 [b.get("revised") for b in block_records(hex_response)],
                 "coins_file and coins give other revised objects on a request with a revision"):
            print("ok:   a request with a revision has the same revised objects with coins_file and with coins")
    if args.snapshot_request:
        # A range request with `coins_file`, such as the short range of scripts/impact_run.py.
        ranged = json.loads(pathlib.Path(args.snapshot_request).read_text())
        ranged = {**{k: v for k, v in ranged.items() if k != "expected_end"}, "id": "snapshot-range"}
        if check("coins_file" in ranged and run(oracle, [ranged], timeout) == run(proposal, [ranged], timeout),
                 f"the two programs differ on the coins_file request {args.snapshot_request}"):
            print(f"ok:   the coins_file range request {args.snapshot_request}: the same bytes")
    if args.mainnet_blocks:
        replay = numbered([r for _, group in mainnet_validate_sets(args.mainnet_blocks) for r in group], "mainnet")
        if check(run(oracle, replay, timeout) == run(proposal, replay, timeout),
                 "the two programs differ on the mainnet replay"):
            print(f"ok:   {len(replay)} mainnet replay request(s): the same bytes")

    # 2. The oracle refuses the argument.
    sample = requests[0]
    refused = responses(oracle, [{**sample, "revision": revision("ExampleVersionVerify", None, 0)}], timeout)[0]
    if check(refused.get("error", {}).get("kind") == "request" and "revision" in refused["error"].get("message", ""),
             f"dogelib-oracle did not refuse the argument revision: {json.dumps(refused)[:200]}"):
        print("ok:   dogelib-oracle refuses the argument revision with a request error")

    # 3. Request errors of the argument.
    malformed = [None, "ExampleVersionVerify", [], {},
                 {"name": "ExampleVersionVerify", "variant": None},
                 {"name": "ExampleVersionVerify", "activation_height": 0},
                 {"variant": None, "activation_height": 0},
                 {"name": "ExampleVersionVerify", "variant": None, "activation_height": 0, "extra": 1},
                 revision("Unknown", None, 0), revision("ExampleVersionVerify", "corrected", 0),
                 revision("ExampleFaultyLocktime", None, 0), revision("ExampleFaultyLocktime", "other", 0),
                 revision("ExampleVersionVerify", None, -1), revision("ExampleVersionVerify", None, 0.5),
                 revision("ExampleVersionVerify", None, "0"), revision("ExampleVersionVerify", None, 2147483647),
                 revision(1, None, 0), revision("ExampleVersionVerify", 1, 0)]
    answers = responses(proposal, [{**sample, "id": f"malformed-{i}", "revision": m} for i, m in enumerate(malformed)], timeout)
    bad = [m for m, a in zip(malformed, answers) if a.get("error", {}).get("kind") != "request"]
    if check(not bad, f"no request error for the revision arguments {bad}"):
        print(f"ok:   {len(malformed)} malformed revision arguments give request errors")

    # 4 and 5. Each revision on the requests of the comparison, without an activation height and from height 0.
    for name, variant in REVISIONS:
        for height in (None, 0):
            where = f"{label(name, variant)}, activation_height {json.dumps(height)}"
            revised = responses(proposal, [{**r, "revision": revision(name, variant, height)} for r in requests], timeout)
            same_state = all(without_revised(a) == b for a, b in zip(revised, baseline))
            check(same_state, f"{where}: a response differs from the baseline apart from the revised objects")
            records = [(new, old) for a, b in zip(revised, baseline)
                       for new, old in zip(block_records(a), block_records(b))]
            complete = all(isinstance(new.get("revised"), dict) for new, _ in records)
            check(complete and records, f"{where}: a block record has no revised object")
            if not (same_state and complete):
                continue
            changed = [(new, old) for new, old in records
                       if (new["revised"]["verdict"] == "accepted") != old["valid"]]
            if height is None:
                equal = all(new["revised"]["active"] is False
                            and new["revised"]["verdict"] == ("accepted" if old["valid"] else "rejected")
                            and new["revised"]["reject_reason"] == old["reject_reason"]
                            and new["revised"]["changes_digest_hex"] == old["changes_digest_hex"]
                            for new, old in records)
                if check(equal, f"{where}: a revised object differs from the baseline record"):
                    print(f"ok:   {where}: {len(records)} block records, each revised object agrees with the baseline")
            else:
                active = all(new["revised"]["active"] is True for new, _ in records)
                check(active, f"{where}: a revised object is not active")
                relaxed = [new["height"] for new, old in changed if not old["valid"]]
                if (name, variant) in SOFT_FORKS:
                    check(not relaxed, f"{where}: blocks at {relaxed} go from rejected to accepted")
                if active and not ((name, variant) in SOFT_FORKS and relaxed):
                    print(f"ok:   {where}: {len(records)} block records, {len(changed)} changed, "
                          f"{len(relaxed)} from rejected to accepted")

    # The step and the transaction of a rejection, on the request of the comparison whose five blocks
    # fail the checks in Core's order (`order_cases`). The expectations follow the comments of that
    # request: the second CheckBlock failure and the ConnectBlock failure are in the transaction at 1.
    order_reasons = ["bad-diffbits", "bad-txnmrklroot", "bad-txns-inputs-duplicate", "bad-txns-nonfinal",
                     "bad-txns-inputs-missingorspent"]
    order_steps = [("ContextualCheckBlockHeader", None), ("CheckBlock", None), ("CheckBlock", 1),
                   ("ContextualCheckBlock", None), ("ConnectBlock", 1)]
    order = [r for r, b in zip(requests, baseline) if [x["reject_reason"] for x in block_records(b)] == order_reasons]
    if check(len(order) == 1, f"{len(order)} requests with the reject reasons of the order case"):
        for height in (None, 0):
            answer = responses(proposal, [{**order[0], "revision": revision("ExampleVersionVerify", None, height)}], timeout)[0]
            got = [(b["revised"]["step"], b["revised"]["tx"]) for b in block_records(answer)]
            reasons = [b["revised"]["reject_reason"] for b in block_records(answer)]
            if check(got == order_steps and reasons == order_reasons,
                     f"order case, activation_height {json.dumps(height)}: steps {got}, reasons {reasons}"):
                print(f"ok:   order case, activation_height {json.dumps(height)}: the step and the transaction of each rejection")

    # 6. Made blocks.
    for name, req, rev, expected, baseline_valid in made_blocks():
        for height, inactive in ((0, False), (None, True)):
            answer = responses(proposal, [{**req, "id": name, "revision": revision(*rev, height)}], timeout)[0]
            records = block_records(answer)
            if not check(len(records) == 1 and isinstance(records[0].get("revised"), dict),
                         f"made block {name}: no block record with a revised object: {json.dumps(answer)[:300]}"):
                continue
            record, got = records[0], records[0]["revised"]
            check(record["valid"] == baseline_valid, f"made block {name}: the baseline verdict is {record['valid']}")
            if inactive:
                want_verdict = "accepted" if baseline_valid else "rejected"
                check(got["active"] is False and got["verdict"] == want_verdict
                      and got["reject_reason"] == record["reject_reason"],
                      f"made block {name}, no activation: {json.dumps(got)}")
                continue
            fixed = {k: got.get(k) for k in expected}
            ok = check(fixed == expected, f"made block {name}: revised is {json.dumps(fixed)}, expected {json.dumps(expected)}")
            digest = got["changes_digest_hex"]
            if expected["verdict"] == "accepted" and baseline_valid:
                ok = check(digest == record["changes_digest_hex"], f"made block {name}: the changes differ") and ok
            else:
                ok = check((digest is None) == (expected["verdict"] != "accepted"),
                           f"made block {name}: changes_digest_hex is {digest}") and ok
            if ok:
                direction = "outside the model" if expected["verdict"] == "unsupported" else (
                    "unchanged" if (expected["verdict"] == "accepted") == baseline_valid else (
                        "accepted to rejected" if baseline_valid else "rejected to accepted"))
                print(f"ok:   made block {name}: {direction}")

    # 7. `block.contextual_check_body`.
    body = numbered([dict(r) for _, rs in contextual_body_sets() for r in rs], "body")
    body_baseline = run(oracle, body, timeout)
    if check(run(proposal, body, timeout) == body_baseline,
             f"block.contextual_check_body: the proposal executable differs from dogelib-oracle on {len(body)} requests"):
        print(f"ok:   {len(body)} block.contextual_check_body requests: the same bytes")
    plain = [json.loads(line) for line in body_baseline.splitlines()]
    refused = responses(oracle, [{**body[0], "revision": revision("RelativeLockTime", None, None)}], timeout)[0]
    check(refused.get("error", {}).get("kind") == "request",
          f"dogelib-oracle accepts revision on block.contextual_check_body: {json.dumps(refused)[:300]}")
    for name, variant in REVISIONS:
        heights = (None,) if name == "RelativeLockTime" else (None, 0)
        for height in heights:
            where = f"block.contextual_check_body, {label(name, variant)}, activation_height {json.dumps(height)}"
            answers = responses(proposal, [{**r, "revision": revision(name, variant, height)} for r in body], timeout)
            good = True
            for old, new in zip(plain, answers):
                if "ok" not in old:
                    good = check(new == old, f"{where}: an error response differs: {json.dumps(new)[:300]}") and good
                    continue
                revised = new.get("ok", {}).get("revised")
                rest = {k: v for k, v in new.get("ok", {}).items() if k != "revised"}
                want = "accepted" if old["ok"]["valid"] else "rejected"
                same = (isinstance(revised, dict) and rest == old["ok"] and revised["verdict"] == want
                        and revised["reject_reason"] == old["ok"]["reject_reason"] and revised["dos"] == old["ok"]["dos"]
                        and revised["reject_code"] == old["ok"]["reject_code"] and revised["reason"] is None
                        and (height is None) == (revised["active"] is False))
                good = check(same, f"{where}: {json.dumps(new)[:400]}") and good
            if good:
                print(f"ok:   {where}: {len(answers)} responses, each revised object agrees with the baseline")

    if failures:
        print(f"{len(failures)} failure(s)")
        return 1
    print("proposal oracle: all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
