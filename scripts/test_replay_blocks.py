#!/usr/bin/env python3
"""Tests of scripts/replay_blocks.py and of `block.validate` with `blocks_file` in both programs.

Usage: python3 -I scripts/test_replay_blocks.py <dogelib-oracle> <core-oracle> [BLOCKS_DIR]

BLOCKS_DIR is the directory that scripts/fetch_release_blocks.py writes, `build/mainnet-blocks`
by default. The tests use its range of heights 0 to 10,000 and its recent range.

1. The replay of heights 0 to 200 passes, and its summary has those heights. The issuance check
   of the replay fails on a total value one koinu above the sum of the subsidies, on a subsidy
   that differs between the two programs, and on a request that does not start at the genesis
   block.
2. The replay fails with the oracle in the place of the harness, and with the harness in the
   place of the oracle.
3. The replay fails for a fixture that does not start at height 0, for a fixture with one changed
   byte, and for a `--last` above the fixture.
4. Each request of the comparison sets of `block.validate` that has one record for each block runs
   again with its blocks in a file. The oracle must give the result of the request with
   `blocks_hex`, and the two programs must agree as in scripts/compare_core.py. These requests
   hold rejected blocks.
5. Both programs give the expected error for each faulty file and each faulty argument.
"""

import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import oracle_block_validate as validate  # noqa: E402
import replay_blocks  # noqa: E402

LAST = 200


def answers(program: str, requests: list[dict]) -> list[dict]:
    data = "".join(json.dumps({**req, "id": i}, sort_keys=True) + "\n" for i, req in enumerate(requests))
    done = subprocess.run([program], input=data, capture_output=True, text=True, timeout=600)
    lines = done.stdout.splitlines()
    if done.returncode != 0 or len(lines) != len(requests):
        raise RuntimeError(f"{program}: status {done.returncode}, {len(lines)} responses to {len(requests)} requests")
    return [json.loads(line) for line in lines]


def error_matches(response: dict, want: dict) -> bool:
    error = response.get("error")
    if set(response) != {"id", "error"} or not isinstance(error, dict):
        return False
    if want == {"kind": "request"}:
        return error.get("kind") == "request" and set(error) == {"kind", "message"}
    return error == want


def issuance_faults(check, oracle: str, harness: str, response: dict) -> None:
    """The issuance check fails on each planted fault of a passing replay's response."""
    request = {"op": "block.validate", "chain": [], "coins": []}
    ok = response["ok"]
    sent = validate.issuance_requests(request, ok)
    ours, core = answers(oracle, sent), answers(harness, sent)
    failure, summary = validate.issuance_bound(request, ok, sent, ours, core)
    check("issuance control", failure is None, str(failure))
    if failure is not None:
        return
    # The final total one koinu above the bound.
    above = {**ok, "set_value": str(int(summary["subsidy_sum"]) + 1)}
    failure, _ = validate.issuance_bound(request, above, sent, ours, core)
    check("issuance above the bound", failure is not None and "exceeds" in failure[1], str(failure))
    # A total of a block record above the bound: the bound at height 0 is 0.
    first = {**ok, "blocks": [{**ok["blocks"][0], "set_value": "1"}] + ok["blocks"][1:]}
    failure, _ = validate.issuance_bound(request, first, sent, ours, core)
    check("issuance above the bound at height 0", failure is not None and "after height 0" in failure[1], str(failure))
    # One subsidy differs between the two programs.
    changed = json.loads(json.dumps(core))
    changed[0]["ok"]["subsidies"][0] = str(int(changed[0]["ok"]["subsidies"][0]) + 1)
    failure, _ = validate.issuance_bound(request, ok, sent, ours, changed)
    check("issuance subsidy disagreement", failure is not None and "different subsidies" in failure[1], str(failure))
    # A range that does not start at the genesis block.
    later = {**ok, "blocks": ok["blocks"][1:]}
    failure, _ = validate.issuance_bound(request, later, sent, ours, core)
    check("issuance without the genesis block", failure is not None and "genesis" in failure[1], str(failure))
    check("issuance requests need the empty start", validate.issuance_requests({**request, "chain": [{}]}, ok) is None)
    # The genesis block alone: no subsidy request, and the bound 0 still holds for the record and the result.
    genesis = {**ok, "blocks": ok["blocks"][:1], "set_value": "0"}
    check("issuance genesis alone", validate.issuance_requests(request, genesis) == []
          and validate.issuance_bound(request, genesis, [], [], [])[0] is None)
    for name, changed in (("record", {**genesis, "blocks": [{**genesis["blocks"][0], "set_value": "1"}]}),
                          ("result", {**genesis, "set_value": "1"})):
        failure, _ = validate.issuance_bound(request, changed, [], [], [])
        check(f"issuance genesis alone, {name} above 0", failure is not None and "exceeds" in failure[1], str(failure))


def main() -> int:
    if len(sys.argv) not in (3, 4):
        print(__doc__)
        return 2
    oracle, harness = sys.argv[1], sys.argv[2]
    blocks = pathlib.Path(sys.argv[3] if len(sys.argv) == 4 else ROOT / "build/mainnet-blocks")
    genesis, recent = blocks / "genesis-10000", blocks / "recent-6455302-6456301"
    failures = 0
    cases = 0

    def check(name: str, passed: bool, detail: str = "") -> None:
        nonlocal failures, cases
        cases += 1
        if not passed:
            failures += 1
            print(f"FAIL {name}{': ' + detail if detail else ''}")

    def fails(name: str, text: str, *args, **kwargs) -> None:
        """The replay must fail with a message that has `text`."""
        try:
            replay_blocks.replay(*args, **kwargs, log=lambda _: None)
        except replay_blocks.ReplayError as error:
            check(name, text in str(error), f"failed with {str(error)[:300]}")
        else:
            check(name, False, "the replay passed")

    with tempfile.TemporaryDirectory() as temporary:
        work = pathlib.Path(temporary)
        try:
            summary = replay_blocks.replay(oracle, harness, [str(genesis)], work / "pass", LAST, log=lambda _: None)
        except replay_blocks.ReplayError as error:
            check("replay", False, str(error)[:300])
        else:
            check("replay", (summary["last"], summary["blocks"], summary["set_digests"]) == (LAST, LAST + 1, 2),
                  json.dumps(summary))
            check("replay responses", all((work / "pass" / name).is_file() for name in
                                          ("blocks.bin", "oracle-response.json", "core-response.json", "summary.json")))
            check("replay issuance", int(summary["set_value"]) <= int(summary["subsidy_sum"])
                  and summary["bound_points"] == 2, json.dumps(summary))
            issuance_faults(check, oracle, harness, json.loads((work / "pass" / "oracle-response.json").read_text()))
        fails("oracle as harness", "BLOCK_VALIDATE", oracle, oracle, [str(genesis)], work / "a", LAST)
        fails("harness as oracle", "BLOCK_VALIDATE", harness, harness, [str(genesis)], work / "b", LAST)
        fails("fixture above height 0", "follows height -1", oracle, harness, [str(recent)], work / "c", LAST)
        fails("last above the fixture", "below --last", oracle, harness, [str(genesis)], work / "d", 10001)
        changed = work / "changed"
        shutil.copytree(genesis, changed)
        with open(changed / "blocks.bin", "r+b") as stream:
            stream.seek(100)
            byte = stream.read(1)
            stream.seek(100)
            stream.write(bytes([byte[0] ^ 1]))
        fails("changed fixture", "fixture check", oracle, harness, [str(changed)], work / "e", LAST)

        requests = [req for _, reqs in validate.block_validate_sets() for req in reqs]
        twins = validate.file_twins(requests, answers(oracle, requests), work)
        faults = validate.file_faults(work)
        check("file twins exist", len(twins) >= 30, f"{len(twins)} twins")
        sent = [req for req, _ in twins] + [req for req, _ in faults]
        ours, core = answers(oracle, sent), answers(harness, sent)
        rejected = 0
        for i, ((req, ok), a, b) in enumerate(zip(twins, ours, core)):
            check(f"file twin {i} in the oracle", a.get("ok") == ok, json.dumps(a)[:300])
            fault = validate.compare(req, a, b)
            check(f"file twin {i} in both programs", fault is None, str(fault)[:300])
            rejected += sum(not record["valid"] for record in ok["blocks"])
        check("file twins hold rejected blocks", rejected >= 20, f"{rejected} rejected blocks")
        for i, ((req, want), a, b) in enumerate(zip(faults, ours[len(twins):], core[len(twins):])):
            check(f"file fault {i} in the oracle", error_matches(a, want), json.dumps(a)[:300])
            check(f"file fault {i} in the harness", error_matches(b, want), json.dumps(b)[:300])
    print(f"replay_blocks: {cases} cases, {failures} failures")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
