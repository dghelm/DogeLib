#!/usr/bin/env python3
"""Historical impact runs of a proposed revision on the mainnet ranges (design record 0011, section 10
and stage 6; design record 0012, section 10.3 and stage 4).

Usage:
  python3 -I scripts/impact_run.py request --range NAME --output DIR [--pass DIR] [--harness PROGRAM]
      [--fixture DIR ...]
  python3 -I scripts/impact_run.py run --range NAME --request FILE --revision NAME[/VARIANT]
      --activation HEIGHT|none --output DIR [--baseline FILE] <proposal executable>
  python3 -I scripts/impact_run.py check --range NAME --request FILE --revision NAME[/VARIANT]
      --activation HEIGHT|none --output DIR --response FILE [--baseline FILE] <proposal executable>

The proposal executable is `dogelib-proposal-oracle` for `RelativeLockTime`. The two examples of
the framework, `ExampleVersionVerify` and `ExampleFaultyLocktime`, are not proposals for Dogecoin,
and only the test build `proposal-test-oracle` names them. The examples run on the short range
alone. Their recorded runs on the other ranges are history (docs/oracle.md).

**Ranges.**

| Name | Heights | Start | Inputs of `request` |
| --- | --- | --- | --- |
| `genesis-10000` | 0 to 10,000 | The empty set | `--fixture` of heights 0 to 10,000 |
| `genesis-145000` | 0 to 145,000 | The empty set | `--fixture` of heights 0 to 10,000 and 10,001 to 145,000 |
| `short` | 9,001 to 10,000 | The snapshot at 9,000 | `--fixture` of heights 0 to 10,000 and `--harness` |
| `S` | 100,001 to 101,000 | The snapshot at 100,000 | `--fixture` of heights 0 to 145,000 and `--harness` |
| The configured ranges of design record 0011 | Design record 0011, section 4 | The Core pass's snapshot | `--pass` and `--fixture` of the range |

`request` writes `request.json` to DIR: the range request of `block.validate`, without `revision`.
For `short` and `S`, the harness first replays the blocks from the genesis block and writes the
snapshot, as scripts/snapshot_range.py does. The snapshot must have the committed manifest
`tests/block/mainnet-blocks/snapshots/coins-<a>.json`. For the ranges of the Core pass, `--pass` is
a directory with the pass's `headers.bin` and `state.json`, and `snapshots/coins-<a>.bin`.
`--digests` names the `state.json` of the second pass, which has the digests at the ends of E1 and E2. The
request has the chain of scripts/run_range.py, and the snapshot must have the length and the
SHA-256 of the committed manifest. The fixture check of scripts/fetch_blocks.py runs on every
fixture, and each block of a range must have the committed hash of its height.

`run` sends the request with the argument `revision` to the proposal executable, and checks:

1. The candidate list `tests/proposals/impact/<NAME>.json` of scripts/impact_candidates.py is
   committed: git tracks it, and it has no change against `HEAD`. It names the blocks file of the
   request by its SHA-256.
2. The baseline. Every block record has `valid` true, because every block is a block of mainnet.
   With `--baseline`, the response without the `revised` objects equals that recorded response of
   the same request by `dogelib-oracle`.
3. Case 1 of section 10.3, with `--activation none`: each `revised` object has `active` false, and
   the verdict, the reject reason and the changes digest of its block record
   (`validateBlockWith_inactive`).
4. Case 2, with an activation height: each `revised` object is active from that height. Every
   changed block is a candidate of the revision (`validateBlockWith_congr`,
   `relativeLockTime_eq_of_untouched`). Every change goes from accepted to rejected, and an
   accepted block has the changes digest of the baseline (`connectBlockWith_restricts`,
   `relativeLockTime_restricts`). A candidate with a verdict in `expected` of the list has that
   verdict.

`check` runs checks 1 to 4 on a saved response of `run`, given with `--response`, and writes the
same files. The response must have one block record for each block of the blocks file, with its
height and its hash, and `out_of_domain_at` null.

It writes `summary.json` and `report.json` to DIR: the counts, the changed blocks with their heights,
hashes, verdicts and reasons, and the unsupported results by reason. A changed block is a block
whose two verdicts differ. An unsupported result is not a rejection.

The result of a run is a statement about the blocks of the range. The `revised` verdicts have no
Core comparison (design record 0011, section 10.4). An empty report is not a compatibility proof.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import core_pass
import fetch_blocks
import impact_candidates
import oracle_block_validate as validate
import replay_blocks
import snapshot_range
from fetch_blocks import display
from replay_blocks import ReplayError

MANIFESTS = ROOT / "tests" / "block" / "mainnet-blocks" / "snapshots"
HASHES = ROOT / "tests" / "block" / "mainnet-blocks" / "ranges"
GENESIS = {"genesis-10000": 10000, "genesis-145000": 145000}
FROM_GENESIS_SNAPSHOT = {"short": (9000, 10000), "S": (100000, 101000)}
PASS_RANGES = ("A", "B", "C", "D", "E1", "E2", "F", "H")
RANGES = (*GENESIS, *FROM_GENESIS_SNAPSHOT, *PASS_RANGES)
# The revisions of the runs: the two examples of design record 0011, section 10.3, which only the
# test build `proposal-test-oracle` names, and the proposed revision of design record 0012.
REVISIONS = {"ExampleVersionVerify": None, "ExampleFaultyLocktime/corrected": "corrected", "RelativeLockTime": None}


class ImpactError(Exception):
    """A failed check of an input or of a run."""


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 24), b""):
            digest.update(chunk)
    return digest.hexdigest()


# ---------------------------------------------------------------------------
# Requests


def genesis_request(name: str, fixtures: list[str], output: Path, log) -> dict:
    last = GENESIS[name]
    blocks = output / fetch_blocks.BLOCKS_FILE
    hashes, sha256 = replay_blocks.gather(fixtures, last, blocks)
    log(f"{name}: heights 0 to {last}, every block pinned, SHA-256 {sha256}")
    return {**snapshot_range.base_request(blocks.resolve()), "id": name, "chain": [], "coins": []}


def snapshot_request(name: str, fixtures: list[str], harness: str, output: Path, log) -> dict:
    """The range request of `short` or `S`: the request of scripts/snapshot_range.py."""
    start, end = FROM_GENESIS_SNAPSHOT[name]
    blocks = output / "pass-blocks.bin"
    hashes, sha256 = replay_blocks.gather(fixtures, end, blocks)
    log(f"{name}: heights 0 to {end} for the pass, every block pinned")
    passed = snapshot_range.run_pass(harness, blocks, sha256, hashes, [start], end, output, True, None, log)
    manifest, _ = snapshot_range.check_snapshot(output, passed["snapshots"][0], hashes, MANIFESTS, False, log)
    chain, body = [], []
    for height, raw in fetch_blocks.read_blocks(blocks):
        if height <= start:
            chain.append({"height": height, "time": int.from_bytes(raw[68:72], "little"),
                          "bits": int.from_bytes(raw[72:76], "little")})
        elif height <= end:
            body.append((height, raw))
    range_file = output / fetch_blocks.BLOCKS_FILE
    range_file.write_bytes(b"".join(validate.file_record(height, raw) for height, raw in body))
    blocks.unlink()
    request = {**snapshot_range.base_request(range_file.resolve()), "id": name, "chain": chain[::-1],
               "coins_file": str((output / f"coins-{start}.bin").resolve())}
    del request["coins"]
    request["expected_end"] = passed["set_digests"][0]["set_digest_hex"]
    return request


def pass_request(name: str, state_dir: Path, fixture: Path, log, digests: Path | None = None) -> dict:
    """The range request of a range of the Core pass: the request of scripts/run_range.py, step 4."""
    start, end = core_pass.RANGES[name]
    state = json.loads((state_dir / "state.json").read_text())
    if state["height"] < end:
        raise ImpactError(f"the pass is at height {state['height']}, below {end}")
    headers = core_pass.Headers(state_dir / "headers.bin", state["height"] + 1, read_only=True)
    verifier = fetch_blocks.check_fixture(fixture, fetch_blocks.Pins.load())
    heights = [b["height"] for b in verifier.blocks]
    if heights != list(range(start + 1, end + 1)):
        raise ImpactError(f"the fixture holds heights {heights[0]} to {heights[-1]}, not {start + 1} to {end}")
    kept = [display(headers.hash(h)) for h in heights]
    listing = "".join(f"{h} {value}\n" for h, value in zip(heights, kept))
    if [b["hash"] for b in verifier.blocks] != kept or (HASHES / name / "hashes.txt").read_text() != listing:
        raise ImpactError(f"range {name}: the blocks differ from the pass's headers or the committed hash list")
    manifest = json.loads((MANIFESTS / f"coins-{start}.json").read_text())
    snapshot = state_dir / "snapshots" / f"coins-{start}.bin"
    if manifest["block_hash_display"] != display(headers.hash(start)):
        raise ImpactError("the committed manifest does not name the block below the range")
    if (snapshot.stat().st_size, file_sha256(snapshot)) != (manifest["bytes"], manifest["sha256"]):
        raise ImpactError(f"{snapshot} differs from the committed manifest coins-{start}.json")
    log(f"range {name}: {len(heights)} blocks with the committed hashes; the snapshot at {start} has its manifest")
    window = name in ("E1", "E2")
    if window:
        chain = [headers.entry(h) for h in range(start, core_pass.chain_floor(headers, start + 1) - 1, -1)]
    else:
        floor = max(0, start - core_pass.PERIOD - 260)
        chain = [{k: v for k, v in headers.entry(h).items() if k != "version"} for h in range(start, floor - 1, -1)]
    request = {"id": f"range-{name}", "op": "block.validate", "mode": "allow_witness", "check_pow": True,
               "check_merkle_root": True, "adjusted_time": validate.ADJUSTED_TIME, "chain": chain,
               "bip34_ancestor_hex": headers.hash(core_pass.BIP34_HEIGHT).hex() if start >= core_pass.BIP34_HEIGHT else None,
               "coins_file": str(snapshot.resolve()), "blocks_file": str((fixture / fetch_blocks.BLOCKS_FILE).resolve())}
    if window:
        request["version_bits_heights"] = [start] + [h for h in range(start + 1, end + 1) if (h + 1) % core_pass.PERIOD == 0]
    digest = state["digests"].get(str(end))
    if digest is None and digests is not None:
        digest = json.loads(digests.read_text())["digests"].get(str(end))
    request["expected_end"] = digest["set_digest_hex"] if digest else None
    return request


def make_request(args, log) -> int:
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    if args.range in GENESIS:
        request = genesis_request(args.range, args.fixture, output, log)
    elif args.range in FROM_GENESIS_SNAPSHOT:
        if not args.harness:
            raise ImpactError("the range needs --harness")
        request = snapshot_request(args.range, args.fixture, args.harness, output, log)
    else:
        if not args.state or len(args.fixture) != 1:
            raise ImpactError("the range needs --pass and one --fixture")
        request = pass_request(args.range, Path(args.state), Path(args.fixture[0]), log,
                               Path(args.digests) if args.digests else None)
    (output / "request.json").write_text(json.dumps(request) + "\n")
    log(f"wrote {output / 'request.json'}")
    return 0


# ---------------------------------------------------------------------------
# Runs


def committed(path: Path) -> str:
    """The last commit that changed `path`, when git tracks `path` and `path` has no change against `HEAD`."""
    tracked = subprocess.run(["git", "-C", str(ROOT), "ls-files", "--error-unmatch", str(path)], capture_output=True)
    clean = subprocess.run(["git", "-C", str(ROOT), "diff", "--quiet", "HEAD", "--", str(path)], capture_output=True)
    if tracked.returncode != 0 or clean.returncode != 0:
        raise ImpactError(f"{path} is not committed: commit the candidate list before the run")
    return subprocess.run(["git", "-C", str(ROOT), "log", "-1", "--format=%H", "--", str(path)], capture_output=True,
                          text=True, check=True).stdout.strip()


def changed(record: dict) -> bool:
    return record["valid"] != (record["revised"]["verdict"] == "accepted") and record["revised"]["verdict"] != "unsupported"


def requested_blocks(request: dict) -> list[tuple[int, str]]:
    """The height and the block hash, in display order, of each block of the request's `blocks_file`."""
    return [(height, display(fetch_blocks.sha256d(raw[:80])))
            for height, raw in fetch_blocks.read_blocks(Path(request["blocks_file"]))]


def check_response(answer: dict, request: dict, revision: dict, candidates: dict, baseline: dict | None,
                   blocks: list[tuple[int, str]]) -> dict:
    """Checks 2 to 4 of a run, and the report. Raise `ImpactError` on a failed check.

    `blocks` is the height and the hash of each requested block. The response must have one block
    record for each of them, in order, and `out_of_domain_at` null, so an empty or a truncated
    response fails."""
    ok = answer.get("ok")
    if not isinstance(ok, dict):
        raise ImpactError(f"the proposal executable returned {json.dumps(answer)[:300]}")
    records = ok["blocks"]
    if ok.get("out_of_domain_at") is not None:
        raise ImpactError(f"the run left the arithmetic domain at {ok['out_of_domain_at']}")
    if len(records) != len(blocks):
        raise ImpactError(f"{len(records)} block records for {len(blocks)} requested blocks")
    for r, (height, block_hash) in zip(records, blocks):
        if (r.get("height"), r.get("hash_display")) != (height, block_hash):
            raise ImpactError(f"the block record of height {r.get('height')} is not the requested block {height} {block_hash}")
    if any(not isinstance(r.get("revised"), dict) for r in records):
        raise ImpactError("a block record has no revised object")
    invalid = [r["height"] for r in records if not r["valid"]]
    if invalid:
        raise ImpactError(f"the baseline rejects the blocks at {invalid[:10]}")
    if baseline is not None:
        plain = {**ok, "blocks": [{k: v for k, v in r.items() if k != "revised"} for r in records]}
        if plain != baseline.get("ok"):
            raise ImpactError("the response without the revised objects differs from the recorded baseline response")
    if request.get("expected_end") and ok["set_digest_hex"] != request["expected_end"]:
        raise ImpactError(f"the end digest {ok['set_digest_hex']} is not the expected {request['expected_end']}")
    activation = revision["activation_height"]
    listed = {c["height"]: c for c in candidates["candidates"]}
    report = {"changed": [], "unsupported": {}, "rejected_by_step": {}}
    for r in records:
        rev = r["revised"]
        want_active = activation is not None and r["height"] >= activation
        if rev["active"] is not want_active:
            raise ImpactError(f"height {r['height']}: active is {rev['active']}, expected {want_active}")
        if activation is None:
            same = (rev["verdict"] == "accepted" and rev["reject_reason"] == r["reject_reason"]
                    and rev["changes_digest_hex"] == r["changes_digest_hex"])
            if not same:
                raise ImpactError(f"height {r['height']}: with no activation the revised object differs: {json.dumps(rev)}")
            continue
        if rev["verdict"] == "unsupported":
            report["unsupported"][rev["reason"]] = report["unsupported"].get(rev["reason"], 0) + 1
            report.setdefault("unsupported_blocks", []).append({"height": r["height"], "hash": r["hash_display"],
                                                                "step": rev["step"], "reason": rev["reason"]})
        elif rev["verdict"] == "accepted":
            if rev["changes_digest_hex"] != r["changes_digest_hex"]:
                raise ImpactError(f"height {r['height']}: the revision accepts with other coin changes")
        if changed(r):
            entry = {"height": r["height"], "hash": r["hash_display"], "baseline": "accepted", "revised": rev["verdict"],
                     **{k: rev[k] for k in ("step", "reject_reason", "tx", "input", "script_error", "mandatory")}}
            if not r["valid"]:
                raise ImpactError(f"height {r['height']}: the block goes from rejected to accepted")
            if r["height"] not in listed:
                raise ImpactError(f"height {r['height']}: a changed block that is not a candidate: {json.dumps(entry)}")
            report["changed"].append(entry)
            key = f"{rev['step']}: {rev['reject_reason']}"
            report["rejected_by_step"][key] = report["rejected_by_step"].get(key, 0) + 1
        expected = listed.get(r["height"], {}).get("expected")
        if expected is not None:
            got = {k: rev.get(k) for k in expected}
            if got != expected:
                raise ImpactError(f"height {r['height']}: the candidate has {json.dumps(got)}, expected {json.dumps(expected)}")
    report["blocks"] = len(records)
    report["candidate_blocks"] = len(listed)
    report["changed_blocks"] = len(report["changed"])
    return report


def run(args, log) -> int:
    """`run`, and `check` on a saved response with `--response`."""
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    name = args.revision.split("/")[0]
    if args.revision not in REVISIONS:
        raise ImpactError(f"unknown revision {args.revision}")
    activation = None if args.activation == "none" else int(args.activation)
    revision = {"name": name, "variant": REVISIONS[args.revision], "activation_height": activation}
    request = json.loads(Path(args.request).read_text())
    path = impact_candidates.list_path(args.range)
    commit = committed(path)
    candidates = impact_candidates.load(args.range)
    blocks_sha256 = file_sha256(Path(request["blocks_file"]))
    if candidates["blocks_sha256"] != blocks_sha256:
        raise ImpactError(f"the candidate list names the blocks file {candidates['blocks_sha256']}, not {blocks_sha256}")
    baseline = json.loads(Path(args.baseline).read_text()) if args.baseline else None
    body = {k: v for k, v in request.items() if k != "expected_end"}
    body = {**body, "id": f"impact-{args.range}", "revision": revision}
    log(f"{args.range}: {args.revision}, activation {args.activation}, {candidates['revisions'][name]['candidate_blocks']} "
        f"candidate blocks in {path.relative_to(ROOT)} at {commit[:12]}")
    if getattr(args, "response", None):
        answer, seconds = json.loads(Path(args.response).read_text()), None
        if answer.get("id") != body["id"]:
            raise ImpactError(f"{args.response} is not a response to this request")
        log(f"{args.range}: checking the saved response {args.response}")
    else:
        answer, seconds = replay_blocks.run(args.proposal_oracle, body, output / "response.json", None)
        log(f"{args.range}: the proposal executable took {seconds:.0f} seconds")
    report = check_response(answer, request, revision, candidates["revisions"][name], baseline,
                            requested_blocks(request))
    summary = {"range": args.range, "revision": revision, "first": candidates["first"], "last": candidates["last"],
               "blocks_sha256": blocks_sha256, "coins_file": Path(request["coins_file"]).name if request.get("coins_file") else None,
               "candidate_list": str(path.relative_to(ROOT)), "candidate_list_sha256": file_sha256(path),
               "candidate_list_commit": commit, "proposal_oracle_sha256": file_sha256(Path(args.proposal_oracle)),
               "baseline_compared": args.baseline is not None, "set_digest_hex": answer["ok"]["set_digest_hex"],
               "set_coins": answer["ok"]["set_coins"], "seconds": None if seconds is None else round(seconds),
               "saved_response": getattr(args, "response", None),
               **{k: report[k] for k in ("blocks", "candidate_blocks", "changed_blocks", "unsupported", "rejected_by_step")}}
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    log(f"{args.range}: {report['blocks']} blocks, {report['candidate_blocks']} candidates, "
        f"{report['changed_blocks']} changed, unsupported {report['unsupported']}")
    print(json.dumps(summary, indent=2))
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    req = sub.add_parser("request")
    req.add_argument("--range", required=True, choices=RANGES)
    req.add_argument("--output", required=True, metavar="DIR")
    req.add_argument("--pass", dest="state", metavar="DIR")
    req.add_argument("--harness", metavar="PROGRAM")
    req.add_argument("--digests", metavar="STATE", help="a second pass's state.json with the digest at the range end")
    req.add_argument("--fixture", action="append", default=[], metavar="DIR")
    go = sub.add_parser("run")
    go.add_argument("--range", required=True, choices=RANGES)
    go.add_argument("--request", required=True, metavar="FILE")
    go.add_argument("--revision", required=True, choices=sorted(REVISIONS))
    go.add_argument("--activation", required=True, metavar="HEIGHT|none")
    go.add_argument("--output", required=True, metavar="DIR")
    go.add_argument("--baseline", metavar="FILE")
    go.add_argument("proposal_oracle")
    again = sub.add_parser("check")
    for flag, extra in (("--range", {"choices": RANGES}), ("--request", {}), ("--revision", {"choices": sorted(REVISIONS)}),
                        ("--activation", {}), ("--output", {}), ("--response", {})):
        again.add_argument(flag, required=True, **extra)
    again.add_argument("--baseline", metavar="FILE")
    again.add_argument("proposal_oracle", help="the executable that wrote the response, for its SHA-256")
    args = parser.parse_args(argv)
    log = lambda text: print(text, flush=True)
    try:
        return make_request(args, log) if args.command == "request" else run(args, log)
    except (ImpactError, ReplayError, core_pass.PassError, fetch_blocks.FetchError, impact_candidates.CandidateError,
            OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
