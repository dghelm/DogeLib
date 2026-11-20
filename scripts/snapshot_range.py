#!/usr/bin/env python3
"""Run a range of mainnet blocks through `block.validate` from a coin-set snapshot, in the oracle and in Core.

Usage:
  python3 -I scripts/snapshot_range.py --start A --end B [--snapshot HEIGHT]... --output DIR
      [--manifests DIR] [--write-manifests] [--reuse-pass] [--jobs N] [--fault-blocks N] [--timeout SECONDS]
      <dogelib-oracle> <core-oracle> FIXTURE...

Each FIXTURE is a directory of scripts/fetch_blocks.py or scripts/fetch_release_blocks.py. Together,
in the order given, the fixtures hold the consecutive heights from 0 to at least B.

This is the gate of design record 0011, stage 1: the snapshot path on blocks that the replay from
the genesis block covers. The range has the heights from A + 1 to B, and it starts from the
snapshot at A (docs/oracle.md, "Coin-set snapshots"). The script works in seven steps:

1. It checks the fixtures and writes their blocks to `DIR/blocks.bin`, as scripts/replay_blocks.py
   does. Every block must have a pinned hash.
2. The pass. The Core harness replays the blocks from the genesis block, from the empty coin
   set. It writes a snapshot at A and at each `--snapshot` height, and it reports the digest of
   the whole set at B. Every block must be accepted.
3. The script reads each snapshot again and computes its SHA-256, its digest, its number of
   coins and its total value from the definition of the format. All must equal the values of the
   harness. The script writes a manifest for each snapshot, and requires that it equals the
   committed manifest of `--manifests` (default tests/block/mainnet-blocks/snapshots).
   `--write-manifests` writes the committed manifests in the place of that comparison.
4. The range. The oracle and the harness get one request with `coins_file` and the blocks of the
   range. The first block must name the block hash of the manifest. The range agrees when both
   programs report the digest and the number of coins of the manifest as the start, accept every
   block with equal block records, and report the digest of step 2 at B as the end. The block
   records must also equal those of the same heights in the pass, without the digests of the
   whole set.
5. The oracle runs the range again with `coins_in_memory`, on the whole set. Its `ok` object must
   equal the one of step 4.
6. Changed snapshots. Each case changes the snapshot at A and runs the first `--fault-blocks`
   blocks of the range in both programs. A change that leaves the records of a coin set must give
   a start digest that is not the manifest's, in both programs, and equal to the digest that the
   script computes from the changed file. Where such a change makes both programs reject a block,
   the block after it is not linked, and both must return that error. Every other change must
   give its error in both programs. One removed record has a transaction ID that no block of the
   request names: the block records then equal those of the unchanged snapshot, and only the
   digests differ.
7. The small requests of scripts/oracle_block_validate.py run in both programs with their coins
   in a snapshot, and so do its changed snapshots.

`--reuse-pass` skips step 2 when DIR holds the response of an earlier pass on the same blocks,
with the same heights, and each snapshot file still has its SHA-256.

The script writes the responses, the manifests and `summary.json` to DIR. The exit status is 0
only when every step passes. A snapshot of height 100,000 has about 420 MB, and step 6 writes
one changed copy at a time for each of `--jobs` workers.

The short form of CI, on the released blocks of heights 0 to 10,000:

  python3 -I scripts/snapshot_range.py --start 9000 --end 10000 --output build/snapshot-range/short \\
      .lake/build/bin/dogelib-oracle build/core-harness/core-oracle build/mainnet-blocks/genesis-10000

Range S of the design record, outside CI, with the snapshot at height 145,000:

  taskset -c 8-11 nice -n 19 python3 -I scripts/snapshot_range.py --start 100000 --end 101000 \\
      --snapshot 145000 --jobs 3 --output build/snapshot-range/s \\
      .lake/build/bin/dogelib-oracle build/core-harness/core-oracle \\
      build/mainnet-blocks/genesis-10000 build/mainnet-blocks/range-10001-145000
"""

import argparse
import concurrent.futures
import hashlib
import json
import sys
import tempfile
from pathlib import Path

# Import the helpers beside this script, including under Python's isolated mode.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fetch_blocks
import oracle_block_validate as validate
import replay_blocks
from oracle_block_check import split_block
from replay_blocks import ReplayError

FORMAT = "dogelib-coins/1"
MANIFESTS = Path(__file__).resolve().parent.parent / "tests" / "block" / "mainnet-blocks" / "snapshots"


def base_request(blocks: Path) -> dict:
    """The arguments of a real range from the genesis block: both flags, the witness mode, no chain and no coin."""
    request = {**validate.request([], check_pow=True, mode="allow_witness"), "blocks_file": str(blocks)}
    del request["blocks_hex"]
    return request


def manifest_of(snapshot: dict) -> dict:
    """The manifest of a snapshot, from its record in the response of the harness."""
    return {"format": FORMAT, "height": snapshot["height"], "block_hash_hex": snapshot["hash_hex"],
            "block_hash_display": snapshot["hash_display"], "coins": snapshot["set_coins"],
            "set_digest_hex": snapshot["set_digest_hex"], "set_value": snapshot["set_value"],
            "bytes": snapshot["bytes"], "sha256": snapshot["sha256"]}


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run_pass(harness: str, blocks: Path, blocks_sha256: str, hashes: list[str], snapshots: list[int], end: int,
             output: Path, reuse: bool, timeout, log) -> dict:
    """Step 2: the replay from the genesis block by the harness, with the snapshots and the digest at `end`."""
    request = {**base_request(blocks), "id": "pass", "snapshot_heights": snapshots, "snapshot_dir": str(output),
               "digest_heights": [end]}
    response, stamp = output / "pass-response.json", output / "pass.json"
    key = {"blocks_sha256": blocks_sha256, "snapshot_heights": snapshots, "digest_heights": [end]}
    answer = None
    if reuse and response.exists() and stamp.exists() and json.loads(stamp.read_text()) == key:
        answer = json.loads(response.read_text())
        log("pass: reusing the response in the output directory")
    if answer is None:
        stamp.unlink(missing_ok=True)
        answer, seconds = replay_blocks.run(harness, request, response, timeout)
        stamp.write_text(json.dumps(key) + "\n")
        log(f"pass: Core replayed heights 0 to {len(hashes) - 1} in {seconds:.0f} seconds")
    ok = answer.get("ok")
    if not isinstance(ok, dict):
        raise ReplayError(f"pass: the harness returned {json.dumps(answer)[:300]}")
    records = ok["blocks"]
    if [r["hash_display"] for r in records if r["valid"]] != hashes or len(records) != len(hashes):
        raise ReplayError("pass: the harness did not accept every block of the fixtures")
    if [s["height"] for s in ok.get("snapshots", [])] != snapshots:
        raise ReplayError("pass: the harness did not write every snapshot")
    if [d["height"] for d in ok.get("set_digests", [])] != [end]:
        raise ReplayError(f"pass: the harness did not report the digest at height {end}")
    # A block record of the pass has the digest of the whole set at each multiple of 1,000,
    # which the replays from the genesis block compare with the oracle.
    for entry in ok["snapshots"] + ok["set_digests"]:
        record = records[entry["height"]]
        if record["set_digest_hex"] not in (None, entry["set_digest_hex"]):
            raise ReplayError(f"pass: two digests of the whole set at height {entry['height']}")
    return ok


def check_snapshot(output: Path, snapshot: dict, hashes: list[str], manifests: Path, write: bool, log) -> tuple[dict, bytes]:
    """Step 3 for one snapshot: its values from the definition, its manifest, and the committed manifest."""
    height = snapshot["height"]
    manifest = manifest_of(snapshot)
    data = (output / snapshot["file"]).read_bytes()
    try:
        digest, coins, value = validate.snapshot_summary(data)
    except ValueError as error:
        raise ReplayError(f"snapshot {height}: {error}") from None
    computed = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "set_digest_hex": digest,
                "coins": coins, "set_value": value, "block_hash_display": hashes[height]}
    for field, got in computed.items():
        if manifest[field] != got:
            raise ReplayError(f"snapshot {height}: the harness reports {field} {manifest[field]!r}, and the file gives {got!r}")
    text = json.dumps(manifest, indent=2) + "\n"
    (output / f"coins-{height}.json").write_text(text)
    committed = manifests / f"coins-{height}.json"
    if write:
        manifests.mkdir(parents=True, exist_ok=True)
        committed.write_text(text)
    elif not committed.exists():
        raise ReplayError(f"snapshot {height}: no committed manifest {committed}")
    elif json.loads(committed.read_text()) != manifest:
        raise ReplayError(f"snapshot {height}: the manifest differs from the committed {committed}")
    log(f"snapshot {height}: {coins} coins, {len(data)} bytes, digest {digest}, manifest {'written' if write else 'agrees'}")
    return manifest, data


def strip(ok: dict) -> list[dict]:
    """The block records without the oracle's diagnostic and without the digests of the whole set."""
    return [{k: v for k, v in record.items() if k not in ("diagnostic", "set_digest_hex", "set_value")}
            for record in ok["blocks"]]


def start_fault(ok: dict, manifest: dict) -> str | None:
    """How the start of a response differs from the manifest of its snapshot, or None."""
    if ok["start_set_digest_hex"] != manifest["set_digest_hex"]:
        return f"the start digest is {ok['start_set_digest_hex']}, and the manifest has {manifest['set_digest_hex']}"
    if ok["start_set_coins"] != manifest["coins"]:
        return f"the start has {ok['start_set_coins']} coins, and the manifest has {manifest['coins']}"
    return None


def named_ids(blocks: list[bytes]) -> set[bytes]:
    """The transaction IDs that the blocks name: the ID of each transaction, and the ID in the outpoint of each input."""
    ids = set()
    for raw in blocks:
        for tx in split_block(raw)[1]:
            base, inputs, _, _ = validate.parse_transaction(tx, 0)
            ids.add(validate.sha256d(base))
            ids.update(point[:32] for point in inputs)
    return ids


def run_faults(oracle: str, harness: str, request: dict, manifest: dict, data: bytes, blocks: list[tuple[int, bytes]],
               output: Path, jobs: int, timeout, log) -> int:
    """Step 6: the changed snapshots. Return the number of cases."""
    short = output / "fault-blocks.bin"
    short.write_bytes(b"".join(validate.file_record(height, raw) for height, raw in blocks))
    offsets = validate.snapshot_offsets(data)
    single, pair = validate.snapshot_positions(data, offsets)
    named = named_ids([raw for _, raw in blocks])
    ids = [data[start + 1:start + 33] for start in offsets[:-1]]
    inside = next((i for i, txid in enumerate(ids) if txid in named), None)
    outside = next(i for i, txid in enumerate(ids) if txid not in named)
    if inside is None:
        raise ReplayError("faults: the first blocks of the range name no coin of the snapshot")
    cases = validate.snapshot_mutations(data, offsets, single, pair, removed=(inside, outside))

    def one(case, good=None):
        name, content, error = case
        with tempfile.NamedTemporaryFile(dir=output, prefix=f"fault-{name}-", suffix=".coins") as changed:
            changed.write(content)
            changed.flush()
            req = {**request, "id": f"fault-{name}", "blocks_file": str(short), "coins_file": changed.name}
            with tempfile.TemporaryDirectory(dir=output) as scratch:
                core, _ = replay_blocks.run(harness, req, Path(scratch) / "core.json", timeout)
                ours, _ = replay_blocks.run(oracle, req, Path(scratch) / "oracle.json", timeout)
        if error is not None:
            for side, answer in (("oracle", ours), ("Core", core)):
                if answer.get("error") != error:
                    raise ReplayError(f"fault {name}: {side} returned {json.dumps(answer)[:300]}, expected the error {json.dumps(error)}")
            return name, None
        failure = validate.compare(req, ours, core)
        if failure:
            raise ReplayError(f"fault {name}: {failure[1]}")
        if "ok" not in ours:
            # A block that the changed coins reject changes nothing, so the block after it is not linked.
            if content == data or ours["error"].get("reason") != "not_linked":
                raise ReplayError(f"fault {name}: both programs returned {json.dumps(ours['error'])}")
            return name, None
        ok = ours["ok"]
        if content == data:
            if start_fault(ok, manifest):
                raise ReplayError(f"faults: the unchanged snapshot fails: {start_fault(ok, manifest)}")
            return name, ok
        if not start_fault(ok, manifest) or ok["start_set_digest_hex"] == manifest["set_digest_hex"]:
            raise ReplayError(f"fault {name}: the changed snapshot has the start of the manifest")
        if ok["start_set_digest_hex"] != validate.snapshot_summary(content)[0]:
            raise ReplayError(f"fault {name}: the start digest is not the digest of the changed file")
        if name == f"removed-{outside}":
            if strip(ok) != strip(good) or ok["set_digest_hex"] == good["set_digest_hex"]:
                raise ReplayError(f"fault {name}: a removed coin that no block names must change the digests alone")
        return name, ok

    _, good = one(("unchanged", data, None))
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for (name, _, error), (_, ok) in zip(cases, pool.map(lambda case: one(case, good), cases)):
            how = "error" if error is not None else "start digest" if ok is not None else "rejected block"
            log(f"changed snapshot {name}: found by the {how}")
    return len(cases)


def run_twins(oracle: str, harness: str, timeout, log) -> tuple[int, int]:
    """Step 7: the small requests with their coins in a snapshot, and the changed synthetic snapshots, in both programs."""
    requests = [req for _, group in validate.block_validate_sets() for req in group]
    with tempfile.TemporaryDirectory() as directory:
        plain = replay_blocks.run_stream(oracle, requests, timeout)
        twins = validate.snapshot_twins(requests, plain, directory)
        faults = validate.snapshot_faults(directory)
        sent = [req for req, _ in twins] + [req for req, _, _ in faults]
        ours = replay_blocks.run_stream(oracle, sent, timeout)
        core = replay_blocks.run_stream(harness, sent, timeout)
        memory = replay_blocks.run_stream(oracle, [{**req, "coins_in_memory": True} for req, _ in twins], timeout)
    for i, (req, expected) in enumerate(twins):
        if ours[i].get("ok") != expected or memory[i].get("ok") != expected:
            raise ReplayError(f"twin {i}: the oracle differs from the request with `coins`: {json.dumps(ours[i])[:300]}")
        plain_core = {k: v for k, v in expected.items()}
        plain_core["blocks"] = [{k: v for k, v in record.items() if k != "diagnostic"} for record in expected["blocks"]]
        if core[i].get("ok") != plain_core:
            raise ReplayError(f"twin {i}: Core differs from the oracle: {json.dumps(core[i])[:300]}")
    for i, (req, error, digest) in enumerate(faults, start=len(twins)):
        for side, answer in (("oracle", ours[i]), ("Core", core[i])):
            if error is None:
                good = isinstance(answer.get("ok"), dict) and answer["ok"].get("start_set_digest_hex") == digest
            elif error == {"kind": "request"}:
                good = isinstance(answer.get("error"), dict) and answer["error"].get("kind") == "request"
            else:
                good = answer.get("error") == error
            if not good:
                raise ReplayError(f"synthetic fault {i - len(twins)}: {side} returned {json.dumps(answer)[:300]}")
    log(f"small requests: {len(twins)} with a snapshot agree in both programs and with coins_in_memory, "
        f"and {len(faults)} changed snapshots or requests give their expected results")
    return len(twins), len(faults)


def snapshot_range(oracle: str, harness: str, fixtures: list[str], output: Path, start: int, end: int,
                   extra: list[int], manifests: Path = MANIFESTS, write_manifests: bool = False, reuse: bool = False,
                   jobs: int = 2, fault_blocks: int = 10, timeout=None, pins=None,
                   log=lambda text: print(text, flush=True)) -> dict:
    """Run the seven steps, and return the summary. Raise `ReplayError` on any failure."""
    output.mkdir(parents=True, exist_ok=True)
    snapshots = sorted({start, *extra})
    last = max(end, snapshots[-1])
    blocks = output / fetch_blocks.BLOCKS_FILE
    hashes, sha256 = replay_blocks.gather(fixtures, last, blocks, pins)
    log(f"fixtures: heights 0 to {last}, every block pinned, SHA-256 {sha256}")
    twins, synthetic = run_twins(oracle, harness, timeout, log)

    passed = run_pass(harness, blocks, sha256, hashes, snapshots, end, output, reuse, timeout, log)
    end_set = passed["set_digests"][0]
    checked = {s["height"]: check_snapshot(output, s, hashes, manifests, write_manifests, log) for s in passed["snapshots"]}
    manifest, data = checked[start]
    del checked

    # The chain of the range, newest first, and its blocks.
    chain, body = [], []
    for height, raw in fetch_blocks.read_blocks(blocks):
        if height <= start:
            chain.append({"height": height, "time": int.from_bytes(raw[68:72], "little"),
                          "bits": int.from_bytes(raw[72:76], "little")})
        elif height <= end:
            body.append((height, raw))
    if body[0][1][4:36][::-1].hex() != manifest["block_hash_display"]:
        raise ReplayError("range: the first block does not name the block hash of the manifest")
    range_file = output / "range.bin"
    range_file.write_bytes(b"".join(validate.file_record(height, raw) for height, raw in body))
    request = {**base_request(range_file), "id": "range", "chain": chain[::-1],
               "coins_file": str(output / f"coins-{start}.bin")}
    del request["coins"]
    (output / "range-request.json").write_text(json.dumps(request) + "\n")

    core, core_seconds = replay_blocks.run(harness, request, output / "range-core-response.json", timeout)
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(jobs, 2)) as pool:
        restricted = pool.submit(replay_blocks.run, oracle, request, output / "range-oracle-response.json", timeout)
        whole = pool.submit(replay_blocks.run, oracle, {**request, "coins_in_memory": True},
                            output / "range-oracle-memory-response.json", timeout)
        (ours, oracle_seconds), (memory, memory_seconds) = restricted.result(), whole.result()
    log(f"range: Core {core_seconds:.0f} seconds, oracle {oracle_seconds:.0f} seconds, "
        f"oracle with coins_in_memory {memory_seconds:.0f} seconds")
    failure = validate.compare(request, ours, core)
    if failure:
        raise ReplayError(f"range: {failure[1]}")
    ok = ours["ok"]
    if [r["hash_display"] for r in ok["blocks"] if r["valid"]] != hashes[start + 1:end + 1]:
        raise ReplayError("range: the programs did not accept every block of the range")
    if start_fault(ok, manifest):
        raise ReplayError(f"range: {start_fault(ok, manifest)}")
    for field in ("set_digest_hex", "set_coins", "set_value"):
        if ok[field] != end_set[field]:
            raise ReplayError(f"range: the end has {field} {ok[field]!r}, and the pass has {end_set[field]!r} at height {end}")
    if strip(ok) != strip({"blocks": passed["blocks"][start + 1:end + 1]}):
        raise ReplayError("range: the block records differ from those of the replay from the genesis block")
    if memory.get("ok") != ok:
        raise ReplayError("range: the oracle with coins_in_memory differs from the oracle on the named coins")
    log(f"range: heights {start + 1} to {end} agree, from {manifest['coins']} coins to {ok['set_coins']} coins")

    faults = run_faults(oracle, harness, request, manifest, data, body[:fault_blocks], output, jobs, timeout, log)
    summary = {
        "start": start, "end": end, "blocks": len(body), "blocks_sha256": sha256,
        "snapshots": snapshots,
        "start_set_digest_hex": ok["start_set_digest_hex"], "start_set_coins": ok["start_set_coins"],
        "set_digest_hex": ok["set_digest_hex"], "set_coins": ok["set_coins"], "set_value": ok["set_value"],
        "spent": sum(r["spent"] for r in ok["blocks"]), "created": sum(r["created"] for r in ok["blocks"]),
        "changed_snapshots": faults, "snapshot_twins": twins, "synthetic_faults": synthetic,
        "core_seconds": round(core_seconds), "oracle_seconds": round(oracle_seconds),
        "oracle_memory_seconds": round(memory_seconds),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--start", type=int, required=True, metavar="A", help="the height of the snapshot")
    parser.add_argument("--end", type=int, required=True, metavar="B", help="the last height of the range")
    parser.add_argument("--snapshot", type=int, action="append", default=[], metavar="HEIGHT",
                        help="another height at which the pass writes a snapshot")
    parser.add_argument("--output", required=True, metavar="DIR")
    parser.add_argument("--manifests", default=str(MANIFESTS), metavar="DIR", help="the committed manifests")
    parser.add_argument("--write-manifests", action="store_true", help="write the committed manifests")
    parser.add_argument("--reuse-pass", action="store_true", help="reuse the pass of an earlier run in DIR")
    parser.add_argument("--jobs", type=int, default=2, metavar="N", help="program pairs at one time, default 2")
    parser.add_argument("--fault-blocks", type=int, default=10, metavar="N",
                        help="blocks of the range in each changed-snapshot case, default 10")
    parser.add_argument("--timeout", type=float, metavar="SECONDS", help="for each program run; no limit by default")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    parser.add_argument("fixtures", nargs="+", metavar="FIXTURE")
    args = parser.parse_args(argv)
    if not 0 <= args.start < args.end or any(height < 0 for height in args.snapshot):
        parser.error("the heights must satisfy 0 <= A < B")
    if args.jobs < 1 or args.fault_blocks < 1:
        parser.error("--jobs and --fault-blocks need a number from 1")
    try:
        summary = snapshot_range(args.oracle, args.harness, args.fixtures, Path(args.output), args.start, args.end,
                                 args.snapshot, Path(args.manifests), args.write_manifests, args.reuse_pass, args.jobs,
                                 args.fault_blocks, args.timeout)
    except ReplayError as error:
        print(f"FAIL: {error}")
        return 1
    print(f"block.validate from the snapshot at height {summary['start']}: heights {summary['start'] + 1} to "
          f"{summary['end']}, {summary['blocks']} blocks accepted by both programs")
    print(f"start: {summary['start_set_coins']} coins, digest {summary['start_set_digest_hex']}, as the manifest")
    print(f"end: {summary['set_coins']} coins, digest {summary['set_digest_hex']}, as the replay from the genesis block")
    print(f"coin changes: {summary['spent']} spent, {summary['created']} created; the oracle agrees with coins_in_memory")
    print(f"{summary['changed_snapshots']} changed snapshots found, {summary['snapshot_twins']} small requests and "
          f"{summary['synthetic_faults']} synthetic cases agree, 0 failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())
