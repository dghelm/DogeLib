#!/usr/bin/env python3
"""Run one range of design record 0011 from a snapshot of the Core pass, in the oracle and in Core.

Usage:
  python3 -I scripts/run_range.py --range NAME --pass DIR --fixture DIR --output DIR [--write-hashes]
      [--cache-mb MB] <dogelib-oracle> <core-oracle>

NAME is a range of design record 0011, section 4: A, B, C, D, F, H or G. DIR of `--pass` is the
state directory of scripts/core_pass.py, which must have passed the range's end. The fixture is a
directory of scripts/fetch_blocks.py with the blocks of the range, from `a + 1` to `b`. The script
works in six steps:

1. It checks the fixture as `scripts/fetch_blocks.py --check` does. Each block hash must equal the
   hash of the header that the pass kept at its height, and the committed list
   `tests/block/mainnet-blocks/ranges/<NAME>/hashes.txt`. `--write-hashes` writes that list and its
   `SHA256SUMS` from the pass's headers in the place of the comparison.
2. It checks the snapshot of the range start: its SHA-256 and length equal the pass's manifest,
   and the manifest names the block below the range. The manifest file of the pass must equal the
   committed `tests/block/mainnet-blocks/snapshots/coins-<a>.json`, when that file exists.
3. `block.check` with both flags on every block, in the oracle and in Core, before the range
   (design record 0011, section 7). Both must accept every block. The oracle's time is recorded.
4. The range request: the snapshot at `a` as `coins_file`, the blocks of the fixture, the chain
   from the pass's headers, the BIP34 ancestor, both flags and the adjusted time of the pass. The
   harness also gets `coins_db` on a scratch directory, because the set of a recent height does
   not fit in its map. The oracle holds only the coins that the blocks name.
5. The range agrees under section 3.4 when both programs report the digest and the number of
   coins of the manifest as the start, accept every block with equal block records, and report
   the pass's digest at `b` as the end. The block records must also equal those of the pass.
6. It writes `summary.json` with the inputs, their SHA-256 values, the counts and the times.

Run each range on one core at low priority, and register it in the lane's STATUS.md.
"""

import argparse
import gzip
import hashlib
import json
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import core_pass
import fetch_blocks
import oracle_block_validate as validate
import replay_blocks
from fetch_blocks import display
from oracle_block_check import block_request
from replay_blocks import ReplayError

ROOT = Path(__file__).resolve().parent.parent
HASHES = ROOT / "tests" / "block" / "mainnet-blocks" / "ranges"
MANIFESTS = ROOT / "tests" / "block" / "mainnet-blocks" / "snapshots"


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 22), b""):
            digest.update(chunk)
    return digest.hexdigest()


def pass_records(state_dir: Path, first: int, last: int) -> list[dict]:
    """The block records of the pass for the heights from `first` to `last`.

    The records come from every archived response on disk. A restart of the pass removes a segment
    above its snapshot from the state, but its archive stays, and a later segment can cover the same
    heights again. Two records of one height must then be equal."""
    by_height = {}
    for archive in sorted((state_dir / "responses").glob("from-*.json.gz")):
        start = int(archive.name[len("from-"):-len(".json.gz")])
        if start > last:
            continue
        with gzip.open(archive, "rt") as stream:
            ok = json.loads(stream.readline())["ok"]
        for record in ok["blocks"]:
            if first <= record["height"] <= last:
                if by_height.setdefault(record["height"], record) != record:
                    raise ReplayError(f"two archived records of height {record['height']} differ")
    if sorted(by_height) != list(range(first, last + 1)):
        raise ReplayError(f"the pass's responses do not hold the heights {first} to {last}")
    return [by_height[h] for h in range(first, last + 1)]


def strip(records: list[dict]) -> list[dict]:
    return [{k: v for k, v in r.items() if k not in ("diagnostic", "set_digest_hex", "set_value")} for r in records]


def run_range(name: str, state_dir: Path, fixture: Path, output: Path, oracle: str, harness: str,
              write_hashes: bool = False, cache_mb: int = 2048, log=lambda text: print(text, flush=True),
              hashes: Path = HASHES, manifests: Path = MANIFESTS) -> dict:
    start, end = core_pass.RANGES[name]
    output.mkdir(parents=True, exist_ok=True)
    state = core_pass.load_state(state_dir / "state.json")
    if state["height"] < end or str(end) not in state["digests"]:
        raise ReplayError(f"the pass is at height {state['height']}, without the digest at {end}")
    headers = core_pass.Headers(state_dir / "headers.bin", state["height"] + 1, read_only=True)

    # 1. The fixture and the hash list.
    try:
        verifier = fetch_blocks.check_fixture(fixture, fetch_blocks.Pins.load())
    except fetch_blocks.FetchError as error:
        raise ReplayError(f"fixture check: {error}") from None
    heights = [b["height"] for b in verifier.blocks]
    if heights != list(range(start + 1, end + 1)):
        raise ReplayError(f"the fixture holds heights {heights[0]} to {heights[-1]}, not {start + 1} to {end}")
    kept = [display(headers.hash(h)) for h in heights]
    if [b["hash"] for b in verifier.blocks] != kept:
        raise ReplayError("the fixture's blocks are not the blocks of the pass")
    listing = "".join(f"{h} {value}\n" for h, value in zip(heights, kept))
    committed = hashes / name / "hashes.txt"
    if write_hashes:
        committed.parent.mkdir(parents=True, exist_ok=True)
        committed.write_text(listing)
        (committed.parent / "SHA256SUMS").write_text(f"{hashlib.sha256(listing.encode()).hexdigest()}  hashes.txt\n")
    elif committed.read_text() != listing:
        raise ReplayError(f"the blocks differ from the committed list {committed}")
    blocks = Path(fixture) / fetch_blocks.BLOCKS_FILE
    log(f"range {name}: heights {start + 1} to {end}, {len(heights)} blocks, {sum(b['auth'] == 'pinned' for b in verifier.blocks)} pinned")

    # 2. The snapshot.
    manifest = state["snapshots"][str(start)]
    snapshot = state_dir / "snapshots" / manifest["file"]
    if not manifest.get("kept", True) or not snapshot.exists():
        raise ReplayError(f"the snapshot at {start} is not on disk")
    snapshot_sha256 = file_sha256(snapshot)
    if (snapshot_sha256, snapshot.stat().st_size) != (manifest["sha256"], manifest["bytes"]):
        raise ReplayError(f"the snapshot at {start} differs from its manifest")
    if manifest["block_hash_display"] != display(headers.hash(start)):
        raise ReplayError("the manifest does not name the block below the range")
    written = state_dir / "snapshots" / f"coins-{start}.json"
    committed_manifest = manifests / written.name
    if json.loads(written.read_text()) != {k: v for k, v in manifest.items() if k not in ("file", "kept")}:
        raise ReplayError(f"{written} differs from the pass's state")
    if committed_manifest.exists() and committed_manifest.read_bytes() != written.read_bytes():
        raise ReplayError(f"the snapshot manifest of the pass differs from the committed {committed_manifest}")

    # 3. block.check on every block.
    checks = [{**block_request(raw, mode="allow_witness", pow=True), "id": str(h)}
              for h, raw in fetch_blocks.read_blocks(blocks)]
    began = time.monotonic()
    ours = replay_blocks.run_stream(oracle, checks, None)
    check_seconds = time.monotonic() - began
    core = replay_blocks.run_stream(harness, checks, None)
    for h, a, b in zip(heights, ours, core):
        if not a.get("ok", {}).get("valid") or not b.get("ok", {}).get("valid"):
            raise ReplayError(f"block.check at height {h}: oracle {json.dumps(a)[:200]}, Core {json.dumps(b)[:200]}")
    log(f"range {name}: block.check accepts every block in both programs; the oracle took {check_seconds:.0f} seconds")

    # 4. The range request.
    floor = max(0, start - core_pass.PERIOD - 260)
    boundary = start - ((start + 1) % core_pass.PERIOD)
    if boundary >= 0 and core_pass.CSV_START <= headers.median_time(boundary) < core_pass.CSV_TIMEOUT:
        raise ReplayError("the range starts inside the CSV window, which the oracle does not model")
    chain = [{k: v for k, v in headers.entry(h).items() if k != "version"} for h in range(start, floor - 1, -1)]
    request = {"id": f"range-{name}", "op": "block.validate", "mode": "allow_witness", "check_pow": True,
               "check_merkle_root": True, "adjusted_time": validate.ADJUSTED_TIME, "chain": chain,
               "bip34_ancestor_hex": headers.hash(core_pass.BIP34_HEIGHT).hex() if start >= core_pass.BIP34_HEIGHT else None,
               "coins_file": str(snapshot.resolve()), "blocks_file": str(blocks.resolve())}
    (output / "range-request.json").write_text(json.dumps(request) + "\n")
    with tempfile.TemporaryDirectory(dir=output) as db:
        harness_request = {**request, "coins_db": db, "coins_db_cache_mb": cache_mb}
        core_answer, core_seconds = replay_blocks.run(harness, harness_request, output / "range-core-response.json", None)
    log(f"range {name}: Core took {core_seconds:.0f} seconds")
    ours_answer, oracle_seconds = replay_blocks.run(oracle, request, output / "range-oracle-response.json", None)
    log(f"range {name}: the oracle took {oracle_seconds:.0f} seconds")

    # 5. Agreement under section 3.4.
    if "ok" in core_answer:
        core_answer = {**core_answer, "ok": {k: v for k, v in core_answer["ok"].items() if not k.startswith("coins_db_")}}
    failure = validate.compare(request, ours_answer, core_answer)
    if failure:
        raise ReplayError(f"range {name}: {failure[1]}")
    ok = ours_answer["ok"]
    if [r["hash_display"] for r in ok["blocks"] if r["valid"]] != kept or len(ok["blocks"]) != len(kept):
        raise ReplayError(f"range {name}: the programs did not accept every block")
    if (ok["start_set_digest_hex"], ok["start_set_coins"]) != (manifest["set_digest_hex"], manifest["coins"]):
        raise ReplayError(f"range {name}: the start is not the manifest's")
    end_digest = state["digests"][str(end)]
    for field in ("set_digest_hex", "set_coins", "set_value"):
        if ok[field] != end_digest[field]:
            raise ReplayError(f"range {name}: the end has {field} {ok[field]!r}, and the pass has {end_digest[field]!r}")
    if strip(ok["blocks"]) != strip(pass_records(state_dir, start + 1, end)):
        raise ReplayError(f"range {name}: the block records differ from those of the pass")
    log(f"range {name}: agrees: from {manifest['coins']} coins to {ok['set_coins']} coins, end digest {ok['set_digest_hex']}")

    summary = {
        "range": name, "first": start + 1, "last": end, "blocks": len(kept),
        "blocks_sha256": file_sha256(blocks), "blocks_bytes": blocks.stat().st_size,
        "pinned": sum(b["auth"] == "pinned" for b in verifier.blocks),
        "snapshot": {k: manifest[k] for k in ("height", "block_hash_display", "coins", "set_digest_hex", "bytes", "sha256")},
        "start_set_digest_hex": ok["start_set_digest_hex"], "start_set_coins": ok["start_set_coins"],
        "set_digest_hex": ok["set_digest_hex"], "set_coins": ok["set_coins"], "set_value": ok["set_value"],
        "spent": sum(r["spent"] for r in ok["blocks"]), "created": sum(r["created"] for r in ok["blocks"]),
        "block_check_oracle_seconds": round(check_seconds), "core_seconds": round(core_seconds),
        "oracle_seconds": round(oracle_seconds), "request_sha256": file_sha256(output / "range-request.json"),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--range", required=True, choices=sorted(set(core_pass.RANGES) - {"S"}))
    parser.add_argument("--pass", dest="state", required=True, metavar="DIR")
    parser.add_argument("--fixture", required=True, metavar="DIR")
    parser.add_argument("--output", required=True, metavar="DIR")
    parser.add_argument("--write-hashes", action="store_true")
    parser.add_argument("--cache-mb", type=int, default=2048, metavar="MB")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    args = parser.parse_args(argv)
    try:
        summary = run_range(args.range, Path(args.state), Path(args.fixture), Path(args.output), args.oracle,
                            args.harness, args.write_hashes, args.cache_mb)
    except (ReplayError, core_pass.PassError) as error:
        print(f"FAIL: {error}")
        return 1
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
