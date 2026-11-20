#!/usr/bin/env python3
"""Replay mainnet blocks from the genesis block through `block.validate`, in the oracle and in Core.

Usage:
  python3 -I scripts/replay_blocks.py [--last HEIGHT] [--timeout SECONDS] --output DIR
      <dogelib-oracle> <core-oracle> FIXTURE...

Each FIXTURE is a directory of scripts/fetch_blocks.py or scripts/fetch_release_blocks.py, with
`blocks.bin`, `manifest.json` and `SHA256SUMS`. Together, in the order given, the fixtures must
hold the consecutive heights from 0. With `--last HEIGHT` the replay stops after that height.

This is the gate outside CI of design record 0010, section 5, exit condition 1: the replay from
the genesis block to height 145,000, the whole random-reward era. The two programs must accept
every block and agree on each block record, on the digest of each block's coin changes and on
each digest of the whole coin set (docs/oracle.md, "Block validation").

The script works in four steps:

1. It checks each fixture as `scripts/fetch_blocks.py --check` does, without a network
   connection. It then requires that every block has the label `pinned`: the block hash equals a
   value that the repository pins, and the Merkle root of the block's transaction IDs is the root
   of its header. The pinned values of heights 0 to 144,999 are the committed previous-block
   hashes, and the value of height 145,000 is a checkpoint of Core.
2. It writes the blocks of all fixtures to `DIR/blocks.bin`, in the format of the fixtures.
3. It sends each program one request, with `blocks_file` set to that file, the empty chain and
   the empty coin set. Core runs first, because it is faster. Each program reads the file one
   block at a time. The oracle writes each thousandth accepted height to standard error.
4. It compares the two responses with the comparison of scripts/compare_core.py, and requires
   that the accepted hashes are the hashes of the fixtures, at the heights from 0.

It writes the two responses and `summary.json` to DIR. The exit status is 0 only when the two
programs agree and accept every block.

Run the long replay on one core at low priority, and register it in the lane's STATUS.md:

  taskset -c 7 nice -n 19 python3 -I scripts/replay_blocks.py --output build/replay-145000 \\
      .lake/build/bin/dogelib-oracle build/core-harness/core-oracle \\
      build/mainnet-blocks/genesis-10000 build/mainnet-blocks/range-10001-145000
"""

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

# Import the helpers beside this script, including under Python's isolated mode.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fetch_blocks
import oracle_block_validate as validate


class ReplayError(Exception):
    """A failed check of the fixtures, a failed program run or a disagreement."""


def gather(fixtures: list[str], last: int | None, target: Path, pins=None) -> tuple[list[str], str]:
    """Check the fixtures and write their blocks to `target`. Return the block hashes and the SHA-256 of the file."""
    pins = pins or fetch_blocks.Pins.load()
    hashes = []
    digest = hashlib.sha256()
    with open(target, "wb") as stream:
        for fixture in fixtures:
            try:
                verifier = fetch_blocks.check_fixture(fixture, pins)
            except fetch_blocks.FetchError as error:
                raise ReplayError(f"fixture check: {error}") from None
            records = verifier.blocks
            for record, (height, raw) in zip(records, fetch_blocks.read_blocks(Path(fixture) / fetch_blocks.BLOCKS_FILE)):
                if last is not None and len(hashes) > last:
                    break
                if record["height"] != height or height != len(hashes):
                    raise ReplayError(f"{fixture}: height {height} follows height {len(hashes) - 1}")
                if record["auth"] != "pinned":
                    raise ReplayError(f"{fixture}: the block at height {height} has no pinned hash")
                data = height.to_bytes(4, "little") + len(raw).to_bytes(4, "little") + raw
                stream.write(data)
                digest.update(data)
                hashes.append(record["hash"])
    if not hashes:
        raise ReplayError("the fixtures have no block")
    if last is not None and len(hashes) != last + 1:
        raise ReplayError(f"the fixtures end at height {len(hashes) - 1}, below --last {last}")
    return hashes, digest.hexdigest()


def run(program: str, request: dict, response: Path, timeout: float | None) -> tuple[dict, float]:
    """Send one request to `program`, keep its response line in `response`, and return it with the seconds."""
    start = time.monotonic()
    with open(response, "wb") as out:
        try:
            done = subprocess.run([program], input=(json.dumps(request, sort_keys=True) + "\n").encode(),
                                  stdout=out, timeout=timeout)
        except subprocess.TimeoutExpired:
            raise ReplayError(f"{program} did not finish within {timeout} seconds") from None
        except OSError as error:
            raise ReplayError(f"{program}: {type(error).__name__}") from None
    seconds = time.monotonic() - start
    if done.returncode != 0:
        raise ReplayError(f"{program} exited with status {done.returncode}")
    lines = response.read_text().splitlines()
    if len(lines) != 1:
        raise ReplayError(f"{program}: {len(lines)} response lines to one request")
    try:
        answer = json.loads(lines[0])
    except ValueError:
        raise ReplayError(f"{program}: the response is not JSON") from None
    if not isinstance(answer, dict) or answer.get("id") != request["id"]:
        raise ReplayError(f"{program}: the response does not have the id of the request")
    return answer, seconds


def replay(oracle: str, harness: str, fixtures: list[str], output: Path, last: int | None = None,
           timeout: float | None = None, pins=None, log=lambda text: print(text, flush=True)) -> dict:
    """Run the four steps, and return the summary. Raise `ReplayError` on any failure."""
    output.mkdir(parents=True, exist_ok=True)
    blocks = output / fetch_blocks.BLOCKS_FILE
    hashes, sha256 = gather(fixtures, last, blocks, pins)
    log(f"fixtures: heights 0 to {len(hashes) - 1}, every block pinned, {blocks.stat().st_size} bytes, SHA-256 {sha256}")
    request = {**validate.request([], check_pow=True, mode="allow_witness"), "id": "replay", "blocks_file": str(blocks)}
    del request["blocks_hex"]
    validate.EXPECTATIONS[validate.key(request)] = {"error": None, "accepted": hashes}
    core, core_seconds = run(harness, request, output / "core-response.json", timeout)
    log(f"Core: {core_seconds:.0f} seconds")
    ours, oracle_seconds = run(oracle, request, output / "oracle-response.json", timeout)
    log(f"oracle: {oracle_seconds:.0f} seconds")
    failure = validate.compare(request, ours, core)
    if failure:
        raise ReplayError(f"{failure[0]}: {failure[1]}")
    records = ours["ok"]["blocks"]
    if len(records) != len(hashes):
        raise ReplayError(f"{len(records)} block records for {len(hashes)} blocks")
    summary = {
        "first": 0, "last": len(hashes) - 1, "blocks": len(records),
        "blocks_sha256": sha256,
        "last_hash": hashes[-1],
        "spent": sum(record["spent"] for record in records),
        "created": sum(record["created"] for record in records),
        "set_digests": sum(record["set_digest_hex"] is not None for record in records) + 1,
        "set_coins": ours["ok"]["set_coins"],
        "set_digest_hex": ours["ok"]["set_digest_hex"],
        "oracle_seconds": round(oracle_seconds), "core_seconds": round(core_seconds),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--last", type=int, metavar="HEIGHT", help="stop after this height")
    parser.add_argument("--timeout", type=float, metavar="SECONDS", help="for each program run; no limit by default")
    parser.add_argument("--output", required=True, metavar="DIR")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    parser.add_argument("fixtures", nargs="+", metavar="FIXTURE")
    args = parser.parse_args(argv)
    if args.last is not None and args.last < 0:
        parser.error("--last needs a height from 0")
    try:
        summary = replay(args.oracle, args.harness, args.fixtures, Path(args.output), args.last, args.timeout)
    except ReplayError as error:
        print(f"FAIL: {error}")
        return 1
    print(f"block.validate replay: heights 0 to {summary['last']}, {summary['blocks']} blocks accepted by both programs")
    print(f"coin changes: {summary['spent']} spent, {summary['created']} created; "
          f"{summary['set_digests']} digests of the whole set agree")
    print(f"coin set after height {summary['last']}: {summary['set_coins']} coins, digest {summary['set_digest_hex']}")
    print(f"oracle {summary['oracle_seconds']} seconds, Core {summary['core_seconds']} seconds, 0 failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())
