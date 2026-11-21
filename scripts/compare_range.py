#!/usr/bin/env python3
"""Compare the oracle and Core on a range of design record 0011 with its restricted coins (stage 3).

Usage:
  python3 -I scripts/compare_range.py --range-dir DIR [--request FILE] --blocks FIXTURE <dogelib-oracle> <core-oracle>

DIR holds `expected.json` of one range, which scripts/restrict_coins.py wrote from the recorded
run of scripts/run_range.py, and `SHA256SUMS`. FILE is the *range request* of
scripts/restrict_coins.py: the request with the restricted coins and without its blocks. It is
`DIR/request.json` by default, and scripts/restrict_coins.py writes it to its output directory.
`SHA256SUMS` gives the SHA-256 of both files. FIXTURE is the `dogelib-blocks/1` fixture of the
range's blocks. The script works in four steps:

1. It checks both files against `SHA256SUMS`, and the fixture as `scripts/fetch_blocks.py --check` does. The fixture
   must hold the heights of `expected.json`, and its first block must name the hash of the
   expected start as its previous block.
2. Both programs run the request with the coins in memory and the blocks through `blocks_file`.
3. They must agree as the full comparison requires (`compare` of scripts/oracle_block_validate.py):
   every block record, the digest of each block's coin changes, and each digest and total value
   of the set. The set is the restricted coins and their changes, not the coin set of mainnet.
4. Both programs must accept every block. The block records without `set_digest_hex` and
   `set_value` must have the SHA-256 of `expected.json`: the records of the recorded run from the
   whole snapshot. So the restricted coins give the verdicts and coin changes of that run.
"""

import argparse
import hashlib
import json
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks
import oracle_block_validate as validate
import replay_blocks

NOT_COMPARED = ("diagnostic", "set_digest_hex", "set_value")


class RangeError(Exception):
    """A changed input or a disagreement."""


def records_sha256(records: list[dict]) -> str:
    """The SHA-256 of the block records without the fields of the whole set, as canonical JSON."""
    stripped = [{k: v for k, v in r.items() if k not in NOT_COMPARED} for r in records]
    return hashlib.sha256(json.dumps(stripped, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while chunk := stream.read(1 << 24):
            digest.update(chunk)
    return digest.hexdigest()


def check_sums(range_dir: Path, request_file: Path) -> None:
    """`SHA256SUMS` of DIR lists `expected.json` and `request.json`, and both files have its SHA-256."""
    listed = {}
    for line in (range_dir / "SHA256SUMS").read_text().splitlines():
        digest, separator, name = line.partition("  ")
        if not separator or name in listed:
            raise RangeError(f"{range_dir / 'SHA256SUMS'}: malformed line {line!r}")
        listed[name] = digest
    if sorted(listed) != ["expected.json", "request.json"]:
        raise RangeError(f"{range_dir / 'SHA256SUMS'}: lists {sorted(listed)}, not expected.json and request.json")
    for name, path in (("expected.json", range_dir / "expected.json"), ("request.json", request_file)):
        if file_sha256(path) != listed[name]:
            raise RangeError(f"{path}: SHA256SUMS mismatch")


def compare_range(range_dir: Path, fixture: Path, oracle: str, harness: str, log=print,
                  request_file: Path | None = None) -> dict:
    request_file = request_file or range_dir / "request.json"
    check_sums(range_dir, request_file)
    request = json.loads(request_file.read_text())
    expected = json.loads((range_dir / "expected.json").read_text())
    try:
        verifier = fetch_blocks.check_fixture(fixture, fetch_blocks.Pins.load())
    except fetch_blocks.FetchError as error:
        raise RangeError(f"fixture check: {error}") from None
    heights = [b["height"] for b in verifier.blocks]
    if heights != list(range(expected["first"], expected["last"] + 1)):
        raise RangeError(f"the fixture holds heights {heights[0]} to {heights[-1]}, not {expected['first']} to {expected['last']}")
    blocks = fixture / fetch_blocks.BLOCKS_FILE
    first = next(fetch_blocks.read_blocks(blocks))[1]
    if first[4:36][::-1].hex() != expected["start_block_hash_display"]:
        raise RangeError("the first block does not name the block of the expected start")

    req = {**request, "id": "range", "blocks_file": str(blocks.resolve())}
    with tempfile.TemporaryDirectory() as scratch:
        began = time.monotonic()
        ours, _ = replay_blocks.run(oracle, req, Path(scratch) / "oracle.json", None)
        oracle_seconds = time.monotonic() - began
        began = time.monotonic()
        core, _ = replay_blocks.run(harness, req, Path(scratch) / "core.json", None)
        core_seconds = time.monotonic() - began
    failure = validate.compare(req, ours, core)
    if failure:
        raise RangeError(failure[1])
    if "ok" not in ours:
        raise RangeError(f"both programs refused the request: {json.dumps(ours.get('error'))[:300]}")
    ok = ours["ok"]
    if len(ok["blocks"]) != len(heights) or not all(r["valid"] for r in ok["blocks"]):
        raise RangeError("the programs did not accept every block")
    got = records_sha256(ok["blocks"])
    if got != expected["records_sha256"]:
        raise RangeError(f"the block records have the SHA-256 {got}, and the recorded run {expected['records_sha256']}")
    log(f"range: {len(heights)} blocks, heights {heights[0]} to {heights[-1]}; both programs accept every block and agree; "
        f"the records are those of the recorded run")
    log(f"range: the restricted set ends with {ok['set_coins']} coins, digest {ok['set_digest_hex']}")
    log(f"range: the oracle took {oracle_seconds:.0f} seconds, Core {core_seconds:.0f} seconds")
    return {"set_coins": ok["set_coins"], "set_digest_hex": ok["set_digest_hex"],
            "oracle_seconds": oracle_seconds, "core_seconds": core_seconds}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--range-dir", required=True, metavar="DIR")
    parser.add_argument("--request", metavar="FILE")
    parser.add_argument("--blocks", required=True, metavar="FIXTURE")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    args = parser.parse_args(argv)
    try:
        compare_range(Path(args.range_dir), Path(args.blocks), args.oracle, args.harness,
                      request_file=Path(args.request) if args.request else None)
    except (OSError, ValueError, KeyError, RangeError, replay_blocks.ReplayError) as error:
        print(f"FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
