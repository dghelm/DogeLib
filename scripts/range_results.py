#!/usr/bin/env python3
"""Run a range request in a dogelib-oracle/1 program and write a dogelib-range-results/1 file.

Usage:
  python3 -I scripts/range_results.py --range NAME --request FILE --blocks FILE --output FILE
      [--keep DIR] PROGRAM [ARGUMENT ...]

PROGRAM is a program that answers `block.validate` requests of the `dogelib-oracle/1` protocol on
standard input and standard output, such as `build/core-harness/core-oracle` or
`.lake/build/bin/dogelib-oracle`. The format of the corpus is in docs/conformance.md.

The script works in four steps:

1. It reads the range request FILE and the blocks FILE, and computes the SHA-256 of each.
   The request must be a `block.validate` request with `coins`, and without `id`, `blocks_hex`,
   `blocks_file` and `coins_file`. The heights of the blocks must follow each other.
2. It sends PROGRAM the range request with an empty blocks file. The result has no block record,
   and its `set_digest_hex` and `set_coins` are the digest and the number of the coins of the
   request: the start of the results.
3. It sends PROGRAM the range request with the blocks file. The response must have one block
   record for each block of the file, in order. Each block record and the digest and number of
   the coins after the last record go into the results.
4. It writes the results file: one JSON line for the start, one for each block record, and one
   for the end.

With `--keep DIR` it keeps both response lines in DIR, as `start-response.json` and
`range-response.json`. A program that refuses a request, or a response without the fields of the
results, fails the run, and the script writes no results file.

The script uses only the Python standard library, so it runs from a copy of this file alone.
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAT = "dogelib-range-results/1"
REFUSED_KEYS = ("id", "blocks_hex", "blocks_file", "coins_file")


class ResultsError(Exception):
    """A malformed input, a refused request or a malformed response."""


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while chunk := stream.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()


def block_heights(path: Path) -> list[int]:
    """The height of each record of a `dogelib-blocks/1` blocks file, in order."""
    heights = []
    with open(path, "rb") as stream:
        while head := stream.read(8):
            if len(head) != 8:
                raise ResultsError(f"{path}: the file ends inside a record header")
            length = int.from_bytes(head[4:], "little")
            stream.seek(length, os.SEEK_CUR)
            heights.append(int.from_bytes(head[:4], "little"))
        if stream.tell() != path.stat().st_size:
            raise ResultsError(f"{path}: the file ends inside a block")
    if not heights:
        raise ResultsError(f"{path}: the file has no block")
    return heights


def ask(program: list[str], request: dict, keep: Path | None, name: str) -> dict:
    """Send one request to a new process of `program`, and return the `ok` object of its response."""
    line = json.dumps(request, sort_keys=True) + "\n"
    try:
        done = subprocess.run(program, input=line.encode(), stdout=subprocess.PIPE)
    except OSError as error:
        raise ResultsError(f"{program[0]}: {type(error).__name__}") from None
    if keep is not None:
        (keep / f"{name}-response.json").write_bytes(done.stdout)
    if done.returncode != 0:
        raise ResultsError(f"{program[0]} exited with status {done.returncode}")
    lines = done.stdout.decode().splitlines()
    if len(lines) != 1:
        raise ResultsError(f"{program[0]}: {len(lines)} response lines to one request")
    try:
        answer = json.loads(lines[0])
    except ValueError:
        raise ResultsError(f"{program[0]}: the response is not JSON") from None
    if not isinstance(answer, dict) or answer.get("id") != request["id"]:
        raise ResultsError(f"{program[0]}: the response does not have the id of the request")
    if "ok" not in answer:
        raise ResultsError(f"{program[0]} refused the {name} request: {json.dumps(answer.get('error'))[:300]}")
    return answer["ok"]


def set_fields(ok: dict, name: str) -> tuple[str, int]:
    digest, coins = ok.get("set_digest_hex"), ok.get("set_coins")
    if not isinstance(digest, str) or type(coins) is not int:
        raise ResultsError(f"the {name} response has no set_digest_hex or set_coins")
    return digest, coins


def block_line(record: dict) -> dict:
    """The line of one block record, with the fields of dogelib-range-results/1."""
    try:
        line = {"height": record["height"], "hash_display": record["hash_display"], "valid": record["valid"],
                "reject_reason": record["reject_reason"], "changes_digest_hex": record["changes_digest_hex"],
                "spent": record["spent"], "created": record["created"]}
    except (KeyError, TypeError):
        raise ResultsError("a block record lacks a field of the results") from None
    return line


def results(range_name: str, request_file: Path, blocks_file: Path, program: list[str],
            keep: Path | None = None) -> list[dict]:
    """The lines of the results file of one range."""
    try:
        request = json.loads(request_file.read_bytes())
    except (OSError, ValueError) as error:
        raise ResultsError(f"{request_file}: cannot read: {type(error).__name__}") from None
    if not isinstance(request, dict) or request.get("op") != "block.validate" or "coins" not in request:
        raise ResultsError(f"{request_file}: not a block.validate request with coins")
    if any(key in request for key in REFUSED_KEYS):
        raise ResultsError(f"{request_file}: a range request has none of {', '.join(REFUSED_KEYS)}")
    heights = block_heights(blocks_file)
    if heights != list(range(heights[0], heights[-1] + 1)):
        raise ResultsError(f"{blocks_file}: the heights of the blocks do not follow each other")
    head = {"format": FORMAT, "range": range_name, "first": heights[0], "last": heights[-1],
            "request_sha256": file_sha256(request_file), "blocks_sha256": file_sha256(blocks_file)}
    with tempfile.TemporaryDirectory() as scratch:
        empty = Path(scratch) / "empty.bin"
        empty.write_bytes(b"")
        start = ask(program, {**request, "id": "start", "blocks_file": str(empty)}, keep, "start")
    if start.get("blocks") != []:
        raise ResultsError("the start response has a block record")
    head["start_set_digest_hex"], head["start_set_coins"] = set_fields(start, "start")
    ok = ask(program, {**request, "id": "range", "blocks_file": str(blocks_file.resolve())}, keep, "range")
    records = ok.get("blocks")
    if not isinstance(records, list):
        raise ResultsError("the range response has no list of block records")
    lines = [block_line(r) for r in records]
    got = [line["height"] for line in lines]
    if got != heights:
        raise ResultsError(f"the range response has {len(got)} block records, not one for each of the "
                           f"{len(heights)} blocks of {blocks_file} in order")
    end_digest, end_coins = set_fields(ok, "range")
    return [head, *lines,
            {"end_set_digest_hex": end_digest, "end_set_coins": end_coins}]


def results_text(lines: list[dict]) -> str:
    return "".join(json.dumps(line, sort_keys=True, separators=(",", ":")) + "\n" for line in lines)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--range", required=True, metavar="NAME")
    parser.add_argument("--request", required=True, type=Path, metavar="FILE")
    parser.add_argument("--blocks", required=True, type=Path, metavar="FILE")
    parser.add_argument("--output", required=True, type=Path, metavar="FILE")
    parser.add_argument("--keep", type=Path, metavar="DIR")
    parser.add_argument("program", nargs=argparse.REMAINDER, metavar="PROGRAM [ARGUMENT ...]")
    args = parser.parse_args(argv)
    if not args.program:
        parser.error("PROGRAM is required")
    try:
        if args.keep is not None:
            args.keep.mkdir(parents=True, exist_ok=True)
        lines = results(args.range, args.request, args.blocks, args.program, args.keep)
        text = results_text(lines)
        temporary = args.output.with_name(args.output.name + ".tmp")
        temporary.write_text(text)
        os.replace(temporary, args.output)
    except (OSError, ResultsError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(f"wrote {args.output}: {len(lines) - 2} block records, heights {lines[0]['first']} to {lines[0]['last']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
