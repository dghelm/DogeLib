#!/usr/bin/env python3
"""Compare a dogelib-range-results/1 file with the expected results of its range.

Usage:
  python3 -I scripts/check_range_results.py RESULTS EXPECTED

RESULTS is the results file of a program under test. EXPECTED is the committed expected results
of the same range, `tests/conformance/ranges/<range>/expected.jsonl`. docs/conformance.md
defines the format.

The check reads both files strictly. Each must be a start line, one line for each block record
and an end line, each a JSON object with exactly the keys of its kind. The check then requires
that RESULTS has the values of EXPECTED: every field of the start line, then each block record in
order, then every field of the end line. It compares values, not bytes, so the order of the keys
and the white space of a line do not matter. Last, each file must have one block record for each
height from `first` to `last` of its start line, in order.

The script prints `PASS` and exits with status 0 when the files agree. Otherwise it prints the
first difference and exits with status 1. A file that does not read is status 2. The script uses
only the Python standard library and runs no other program.
"""

import json
import sys

FORMAT = "dogelib-range-results/1"
HEAD_KEYS = ("format", "range", "first", "last", "request_sha256", "blocks_sha256",
             "start_set_digest_hex", "start_set_coins")
BLOCK_KEYS = ("height", "hash_display", "valid", "reject_reason", "changes_digest_hex", "spent", "created")
END_KEYS = ("end_set_digest_hex", "end_set_coins")


class Malformed(Exception):
    """A file that is not a dogelib-range-results/1 file."""


def is_hex(value, size: int) -> bool:
    return isinstance(value, str) and len(value) == 2 * size and all(c in "0123456789abcdef" for c in value)


def is_count(value) -> bool:
    return type(value) is int and value >= 0


def check_head(line: dict) -> None:
    if line["format"] != FORMAT:
        raise Malformed(f"the format is not {FORMAT}")
    if not isinstance(line["range"], str) or not line["range"]:
        raise Malformed("the range is not a name")
    if not (is_count(line["first"]) and is_count(line["last"]) and line["first"] <= line["last"]):
        raise Malformed("first and last are not heights in order")
    for key in ("request_sha256", "blocks_sha256", "start_set_digest_hex"):
        if not is_hex(line[key], 32):
            raise Malformed(f"{key} is not 64 lowercase hexadecimal digits")
    if not is_count(line["start_set_coins"]):
        raise Malformed("start_set_coins is not a count")


def check_block(line: dict, number: int) -> None:
    where = f"line {number}"
    if not is_count(line["height"]) or not is_hex(line["hash_display"], 32) or type(line["valid"]) is not bool:
        raise Malformed(f"{where}: malformed height, hash_display or valid")
    if line["valid"]:
        if line["reject_reason"] is not None:
            raise Malformed(f"{where}: an accepted block has a reject_reason")
        if not (is_hex(line["changes_digest_hex"], 32) and is_count(line["spent"]) and is_count(line["created"])):
            raise Malformed(f"{where}: an accepted block lacks its changes_digest_hex, spent or created")
    else:
        if not isinstance(line["reject_reason"], str) or not line["reject_reason"]:
            raise Malformed(f"{where}: a rejected block has no reject_reason")
        if any(line[key] is not None for key in ("changes_digest_hex", "spent", "created")):
            raise Malformed(f"{where}: a rejected block has changes")


def check_end(line: dict) -> None:
    if not is_hex(line["end_set_digest_hex"], 32) or not is_count(line["end_set_coins"]):
        raise Malformed("malformed end line")


def read_results(path: str) -> tuple[dict, list[dict], dict]:
    """The start line, the block lines and the end line of a results file."""
    try:
        with open(path, "rb") as stream:
            text = stream.read().decode("utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise Malformed(f"cannot read: {type(error).__name__}") from None
    if not text.endswith("\n"):
        raise Malformed("the file does not end with a newline")
    lines = []
    for number, raw in enumerate(text[:-1].split("\n"), 1):
        try:
            value = json.loads(raw)
        except ValueError:
            raise Malformed(f"line {number} is not JSON") from None
        if not isinstance(value, dict):
            raise Malformed(f"line {number} is not a JSON object")
        lines.append(value)
    if len(lines) < 2:
        raise Malformed("the file has no start line and end line")
    shapes = [(1, lines[0], HEAD_KEYS, "start")] + [(n, line, BLOCK_KEYS, "block") for n, line in
                                                     enumerate(lines[1:-1], 2)] + [(len(lines), lines[-1], END_KEYS, "end")]
    for number, line, keys, kind in shapes:
        if sorted(line) != sorted(keys):
            raise Malformed(f"line {number} does not have the keys of a {kind} line: {sorted(line)}")
    head, blocks, end = lines[0], lines[1:-1], lines[-1]
    check_head(head)
    for number, block in enumerate(blocks, 2):
        check_block(block, number)
    check_end(end)
    return head, blocks, end


def check_complete(parsed) -> None:
    """Require one block record for each height from `first` to `last` of the start line, in order."""
    head, blocks, _ = parsed
    heights = [block["height"] for block in blocks]
    if heights != list(range(head["first"], head["last"] + 1)):
        raise Malformed(f"the {len(heights)} block records do not cover heights {head['first']} to {head['last']} "
                        "once each, in order")


def describe(block: dict) -> str:
    return f"height {block['height']}, hash {block['hash_display']}"


def first_difference(results, expected) -> str | None:
    """The first way in which `results` differs from `expected`, or None."""
    (head, blocks, end), (want_head, want_blocks, want_end) = results, expected
    for key in HEAD_KEYS:
        if head[key] != want_head[key]:
            return f"start line: {key} is {head[key]!r}, expected {want_head[key]!r}"
    for position, (got, want) in enumerate(zip(blocks, want_blocks)):
        if (got["height"], got["hash_display"]) != (want["height"], want["hash_display"]):
            if any((b["height"], b["hash_display"]) == (got["height"], got["hash_display"])
                   for b in want_blocks[position + 1:]):
                return f"block record {position}: missing block ({describe(want)})"
            return f"block record {position}: added block ({describe(got)}), expected {describe(want)}"
        for key in BLOCK_KEYS:
            if got[key] != want[key]:
                return f"block record {position} ({describe(want)}): {key} is {got[key]!r}, expected {want[key]!r}"
    if len(blocks) < len(want_blocks):
        return f"block record {len(blocks)}: missing block ({describe(want_blocks[len(blocks)])})"
    if len(blocks) > len(want_blocks):
        return f"block record {len(want_blocks)}: added block ({describe(blocks[len(want_blocks)])})"
    for key in END_KEYS:
        if end[key] != want_end[key]:
            return f"end line: {key} is {end[key]!r}, expected {want_end[key]!r}"
    return None


def main(argv=None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 2:
        print("usage: check_range_results.py RESULTS EXPECTED", file=sys.stderr)
        return 2
    parsed = []
    for path in argv:
        try:
            parsed.append(read_results(path))
        except Malformed as error:
            print(f"ERROR: {path}: {error}")
            return 2
    difference = first_difference(*parsed)
    if difference is not None:
        print(f"FAIL: {argv[0]}: {difference}")
        return 1
    for path, results in zip(argv, parsed):
        try:
            check_complete(results)
        except Malformed as error:
            print(f"ERROR: {path}: {error}")
            return 2
    head, blocks, _ = parsed[0]
    print(f"PASS: range {head['range']}, heights {head['first']} to {head['last']}, "
          f"{len(blocks)} block records agree with {argv[1]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
