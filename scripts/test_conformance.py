#!/usr/bin/env python3
"""Self-test of scripts/check_range_results.py on the committed expected results.

Usage:
  python3 -I scripts/test_conformance.py

For each committed `tests/conformance/ranges/<range>/expected.jsonl`, the checker must pass on
the file itself and on a copy with other key orders and white space. On a copy of the results of
the short range, each planted fault below must fail with its status and its message. The test
runs the checker as a separate program, as a user runs it, and needs no other program.

Two results files that agree, but whose block records do not cover the heights of their start
line, must fail with status 2: a file with no block record, and a file without its last record.

The wrapper `scripts/range_results.py` and the comparison of `scripts/conformance.py` run a made
responder program on three made blocks. Both must accept a response with one record for each
block, and refuse a response with no record, a response without the last record, and one with
the records in another order.

The committed `tests/conformance/release.json` must pass the checks of
`scripts/conformance.py`, and each planted fault of a copy must fail them.
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import conformance  # noqa: E402
import range_results  # noqa: E402

CHECKER = ROOT / "scripts/check_range_results.py"
RANGES = ROOT / "tests/conformance/ranges"
BASE = RANGES / "short/expected.jsonl"
FAILURES = []


def run(results: Path, expected: Path) -> tuple[int, str]:
    done = subprocess.run([sys.executable, "-I", str(CHECKER), str(results), str(expected)],
                          capture_output=True, text=True)
    return done.returncode, done.stdout + done.stderr


def check(condition: bool, message: str) -> None:
    if not condition:
        FAILURES.append(message)


def read(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines()]


def write(path: Path, lines: list[dict], **dumps) -> Path:
    path.write_text("".join(json.dumps(line, **dumps) + "\n" for line in lines))
    return path


def planted(base: list[dict]) -> list[tuple[str, list[dict] | str, int, str]]:
    """Each fault: a name, the lines or the text of the file, the status and a part of the message."""
    middle = len(base) // 2
    cases = []

    def change(name, status, message, edit):
        lines = json.loads(json.dumps(base))
        edit(lines)
        cases.append((name, lines, status, message))

    def reject(lines):
        lines[middle].update(valid=False, reject_reason="bad-txns-in-belowout", changes_digest_hex=None,
                             spent=None, created=None)

    def flip(value: str) -> str:
        return ("0" if value[0] != "0" else "1") + value[1:]

    change("wrong verdict", 1, "valid is False", reject)
    change("wrong digest of the changes", 1, "changes_digest_hex",
           lambda lines: lines[middle].update(changes_digest_hex=flip(lines[middle]["changes_digest_hex"])))
    change("wrong number of spent coins", 1, "spent is", lambda lines: lines[middle].update(spent=lines[middle]["spent"] + 1))
    change("wrong number of created coins", 1, "created is",
           lambda lines: lines[middle].update(created=lines[middle]["created"] + 1))
    change("wrong start digest", 1, "start_set_digest_hex",
           lambda lines: lines[0].update(start_set_digest_hex=flip(lines[0]["start_set_digest_hex"])))
    change("wrong number of start coins", 1, "start_set_coins",
           lambda lines: lines[0].update(start_set_coins=lines[0]["start_set_coins"] + 1))
    change("wrong end digest", 1, "end_set_digest_hex",
           lambda lines: lines[-1].update(end_set_digest_hex=flip(lines[-1]["end_set_digest_hex"])))
    change("wrong number of end coins", 1, "end_set_coins",
           lambda lines: lines[-1].update(end_set_coins=lines[-1]["end_set_coins"] - 1))
    change("wrong request", 1, "request_sha256",
           lambda lines: lines[0].update(request_sha256=flip(lines[0]["request_sha256"])))
    change("wrong blocks", 1, "blocks_sha256", lambda lines: lines[0].update(blocks_sha256=flip(lines[0]["blocks_sha256"])))
    change("wrong range", 1, "range", lambda lines: lines[0].update(range="other"))
    change("missing block", 1, "missing block", lambda lines: lines.pop(middle))
    change("missing first block", 1, "missing block", lambda lines: lines.pop(1))
    change("missing last block", 1, "missing block", lambda lines: lines.pop(-2))
    change("added block", 1, "added block",
           lambda lines: lines.insert(middle, {**lines[middle], "hash_display": flip(lines[middle]["hash_display"])}))
    change("added block at the end", 1, "added block",
           lambda lines: lines.insert(-1, {**lines[-2], "hash_display": flip(lines[-2]["hash_display"])}))
    change("two blocks swapped", 1, "block record",
           lambda lines: lines.__setitem__(slice(middle, middle + 2), [lines[middle + 1], lines[middle]]))
    change("a block twice", 1, "added block", lambda lines: lines.insert(middle, lines[middle]))
    change("an extra key", 2, "keys of a block line", lambda lines: lines[middle].update(dos=0))
    change("a missing key", 2, "keys of a start line", lambda lines: lines[0].pop("blocks_sha256"))
    change("no end line", 2, "keys of", lambda lines: lines.pop())
    change("other format", 2, "format", lambda lines: lines[0].update(format="dogelib-range-results/2"))
    change("a digest in upper case", 2, "malformed end line",
           lambda lines: lines[-1].update(end_set_digest_hex=lines[-1]["end_set_digest_hex"].upper()))
    change("an accepted block without changes", 2, "lacks its changes", lambda lines: lines[middle].update(spent=None))
    change("a rejected block with changes", 2, "has changes",
           lambda lines: lines[middle].update(valid=False, reject_reason="bad-blk-sigops"))
    change("a count as a string", 2, "start_set_coins", lambda lines: lines[0].update(start_set_coins="1"))
    text = "".join(json.dumps(line) + "\n" for line in base)
    cases.append(("a line that is not JSON", text.replace("\n", "\n{\n", 1), 2, "is not JSON"))
    cases.append(("no newline at the end", text[:-1], 2, "newline"))
    cases.append(("an empty line", text.replace("\n", "\n\n", 1), 2, "is not JSON"))
    cases.append(("an empty file", "", 2, "newline"))
    return cases


def release_faults(release: dict) -> list[tuple[str, dict]]:
    """Each fault of the release file: a name and the changed copy."""
    cases = []

    def change(name, edit):
        copy = json.loads(json.dumps(release))
        edit(copy)
        cases.append((name, copy))

    change("other format", lambda r: r.update(format="dogelib-block-assets/1"))
    change("a tag with a slash", lambda r: r.update(tag="a/b"))
    change("a missing range", lambda r: r["ranges"].pop(1))
    change("two ranges swapped", lambda r: r["ranges"].__setitem__(slice(0, 2), r["ranges"][1::-1]))
    change("an added range", lambda r: r["ranges"].append({**r["ranges"][-1], "name": "G2"}))
    change("other heights", lambda r: r["ranges"][0].update(first=r["ranges"][0]["first"] + 1))
    change("other number of blocks", lambda r: r["ranges"][0].update(blocks=r["ranges"][0]["blocks"] - 1))
    change("a missing request", lambda r: r["ranges"][0]["files"].pop(conformance.REQUEST_FILE))
    change("a malformed SHA-256", lambda r: r["ranges"][0]["files"]["blocks.bin"].update(sha256="00"))
    change("an asset in a directory", lambda r: r["ranges"][0]["files"]["blocks.bin"].update(asset="../x"))
    change("a negative size", lambda r: r["ranges"][0]["files"]["blocks.bin"].update(bytes=-1))
    return cases


RESPONDER = """#!/usr/bin/env python3
import json, sys
MODE, ORACLE = %r, %r
request = json.loads(sys.stdin.readline())
heights = []
with open(request["blocks_file"], "rb") as stream:
    while head := stream.read(8):
        heights.append(int.from_bytes(head[:4], "little"))
        stream.seek(int.from_bytes(head[4:], "little"), 1)
if MODE == "empty":
    heights = []
elif MODE == "truncated":
    heights = heights[:-1]
elif MODE == "reordered":
    heights = heights[::-1]
blocks = [{"height": h, "hash_hex": "%%064x" %% h, "hash_display": "%%064x" %% h, "valid": True,
           "reject_reason": None, "dos": None, "reject_code": None, "changes_digest_hex": "11" * 32,
           "spent": 0, "created": 1, "set_digest_hex": None, "set_value": None} for h in heights]
if ORACLE:
    blocks = [{**block, "diagnostic": None} for block in blocks]
print(json.dumps({"id": request["id"], "ok": {"blocks": blocks, "out_of_domain_at": None,
                                               "set_digest_hex": "22" * 32, "set_coins": len(blocks),
                                               "set_value": "0"}}))
"""
MADE_HEIGHTS = (1001, 1002, 1003)


def responder(scratch: Path, mode: str, oracle: bool = False) -> str:
    """A made program that answers a block.validate request with the records of `mode`, in the
    form of the oracle or of the Core harness. The full comparison accepts each form."""
    path = scratch / f"responder-{mode}-{'oracle' if oracle else 'core'}.py"
    path.write_text(RESPONDER % (mode, oracle))
    path.chmod(0o755)
    return str(path)


def made_range(directory: Path) -> tuple[Path, Path]:
    """A range directory with a range request and a blocks file of three made blocks."""
    (directory / "fixture").mkdir(parents=True, exist_ok=True)
    request = directory / conformance.REQUEST_FILE
    request.write_text(json.dumps({"op": "block.validate", "coins": []}))
    blocks = directory / "fixture" / "blocks.bin"
    blocks.write_bytes(b"".join(h.to_bytes(4, "little") + (1).to_bytes(4, "little") + b"\0" for h in MADE_HEIGHTS))
    return request, blocks


def test_incomplete(scratch: Path) -> None:
    """Results that agree with each other but do not cover their heights, then the wrapper and the comparison."""
    base = read(BASE)
    for name, lines in (("no block record", [base[0], base[-1]]), ("no last record", base[:-2] + base[-1:])):
        path = write(scratch / "incomplete.jsonl", lines)
        status, output = run(path, path)
        check(status == 2 and "do not cover" in output, f"two files with {name}: status {status}, output {output.strip()!r}")
        print(f"two files with {name}: status {status}")
    request, blocks = made_range(scratch / "made")
    lines = range_results.results("made", request, blocks, [responder(scratch, "full")])
    check([line["height"] for line in lines[1:-1]] == list(MADE_HEIGHTS), "the wrapper does not accept a full response")
    out = conformance.compare("made", scratch / "made", responder(scratch, "full", oracle=True),
                              responder(scratch, "full"), None, False, log=lambda _: None)
    check(out["blocks"] == len(MADE_HEIGHTS), "the comparison does not accept two full responses")
    for mode in ("empty", "truncated", "reordered"):
        try:
            range_results.results("made", request, blocks, [responder(scratch, mode)])
            check(False, f"the wrapper accepts a response with the records {mode}")
        except range_results.ResultsError as error:
            check("block records" in str(error), f"the wrapper refuses a {mode} response with {error}")
            print(f"wrapper, response {mode}: refused")
        try:
            conformance.compare("made", scratch / "made", responder(scratch, mode, oracle=True),
                                responder(scratch, mode), None, False, log=lambda _: None)
            check(False, f"the comparison accepts two responses with the records {mode}")
        except (range_results.ResultsError, conformance.CorpusError) as error:
            check("block records" in str(error), f"the comparison refuses a {mode} response with {error}")
            print(f"comparison, two responses {mode}: refused")


def test_release(scratch: Path) -> None:
    release = conformance.load_release()
    check(release["tag"].startswith("conformance-corpus-"), f"the tag {release['tag']} does not name the corpus")
    for name, copy in release_faults(release):
        path = scratch / "release.json"
        path.write_text(json.dumps(copy))
        try:
            conformance.load_release(path)
            check(False, f"release.json with {name} passes")
        except conformance.CorpusError:
            print(f"release.json with {name}: fails")


def main() -> int:
    files = sorted(RANGES.glob("*/expected.jsonl"))
    check(BASE in files, f"{BASE} is not committed")
    with tempfile.TemporaryDirectory() as scratch:
        scratch = Path(scratch)
        test_release(scratch)
        test_incomplete(scratch)
        for path in files:
            status, output = run(path, path)
            check(status == 0 and output.startswith("PASS"), f"{path}: the checker does not pass on the file itself: {output}")
            lines = read(path)
            check(lines[0]["range"] == path.parent.name, f"{path}: the range is {lines[0]['range']!r}")
            reordered = write(scratch / "reordered.jsonl", [dict(reversed(list(line.items()))) for line in lines], indent=None)
            status, output = run(reordered, path)
            check(status == 0, f"{path}: the checker fails on other key orders and white space: {output}")
        if len(files) > 1:
            status, output = run(files[0], files[1])
            check(status == 1, f"the results of {files[0].parent.name} pass against those of {files[1].parent.name}")
        if BASE.is_file():
            base = read(BASE)
            for name, content, want, part in planted(base):
                path = scratch / "planted.jsonl"
                if isinstance(content, str):
                    path.write_text(content)
                else:
                    write(path, content)
                status, output = run(path, BASE)
                check(status == want and part in output,
                      f"{name}: status {status} (expected {want}), output {output.strip()!r} (expected {part!r})")
                print(f"{name}: status {status}")
    if FAILURES:
        for failure in FAILURES:
            print(f"FAIL: {failure}")
        return 1
    print(f"PASS: {len(files)} committed results files and release.json; every planted fault fails")
    return 0


if __name__ == "__main__":
    sys.exit(main())
