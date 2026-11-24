#!/usr/bin/env python3
"""Self-test of scripts/check_range_results.py on the committed expected results.

Usage:
  python3 -I scripts/test_check_range_results.py

For each committed `tests/conformance/ranges/<range>/expected.jsonl`, the checker must pass on
the file itself and on a copy with other key orders and white space. On a copy of the results of
the short range, each planted fault below must fail with its status and its message. The test
runs the checker as a separate program, as a user runs it, and needs no other program.

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
