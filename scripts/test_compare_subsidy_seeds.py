#!/usr/bin/env python3
"""Self-test of scripts/compare_subsidy_seeds.py: the run must be able to fail.

Usage: python3 -I scripts/test_compare_subsidy_seeds.py <dogelib-oracle>

A wrapper stands in for the Core harness. It sends each request to the
oracle and gives the response the form of the harness. The test needs no
Core build. It runs 65,536 seeds in each case:

- control: the wrapper changes nothing else, and the run must pass.
- value: the wrapper adds one coin to one subsidy, and the run must fail.
- crash: the wrapper answers every request and ends with status 7, and the run must fail.
- oracle on both sides: the run must fail before it sends a request.
- error: the wrapper turns one response into an error, and the run must fail.
"""

import json
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "compare_subsidy_seeds.py"


def wrap(mode: str, oracle: str, args: list[str]) -> int:
    name = json.loads(subprocess.run([oracle, "--version"], capture_output=True, text=True, check=True).stdout)["format"]
    if args == ["--version"]:
        print(json.dumps({"format": name + "-core-projection"}))
        return 0
    changed = False
    for line in sys.stdin:
        response = json.loads(subprocess.run([oracle], input=line, capture_output=True, text=True, check=True).stdout)
        ok = response["ok"]
        del ok["redraws"]
        ok["boost_version"] = "1.70.0"
        if mode == "value" and not changed:
            ok["subsidies"][5] = str(int(ok["subsidies"][5]) + 100000000)
        if mode == "error" and not changed:
            response = {"id": response["id"], "error": {"kind": "subsidy", "reason": "fuel_exhausted", "index": 0}}
        changed = True
        print(json.dumps(response), flush=True)
    return 7 if mode == "crash" else 0


def main() -> int:
    if len(sys.argv) >= 4 and sys.argv[1] == "--wrap":
        return wrap(sys.argv[2], sys.argv[3], sys.argv[4:])
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    oracle = os.path.abspath(sys.argv[1])
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        cases = [("control", 0), ("value", 1), ("crash", 1), ("error", 1)]
        for mode, expected in cases:
            wrapper = pathlib.Path(tmp) / f"harness-{mode}"
            wrapper.write_text(f'#!/bin/sh\nexec "{sys.executable}" -I "{__file__}" --wrap {mode} "{oracle}" "$@"\n')
            wrapper.chmod(0o755)
            result = subprocess.run([sys.executable, "-I", str(SCRIPT), "--jobs", "1", "--count", "65536",
                                     oracle, str(wrapper)], capture_output=True, text=True)
            passed = result.returncode == expected and ("PASS" in result.stdout) == (expected == 0)
            print(f"{'ok  ' if passed else 'FAIL'} {mode}: exit {result.returncode}")
            if not passed:
                failures += 1
                print(result.stdout[-1000:] + result.stderr[-1000:])
        result = subprocess.run([sys.executable, "-I", str(SCRIPT), "--jobs", "1", "--count", "65536", oracle, oracle],
                                capture_output=True, text=True)
        passed = result.returncode == 1 and "FAIL VERSION" in result.stdout
        print(f"{'ok  ' if passed else 'FAIL'} oracle on both sides: exit {result.returncode}")
        failures += 0 if passed else 1
    print("PASS" if failures == 0 else f"FAIL: {failures} failures")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
