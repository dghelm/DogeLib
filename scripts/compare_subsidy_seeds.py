#!/usr/bin/env python3
"""Compare the random block subsidy of the oracle and of Dogecoin Core on every seed.

Usage: python3 -I scripts/compare_subsidy_seeds.py [--jobs N] [--first SEED] [--count N]
           [--output DIR] <dogelib-oracle> <core-oracle>

Core seeds its generator from seven hexadecimal digits of the previous block
hash (SOURCES.md D104, src/dogecoin.cpp lines 134 to 137), so the random
subsidy has 2^28 seeds. It has two ranges on mainnet: `maxReward` is 999,999
below height 100,000 and 499,999 from 100,000 to 144,999. This script sends
both programs `block.subsidy` requests for every seed at heights 1 and
100,000, and requires equal subsidies. A previous hash carries the seed in
characters 7 to 13 of its display form, and zero digits elsewhere.

The run is exit condition 5 of design record 0010, section 4. It is not part
of CI. A full run sends 2^29 cases in 8,192 requests of 65,536 cases.

The script fails if the programs disagree on any case, if either gives an
error, or if either ends with a nonzero status. It first requires the format
name of the oracle from the first program and the name of the Core projection
from the second, and each response must have the fields of its program. So
the oracle cannot stand in for the harness. An oracle error includes `fuel_exhausted`, so a pass shows that the
fuel of the oracle suffices on every seed. The summary, also written to
DIR/summary.json, records the largest number of redraws that the oracle
reports, and the Boost release of the harness.
"""

import argparse
import json
import multiprocessing
import pathlib
import subprocess
import sys
import time

ORACLE_FORMAT = "dogelib-oracle/1"
SEEDS = 1 << 28
BATCH = 65536
# One height in each random range (D104, line 138).
HEIGHTS = (1, 100000)
MAX_REPORTS = 10


def prev_hash_hex(seed: int) -> str:
    """Internal-order bytes of the hash whose display digits 7 to 13 are `seed`."""
    display = "0" * 7 + f"{seed:07x}" + "0" * 50
    return bytes.fromhex(display)[::-1].hex()


def ask(process: subprocess.Popen, request: dict) -> dict:
    process.stdin.write(json.dumps(request, separators=(",", ":")) + "\n")
    process.stdin.flush()
    line = process.stdout.readline()
    if not line:
        raise RuntimeError(f"{process.args[0]} ended with status {process.wait()}")
    return json.loads(line)


def run_range(job: tuple[str, str, int, int]) -> dict:
    """Compare the seeds `first` to `first + count - 1` at both heights."""
    oracle, harness, first, count = job
    result = {"cases": 0, "failures": [], "redraws": {str(h): {} for h in HEIGHTS}, "boost": []}
    programs = [subprocess.Popen([program], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
                for program in (oracle, harness)]
    try:
        for start in range(first, first + count, BATCH):
            seeds = range(start, min(start + BATCH, first + count))
            for height in HEIGHTS:
                request = {"id": f"{height}:{start}", "op": "block.subsidy",
                           "cases": [{"height": height, "prev_hash_hex": prev_hash_hex(seed)} for seed in seeds]}
                ours, core = (ask(program, request) for program in programs)
                result["cases"] += len(seeds)
                a, b = ours.get("ok"), core.get("ok")
                a, b = (a if isinstance(a, dict) else {}), (b if isinstance(b, dict) else {})
                # Each program has its own projection: the oracle counts redraws, the harness names Boost.
                if (ours.get("id") != request["id"] or core.get("id") != request["id"] or
                        set(a) != {"subsidies", "redraws"} or set(b) != {"subsidies", "boost_version"} or
                        not isinstance(b["boost_version"], str) or
                        not isinstance(a.get("subsidies"), list) or not isinstance(b.get("subsidies"), list) or
                        not isinstance(a.get("redraws"), list) or
                        not len(a["subsidies"]) == len(b["subsidies"]) == len(a["redraws"]) == len(seeds)):
                    result["failures"].append({"height": height, "first_seed": start,
                                               "oracle": json.dumps(ours)[:300], "core": json.dumps(core)[:300]})
                    continue
                if b["boost_version"] not in result["boost"]:
                    result["boost"].append(b["boost_version"])
                histogram = result["redraws"][str(height)]
                for seed, x, y, redraws in zip(seeds, a["subsidies"], b["subsidies"], a["redraws"]):
                    if x != y or type(redraws) is not int:
                        result["failures"].append({"height": height, "seed": seed, "oracle": x, "core": y,
                                                   "redraws": redraws})
                    else:
                        histogram[str(redraws)] = histogram.get(str(redraws), 0) + 1
    finally:
        for program in programs:
            program.stdin.close()
            status = program.wait()
            if status != 0:
                result["failures"].append({"error": f"{program.args[0]} ended with status {status}",
                                           "first_seed": first})
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--jobs", type=int, default=8, help="worker processes, each with one oracle and one harness")
    parser.add_argument("--first", type=int, default=0, help="first seed (default 0)")
    parser.add_argument("--count", type=int, default=SEEDS, help="number of seeds (default 2^28, every seed)")
    parser.add_argument("--output", help="directory for summary.json")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    args = parser.parse_args()
    if not (0 <= args.first and 0 < args.count and args.first + args.count <= SEEDS and args.jobs > 0):
        parser.error("the seeds must lie in 0 to 2^28 - 1, and --jobs must be positive")

    for program, expected in ((args.oracle, ORACLE_FORMAT), (args.harness, ORACLE_FORMAT + "-core-projection")):
        version = subprocess.run([program, "--version"], capture_output=True, text=True)
        try:
            found = json.loads(version.stdout).get("format") if version.returncode == 0 else None
        except (ValueError, AttributeError):
            found = None
        if found != expected:
            print(f"FAIL VERSION {program} --version must give the format {expected}, got {found!r}")
            return 1

    started = time.time()
    # Each job is a whole number of requests, so a worker returns to the pool often.
    step = BATCH * 16
    jobs = [(args.oracle, args.harness, first, min(step, args.first + args.count - first))
            for first in range(args.first, args.first + args.count, step)]
    summary = {"first_seed": args.first, "seeds": args.count, "heights": list(HEIGHTS), "cases": 0,
               "failures": 0, "redraws": {str(h): {} for h in HEIGHTS}, "boost": []}
    reports = []
    with multiprocessing.Pool(args.jobs) as pool:
        for done, result in enumerate(pool.imap_unordered(run_range, jobs), start=1):
            summary["cases"] += result["cases"]
            summary["failures"] += len(result["failures"])
            reports.extend(result["failures"][:MAX_REPORTS - len(reports)])
            for version in result["boost"]:
                if version not in summary["boost"]:
                    summary["boost"].append(version)
            for height, histogram in result["redraws"].items():
                for redraws, count in histogram.items():
                    total = summary["redraws"][height]
                    total[redraws] = total.get(redraws, 0) + count
            if done % 32 == 0 or done == len(jobs):
                print(f"progress: {done}/{len(jobs)} jobs, {summary['cases']} cases, "
                      f"{summary['failures']} failures, {time.time() - started:.0f} s", flush=True)
    summary["redraws"] = {h: dict(sorted(v.items(), key=lambda kv: int(kv[0]))) for h, v in summary["redraws"].items()}
    summary["largest_redraws"] = max((int(r) for v in summary["redraws"].values() for r in v), default=None)
    summary["seconds"] = round(time.time() - started)
    summary["first_failures"] = reports
    expected = len(HEIGHTS) * args.count
    if summary["cases"] != expected:
        summary["failures"] += 1
        reports.append({"error": f"{summary['cases']} cases, expected {expected}"})
    for report in reports:
        print(f"FAIL {json.dumps(report)}")
    text = json.dumps(summary, indent=2)
    print(text)
    if args.output:
        directory = pathlib.Path(args.output)
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "summary.json").write_text(text + "\n")
    print("PASS" if summary["failures"] == 0 else f"FAIL: {summary['failures']} failures")
    return 0 if summary["failures"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
