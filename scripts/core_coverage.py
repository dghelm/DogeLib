"""Measure the lines of Core's src/validation.cpp that a comparison executes.

Usage: python3 -I scripts/core_coverage.py [--op OP] [--timeout SECONDS] --output DIR <dogelib-oracle> <build-dir>

<build-dir> is a directory of `scripts/build_core_harness.sh --coverage`, such as build/core-harness.
It holds core-oracle, core-oracle-coverage and coverage/, the object of the unit that includes
validation.cpp with its notes file (design record 0013, section 9.2, and decision 13).

The script takes the requests of the full comparison of scripts/compare_core.py whose operation is OP,
`block.validate` by default, or every request with `--op all`. It runs them in this order:

1. The oracle answers each request.
2. Each harness gets the request that the comparison gives it (`harness_request`): without the block
   that the oracle found outside the int64 range.
3. core-oracle and core-oracle-coverage answer the same harness requests, after the old counts are removed.
   Their responses must be equal as JSON values, because the coverage build is a measurement tool and no
   verdict comes from it. A difference fails with `FAIL COVERAGE_DIFFERS`.
4. The oracle and core-oracle-coverage must agree under the comparison's own agreement function.
   A difference fails with `FAIL <code>` of that function.
5. gcov reads the counts and writes its text and JSON output to DIR.

DIR then holds `validation.cpp.gcov`, gcov's line and branch counts of the whole file, and
`report.json` and `report.md`. The report gives, for each function of design record 0013, section 3.2,
its executed lines and taken branches, and each line of the function that no request executed. It also
gives the count of each reject site of sections 3.2 and 3.3. The counts are a measurement, and no
expected value comes from them. The exit status is 0 only when steps 1 to 5 succeed.
"""

import argparse
import gzip
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from compare_core import RunError, compare, compare_refused, harness_refused, request_sets, run_stream
from oracle_block_validate import harness_request

PIN = "e0a1c157791544e818c901bd9341896965afbf9d"

# The functions of design record 0013, section 3.2, by the name that gcov prints before the parameters.
FUNCTIONS = ["CheckTransaction", "CheckBlockHeader", "CheckBlock", "ContextualCheckBlockHeader",
             "ContextualCheckBlock", "ConnectBlock", "Consensus::CheckTxInputs", "CheckInputs", "AcceptBlockHeader"]

# The reject sites of section 3.2 (in scope) and section 3.3 (out of scope): line of src/validation.cpp at the pin.
SITES = [
    (531, "bad-txns-vin-empty", True), (533, "bad-txns-vout-empty", True), (536, "bad-txns-oversize", True),
    (543, "bad-txns-vout-negative", True), (545, "bad-txns-vout-toolarge", True),
    (548, "bad-txns-txouttotal-toolarge", True), (557, "bad-txns-inputs-duplicate", True),
    (564, "bad-cb-length", True), (570, "bad-txns-prevout-null", True),
    (2934, "high-hash", True),
    (2956, "bad-txnmrklroot", True), (2962, "bad-txns-duplicate", True), (2973, "bad-blk-length", True),
    (2977, "bad-cb-missing", True), (2980, "bad-cb-multiple", True), (2994, "bad-blk-sigops (CheckBlock)", True),
    (3077, "late-legacy-block", True), (3086, "early-auxpow-block", True), (3090, "bad-diffbits", True),
    (3099, "bad-fork-prior-to-checkpoint", True), (3104, "time-too-old", True), (3108, "time-too-new", True),
    (3115, "bad-version(0x…)", True),
    (3141, "bad-txns-nonfinal (ContextualCheckBlock)", True), (3151, "bad-cb-height", True),
    (3187, "unexpected-witness", True), (3199, "bad-blk-weight", True),
    (1886, "bad-txns-BIP30", True), (1946, "bad-txns-inputs-missingorspent", True),
    (1969, "bad-blk-sigops (ConnectBlock)", True), (2001, "bad-cb-amount", True),
    (1436, "bad-txns-premature-spend-of-coinbase", True), (1443, "bad-txns-inputvalues-outofrange", True),
    (1448, "bad-txns-in-belowout", True),
    (1503, "non-mandatory-script-verify-flag", True), (1512, "mandatory-script-verify-flag-failed", True),
    (3220, "duplicate", True), (3231, "bad-prevblk, unknown predecessor", True),
    (3234, "bad-prevblk, predecessor with a failure flag", True), (3253, "bad-prevblk, failed ancestor", True),
    (3173, "bad-witness-nonce-size", False), (3177, "bad-witness-merkle-match", False),
    (1958, "bad-txns-nonfinal (ConnectBlock)", False), (1420, "empty reason of CheckTxInputs", False),
    (1454, "bad-txns-fee-negative", False), (1457, "bad-txns-fee-outofrange", False),
    (2004, "rejection without a reason", False),
]


def fail(code: str, message: str) -> int:
    print(f"FAIL {code} {message}")
    return 1


def gcov(build: pathlib.Path, output: pathlib.Path) -> dict:
    """Run gcov on the counts of the coverage unit, and return its JSON record of validation.cpp."""
    covdir = build / "coverage"
    obj = covdir / "core_validation.o"
    for flags in (["-b", "-c"], ["-j", "-b"]):
        subprocess.run(["gcov", *flags, "-o", str(covdir), str(obj)], cwd=output, check=True,
                       stdout=subprocess.DEVNULL)
    data = json.loads(gzip.decompress((output / "core_validation.gcov.json.gz").read_bytes()))
    for f in data["files"]:
        if f["file"].endswith("/src/validation.cpp"):
            return f
    raise RunError("GCOV", "gcov output has no record of src/validation.cpp")


def report(record: dict, source: list[str]) -> dict:
    lines = {line["line_number"]: line for line in record["lines"]}
    functions = []
    for name in FUNCTIONS:
        found = [f for f in record["functions"] if f["demangled_name"].startswith(name + "(")]
        if len(found) != 1:
            raise RunError("GCOV", f"{len(found)} functions named {name} in the gcov record")
        f = found[0]
        span = [lines[n] for n in range(f["start_line"], f["end_line"] + 1) if n in lines]
        branches = [b for line in span for b in line.get("branches", [])]
        functions.append({
            "function": name, "start_line": f["start_line"], "end_line": f["end_line"],
            "calls": f["execution_count"],
            "lines": len(span), "lines_executed": sum(1 for line in span if line["count"]),
            "branches": len(branches), "branches_taken": sum(1 for b in branches if b["count"]),
            "unexecuted": [{"line": line["line_number"], "text": source[line["line_number"] - 1].strip()}
                           for line in span if not line["count"]],
        })
    sites = [{"line": n, "reason": reason, "in_scope": scope, "count": lines[n]["count"] if n in lines else None,
              "text": source[n - 1].strip()} for n, reason, scope in SITES]
    return {"functions": functions, "sites": sites}


def write_markdown(path: pathlib.Path, header: list[str], rep: dict) -> None:
    out = [*header, "", "| Function | Lines | Executed | Branches | Taken |", "| --- | ---: | ---: | ---: | ---: |"]
    for f in rep["functions"]:
        out.append(f"| `{f['function']}` (lines {f['start_line']} to {f['end_line']}) | {f['lines']} | "
                   f"{f['lines_executed']} | {f['branches']} | {f['branches_taken']} |")
    out += ["", "| Line | Reject site | Section | Count |", "| ---: | --- | --- | ---: |"]
    for s in rep["sites"]:
        out.append(f"| {s['line']} | `{s['reason']}` | {'3.2' if s['in_scope'] else '3.3'} | {s['count']} |")
    for f in rep["functions"]:
        out += ["", f"Lines of `{f['function']}` that no request executed:", ""]
        out += [f"- {u['line']}: `{u['text']}`" for u in f["unexecuted"]] or ["- None"]
    path.write_text("\n".join(out) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--op", default="block.validate", help="the operation of the requests, or `all`")
    parser.add_argument("--timeout", type=float, default=3600.0, help="seconds for each program run")
    parser.add_argument("--output", required=True, help="the directory of the gcov output and the report")
    parser.add_argument("oracle")
    parser.add_argument("build", help="the build directory of scripts/build_core_harness.sh --coverage")
    args = parser.parse_args()
    build = pathlib.Path(args.build).resolve()
    output = pathlib.Path(args.output).resolve()
    ordinary, coverage = build / "core-oracle", build / "core-oracle-coverage"
    if not coverage.is_file() or not (build / "coverage" / "core_validation.gcno").is_file():
        return fail("BUILD", f"{build} has no coverage build. Run scripts/build_core_harness.sh --coverage first.")
    output.mkdir(parents=True, exist_ok=True)

    sets, _ = request_sets()
    requests = [r for _, reqs in sets for r in reqs if args.op == "all" or r["op"] == args.op]
    if not requests:
        return fail("REQUESTS", f"the full comparison has no request of {args.op}")
    requests = [{**r, "id": f"c{i}"} for i, r in enumerate(requests)]
    for stale in (build / "coverage").glob("*.gcda"):
        stale.unlink()
    try:
        ours = run_stream(args.oracle, requests, args.timeout)
        to_core = [harness_request(r, a) for r, a in zip(requests, ours)]
        plain = run_stream(str(ordinary), to_core, args.timeout)
        counted = run_stream(str(coverage), to_core, args.timeout)
    except RunError as e:
        return fail(e.code, str(e))

    failures = 0
    for req, a, p, c in zip(requests, ours, plain, counted):
        if p != c:
            failures += 1
            print(f"FAIL COVERAGE_DIFFERS {req['id']}: {json.dumps(p)[:300]} != {json.dumps(c)[:300]}")
            continue
        result = compare_refused(req, a, c) if harness_refused(req) else compare(req, a, c)
        if result is not None:
            failures += 1
            print(f"FAIL {result[0]} {req['id']}: {result[1]}")
    if failures:
        print(f"{failures} failures in {len(requests)} requests")
        return 1

    try:
        record = gcov(build, output)
        source = (build / "core" / "src" / "validation.cpp").read_text().splitlines()
        rep = report(record, source)
    except (RunError, subprocess.CalledProcessError, OSError, KeyError) as e:
        return fail("GCOV", str(e))
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    header = [f"# Coverage of src/validation.cpp: {len(requests)} requests of {args.op}", "",
              f"DogeLib revision {revision}, Core {PIN}, coverage build {coverage}.",
              "The oracle, core-oracle and core-oracle-coverage agreed on every request."]
    (output / "report.json").write_text(json.dumps({"op": args.op, "requests": len(requests), "revision": revision,
                                                    "core": PIN, **rep}, indent=1) + "\n")
    write_markdown(output / "report.md", header, rep)
    for f in rep["functions"]:
        print(f"{f['function']}: {f['lines_executed']} of {f['lines']} lines, "
              f"{f['branches_taken']} of {f['branches']} branches")
    print(f"PASS {len(requests)} requests of {args.op}; report in {output / 'report.md'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
