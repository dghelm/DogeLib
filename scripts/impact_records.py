#!/usr/bin/env python3
"""Write and check the committed records of the historical impact runs (docs/oracle.md, Historical
impact runs).

Usage:
  python3 -I scripts/impact_records.py write [--outputs DIR] [--records DIR]
  python3 -I scripts/impact_records.py --check [--outputs DIR] [--records DIR]
  python3 -I scripts/impact_records.py --self-test

The responses and logs of the runs are too large for Git. The maintainer's machine keeps them
under `build/impact/`: `runs/<range>/<run>/` has `response.json`, `report.json` and
`summary.json` of `scripts/impact_run.py run`, and `runs/<range>/<run>.log` has its log with the
measurements of `/usr/bin/time -v`. `requests/<range>/` has the request, and `recheck/` has the
reports of `impact_run.py check` on each saved response. No release asset holds them.

`write` reads those files once and writes, under `tests/proposals/impact/runs/`:

- `<range>/<run>.json` for each run, format `dogelib-impact-run/1`: the range, the revision and its
  activation, the SHA-256 of the executable, of the request, of the blocks file, of the coins file
  and of the baseline response. Also the SHA-256 and size of the response, the report and the
  summary, the counts, the digest at the end, the time, the memory, and the recheck.
- `index.json`, format `dogelib-impact-runs/1`: the build of the runs, where the outputs are kept,
  and one entry for each run with the path and SHA-256 of its record.
- `SHA256SUMS` of the index and of every record.

`--check` requires that the index names each record file exactly once, with its SHA-256, that
each record agrees with its index entry, and that `SHA256SUMS` lists exactly those files with
their SHA-256 values. With `--outputs DIR` it also requires that the saved files under DIR have the
SHA-256 values of the records. It runs no DogeLib code and reads no network.

`--self-test` plants faults in a copy of the records, and `--check` must fail on each one.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import re
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORDS = ROOT / "tests" / "proposals" / "impact" / "runs"
OUTPUTS = ROOT / "build" / "impact"
RUN_FORMAT = "dogelib-impact-run/1"
INDEX_FORMAT = "dogelib-impact-runs/1"
# The build of the recorded runs (docs/oracle.md, Historical impact runs).
BUILD = {
    "commit": "6ef0e12f8ace3a7576216f9ef2c1bf11d7fb095f",
    "dogelib-proposal-oracle_sha256": "220a29cdff67c47bb80541fb7cbf75098b9965f68837b56155216b47c24d4548",
    "dogelib-oracle_sha256": "32b9fc94235fe8408d0bd06d3bc90945d0314057e037d68fb8db50647cf1a025",
}
RETAINED = ("The maintainer's machine keeps the requests, responses, reports, summaries and logs under "
            "build/impact/. They are not in Git and not in a release asset.")
RUN_NAMES = ("ExampleVersionVerify-none", "ExampleVersionVerify-0", "ExampleFaultyLocktime-corrected-none",
             "ExampleFaultyLocktime-corrected-0", "RelativeLockTime-1")


class RecordError(Exception):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_entry(path: Path) -> dict:
    return {"sha256": sha256_file(path), "bytes": path.stat().st_size}


def dump(value) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def baseline_path(outputs: Path, range_name: str, request: dict, summary: dict) -> Path | None:
    """The baseline response that `.lane/jobs.sh` passed with `--baseline`, or None."""
    if not summary["baseline_compared"]:
        return None
    own = outputs / "runs" / range_name / "baseline-response.json"
    if own.exists():
        return own
    # The ranges of the Core pass use the recorded response of scripts/run_range.py beside their blocks file.
    recorded = Path(request["blocks_file"]).resolve().parent.parent.parent / "range-runs" / range_name / "range-oracle-response.json"
    if not recorded.exists():
        raise RecordError(f"{range_name}: no baseline response found")
    return recorded


def max_rss_kib(log: Path) -> int:
    found = re.findall(r"Maximum resident set size \(kbytes\): (\d+)", log.read_text())
    if not found:
        raise RecordError(f"{log}: no memory measurement")
    return int(found[-1])


def run_record(outputs: Path, range_name: str, run: str, hashed: dict) -> dict:
    run_dir = outputs / "runs" / range_name / run
    request_path = outputs / "requests" / range_name / "request.json"
    request = json.loads(request_path.read_text())
    summary = json.loads((run_dir / "summary.json").read_text())
    recheck_dir = outputs / "recheck" / range_name / run
    recheck = json.loads((recheck_dir / "summary.json").read_text())

    def cached(path: Path) -> dict:
        key = str(path.resolve())
        if key not in hashed:
            hashed[key] = file_entry(path)
        return hashed[key]

    blocks = cached(Path(request["blocks_file"]))
    if blocks["sha256"] != summary["blocks_sha256"]:
        raise RecordError(f"{range_name}/{run}: the blocks file differs from the summary")
    coins = cached(Path(request["coins_file"])) if request.get("coins_file") else None
    baseline = baseline_path(outputs, range_name, request, summary)
    result_keys = ("blocks", "candidate_blocks", "changed_blocks", "unsupported", "rejected_by_step", "set_digest_hex", "set_coins")
    for key in result_keys:
        if recheck[key] != summary[key]:
            raise RecordError(f"{range_name}/{run}: the recheck differs from the run in {key}")
    finished = datetime.datetime.fromtimestamp((run_dir / "summary.json").stat().st_mtime, datetime.timezone.utc)
    return {
        "format": RUN_FORMAT,
        "range": range_name,
        "run": run,
        "first": summary["first"],
        "last": summary["last"],
        "revision": summary["revision"],
        "executable": {"name": "dogelib-proposal-oracle", "sha256": summary["proposal_oracle_sha256"], "commit": BUILD["commit"]},
        "inputs": {
            "request": file_entry(request_path),
            "blocks_file": blocks,
            "coins_file": None if coins is None else {"name": Path(request["coins_file"]).name, **coins},
            "expected_end": request.get("expected_end"),
            "candidate_list": summary["candidate_list"],
            "candidate_list_sha256": summary["candidate_list_sha256"],
            "baseline_response": None if baseline is None else cached(baseline),
        },
        "outputs": {name: file_entry(run_dir / f"{name}.json") for name in ("response", "report", "summary")},
        "result": {key: summary[key] for key in result_keys},
        "time": {"seconds": summary["seconds"], "max_rss_kib": max_rss_kib(outputs / "runs" / range_name / f"{run}.log"),
                 "finished_utc": finished.strftime("%Y-%m-%dT%H:%M:%SZ")},
        "recheck": {"command": "impact_run.py check", "summary": file_entry(recheck_dir / "summary.json"),
                    "changed_blocks": recheck["changed_blocks"]},
    }


def saved_runs(outputs: Path) -> list[tuple[str, str]]:
    runs = []
    for summary in sorted((outputs / "runs").glob("*/*/summary.json")):
        range_name, run = summary.parent.parent.name, summary.parent.name
        if run not in RUN_NAMES:
            raise RecordError(f"unknown run {range_name}/{run}")
        runs.append((range_name, run))
    return runs


def write(outputs: Path, records: Path, log) -> None:
    hashed: dict = {}
    entries = []
    if records.exists():
        shutil.rmtree(records)
    for range_name, run in saved_runs(outputs):
        record = run_record(outputs, range_name, run, hashed)
        path = records / range_name / f"{run}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(dump(record))
        entries.append({"range": range_name, "run": run, "revision": record["revision"],
                        "file": f"{range_name}/{run}.json", "sha256": sha256_file(path)})
        log(f"{range_name}/{run}: {record['result']['blocks']} blocks, {record['result']['changed_blocks']} changed")
    index = {"format": INDEX_FORMAT, "build": BUILD, "retained": RETAINED, "runs": entries}
    (records / "index.json").write_text(dump(index))
    write_sums(records)
    log(f"wrote {len(entries)} records under {records}")


def write_sums(records: Path) -> None:
    files = sorted(p.relative_to(records).as_posix() for p in records.rglob("*.json"))
    (records / "SHA256SUMS").write_text("".join(f"{sha256_file(records / f)}  {f}\n" for f in files))


def check(records: Path, outputs: Path | None, log) -> None:
    index = json.loads((records / "index.json").read_text())
    if index.get("format") != INDEX_FORMAT or index.get("build") != BUILD:
        raise RecordError("index.json has another format or build")
    files = {e["file"] for e in index["runs"]}
    if len(files) != len(index["runs"]):
        raise RecordError("index.json names a record twice")
    present = {p.relative_to(records).as_posix() for p in records.rglob("*.json")} - {"index.json"}
    if present != files:
        raise RecordError(f"records and index differ: {sorted(present ^ files)}")
    for entry in index["runs"]:
        path = records / entry["file"]
        if sha256_file(path) != entry["sha256"]:
            raise RecordError(f"{entry['file']} does not have the SHA-256 of the index")
        record = json.loads(path.read_text())
        if (record.get("format"), record["range"], record["run"], record["revision"]) != (
                RUN_FORMAT, entry["range"], entry["run"], entry["revision"]):
            raise RecordError(f"{entry['file']} differs from its index entry")
        if entry["file"] != f"{record['range']}/{record['run']}.json":
            raise RecordError(f"{entry['file']} is not at the path of its range and run")
        if record["executable"]["sha256"] != BUILD["dogelib-proposal-oracle_sha256"]:
            raise RecordError(f"{entry['file']} names another executable")
        if record["result"]["changed_blocks"] != record["recheck"]["changed_blocks"]:
            raise RecordError(f"{entry['file']}: the recheck differs from the run")
        if outputs is not None:
            run_dir = outputs / "runs" / record["range"] / record["run"]
            for name, expected in record["outputs"].items():
                if file_entry(run_dir / f"{name}.json") != expected:
                    raise RecordError(f"{run_dir}/{name}.json differs from its record")
    sums = {}
    for line in (records / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        sums[name] = digest
    if set(sums) != files | {"index.json"}:
        raise RecordError("SHA256SUMS does not list exactly the index and the records")
    for name, digest in sums.items():
        if sha256_file(records / name) != digest:
            raise RecordError(f"{name} does not have its SHA-256 in SHA256SUMS")
    log(f"{len(files)} records agree with index.json and SHA256SUMS"
        + (f", and with the saved outputs under {outputs}" if outputs is not None else ""))


def self_test(records: Path) -> int:
    def fails(name: str, plant) -> bool:
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "runs"
            shutil.copytree(records, copy)
            plant(copy)
            try:
                check(copy, None, lambda _: None)
            except (RecordError, OSError, ValueError, KeyError) as error:
                print(f"ok: {name} fails ({error})")
                return True
            print(f"FAIL: {name} passes")
            return False

    first = json.loads((records / "index.json").read_text())["runs"][0]["file"]

    def edit_record(copy: Path, change) -> None:
        path = copy / first
        record = json.loads(path.read_text())
        change(record)
        path.write_text(dump(record))

    def drop_entry(copy: Path) -> None:
        index = json.loads((copy / "index.json").read_text())
        index["runs"].pop()
        (copy / "index.json").write_text(dump(index))

    def resum_after(change):
        def plant(copy: Path) -> None:
            change(copy)
            write_sums(copy)
        return plant

    cases = [
        ("a changed record", lambda c: edit_record(c, lambda r: r["result"].update(changed_blocks=1))),
        ("a changed record with new sums", resum_after(lambda c: edit_record(c, lambda r: r["result"].update(changed_blocks=1)))),
        ("a missing record", lambda c: (c / first).unlink()),
        ("an extra record", lambda c: (c / first).with_name("extra.json").write_text((c / first).read_text())),
        ("an index without an entry", resum_after(drop_entry)),
        ("a record of another executable", resum_after(lambda c: (edit_record(c, lambda r: r["executable"].update(sha256="0" * 64)),
                                                                 refresh_index(c)))),
        ("a changed SHA256SUMS", lambda c: (c / "SHA256SUMS").write_text((c / "SHA256SUMS").read_text().replace("0", "1", 1))),
    ]
    clean = True
    try:
        check(records, None, print)
    except RecordError as error:
        print(f"FAIL: the committed records fail ({error})")
        clean = False
    return 0 if clean and all(fails(name, plant) for name, plant in cases) else 1


def refresh_index(copy: Path) -> None:
    """Give each index entry the SHA-256 of its record, so that only the planted field is wrong."""
    index = json.loads((copy / "index.json").read_text())
    for entry in index["runs"]:
        entry["sha256"] = sha256_file(copy / entry["file"])
    (copy / "index.json").write_text(dump(index))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", nargs="?", choices=["write"])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--outputs", metavar="DIR")
    parser.add_argument("--records", metavar="DIR", default=str(RECORDS))
    args = parser.parse_args(argv)
    records = Path(args.records)
    try:
        if args.self_test:
            return self_test(records)
        if args.command == "write":
            write(Path(args.outputs) if args.outputs else OUTPUTS, records, print)
            return 0
        if args.check:
            check(records, Path(args.outputs) if args.outputs else None, print)
            return 0
        parser.error("give write, --check or --self-test")
    except (RecordError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
