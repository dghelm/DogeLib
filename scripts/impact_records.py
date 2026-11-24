#!/usr/bin/env python3
"""Write and check the committed records of the historical impact runs (docs/oracle.md, Historical
impact runs).

Usage:
  python3 -I scripts/impact_records.py recheck
  python3 -I scripts/impact_records.py write
  python3 -I scripts/impact_records.py --check [--outputs DIR]
  python3 -I scripts/impact_records.py --self-test

The responses and logs of the runs are too large for Git. The maintainer's machine keeps them
under `build/impact/`, and no release asset holds them:

- `runs/<range>/<run>/` has `response.json`, `report.json` and `summary.json` of
  `scripts/impact_run.py run`, and `runs/<range>/<run>.log` has its log with the measurements of
  `/usr/bin/time -v`.
- `requests/<range>/request.json` is the request of the range.
- `recheck/<range>/<run>/` has `summary.json` and `report.json` of `impact_run.py check` on the
  saved response, and `command.txt`, the command that wrote them.

The baseline responses are `build/range-runs/<range>/range-oracle-response.json`, the recorded
responses of `scripts/run_range.py`, for the ranges of the Core pass. For `short`, `S`, `E1` and
`E2` they are `build/impact/runs/<range>/baseline-response.json`, from `dogelib-oracle` of the
build of the runs. Heights 0 to 145,000 have none.

`recheck` runs `impact_run.py check` on each saved response with the command of `recheck_command`,
and saves that command. `write` reads the saved files and writes, under
`tests/proposals/impact/runs/`, one record `<range>/<run>.json` for each run (format
`dogelib-impact-run/1`, `RECORD_SCHEMA`), `index.json` (format `dogelib-impact-runs/1`) and
`SHA256SUMS`.

`--check` requires the 51 runs of `EXPECTED`, which the script states without the index. Each
record must have exactly the keys of `RECORD_SCHEMA` at every level, and each value must pass the
test of its type. The comment of each field of `RECORD_SCHEMA` names what the check compares it
with: a fixed rule of this script, a committed file, or a saved file. The committed files are the
candidate lists and the snapshot manifests. `--check` alone compares the fixed rules and the
committed files. With `--outputs DIR` it also compares the saved files under DIR, which only the
maintainer's machine has. The check runs no DogeLib code and reads no network.

`--self-test` makes saved outputs for the 51 runs, writes their records, and requires that
`--check --outputs` passes. Then it changes one value of one record for each field of
`RECORD_SCHEMA`, gives the index and `SHA256SUMS` the new hashes, and requires that the check
fails. It also deletes a required key from each object and adds an unknown key to each, and
plants faults in the inventory, the index, the sums and the saved files.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORDS = ROOT / "tests" / "proposals" / "impact" / "runs"
LISTS = ROOT / "tests" / "proposals" / "impact"
MANIFESTS = ROOT / "tests" / "block" / "mainnet-blocks" / "snapshots"
OUTPUTS = ROOT / "build" / "impact"
RUN_FORMAT = "dogelib-impact-run/1"
INDEX_FORMAT = "dogelib-impact-runs/1"
# The build of the recorded runs (docs/oracle.md, Historical impact runs).
BUILD = {
    "commit": "6ef0e12f8ace3a7576216f9ef2c1bf11d7fb095f",
    "dogelib-proposal-oracle_sha256": "220a29cdff67c47bb80541fb7cbf75098b9965f68837b56155216b47c24d4548",
    "dogelib-oracle_sha256": "32b9fc94235fe8408d0bd06d3bc90945d0314057e037d68fb8db50647cf1a025",
}
EXECUTABLE = {"name": "dogelib-proposal-oracle", "sha256": BUILD["dogelib-proposal-oracle_sha256"], "commit": BUILD["commit"]}
PROGRAM = "build/bin-6ef0e12/dogelib-proposal-oracle"
RETAINED = ("The maintainer's machine keeps the requests, responses, reports, summaries and logs under "
            "build/impact/. They are not in Git and not in a release asset.")

# The runs that the records must cover, without the index: the five runs of each range from a
# snapshot, and RelativeLockTime from height 1 on heights 0 to 145,000.
REVISION_OF_RUN = {
    "ExampleVersionVerify-none": {"name": "ExampleVersionVerify", "variant": None, "activation_height": None},
    "ExampleVersionVerify-0": {"name": "ExampleVersionVerify", "variant": None, "activation_height": 0},
    "ExampleFaultyLocktime-corrected-none": {"name": "ExampleFaultyLocktime", "variant": "corrected", "activation_height": None},
    "ExampleFaultyLocktime-corrected-0": {"name": "ExampleFaultyLocktime", "variant": "corrected", "activation_height": 0},
    "RelativeLockTime-1": {"name": "RelativeLockTime", "variant": None, "activation_height": 1},
}
RUN_NAMES = tuple(REVISION_OF_RUN)
PASS_RANGES = ("A", "B", "C", "D", "F", "H")
SNAPSHOT_RANGES = ("short", "S", "A", "B", "C", "D", "E1", "E2", "F", "H")
GENESIS = "genesis-145000"
EXPECTED = {(r, run): REVISION_OF_RUN[run] for r in SNAPSHOT_RANGES for run in RUN_NAMES}
EXPECTED[(GENESIS, "RelativeLockTime-1")] = REVISION_OF_RUN["RelativeLockTime-1"]
OUTPUT_NAMES = ("response", "report", "summary")
HEX64 = re.compile(r"[0-9a-f]{64}")


class RecordError(Exception):
    pass


def baseline_relative(range_name: str) -> str | None:
    """The baseline response of a range, relative to the root of the build directory's parent."""
    if range_name == GENESIS:
        return None
    if range_name in PASS_RANGES:
        return f"build/range-runs/{range_name}/range-oracle-response.json"
    return f"build/impact/runs/{range_name}/baseline-response.json"


def recheck_command(range_name: str, run: str) -> str:
    """The exact command of the recheck of one run, run from the root of the repository."""
    revision = REVISION_OF_RUN[run]
    name = revision["name"] + (f"/{revision['variant']}" if revision["variant"] else "")
    activation = "none" if revision["activation_height"] is None else str(revision["activation_height"])
    parts = ["python3", "-I", "scripts/impact_run.py", "check", "--range", range_name,
             "--request", f"build/impact/requests/{range_name}/request.json", "--revision", name, "--activation", activation]
    baseline = baseline_relative(range_name)
    if baseline is not None:
        parts += ["--baseline", baseline]
    parts += ["--response", f"build/impact/runs/{range_name}/{run}/response.json",
              "--output", f"build/impact/recheck/{range_name}/{run}", PROGRAM]
    return " ".join(parts)


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


def utc_of_mtime(path: Path) -> str:
    moment = datetime.datetime.fromtimestamp(path.stat().st_mtime, datetime.timezone.utc)
    return moment.strftime("%Y-%m-%dT%H:%M:%SZ")


def time_log(log: Path) -> dict:
    """The peak memory and the wall-clock time that `/usr/bin/time -v` wrote at the end of LOG."""
    text = log.read_text()
    rss = re.findall(r"Maximum resident set size \(kbytes\): (\d+)", text)
    elapsed = re.findall(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)", text)
    if not rss or not elapsed:
        raise RecordError(f"{log}: no measurement of /usr/bin/time -v")
    return {"max_rss_kib": int(rss[-1]), "elapsed": elapsed[-1]}


@dataclass
class Layout:
    """Where the saved files of the runs are. `base` is the directory that holds `build/`."""
    base: Path

    @property
    def outputs(self) -> Path:
        return self.base / "build" / "impact"

    def run_dir(self, range_name: str, run: str) -> Path:
        return self.outputs / "runs" / range_name / run

    def log(self, range_name: str, run: str) -> Path:
        return self.outputs / "runs" / range_name / f"{run}.log"

    def request(self, range_name: str) -> Path:
        return self.outputs / "requests" / range_name / "request.json"

    def recheck_dir(self, range_name: str, run: str) -> Path:
        return self.outputs / "recheck" / range_name / run

    def baseline(self, range_name: str) -> Path | None:
        relative = baseline_relative(range_name)
        return None if relative is None else self.base / relative


@dataclass
class Sources:
    """The committed files that a record is compared with: the candidate lists and the snapshot manifests."""
    lists: Path = LISTS
    manifests: Path = MANIFESTS

    def candidate_list(self, range_name: str) -> Path:
        return self.lists / f"{range_name}.json"


def is_int(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def natural(value) -> bool:
    return is_int(value) and value >= 0


def positive(value) -> bool:
    return is_int(value) and value > 0


def text(value) -> bool:
    return isinstance(value, str) and value != ""


def hex64(value) -> bool:
    return isinstance(value, str) and HEX64.fullmatch(value) is not None


def utc_time(value) -> bool:
    return isinstance(value, str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value) is not None


def clock(value) -> bool:
    return isinstance(value, str) and re.fullmatch(r"(\d+:)?\d+:\d{2}(\.\d+)?", value) is not None


def counts(value) -> bool:
    """A map from a reason or a step to a count, as `unsupported` and `rejected_by_step` are."""
    return isinstance(value, dict) and all(isinstance(k, str) and positive(v) for k, v in value.items())


def optional(schema):
    return ("optional", schema)


# The exact key set of each object of `dogelib-impact-run/1`, and the test of each value. A value
# may be null only under `optional`. The comment of each field names what `check_record` (fixed
# rules and committed files) and `check_outputs` (saved files, with `--outputs`) compare it with.
# "Saved" means a file under build/ on the maintainer's machine.
ENTRY_NOTE = "an entry: the SHA-256 and size of the file that its comment names"
RECORD_SCHEMA = {
    "format": text,      # Rule: RUN_FORMAT.
    "range": text,       # Rule: EXPECTED, the index entry and the path of the record.
    "run": text,         # Rule: EXPECTED, the index entry and the path of the record.
    "first": natural,    # Committed: `first` of the candidate list. Saved: `first` of the run summary.
    "last": natural,     # Committed: `last` of the candidate list. Saved: `last` of the run summary.
    "revision": {        # Rule: EXPECTED and the index entry. Saved: `revision` of the run summary.
        "name": text,
        "variant": optional(text),
        "activation_height": optional(natural),
    },
    "executable": {      # Rule: EXECUTABLE. Saved: `proposal_oracle_sha256` of the run summary.
        "name": text,
        "sha256": hex64,
        "commit": text,
    },
    "inputs": {
        # Saved: the request file of the range.
        "request": {"sha256": hex64, "bytes": positive},
        # Committed: `blocks_sha256` of the candidate list. Saved: the file of the request's
        # `blocks_file`, and `blocks_sha256` of the run summary.
        "blocks_file": {"sha256": hex64, "bytes": positive},
        # Rule: null exactly for heights 0 to 145,000. Committed: `snapshot` of the candidate list
        # names it, and the snapshot manifest, where one is committed, has its SHA-256 and size.
        # Saved: the file of the request's `coins_file`.
        "coins_file": optional({"name": text, "sha256": hex64, "bytes": positive}),
        # Rule: equal to `result.set_digest_hex`. Saved: `expected_end` of the request.
        "expected_end": hex64,
        # Rule: tests/proposals/impact/<range>.json. Saved: `candidate_list` of the run summary.
        "candidate_list": text,
        # Committed: the SHA-256 of the candidate list. Saved: `candidate_list_sha256` of the run summary.
        "candidate_list_sha256": hex64,
        # Rule: null exactly for heights 0 to 145,000. Saved: the file of `baseline_relative`, and
        # `baseline_compared` of the run summary.
        "baseline_response": optional({"sha256": hex64, "bytes": positive}),
    },
    "outputs": {         # Saved: response.json, report.json and summary.json of the run.
        "response": {"sha256": hex64, "bytes": positive},
        "report": {"sha256": hex64, "bytes": positive},
        "summary": {"sha256": hex64, "bytes": positive},
    },
    "result": {          # Saved: each field of the run summary, the recheck summary and, where it has the field, the report.
        "blocks": positive,                # Rule: last - first + 1.
        "candidate_blocks": natural,       # Committed: `candidate_blocks` of the revision in the candidate list.
        "changed_blocks": natural,         # Rule: equal to `recheck.changed_blocks`.
        "unsupported": counts,
        "rejected_by_step": counts,
        "set_digest_hex": hex64,           # Rule: equal to `inputs.expected_end`.
        "set_coins": positive,
    },
    "time": {
        "seconds": positive,               # Saved: `seconds` of the run summary.
        "max_rss_kib": positive,           # Saved: "Maximum resident set size" in the log of the run.
        "elapsed": clock,                  # Saved: "Elapsed (wall clock) time" in the log of the run.
        "finished_utc": utc_time,          # Saved: the modification time of the run summary, in UTC seconds.
    },
    "recheck": {
        "command": text,                   # Rule: `recheck_command`. Saved: command.txt of the recheck.
        "summary": {"sha256": hex64, "bytes": positive},   # Saved: summary.json of the recheck.
        "changed_blocks": natural,         # Saved: `changed_blocks` of the recheck summary.
    },
}
RESULT_KEYS = tuple(RECORD_SCHEMA["result"])
REPORT_KEYS = ("blocks", "candidate_blocks", "changed_blocks", "unsupported", "rejected_by_step")


def check_schema(value, schema, where: str) -> None:
    """VALUE has exactly the keys of SCHEMA, at every level, and each leaf passes its test."""
    if isinstance(schema, tuple):
        if value is not None:
            check_schema(value, schema[1], where)
        return
    if isinstance(schema, dict):
        if not isinstance(value, dict):
            raise RecordError(f"{where} is not an object")
        if set(value) != set(schema):
            missing, extra = sorted(set(schema) - set(value)), sorted(set(value) - set(schema))
            raise RecordError(f"{where} has other keys: missing {missing}, unknown {extra}")
        for key, inner in schema.items():
            check_schema(value[key], inner, f"{where}.{key}")
        return
    if not schema(value):
        raise RecordError(f"{where} has an invalid value")


def require(condition: bool, where: str, what: str) -> None:
    if not condition:
        raise RecordError(f"{where}: {what}")


def check_record(record: dict, range_name: str, run: str, sources: Sources) -> None:
    """The record has the schema, the fixed rules, and the values of the committed files."""
    where = f"{range_name}/{run}"
    check_schema(record, RECORD_SCHEMA, where)
    require((record["format"], record["range"], record["run"]) == (RUN_FORMAT, range_name, run), where,
            "the record has another format, range or run")
    require(record["revision"] == EXPECTED[(range_name, run)], where, "the record has another revision or activation")
    require(record["executable"] == EXECUTABLE, where, "the record names another executable")
    listing_path = sources.candidate_list(range_name)
    listing = json.loads(listing_path.read_text())
    inputs, result = record["inputs"], record["result"]
    require((record["first"], record["last"]) == (listing["first"], listing["last"]), where,
            "the heights differ from the candidate list")
    require(inputs["candidate_list"] == f"tests/proposals/impact/{range_name}.json", where, "another candidate list")
    require(inputs["candidate_list_sha256"] == sha256_file(listing_path), where,
            "the candidate list does not have the recorded SHA-256")
    require(inputs["blocks_file"]["sha256"] == listing["blocks_sha256"], where,
            "the blocks file differs from the candidate list")
    require(result["candidate_blocks"] == listing["revisions"][record["revision"]["name"]]["candidate_blocks"], where,
            "the candidate count differs from the candidate list")
    from_genesis = range_name == GENESIS
    for name in ("coins_file", "baseline_response"):
        require((inputs[name] is None) == from_genesis, where, f"the {name} does not fit the range")
    if not from_genesis:
        coins = inputs["coins_file"]
        require(coins["name"] == listing["snapshot"], where, "the coins file is not the snapshot of the candidate list")
        manifest_path = sources.manifests / f"{Path(coins['name']).stem}.json"
        if manifest_path.exists():
            manifest = json.loads(manifest_path.read_text())
            require((coins["sha256"], coins["bytes"]) == (manifest["sha256"], manifest["bytes"]), where,
                    "the coins file differs from its snapshot manifest")
    require(result["set_digest_hex"] == inputs["expected_end"], where, "the end digest is not the expected end")
    require(result["blocks"] == record["last"] - record["first"] + 1, where, "the block count does not fit the heights")
    require(result["changed_blocks"] == record["recheck"]["changed_blocks"], where, "the recheck differs from the run")
    require(record["recheck"]["command"] == recheck_command(range_name, run), where, "the recheck command is not the expected one")


def check_outputs(record: dict, layout: Layout, hashed: dict) -> None:
    """Each value that a saved file holds equals the record."""
    range_name, run = record["range"], record["run"]
    where = f"{range_name}/{run}"
    require(layout.outputs.is_dir(), where, f"{layout.outputs} is not a directory of saved outputs")

    def cached(path: Path) -> dict:
        require(path.is_file(), where, f"the saved file {path} is missing")
        key = str(path.resolve())
        if key not in hashed:
            hashed[key] = file_entry(path)
        return hashed[key]

    run_dir = layout.run_dir(range_name, run)
    for name in OUTPUT_NAMES:
        require(cached(run_dir / f"{name}.json") == record["outputs"][name], where, f"the saved {name}.json differs")
    summary = json.loads((run_dir / "summary.json").read_text())
    report = json.loads((run_dir / "report.json").read_text())
    recheck_dir = layout.recheck_dir(range_name, run)
    require(cached(recheck_dir / "summary.json") == record["recheck"]["summary"], where, "the saved recheck summary differs")
    recheck = json.loads((recheck_dir / "summary.json").read_text())
    for key in RESULT_KEYS:
        for name, saved in (("run summary", summary), ("recheck summary", recheck)):
            require(key in saved and saved[key] == record["result"][key], where, f"the {name} differs in {key}")
    for key in REPORT_KEYS:
        require(key in report and report[key] == record["result"][key], where, f"the report differs in {key}")
    require(recheck.get("changed_blocks") == record["recheck"]["changed_blocks"], where, "the recheck differs")
    pairs = {"first": (summary.get("first"), record["first"]),
             "last": (summary.get("last"), record["last"]),
             "revision": (summary.get("revision"), record["revision"]),
             "seconds": (summary.get("seconds"), record["time"]["seconds"]),
             "executable": (summary.get("proposal_oracle_sha256"), record["executable"]["sha256"]),
             "blocks hash": (summary.get("blocks_sha256"), record["inputs"]["blocks_file"]["sha256"]),
             "candidate list": (summary.get("candidate_list"), record["inputs"]["candidate_list"]),
             "candidate list hash": (summary.get("candidate_list_sha256"), record["inputs"]["candidate_list_sha256"]),
             "baseline": (summary.get("baseline_compared"), record["inputs"]["baseline_response"] is not None)}
    for name, (saved, recorded) in pairs.items():
        require(saved == recorded, where, f"the run summary differs in {name}")
    require(time_log(layout.log(range_name, run)) == {k: record["time"][k] for k in ("max_rss_kib", "elapsed")}, where,
            "the log of the run has another memory or time")
    require(utc_of_mtime(run_dir / "summary.json") == record["time"]["finished_utc"], where,
            "the run summary has another modification time")
    command = recheck_dir / "command.txt"
    require(command.is_file() and command.read_text().strip() == record["recheck"]["command"], where,
            "the saved recheck command differs")
    request_path = layout.request(range_name)
    require(cached(request_path) == record["inputs"]["request"], where, "the saved request differs")
    request = json.loads(request_path.read_text())
    require(request.get("expected_end") == record["inputs"]["expected_end"], where, "the request has another expected end")
    require(cached(Path(request["blocks_file"])) == record["inputs"]["blocks_file"], where, "the blocks file differs")
    coins = record["inputs"]["coins_file"]
    if coins is None:
        require(request.get("coins_file") is None, where, "the request has a coins file")
    else:
        require(request.get("coins_file") is not None, where, "the request has no coins file")
        require({"name": Path(request["coins_file"]).name, **cached(Path(request["coins_file"]))} == coins, where,
                "the coins file differs")
    baseline = layout.baseline(range_name)
    require((None if baseline is None else cached(baseline)) == record["inputs"]["baseline_response"], where,
            "the baseline response differs")


def run_record(layout: Layout, range_name: str, run: str, hashed: dict) -> dict:
    """The record of one run, from its saved files."""
    run_dir = layout.run_dir(range_name, run)
    request = json.loads(layout.request(range_name).read_text())
    summary = json.loads((run_dir / "summary.json").read_text())
    recheck_dir = layout.recheck_dir(range_name, run)
    recheck = json.loads((recheck_dir / "summary.json").read_text())

    def cached(path: Path) -> dict:
        key = str(path.resolve())
        if key not in hashed:
            hashed[key] = file_entry(path)
        return hashed[key]

    baseline = layout.baseline(range_name) if summary["baseline_compared"] else None
    return {
        "format": RUN_FORMAT,
        "range": range_name,
        "run": run,
        "first": summary["first"],
        "last": summary["last"],
        "revision": summary["revision"],
        "executable": {**EXECUTABLE, "sha256": summary["proposal_oracle_sha256"]},
        "inputs": {
            "request": file_entry(layout.request(range_name)),
            "blocks_file": cached(Path(request["blocks_file"])),
            "coins_file": None if not request.get("coins_file") else
            {"name": Path(request["coins_file"]).name, **cached(Path(request["coins_file"]))},
            "expected_end": request.get("expected_end"),
            "candidate_list": summary["candidate_list"],
            "candidate_list_sha256": summary["candidate_list_sha256"],
            "baseline_response": None if baseline is None else cached(baseline),
        },
        "outputs": {name: file_entry(run_dir / f"{name}.json") for name in OUTPUT_NAMES},
        "result": {key: summary[key] for key in RESULT_KEYS},
        "time": {"seconds": summary["seconds"], **time_log(layout.log(range_name, run)),
                 "finished_utc": utc_of_mtime(run_dir / "summary.json")},
        "recheck": {"command": (recheck_dir / "command.txt").read_text().strip(),
                    "summary": file_entry(recheck_dir / "summary.json"), "changed_blocks": recheck["changed_blocks"]},
    }


def write(layout: Layout, records: Path, log) -> None:
    hashed: dict = {}
    entries = []
    if records.exists():
        shutil.rmtree(records)
    for range_name, run in sorted(EXPECTED):
        record = run_record(layout, range_name, run, hashed)
        path = records / range_name / f"{run}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(dump(record))
        entries.append({"range": range_name, "run": run, "revision": record["revision"],
                        "file": f"{range_name}/{run}.json", "sha256": sha256_file(path)})
        log(f"{range_name}/{run}: {record['result']['blocks']} blocks, {record['result']['changed_blocks']} changed")
    (records / "index.json").write_text(dump({"format": INDEX_FORMAT, "build": BUILD, "retained": RETAINED, "runs": entries}))
    write_sums(records)
    log(f"wrote {len(entries)} records under {records}")


def write_sums(records: Path) -> None:
    files = sorted(p.relative_to(records).as_posix() for p in records.rglob("*.json"))
    (records / "SHA256SUMS").write_text("".join(f"{sha256_file(records / f)}  {f}\n" for f in files))


def recheck_all(log) -> None:
    """Run the recheck of each saved response with `recheck_command`, and save the command beside its output."""
    for range_name, run in sorted(EXPECTED):
        command = recheck_command(range_name, run)
        out = Path(ROOT / f"build/impact/recheck/{range_name}/{run}")
        if out.exists():
            shutil.rmtree(out)
        result = subprocess.run(["nice", "-n", "19", *shlex.split(command)], cwd=ROOT, capture_output=True, text=True)
        if result.returncode != 0:
            raise RecordError(f"{range_name}/{run}: the recheck failed:\n{result.stdout}{result.stderr}")
        (out / "command.txt").write_text(command + "\n")
        log(f"{range_name}/{run}: recheck passed")


def check(records: Path, layout: Layout | None, log, sources: Sources | None = None) -> None:
    sources = sources or Sources()
    index = json.loads((records / "index.json").read_text())
    require(index.get("format") == INDEX_FORMAT and index.get("build") == BUILD and index.get("retained") == RETAINED,
            "index.json", "another format, build or retention")
    require(set(index) == {"format", "build", "retained", "runs"}, "index.json", "other keys")
    listed = [(e["range"], e["run"]) for e in index["runs"]]
    require(len(set(listed)) == len(listed), "index.json", "a run is named twice")
    if set(listed) != set(EXPECTED):
        differ = sorted(set(listed) ^ set(EXPECTED))
        raise RecordError(f"index.json does not list exactly the {len(EXPECTED)} expected runs: {len(differ)} differ, "
                          f"such as {differ[:3]}")
    files = {e["file"] for e in index["runs"]}
    present = {p.relative_to(records).as_posix() for p in records.rglob("*.json")} - {"index.json"}
    require(present == files, "records", f"records and index differ: {sorted(present ^ files)}")
    hashed: dict = {}
    for entry in index["runs"]:
        require(set(entry) == {"range", "run", "revision", "file", "sha256"}, entry["file"], "the index entry has other keys")
        require(entry["file"] == f"{entry['range']}/{entry['run']}.json", entry["file"], "not at the path of its range and run")
        require(entry["revision"] == EXPECTED[(entry["range"], entry["run"])], entry["file"],
                "the index names another revision or activation")
        path = records / entry["file"]
        require(sha256_file(path) == entry["sha256"], entry["file"], "not the SHA-256 of the index")
        record = json.loads(path.read_text())
        check_record(record, entry["range"], entry["run"], sources)
        if layout is not None:
            check_outputs(record, layout, hashed)
    sums = {}
    for line in (records / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        sums[name] = digest
    require(set(sums) == files | {"index.json"}, "SHA256SUMS", "it does not list exactly the index and the records")
    for name, digest in sums.items():
        require(sha256_file(records / name) == digest, name, "not its SHA-256 in SHA256SUMS")
    log(f"{len(files)} records agree with the expected runs, index.json and SHA256SUMS"
        + (f", and with the saved outputs under {layout.outputs}" if layout is not None else ""))


# The self-test.

def refresh(records: Path) -> None:
    """Give each index entry the SHA-256 of its record, and rewrite SHA256SUMS, so that only the planted fault is wrong."""
    index = json.loads((records / "index.json").read_text())
    for entry in index["runs"]:
        entry["sha256"] = sha256_file(records / entry["file"])
    (records / "index.json").write_text(dump(index))
    write_sums(records)


def made_world(root: Path) -> tuple[Layout, Sources]:
    """Saved outputs, candidate lists and snapshot manifests for the 51 expected runs, made small."""
    layout = Layout(root)
    sources = Sources(root / "lists", root / "manifests")
    sources.lists.mkdir(parents=True)
    sources.manifests.mkdir(parents=True)
    data = root / "data"
    data.mkdir()
    for index, range_name in enumerate((GENESIS, *SNAPSHOT_RANGES)):
        listing = json.loads((LISTS / f"{range_name}.json").read_text())
        blocks = data / f"{range_name}-blocks.bin"
        blocks.write_bytes(f"blocks of {range_name}".encode())
        listing["blocks_sha256"] = sha256_file(blocks)
        (sources.lists / f"{range_name}.json").write_text(dump(listing))
        request = {"blocks_file": str(blocks), "coins_file": None, "expected_end": hashlib.sha256(range_name.encode()).hexdigest()}
        if range_name != GENESIS:
            coins = data / listing["snapshot"]
            coins.write_bytes(f"coins of {range_name}".encode())
            request["coins_file"] = str(coins)
            if (MANIFESTS / f"{coins.stem}.json").exists():
                (sources.manifests / f"{coins.stem}.json").write_text(dump(file_entry(coins)))
            baseline = layout.baseline(range_name)
            baseline.parent.mkdir(parents=True, exist_ok=True)
            baseline.write_text(dump({"baseline": range_name}))
        layout.request(range_name).parent.mkdir(parents=True)
        layout.request(range_name).write_text(dump(request))
        for number, run in enumerate(RUN_NAMES):
            if (range_name, run) not in EXPECTED:
                continue
            revision = REVISION_OF_RUN[run]
            blocks_count = listing["last"] - listing["first"] + 1
            result = {"blocks": blocks_count, "candidate_blocks": listing["revisions"][revision["name"]]["candidate_blocks"],
                      "changed_blocks": 0, "unsupported": {}, "rejected_by_step": {},
                      "set_digest_hex": request["expected_end"], "set_coins": 1000 + index}
            summary = {"range": range_name, "revision": revision, "first": listing["first"], "last": listing["last"],
                       "blocks_sha256": listing["blocks_sha256"], "coins_file": listing.get("snapshot"),
                       "candidate_list": f"tests/proposals/impact/{range_name}.json",
                       "candidate_list_sha256": sha256_file(sources.lists / f"{range_name}.json"),
                       "proposal_oracle_sha256": EXECUTABLE["sha256"], "baseline_compared": range_name != GENESIS,
                       "seconds": 100 + number, **result}
            run_dir = layout.run_dir(range_name, run)
            run_dir.mkdir(parents=True)
            (run_dir / "summary.json").write_text(dump(summary))
            (run_dir / "report.json").write_text(dump({"changed": [], **{k: result[k] for k in REPORT_KEYS}}))
            (run_dir / "response.json").write_text(dump({"ok": {"blocks": [], "range": range_name, "run": run}}))
            layout.log(range_name, run).write_text(
                f"\tElapsed (wall clock) time (h:mm:ss or m:ss): 1:4{number}.50\n\tMaximum resident set size (kbytes): {2000 + number}\n")
            recheck_dir = layout.recheck_dir(range_name, run)
            recheck_dir.mkdir(parents=True)
            (recheck_dir / "summary.json").write_text(dump({**summary, "seconds": None}))
            (recheck_dir / "command.txt").write_text(recheck_command(range_name, run) + "\n")
    return layout, sources


def leaf_paths(schema, path=()):
    for key, inner in schema.items():
        if isinstance(inner, tuple):
            inner = inner[1]
        if isinstance(inner, dict):
            yield from leaf_paths(inner, path + (key,))
        else:
            yield path + (key,)


def mutated(value, path):
    """Another value of the same type for the field at PATH."""
    if path == ("time", "max_rss_kib"):
        return 1
    if isinstance(value, bool) or value is None:
        return 0
    if isinstance(value, int):
        return value + 1
    if isinstance(value, dict):
        return {"planted": 1}
    if HEX64.fullmatch(value):
        return ("1" if value[0] == "0" else "0") * 64
    if utc_time(value):
        return value[:-3] + ("00Z" if value[-3:] != "00Z" else "01Z")
    if clock(value):
        return "9" + value
    return value + "x"


def self_test() -> int:
    results = []

    def outcome(name: str, run) -> None:
        try:
            run()
        except (RecordError, OSError, ValueError, KeyError, TypeError) as error:
            print(f"ok: {name} fails ({error})")
            results.append(True)
            return
        print(f"FAIL: {name} passes")
        results.append(False)

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        layout, sources = made_world(root / "world")
        clean = root / "records"
        write(layout, clean, lambda _: None)
        try:
            check(clean, layout, print, sources)
        except RecordError as error:
            print(f"FAIL: the made records fail ({error})")
            return 1

        def planted(name: str, plant, with_outputs: bool = True) -> None:
            copy = root / "copy"
            if copy.exists():
                shutil.rmtree(copy)
            shutil.copytree(clean, copy)
            plant(copy)
            outcome(name, lambda: check(copy, layout if with_outputs else None, lambda _: None, sources))

        def edit(path: str, change):
            def plant(copy: Path) -> None:
                record = json.loads((copy / path).read_text())
                change(record)
                (copy / path).write_text(dump(record))
                refresh(copy)
            return plant

        def at(record: dict, path: tuple):
            for key in path:
                record = record[key]
            return record

        def set_at(record: dict, path: tuple, value) -> None:
            at(record, path[:-1])[path[-1]] = value

        snapshot_record = "A/RelativeLockTime-1.json"
        genesis_record = f"{GENESIS}/RelativeLockTime-1.json"
        # One changed value for each field, with the index and the sums refreshed.
        record = json.loads((clean / snapshot_record).read_text())
        for path in leaf_paths(RECORD_SCHEMA):
            value = mutated(at(record, path), path)
            planted(f"{'.'.join(path)} changed to {value!r}",
                    edit(snapshot_record, lambda r, path=path, value=value: set_at(r, path, value)))
        planted("a coins file on heights 0 to 145,000", edit(genesis_record, lambda r: r["inputs"].update(
            coins_file=json.loads((clean / snapshot_record).read_text())["inputs"]["coins_file"])))
        planted("a baseline on heights 0 to 145,000", edit(genesis_record, lambda r: r["inputs"].update(
            baseline_response={"sha256": "0" * 64, "bytes": 1})))
        # The fields that only a saved file checks fail without --outputs too, where a rule or a committed file holds them.
        for path in (("first",), ("inputs", "blocks_file", "sha256"), ("inputs", "candidate_list_sha256"),
                     ("result", "candidate_blocks"), ("recheck", "command")):
            value = mutated(at(record, path), path)
            planted(f"{'.'.join(path)} changed, without --outputs",
                    edit(snapshot_record, lambda r, path=path, value=value: set_at(r, path, value)), with_outputs=False)

        # One deleted key and one unknown key in each object.
        objects = [()] + [p for p in object_paths(RECORD_SCHEMA)]
        for path in objects:
            label = ".".join(path) or "the record"
            key = next(iter(at(record, path)))
            planted(f"{label} without {key}", edit(snapshot_record, lambda r, path=path, key=key: at(r, path).pop(key)))
            planted(f"{label} with an unknown key", edit(snapshot_record, lambda r, path=path: at(r, path).update(unknown=0)))
        planted("a result without candidate_blocks, unsupported, rejected_by_step and set_coins",
                edit(snapshot_record, lambda r: [r["result"].pop(k) for k in
                                                 ("candidate_blocks", "unsupported", "rejected_by_step", "set_coins")]))
        planted("a count that is a string", edit(snapshot_record, lambda r: r["result"].update(candidate_blocks="0")))
        planted("a time that is a Boolean", edit(snapshot_record, lambda r: r["time"].update(seconds=True)))

        # The inventory, the index and the sums.
        def edit_index(change):
            def plant(copy: Path) -> None:
                index = json.loads((copy / "index.json").read_text())
                change(index, copy)
                (copy / "index.json").write_text(dump(index))
                refresh(copy)
            return plant

        def drop(file: str):
            def change(index, copy):
                (copy / file).unlink()
                index["runs"] = [e for e in index["runs"] if e["file"] != file]
            return change

        def empty(index, copy):
            for entry in index["runs"]:
                (copy / entry["file"]).unlink()
            index["runs"] = []

        planted("the record and entry of heights 0 to 145,000 deleted together", edit_index(drop(genesis_record)))
        planted("an empty inventory", edit_index(empty))
        planted("an index entry with another activation", edit_index(
            lambda index, copy: index["runs"][0]["revision"].update(activation_height=7)))
        planted("an index with an unknown key", edit_index(lambda index, copy: index.update(unknown=0)))
        planted("a changed record without new hashes", lambda c: (c / snapshot_record).write_text(
            (c / snapshot_record).read_text().replace('"changed_blocks": 0', '"changed_blocks": 1', 1)))
        planted("an extra record", lambda c: (c / "A" / "extra.json").write_text((c / snapshot_record).read_text()))
        planted("a changed SHA256SUMS", lambda c: (c / "SHA256SUMS").write_text(
            (c / "SHA256SUMS").read_text().replace("0", "1", 1)))

        # Saved files that differ from the records.
        def saved(name: str, path: Path, change):
            def run() -> None:
                kept, stat = path.read_bytes(), path.stat()
                change(path)
                try:
                    check(clean, layout, lambda _: None, sources)
                finally:
                    path.write_bytes(kept)
                    os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
            outcome(name, run)

        run_dir = layout.run_dir("A", "RelativeLockTime-1")
        for name in ("response", "report", "summary"):
            saved(f"a changed saved {name}", run_dir / f"{name}.json", lambda p: p.write_text("{}"))
        saved("a log with another memory", layout.log("A", "RelativeLockTime-1"),
              lambda p: p.write_text(p.read_text().replace("Maximum resident set size (kbytes): ", "Maximum resident set size (kbytes): 9")))
        saved("a log with another time", layout.log("A", "RelativeLockTime-1"), lambda p: p.write_text(p.read_text().replace("1:4", "2:4")))
        saved("a log without measurements", layout.log("A", "RelativeLockTime-1"), lambda p: p.write_text(""))
        saved("a changed saved recheck command", layout.recheck_dir("A", "RelativeLockTime-1") / "command.txt",
              lambda p: p.write_text(p.read_text().replace("--activation 1", "--activation 2")))
        saved("a changed saved recheck", layout.recheck_dir("A", "RelativeLockTime-1") / "summary.json", lambda p: p.write_text("{}"))
        saved("a changed saved request", layout.request("A"), lambda p: p.write_text("{}"))
        saved("a changed baseline", layout.baseline("A"), lambda p: p.write_text("{}"))
        saved("a changed blocks file", root / "world" / "data" / "A-blocks.bin", lambda p: p.write_bytes(b"other"))
        saved("a changed coins file", root / "world" / "data" / "coins-145000.bin", lambda p: p.write_bytes(b"other"))

        def touch(path: Path) -> None:
            stat = path.stat()
            os.utime(path, (stat.st_atime, stat.st_mtime + 3600))
        saved("a run summary with another modification time", run_dir / "summary.json", touch)
        outcome("a missing directory of saved outputs", lambda: check(clean, Layout(root / "absent"), lambda _: None, sources))
    return 0 if all(results) else 1


def object_paths(schema, path=()):
    for key, inner in schema.items():
        if isinstance(inner, tuple):
            inner = inner[1]
        if isinstance(inner, dict):
            yield path + (key,)
            yield from object_paths(inner, path + (key,))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", nargs="?", choices=["write", "recheck"])
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--outputs", metavar="DIR", help="the saved outputs, build/impact")
    args = parser.parse_args(argv)
    try:
        if args.self_test:
            return self_test()
        if args.command == "recheck":
            recheck_all(print)
            return 0
        if args.command == "write":
            write(Layout(ROOT), RECORDS, print)
            return 0
        if args.check:
            check(RECORDS, Layout(Path(args.outputs).resolve().parent.parent) if args.outputs else None, print)
            return 0
        parser.error("give recheck, write, --check or --self-test")
    except (RecordError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
