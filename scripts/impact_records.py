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

`--check` requires the 51 expected runs, which the script states without the index: the five runs
of each of the ten ranges from a snapshot, and `RelativeLockTime` from height 1 on heights 0 to
145,000. The index must name each once, with the revision and activation of the run and the
SHA-256 of its record. Each record must have the response, the report and the summary, and its
inputs and recheck, each with a SHA-256 and a size above 0, and an end digest equal to the expected
end of its request. Each object of a record, at every level, has exactly the keys of
`RECORD_SCHEMA`, and each value passes the test of its type. `SHA256SUMS` must list exactly the index and the records, with their SHA-256.
With `--outputs DIR`, each saved file of a run must exist under DIR with the SHA-256 and size of its
record: the response, report, summary, request, recheck, blocks file, coins file and baseline. The
counts, digest and block count of each saved summary must equal the record. The check runs no
DogeLib code and reads no network.

`--self-test` plants faults in a copy of the records, after which the index and the sums are made
to agree with the planted copy. It also plants faults in a made directory of saved outputs for
one run. `--check` must fail on each.
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


# The runs that the records must cover, independently of the index: the five runs of each range
# from a snapshot, and RelativeLockTime from height 1 on heights 0 to 145,000.
REVISION_OF_RUN = {
    "ExampleVersionVerify-none": {"name": "ExampleVersionVerify", "variant": None, "activation_height": None},
    "ExampleVersionVerify-0": {"name": "ExampleVersionVerify", "variant": None, "activation_height": 0},
    "ExampleFaultyLocktime-corrected-none": {"name": "ExampleFaultyLocktime", "variant": "corrected", "activation_height": None},
    "ExampleFaultyLocktime-corrected-0": {"name": "ExampleFaultyLocktime", "variant": "corrected", "activation_height": 0},
    "RelativeLockTime-1": {"name": "RelativeLockTime", "variant": None, "activation_height": 1},
}
SNAPSHOT_RANGES = ("short", "S", "A", "B", "C", "D", "E1", "E2", "F", "H")
EXPECTED = {(r, run): REVISION_OF_RUN[run] for r in SNAPSHOT_RANGES for run in RUN_NAMES}
EXPECTED[("genesis-145000", "RelativeLockTime-1")] = REVISION_OF_RUN["RelativeLockTime-1"]
OUTPUT_NAMES = ("response", "report", "summary")
HEX64 = re.compile(r"[0-9a-f]{64}")


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


def counts(value) -> bool:
    """A map from a reason or a step to a count, as `unsupported` and `rejected_by_step` are."""
    return isinstance(value, dict) and all(isinstance(k, str) and positive(v) for k, v in value.items())


def optional(schema):
    return ("optional", schema)


# The exact key set of each object of `dogelib-impact-run/1`. A value is a test of a leaf, a nested
# schema, or `optional(...)` for a value that may be null.
ENTRY = {"sha256": hex64, "bytes": positive}
COINS_ENTRY = {"name": text, "sha256": hex64, "bytes": positive}
RECORD_SCHEMA = {
    "format": text,
    "range": text,
    "run": text,
    "first": natural,
    "last": natural,
    "revision": {"name": text, "variant": optional(text), "activation_height": optional(natural)},
    "executable": {"name": text, "sha256": hex64, "commit": text},
    "inputs": {
        "request": ENTRY,
        "blocks_file": ENTRY,
        "coins_file": optional(COINS_ENTRY),
        "expected_end": hex64,
        "candidate_list": text,
        "candidate_list_sha256": hex64,
        "baseline_response": optional(ENTRY),
    },
    "outputs": {"response": ENTRY, "report": ENTRY, "summary": ENTRY},
    "result": {
        "blocks": positive,
        "candidate_blocks": natural,
        "changed_blocks": natural,
        "unsupported": counts,
        "rejected_by_step": counts,
        "set_digest_hex": hex64,
        "set_coins": natural,
    },
    "time": {"seconds": positive, "max_rss_kib": positive, "finished_utc": utc_time},
    "recheck": {"command": text, "summary": ENTRY, "changed_blocks": natural},
}
RESULT_KEYS = tuple(RECORD_SCHEMA["result"])


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


def check_record(record: dict, range_name: str, run: str) -> None:
    """The record has the schema of `dogelib-impact-run/1`, and the values of its run."""
    where = f"{range_name}/{run}"
    check_schema(record, RECORD_SCHEMA, where)
    if (record["format"], record["range"], record["run"]) != (RUN_FORMAT, range_name, run):
        raise RecordError(f"{where}: the record has another format, range or run")
    if record["revision"] != EXPECTED[(range_name, run)]:
        raise RecordError(f"{where}: the record has another revision or activation")
    if record["executable"] != {"name": "dogelib-proposal-oracle", "sha256": BUILD["dogelib-proposal-oracle_sha256"],
                                "commit": BUILD["commit"]}:
        raise RecordError(f"{where}: the record names another executable")
    inputs = record["inputs"]
    from_genesis = range_name == "genesis-145000"
    for name in ("coins_file", "baseline_response"):
        if (inputs[name] is None) != from_genesis:
            raise RecordError(f"{where}: the {name} does not fit a range {'from the empty set' if from_genesis else 'from a snapshot'}")
    if inputs["candidate_list"] != f"tests/proposals/impact/{range_name}.json":
        raise RecordError(f"{where}: the candidate list is not the list of the range")
    result = record["result"]
    if result["set_digest_hex"] != inputs["expected_end"] or result["blocks"] != record["last"] - record["first"] + 1:
        raise RecordError(f"{where}: the result has another end digest or block count")
    if result["changed_blocks"] != record["recheck"]["changed_blocks"]:
        raise RecordError(f"{where}: the recheck differs from the run")


def check_outputs(record: dict, outputs: Path, hashed: dict) -> None:
    """The saved files of one run under OUTPUTS have the hashes of the record, and agree with its result."""
    where = f"{record['range']}/{record['run']}"
    if not outputs.is_dir():
        raise RecordError(f"{outputs} is not a directory of saved outputs")
    run_dir = outputs / "runs" / record["range"] / record["run"]
    for name in OUTPUT_NAMES:
        path = run_dir / f"{name}.json"
        if not path.is_file() or file_entry(path) != record["outputs"][name]:
            raise RecordError(f"{where}: the saved {name}.json is missing or differs from the record")
    summary = json.loads((run_dir / "summary.json").read_text())
    for key in RESULT_KEYS:
        if key not in summary or summary[key] != record["result"][key]:
            raise RecordError(f"{where}: the saved summary differs from the record in {key}")
    if json.loads((run_dir / "report.json").read_text()).get("changed_blocks") != record["result"]["changed_blocks"]:
        raise RecordError(f"{where}: the saved report differs from the record in changed_blocks")
    pairs = [(summary.get("first"), record["first"]), (summary.get("last"), record["last"]),
             (summary.get("revision"), record["revision"]), (summary.get("seconds"), record["time"]["seconds"]),
             (summary.get("proposal_oracle_sha256"), record["executable"]["sha256"]),
             (summary.get("blocks_sha256"), record["inputs"]["blocks_file"]["sha256"]),
             (summary.get("candidate_list_sha256"), record["inputs"]["candidate_list_sha256"])]
    if any(a != b for a, b in pairs):
        raise RecordError(f"{where}: the saved summary differs from the record")
    request_path = outputs / "requests" / record["range"] / "request.json"
    if not request_path.is_file() or file_entry(request_path) != record["inputs"]["request"]:
        raise RecordError(f"{where}: the saved request is missing or differs from the record")
    request = json.loads(request_path.read_text())
    if request.get("expected_end") != record["inputs"]["expected_end"]:
        raise RecordError(f"{where}: the saved request has another expected end")

    def cached(path: Path) -> dict:
        key = str(path.resolve())
        if key not in hashed:
            hashed[key] = file_entry(path)
        return hashed[key]

    if cached(Path(request["blocks_file"])) != record["inputs"]["blocks_file"]:
        raise RecordError(f"{where}: the blocks file differs from the record")
    coins = record["inputs"]["coins_file"]
    if (coins is None) != (request.get("coins_file") is None) or (
            coins is not None and {"name": Path(request["coins_file"]).name, **cached(Path(request["coins_file"]))} != coins):
        raise RecordError(f"{where}: the coins file differs from the record")
    baseline = baseline_path(outputs, record["range"], request, summary)
    if (None if baseline is None else cached(baseline)) != record["inputs"]["baseline_response"]:
        raise RecordError(f"{where}: the baseline response differs from the record")
    recheck_path = outputs / "recheck" / record["range"] / record["run"] / "summary.json"
    if not recheck_path.is_file() or file_entry(recheck_path) != record["recheck"]["summary"]:
        raise RecordError(f"{where}: the saved recheck is missing or differs from the record")
    if json.loads(recheck_path.read_text()).get("changed_blocks") != record["recheck"]["changed_blocks"]:
        raise RecordError(f"{where}: the saved recheck differs from the record")


def check(records: Path, outputs: Path | None, log) -> None:
    index = json.loads((records / "index.json").read_text())
    if index.get("format") != INDEX_FORMAT or index.get("build") != BUILD:
        raise RecordError("index.json has another format or build")
    listed = [(e["range"], e["run"]) for e in index["runs"]]
    if len(set(listed)) != len(listed):
        raise RecordError("index.json names a run twice")
    if set(listed) != set(EXPECTED):
        differ = sorted(set(listed) ^ set(EXPECTED))
        raise RecordError(f"index.json does not list exactly the {len(EXPECTED)} expected runs: {len(differ)} differ, "
                          f"such as {differ[:3]}")
    files = {e["file"] for e in index["runs"]}
    present = {p.relative_to(records).as_posix() for p in records.rglob("*.json")} - {"index.json"}
    if present != files:
        raise RecordError(f"records and index differ: {sorted(present ^ files)}")
    hashed: dict = {}
    for entry in index["runs"]:
        if entry["file"] != f"{entry['range']}/{entry['run']}.json":
            raise RecordError(f"{entry['file']} is not at the path of its range and run")
        if entry["revision"] != EXPECTED[(entry["range"], entry["run"])]:
            raise RecordError(f"{entry['file']}: the index names another revision or activation")
        path = records / entry["file"]
        if sha256_file(path) != entry["sha256"]:
            raise RecordError(f"{entry['file']} does not have the SHA-256 of the index")
        record = json.loads(path.read_text())
        check_record(record, entry["range"], entry["run"])
        if outputs is not None:
            check_outputs(record, outputs, hashed)
    sums = {}
    for line in (records / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        sums[name] = digest
    if set(sums) != files | {"index.json"}:
        raise RecordError("SHA256SUMS does not list exactly the index and the records")
    for name, digest in sums.items():
        if sha256_file(records / name) != digest:
            raise RecordError(f"{name} does not have its SHA-256 in SHA256SUMS")
    log(f"{len(files)} records agree with the expected runs, index.json and SHA256SUMS"
        + (f", and with the saved outputs under {outputs}" if outputs is not None else ""))


def refresh(copy: Path) -> None:
    """Give each index entry the SHA-256 of its record, and rewrite SHA256SUMS, so that only the planted fault is wrong."""
    index = json.loads((copy / "index.json").read_text())
    for entry in index["runs"]:
        entry["sha256"] = sha256_file(copy / entry["file"])
    (copy / "index.json").write_text(dump(index))
    write_sums(copy)


def made_outputs(root: Path) -> tuple[Path, dict]:
    """A made directory of saved outputs for one run of the short range, and its record."""
    outputs = root / "impact"
    run_dir = outputs / "runs" / "short" / "RelativeLockTime-1"
    run_dir.mkdir(parents=True)
    (outputs / "requests" / "short").mkdir(parents=True)
    (outputs / "recheck" / "short" / "RelativeLockTime-1").mkdir(parents=True)
    blocks, coins = root / "blocks.bin", root / "coins-9000.bin"
    blocks.write_bytes(b"made blocks")
    coins.write_bytes(b"made coins")
    digest = "ab" * 32
    (outputs / "requests" / "short" / "request.json").write_text(dump(
        {"blocks_file": str(blocks), "coins_file": str(coins), "expected_end": digest}))
    summary = {"range": "short", "revision": REVISION_OF_RUN["RelativeLockTime-1"], "first": 9001, "last": 9002,
               "blocks_sha256": sha256_file(blocks), "coins_file": coins.name, "candidate_list": "tests/proposals/impact/short.json",
               "candidate_list_sha256": "cd" * 32, "proposal_oracle_sha256": BUILD["dogelib-proposal-oracle_sha256"],
               "baseline_compared": True, "set_digest_hex": digest, "set_coins": 5, "seconds": 3, "blocks": 2,
               "candidate_blocks": 0, "changed_blocks": 0, "unsupported": {}, "rejected_by_step": {}}
    (run_dir / "summary.json").write_text(dump(summary))
    (run_dir / "report.json").write_text(dump({"changed": [], "blocks": 2, "changed_blocks": 0}))
    (run_dir / "response.json").write_text(dump({"ok": {"blocks": []}}))
    (outputs / "runs" / "short" / "RelativeLockTime-1.log").write_text("\tMaximum resident set size (kbytes): 1000\n")
    (outputs / "runs" / "short" / "baseline-response.json").write_text(dump({"ok": {}}))
    (outputs / "recheck" / "short" / "RelativeLockTime-1" / "summary.json").write_text(dump(summary))
    return outputs, run_record(outputs, "short", "RelativeLockTime-1", {})


def self_test(records: Path) -> int:
    clean = True
    try:
        check(records, None, print)
    except RecordError as error:
        print(f"FAIL: the committed records fail ({error})")
        clean = False

    def outcome(name: str, run) -> bool:
        try:
            run()
        except (RecordError, OSError, ValueError, KeyError, TypeError) as error:
            print(f"ok: {name} fails ({error})")
            return True
        print(f"FAIL: {name} passes")
        return False

    def planted(name: str, plant) -> bool:
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "runs"
            shutil.copytree(records, copy)
            plant(copy)
            return outcome(name, lambda: check(copy, None, lambda _: None))

    first = "A/ExampleFaultyLocktime-corrected-0.json"
    genesis = "genesis-145000/RelativeLockTime-1.json"

    def edit_record(copy: Path, change, path: str = first) -> None:
        record = json.loads((copy / path).read_text())
        change(record)
        (copy / path).write_text(dump(record))

    def edit_index(copy: Path, change) -> None:
        index = json.loads((copy / "index.json").read_text())
        change(index)
        (copy / "index.json").write_text(dump(index))

    def coherent(plant):
        def run(copy: Path) -> None:
            plant(copy)
            refresh(copy)
        return run

    def delete_genesis(copy: Path) -> None:
        (copy / genesis).unlink()
        edit_index(copy, lambda i: i.update(runs=[e for e in i["runs"] if e["file"] != genesis]))

    def empty(copy: Path) -> None:
        for path in list(copy.rglob("*.json")):
            if path.name != "index.json":
                path.unlink()
        edit_index(copy, lambda i: i.update(runs=[]))

    def other_activation(copy: Path) -> None:
        edit_record(copy, lambda r: r["revision"].update(activation_height=2))
        edit_index(copy, lambda i: [e["revision"].update(activation_height=2) for e in i["runs"] if e["file"] == first])

    cases = [
        ("a changed record", lambda c: edit_record(c, lambda r: r["result"].update(changed_blocks=1))),
        ("a changed record with a new index and sums", coherent(lambda c: edit_record(c, lambda r: r["result"].update(changed_blocks=1)))),
        ("a missing record", lambda c: (c / first).unlink()),
        ("an extra record", lambda c: (c / first).with_name("extra.json").write_text((c / first).read_text())),
        ("an index without an entry", coherent(lambda c: edit_index(c, lambda i: i["runs"].pop()))),
        ("the record and entry of heights 0 to 145,000 deleted together", coherent(delete_genesis)),
        ("an empty inventory", coherent(empty)),
        ("another activation in the record and the index", coherent(other_activation)),
        ("a record of another executable", coherent(lambda c: edit_record(c, lambda r: r["executable"].update(sha256="0" * 64)))),
        ("empty outputs", coherent(lambda c: edit_record(c, lambda r: r.update(outputs={})))),
        ("outputs without the report", coherent(lambda c: edit_record(c, lambda r: r["outputs"].pop("report")))),
        ("an output hash that is not a SHA-256", coherent(lambda c: edit_record(c, lambda r: r["outputs"]["response"].update(sha256="xyz")))),
        ("an output of size 0", coherent(lambda c: edit_record(c, lambda r: r["outputs"]["summary"].update(bytes=0)))),
        ("a missing request hash", coherent(lambda c: edit_record(c, lambda r: r["inputs"].update(request=None)))),
        ("a range from a snapshot without coins", coherent(lambda c: edit_record(c, lambda r: r["inputs"].update(coins_file=None)))),
        ("an end digest other than the expected end", coherent(lambda c: edit_record(c, lambda r: r["result"].update(set_digest_hex="0" * 64)))),
        ("a changed SHA256SUMS", lambda c: (c / "SHA256SUMS").write_text((c / "SHA256SUMS").read_text().replace("0", "1", 1))),
    ]

    def at(record: dict, path: tuple) -> dict:
        for key in path:
            record = record[key]
        return record

    # For each object of the schema: a required key deleted, and an unknown key added.
    objects = [((), "result"), (("revision",), "activation_height"), (("executable",), "commit"),
               (("inputs",), "expected_end"), (("inputs", "request"), "bytes"), (("inputs", "coins_file"), "name"),
               (("inputs", "baseline_response"), "sha256"), (("outputs",), "report"), (("outputs", "response"), "sha256"),
               (("result",), "set_coins"), (("time",), "max_rss_kib"), (("recheck",), "summary"),
               (("recheck", "summary"), "bytes")]
    for path, key in objects:
        label = ".".join(path) or "the record"
        cases.append((f"{label} without {key}",
                      coherent(lambda c, path=path, key=key: edit_record(c, lambda r: at(r, path).pop(key)))))
        cases.append((f"{label} with an unknown key",
                      coherent(lambda c, path=path: edit_record(c, lambda r: at(r, path).update(unknown=0)))))
    cases.append(("a result without candidate_blocks, unsupported, rejected_by_step and set_coins",
                  coherent(lambda c: edit_record(c, lambda r: [r["result"].pop(k) for k in
                                                               ("candidate_blocks", "unsupported", "rejected_by_step", "set_coins")]))))
    cases.append(("a count that is not a number", coherent(lambda c: edit_record(c, lambda r: r["result"].update(candidate_blocks="0")))))
    cases.append(("a time that is a Boolean", coherent(lambda c: edit_record(c, lambda r: r["time"].update(seconds=True)))))
    results = [planted(name, plant) for name, plant in cases]

    # The check of saved outputs, on a made directory for one run.
    with tempfile.TemporaryDirectory() as tmp:
        outputs, record = made_outputs(Path(tmp))
        try:
            check_record(record, "short", "RelativeLockTime-1")
            check_outputs(record, outputs, {})
            print("ok: the made outputs agree with their record")
        except RecordError as error:
            print(f"FAIL: the made outputs fail ({error})")
            clean = False
        run_dir = outputs / "runs" / "short" / "RelativeLockTime-1"

        def changed_file(path: Path, text: str):
            def run() -> None:
                saved = path.read_text()
                path.write_text(text)
                try:
                    check_outputs(record, outputs, {})
                finally:
                    path.write_text(saved)
            return run

        def changed_summary_drop(key: str):
            summary = json.loads((run_dir / "summary.json").read_text())
            summary.pop(key)
            return replaced_summary(dump(summary))

        def changed_summary(key: str, value):
            summary = json.loads((run_dir / "summary.json").read_text())
            summary[key] = value
            return replaced_summary(dump(summary))

        def replaced_summary(changed: str):
            # The record follows the new summary file, so that only the field comparison can fail.
            def run() -> None:
                saved = (run_dir / "summary.json").read_text()
                (run_dir / "summary.json").write_text(changed)
                kept = record["outputs"]["summary"]
                record["outputs"]["summary"] = file_entry(run_dir / "summary.json")
                try:
                    check_outputs(record, outputs, {})
                finally:
                    (run_dir / "summary.json").write_text(saved)
                    record["outputs"]["summary"] = kept
            return run

        output_cases = [
            ("a missing outputs directory", lambda: check_outputs(record, Path(tmp) / "absent", {})),
            ("a missing saved summary", missing(run_dir / "summary.json", lambda: check_outputs(record, outputs, {}))),
            ("a changed saved response", changed_file(run_dir / "response.json", "{}")),
            ("a changed saved request", changed_file(outputs / "requests" / "short" / "request.json", "{}")),
            ("a changed saved recheck", changed_file(outputs / "recheck" / "short" / "RelativeLockTime-1" / "summary.json", "{}")),
            ("a changed blocks file", changed_file(Path(tmp) / "blocks.bin", "other blocks")),
            ("a changed coins file", changed_file(Path(tmp) / "coins-9000.bin", "other coins")),
            ("a changed baseline", changed_file(outputs / "runs" / "short" / "baseline-response.json", "{}")),
            ("a saved summary with another count", changed_summary("changed_blocks", 1)),
            ("a saved summary with another digest", changed_summary("set_digest_hex", "0" * 64)),
            ("a saved summary with another block count", changed_summary("blocks", 3)),
            ("a saved summary with another blocks hash", changed_summary("blocks_sha256", "0" * 64)),
            ("a saved summary without set_coins", changed_summary_drop("set_coins")),
            ("a changed saved report", changed_file(run_dir / "report.json", "{}")),
        ]
        results += [outcome(name, run) for name, run in output_cases]
    return 0 if clean and all(results) else 1


def missing(path: Path, run):
    """Run with PATH moved away, and put it back."""
    def go() -> None:
        moved = path.with_name(path.name + ".moved")
        path.rename(moved)
        try:
            run()
        finally:
            moved.rename(path)
    return go


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
