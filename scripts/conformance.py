#!/usr/bin/env python3
"""Build, fetch and compare the conformance corpus of design record 0011, stage 5.

Usage:
  python3 -I scripts/conformance.py request --range NAME --source FILE --snapshot FILE --fixture DIR --output DIR
  python3 -I scripts/conformance.py pack --work DIR --assets DIR
  python3 -I scripts/conformance.py fetch [--assets DIR] [--output DIR] [NAME ...]
  python3 -I scripts/conformance.py compare [--range NAME [--dir DIR] [--recorded FILE]] [--write-expected]
      <dogelib-oracle> <core-oracle>
  python3 -I scripts/conformance.py record --work DIR --commit COMMIT --date DATE --harness-build DIR

docs/conformance.md defines the formats. The ranges of the corpus are the short range of stage 1
and A, B, C, D, E1, E2, F and H. `RANGES` below gives the heights of each range and the height of
the snapshot at its start, whose manifest is committed in tests/block/mainnet-blocks/snapshots.

`request` writes the range request of one range to `DIR/request.json`, and its block fixture to
`DIR/fixture`. FILE of `--source` is a request of `scripts/impact_run.py request` for the range,
with `coins_file` and `blocks_file`: it gives the chain context. The blocks of `--fixture` must
have the SHA-256 of its `blocks_file`, after the cut to the heights of the range. The snapshot
must have the size and the SHA-256 of its committed manifest, and the first block must name the
block of the manifest. The coins of the request are the restricted coins: each coin of the
snapshot whose transaction ID the blocks name (scripts/restrict_coins.py). The request has the
keys of `REQUEST_KEYS`, and no `version_bits_heights`.

`pack` writes the three assets of each range under `--work` to `--assets`, compressed with xz,
and writes `tests/conformance/release.json`.

`fetch` restores each range of `release.json` to `DIR/<name>`, by default `build/conformance`:
`fixture/` with `blocks.bin`, `manifest.json` and `SHA256SUMS`, and `request.json`. It downloads
each asset without credentials, or reads it from `--assets DIR`. Each asset and each file must
have the committed size and SHA-256, and the fixture must pass every check of
`scripts/fetch_blocks.py --check`.

`compare` runs `scripts/range_results.py` on one range in both programs, or on each range in turn
without `--range`. `DIR` is `build/conformance/<name>` by default, as `fetch` writes it. The two `block.validate`
responses must agree as the full comparison requires, and the checker must pass on the oracle's
results against the harness's results. With `--recorded`, a `range-oracle-response.json` of
scripts/run_range.py, the block records must equal those of that run on the whole coin set,
without the fields of the whole set; records of other heights in FILE are left out. With `--write-expected`, the harness's results become
`tests/conformance/ranges/<name>/expected.jsonl`.

`record` writes `tests/generators.toml` and `tests/conformance/SHA256SUMS` from the file
`compare.json` that `compare` wrote in `DIR/<name>` for each range. Each expected-results file
must have the SHA-256 of the harness's results of that run. COMMIT is the DogeLib commit of the
sources of both programs, and `--harness-build` is the build directory of the harness, whose
`core.stamp` names the Core commit and the build.
"""

import argparse
import hashlib
import json
import lzma
import shutil
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import check_range_results  # noqa: E402
import fetch_blocks as fb  # noqa: E402
import fetch_release_blocks as frb  # noqa: E402
import oracle_block_validate as validate  # noqa: E402
import range_results  # noqa: E402
import restrict_coins  # noqa: E402
from compare_range import records_sha256  # noqa: E402

FORMAT = "dogelib-corpus-assets/1"
CORPUS = ROOT / "tests/conformance"
RELEASE_FILE = CORPUS / "release.json"
SNAPSHOTS = ROOT / "tests/block/mainnet-blocks/snapshots"
DEFAULT_OUTPUT = ROOT / "build/conformance"
REQUEST_FILE = "request.json"
FILES = (fb.BLOCKS_FILE, fb.MANIFEST_FILE, REQUEST_FILE)
REQUEST_KEYS = ("op", "mode", "check_pow", "check_merkle_root", "adjusted_time", "chain", "bip34_ancestor_hex", "coins")

# name: (first height, last height); the snapshot of the start is at first - 1.
RANGES = {
    "short": (9001, 10000),
    "A": (145001, 155000),
    "B": (370337, 372336),
    "C": (599000, 600999),
    "D": (1033383, 1035382),
    "E1": (1198520, 1200519),
    "E2": (1702520, 1704519),
    "F": (3463751, 3465750),
    "H": (5049001, 5050000),
}


class CorpusError(Exception):
    """A changed input, a malformed release file or a disagreement."""


def snapshot_manifest(name: str) -> dict:
    return json.loads((SNAPSHOTS / f"coins-{RANGES[name][0] - 1}.json").read_text())


def cut_fixture(source: Path, first: int, last: int, output: Path, pins: fb.Pins) -> fb.Verifier:
    """Write the blocks of heights `first` to `last` of a fixture as a new fixture, and check it."""
    head = json.loads((source / fb.MANIFEST_FILE).read_text())
    output.mkdir(parents=True, exist_ok=True)
    verifier = fb.Verifier(pins)
    with open(output / fb.BLOCKS_FILE, "wb") as out:
        for height, raw in fb.read_blocks(source / fb.BLOCKS_FILE):
            if first <= height <= last:
                verifier.add(height, raw)
                out.write(height.to_bytes(4, "little") + len(raw).to_bytes(4, "little") + raw)
    manifest = {key: value for key, value in head.items() if key not in ("count", "bytes", "runs", "pinned_by", "blocks")}
    manifest.update(first=first, last=last, **verifier.derived())
    text = fb.manifest_text(manifest).encode()
    fb.write_atomic(output / fb.MANIFEST_FILE, text)
    sums = "".join(f"{frb.sha256_file(output / name)}  {name}\n" for name in (fb.BLOCKS_FILE, fb.MANIFEST_FILE))
    fb.write_atomic(output / fb.SUMS_FILE, sums.encode())
    return fb.check_fixture(output, pins)


def build_request(name: str, source: Path, snapshot: Path, fixture: Path, output: Path, log=print) -> dict:
    first, last = RANGES[name]
    pins = fb.Pins.load()
    manifest = snapshot_manifest(name)
    request = json.loads(source.read_text())
    verifier = cut_fixture(fixture, first, last, output / "fixture", pins)
    heights = [block["height"] for block in verifier.blocks]
    if heights != list(range(first, last + 1)):
        raise CorpusError(f"the fixture does not hold every height from {first} to {last}")
    blocks = output / "fixture" / fb.BLOCKS_FILE
    if frb.sha256_file(blocks) != frb.sha256_file(Path(request["blocks_file"])):
        raise CorpusError(f"the blocks of {fixture} are not the blocks of the source request")
    first_block = next(fb.read_blocks(blocks))[1]
    if first_block[4:36].hex() != manifest["block_hash_hex"]:
        raise CorpusError("the first block does not name the block of the snapshot's manifest")
    missing = [key for key in REQUEST_KEYS if key != "coins" and key not in request]
    if missing:
        raise CorpusError(f"the source request lacks {missing}")
    ids = restrict_coins.named_ids(blocks)
    coins, count = restrict_coins.restricted(snapshot, ids, manifest["bytes"], manifest["sha256"])
    out = {key: request[key] for key in REQUEST_KEYS if key != "coins"}
    out["coins"] = coins
    (output / REQUEST_FILE).write_text(json.dumps(out, separators=(",", ":")) + "\n")
    log(f"range {name}: {len(heights)} blocks, {len(ids)} named transaction IDs, {len(coins)} of them with "
        f"{count} coins of the {manifest['coins']} of the snapshot; request {frb.sha256_file(output / REQUEST_FILE)}")
    return out


def pack(work: Path, assets: Path, log=print) -> dict:
    assets.mkdir(parents=True, exist_ok=True)
    entries = []
    for name, (first, last) in RANGES.items():
        directory = work / name
        verifier = fb.check_fixture(directory / "fixture", fb.Pins.load())
        if [b["height"] for b in verifier.blocks] != list(range(first, last + 1)):
            raise CorpusError(f"{directory}: the fixture does not hold heights {first} to {last}")
        files = {}
        for file_name in FILES:
            path = directory / ("fixture" if file_name != REQUEST_FILE else "") / file_name
            content = path.read_bytes()
            data = lzma.compress(content, format=lzma.FORMAT_XZ, preset=9 | lzma.PRESET_EXTREME)
            asset = f"conformance-{name}-{first}-{last}.{file_name}.xz"
            fb.write_atomic(assets / asset, data)
            files[file_name] = {"asset": asset, "asset_bytes": len(data), "asset_sha256": hashlib.sha256(data).hexdigest(),
                                "bytes": len(content), "sha256": hashlib.sha256(content).hexdigest()}
            log(f"{asset}: {len(data)} bytes")
        entries.append({"name": name, "first": first, "last": last, "blocks": last - first + 1, "files": files})
    return entries


def load_release(path: Path = RELEASE_FILE) -> dict:
    """Read and validate `release.json` of the corpus."""
    try:
        release = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise CorpusError(f"{path}: cannot read: {type(error).__name__}") from None
    if not isinstance(release, dict) or release.get("format") != FORMAT:
        raise CorpusError(f"{path}: the format is not {FORMAT}")
    repository, tag, ranges = release.get("repository"), release.get("tag"), release.get("ranges")
    if (not isinstance(repository, str) or len(repository.split("/")) != 2
            or not all(frb.is_name(part) for part in repository.split("/")) or not frb.is_name(tag)):
        raise CorpusError(f"{path}: malformed repository or tag")
    if not isinstance(ranges, list) or [e.get("name") if isinstance(e, dict) else None for e in ranges] != list(RANGES):
        raise CorpusError(f"{path}: the ranges are not {', '.join(RANGES)}, in that order")
    for entry in ranges:
        first, last = RANGES[entry["name"]]
        if ([entry.get("first"), entry.get("last"), entry.get("blocks")] != [first, last, last - first + 1]
                or not isinstance(entry.get("files"), dict) or sorted(entry["files"]) != sorted(FILES)):
            raise CorpusError(f"{path}: malformed range entry {entry['name']}")
        for record in entry["files"].values():
            if (not isinstance(record, dict) or not frb.is_name(record.get("asset"))
                    or not frb.is_count(record.get("bytes")) or not frb.is_count(record.get("asset_bytes"))
                    or not frb.is_sha256(record.get("sha256")) or not frb.is_sha256(record.get("asset_sha256"))):
                raise CorpusError(f"{path}: malformed file record in the range {entry['name']}")
    return release


def fetch(release: dict, output: Path, names: list[str], assets: Path | None = None, fetcher=frb.download,
          timeout: float = 120.0, log=print) -> None:
    pins = fb.Pins.load()
    for entry in release["ranges"]:
        if names and entry["name"] not in names:
            continue
        directory = output / entry["name"]
        (directory / "fixture").mkdir(parents=True, exist_ok=True)
        for file_name in FILES:
            target = directory / ("fixture" if file_name != REQUEST_FILE else "") / file_name
            try:
                source = frb.restore_file(release, entry["files"][file_name], target, assets, fetcher, timeout)
            except frb.AssetError as error:
                raise CorpusError(str(error)) from None
            log(f"{entry['name']}/{file_name}: {source}")
        fb.write_atomic(directory / "fixture" / fb.SUMS_FILE, frb.sums_text(entry).encode())
        try:
            verifier = frb.check_range(entry, directory / "fixture", pins)
        except frb.AssetError as error:
            raise CorpusError(str(error)) from None
        manifest = snapshot_manifest(entry["name"])
        if next(fb.read_blocks(directory / "fixture" / fb.BLOCKS_FILE))[1][4:36].hex() != manifest["block_hash_hex"]:
            raise CorpusError(f"range {entry['name']}: the first block does not name the block of the snapshot's manifest")
        log(f"range {entry['name']}: {len(verifier.blocks)} blocks checked in {directory}")


def strip(records: list[dict]) -> list[dict]:
    return [{k: v for k, v in r.items() if k not in ("diagnostic", "set_digest_hex", "set_value")} for r in records]


def compare(name: str, directory: Path, oracle: str, harness: str, recorded: Path | None, write_expected: bool,
            log=print) -> dict:
    request_file, blocks = directory / REQUEST_FILE, directory / "fixture" / fb.BLOCKS_FILE
    out = {}
    for side, program in (("core", harness), ("oracle", oracle)):
        keep = directory / f"{side}-responses"
        keep.mkdir(exist_ok=True)
        began = time.monotonic()
        lines = range_results.results(name, request_file, blocks, [program], keep)
        seconds = time.monotonic() - began
        (directory / f"{side}-results.jsonl").write_text(range_results.results_text(lines))
        out[side] = {"seconds": round(seconds), "program": program}
        log(f"range {name}: {side} took {seconds:.0f} seconds")
    request = {**json.loads(request_file.read_text()), "id": "range", "blocks_file": str(blocks.resolve())}
    responses = {side: json.loads((directory / f"{side}-responses/range-response.json").read_text())
                 for side in ("oracle", "core")}
    failure = validate.compare(request, responses["oracle"], responses["core"])
    if failure:
        raise CorpusError(f"range {name}: the programs disagree: {failure[1]}")
    for side in ("oracle", "core"):
        if not all(r["valid"] for r in responses[side]["ok"]["blocks"]):
            raise CorpusError(f"range {name}: {side} rejected a block")
    parsed = [check_range_results.read_results(str(directory / f"{side}-results.jsonl")) for side in ("oracle", "core")]
    heights = range_results.block_heights(blocks)
    for side, results in zip(("oracle", "core"), parsed):
        try:
            check_range_results.check_complete(results)
        except check_range_results.Malformed as error:
            raise CorpusError(f"range {name}: the {side} results: {error}") from None
        if [r["height"] for r in results[1]] != heights:
            raise CorpusError(f"range {name}: the {side} results do not have one record for each block of {blocks}")
    difference = check_range_results.first_difference(*parsed)
    if difference is not None:
        raise CorpusError(f"range {name}: the checker fails on the oracle's results: {difference}")
    if recorded is not None:
        first, last = RANGES[name]
        old = [r for r in json.loads(recorded.read_text())["ok"]["blocks"] if first <= r["height"] <= last]
        if strip(old) != strip(responses["core"]["ok"]["blocks"]):
            raise CorpusError(f"range {name}: the block records differ from those of {recorded}")
        out["recorded_records_sha256"] = records_sha256(old)
        log(f"range {name}: the block records equal those of the recorded run on the whole coin set")
    head, records, end = parsed[1]
    out.update(request_sha256=head["request_sha256"], blocks_sha256=head["blocks_sha256"],
               start=[head["start_set_digest_hex"], head["start_set_coins"]],
               end=[end["end_set_digest_hex"], end["end_set_coins"]], blocks=len(records),
               spent=sum(r["spent"] for r in records), created=sum(r["created"] for r in records),
               results_sha256=frb.sha256_file(directory / "core-results.jsonl"))
    log(f"range {name}: both programs accept {len(records)} blocks and agree; restricted set "
        f"{head['start_set_coins']} coins {head['start_set_digest_hex']} to {end['end_set_coins']} coins "
        f"{end['end_set_digest_hex']}")
    (directory / "compare.json").write_text(json.dumps(out, indent=2) + "\n")
    if write_expected:
        target = CORPUS / "ranges" / name
        target.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(directory / "core-results.jsonl", target / "expected.jsonl")
        log(f"wrote {target / 'expected.jsonl'}")
    return out


GENERATORS = ROOT / "tests/generators.toml"
GENERATORS_HEAD = """\
# The programs that wrote the generated fixtures of the repository, with the inputs of each run.
#
# Each table names one generated file. `program` wrote the file, and `agreed` gave the same
# values in the same run. `command` is the command of the run, without the argument `--recorded`
# of a local file, and the file is the results file of `program` in that run. The SHA-256 values
# name the inputs and the output. tests/conformance/SHA256SUMS pins each file.
#
# scripts/conformance.py record writes this file from the runs of scripts/conformance.py compare.
"""


def toml_string(value: str) -> str:
    return json.dumps(value)


def record(work: Path, commit: str, date: str, harness_build: Path, log=print) -> None:
    stamp = dict(line.split(" ", 1) for line in (harness_build / "core.stamp").read_text().splitlines() if " " in line)
    if "pin" not in stamp:
        raise CorpusError(f"{harness_build / 'core.stamp'} names no pinned Core commit")
    text = [GENERATORS_HEAD]
    sums = []
    for name in RANGES:
        result = json.loads((work / name / "compare.json").read_text())
        expected = CORPUS / "ranges" / name / "expected.jsonl"
        sha256 = frb.sha256_file(expected)
        if sha256 != result["results_sha256"]:
            raise CorpusError(f"{expected} does not have the SHA-256 of the harness's results of the run")
        sums.append(f"{sha256}  ranges/{name}/expected.jsonl")
        recorded = ("the block records of the recorded run on the whole coin set, "
                    f"SHA-256 {result['recorded_records_sha256']} without the fields of the whole set"
                    if "recorded_records_sha256" in result else "none")
        text.append(f"""
[generators."tests/conformance/ranges/{name}/expected.jsonl"]
format = "dogelib-range-results/1"
program = "build/core-harness/core-oracle: the Core harness of scripts/build_core_harness.sh, without --trap-overflow"
core_repository = "dogecoin/dogecoin"
core_commit = {toml_string(stamp["pin"])}
dogelib_commit = {toml_string(commit)}
compiler = {toml_string(stamp.get("cxx", ""))}
agreed = ".lake/build/bin/dogelib-oracle, built from the same DogeLib commit"
command = "python3 -I scripts/conformance.py compare --range {name} --dir build/conformance-work/{name} .lake/build/bin/dogelib-oracle build/core-harness/core-oracle"
date = {toml_string(date)}
request_sha256 = {toml_string(result["request_sha256"])}
blocks_sha256 = {toml_string(result["blocks_sha256"])}
results_sha256 = {toml_string(sha256)}
blocks = {result["blocks"]}
spent = {result["spent"]}
created = {result["created"]}
core_seconds = {result["core"]["seconds"]}
oracle_seconds = {result["oracle"]["seconds"]}
recorded_run = {toml_string(recorded)}
""")
    GENERATORS.write_text("".join(text))
    (CORPUS / "SHA256SUMS").write_text("".join(line + "\n" for line in sums))
    log(f"wrote {GENERATORS} and {CORPUS / 'SHA256SUMS'}")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("request")
    p.add_argument("--range", required=True, choices=list(RANGES))
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--snapshot", required=True, type=Path)
    p.add_argument("--fixture", required=True, type=Path)
    p.add_argument("--output", required=True, type=Path)
    p = sub.add_parser("pack")
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--assets", required=True, type=Path)
    p.add_argument("--repository", default="dghelm/DogeLib")
    p.add_argument("--tag", required=True)
    p = sub.add_parser("fetch")
    p.add_argument("--assets", type=Path)
    p.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    p.add_argument("--timeout", type=float, default=120.0)
    p.add_argument("names", nargs="*", metavar="NAME")
    p = sub.add_parser("compare")
    p.add_argument("--range", choices=list(RANGES), help="one range; every range by default")
    p.add_argument("--dir", type=Path)
    p.add_argument("--recorded", type=Path)
    p.add_argument("--write-expected", action="store_true")
    p.add_argument("oracle")
    p.add_argument("harness")
    p = sub.add_parser("record")
    p.add_argument("--work", required=True, type=Path)
    p.add_argument("--commit", required=True)
    p.add_argument("--date", required=True)
    p.add_argument("--harness-build", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        if args.command == "request":
            build_request(args.range, args.source, args.snapshot, args.fixture, args.output)
        elif args.command == "pack":
            entries = pack(args.work, args.assets)
            release = {"format": FORMAT, "repository": args.repository, "tag": args.tag, "ranges": entries}
            RELEASE_FILE.write_text(json.dumps(release, indent=2) + "\n")
            load_release()
            print(f"wrote {RELEASE_FILE}")
        elif args.command == "fetch":
            unknown = [name for name in args.names if name not in RANGES]
            if unknown:
                parser.error(f"unknown ranges {unknown}; the ranges are {', '.join(RANGES)}")
            fetch(load_release(), args.output, args.names, args.assets, timeout=args.timeout)
        elif args.command == "record":
            record(args.work, args.commit, args.date, args.harness_build)
        else:
            if (args.dir or args.recorded) and not args.range:
                parser.error("--dir and --recorded need --range")
            for name in [args.range] if args.range else RANGES:
                compare(name, args.dir or DEFAULT_OUTPUT / name, args.oracle, args.harness, args.recorded,
                        args.write_expected)
    except (OSError, ValueError, KeyError, CorpusError, fb.FetchError, restrict_coins.RestrictError,
            range_results.ResultsError, check_range_results.Malformed) as error:
        print(f"FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
