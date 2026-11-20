#!/usr/bin/env python3
"""Run the Core pass: replay mainnet from the genesis block in the Core harness, in segments, and write coin-set snapshots.

Usage:
  python3 -I scripts/core_pass.py --state DIR [--last HEIGHT] [--local FIXTURE]... [--cache-mb MB]
      [--segment-blocks N] [--segment-bytes BYTES] [--min-free-gb GB] [--stop-after N] <core-oracle-trap>
  python3 -I scripts/core_pass.py --state DIR --version-bits <dogelib-oracle> <core-oracle>

This is the Core pass of design record 0011 (sections 3.2, 3.4 and 5, stage 2). The harness
replays the chain once, from the empty coin set, and every request has both flags true and the
adjusted time of scripts/oracle_block_validate.py. The pass:

- reads the blocks in segments of at most `--segment-blocks` blocks (default 100,000) and at most
  `--segment-bytes` bytes (default 4 GB). Each block comes from a `--local` fixture of
  scripts/fetch_blocks.py when one holds its height, and from the node otherwise. Each block passes
  the checks of scripts/fetch_blocks.py: its parse, its header hash, its Merkle root, its link to
  the block below and each pinned hash. The fetch of the next segment runs while the harness runs
  the current one. A segment's file is deleted when the harness accepts all of it.
- carries the coin set in Core's CCoinsViewDB in `DIR/coins-db`, which persists from one segment to
  the next (docs/oracle.md, "The Core pass"). A segment request has `coins_db_continue`, so the
  harness requires that the database's best block is the previous hash of the segment's first
  block, which is the last block of the segment before. Each response reports the digest of the
  whole set at the segment's end.
- keeps the header of every accepted block in `DIR/headers.bin`, and builds each segment's `chain`,
  with the version of each entry, and `bip34_ancestor_hex` from it. Inside the CSV window the chain
  reaches back to the version-bits boundary below the CSV start.
- writes a snapshot at each range start of design record 0011, section 4, and at each multiple of
  500,000 for a restart. It writes a manifest for each, and keeps only the newest restart snapshot
  that is not a range start. It requests the digest of the whole set at each range end, and Core's
  `gettxoutsetinfo` values at the last height.
- requires every checkpoint of Core, and the committed digests of heights 100,000, 101,000 and
  145,000 from the replays of design record 0011, stage 1.
- requests Core's version-bits state at every period boundary.

The state is in `DIR/state.json`. A run continues from it. When the database does not have the best
block of the state, the run starts again from the newest snapshot below the state's height. A
harness that stops with an error, such as the signed-overflow trap of
`scripts/build_core_harness.sh --trap-overflow`, stops the pass, and the script prints the last
height that the harness reported.

`--version-bits` compares each recorded state of a boundary from the CSV start to one period after
the CSV timeout with `block.version_bits_state` of the oracle and of the harness on the kept
headers from the genesis block (design record 0011, stage 2).

The password of the node comes from the environment or the file of scripts/fetch_blocks.py, and the
script does not print it. Run the pass on one core at low priority, and register it in STATUS.md.
"""

import argparse
import gzip
import hashlib
import json
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
from pathlib import Path

# Import the helpers beside this script, including under Python's isolated mode.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fetch_blocks
import oracle_block_validate as validate
from fetch_blocks import FetchError, display

ROOT = Path(__file__).resolve().parent.parent
FORMAT = "dogelib-coins/1"
PERIOD = 10080
CSV_START = 1462060800
CSV_TIMEOUT = 1493596800
BIP34_HEIGHT = 1034383
RESTART_EVERY = 500000
# Blocks in one JSON-RPC batch. A batch of blocks above 4.5 million has a few MB.
BATCH = 50
DEFAULT_LAST = 6465793
# The range starts and ends of design record 0011, section 4, with range S of stage 1.
RANGES = {
    "S": (100000, 101000),
    "A": (145000, 155000),
    "B": (370336, 372336),
    "C": (598999, 600999),
    "D": (1033382, 1035382),
    "F": (3463750, 3465750),
    "H": (5049000, 5050000),
    "G": (6455301, 6456301),
}
# Digests of the whole set from a source other than this pass: the replay of mainnet to height
# 145,000 by the oracle, and the committed manifest and the recorded range S of stage 1
# (docs/oracle.md, "Replay of mainnet to height 145,000" and "Ranges from a snapshot").
ANCHORS = {
    100000: (5556212, "dda64f97c6bc79ee64954d5e95ba26fb207c15b5255ffd041be333d6cbe4e817"),
    101000: (5585974, "e6aeca49614547750a803c3d4dd85f6986f69f819a207531f896e1aa7840aa1b"),
    145000: (5094671, "b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d"),
}
# The node's gettxoutsetinfo at height 6,465,793, recorded in stage 0 (docs/oracle.md,
# "Measurements for the Core pass"). Design record 0011, decision 7.
NODE_STATS = {
    6465793: {"best_display": "9ebb986b0b16a65680c5f3447baca7154e2999680c76c97f24c4441897bc7385",
              "transactions": 181209861, "txouts": 202470869,
              "hash_serialized": "a053d324494c91478b7e8525f52b062b56e976c61ef856509d59d33360048680"},
}


class PassError(Exception):
    """A failed check, a failed fetch or a harness that stopped."""


class DiskLow(PassError):
    """The free space fell below the margin."""


# Headers


class Headers:
    """The 80-byte header of each accepted block, by height, in `headers.bin`."""

    def __init__(self, path: Path, count: int, read_only: bool = False):
        """The first `count` headers. The pass truncates a longer file. A reader beside a running
        pass sets `read_only`, because the pass appends headers before it saves its state."""
        self.path = path
        data = path.read_bytes() if path.exists() else b""
        if len(data) < 80 * count:
            raise PassError(f"{path} has {len(data) // 80} headers, and the state has {count}")
        self.data = bytearray(data[:80 * count])
        if len(data) != 80 * count and not read_only:
            path.write_bytes(self.data)

    def __len__(self) -> int:
        return len(self.data) // 80

    def header(self, height: int) -> bytes:
        return bytes(self.data[80 * height:80 * height + 80])

    def hash(self, height: int) -> bytes:
        return fetch_blocks.sha256d(self.header(height))

    def time(self, height: int) -> int:
        return int.from_bytes(self.data[80 * height + 68:80 * height + 72], "little")

    def entry(self, height: int) -> dict:
        h = self.header(height)
        return {"height": height, "version": int.from_bytes(h[0:4], "little"),
                "time": int.from_bytes(h[68:72], "little"), "bits": int.from_bytes(h[72:76], "little")}

    def median_time(self, height: int) -> int:
        """Core's GetMedianTimePast of the block at `height`."""
        times = sorted(self.time(h) for h in range(max(0, height - 10), height + 1))
        return times[len(times) // 2]

    def append(self, headers: list[bytes]) -> None:
        with open(self.path, "ab") as stream:
            for header in headers:
                stream.write(header)
            stream.flush()
            os.fsync(stream.fileno())
        for header in headers:
            self.data += header

    def truncate(self, count: int) -> None:
        del self.data[80 * count:]
        with open(self.path, "r+b") as stream:
            stream.truncate(80 * count)


def chain_floor(headers: Headers, first: int) -> int:
    """The lowest height of the chain of a segment whose first block is at `first`.

    The harness reads the median time of the predecessor, at most 241 blocks of retarget history,
    and the aligned version-bits boundary with its ten predecessors. Inside the CSV window, Core
    walks back to the boundary below the CSV start and counts the versions above it.
    """
    floor = first - 1 - PERIOD - 260
    boundary = (first - 1) - (first % PERIOD)
    while boundary >= 0:
        mtp = headers.median_time(boundary)
        if mtp < CSV_START or mtp >= CSV_TIMEOUT:
            break
        boundary -= PERIOD
    if boundary >= 0:
        floor = min(floor, boundary - 11)
    return max(0, floor)


def segment_request(headers: Headers, first: int, blocks: Path, db: Path, cache_mb: int, plan: dict,
                    last: int, fresh_coins: str | None) -> dict:
    """The request of the segment whose blocks are in `blocks`, from `first` to `last`."""
    request = {"id": f"segment-{first}", "op": "block.validate", "mode": "allow_witness", "check_pow": True,
               "check_merkle_root": True, "adjusted_time": validate.ADJUSTED_TIME,
               "blocks_file": str(blocks), "coins_db": str(db), "coins_db_cache_mb": cache_mb}
    if first == 0:
        request.update(chain=[], bip34_ancestor_hex=None, coins=[])
    else:
        floor = chain_floor(headers, first)
        request["chain"] = [headers.entry(h) for h in range(first - 1, floor - 1, -1)]
        request["bip34_ancestor_hex"] = headers.hash(BIP34_HEIGHT).hex() if first - 1 >= BIP34_HEIGHT else None
        if fresh_coins is None:
            request["coins_db_continue"] = True
        else:
            request["coins_file"] = fresh_coins
    inside = lambda heights: sorted(h for h in heights if first <= h <= last)
    request["snapshot_heights"] = inside(plan["snapshots"])
    request["snapshot_dir"] = str(plan["snapshot_dir"])
    request["digest_heights"] = inside(plan["digests"])
    request["version_bits_heights"] = [h for h in range(max(first - 1, PERIOD - 1), last + 1) if (h + 1) % PERIOD == 0]
    return request


# Blocks


class LocalSource:
    """Blocks of checked fixtures, by height."""

    def __init__(self, fixtures: list[str], pins, log):
        self.where = {}
        for fixture in fixtures:
            path = Path(fixture) / fetch_blocks.BLOCKS_FILE
            log(f"local fixture {fixture}: checking")
            try:
                fetch_blocks.check_fixture(fixture, pins)
            except FetchError as error:
                raise PassError(f"fixture check: {error}") from None
            offset = 0
            for height, raw in fetch_blocks.read_blocks(path):
                self.where[height] = (path, offset + 8, len(raw))
                offset += 8 + len(raw)

    def get(self, height: int) -> bytes | None:
        if height not in self.where:
            return None
        path, offset, length = self.where[height]
        with open(path, "rb") as stream:
            stream.seek(offset)
            return stream.read(length)


def free_gb(path: Path) -> float:
    return shutil.disk_usage(path).free / 1e9


def fetch_segment(rpc_factory, local, pins, first: int, target: int, previous: bytes, directory: Path,
                  max_blocks: int, max_bytes: int, min_free: float, log) -> dict:
    """Fetch and check the blocks from `first`, and write `blocks.bin` and `segment.json` in `directory`."""
    directory.mkdir(parents=True, exist_ok=True)
    verifier = fetch_blocks.Verifier(pins)
    if first > 0:
        # The link to the block below the segment: the last block of the segment before.
        verifier.last = (first - 1, previous)
        verifier.runs.append({"first": first, "last": first - 1, "previous": "pass"})
    rpc = None
    digest = hashlib.sha256()
    size = 0
    headers = []
    temporary = directory / "blocks.bin.tmp"
    with open(temporary, "wb") as stream:
        height = first
        pending = []  # (height, raw, claimed) of a batch from the node
        while height <= target and height - first < max_blocks and size < max_bytes - fetch_blocks.MAX_SIZE:
            if not pending:
                raw = local.get(height) if local else None
                if raw is not None:
                    pending = [(height, raw, None)]
                else:
                    # One batch of hashes and one of blocks, of at most BATCH heights. A segment
                    # that ends at its size limit drops the rest, and the next segment fetches it again.
                    if rpc is None:
                        rpc = rpc_factory()
                    count = min(BATCH, target - height + 1, max_blocks - (height - first))
                    wanted = list(range(height, height + count))
                    hashes = rpc.batch("getblockhash", [[h] for h in wanted])
                    blocks = rpc.batch("getblock", [[value, False] for value in hashes])
                    try:
                        pending = [(h, bytes.fromhex(raw_hex), bytes.fromhex(value)[::-1])
                                   for h, value, raw_hex in zip(wanted, hashes, blocks)]
                    except (TypeError, ValueError):
                        raise PassError(f"fetch: a malformed result in the batch from height {height}") from None
            h, raw, claimed = pending.pop(0)
            if h != height:
                raise PassError(f"fetch: the batch gives height {h} in the place of {height}")
            try:
                verifier.add(height, raw, claimed)
            except FetchError as error:
                raise PassError(f"fetch: {error}") from None
            record = validate.file_record(height, raw)
            stream.write(record)
            digest.update(record)
            size += len(record)
            headers.append(raw[:80])
            if (height - first) % 10000 == 9999 and free_gb(directory) < min_free:
                raise DiskLow(f"{free_gb(directory):.0f} GB free during the fetch at height {height}")
            height += 1
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, directory / "blocks.bin")
    pinned = sum(b["auth"] == "pinned" for b in verifier.blocks)
    info = {"first": first, "last": height - 1, "blocks": height - first, "bytes": size,
            "sha256": digest.hexdigest(), "pinned": pinned,
            "last_hash_display": display(verifier.last[1]),
            "node_version": rpc.version() if rpc else None}
    (directory / "headers.bin").write_bytes(b"".join(headers))
    (directory / "segment.json").write_text(json.dumps(info, indent=2) + "\n")
    log(f"fetched heights {first} to {height - 1}: {size} bytes, {pinned} pinned")
    return info


# The pass


def load_state(path: Path) -> dict:
    if path.exists():
        return json.loads(path.read_text())
    return {"height": -1, "hash_display": None, "set_digest_hex": None, "segments": [], "snapshots": {},
            "digests": {}, "version_bits": {}, "restart": None}


def save_state(path: Path, state: dict) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(state, indent=1) + "\n")
    os.replace(temporary, path)


def plan_of(state_dir: Path, last: int, extra_snapshots=(), extra_digests=()) -> dict:
    snapshots = {start for start, _ in RANGES.values() if start <= last and start != 100000}
    snapshots |= set(range(RESTART_EVERY, last + 1, RESTART_EVERY)) | {h for h in extra_snapshots if h <= last}
    digests = {end for _, end in RANGES.values() if end <= last} | {h for h in ANCHORS if h <= last} | {last}
    digests |= {h for h in extra_digests if h <= last}
    return {"snapshots": sorted(snapshots), "digests": sorted(digests), "snapshot_dir": state_dir / "snapshots",
            "range_starts": {start for start, _ in RANGES.values()}}


def check_response(answer: dict, info: dict, headers: list[bytes], request: dict, state: dict) -> dict:
    ok = answer.get("ok")
    if not isinstance(ok, dict):
        raise PassError(f"segment {info['first']}: the harness returned {json.dumps(answer)[:400]}")
    records = ok["blocks"]
    if len(records) != info["blocks"] or not all(r["valid"] for r in records):
        bad = next((r for r in records if not r["valid"]), None)
        raise PassError(f"segment {info['first']}: the harness did not accept every block: {json.dumps(bad)[:400]}")
    for i, record in enumerate(records):
        if record["height"] != info["first"] + i or record["hash_hex"] != fetch_blocks.sha256d(headers[i]).hex():
            raise PassError(f"segment {info['first']}: record {i} is not the block of height {info['first'] + i}")
    start = state["hash_display"] if info["first"] > 0 else "00" * 32
    if "coins_file" not in request and ok["coins_db_start_display"] != start:
        raise PassError(f"segment {info['first']}: the database starts at {ok['coins_db_start_display']}, not {start}")
    if ok["coins_db_best_display"] != info["last_hash_display"]:
        raise PassError(f"segment {info['first']}: the database ends at {ok['coins_db_best_display']}")
    if "coins_file" in request:
        # A restart: the harness's digest of the loaded snapshot must be the manifest's.
        manifest = state["snapshots"][str(info["first"] - 1)]
        if (ok.get("start_set_digest_hex"), ok.get("start_set_coins")) != (manifest["set_digest_hex"], manifest["coins"]):
            raise PassError(f"segment {info['first']}: the loaded snapshot has the start "
                            f"{ok.get('start_set_digest_hex')} with {ok.get('start_set_coins')} coins, not the manifest's")
    if [s["height"] for s in ok["snapshots"]] != request["snapshot_heights"]:
        raise PassError(f"segment {info['first']}: the harness did not write every snapshot")
    if [d["height"] for d in ok["set_digests"]] != request["digest_heights"]:
        raise PassError(f"segment {info['first']}: the harness did not report every digest")
    if [v["height"] for v in ok["version_bits_states"]] != request["version_bits_heights"]:
        raise PassError(f"segment {info['first']}: the harness did not report every version-bits state")
    return ok


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 22), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_manifest(snapshot: dict, directory: Path) -> dict:
    """The manifest of a snapshot, after the SHA-256 and the length of its file are computed again."""
    path = directory / snapshot["file"]
    digest = hashlib.sha256()
    size = 0
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 22), b""):
            digest.update(chunk)
            size += len(chunk)
    if (digest.hexdigest(), size) != (snapshot["sha256"], snapshot["bytes"]):
        raise PassError(f"snapshot {snapshot['height']}: the file differs from the harness's record")
    manifest = {"format": FORMAT, "height": snapshot["height"], "block_hash_hex": snapshot["hash_hex"],
                "block_hash_display": snapshot["hash_display"], "coins": snapshot["set_coins"],
                "set_digest_hex": snapshot["set_digest_hex"], "set_value": snapshot["set_value"],
                "bytes": snapshot["bytes"], "sha256": snapshot["sha256"]}
    (directory / f"coins-{snapshot['height']}.json").write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def check_anchor(height: int, coins: int, digest: str, best_display: str) -> None:
    pinned = fetch_blocks.CHECKPOINTS.get(height)
    if pinned and pinned != best_display:
        raise PassError(f"height {height}: the block {best_display} is not the checkpoint {pinned}")
    if height in ANCHORS and (coins, digest) != ANCHORS[height]:
        raise PassError(f"height {height}: {coins} coins and the digest {digest}, and the recorded value is {ANCHORS[height]}")


def run_harness(harness: str, request: dict, response: Path, log_path: Path, register) -> tuple[dict, float]:
    """Run one segment request. Return the response and the seconds."""
    started = time.monotonic()
    with open(response, "wb") as out, open(log_path, "ab") as err:
        process = subprocess.Popen([harness], stdin=subprocess.PIPE, stdout=out, stderr=err)
        register(process.pid)
        process.stdin.write((json.dumps(request) + "\n").encode())
        process.stdin.close()
        status = process.wait()
    seconds = time.monotonic() - started
    if status != 0:
        tail = log_path.read_bytes()[-2000:].decode(errors="replace")
        lines = [line for line in tail.splitlines() if "accepted height" in line]
        last = lines[-1] if lines else "no progress line"
        raise PassError(f"the harness stopped with status {status} in the segment from {request['id']}; "
                        f"last progress: {last}; log tail: {' | '.join(tail.splitlines()[-4:])}")
    lines = response.read_text().splitlines()
    if len(lines) != 1:
        raise PassError(f"the harness wrote {len(lines)} response lines")
    return json.loads(lines[0]), seconds


def restart_point(state: dict) -> tuple[int, str] | None:
    """The newest snapshot at or below the state's height: its height and file."""
    candidates = [(int(h), s["file"]) for h, s in state["snapshots"].items()
                  if int(h) <= state["height"] and s.get("kept", True)]
    return max(candidates) if candidates else None


def core_pass(harness: str, state_dir: Path, last: int, local_fixtures: list[str], cache_mb: int,
              max_blocks: int, max_bytes: int, min_free: float, stop_after: int | None,
              rpc_factory=None, pins=None, log=lambda text: print(text, flush=True),
              register=lambda pid: None, extra_snapshots=(), extra_digests=()) -> dict:
    state_dir.mkdir(parents=True, exist_ok=True)
    plan = plan_of(state_dir, last, extra_snapshots, extra_digests)
    plan["snapshot_dir"].mkdir(exist_ok=True)
    state_path = state_dir / "state.json"
    state = load_state(state_path)
    headers = Headers(state_dir / "headers.bin", state["height"] + 1)
    db = state_dir / "coins-db"
    db.mkdir(exist_ok=True)
    (state_dir / "responses").mkdir(exist_ok=True)
    pins = pins or fetch_blocks.Pins.load()
    local = LocalSource(local_fixtures, pins, log) if local_fixtures else None
    log_path = state_dir / "harness.log"

    # A database without the state's best block, such as one that a stopped harness left ahead of
    # the state, starts again from the newest snapshot below the state's height.
    fresh_coins = None
    if state["height"] >= 0 and state.get("db_height") != state["height"]:
        point = restart_point(state)
        if point is None:
            raise PassError("the database is not at the state's height, and no snapshot is below it")
        height, name = point
        recorded = state["snapshots"][str(height)]
        path = plan["snapshot_dir"] / name
        if not path.exists() or (file_sha256(path), path.stat().st_size) != (recorded["sha256"], recorded["bytes"]):
            raise PassError(f"the snapshot at height {height} differs from its manifest")
        log(f"restart from the snapshot at height {height}")
        for key in ("digests", "version_bits"):
            state[key] = {h: v for h, v in state[key].items() if int(h) <= height}
        state["snapshots"] = {h: v for h, v in state["snapshots"].items() if int(h) <= height}
        state["segments"] = [s for s in state["segments"] if s["last"] <= height]
        state["height"], state["hash_display"] = height, display(headers.hash(height))
        state["set_digest_hex"] = state["snapshots"][str(height)]["set_digest_hex"]
        state["restart_from"] = height
        # The state first: a later run truncates a longer header file itself.
        save_state(state_path, state)
        headers.truncate(height + 1)
        fresh_coins = str(plan["snapshot_dir"] / name)

    fetched = queue.Queue(maxsize=1)
    stop = threading.Event()

    def fetcher():
        first, previous = state["height"] + 1, (headers.hash(state["height"]) if state["height"] >= 0 else bytes(32))
        try:
            while first <= last and not stop.is_set():
                directory = state_dir / "segments" / f"from-{first}"
                info = fetch_segment(rpc_factory, local, pins, first, last, previous, directory,
                                     max_blocks, max_bytes, min_free, log)
                fetched.put((directory, info))
                first, previous = info["last"] + 1, bytes.fromhex(info["last_hash_display"])[::-1]
        except BaseException as error:  # noqa: BLE001 - the main thread reports it
            fetched.put((None, error))
            return
        fetched.put((None, None))

    thread = threading.Thread(target=fetcher, daemon=True)
    thread.start()
    done = 0
    try:
        while True:
            directory, info = fetched.get()
            if directory is None:
                if isinstance(info, BaseException):
                    raise info if isinstance(info, PassError) else PassError(f"fetch: {info}")
                break
            if free_gb(state_dir) < min_free:
                raise DiskLow(f"{free_gb(state_dir):.0f} GB free before the segment from {info['first']}")
            first, end = info["first"], info["last"]
            header_bytes = (directory / "headers.bin").read_bytes()
            segment_headers = [header_bytes[i:i + 80] for i in range(0, 80 * info["blocks"], 80)]
            request = segment_request(headers, first, directory / "blocks.bin", db, cache_mb, plan, end, fresh_coins)
            response = state_dir / "responses" / f"from-{first}.json"
            state["db_height"] = None
            save_state(state_path, state)
            log(f"segment {first} to {end}: {info['blocks']} blocks, {info['bytes']} bytes")
            answer, seconds = run_harness(harness, request, response, log_path, register)
            ok = check_response(answer, info, segment_headers, request, state)
            fresh_coins = None
            headers.append(segment_headers)
            for snapshot in ok["snapshots"]:
                manifest = write_manifest(snapshot, plan["snapshot_dir"])
                check_anchor(snapshot["height"], manifest["coins"], manifest["set_digest_hex"], manifest["block_hash_display"])
                state["snapshots"][str(snapshot["height"])] = {**manifest, "file": snapshot["file"], "kept": True}
                log(f"snapshot {snapshot['height']}: {manifest['coins']} coins, {manifest['bytes']} bytes, "
                    f"digest {manifest['set_digest_hex']}")
            for entry in ok["set_digests"]:
                height = entry["height"]
                check_anchor(height, entry["set_coins"], entry["set_digest_hex"], display(headers.hash(height)))
                state["digests"][str(height)] = {**entry, "best_display": display(headers.hash(height))}
                log(f"digest {height}: {entry['set_coins']} coins, {entry['set_digest_hex']}")
            for entry in ok["version_bits_states"]:
                state["version_bits"][str(entry["height"])] = {"csv": entry["csv"], "segwit": entry["segwit"]}
            for h in range(first, end + 1):
                if h in fetch_blocks.CHECKPOINTS and display(headers.hash(h)) != fetch_blocks.CHECKPOINTS[h]:
                    raise PassError(f"height {h}: the accepted block is not Core's checkpoint")
            state["segments"].append({"first": first, "last": end, "blocks": info["blocks"], "bytes": info["bytes"],
                                      "sha256": info["sha256"], "pinned": info["pinned"],
                                      "node_version": info["node_version"], "seconds": round(seconds),
                                      "spent": sum(r["spent"] for r in ok["blocks"]),
                                      "created": sum(r["created"] for r in ok["blocks"]),
                                      "set_digest_hex": ok["set_digest_hex"], "set_coins": ok["set_coins"],
                                      "set_value": ok["set_value"], "end_display": ok["coins_db_best_display"]})
            # The records of the segment, compressed, for the range comparisons, before the state names the segment.
            archive = Path(str(response) + ".gz")
            with open(response, "rb") as source, gzip.open(str(archive) + ".tmp", "wb") as target:
                shutil.copyfileobj(source, target)
            os.replace(str(archive) + ".tmp", archive)
            state.update(height=end, hash_display=ok["coins_db_best_display"], set_digest_hex=ok["set_digest_hex"],
                         db_height=end)
            # Only the newest restart snapshot that is not a range start stays.
            restarts = sorted(int(h) for h, s in state["snapshots"].items()
                              if int(h) not in plan["range_starts"] and s.get("kept", True))
            for old in restarts[:-1]:
                (plan["snapshot_dir"] / state["snapshots"][str(old)]["file"]).unlink(missing_ok=True)
                state["snapshots"][str(old)]["kept"] = False
            save_state(state_path, state)
            response.unlink()
            shutil.rmtree(directory)
            log(f"segment {first} to {end} accepted in {seconds:.0f} seconds: {ok['set_coins']} coins, "
                f"digest {ok['set_digest_hex']}, {free_gb(state_dir):.0f} GB free")
            done += 1
            if stop_after is not None and done >= stop_after:
                break
    finally:
        stop.set()
        # Unblock the fetcher, which may wait to put a finished segment.
        try:
            fetched.get_nowait()
        except queue.Empty:
            pass
    if state["height"] == last and str(last) in state["digests"]:
        compare_node(state, last, log)
    return state


def compare_node(state: dict, height: int, log) -> None:
    """Design record 0011, decision 7: Core's gettxoutsetinfo values of the harness's set against the node's."""
    if height not in NODE_STATS:
        return
    node, ours = NODE_STATS[height], state["digests"][str(height)]
    mine = {"best_display": ours["best_display"], "transactions": ours["transactions"], "txouts": ours["set_coins"],
            "hash_serialized": ours["hash_serialized"]}
    if mine != node:
        raise PassError(f"height {height}: the harness gives {mine}, and the node gave {node}")
    log(f"height {height}: hash_serialized, transactions and txouts equal the node's gettxoutsetinfo")


def check_version_bits(state_dir: Path, oracle: str, harness: str, log) -> int:
    """Compare the recorded states of the window's boundaries with the full walk of both programs."""
    state = load_state(state_dir / "state.json")
    headers = Headers(state_dir / "headers.bin", state["height"] + 1, read_only=True)
    boundaries = [int(h) for h in state["version_bits"]]
    window = [h for h in sorted(boundaries) if headers.median_time(h) >= CSV_START]
    window = [h for h in window if headers.median_time(h - PERIOD) < CSV_TIMEOUT]
    below = [h for h in sorted(boundaries) if h not in window and headers.median_time(h) < CSV_START]
    targets = below[-1:] + window
    if not targets:
        raise PassError("no recorded boundary in the CSV window")
    count = 0
    for height in targets:
        chain = [{"version": headers.entry(h)["version"], "time": headers.time(h)} for h in range(height + 1)]
        request = {"id": f"vb-{height}", "op": "block.version_bits_state", "chain": chain}
        recorded = state["version_bits"][str(height)]
        for program in (oracle, harness):
            done = subprocess.run([program], input=(json.dumps(request) + "\n").encode(), capture_output=True)
            answer = json.loads(done.stdout.decode().splitlines()[0])
            got = {"csv": answer["ok"]["csv"], "segwit": answer["ok"]["segwit"]}
            if got != recorded:
                raise PassError(f"boundary {height}: {program} gives {got}, and the pass recorded {recorded}")
        log(f"boundary {height}: csv {recorded['csv']}, segwit {recorded['segwit']}, as both full walks")
        count += 1
    return count


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--state", required=True, metavar="DIR")
    parser.add_argument("--last", type=int, default=DEFAULT_LAST, metavar="HEIGHT")
    parser.add_argument("--local", action="append", default=[], metavar="FIXTURE")
    parser.add_argument("--cache-mb", type=int, default=4096, metavar="MB")
    parser.add_argument("--segment-blocks", type=int, default=100000, metavar="N")
    parser.add_argument("--segment-bytes", type=int, default=4_000_000_000, metavar="BYTES")
    parser.add_argument("--min-free-gb", type=float, default=150.0, metavar="GB")
    parser.add_argument("--stop-after", type=int, metavar="N", help="stop after N segments")
    parser.add_argument("--version-bits", action="store_true", help="compare the recorded version-bits states")
    parser.add_argument("--url", default=fetch_blocks.DEFAULT_URL)
    parser.add_argument("--user", default=fetch_blocks.DEFAULT_USER)
    parser.add_argument("--timeout", type=float, default=120.0, help="seconds for each RPC request")
    parser.add_argument("programs", nargs="+", metavar="PROGRAM")
    args = parser.parse_args(argv)
    state_dir = Path(args.state)
    try:
        if args.version_bits:
            if len(args.programs) != 2:
                parser.error("--version-bits needs the oracle and the harness")
            count = check_version_bits(state_dir, args.programs[0], args.programs[1], print)
            print(f"{count} boundaries agree")
            return 0
        if len(args.programs) != 1:
            parser.error("the pass needs one harness")
        if args.segment_blocks > 100000 or args.segment_bytes > 4_000_000_000:
            parser.error("a segment has at most 100,000 blocks and 4 GB")

        def rpc_factory():
            password = fetch_blocks.read_password(os.environ, fetch_blocks.PASSWORD_FILE.expanduser())
            return fetch_blocks.Rpc(args.url, args.user, password, fetch_blocks.http_transport(args.timeout))

        state = core_pass(args.programs[0], state_dir, args.last, args.local, args.cache_mb, args.segment_blocks,
                          args.segment_bytes, args.min_free_gb, args.stop_after, rpc_factory)
    except DiskLow as error:
        print(f"STOP (disk): {error}")
        return 4
    except (PassError, FetchError, fetch_blocks.PasswordMissing) as error:
        print(f"FAIL: {error}")
        return 1
    print(f"pass at height {state['height']}, block {state['hash_display']}, digest {state['set_digest_hex']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
