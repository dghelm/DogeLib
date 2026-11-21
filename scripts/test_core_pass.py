#!/usr/bin/env python3
"""Test the harness arguments of the Core pass and scripts/core_pass.py (design record 0011, stage 2).

Usage:
  python3 -I scripts/test_core_pass.py <dogelib-oracle> <core-oracle> <core-oracle-trap> <genesis-10000-fixture>

The fixture is the released blocks of heights 0 to 10,000 (scripts/fetch_release_blocks.py). The
test has six parts:

1. The CSV window. Synthetic chains from the genesis block: one that signals CSV for a whole
   period inside the window, one that never signals, and one that crosses the CSV timeout. At
   each period boundary, `block.validate` with a chain that reaches back to the boundary below the
   CSV start, and with `version_bits_heights`, reports Core's state. It must equal
   `block.version_bits_state` of the oracle and of the harness on the whole chain. A chain one
   entry shorter, and an entry above that boundary without a version, are request errors.
2. The coin database. Each small request of scripts/oracle_block_validate.py gives the same
   response with `coins_db` as without it, apart from the digests of the whole set in the block
   records and the fields of the database.
3. The pass. scripts/core_pass.py replays heights 0 to 10,000 in segments of 2,500 blocks, with a
   cache of 1 MB, so that the harness writes the database after every block. Its digest at
   10,000 must equal the digest of the harness with the set in memory. A pass that starts again
   from its newest restart snapshot, at height 9,000, must reach the same digest, and the older one
   at 3,000 is deleted. A restart from a changed snapshot fails. A segment request whose first
   block does not name the database's best block is the error `coins_db_best_block`.
4. `hash_serialized`. At height 9,000 the harness's `hash_serialized` and `transactions` must
   equal the values that this script computes from the snapshot file by the definition of Core's
   GetUTXOStats.
5. The range script. scripts/run_range.py runs heights 9,001 to 9,200 from the pass's snapshot at
   9,000 in both programs, and they agree with each other and with the pass. A changed hash list
   and a committed snapshot manifest that differs from the pass's both fail.
6. The overflow trap. On the two requests of the arithmetic-domain cases that leave the int64_t
   range, the trap build stops with a signed-overflow report, one in validation.cpp and one in
   coins.cpp. On the other requests of those cases it gives the response of the ordinary build.
"""

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import core_pass
import fetch_blocks
import oracle_block_validate as validate
import run_range
from replay_blocks import ReplayError
from oracle_block_check import compact_size

PERIOD = core_pass.PERIOD
SIGNAL = 0x20000001  # The top bits of BIP 9 and bit 0, the CSV bit.


def check(condition, detail):
    """Keep checks active when Python optimizes bytecode."""
    if not condition:
        raise RuntimeError(detail)


def run(program, requests, timeout=600):
    data = "".join(json.dumps({**r, "id": str(i)}) + "\n" for i, r in enumerate(requests))
    done = subprocess.run([program], input=data, capture_output=True, text=True, timeout=timeout)
    check(done.returncode == 0, f"{program} exited with {done.returncode}: {done.stderr[-400:]}")
    lines = [json.loads(line) for line in done.stdout.splitlines() if line.strip()]
    check(len(lines) == len(requests), f"{program} gave {len(lines)} responses for {len(requests)} requests")
    return lines


# 1. The CSV window


def synthetic(periods: int, t0: int, spacing: int, signalling: set[int]) -> list[dict]:
    """A chain from the genesis block. Every block of each period in `signalling` signals CSV."""
    return [{"height": h, "time": t0 + spacing * h, "bits": 0x1e0ffff0,
             "version": SIGNAL if h // PERIOD in signalling else 0x00620004} for h in range(periods * PERIOD)]


def window_request(chain: list[dict], tip: int, floor: int, drop_version: int | None = None) -> dict:
    entries = []
    for h in range(tip, floor - 1, -1):
        entry = dict(chain[h])
        if h == drop_version:
            del entry["version"]
        entries.append(entry)
    req = validate.request([])
    req.update(chain=entries, version_bits_heights=[tip])
    return req


def test_window(oracle: str, harness: str) -> int:
    start = core_pass.CSV_START
    cases = [
        # Boundary 10,079 is below the CSV start. Period 2 signals, so CSV locks in and then activates.
        ("lock-in", synthetic(5, start - PERIOD * 60 - 30000, 60, {2}), 10079),
        ("no signal", synthetic(5, start - PERIOD * 60 - 30000, 60, set()), 10079),
        # Twenty-minute spacing crosses the CSV timeout in the fifth period.
        ("timeout", synthetic(6, start - PERIOD * 1200 - 30000, 1200, set()), 10079),
    ]
    seen = set()
    count = 0
    for name, chain, base in cases:
        tips = [h for h in range(PERIOD - 1, len(chain), PERIOD)]
        walks = []
        for tip in tips:
            full = {"op": "block.version_bits_state", "chain": [{"version": e["version"], "time": e["time"]} for e in chain[:tip + 1]]}
            walks.append(full)
        ours = run(oracle, walks)
        core = run(harness, walks)
        local = run(harness, [window_request(chain, tip, base - 10) for tip in tips])
        for tip, a, b, c in zip(tips, ours, core, local):
            check(a.get("ok") == b.get("ok"), f"{name} {tip}: the oracle's walk {a} and Core's walk {b} differ")
            check("ok" in c, f"{name} {tip}: block.validate returned {c}")
            states = c["ok"]["version_bits_states"]
            check(states == [{"height": tip, **b["ok"]}], f"{name} {tip}: block.validate reports {states}, the walk {b['ok']}")
            seen.add(b["ok"]["csv"])
            count += 1
        # The refusals, at the last boundary inside the window.
        inside = [tip for tip, b in zip(tips, core) if b["ok"]["csv"] in ("started", "locked_in", "active")]
        if inside:
            tip = inside[-1]
            short, unversioned = run(harness, [window_request(chain, tip, base - 9),
                                               window_request(chain, tip, base - 10, drop_version=base + 1)])
            check(short.get("error", {}).get("kind") == "request", f"{name}: a short chain gave {short}")
            check(unversioned.get("error", {}).get("kind") == "request", f"{name}: an entry without a version gave {unversioned}")
    check({"defined", "started", "locked_in", "active", "failed"} <= seen, f"the cases reach only the states {seen}")
    print(f"CSV window: {count} boundaries agree with both full walks, states {sorted(seen)}; refusals OK")
    return count


# 2. The coin database


def db_projection(answer: dict) -> dict:
    answer = {k: v for k, v in answer.items() if k != "id"}
    if "ok" not in answer:
        return answer
    ok = {k: v for k, v in answer["ok"].items() if not k.startswith("coins_db_")}
    ok["blocks"] = [{k: v for k, v in r.items() if k not in ("set_digest_hex", "set_value")} for r in ok["blocks"]]
    return {**answer, "ok": ok}


def test_database(harness: str) -> int:
    requests = [{k: v for k, v in req.items() if k not in ("expect", "expected")}
                for _, group in validate.block_validate_sets() for req in group]
    plain = run(harness, requests)
    count = 0
    for i, (req, a) in enumerate(zip(requests, plain)):
        with tempfile.TemporaryDirectory() as db:
            (b,) = run(harness, [{**req, "coins_db": db, "coins_db_cache_mb": 1}])
        check(db_projection(a) == db_projection(b), f"request {i}: with coins_db {json.dumps(b)[:300]}, without {json.dumps(a)[:300]}")
        count += 1
    print(f"coin database: {count} small requests give the response of the set in memory")
    return count


# 3. The pass, and 4. hash_serialized


def var_int(n: int) -> bytes:
    """Core's VARINT (serialize.h, WriteVarInt)."""
    out = [n & 0x7F]
    while n > 0x7F:
        n = (n >> 7) - 1
        out.append((n & 0x7F) | 0x80)
    return bytes(reversed(out))


def utxo_stats(snapshot: bytes, best: bytes) -> tuple[str, int]:
    """Core's hash_serialized and transactions of the set of a snapshot, from GetUTXOStats."""
    offsets = validate.snapshot_offsets(snapshot)
    stream = bytearray(best)
    transactions, last = 0, None
    for start, end in zip(offsets, offsets[1:]):
        point, _, _, value, script = validate.record_fields(snapshot[start:end])
        txid, n = point[:32], int.from_bytes(point[32:], "little")
        if txid != last:
            if last is not None:
                stream += var_int(0)
            stream += txid
            transactions += 1
            last = txid
        stream += var_int(n + 1) + value.to_bytes(8, "little") + compact_size(len(script)) + script
    if last is not None:
        stream += var_int(0)
    return hashlib.sha256(hashlib.sha256(bytes(stream)).digest()).digest()[::-1].hex(), transactions


def range_fixture(blocks: Path, first: int, last: int, directory: Path) -> None:
    """A fixture of `scripts/fetch_blocks.py` with the heights from `first` to `last` of `blocks`."""
    verifier = fetch_blocks.Verifier(fetch_blocks.Pins.load())
    records = b""
    for height, raw in fetch_blocks.read_blocks(blocks):
        if first <= height <= last:
            verifier.add(height, raw)
            records += validate.file_record(height, raw)
    directory.mkdir(parents=True)
    (directory / fetch_blocks.BLOCKS_FILE).write_bytes(records)
    manifest = {"format": fetch_blocks.FORMAT, "selection": "range", "first": first, "last": last, **verifier.derived()}
    text = fetch_blocks.manifest_text(manifest).encode()
    (directory / fetch_blocks.MANIFEST_FILE).write_bytes(text)
    (directory / fetch_blocks.SUMS_FILE).write_text(
        f"{hashlib.sha256(records).hexdigest()}  {fetch_blocks.BLOCKS_FILE}\n{hashlib.sha256(text).hexdigest()}  {fetch_blocks.MANIFEST_FILE}\n")


def test_range(oracle: str, harness: str, blocks: Path, state_dir: Path, scratch: Path) -> None:
    core_pass.RANGES["T"] = (9000, 9200)
    fixture, hashes, manifests = scratch / "fixture", scratch / "hashes", scratch / "manifests"
    range_fixture(blocks, 9001, 9200, fixture)
    manifests.mkdir()
    quiet = lambda text: None
    summary = run_range.run_range("T", state_dir, fixture, scratch / "out", oracle, harness, write_hashes=True,
                                  cache_mb=1, log=quiet, hashes=hashes, manifests=manifests)
    pass_end = json.loads((state_dir / "state.json").read_text())["digests"]["9200"]
    check((summary["blocks"], summary["set_digest_hex"], summary["set_coins"]) == (200, pass_end["set_digest_hex"], pass_end["set_coins"]),
          f"range T: {summary}")
    check((hashes / "T" / "SHA256SUMS").exists() and len((hashes / "T" / "hashes.txt").read_text().splitlines()) == 200,
          "range T: no hash list")
    fetch_blocks.read_range_hashes(hashes / "T")
    # A changed hash list.
    listing = hashes / "T" / "hashes.txt"
    lines = listing.read_text().splitlines()
    lines[7] = lines[7][:-1] + ("0" if lines[7][-1] != "0" else "1")
    listing.write_text("\n".join(lines) + "\n")
    try:
        run_range.run_range("T", state_dir, fixture, scratch / "out", oracle, harness, log=quiet, hashes=hashes, manifests=manifests)
        check(False, "range T: a changed hash list did not fail")
    except ReplayError as error:
        check("differ from the committed list" in str(error), f"range T: a changed hash list gave {error}")
    # A committed manifest that differs from the pass's. `write_hashes` writes the list again first.
    written = json.loads((state_dir / "snapshots" / "coins-9000.json").read_text())
    (manifests / "coins-9000.json").write_text(json.dumps({**written, "coins": written["coins"] + 1}, indent=2) + "\n")
    try:
        run_range.run_range("T", state_dir, fixture, scratch / "out", oracle, harness, write_hashes=True, log=quiet,
                            hashes=hashes, manifests=manifests)
        check(False, "range T: a changed committed manifest did not fail")
    except ReplayError as error:
        check("differs from the committed" in str(error), f"range T: a changed manifest gave {error}")
    print("range: heights 9,001 to 9,200 from the snapshot at 9,000 agree with the pass; a changed list and manifest fail")


def test_pass(oracle: str, harness: str, trap: str, fixture: str) -> None:
    blocks = Path(fixture) / "blocks.bin"
    whole = validate.request([], check_pow=True, mode="allow_witness")
    del whole["blocks_hex"]
    whole.update(blocks_file=str(blocks), digest_heights=[9000, 10000])
    (memory,) = run(harness, [whole])
    expected = {d["height"]: d for d in memory["ok"]["set_digests"]}
    quiet = lambda text: None
    with tempfile.TemporaryDirectory() as directory:
        state_dir = Path(directory) / "pass"
        args = dict(harness=trap, state_dir=state_dir, last=10000, local_fixtures=[fixture], cache_mb=1,
                    max_blocks=2500, max_bytes=4_000_000_000, min_free=0, log=quiet,
                    extra_snapshots=(3000, 9000), extra_digests=(9000, 9200))
        state = core_pass.core_pass(stop_after=None, **args)
        for height in (9000, 10000):
            got = {k: state["digests"][str(height)][k] for k in ("set_digest_hex", "set_coins", "set_value", "hash_serialized", "transactions")}
            want = {k: expected[height][k] for k in got}
            check(got == want, f"pass at {height}: {got}, the set in memory gives {want}")
        # 4. hash_serialized from the snapshot file at 9000.
        snapshot = (state_dir / "snapshots" / "coins-9000.bin").read_bytes()
        best = bytes.fromhex(state["snapshots"]["9000"]["block_hash_hex"])
        computed = utxo_stats(snapshot, best)
        check(computed == (expected[9000]["hash_serialized"], expected[9000]["transactions"]),
              f"hash_serialized at 9000: the harness {expected[9000]['hash_serialized']}, the definition {computed}")
        # 5. The range script on the snapshot at 9,000.
        test_range(oracle, harness, blocks, state_dir, Path(directory) / "range")
        # The restart: a database without the state's best block starts again from the newest restart snapshot.
        data = json.loads((state_dir / "state.json").read_text())
        data["db_height"] = None
        (state_dir / "state.json").write_text(json.dumps(data))
        # Only the newest restart snapshot stays, so the run starts again from 9,000.
        check(not data["snapshots"]["3000"]["kept"] and not (state_dir / "snapshots" / "coins-3000.bin").exists(),
              "the older restart snapshot was not removed")
        restarted = []
        state = core_pass.core_pass(stop_after=None, **{**args, "log": restarted.append})
        check(any("restart from the snapshot at height 9000" in line for line in restarted), "the pass did not restart")
        check(state["digests"]["10000"]["set_digest_hex"] == expected[10000]["set_digest_hex"],
              "the restarted pass reaches another digest")
        # A restart from a changed snapshot fails before the harness runs.
        path = state_dir / "snapshots" / "coins-9000.bin"
        changed = bytearray(path.read_bytes())
        changed[45] ^= 1  # A byte of the first record's amount.
        path.write_bytes(changed)
        data = json.loads((state_dir / "state.json").read_text())
        data["db_height"] = None
        (state_dir / "state.json").write_text(json.dumps(data))
        try:
            core_pass.core_pass(stop_after=None, **args)
            check(False, "a restart from a changed snapshot did not fail")
        except core_pass.PassError as error:
            check("differs from its manifest" in str(error), f"a changed snapshot gave {error}")
        # A first block that does not name the database's best block.
        wrong = core_pass.segment_request(core_pass.Headers(state_dir / "headers.bin", 10001), 9000, blocks,
                                          state_dir / "coins-db", 1, core_pass.plan_of(state_dir, 10000), 9000, None)
        with tempfile.TemporaryDirectory() as scratch:
            one = Path(scratch) / "one.bin"
            raw = next(r for h, r in validate_blocks(blocks) if h == 9000)
            one.write_bytes(validate.file_record(9000, raw))
            wrong.update(blocks_file=str(one), snapshot_heights=[], digest_heights=[], version_bits_heights=[])
            (answer,) = run(trap, [wrong])
        check(answer.get("error", {}).get("reason") == "coins_db_best_block", f"a wrong best block gave {json.dumps(answer)[:300]}")
    print("pass: heights 0 to 10,000 in segments, the restart from a snapshot, hash_serialized and the best-block check OK")


def validate_blocks(path: Path):
    import fetch_blocks
    yield from fetch_blocks.read_blocks(path)


# 6. The overflow trap


def test_trap(harness: str, trap: str) -> None:
    requests = [{k: v for k, v in req.items() if k not in ("expect", "expected")} for req in validate.domain_cases()]
    plain = run(harness, requests)
    stopped = []
    for i, req in enumerate(requests):
        done = subprocess.run([trap], input=json.dumps({**req, "id": "0"}) + "\n", capture_output=True, text=True, timeout=300)
        if done.returncode != 0:
            check("runtime error: signed integer overflow" in done.stderr, f"request {i}: {done.stderr[-300:]}")
            stopped.append("validation.cpp" if "validation.cpp" in done.stderr else "coins.cpp" if "coins.cpp" in done.stderr else "?")
        else:
            check(json.loads(done.stdout) == {**plain[i], "id": "0"}, f"request {i}: the trap build differs")
    check(sorted(stopped) == ["coins.cpp", "validation.cpp"] or sorted(stopped) == ["coins.cpp", "validation.cpp", "validation.cpp"],
          f"the trap stopped on {stopped}")
    print(f"overflow trap: stops in {sorted(set(stopped))}, and agrees with the ordinary build on the other requests")


def main(argv=None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 4:
        print(__doc__.splitlines()[2])
        return 2
    oracle, harness, trap, fixture = args
    test_window(oracle, harness)
    test_database(harness)
    test_pass(oracle, harness, trap, fixture)
    test_trap(harness, trap)
    print("PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
