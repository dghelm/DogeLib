"""List the cutoff candidates of the proposed revision RelativeLockTime (design record 0012, section 10.3).

Usage: python3 -I scripts/relative_lock_time_candidates.py [--check] [--mainnet-blocks DIR]

The proposed revision replaces the lock-time cutoff of a block: the time of the block becomes
the median time past of its predecessor (BIP 113; Core's ContextualCheckBlock, SOURCES.md D110,
src/validation.cpp, lines 3127 to 3140). A *cutoff transaction* is a transaction that the
change can reach. Its lock time is a time (at least LOCKTIME_THRESHOLD, 500,000,000). The lock
time is from the median cutoff to below the block time. One of its inputs has a sequence other
than SEQUENCE_FINAL. A *candidate block* has a cutoff transaction.

The script reads the 11,018 mainnet blocks of `block.contextual_check_body` (design record 0010,
section 4): heights 0 to 10,000, the recent range, and the 17 rule-change blocks. It computes
each median itself, from the header times of the eleven predecessors, as Core's GetMedianTimePast
does (SOURCES.md D18, src/chain.h, lines 286 to 298). It runs no DogeLib code, so the list is an
expectation that no implementation under test produced.

Without --check, the script writes tests/proposals/relative-lock-time/cutoff-candidates.json.
With --check, it fails when that file differs from the list that it computes.
The list is committed before a run of scripts/compare_csv_forced.py, which requires that the
blocks with a changed verdict are exactly the candidates.

The theorem relativeLockTime_eq_of_cutoff_untouched shows that a block without a cutoff
transaction has one result under the baseline and under the revision with the rule of BIP 113.
A count is a statement about these blocks. It says nothing about unconfirmed transactions.
"""
import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_release_blocks
from compare_core import walk_tx
from oracle_block_check import fixture_blocks, split_block
from oracle_contextual_body import (PERIOD, RULE_DIR, RULE_RANGE, VERSION_BITS_HEADERS, body_chain,
                                    chain_entry, combined_headers, header_time_bits)

OUTPUT = ROOT / "tests/proposals/relative-lock-time/cutoff-candidates.json"
FORMAT = "dogelib-cutoff-candidates/1"
LOCKTIME_THRESHOLD = 500000000  # SOURCES.md D24, src/script/script.h, line 35
SEQUENCE_FINAL = 0xffffffff  # SOURCES.md D4, src/primitives/transaction.h, line 76
MEDIAN_TIME_SPAN = 11  # SOURCES.md D18, src/chain.h, line 276


def median_time_past(chain: list[dict]) -> int:
    """GetMedianTimePast of the first entry of a chain, newest first: the median of up to eleven times."""
    times = sorted(entry["time"] for entry in chain[:MEDIAN_TIME_SPAN])
    return times[len(times) // 2]


def lock_fields(tx: bytes) -> tuple[int, list[int]]:
    """The lock time and the sequences of a transaction of a block."""
    try:
        fields = walk_tx(tx)["fixed"]
    except (ValueError, IndexError):
        fields = walk_tx(tx, witness=True)["fixed"]
    read = lambda pos: int.from_bytes(tx[pos:pos + 4], "little")
    lock = next(read(pos) for pos, _, name in fields if name == "lock_time")
    return lock, [read(pos) for pos, _, name in fields if name == "sequence"]


def block_groups(directory) -> list[tuple[str, list[tuple[dict, bytes, list[dict]]]]]:
    """The 11,018 blocks in three groups: the name, and each block with its record and its chain.

    The chain of a block is its view, newest first, as `block.contextual_check_body` takes it.
    It holds the eleven predecessors, or every predecessor below height 11. For a block from the
    first period on, it also reaches the aligned version-bits boundary and its ten predecessors."""
    directory = pathlib.Path(directory)
    release = fetch_release_blocks.load_release()
    groups = []
    for entry in release["ranges"]:
        if entry["last"] >= PERIOD:
            continue
        blocks = fixture_blocks(directory / entry["name"], fetch_release_blocks.sums_text(entry))
        entries = {record["height"]: chain_entry(record["height"], *header_time_bits(raw)) for record, raw in blocks}
        rows = []
        for record, raw in blocks:
            height = record["height"]
            low = max(0, height - MEDIAN_TIME_SPAN)
            rows.append((record, raw, [entries[x] for x in range(height - 1, low - 1, -1)]))
        groups.append((entry["name"], rows))
    recent = [e["name"] for e in release["ranges"] if e["last"] >= PERIOD]
    names = recent + ([RULE_RANGE] if RULE_DIR.exists() else [])
    if names and VERSION_BITS_HEADERS.exists():
        headers, committed = combined_headers(directory, names)
        by_group: dict[str, list] = {name: [] for name in names}
        counts = {name: len(fixture_blocks(RULE_DIR if name == RULE_RANGE else directory / name)) for name in names}
        position = 0
        for name in names:
            for record, raw in committed[position:position + counts[name]]:
                by_group[name].append((record, raw, body_chain(record["height"], headers)))
            position += counts[name]
        groups += [(name, by_group[name]) for name in names]
    return groups


def cutoff_transactions(raw: bytes, chain: list[dict]) -> tuple[int, int, int, list[dict]]:
    """The block time, the median cutoff, the count of time lock times with an input that is not final, and the cutoff transactions."""
    block_time = header_time_bits(raw)[0]
    if not chain:
        return block_time, block_time, 0, []
    median = median_time_past(chain)
    _, txs = split_block(raw)
    time_locks, found = 0, []
    for index, tx in enumerate(txs):
        lock, sequences = lock_fields(tx)
        if lock < LOCKTIME_THRESHOLD or all(s == SEQUENCE_FINAL for s in sequences):
            continue
        time_locks += 1
        if median <= lock < block_time:
            found.append({"index": index, "lock_time": lock})
    return block_time, median, time_locks, found


def candidates(directory) -> dict:
    groups = []
    for name, rows in block_groups(directory):
        listed, time_locks, cutoff_txs = [], 0, 0
        for record, raw, chain in rows:
            block_time, median, locks, found = cutoff_transactions(raw, chain)
            time_locks += locks
            cutoff_txs += len(found)
            if found:
                listed.append({"height": record["height"], "hash": record["hash"], "time": block_time,
                               "median_time_past": median, "transactions": found})
        groups.append({"name": name, "blocks": len(rows), "first": rows[0][0]["height"],
                       "last": rows[-1][0]["height"], "time_lock_transactions": time_locks,
                       "cutoff_transactions": cutoff_txs, "candidates": listed})
    return {"format": FORMAT, "revision": "RelativeLockTime", "rule": "BIP 113 lock-time cutoff",
            "blocks": sum(g["blocks"] for g in groups),
            "cutoff_transactions": sum(g["cutoff_transactions"] for g in groups),
            "candidate_blocks": sum(len(g["candidates"]) for g in groups), "groups": groups}


def text_of(listing: dict) -> str:
    return json.dumps(listing, indent=2, sort_keys=True) + "\n"


def load() -> dict:
    listing = json.loads(OUTPUT.read_text())
    if listing.get("format") != FORMAT:
        raise ValueError(f"{OUTPUT}: not a {FORMAT} file")
    return listing


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--check", action="store_true", help="compare with the committed list")
    parser.add_argument("--mainnet-blocks", default=str(ROOT / "build/mainnet-blocks"),
                        help="the directory of scripts/fetch_release_blocks.py")
    args = parser.parse_args()
    text = text_of(candidates(args.mainnet_blocks))
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != text:
            print(f"FAIL: {OUTPUT.relative_to(ROOT)} differs from the list that this script computes")
            return 1
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(text)
    listing = json.loads(text)
    for group in listing["groups"]:
        print(f"{group['name']}: {group['blocks']} blocks, {group['time_lock_transactions']} transactions with a time "
              f"lock time and an input that is not final, {group['cutoff_transactions']} cutoff transactions, "
              f"{len(group['candidates'])} candidate blocks")
    print(f"total: {listing['blocks']} blocks, {listing['cutoff_transactions']} cutoff transactions, "
          f"{listing['candidate_blocks']} candidate blocks")
    return 0


if __name__ == "__main__":
    sys.exit(main())
