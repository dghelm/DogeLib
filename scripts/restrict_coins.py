#!/usr/bin/env python3
"""Write the restricted coins of a range of design record 0011 (stage 3, exit condition 2).

Usage:
  python3 -I scripts/restrict_coins.py --run DIR --output OUT [--check <dogelib-oracle>]

DIR is the output directory of scripts/run_range.py for one range, after the range agreed. The
script works in four steps:

1. It reads `range-request.json` and `summary.json` of DIR. The request must have the SHA-256
   `request_sha256` of the summary, and its blocks file must have the SHA-256 `blocks_sha256`.
   So the range request keeps the context of the recorded run.
2. It collects `T`, the transaction IDs that the blocks name: the ID of each transaction, and the
   ID in the outpoint of each input. That is the `T` of the oracle's snapshot path
   (docs/oracle.md, the snapshot path).
3. It reads the snapshot of the request once. The file must have the length and the SHA-256 of the
   summary's manifest. Each record whose transaction ID is in `T` goes to the restricted coins, in
   the order of the file. By `validateBlock_restrict`, each block gives the same outcome on these
   coins as on the whole set.
4. It writes three files to the directory OUT. `request.json` is the *range request*: the request
   without `id`, `blocks_file` and `coins_file`, with the restricted coins as `coins`, in the form
   of the `coins` argument of `block.validate`. `expected.json` names the heights, the block below
   the range, and the SHA-256 of the block records of the recorded run without `diagnostic`,
   `set_digest_hex` and `set_value` (scripts/compare_range.py). `SHA256SUMS` covers both.

With `--check`, the oracle then runs the range request with the blocks file of DIR. Each block
record must equal the record of the recorded run, `range-oracle-response.json` of DIR, apart from
`set_digest_hex` and `set_value`, which are digests of another set.
"""

import argparse
import hashlib
import json
import mmap
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks
import replay_blocks
from oracle_block_check import split_block
from compare_range import records_sha256
from oracle_block_validate import parse_transaction, read_size

DROPPED = ("id", "blocks_file", "coins_file")
NOT_COMPARED = ("set_digest_hex", "set_value")


class RestrictError(Exception):
    """A missing or changed input, or a run that does not give the recorded records."""


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        while chunk := stream.read(1 << 24):
            digest.update(chunk)
    return digest.hexdigest()


def named_ids(blocks: Path) -> set[bytes]:
    """T: the ID of each transaction of the blocks, and the ID in the outpoint of each input."""
    ids = set()
    for _, raw in fetch_blocks.read_blocks(blocks):
        _, txs = split_block(raw)
        for tx in txs:
            base, inputs, _, end = parse_transaction(tx, 0)
            if end != len(tx):
                raise RestrictError("a transaction is not in the base format")
            ids.add(hashlib.sha256(hashlib.sha256(base).digest()).digest())
            ids.update(outpoint[:32] for outpoint in inputs)
    return ids


def restricted(snapshot: Path, ids: set[bytes], size: int, sha256: str) -> tuple[list[dict], int]:
    """The entries of the snapshot whose ID is in `ids`, grouped by ID, and the number of their coins."""
    if snapshot.stat().st_size != size:
        raise RestrictError(f"{snapshot} does not have the length of its manifest")
    entries: dict[bytes, dict] = {}
    coins = 0
    digest = hashlib.sha256()
    with open(snapshot, "rb") as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
        for start in range(0, size, 1 << 26):
            digest.update(data[start:start + (1 << 26)])
        if digest.hexdigest() != sha256:
            raise RestrictError(f"{snapshot} does not have the SHA-256 of its manifest")
        pos = 0
        while pos < size:
            if size < pos + 51:
                raise RestrictError("the snapshot ends inside a record")
            length, script = read_size(data, pos + 50)
            end = script + length
            if end > size:
                raise RestrictError("the snapshot ends inside a script")
            txid = data[pos + 1:pos + 33]
            if txid in ids:
                entry = entries.setdefault(txid, {"txid_hex": txid.hex(),
                                                  "coinbase": data[pos + 41] == 1,
                                                  "height": int.from_bytes(data[pos + 37:pos + 41], "little"),
                                                  "outputs": []})
                entry["outputs"].append({"n": int.from_bytes(data[pos + 33:pos + 37], "little"),
                                         "value": str(int.from_bytes(data[pos + 42:pos + 50], "little")),
                                         "script_hex": data[script:end].hex()})
                coins += 1
            pos = end
    return list(entries.values()), coins


def strip(records: list[dict]) -> list[dict]:
    return [{k: v for k, v in r.items() if k not in NOT_COMPARED} for r in records]


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--run", required=True, metavar="DIR")
    parser.add_argument("--output", required=True, metavar="OUT")
    parser.add_argument("--check", metavar="ORACLE")
    args = parser.parse_args(argv)
    run, output = Path(args.run), Path(args.output)
    try:
        summary = json.loads((run / "summary.json").read_text())
        source = run / "range-request.json"
        if file_sha256(source) != summary["request_sha256"]:
            raise RestrictError(f"{source} does not have the SHA-256 of the recorded run")
        request = json.loads(source.read_text())
        blocks, snapshot = Path(request["blocks_file"]), Path(request["coins_file"])
        if file_sha256(blocks) != summary["blocks_sha256"]:
            raise RestrictError(f"{blocks} does not have the SHA-256 of the recorded run")
        ids = named_ids(blocks)
        began = time.monotonic()
        coins, count = restricted(snapshot, ids, summary["snapshot"]["bytes"], summary["snapshot"]["sha256"])
        print(f"{len(ids)} named transaction IDs; {len(coins)} of them have coins at the start, "
              f"{count} coins; the snapshot took {time.monotonic() - began:.0f} seconds")
        out = {k: v for k, v in request.items() if k not in DROPPED}
        out["coins"] = coins
        recorded = json.loads((run / "range-oracle-response.json").read_text())["ok"]["blocks"]
        expected = {"range": summary["range"], "first": summary["first"], "last": summary["last"],
                    "start_block_hash_display": summary["snapshot"]["block_hash_display"],
                    "start_set_digest_hex": summary["start_set_digest_hex"],
                    "end_set_digest_hex": summary["set_digest_hex"],
                    "records_sha256": records_sha256(recorded)}
        output.mkdir(parents=True, exist_ok=True)
        (output / "request.json").write_text(json.dumps(out) + "\n")
        (output / "expected.json").write_text(json.dumps(expected, indent=2) + "\n")
        (output / "SHA256SUMS").write_text("".join(f"{file_sha256(output / name)}  {name}\n"
                                                   for name in ("expected.json", "request.json")))
        size = (output / "request.json").stat().st_size
        print(f"wrote {output}: request.json has {size} bytes")
        if args.check:
            began = time.monotonic()
            answer, _ = replay_blocks.run(args.check, {**out, "id": "restricted", "blocks_file": str(blocks.resolve())},
                                          run / "restricted-oracle-response.json", None)
            if "ok" not in answer:
                raise RestrictError(f"the oracle refused the range request: {json.dumps(answer)[:300]}")
            if strip(answer["ok"]["blocks"]) != strip(recorded):
                raise RestrictError("the block records on the restricted coins differ from the recorded run")
            print(f"the oracle gives the recorded block records on the restricted coins "
                  f"({len(recorded)} blocks, {time.monotonic() - began:.0f} seconds)")
    except (OSError, ValueError, KeyError, RestrictError, fetch_blocks.FetchError, replay_blocks.ReplayError) as error:
        print(f"FAIL: {error}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
