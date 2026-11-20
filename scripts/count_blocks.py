#!/usr/bin/env python3
"""Count the transactions, inputs and outputs of block fixtures.

Usage:
  python3 -I scripts/count_blocks.py [--coin-set] [--last HEIGHT] FIXTURE...
  python3 -I scripts/count_blocks.py --sample-heights --last HEIGHT [--stride N] [--seed S]
  python3 -I scripts/count_blocks.py --estimate --last HEIGHT [--stride N] FIXTURE

Each FIXTURE is a directory of scripts/fetch_blocks.py or scripts/fetch_release_blocks.py, with
`blocks.bin`, `manifest.json` and `SHA256SUMS`. The script checks `SHA256SUMS`, and parses every
block with the parser of scripts/fetch_blocks.py. It does not repeat the hash, Merkle root and
link checks of `fetch_blocks.py --check`, and it runs no oracle and no node. This is the count of
design record 0011, section 2, and the measurement of its stage 0.

The first form reads the fixtures in the order given, as one sequence of blocks, and prints one
JSON object. With `--last HEIGHT` it stops after the block at that height:

- `blocks`, `bytes`: the blocks and the sum of their sizes.
- `transactions`: all transactions, coinbases included.
- `inputs`: the inputs of transactions other than a coinbase.
- `inputs_internal`: inputs that spend an output of an earlier transaction of the sequence, in
  the same block or an earlier one. `inputs_external` are the other inputs, and
  `external_txids` counts the distinct transaction IDs that they name.
- `max_inputs`: the largest number of inputs of one transaction.
- `outputs`: all outputs. `outputs_entering_set` excludes the outputs that Core's
  `CScript::IsUnspendable` rejects: a script that starts with OP_RETURN, or a script of more
  than 10,000 bytes (src/script/script.h, `MAX_SCRIPT_SIZE`). It also excludes the output of
  the block at height 0: `ConnectBlock` adds no coin for the genesis block (src/validation.cpp).

With `--coin-set` it also builds the coin set of the sequence, which must start at height 0, and
reports it after the last block under `coin_set`:

- `txouts`, `transactions`: the coins, and the distinct transaction IDs of the coins. These are
  the `txouts` and `transactions` of `gettxoutsetinfo`.
- `slots`: for each transaction ID of the set, one more than the largest index of its coins,
  summed. Dogecoin Core 1.14 keeps one `CTxOut` for each index up to that one in `CCoins`.
- `scripts_over_28_bytes`: the coins whose script does not fit the 28 bytes that `CScript`
  holds without an allocation (`prevector<28, unsigned char>`, src/script/script.h).
- `script_bytes`: the sum of the script lengths of the coins.

A later output with the transaction ID of a coin in the set replaces the coins of that ID, as
Core 1.14 does for the two duplicate coinbases of Bitcoin. `replaced_txids` counts such cases.

`--sample-heights` prints a comma-separated list of heights for `scripts/fetch_blocks.py
--heights`. It splits the heights from 0 to HEIGHT into strata of N heights (default 1,000), and
takes one height from each, chosen by a generator seeded with S (default 20261120).

`--estimate` reads one fixture of such a sample. For each stratum it multiplies the counts of
its sampled blocks by the number of heights of the stratum over the number of sampled blocks.
It prints the sums: an estimate of the bytes, transactions, inputs and outputs of the chain
from height 0 to HEIGHT, and the estimate for each band of 500,000 heights. `standard_error` is
the estimate of collapsed strata: it pairs the strata in height order, and takes the square root
of the sum of the squared differences of the two scaled values of each pair. A last stratum
without a partner adds nothing. The estimate assumes that the two strata of a pair have the same
mean, so it can be larger or smaller than the true error.
"""

import argparse
import json
import random
import sys
from pathlib import Path

# Import the helpers beside this script, including under Python's isolated mode.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fetch_blocks
from fetch_blocks import AUXPOW_FLAG, FetchError, Reader, read_blocks, sha256d

OP_RETURN = 0x6A
MAX_SCRIPT_SIZE = 10000
PREVECTOR_INLINE = 28
NULL_TXID = bytes(32)
DEFAULT_STRIDE = 1000
DEFAULT_SEED = 20261120
BAND = 500000


def read_transaction(reader: Reader):
    """Read one transaction. Return its ID, its outpoints and the script of each output.

    The parse is the one of `fetch_blocks.read_transaction`, which follows Core's
    `UnserializeTransaction` with witness data allowed.
    """
    version = reader.take(4)
    body_start = reader.pos
    count = reader.compact_size()
    flags = 0
    if count == 0:
        flags = reader.take(1)[0]
        if flags != 0:
            body_start = reader.pos
            count = reader.compact_size()
    prevouts, scripts = [], []
    if count != 0 or flags != 0:
        for _ in range(count):
            outpoint = reader.take(36)
            prevouts.append((outpoint[:32], int.from_bytes(outpoint[32:], "little")))
            reader.take(reader.compact_size())
            reader.take(4)
        for _ in range(reader.compact_size()):
            reader.take(8)
            scripts.append(reader.take(reader.compact_size()))
    body = reader.data[body_start:reader.pos]
    if flags & 1:
        flags ^= 1
        for _ in range(count):
            for _ in range(reader.compact_size()):
                reader.take(reader.compact_size())
    if flags:
        raise FetchError(f"unknown transaction flags before offset {reader.pos}")
    lock_time = reader.take(4)
    return sha256d(version + body + lock_time), prevouts, scripts


def transactions(raw: bytes):
    """The transactions of one block, as `read_transaction` returns them."""
    reader = Reader(raw)
    header = reader.take(80)
    if int.from_bytes(header[:4], "little") & AUXPOW_FLAG:
        # CAuxPow (src/auxpow.h), as in fetch_blocks.Block.
        read_transaction(reader)
        reader.take(32)
        reader.hashes()
        reader.take(4)
        reader.hashes()
        reader.take(4)
        reader.take(80)
    result = [read_transaction(reader) for _ in range(reader.compact_size())]
    if reader.pos != len(raw):
        raise FetchError(f"{len(raw) - reader.pos} trailing bytes after the last transaction")
    return result


def unspendable(script: bytes) -> bool:
    """Core's `CScript::IsUnspendable`."""
    return (len(script) > 0 and script[0] == OP_RETURN) or len(script) > MAX_SCRIPT_SIZE


def fixture_blocks(fixture):
    """Check `SHA256SUMS` of a fixture, and yield `(height, raw)` for each block."""
    directory = Path(fixture)
    fetch_blocks.check_sums(directory, (fetch_blocks.BLOCKS_FILE, fetch_blocks.MANIFEST_FILE))
    yield from read_blocks(directory / fetch_blocks.BLOCKS_FILE)


def count(fixtures: list[str], coin_set: bool = False, last: int | None = None) -> dict:
    """The counts of the first form, over the blocks of `fixtures` in order."""
    totals = dict(blocks=0, bytes=0, transactions=0, inputs=0, inputs_internal=0, inputs_external=0,
                  max_inputs=0, outputs=0, outputs_entering_set=0)
    # Without --coin-set, `created` keeps each outpoint that the sequence created and has not
    # spent. With --coin-set it maps each such outpoint to the length of its script.
    created: dict = {}
    external_txids = set()
    replaced = 0
    expected_height = None
    for fixture in fixtures:
        for height, raw in fixture_blocks(fixture):
            if last is not None and height > last:
                break
            if coin_set and expected_height is None and height != 0:
                raise FetchError("--coin-set needs a sequence that starts at height 0")
            if coin_set and expected_height is not None and height != expected_height:
                raise FetchError(f"--coin-set needs consecutive heights: {height} follows {expected_height - 1}")
            expected_height = height + 1
            totals["blocks"] += 1
            totals["bytes"] += len(raw)
            for position, (txid, prevouts, scripts) in enumerate(transactions(raw)):
                totals["transactions"] += 1
                if position > 0:
                    totals["inputs"] += len(prevouts)
                    totals["max_inputs"] = max(totals["max_inputs"], len(prevouts))
                    for outpoint in prevouts:
                        if outpoint in created:
                            del created[outpoint]
                            totals["inputs_internal"] += 1
                        else:
                            totals["inputs_external"] += 1
                            external_txids.add(outpoint[0])
                totals["outputs"] += len(scripts)
                if coin_set and any((txid, n) in created for n in range(len(scripts))):
                    replaced += 1
                    for n in range(len(scripts)):
                        created.pop((txid, n), None)
                for n, script in enumerate(scripts):
                    if height != 0 and not unspendable(script):
                        totals["outputs_entering_set"] += 1
                        created[(txid, n)] = len(script) if coin_set else None
    totals["external_txids"] = len(external_txids)
    if coin_set:
        last_index: dict = {}
        over, script_bytes = 0, 0
        for (txid, n), length in created.items():
            if last_index.get(txid, -1) < n:
                last_index[txid] = n
            over += length > PREVECTOR_INLINE
            script_bytes += length
        totals["coin_set"] = dict(
            height=expected_height - 1 if expected_height else None,
            txouts=len(created), transactions=len(last_index),
            slots=sum(n + 1 for n in last_index.values()),
            scripts_over_28_bytes=over, script_bytes=script_bytes, replaced_txids=replaced)
    return totals


def sample_heights(last: int, stride: int, seed: int) -> list[int]:
    """One height from each stratum of `stride` heights from 0 to `last`."""
    generator = random.Random(seed)
    return [generator.randrange(start, min(start + stride, last + 1)) for start in range(0, last + 1, stride)]


def estimate(fixture: str, last: int, stride: int) -> dict:
    """Scale the counts of a sampled fixture to every height from 0 to `last`."""
    keys = ("bytes", "transactions", "inputs", "outputs", "outputs_entering_set")
    strata: dict = {}
    for height, raw in fixture_blocks(fixture):
        if height > last:
            raise FetchError(f"height {height} is above --last {last}")
        row = strata.setdefault(height // stride, dict.fromkeys(keys + ("sampled",), 0))
        row["sampled"] += 1
        row["bytes"] += len(raw)
        for position, (_, prevouts, scripts) in enumerate(transactions(raw)):
            row["transactions"] += 1
            row["inputs"] += len(prevouts) if position > 0 else 0
            row["outputs"] += len(scripts)
            if height != 0:
                row["outputs_entering_set"] += sum(not unspendable(script) for script in scripts)
    expected = last // stride + 1
    if len(strata) != expected:
        raise FetchError(f"the fixture samples {len(strata)} of the {expected} strata")
    total = dict.fromkeys(keys, 0.0)
    bands: dict = {}
    scaled: dict = {}
    for index, row in sorted(strata.items()):
        size = min((index + 1) * stride, last + 1) - index * stride
        start = index * stride
        band = bands.setdefault(start // BAND, dict.fromkeys(keys, 0.0))
        for key in keys:
            value = row[key] * size / row["sampled"]
            scaled.setdefault(key, []).append(row[key] * stride / row["sampled"])
            total[key] += value
            band[key] += value
    rounded = lambda row: {key: round(value) for key, value in row.items()}
    return {
        "first": 0, "last": last, "stride": stride, "sampled_blocks": sum(row["sampled"] for row in strata.values()),
        "estimate": rounded(total),
        "standard_error": {key: round(sum((values[i] - values[i + 1]) ** 2
                                          for i in range(0, len(values) - 1, 2)) ** 0.5)
                           for key, values in scaled.items()},
        "bands": [{"first": index * BAND, "last": min((index + 1) * BAND - 1, last), **rounded(band)}
                  for index, band in sorted(bands.items())],
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--coin-set", action="store_true", help="also build the coin set from height 0")
    mode.add_argument("--sample-heights", action="store_true", help="print the heights of a sample")
    mode.add_argument("--estimate", action="store_true", help="scale a sample fixture to the chain")
    parser.add_argument("--last", type=int, metavar="HEIGHT")
    parser.add_argument("--stride", type=int, default=DEFAULT_STRIDE, metavar="N")
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED, metavar="S")
    parser.add_argument("fixtures", nargs="*", metavar="FIXTURE")
    args = parser.parse_args(argv)
    if args.last is not None and args.last < 0:
        parser.error("--last needs a height from 0")
    if (args.sample_heights or args.estimate) and (args.last is None or args.stride < 1):
        parser.error("--sample-heights and --estimate need --last HEIGHT >= 0 and --stride N >= 1")
    try:
        if args.sample_heights:
            if args.fixtures:
                parser.error("--sample-heights takes no fixture")
            print(",".join(map(str, sample_heights(args.last, args.stride, args.seed))))
            return 0
        if args.estimate:
            if len(args.fixtures) != 1:
                parser.error("--estimate takes one fixture")
            result = estimate(args.fixtures[0], args.last, args.stride)
        else:
            if not args.fixtures:
                parser.error("give at least one fixture")
            result = count(args.fixtures, args.coin_set, args.last)
    except (FetchError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
