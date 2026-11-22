#!/usr/bin/env python3
"""List the candidate blocks of a historical impact run (design record 0011, section 10.3, case 2;
design record 0012, section 10.3).

Usage:
  python3 -I scripts/impact_candidates.py --range NAME --request FILE [--check]

FILE is the range request of scripts/impact_run.py for the range NAME (`impact_run.py request`).
The script reads the blocks of its `blocks_file`, the header times of its `chain`, and the scripts
of the spent coins. A range from a snapshot takes the coins from its `coins_file`. A range from the
genesis block starts from the empty set. Coins that a block of the range creates come from the
blocks themselves. The script runs no DogeLib code, so the list is an expectation that no
implementation under test produced.

**Scripts of a spend.** For each input of a transaction that is not a coinbase, the scripts are the
`scriptSig`, the spent `scriptPubKey`, and the redeem script when the spent `scriptPubKey` is
pay-to-script-hash and the `scriptSig` is push-only. The redeem script is the last item that the
`scriptSig` pushes. This is `SpendUntouched` of `DogeLib.Proposals.Framework.Proofs.Block`. A
script *holds* an opcode when one of its instructions, read from the start, has that opcode. The
reading stops at a push that the script truncates, as `opcodeFree` does. So a byte inside push data
is not an instruction.

**Candidates.**

| Revision | A candidate block has |
| --- | --- |
| `ExampleVersionVerify` | A spend whose scripts hold `0xb9` (`OP_NOP10`) |
| `ExampleFaultyLocktime` | A spend whose scripts hold `0xb3` (`OP_NOP4`) |
| `RelativeLockTime` | A cutoff transaction, a sequence candidate, or a spend whose scripts hold `0xb2` |

For every revision, a spend whose coin the script cannot find also makes its block a candidate.
The theorems `example_block_congr`, `corrected_block_congr` (through `validateBlockWith_congr`) and
`relativeLockTime_eq_of_untouched` show that a block whose two verdicts differ is a candidate.

`RelativeLockTime` is active from height 1, and the genesis block is not applicable to it. The
counts of design record 0012, section 10.3, that need no coins of the oracle come from here:

- A *cutoff transaction* has a lock time of at least 500,000,000, from the median time past of the
  predecessor to below the time of the block, and an input whose sequence is not `0xffffffff`
  (`CutoffUntouched`). The median is Core's `GetMedianTimePast`: the sorted time at index n / 2 of
  the up to eleven predecessors (SOURCES.md, D18).
- A *sequence candidate* is a transaction that is not a coinbase, with a version of at least 2 as
  an unsigned 32-bit value and an input whose sequence has bit 31 clear (`SequenceUntouched`).
- An *opcode spend* is an input whose scripts hold `0xb2`. An *opcode output* is a created
  `scriptPubKey` that holds `0xb2`. The list says whether the range spends each one. No redeem
  script is visible before its spend.

Without --check, the script writes tests/proposals/impact/<NAME>.json. With --check, it fails when
that file differs from the list that it computes. The lane commits each list before the run of the
range, and scripts/impact_run.py refuses a list that is not committed.
"""

import argparse
import hashlib
import json
import mmap
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks
from oracle_block_check import split_block

FORMAT = "dogelib-impact-candidates/1"
LISTS = ROOT / "tests" / "proposals" / "impact"
OP_NOP10, OP_NOP4, OP_CSV = 0xb9, 0xb3, 0xb2  # SOURCES.md D24, src/script/script.h
OPCODES = {"ExampleVersionVerify": OP_NOP10, "ExampleFaultyLocktime": OP_NOP4, "RelativeLockTime": OP_CSV}
REVISIONS = ("ExampleFaultyLocktime", "ExampleVersionVerify", "RelativeLockTime")
LOCKTIME_THRESHOLD = 500000000  # SOURCES.md D24, src/script/script.h, line 35
SEQUENCE_FINAL = 0xffffffff  # SOURCES.md D4, src/primitives/transaction.h, line 76
SEQUENCE_DISABLE = 1 << 31  # SEQUENCE_LOCKTIME_DISABLE_FLAG, src/primitives/transaction.h, line 81
MEDIAN_TIME_SPAN = 11  # SOURCES.md D18, src/chain.h, line 276
OP_PUSHDATA1, OP_PUSHDATA2, OP_PUSHDATA4, OP_1NEGATE, OP_16 = 0x4c, 0x4d, 0x4e, 0x4f, 0x60


class CandidateError(Exception):
    """An input that the script cannot read."""


# ---------------------------------------------------------------------------
# Scripts


def instructions(script: bytes):
    """Yield `(opcode, data)` for each instruction of `script`, read from the start, as `GetOp` reads it.

    The reading stops at a push that the script truncates. `data` is the pushed bytes, or None for
    an instruction that is not a data push."""
    pc, n = 0, len(script)
    while pc < n:
        op = script[pc]
        pc += 1
        if op <= OP_PUSHDATA4:
            if op < OP_PUSHDATA1:
                size = op
            else:
                width = {OP_PUSHDATA1: 1, OP_PUSHDATA2: 2, OP_PUSHDATA4: 4}[op]
                if pc + width > n:
                    return
                size = int.from_bytes(script[pc:pc + width], "little")
                pc += width
            if pc + size > n:
                return
            yield op, script[pc:pc + size]
            pc += size
        else:
            yield op, None


def held(script: bytes, opcodes) -> set[int]:
    """The opcodes of `opcodes` that an instruction of `script` has."""
    if not any(op in script for op in opcodes):
        return set()
    return {op for op, _ in instructions(script) if op in opcodes}


def redeem_script(script_sig: bytes) -> bytes | None:
    """The last item that a push-only `scriptSig` pushes, or None when it is not push-only or pushes nothing.

    A truncated push makes the script not push-only (`isPushOnly`). `OP_1NEGATE` and `OP_1` to `OP_16`
    push one byte. `OP_RESERVED` (0x50) is push-only and fails the evaluation, so it adds no item."""
    last = None
    for op, data in instructions(script_sig):
        if op > OP_16:
            return None
        if data is not None:
            last = data
        elif op == OP_1NEGATE:
            last = b"\x81"
        elif op > 0x50:
            last = bytes([op - 0x50])
    # A truncated push ends the reading early: then the script is not push-only.
    if not reads_to_end(script_sig):
        return None
    return last


def reads_to_end(script: bytes) -> bool:
    pc, n = 0, len(script)
    while pc < n:
        op = script[pc]
        pc += 1
        if op <= OP_PUSHDATA4:
            if op < OP_PUSHDATA1:
                size = op
            else:
                width = {OP_PUSHDATA1: 1, OP_PUSHDATA2: 2, OP_PUSHDATA4: 4}[op]
                if pc + width > n:
                    return False
                size = int.from_bytes(script[pc:pc + width], "little")
                pc += width
            if pc + size > n:
                return False
            pc += size
    return True


def is_p2sh(script: bytes) -> bool:
    """`CScript::IsPayToScriptHash`: 23 bytes, `OP_HASH160`, a push of 20 bytes, `OP_EQUAL`."""
    return len(script) == 23 and script[0] == 0xa9 and script[1] == 0x14 and script[22] == 0x87


# ---------------------------------------------------------------------------
# Transactions


def read_size(data: bytes, pos: int) -> tuple[int, int]:
    first = data[pos]
    if first < 0xfd:
        return first, pos + 1
    width = {0xfd: 2, 0xfe: 4, 0xff: 8}[first]
    return int.from_bytes(data[pos + 1:pos + 1 + width], "little"), pos + 1 + width


def parse_tx(tx: bytes) -> dict:
    """The fields of a transaction in the base format that the candidates need, and its ID."""
    version = int.from_bytes(tx[0:4], "little")
    if tx[4] == 0 and len(tx) > 5 and tx[5] != 0:
        raise CandidateError("a transaction in the extended format")
    count, pos = read_size(tx, 4)
    inputs = []
    for _ in range(count):
        outpoint = tx[pos:pos + 36]
        size, pos = read_size(tx, pos + 36)
        script_sig = tx[pos:pos + size]
        pos += size
        inputs.append((outpoint, script_sig, int.from_bytes(tx[pos:pos + 4], "little")))
        pos += 4
    count, pos = read_size(tx, pos)
    outputs = []
    for _ in range(count):
        size, pos = read_size(tx, pos + 8)
        outputs.append(tx[pos:pos + size])
        pos += size
    lock_time = int.from_bytes(tx[pos:pos + 4], "little")
    if pos + 4 != len(tx):
        raise CandidateError("a transaction with bytes after its lock time")
    txid = hashlib.sha256(hashlib.sha256(tx).digest()).digest()
    return {"version": version, "inputs": inputs, "outputs": outputs, "lock_time": lock_time, "txid": txid}


def is_coinbase(tx: dict) -> bool:
    return len(tx["inputs"]) == 1 and tx["inputs"][0][0] == bytes(32) + b"\xff\xff\xff\xff"


# ---------------------------------------------------------------------------
# Coins


def spent_outpoints(blocks: Path) -> set[bytes]:
    """The outpoint of each input of a transaction that is not a coinbase."""
    spent = set()
    for _, raw in fetch_blocks.read_blocks(blocks):
        for tx in split_block(raw)[1]:
            parsed = parse_tx(tx)
            if not is_coinbase(parsed):
                spent.update(outpoint for outpoint, _, _ in parsed["inputs"])
    return spent


def snapshot_scripts(path: Path, wanted: set[bytes]) -> dict[bytes, bytes]:
    """The `scriptPubKey` of each record of a `dogelib-coins/1` snapshot whose outpoint is in `wanted`.

    A record is a tag byte, the transaction ID, the output index, the height, the coinbase byte, the
    amount and the script (docs/oracle.md, coin-set snapshots)."""
    found = {}
    ids = {outpoint[:32] for outpoint in wanted}
    with open(path, "rb") as stream, mmap.mmap(stream.fileno(), 0, access=mmap.ACCESS_READ) as data:
        pos, size = 0, len(data)
        while pos < size:
            length, script = read_size(data, pos + 50)
            end = script + length
            if end > size:
                raise CandidateError(f"{path} ends inside a record")
            if data[pos + 1:pos + 33] in ids:
                outpoint = bytes(data[pos + 1:pos + 37])
                if outpoint in wanted:
                    found[outpoint] = bytes(data[script:end])
            pos = end
    return found


# ---------------------------------------------------------------------------
# The list


def median_time_past(times: list[int]) -> int:
    """GetMedianTimePast of the newest entry of `times`, oldest first: the median of the last eleven."""
    window = sorted(times[-MEDIAN_TIME_SPAN:])
    return window[len(window) // 2]


def scan(request: dict, coins: dict[bytes, bytes] | None, log=lambda text: None) -> dict:
    """The candidate blocks and the counts of the blocks of `request`.

    `coins` maps each spent outpoint of a coin at the start to its `scriptPubKey`. A coin that a
    block of the range creates joins the map; a spent coin leaves it."""
    chain = sorted(request.get("chain", []), key=lambda e: e["height"])
    times = [e["time"] for e in chain]
    last_height = chain[-1]["height"] if chain else -1
    utxo: dict[bytes, bytes] = dict(coins or {})
    watch = (OP_NOP10, OP_NOP4, OP_CSV)
    lists = {name: [] for name in REVISIONS}
    counts = {"cutoff_transactions": 0, "time_lock_transactions": 0, "sequence_candidates": 0,
              "opcode_spends": 0, "missing_coins": 0, "transactions": 0, "inputs": 0, "outputs": 0}
    opcode_outputs: dict[bytes, dict] = {}
    blocks = 0
    first = None
    for height, raw in fetch_blocks.read_blocks(Path(request["blocks_file"])):
        if height != last_height + 1:
            raise CandidateError(f"the block at {height} does not follow the height {last_height}")
        if first is None:
            first = height
        last_height = height
        blocks += 1
        header, txs = split_block(raw)
        block_time = int.from_bytes(raw[68:72], "little")
        block_hash = fetch_blocks.display(fetch_blocks.sha256d(raw[:80]))
        median = median_time_past(times) if times else None
        reasons = {name: [] for name in REVISIONS}
        for index, tx_bytes in enumerate(txs):
            tx = parse_tx(tx_bytes)
            counts["transactions"] += 1
            coinbase = is_coinbase(tx)
            # The cutoff of BIP 113, for every transaction of an applicable block (height 1 on).
            if height >= 1 and median is not None and tx["lock_time"] >= LOCKTIME_THRESHOLD and \
                    any(seq != SEQUENCE_FINAL for _, _, seq in tx["inputs"]):
                counts["time_lock_transactions"] += 1
                if median <= tx["lock_time"] < block_time:
                    counts["cutoff_transactions"] += 1
                    reasons["RelativeLockTime"].append({"tx": index, "rule": "cutoff", "lock_time": tx["lock_time"],
                                                        "median_time_past": median, "time": block_time})
            if not coinbase:
                if height >= 1 and tx["version"] >= 2 and any(not seq & SEQUENCE_DISABLE for _, _, seq in tx["inputs"]):
                    counts["sequence_candidates"] += 1
                    reasons["RelativeLockTime"].append({"tx": index, "rule": "sequence", "version": tx["version"],
                                                        "inputs": [i for i, (_, _, s) in enumerate(tx["inputs"])
                                                                   if not s & SEQUENCE_DISABLE]})
                for position, (outpoint, script_sig, _) in enumerate(tx["inputs"]):
                    counts["inputs"] += 1
                    script_pub_key = utxo.pop(outpoint, None)
                    if script_pub_key is None:
                        counts["missing_coins"] += 1
                        for name in REVISIONS:
                            reasons[name].append({"tx": index, "input": position, "rule": "missing coin"})
                        continue
                    if outpoint in opcode_outputs:
                        opcode_outputs[outpoint]["spent_at"] = height
                    found = {"scriptSig": held(script_sig, watch), "scriptPubKey": held(script_pub_key, watch)}
                    if is_p2sh(script_pub_key):
                        redeem = redeem_script(script_sig)
                        if redeem is not None:
                            found["redeem script"] = held(redeem, watch)
                    for name, opcode in OPCODES.items():
                        where = [part for part, ops in found.items() if opcode in ops]
                        if where:
                            if name == "RelativeLockTime":
                                counts["opcode_spends"] += 1
                            reasons[name].append({"tx": index, "input": position, "rule": f"opcode 0x{opcode:02x}",
                                                  "scripts": where})
            for n, script in enumerate(tx["outputs"]):
                counts["outputs"] += 1
                outpoint = tx["txid"] + n.to_bytes(4, "little")
                utxo[outpoint] = script
                if OP_CSV in held(script, (OP_CSV,)):
                    opcode_outputs[outpoint] = {"height": height, "txid_display": tx["txid"][::-1].hex(), "n": n,
                                                "spent_at": None}
        for name in REVISIONS:
            if reasons[name]:
                lists[name].append({"height": height, "hash": block_hash, "reasons": reasons[name]})
        times.append(block_time)
        if blocks % 10000 == 0:
            log(f"height {height}: {len(utxo)} coins in the map")
    return {"first": first, "last": last_height, "blocks": blocks, "counts": counts,
            "opcode_outputs": list(opcode_outputs.values()), "candidates": lists}


def listing(name: str, request: dict, log=lambda text: None) -> dict:
    """The candidate list of the range `name` from its range request."""
    coins = None
    snapshot = request.get("coins_file")
    if snapshot:
        wanted = spent_outpoints(Path(request["blocks_file"]))
        coins = snapshot_scripts(Path(snapshot), wanted)
        log(f"{len(wanted)} spent outpoints, {len(coins)} of them in the snapshot")
    elif request.get("coins"):
        raise CandidateError("a request with inline coins")
    result = scan(request, coins, log)
    sha = hashlib.sha256()
    with open(request["blocks_file"], "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 24), b""):
            sha.update(chunk)
    revisions = {}
    for revision in REVISIONS:
        found = result["candidates"][revision]
        revisions[revision] = {"opcode": f"0x{OPCODES[revision]:02x}", "candidate_blocks": len(found), "candidates": found}
    return {"format": FORMAT, "range": name, "first": result["first"], "last": result["last"],
            "blocks": result["blocks"], "blocks_sha256": sha.hexdigest(),
            "snapshot": Path(snapshot).name if snapshot else None, "counts": result["counts"],
            "opcode_outputs": result["opcode_outputs"], "revisions": revisions}


def text_of(value: dict) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def list_path(name: str, lists: Path = LISTS) -> Path:
    return lists / f"{name}.json"


def load(name: str, lists: Path = LISTS) -> dict:
    value = json.loads(list_path(name, lists).read_text())
    if value.get("format") != FORMAT or value.get("range") != name:
        raise CandidateError(f"{list_path(name, lists)}: not a {FORMAT} list of the range {name}")
    return value


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--range", required=True, metavar="NAME")
    parser.add_argument("--request", required=True, metavar="FILE")
    parser.add_argument("--check", action="store_true", help="compare with the committed list")
    parser.add_argument("--lists", default=str(LISTS), metavar="DIR")
    args = parser.parse_args(argv)
    try:
        request = json.loads(Path(args.request).read_text())
        value = listing(args.range, request, lambda text: print(text, flush=True))
    except (OSError, ValueError, KeyError, CandidateError, fetch_blocks.FetchError) as error:
        print(f"FAIL: {error}")
        return 1
    text = text_of(value)
    path = list_path(args.range, Path(args.lists))
    if args.check:
        if not path.exists() or path.read_text() != text:
            print(f"FAIL: {path} differs from the list that this script computes")
            return 1
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    counts = value["counts"]
    print(f"{args.range}: heights {value['first']} to {value['last']}, {value['blocks']} blocks, "
          f"{counts['transactions']} transactions, {counts['inputs']} inputs, {counts['missing_coins']} missing coins")
    for revision, entry in value["revisions"].items():
        print(f"  {revision}: {entry['candidate_blocks']} candidate blocks")
    print(f"  RelativeLockTime: {counts['cutoff_transactions']} cutoff transactions, {counts['sequence_candidates']} "
          f"sequence candidates, {counts['opcode_spends']} opcode spends, {len(value['opcode_outputs'])} opcode outputs")
    return 0


if __name__ == "__main__":
    sys.exit(main())
