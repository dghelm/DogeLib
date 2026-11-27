"""The measurements of stage 0 of design record 0013: group files, request times and mining.

Usage:
  python3 -I scripts/rejection_measurements.py groups [--corpus DIR] [--cases N] --output DIR
  python3 -I scripts/rejection_measurements.py controls --groups DIR <dogelib-oracle> <core-oracle>
  python3 -I scripts/rejection_measurements.py time --groups DIR --cpu CPU --output FILE <program>...
  python3 -I scripts/rejection_measurements.py mine --samples N --workers W --output FILE [--check ORACLE HARNESS]

The corpus directory is the output of `python3 -I scripts/conformance.py fetch`, build/conformance by
default. Every command reads only the nine ranges of the conformance corpus (design record 0013,
section 4), and no command writes in the repository.

`groups` writes one file in the proposed format `dogelib-block-cases/1` (section 8.2) for each of two
seeds of each range: the first block of the range, and the largest block of the range. The group's
`request` has the keys of the range request. For the first block, `chain` and `coins` are those of the
range request. For the largest block, `chain` adds the earlier blocks of the range, and `coins` comes
from a replay of the request's coins through the earlier blocks, as Core's `UpdateCoins` and `AddCoins`
change them. `coins` keeps the coins whose transaction ID the seed block names. `bip34_ancestor_hex` is
the hash of block 1,034,383 when the predecessor is at or above that height. The group holds the
accepted control, the seed block alone, and N cases, 40 by default. Each case is a copy of the seed
block with one byte changed after the header, then the seed block. The command prints the size of each
file, with and without xz at the preset of the corpus assets (`scripts/conformance.py`), and the size of
its `request`. The cases measure size only: no case aims at a reject site.

`controls` runs the control of each group in both programs. Both must accept the block with the same
`changes_digest_hex` and `set_digest_hex`, and the block's digest must equal the committed expected
results of its range, `tests/conformance/ranges/<range>/expected.jsonl`.

`time` runs, for each group of `SEEDS` (environment, a list of group names) and each program, three
`block.validate` requests, each in a new process pinned to CPU with `taskset` at nice 19:

- `baseline`: the seed block alone.
- `shallow`: 99 candidates and then the seed block. Candidate k changes the lock time of the last
  transaction by k, with no new Merkle root, and both flags are true. `CheckBlock` rejects it with
  `bad-txnmrklroot`.
- `deep`: 99 candidates and then the seed block. In candidate k the coinbase's first output claims k more
  koinu, the Merkle root follows, and `check_pow` is false. Every check runs, and `ConnectBlock` rejects
  it last, with `bad-cb-amount`.

Each request must give the expected reasons and the seed block's digest. The time is the wall time of
the process, which includes the read of the request.

`mine` mines made blocks at height 1 of mainnet at the `nBits` of the genesis block, `0x1e0ffff0`: version 1,
the genesis hash as the previous hash, a made coinbase with the sample index in its script, and the time of
the genesis block plus 60 seconds. The miner tries nonces from 0 with Python's `hashlib.scrypt` (N 1024,
r 1, p 1), as `scripts/generate_header_sequences.py` does, over W processes. With `--check`, both
programs must accept each mined header with `block.check_pow`, and reject it with the nonce below.
"""

import argparse
import hashlib
import json
import lzma
import multiprocessing
import os
import random
import struct
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RANGES = ["short", "A", "B", "C", "D", "E1", "E2", "F", "H"]
AUXPOW_FLAG = 0x100
BIP34_HEIGHT = 1034383
MAX_SCRIPT_SIZE = 10000
OP_RETURN = 0x6a
GENESIS_HASH = bytes.fromhex("1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691")[::-1]
GENESIS_TIME = 1386325540
GENESIS_BITS = 0x1e0ffff0
DEFAULT_SEEDS = "D-first-1033383 D-largest-1034671 H-largest-5049750 E2-first-1702520 E2-largest-1704268"


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


class Reader:
    def __init__(self, data: bytes):
        self.data, self.pos = data, 0

    def take(self, size: int) -> bytes:
        if self.pos + size > len(self.data):
            raise ValueError(f"truncated at offset {self.pos}")
        value = self.data[self.pos:self.pos + size]
        self.pos += size
        return value

    def compact_size(self) -> int:
        tag = self.take(1)[0]
        if tag < 253:
            return tag
        return int.from_bytes(self.take({253: 2, 254: 4, 255: 8}[tag]), "little")


class Tx:
    """One transaction as Core's `UnserializeTransaction` reads it with witness data allowed."""

    def __init__(self, r: Reader):
        self.start = r.pos
        version = r.take(4)
        body = r.pos
        count = r.compact_size()
        flags = 0
        if count == 0:
            flags = r.take(1)[0]
            if flags:
                body = r.pos
                count = r.compact_size()
        self.inputs, self.outputs, self.value0 = [], [], None
        for _ in range(count):
            prevout = r.take(36)
            r.take(r.compact_size())
            r.take(4)
            self.inputs.append((prevout[:32], int.from_bytes(prevout[32:], "little")))
        for i in range(r.compact_size()):
            if i == 0:
                self.value0 = r.pos
            value = int.from_bytes(r.take(8), "little")
            self.outputs.append((value, r.take(r.compact_size())))
        body_end = r.pos
        if flags & 1:
            flags ^= 1
            for _ in range(count):
                for _ in range(r.compact_size()):
                    r.take(r.compact_size())
        if flags:
            raise ValueError(f"unknown transaction flags before offset {r.pos}")
        self.txid = sha256d(version + r.data[body:body_end] + r.take(4))
        self.end = r.pos


class Block:
    def __init__(self, data: bytes):
        r = Reader(data)
        self.header = r.take(80)
        if int.from_bytes(self.header[:4], "little") & AUXPOW_FLAG:
            # CAuxPow (src/auxpow.h): the coinbase, the block hash, two branches with indexes, the parent header.
            Tx(r)
            r.take(32)
            for _ in range(r.compact_size()):
                r.take(32)
            r.take(4)
            for _ in range(r.compact_size()):
                r.take(32)
            r.take(4)
            r.take(80)
        self.txs = [Tx(r) for _ in range(r.compact_size())]
        if r.pos != len(data):
            raise ValueError("trailing bytes after the last transaction")


def range_blocks(path: Path):
    """The (height, bytes) records of a `dogelib-blocks/1` file."""
    data = path.read_bytes()
    pos = 0
    while pos < len(data):
        height, size = struct.unpack_from("<II", data, pos)
        pos += 8
        yield height, data[pos:pos + size]
        pos += size


def compact(value) -> bytes:
    return json.dumps(value, separators=(",", ":")).encode()


# groups

def coins_entries(coins: dict, txids: set) -> list:
    by_txid = {}
    for (txid, n), (coinbase, height, value, script) in coins.items():
        if txid in txids:
            by_txid.setdefault(txid, (coinbase, height, []))[2].append(
                {"n": n, "value": str(value), "script_hex": script.hex()})
    return [{"txid_hex": t.hex(), "coinbase": c, "height": h, "outputs": sorted(o, key=lambda x: x["n"])}
            for t, (c, h, o) in sorted(by_txid.items())]


def make_group(name, range_name, height, data, request, chain, coins, bip34, cases):
    rng = random.Random(f"{range_name}-{height}")
    out = [{"case": "control", "class": None, "site": None, "replace": {}, "blocks_hex": [data.hex()]}]
    for i in range(cases):
        changed = bytearray(data)
        changed[rng.randrange(80, len(changed))] ^= 1
        out.append({"case": f"c{i}", "class": "measurement", "site": None, "replace": {},
                    "blocks_hex": [bytes(changed).hex(), data.hex()]})
    req = {k: request[k] for k in ("op", "mode", "check_pow", "check_merkle_root", "adjusted_time")}
    req.update(chain=chain, bip34_ancestor_hex=request["bip34_ancestor_hex"] or bip34, coins=coins)
    return {"format": "dogelib-block-cases/1", "group": name,
            "seed": {"range": range_name, "height": height, "hash_display": sha256d(data[:80])[::-1].hex()},
            "request": req, "cases": out}


def cmd_groups(args) -> int:
    corpus, output = Path(args.corpus), Path(args.output)
    output.mkdir(parents=True, exist_ok=True)
    print("| Group | Block bytes | Chain entries | Coin entries | File bytes | xz bytes | Request bytes | SHA-256 of the file |")
    print("| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |")
    for name in RANGES:
        request = json.loads((corpus / name / "request.json").read_bytes())
        coins = {}
        for entry in request["coins"]:
            txid = bytes.fromhex(entry["txid_hex"])
            for o in entry["outputs"]:
                coins[(txid, o["n"])] = (entry["coinbase"], entry["height"], int(o["value"]),
                                         bytes.fromhex(o["script_hex"]))
        records = list(range_blocks(corpus / name / "fixture" / "blocks.bin"))
        largest = max(range(len(records)), key=lambda i: len(records[i][1]))
        chain = list(request["chain"])
        bip34 = None
        for i, (height, data) in enumerate(records[:largest + 1]):
            block = Block(data)
            if height == BIP34_HEIGHT:
                bip34 = sha256d(block.header).hex()
            labels = (["first"] if i == 0 else []) + (["largest"] if i == largest else [])
            for label in labels:
                named = {p[0] for tx in block.txs for p in tx.inputs}
                group_name = f"{name}-{label}-{height}"
                group = make_group(group_name, name, height, data, request, chain, coins_entries(coins, named),
                                   bip34 if height > BIP34_HEIGHT else None, args.cases)
                raw = compact(group) + b"\n"
                xz = lzma.compress(raw, format=lzma.FORMAT_XZ, preset=9 | lzma.PRESET_EXTREME)
                (output / f"{group_name}.json").write_bytes(raw)
                print(f"| {group_name} | {len(data):,} | {len(chain):,} | {len(group['request']['coins']):,} | "
                      f"{len(raw):,} | {len(xz):,} | {len(compact(group['request'])):,} | "
                      f"`{hashlib.sha256(raw).hexdigest()}` |", flush=True)
            # The block's changes to the coins, as Core's UpdateCoins and AddCoins make them.
            for k, tx in enumerate(block.txs):
                if k:
                    for prevout in tx.inputs:
                        coins.pop(prevout, None)
                for n, (value, script) in enumerate(tx.outputs):
                    if script[:1] == bytes([OP_RETURN]) or len(script) > MAX_SCRIPT_SIZE:
                        continue
                    coins[(tx.txid, n)] = (k == 0, height, value, script)
            entry = {"height": height, "time": int.from_bytes(block.header[68:72], "little"),
                     "bits": int.from_bytes(block.header[72:76], "little")}
            if "version" in chain[0]:
                entry["version"] = int.from_bytes(block.header[:4], "little")
            chain.insert(0, entry)
    return 0


# controls

def run_one(program, request, cpu=None):
    line = compact(request) + b"\n"
    command = ["taskset", "-c", cpu, "nice", "-n", "19", program] if cpu else [program]
    start = time.monotonic()
    done = subprocess.run(command, input=line, stdout=subprocess.PIPE, check=False)
    seconds = time.monotonic() - start
    if done.returncode:
        raise SystemExit(f"FAIL {program} exited with status {done.returncode}")
    return json.loads(done.stdout), seconds


def group_files(directory: Path):
    return sorted(p for p in directory.glob("*.json") if p.name.count("-") >= 2)


def cmd_controls(args) -> int:
    failures = 0
    for path in group_files(Path(args.groups)):
        group = json.loads(path.read_bytes())
        request = {**group["request"], "id": "control", "blocks_hex": group["cases"][0]["blocks_hex"]}
        results = []
        for program in args.programs:
            response, seconds = run_one(program, request)
            ok = response.get("ok")
            record = ok["blocks"][0] if ok else None
            results.append((record and record["valid"], record and record["changes_digest_hex"],
                            ok and ok["set_digest_hex"], round(seconds, 2)))
        seed = group["seed"]
        expected = None
        for line in (ROOT / "tests" / "conformance" / "ranges" / seed["range"] / "expected.jsonl").open():
            entry = json.loads(line)
            if entry.get("height") == seed["height"]:
                expected = entry
                break
        good = (len({r[:3] for r in results}) == 1 and results[0][0] is True and expected is not None
                and expected["valid"] and expected["changes_digest_hex"] == results[0][1])
        failures += not good
        print(f"{'PASS' if good else 'FAIL'} {path.stem}: " +
              ", ".join(f"{Path(p).name} {r[3]} s" for p, r in zip(args.programs, results)))
    return 1 if failures else 0


# time

def merkle_root(hashes):
    while len(hashes) > 1:
        if len(hashes) % 2:
            hashes = hashes + [hashes[-1]]
        hashes = [sha256d(hashes[i] + hashes[i + 1]) for i in range(0, len(hashes), 2)]
    return hashes[0]


def deep_candidate(data: bytes, k: int) -> bytes:
    block = Block(data)
    coinbase = block.txs[0]
    changed = bytearray(data)
    at = coinbase.value0
    value = int.from_bytes(changed[at:at + 8], "little") + k
    changed[at:at + 8] = value.to_bytes(8, "little")
    txid = Tx(Reader(bytes(changed[coinbase.start:coinbase.end]))).txid
    changed[36:68] = merkle_root([txid] + [tx.txid for tx in block.txs[1:]])
    return bytes(changed)


def shallow_candidate(data: bytes, k: int) -> bytes:
    changed = bytearray(data)
    changed[-1] ^= k  # the last byte of the lock time of the last transaction
    return bytes(changed)


def cmd_time(args) -> int:
    output = Path(args.output)
    rows = []
    for name in os.environ.get("SEEDS", DEFAULT_SEEDS).split():
        group = json.loads((Path(args.groups) / f"{name}.json").read_bytes())
        data = bytes.fromhex(group["cases"][0]["blocks_hex"][0])
        block = Block(data)
        for kind in ("baseline", "shallow", "deep"):
            request = {**group["request"], "id": kind}
            expected = {"accepted": 1}
            if kind == "baseline":
                request["blocks_hex"] = [data.hex()]
            else:
                make = deep_candidate if kind == "deep" else shallow_candidate
                request["blocks_hex"] = [make(data, k).hex() for k in range(1, 100)] + [data.hex()]
                expected["bad-cb-amount" if kind == "deep" else "bad-txnmrklroot"] = 99
                if kind == "deep":
                    request["check_pow"] = False
            digest = None
            for program in args.programs:
                response, seconds = run_one(program, request, args.cpu)
                ok = response.get("ok")
                if not ok:
                    print(f"FAIL {name} {kind} {program}: {json.dumps(response)[:300]}")
                    return 1
                got = {}
                for record in ok["blocks"]:
                    reason = record["reject_reason"] or "accepted"
                    got[reason] = got.get(reason, 0) + 1
                if got != expected or (digest is not None and ok["set_digest_hex"] != digest):
                    print(f"FAIL {name} {kind} {program}: {got}, {ok['set_digest_hex']}")
                    return 1
                digest = ok["set_digest_hex"]
                rows.append({"group": name, "kind": kind, "program": program, "seconds": round(seconds, 3),
                             "blocks": len(request["blocks_hex"]), "block_bytes": len(data),
                             "transactions": len(block.txs), "inputs": sum(len(t.inputs) for t in block.txs[1:]),
                             "chain": len(request["chain"]), "results": got})
                print(json.dumps(rows[-1]), flush=True)
                output.write_text(json.dumps(rows, indent=1) + "\n")
    return 0


# mine

def made_coinbase(sample: int) -> bytes:
    script = bytes([1, 1]) + sample.to_bytes(4, "little")  # the height 1, then the sample index
    output = (5 * 10**12).to_bytes(8, "little") + bytes([1, 0x51])  # OP_TRUE
    return (b"\x01\x00\x00\x00\x01" + bytes(32) + b"\xff" * 4 + bytes([len(script)]) + script
            + b"\xff" * 4 + b"\x01" + output + bytes(4))


def made_header(sample: int, nonce: int) -> bytes:
    return ((1).to_bytes(4, "little") + GENESIS_HASH + sha256d(made_coinbase(sample))
            + (GENESIS_TIME + 60).to_bytes(4, "little") + GENESIS_BITS.to_bytes(4, "little")
            + nonce.to_bytes(4, "little"))


def target(bits: int) -> int:
    return (bits & 0xffffff) << (8 * ((bits >> 24) - 3))


def scrypt_value(header: bytes) -> int:
    return int.from_bytes(hashlib.scrypt(header, salt=header, n=1024, r=1, p=1, dklen=32), "little")


def mine_worker(sample, start, stride, found, tries):
    limit = target(GENESIS_BITS)
    prefix = made_header(sample, 0)[:76]
    nonce = start
    while not found.value:
        if scrypt_value(prefix + nonce.to_bytes(4, "little")) <= limit:
            with found.get_lock():
                if not found.value or nonce < found.value - 1:
                    found.value = nonce + 1
        nonce += stride
        with tries.get_lock():
            tries.value += 1


def cmd_mine(args) -> int:
    rows = []
    for sample in range(args.samples):
        found, tries = multiprocessing.Value("q", 0), multiprocessing.Value("q", 0)
        start = time.monotonic()
        workers = [multiprocessing.Process(target=mine_worker, args=(sample, w, args.workers, found, tries))
                   for w in range(args.workers)]
        for w in workers:
            w.start()
        for w in workers:
            w.join()
        seconds = time.monotonic() - start
        nonce = found.value - 1
        rows.append({"sample": sample, "workers": args.workers, "nonce": nonce, "hashes": tries.value,
                     "seconds": round(seconds, 2), "hashes_per_second": round(tries.value / seconds),
                     "header_hex": made_header(sample, nonce).hex()})
        print(json.dumps(rows[-1]), flush=True)
    Path(args.output).write_text(json.dumps(rows, indent=1) + "\n")
    if args.check:
        requests = []
        for row in rows:
            header = bytes.fromhex(row["header_hex"])
            below = header[:76] + (row["nonce"] - 1).to_bytes(4, "little")
            # The nonce below the found one is a control only when it fails.
            if scrypt_value(below) <= target(GENESIS_BITS):
                below = None
            for label, value in (("mined", header), ("below", below)):
                if value is not None:
                    requests.append(({"id": f"{label}-{row['sample']}", "op": "block.check_pow", "bytes_hex": value.hex(),
                                      "mode": "allow_witness", "network": "mainnet", "selection_height": 1},
                                     label == "mined"))
        stream = b"".join(compact(r) + b"\n" for r, _ in requests)
        for program in args.check:
            lines = subprocess.run([program], input=stream, stdout=subprocess.PIPE, check=True).stdout.splitlines()
            got = [json.loads(line)["ok"]["valid"] for line in lines]
            if got != [want for _, want in requests]:
                print(f"FAIL {program}: block.check_pow gave {got}")
                return 1
            print(f"PASS {program}: block.check_pow accepts each mined header and rejects each header with the nonce below")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("groups")
    p.add_argument("--corpus", default="build/conformance")
    p.add_argument("--cases", type=int, default=40)
    p.add_argument("--output", required=True)
    p = sub.add_parser("controls")
    p.add_argument("--groups", required=True)
    p.add_argument("programs", nargs=2)
    p = sub.add_parser("time")
    p.add_argument("--groups", required=True)
    p.add_argument("--cpu", required=True, help="the CPU of taskset for every run")
    p.add_argument("--output", required=True)
    p.add_argument("programs", nargs="+")
    p = sub.add_parser("mine")
    p.add_argument("--samples", type=int, required=True)
    p.add_argument("--workers", type=int, required=True)
    p.add_argument("--output", required=True)
    p.add_argument("--check", nargs=2, metavar=("ORACLE", "HARNESS"))
    args = parser.parse_args()
    return {"groups": cmd_groups, "controls": cmd_controls, "time": cmd_time,
            "mine": cmd_mine}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
