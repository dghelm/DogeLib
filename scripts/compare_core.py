"""Compare dogelib-oracle with the Dogecoin Core harness on the same requests.

Usage: python3 -I scripts/compare_core.py [--timeout SECONDS] [--quick] <dogelib-oracle> <core-oracle>

The harness, harness/core/core_oracle.cpp, runs Dogecoin Core's own code and
answers a projection of dogelib-oracle/5 (docs/oracle.md, "The Core harness").
This script builds a deterministic stream of well-formed requests, runs each
program once on the whole stream, and requires the two responses to every
supported request to be equal as JSON values, except for the preimage projection: Core does not expose
the preimage of `sighash.legacy`, so the oracle's `preimage_hex` must hash to
Core's digest instead.
Script unsupported results have no compared verdict and are counted separately.

Each failure line starts with `FAIL <CODE>`; scripts/test_compare_core.py
relies on the codes. The exit status is 0 only when every response agrees.

With `--rust-compactsize PATH`, only CompactSize reader requests from the
fixtures and CompactSize boundary set run through all three programs.
The Rust crate has no encoder.
The comparator reads the oracle version at runtime and passes it to the adapter.

The transaction field walker below only locates fields in transactions that
are known to parse. No expected value comes from this script.
"""

import argparse
import hashlib
import json
import os
import pathlib
import random
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
# Import only the helper beside this script, including under Python's isolated mode.
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_hash_block import header_fields, header_records, header_fixtures, merkle_fixtures, hash_fixtures, sha1_fixtures

from oracle_script import script_sets, corpus_records, evaluation, validate_eval, adapter_limit_cases

ORACLE_FORMAT = "dogelib-oracle/5"
MAX_SIZE = 0x02000000
SEED = 20261104
MAX_REPORTS = 10


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


class RunError(Exception):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def run_program(program: str, args: list[str], data: str, timeout: float) -> str:
    """Run `program` with `data` on standard input and return its standard output.

    The program and any children it starts are killed when the timeout passes."""
    proc = subprocess.Popen([program, *args], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = proc.communicate(data, timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        raise RunError("TIMEOUT", f"{program} did not finish within {timeout} seconds")
    if proc.returncode != 0:
        raise RunError("EXIT", f"{program} exited with status {proc.returncode}: {err.strip()[:500]}")
    return out


def run_stream(program: str, requests: list[dict], timeout: float, args: list[str] | None = None) -> list[dict]:
    """The responses of `program` to `requests`, one per request, ids checked in order."""
    data = "".join(json.dumps(r, sort_keys=True, separators=(",", ":")) + "\n" for r in requests)
    lines = run_program(program, args or [], data, timeout).splitlines()
    if len(lines) != len(requests):
        raise RunError("COUNT", f"{program}: {len(lines)} responses to {len(requests)} requests")
    responses = []
    for req, line in zip(requests, lines):
        try:
            resp = json.loads(line)
        except json.JSONDecodeError:
            raise RunError("MALFORMED", f"{program}: response to {req['id']} is not JSON: {line[:200]}")
        if not isinstance(resp, dict):
            raise RunError("MALFORMED", f"{program}: response to {req['id']} is not an object: {line[:200]}")
        if resp.get("id") != req["id"]:
            raise RunError("ID", f"{program}: expected id {req['id']}, got {json.dumps(resp.get('id'))}")
        responses.append(resp)
    return responses


# ---------------------------------------------------------------------------
# Encoding helpers


def compact_size(n: int) -> bytes:
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xffffffff:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


def compact_size_width(prefix: int, n: int) -> bytes:
    """`n` written in the form that `prefix` selects, canonical or not."""
    size = {0xfd: 2, 0xfe: 4, 0xff: 8}[prefix]
    return bytes([prefix]) + n.to_bytes(size, "little")


def read_compact_size(b: bytes, pos: int) -> tuple[int, int]:
    first = b[pos]
    if first < 0xfd:
        return first, pos + 1
    size = {0xfd: 2, 0xfe: 4, 0xff: 8}[first]
    return int.from_bytes(b[pos + 1:pos + 1 + size], "little"), pos + 1 + size


def walk_tx(b: bytes, witness: bool = False) -> dict:
    """Field offsets of a transaction known to parse in the selected format.

    Returns `counts`: (offset, end, value) of each CompactSize field, and
    `fixed`: (offset, size, name) of the version, each sequence, each output
    value and the lock time."""
    counts, fixed = [], [(0, 4, "version")]
    pos = 4
    start = pos
    n_in, pos = read_compact_size(b, pos)
    counts.append((start, pos, n_in))
    flags = 0
    if witness and n_in == 0:
        flags = b[pos]
        pos += 1
        if flags:
            start = pos
            n_in, pos = read_compact_size(b, pos)
            counts.append((start, pos, n_in))
    for _ in range(n_in):
        pos += 36
        start = pos
        length, pos = read_compact_size(b, pos)
        counts.append((start, pos, length))
        pos += length
        fixed.append((pos, 4, "sequence"))
        pos += 4
    start = pos
    if witness and n_in == 0 and flags == 0:
        n_out = 0
    else:
        n_out, pos = read_compact_size(b, pos)
        counts.append((start, pos, n_out))
    for _ in range(n_out):
        fixed.append((pos, 8, "value"))
        pos += 8
        start = pos
        length, pos = read_compact_size(b, pos)
        counts.append((start, pos, length))
        pos += length
    stacks = []
    if witness and flags & 1:
        for _ in range(n_in):
            stack_start = pos
            start = pos
            n_items, pos = read_compact_size(b, pos)
            counts.append((start, pos, n_items))
            for _ in range(n_items):
                start = pos
                length, pos = read_compact_size(b, pos)
                counts.append((start, pos, length))
                pos += length
            stacks.append((stack_start, pos))
    fixed.append((pos, 4, "lock_time"))
    pos += 4
    if pos != len(b):
        raise ValueError("not a complete transaction in the selected format")
    return {"counts": counts, "fixed": fixed, "inputs": n_in, "outputs": n_out, "stacks": stacks}


# ---------------------------------------------------------------------------
# Request sets


def load_fixtures() -> tuple[list[dict], list[str]]:
    """Fixture requests whose expected response is not a request error.

    Returns the requests and the ids of the records left out, with the reason."""
    req_lines = (ROOT / "tests/oracle/requests.jsonl").read_text().splitlines()
    exp_lines = (ROOT / "tests/oracle/expected.jsonl").read_text().splitlines()
    kept, excluded = [], []

    def no_duplicates(pairs):
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            raise ValueError("repeated key")
        return dict(pairs)

    for req_line, exp_line in zip(req_lines, exp_lines):
        expected = json.loads(exp_line)
        label = json.dumps(expected.get("id"))
        if expected.get("error", {}).get("kind") in ("request", "work_view"):
            excluded.append(f"{label} ({expected['error']['kind']} error)")
            continue
        try:
            req = json.loads(req_line, object_pairs_hook=no_duplicates)
        except ValueError as e:
            excluded.append(f"{label} ({e})")
            continue
        if req.get("op") == "oracle.version":
            excluded.append(f"{label} (oracle.version: checked by the version rule)")
            continue
        kept.append(req)
    return kept, excluded


def sighash_records() -> list[list]:
    records = json.loads((ROOT / "tests/transaction/sighash/sighash.json").read_text())
    return [r for r in records if len(r) == 5]


def corpus_txs(witness: bool = False) -> list[bytes]:
    txs = []
    for name in ("tx_valid.json", "tx_invalid.json"):
        records = json.loads((ROOT / "tests/transaction/corpus" / name).read_text())
        # Base mode: the byte after the version is not the zero marker of the extended format.
        txs += [bytes.fromhex(r[1]) for r in records if len(r) == 3 and (witness or r[1][8:10] != "00")]
    return txs


def tx_requests(b: bytes, witness: bool = False) -> list[dict]:
    mode = "witness" if witness else "base"
    return [{"op": f"tx.read_{mode}", "bytes_hex": b.hex()}, {"op": f"tx.decode_{mode}", "bytes_hex": b.hex()}]


def set_corpus(txs: list[bytes], witness: bool = False) -> list[dict]:
    return [r for b in txs for r in tx_requests(b, witness)]


def set_prefixes(txs: list[bytes], witness: bool = False) -> list[dict]:
    return [r for b in txs for n in range(len(b)) for r in
            (tx_requests(b[:n], True) if witness else tx_requests(b[:n])[:1])]


def set_suffixes(txs: list[bytes], witness: bool = False) -> list[dict]:
    suffixes = [b"\x00", b"\xfd\x01\x02", bytes(range(40))]
    return [r for b in txs for s in suffixes for r in tx_requests(b + s, witness)]


def count_variants(value: int) -> list[bytes]:
    """Replacements for a CompactSize field that holds `value`."""
    out = []
    for prefix in (0xfd, 0xfe, 0xff):
        if value < 1 << (8 * {0xfd: 2, 0xfe: 4, 0xff: 8}[prefix]):
            out.append(compact_size_width(prefix, value))
    out += [compact_size(MAX_SIZE), compact_size(MAX_SIZE + 1), compact_size_width(0xff, MAX_SIZE + 1),
            compact_size_width(0xff, (1 << 64) - 1), b"\xfd", b"\xfe\x01\x00", b"\xff\x00\x00\x00\x00\x00\x00\x01"]
    return [v for v in out if v != compact_size(value)]


def set_fields(txs: list[bytes], witness: bool = False) -> list[dict]:
    reqs = []
    for b in txs:
        w = walk_tx(b, witness)
        for start, end, value in w["counts"]:
            for v in count_variants(value):
                mutated = b[:start] + v + b[end:]
                reqs += tx_requests(mutated, witness)
                # The replaced field followed by nothing: an error in the field, then the end of input.
                reqs += tx_requests(b[:start] + v, witness)
        for start, end in w["stacks"]:
            # Empty stack, one empty item, two empty items and one byte item.
            for stack in (b"\x00", b"\x01\x00", b"\x02\x00\x00", b"\x01\x01\xab"):
                reqs += tx_requests(b[:start] + stack + b[end:], witness)
        for start, size, name in w["fixed"]:
            if name == "value":
                values = [0, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]
            else:
                values = [0, 0x7fffffff, 0x80000000, 0xffffffff]
            for value in values:
                mutated = b[:start] + value.to_bytes(size, "little") + b[start + size:]
                reqs.append(tx_requests(mutated, witness)[1])
    return reqs


def build_tx(version: bytes, inputs: list[bytes], outputs: list[bytes], lock_time: bytes) -> bytes:
    return (version + compact_size(len(inputs)) + b"".join(inputs) + compact_size(len(outputs))
            + b"".join(outputs) + lock_time)


def set_shapes(txs: list[bytes]) -> list[dict]:
    """Transactions with no inputs, no outputs or empty scripts."""
    reqs = []
    for b in txs:
        w = walk_tx(b)
        version, lock_time = b[:4], b[-4:]
        pos = w["counts"][0][1]
        inputs, empty_inputs = [], []
        for _ in range(w["inputs"]):
            prevout = b[pos:pos + 36]
            length, after = read_compact_size(b, pos + 36)
            script = b[after:after + length]
            sequence = b[after + length:after + length + 4]
            inputs.append(prevout + compact_size(len(script)) + script + sequence)
            empty_inputs.append(prevout + b"\x00" + sequence)
            pos = after + length + 4
        _, pos = read_compact_size(b, pos)
        outputs, empty_outputs = [], []
        for _ in range(w["outputs"]):
            value = b[pos:pos + 8]
            length, after = read_compact_size(b, pos + 8)
            outputs.append(value + compact_size(length) + b[after:after + length])
            empty_outputs.append(value + b"\x00")
            pos = after + length
        for shaped in (build_tx(version, [], outputs, lock_time), build_tx(version, inputs, [], lock_time),
                       build_tx(version, [], [], lock_time), build_tx(version, empty_inputs, empty_outputs, lock_time)):
            reqs += tx_requests(shaped)
            reqs += tx_requests(shaped[:-1])
    return reqs


def set_compactsize() -> list[dict]:
    values = {0, 1, 0xfc, 0xfd, 0xfe, 0xff, 0x100, 0xfffe, 0xffff, 0x10000, 0x10001, MAX_SIZE - 1, MAX_SIZE,
              MAX_SIZE + 1, 0xfffffffe, 0xffffffff, 0x100000000, 0x100000001, (1 << 63), (1 << 64) - 2, (1 << 64) - 1}
    reqs = [{"op": "compactsize.encode", "value": str(v)} for v in sorted(values)]
    forms = set()
    for v in values:
        forms.add(compact_size(v))
        for prefix in (0xfd, 0xfe, 0xff):
            if v < 1 << (8 * {0xfd: 2, 0xfe: 4, 0xff: 8}[prefix]):
                forms.add(compact_size_width(prefix, v))
    for form in sorted(forms):
        for n in range(len(form) + 1):
            reqs.append({"op": "compactsize.read", "bytes_hex": form[:n].hex()})
        reqs.append({"op": "compactsize.read", "bytes_hex": (form + b"\xab\xcd").hex()})
    return reqs


HASH_TYPES = [-2 ** 31, -1, 0, 1, 2, 3, 4, 0x81, 0x82, 0x83, 0x7fffffff, 2 ** 31, 2 ** 32 - 1]


def sighash_request(tx: str, code: str, n: int, h: int) -> dict:
    return {"op": "sighash.legacy", "tx_hex": tx, "script_code_hex": code, "input_index": n, "hash_type": h}


def set_sighash_corpus(records: list[list]) -> list[dict]:
    return [sighash_request(tx, code, n, h) for tx, code, n, h, _ in records]


def set_sighash_endpoints(records: list[list]) -> list[dict]:
    reqs = []
    for tx, code, _, _, _ in records[:25]:
        w = walk_tx(bytes.fromhex(tx))
        indices = {0, w["inputs"], w["inputs"] + 1, 2 ** 32 - 1}
        if w["inputs"] > 0:
            indices.add(w["inputs"] - 1)
        for n in sorted(indices):
            for h in HASH_TYPES:
                reqs.append(sighash_request(tx, code, n, h))
    # The argument tx_hex fails to read: truncated, non-canonical, trailing bytes.
    tx = bytes.fromhex(records[0][0])
    w = walk_tx(tx)
    start, end, value = w["counts"][0]
    for bad in (tx[:-1], tx[:start] + compact_size_width(0xfd, value) + tx[end:], tx + b"\x00\x00"):
        reqs.append(sighash_request(bad.hex(), "", 0, 1))
    return reqs


def random_script(rng: random.Random) -> bytes:
    parts = []
    for _ in range(rng.randrange(0, 12)):
        kind = rng.randrange(6)
        if kind == 0:
            parts.append(b"\xab")  # OP_CODESEPARATOR
        elif kind == 1:
            n = rng.randrange(1, 76)
            parts.append(bytes([n]) + rng.randbytes(rng.randrange(0, n + 1)))  # possibly truncated push
        elif kind == 2:
            parts.append(b"\x4c" + bytes([rng.randrange(256)]) + rng.randbytes(rng.randrange(0, 4)))
        elif kind == 3:
            parts.append(b"\x4d" + rng.randbytes(rng.randrange(0, 3)))
        elif kind == 4:
            parts.append(b"\x4e" + rng.randbytes(rng.randrange(0, 5)))
        else:
            parts.append(rng.randbytes(rng.randrange(1, 4)))
    return b"".join(parts)


def set_sighash_random(records: list[list], rng: random.Random, count: int) -> list[dict]:
    reqs = []
    for _ in range(count):
        tx = rng.choice(records)[0]
        inputs = walk_tx(bytes.fromhex(tx))["inputs"]
        # Mostly an input that exists, so that most cases hash a preimage.
        if inputs > 0 and rng.random() < 0.8:
            n = rng.randrange(inputs)
        else:
            n = rng.choice([inputs, inputs + 1, 2 ** 32 - 1])
        h = rng.choice([rng.choice(HASH_TYPES), rng.randrange(256), 0x80 | rng.randrange(1, 4),
                        rng.randrange(2 ** 32), -rng.randrange(1, 2 ** 31 + 1)])
        reqs.append(sighash_request(tx, random_script(rng).hex(), n, h))
    return reqs


def set_flips(txs: list[bytes], rng: random.Random, count: int, witness: bool = False) -> list[dict]:
    reqs = []
    for _ in range(count):
        b = bytearray(rng.choice(txs))
        for _ in range(rng.randrange(1, 4)):
            b[rng.randrange(len(b))] = rng.randrange(256)
        reqs += tx_requests(bytes(b), True) if witness else tx_requests(bytes(b))[:1]
    return reqs


def set_witness_cases() -> list[dict]:
    """Source-derived flag and stack cases from tests/KnownAnswers.lean, Witness.cases."""
    version, lock = bytes.fromhex("01000000"), bytes(4)
    txin = bytes(36) + b"\x00" + bytes.fromhex("ffffffff")
    txout = bytes(9)

    def extended(flags, stack):
        return version + bytes([0, flags, 1]) + txin + b"\x01" + txout + stack

    cases = [version + b"\x00\x00" + lock, version + b"\x00\x00", version + b"\x00",
             version + b"\x00\x01\x00\x01" + txout + lock]
    for flags in (1, 2, 3, 0xff):
        stacks = (b"",) if flags == 2 else (b"\x01\x01\xab", b"\x00", b"\x01\x00",
                  b"\x01\x05\xab", b"\xfd\x01\x00\x01\xab", compact_size(MAX_SIZE + 1),
                  b"\x01" + compact_size(MAX_SIZE + 1))
        for stack in stacks:
            cases += [extended(flags, stack), extended(flags, stack) + lock]
    cases.append(version + b"\x00\x02\x01" + txin + b"\x01" + txout[:4])
    cases.append(extended(1, b"\x01\x01\xab") + lock + b"\x00")
    return [r for b in cases for r in tx_requests(b, True)]


def set_large_base() -> list[dict]:
    """Structured base requests across count widths and larger script lengths.

    Core supplies the comparison results for successes and malformed variants.
    """
    requests = []
    for inputs, outputs, script_size in ((253, 253, 0), (254, 254, 1),
                                          (1000, 1, 0), (1, 1000, 0),
                                          (2, 2, 4096), (1, 4, 16384)):
        script = b"\x51" * script_size
        txin = bytes(36) + compact_size(script_size) + script + b"\xff" * 4
        txout = (1).to_bytes(8, "little") + compact_size(script_size) + script
        tx = build_tx((1).to_bytes(4, "little"), [txin] * inputs,
                      [txout] * outputs, bytes(4))
        fields = walk_tx(tx)
        # Select both vector counts and the first script length of each kind.
        selected = [fields["counts"][i] for i in (0, 1, inputs + 1, inputs + 2)]
        variants = [tx, tx + b"\x00", tx + b"\xfd\x01\x02", tx + bytes(range(40))]
        for start, end, value in selected:
            variants.extend(tx[:start] + replacement + tx[end:]
                            for replacement in count_variants(value))
            variants.extend(tx[:n] for n in range(start, end))
        # End within a script, a sequence, an amount and the lock time.
        variants.extend(tx[:n] for n in (selected[1][1] + script_size // 2,
                                         4 + len(compact_size(inputs)) + len(txin) - 1,
                                         selected[2][1] + 7,
                                         selected[3][1] + script_size // 2, len(tx) - 1))
        for data in variants:
            requests.extend(tx_requests(data))
            requests.append(sighash_request(data.hex(), "51", 0, 1))
    return requests


# Work requests carry no generated expected results. Core supplies the comparison.
def set_work_compact() -> list[dict]:
    requests = []
    for size in range(256):
        for word in (0, 1, 0x7f, 0x80, 0xff, 0x100, 0xffff, 0x10000, 0x123456, 0x7fffff):
            for sign in (0, 0x800000):
                requests.append({"op": "work.set_compact", "compact": size << 24 | sign | word})
    values = {0, (1 << 256) - 1}
    for bit in range(256):
        values.update(v for v in ((1 << bit) - 1, 1 << bit, (1 << bit) + 1) if v < 1 << 256)
    for value in sorted(values):
        for negative in (False, True):
            requests.append({"op": "work.get_compact", "value_hex": f"{value:064x}", "negative": negative})
    return requests


def calculate_request(network, selection, height, last_time, first_time, bits):
    return {"op": "work.calculate_next", "network": network, "selection_height": selection,
            "last_height": height, "last_time": last_time, "first_time": first_time, "last_bits": bits}


def set_work_retarget() -> list[dict]:
    requests = []
    for network in ("mainnet", "testnet", "regtest"):
        for selection in (0, 9, 10, 19, 20, 144999, 145000, 157499, 157500, 158100, 371337, 0xffffffff):
            for height in (0, 4999, 5000, 9999, 10000, 145000, 2147483646):
                # Include clamp boundaries for every network timespan, and negative differences.
                spans = {-69, -68, -67, -8, -7, -6, -1, 0, 1, 2, 7, 8, 9,
                         48, 52, 59, 60, 61, 67, 68, 69, 307, 308, 309,
                         899, 900, 901, 1799, 1800, 1801, 3599, 3600, 3601,
                         14399, 14400, 14401, 57599, 57600, 57601}
                for span in sorted(spans):
                    for bits in (0, 0x04923456, 0x1b671062, 0x207fffff, 0xff123456):
                        requests.append(calculate_request(network, selection, height, 100000 + span, 100000, bits))
            for last_time, first_time in ((0, 0xffffffff), (0xffffffff, 0), (0xffffffff, 0xffffffff)):
                requests.append(calculate_request(network, selection, 145000, last_time, first_time, 0x1e0fffff))
    return requests


def work_chain(height, count=241, bits=0x1c123456, spacing=60):
    return [{"height": h, "time": 1000000 + h % 100000 * spacing, "bits": bits}
            for h in range(height, max(-1, height - count), -1)]


def next_request(network, chain, candidate_time):
    return {"op": "work.next", "network": network, "chain": chain, "candidate_time": candidate_time}


def set_work_next() -> list[dict]:
    requests = []
    heights = (0, 1, 8, 9, 10, 19, 20, 238, 239, 240, 479, 4999, 5000, 9999, 10000,
               144998, 144999, 145000, 145001, 157498, 157499, 157500, 157501,
               158099, 158100, 371336, 371337, 2147483646)
    for network in ("mainnet", "testnet", "regtest"):
        spacing = 1 if network == "regtest" else 60
        requests.append(next_request(network, [], 0))
        for height in heights:
            for bits in (0x1c123456, 0x1e0fffff, 0x207fffff):
                chain = work_chain(height, bits=bits, spacing=spacing)
                for delay in (0, spacing * 2 - 1, spacing * 2, spacing * 2 + 1):
                    requests.append(next_request(network, chain, chain[0]["time"] + delay))
    return requests


def set_work_recovery() -> list[dict]:
    requests = []
    for height in (1, 2, 238, 240, 241, 478, 144998):
        for length in (1, 2, 10, 241):
            chain = work_chain(height, count=min(height + 1, 241), bits=0x1e0fffff)
            # Stop at a nonminimum entry or an interval boundary, before any missing link.
            stop = min(length - 1, len(chain) - 1)
            chain[stop] = {**chain[stop], "bits": 0x1c123456}
            requests.append(next_request("testnet", chain, chain[0]["time"] + 120))
    return requests


def set_work_headers() -> list[dict]:
    chain, requests = [], []
    for line in (ROOT / "tests/work/mainnet-headers/headers.txt").read_text().splitlines():
        height, raw = line.split()
        header = bytes.fromhex(raw)
        entry = {"height": int(height), "time": int.from_bytes(header[68:72], "little"),
                 "bits": int.from_bytes(header[72:76], "little")}
        # The first two records supply context, and 144720 lacks its retarget ancestor.
        if int(height) >= 144721:
            requests.append(next_request("mainnet", chain.copy(), entry["time"]))
        chain.insert(0, entry)
    return requests


def set_header_prefixes() -> list[dict]:
    return [{"op": "header.read", "bytes_hex": raw[:n].hex()}
            for raw, _ in header_records() for n in range(80)]


def set_header_boundaries() -> list[dict]:
    requests = []
    base = header_fields(bytes(range(80)))
    for field in ("version", "time", "bits", "nonce"):
        for value in (0, 1, 255, 256, 257, 0x7fffffff, 0x80000000, 0xffffffff):
            header = {**base, field: value}
            raw = (header["version"].to_bytes(4, "little") + bytes.fromhex(header["prev_block_hex"])
                   + bytes.fromhex(header["merkle_root_hex"])
                   + b"".join(header[k].to_bytes(4, "little") for k in ("time", "bits", "nonce")))
            requests.extend([{"op": "header.encode", "header": header},
                             {"op": "header.hash", "header": header},
                             {"op": "header.read", "bytes_hex": raw.hex() + "00ff"}])
    return requests


def set_merkle_generated() -> list[dict]:
    requests = []
    for n in range(65):
        leaves = [sha256d(i.to_bytes(4, "little")).hex() for i in range(n)]
        variants = [leaves]
        if n >= 2:
            variants.extend([[leaves[0]] * n, leaves[:-1] + [leaves[-2]]])
        width = 1
        while 2 * width <= n:
            # Equal aligned complete subtrees at each possible level, without padding.
            variants.append(leaves[:width] * 2 + leaves[2 * width:])
            width *= 2
        if n > 1 and n & (n - 1):
            # Duplicate the final complete subtree, as Core's deterministic test does.
            width = n & -n
            variants.append(leaves + leaves[-width:])
        requests.extend({"op": "merkle.compute", "leaves_hex": xs} for xs in variants)
    return requests


def set_hash_boundaries(algorithm: str) -> list[dict]:
    lengths = set(range(201))
    for blocks in range(1, 17):
        for delta in (-10, -9, -8, -1, 0, 1):
            lengths.add(64 * blocks + delta)
    return [{"op": "hash." + algorithm,
             "bytes_hex": bytes((i * 131 + n) & 255 for i in range(n)).hex()}
            for n in sorted(lengths)]


QUICK_SETS = ("fixtures", "compactsize", "sighash endpoints", "witness flags and stacks",
              "work compact boundaries", "regtest legacy wrap case", "work missing skip traversal", "header field boundaries", "Merkle generated",
              "RIPEMD-160 padding boundaries", "Hash160 padding boundaries", "SHA-1 padding boundaries", "Script reader truncations", "Script resource boundaries")


def request_sets() -> tuple[list[tuple[str, list[dict]]], list[str]]:
    rng = random.Random(SEED)
    fixtures, excluded = load_fixtures()
    records = sighash_records()
    corpus = corpus_txs()
    sighash_txs = [bytes.fromhex(r[0]) for r in records]
    all_txs = corpus + sighash_txs
    witness_corpus = corpus_txs(True)
    extended = [b for b in witness_corpus if b[4] == 0]
    sets = [
        ("fixtures", [r for r in fixtures if not str(r.get("id", "")).startswith(("work-d16-", "work-d7-"))]),
        ("work D16 bignum_SetCompact", [r for r in fixtures if str(r.get("id", "")).startswith("work-d16-")]),
        ("work D7 get_next_work", [r for r in fixtures if str(r.get("id", "")).startswith("work-d7-")]),
        ("sighash.json", set_sighash_corpus(records)),
        ("corpus", set_corpus(corpus)),
        ("prefixes", set_prefixes(all_txs)),
        ("suffixes", set_suffixes(all_txs)),
        ("count and fixed fields", set_fields(corpus + sighash_txs[:100])),
        ("shapes", set_shapes(corpus + sighash_txs[:100])),
        ("compactsize", set_compactsize()),
        ("sighash endpoints", set_sighash_endpoints(records)),
        ("sighash random", set_sighash_random(records, rng, 2000)),
        ("byte flips", set_flips(all_txs, rng, 5000)),
        ("witness corpus (all records)", set_corpus(witness_corpus, True)),
        ("witness corpus (extended records)", set_corpus(extended, True)),
        ("witness prefixes", set_prefixes(extended, True)),
        ("witness suffixes", set_suffixes(extended, True)),
        ("witness counts, lengths and stacks", set_fields(witness_corpus, True)),
        ("witness flags and stacks", set_witness_cases()),
        ("witness byte flips", set_flips(witness_corpus, rng, 5000, True)),
        ("large structured base", set_large_base()),
        ("work compact boundaries", set_work_compact()),
        ("work retarget boundaries", set_work_retarget()),
        ("regtest legacy wrap case", [calculate_request("regtest", 0, 1, 901, 0, 0x207fffff)]),
        ("work network chains", set_work_next()),
        ("work testnet recovery", set_work_recovery()),
        ("work mainnet headers", set_work_headers()),
        # Height 256 has no skip destination in this suffix. GetAncestor(239) crosses it.
        ("work missing skip traversal", [next_request("mainnet", work_chain(479), 1028800)]),
    ]
    sets.extend([
        ("header fixtures", [r for r, _ in header_fixtures()]),
        ("header truncated prefixes", set_header_prefixes()),
        ("header field boundaries", set_header_boundaries()),
        ("Merkle fixtures", [r for r, _ in merkle_fixtures()]),
        ("Merkle generated", set_merkle_generated()),
        ("RIPEMD-160 and Hash160 fixtures", [r for r, _ in hash_fixtures()]),
        ("RIPEMD-160 padding boundaries", set_hash_boundaries("ripemd160")),
        ("Hash160 padding boundaries", set_hash_boundaries("hash160")),
        ("SHA-1 fixtures", [r for r, _ in sha1_fixtures()]),
        ("SHA-1 padding boundaries", set_hash_boundaries("sha1")),
    ])
    sets.extend(script_sets())
    return sets, excluded


# ---------------------------------------------------------------------------
# Comparison


def json_equal(a, b) -> bool:
    """Equality of JSON values. Unlike Python's `==`, `true` is not `1` and `1.0` is not `1`."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(json_equal(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(json_equal(x, y) for x, y in zip(a, b))
    return a == b


def is_hex(s) -> bool:
    return isinstance(s, str) and len(s) % 2 == 0 and all(c in "0123456789abcdefABCDEF" for c in s)


def first_difference(a, b, path="") -> str:
    if type(a) is not type(b):
        return path or "/"
    if isinstance(a, dict):
        for k in sorted(set(a) | set(b)):
            if k not in a or k not in b:
                return f"{path}/{k}"
            if not json_equal(a[k], b[k]):
                return first_difference(a[k], b[k], f"{path}/{k}")
    if isinstance(a, list):
        if len(a) != len(b):
            return f"{path} (length)"
        for i, (x, y) in enumerate(zip(a, b)):
            if not json_equal(x, y):
                return first_difference(x, y, f"{path}/{i}")
    return path or "/"


def outcome(resp: dict) -> str:
    """A short name for the kind of a response, for the report."""
    if "ok" in resp:
        if "result" in resp["ok"]:
            return ":".join(str(resp["ok"][k]) for k in ("result", "reason", "script_error") if k in resp["ok"])
        plan = resp["ok"].get("plan")
        return f"ok:{plan}" if plan else "ok"
    err = resp.get("error", {})
    return ":".join(str(err[k]) for k in ("kind", "reason", "argument") if k in err)


def compare(req: dict, ours: dict, core: dict, peer: str = "core") -> tuple[str, str] | None:
    """None when the responses agree, else a failure code and a message."""
    for side, resp in (("oracle", ours), (peer, core)):
        if resp.get("error", {}).get("kind") == "request":
            return "REQUEST_ERROR", f"{side} rejected the request: {resp['error'].get('message')}"
    if req["op"] == "script.eval":
        for response, allow in ((ours, True), (core, False)):
            error = validate_eval(req, response, allow)
            if error:
                return "SCRIPT_RESULT", error
        if ours["ok"]["result"] == "unsupported":
            return None
    if req["op"] == "sighash.legacy" and "ok" in ours and "ok" in core:
        ok = dict(ours["ok"])
        if "preimage_hex" in core["ok"]:
            return "PROJECTION", "core response has preimage_hex"
        if ok.get("plan") == "hash_bytes":
            if "preimage_hex" not in ok:
                return "PREIMAGE", "oracle response has no preimage_hex for plan hash_bytes"
            preimage = ok.pop("preimage_hex")
            if not is_hex(preimage):
                return "PREIMAGE", "oracle preimage_hex is not a string of hexadecimal digits"
            if sha256d(bytes.fromhex(preimage)).hex() != core["ok"].get("digest_hex"):
                return "PREIMAGE", "oracle preimage does not hash to Core's digest"
        elif "preimage_hex" in ok:
            return "PREIMAGE", "oracle response has preimage_hex for plan fixed_digest"
        ours = {**ours, "ok": ok}
    if not json_equal(ours, core):
        return "MISMATCH", f"first difference at {first_difference(ours, core)}"
    return None


def check_versions(oracle: str, harness: str, timeout: float, oracle_format: str = ORACLE_FORMAT) -> list[str]:
    failures = []
    for program, expected in ((oracle, oracle_format), (harness, oracle_format + "-core-projection")):
        try:
            out = run_program(program, ["--version"], "", timeout).strip()
            resp = run_stream(program, [{"id": "version", "op": "oracle.version"}], timeout)[0]
        except RunError as e:
            failures.append(f"FAIL {e.code} {e}")
            continue
        if out != json.dumps({"format": expected}, separators=(",", ":")):
            failures.append(f"FAIL VERSION {program} --version printed {out!r}, expected format {expected}")
        if resp.get("ok") != {"format": expected}:
            failures.append(f"FAIL VERSION {program} oracle.version answered {json.dumps(resp)}")
    return failures


def compare_adapter_limits(oracle, harness, timeout):
    """Check both adapters against the documented resource-limit expectations."""
    cases = adapter_limit_cases()
    requests = [{**request, "id": f"resource-{i}"} for i, (request, _) in enumerate(cases)]
    try:
        ours = run_stream(oracle, requests, timeout)
        core = run_stream(harness, requests, timeout)
    except RunError as error:
        print(f"FAIL {error.code} Script adapter limits: {error}")
        return [error.code]
    failures = []
    for request, (_, expected), a, b in zip(requests, cases, ours, core):
        if not all(json_equal(response, {"id": request["id"], **expected}) for response in (a, b)):
            print(f"FAIL MISMATCH Script adapter limits: {request['id']}")
            failures.append("MISMATCH")
    print(f"Script adapter limits: {len(cases)} requests, {len(failures)} disagreements")
    return failures


def compare_compositions(oracle, harness, timeout):
    """Run two calls per corpus record, with each side's own successful stack."""
    records = corpus_records()
    first = [{**evaluation(bytes.fromhex(r["scriptSig_hex"]), r["effective_flags_mask"]),
              "id": f"composition-{r['source_index']}"} for r in records]
    try:
        sides = []
        for program in (oracle, harness):
            initial = run_stream(program, first, timeout)
            second = [{**evaluation(bytes.fromhex(r["scriptPubKey_hex"]), r["effective_flags_mask"], a["ok"]["stack_hex"]),
                       "id": req["id"]}
                      for r, req, a in zip(records, first, initial)
                      if a.get("ok", {}).get("result") == "accepted"]
            final = {r["id"]: r for r in run_stream(program, second, timeout)}
            sides.append((initial, final))
    except RunError as e:
        print(f"FAIL {e.code} Script corpus composition: {e}")
        return [e.code]
    failures, outcomes, unsupported = [], {}, {}
    for record, req, a, b in zip(records, first, sides[0][0], sides[1][0]):
        failure = compare(req, a, b)
        final_a = sides[0][1].get(req["id"], a)
        final_b = sides[1][1].get(req["id"], b)
        if failure is None:
            # An unsupported first call stays a first-call result.
            final_req = req if a.get("ok", {}).get("result") != "accepted" else {**req, "bytes_hex": record["scriptPubKey_hex"]}
            failure = compare(final_req, final_a, final_b)
        label = outcome(final_b)
        outcomes[label] = outcomes.get(label, 0) + 1
        if final_a.get("ok", {}).get("result") == "unsupported":
            label = final_a["ok"].get("reason", "malformed") + " -> Core " + label
            unsupported[label] = unsupported.get(label, 0) + 1
        if failure:
            failures.append(failure[0])
            if len(failures) <= MAX_REPORTS:
                print(f"FAIL {failure[0]} Script corpus composition source_index={req['id']}: {failure[1]}")
    skipped = sum(unsupported.values())
    print(f"Script corpus composition: {len(records)} records, {len(records) - skipped} compared, {skipped} unsupported, {len(failures)} disagreements")
    print("  Core's outcomes: " + ", ".join(f"{k} {v}" for k, v in sorted(outcomes.items())))
    for label, count in sorted(unsupported.items()):
        print(f"  unsupported {label}: {count}")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument("--quick", action="store_true",
                        help=f"only the sets {', '.join(QUICK_SETS)}, for the comparator's self-test")
    parser.add_argument("--rust-compactsize", metavar="PATH",
                        help="compare only CompactSize reader requests with this native Rust adapter as a third program")
    parser.add_argument("oracle")
    parser.add_argument("harness")
    args = parser.parse_args()

    rust_args = []
    if args.rust_compactsize:
        try:
            version = json.loads(run_program(args.oracle, ["--version"], "", args.timeout))
            oracle_format = version["format"]
            if oracle_format != ORACLE_FORMAT:
                raise ValueError(f"oracle format {oracle_format!r} does not match pinned {ORACLE_FORMAT}")
            rust_args = ["--oracle-format", oracle_format]
            expected = {"format": oracle_format + "-rust-compactsize"}
            rust_version = json.loads(run_program(args.rust_compactsize, [*rust_args, "--version"], "", args.timeout))
            response = run_stream(args.rust_compactsize, [{"id": "version", "op": "oracle.version"}],
                                  args.timeout, rust_args)[0]
            if not json_equal(rust_version, expected) or not json_equal(response, {"id": "version", "ok": expected}):
                raise ValueError("unexpected Rust projection format")
        except RunError as e:
            print(f"FAIL {e.code} {e}")
            return 1
        except (ValueError, KeyError, TypeError) as e:
            print(f"FAIL VERSION {e}")
            return 1
    else:
        oracle_format = ORACLE_FORMAT
    failures = check_versions(args.oracle, args.harness, args.timeout, oracle_format)
    for line in failures:
        print(line)

    if args.rust_compactsize:
        fixtures, excluded = load_fixtures()
        sets = [("fixtures", fixtures), ("compactsize", set_compactsize())]
        sets = [(name, [r for r in reqs if r["op"] == "compactsize.read"]) for name, reqs in sets]
        print("CompactSize-only: compiled Rust, oracle and Core (reader only, no Rust encoder)")
    else:
        sets, excluded = request_sets()
    if args.quick:
        sets = [(name, reqs) for name, reqs in sets if name in QUICK_SETS]
    print(f"fixtures left out: {len(excluded)}")
    for e in excluded:
        print(f"  {e}")

    requests = []
    owner = []
    for name, reqs in sets:
        for r in reqs:
            requests.append({**r, "id": f"c{len(requests)}"})
            owner.append(name)
    try:
        ours = run_stream(args.oracle, requests, args.timeout)
        core = run_stream(args.harness, requests, args.timeout)
        rust = run_stream(args.rust_compactsize, requests, args.timeout, rust_args) if args.rust_compactsize else None
    except RunError as e:
        print(f"FAIL {e.code} {e}")
        return 1

    per_set = {name: [len(reqs), 0] for name, reqs in sets}
    outcomes = {name: {} for name, _ in sets}
    unsupported = {name: {} for name, _ in sets}
    reported = 0
    for i, (req, name, a, b) in enumerate(zip(requests, owner, ours, core)):
        kind = outcome(b)
        if req["op"] == "script.eval" and a.get("ok", {}).get("result") == "unsupported":
            label = a["ok"].get("reason", "malformed") + " -> Core " + kind
            unsupported[name][label] = unsupported[name].get(label, 0) + 1
        outcomes[name][kind] = outcomes[name].get(kind, 0) + 1
        result = compare(req, a, b)
        if result is None and rust is not None:
            result = compare(req, a, rust[i], "rust")
        if result is None:
            continue
        per_set[name][1] += 1
        failures.append(result[0])
        if reported < MAX_REPORTS:
            reported += 1
            code, message = result
            print(f"FAIL {code} [{name}] {message}")
            print(f"  request: {json.dumps(req)[:400]}")
            print(f"  oracle:  {json.dumps(a)[:400]}")
            print(f"  core:    {json.dumps(b)[:400]}")
            if rust is not None:
                print(f"  rust:    {json.dumps(rust[i])[:400]}")
    for name, (total, bad) in per_set.items():
        skipped = sum(unsupported[name].values())
        print(f"{name}: {total} requests, {total - skipped} compared, {skipped} unsupported, {bad} disagreements")
        for label, count in sorted(unsupported[name].items()):
            print(f"  unsupported {label}: {count}")
        print("  Core's outcomes: " + ", ".join(f"{k} {v}" for k, v in sorted(outcomes[name].items())))
    if not args.quick and not args.rust_compactsize:
        failures.extend(compare_adapter_limits(args.oracle, args.harness, args.timeout))
        failures.extend(compare_compositions(args.oracle, args.harness, args.timeout))
    print(f"total: {len(requests)} stream requests, {len(failures)} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
