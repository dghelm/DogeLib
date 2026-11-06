"""Tests of the oracle, `dogelib-oracle`, through its standard input and output.

Usage: python3 -I scripts/test_oracle.py <path to dogelib-oracle>

`scripts/test_oracle.sh` builds the oracle and runs this file. It checks five things:

1. Each request of `tests/oracle/requests.jsonl` gets the response on the same line of
   `tests/oracle/expected.jsonl`. Two parts of a response are not compared exactly:
   - an `error` of kind `request` is compared by its kind only, because its message is free text;
   - an expected `preimage_hex` of `"*"` requires a preimage whose double SHA-256 is `digest_hex`.
2. Every record of Core's `sighash.json` gets Core's digest from `sighash.legacy`.
3. Every base-mode record of Core's `tx_valid.json` and `tx_invalid.json` gets its own bytes back
   from `tx.decode_base`, and a transaction ID equal to the double SHA-256 that `hashlib` computes.
4. Every transaction corpus record passes both witness operations. Its stacks and base bytes follow
   D4's field layout. Its witness serialization and both hashes agree with those bytes and `hashlib`.
5. The process answers each line before it reads the next, keeps going after a malformed line,
   skips blank lines, and answers a final line that has no newline.

The expected values come from Core's files, Core's source and `hashlib`, never from the oracle.
`tests/oracle/README.md` gives the source of each fixture.
"""

import hashlib
import json
import pathlib
import subprocess
import sys
import threading

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_hash_block import header_fixtures, merkle_fixtures, hash_fixtures, sha1_fixtures

from oracle_script import adapter_limit_cases

TIMEOUT = 10


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def run_batch(oracle: str, lines: list[str]) -> list[dict]:
    """The responses to `lines`, sent in one batch."""
    out = subprocess.run([oracle], input="\n".join(lines) + "\n", capture_output=True, text=True,
                         check=True, timeout=600).stdout
    return [json.loads(line) for line in out.splitlines()]


def run_requests(oracle: str, name: str, requests: list[dict]) -> list[dict] | None:
    """The responses to `requests`, or `None` after a report when they are not one per request with each `id` in order."""
    got = run_batch(oracle, [json.dumps(r) for r in requests])
    if len(got) != len(requests):
        print(f"FAIL {name}: {len(got)} responses to {len(requests)} requests")
        return None
    for line, (req, resp) in enumerate(zip(requests, got), start=1):
        if resp.get("id") != req["id"]:
            print(f"FAIL {name}: response {line} has id {resp.get('id')!r}, expected {req['id']!r}")
            return None
    return got


def matches(got, want) -> bool:
    """Whether a response matches its expected value, with the two exceptions of item 1."""
    if isinstance(want, dict) and isinstance(got, dict):
        if want.get("kind") == "request" and set(want) == {"kind"}:
            return got.get("kind") == "request" and set(got) == {"kind", "message"}
        if want.get("preimage_hex") == "*":
            pre = got.get("preimage_hex")
            if not isinstance(pre, str) or sha256d(bytes.fromhex(pre)).hex() != got.get("digest_hex"):
                return False
            got = {k: v for k, v in got.items() if k != "preimage_hex"}
            want = {k: v for k, v in want.items() if k != "preimage_hex"}
        return set(got) == set(want) and all(matches(got[k], want[k]) for k in want)
    if isinstance(want, list) and isinstance(got, list):
        return len(got) == len(want) and all(matches(g, w) for g, w in zip(got, want))
    return type(got) is type(want) and got == want


def check_fixtures(oracle: str) -> int:
    requests = (ROOT / "tests/oracle/requests.jsonl").read_text().splitlines()
    expected = [json.loads(line) for line in (ROOT / "tests/oracle/expected.jsonl").read_text().splitlines()]
    got = run_batch(oracle, requests)
    failures = 0
    if len(got) != len(expected):
        print(f"FAIL fixtures: {len(got)} responses to {len(expected)} requests")
        return 1
    for line, (g, e) in enumerate(zip(got, expected), start=1):
        if not matches(g, e):
            failures += 1
            print(f"FAIL fixture line {line}: got {json.dumps(g)}, expected {json.dumps(e)}")
    print(f"fixtures: {len(expected)} records, {failures} failures")
    return failures


def check_sighash_corpus(oracle: str) -> int:
    records = json.loads((ROOT / "tests/transaction/sighash/sighash.json").read_text())
    records = [r for r in records if len(r) == 5]
    requests = [{"id": i, "op": "sighash.legacy", "tx_hex": tx, "script_code_hex": code,
                 "input_index": n, "hash_type": h}
                for i, (tx, code, n, h, _) in enumerate(records)]
    responses = run_requests(oracle, "sighash.json", requests)
    if responses is None:
        return 1
    failures = 0
    for (*_, digest), resp in zip(records, responses):
        if resp.get("ok", {}).get("digest_display") != digest:
            failures += 1
            print(f"FAIL sighash.json record {resp.get('id')}: {json.dumps(resp)[:200]}")
    print(f"sighash.json: {len(records)} records, {failures} failures")
    return failures


def check_tx_corpus(oracle: str) -> int:
    failures = 0
    for name in ("tx_valid.json", "tx_invalid.json"):
        records = json.loads((ROOT / "tests/transaction/corpus" / name).read_text())
        # Base mode: the byte after the version is not the zero marker of the extended format (issue #22).
        txs = [r[1] for r in records if len(r) == 3 and r[1][8:10] != "00"]
        requests = [{"id": i, "op": "tx.decode_base", "bytes_hex": tx} for i, tx in enumerate(txs)]
        responses = run_requests(oracle, name, requests)
        if responses is None:
            failures += 1
            continue
        bad = 0
        for tx, resp in zip(txs, responses):
            ok = resp.get("ok", {})
            txid = sha256d(bytes.fromhex(tx))
            if (ok.get("serialized_hex") != tx.lower() or ok.get("txid_hex") != txid.hex()
                    or ok.get("txid_display") != txid[::-1].hex()):
                bad += 1
                print(f"FAIL {name} base record {resp.get('id')}: {json.dumps(resp)[:200]}")
        print(f"{name}: {len(txs)} base-mode records, {bad} failures")
        failures += bad
    return failures


def witness_corpus_fields(raw: bytes) -> tuple[bytes, list[list[str]]]:
    """Separate base bytes and stacks in a known corpus record, by D4's field layout."""
    def count(pos):
        first = raw[pos]
        size = {253: 2, 254: 4, 255: 8}.get(first, 0)
        return ((int.from_bytes(raw[pos + 1:pos + 1 + size], "little"), pos + 1 + size)
                if size else (first, pos + 1))

    extended = raw[4] == 0
    if extended:
        assert raw[5] == 1, "corpus witness records must use flag 01"
    start = 6 if extended else 4
    inputs, pos = count(start)
    for _ in range(inputs):
        length, pos = count(pos + 36)
        pos += length + 4
    outputs, pos = count(pos)
    for _ in range(outputs):
        length, pos = count(pos + 8)
        pos += length
    end = pos
    stacks = []
    for _ in range(inputs):
        stack = []
        if extended:
            items, pos = count(pos)
            for _ in range(items):
                length, pos = count(pos)
                stack.append(raw[pos:pos + length].hex())
                pos += length
        stacks.append(stack)
    if pos + 4 != len(raw):
        raise ValueError("corpus record does not match D4's layout")
    return raw[:4] + raw[start:end] + raw[pos:], stacks


def check_witness_corpus(oracle: str) -> int:
    """Check both witness operations against corpus bytes and Python's hashlib."""
    failures = 0
    for name in ("tx_valid.json", "tx_invalid.json"):
        records = json.loads((ROOT / "tests/transaction/corpus" / name).read_text())
        txs = [bytes.fromhex(r[1]) for r in records if len(r) == 3]
        requests = [{"id": f"{i}-{op}", "op": op, "bytes_hex": tx.hex()}
                    for i, tx in enumerate(txs) for op in ("tx.read_witness", "tx.decode_witness")]
        responses = run_requests(oracle, name + " witness", requests)
        if responses is None:
            failures += 1
            continue
        bad = 0
        for req, resp in zip(requests, responses):
            raw = bytes.fromhex(req["bytes_hex"])
            base, stacks = witness_corpus_fields(raw)
            has_witness = any(stacks)
            encoded = raw if has_witness else base
            txid, wtxid = sha256d(base), sha256d(encoded)
            expected = {"serialized_hex": encoded.hex(), "witnesses": stacks, "has_witness": has_witness,
                        "txid_hex": txid.hex(), "txid_display": txid[::-1].hex(),
                        "wtxid_hex": wtxid.hex(), "wtxid_display": wtxid[::-1].hex()}
            if req["op"] == "tx.read_witness":
                expected.update(consumed=len(raw), rest_hex="")
            ok = resp.get("ok", {})
            if not all(matches(ok.get(k), v) for k, v in expected.items()):
                bad += 1
                print(f"FAIL {name} witness record {req['id']}: {json.dumps(resp)[:200]}")
        print(f"{name}: {len(txs)} records through both witness operations, {bad} failures")
        failures += bad
    return failures


def check_hash_block_fixtures(oracle: str) -> int:
    failures = 0
    for name, cases in (("header fixtures", header_fixtures()), ("Merkle fixtures", merkle_fixtures()),
                        ("hash fixtures", hash_fixtures()), ("SHA-1 fixtures", sha1_fixtures())):
        requests = [{**req, "id": i} for i, (req, _) in enumerate(cases)]
        responses = run_requests(oracle, name, requests)
        if responses is None:
            failures += 1
            continue
        bad = 0
        for i, (response, (_, expected)) in enumerate(zip(responses, cases)):
            if not matches(response, {"id": i, "ok": expected}):
                print(f"FAIL {name} {i}: {response!r}, expected {expected!r}")
                bad += 1
        print(f"{name}: {len(cases)} records, {bad} failures")
        failures += bad
    return failures


def check_script_adapter_limits(oracle: str) -> int:
    failures = 0
    cases = adapter_limit_cases()
    for i, (request, expected) in enumerate(cases):
        got = run_batch(oracle, [json.dumps({**request, "id": i})])
        if got != [{"id": i, **expected}]:
            print(f"FAIL Script adapter resource boundary {i}")
            failures += 1
    print(f"Script adapter resource limits: {len(cases)} cases, {failures} failures")
    return failures


def check_process(oracle: str) -> int:
    """Item 5: line-by-line answers from a process whose input stays open."""
    proc = subprocess.Popen([oracle], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)
    failures = 0

    def read_line() -> dict | None:
        result: list[str] = []
        reader = threading.Thread(target=lambda: result.append(proc.stdout.readline()), daemon=True)
        reader.start()
        reader.join(TIMEOUT)
        return json.loads(result[0]) if result and result[0] else None

    def expect(step: str, send: str, check) -> None:
        nonlocal failures
        proc.stdin.write(send)
        proc.stdin.flush()
        resp = read_line()
        if resp is None or not check(resp):
            failures += 1
            print(f"FAIL process, {step}: {resp}")

    expect("one request, input open", '{"id":1,"op":"oracle.version"}\n',
           lambda r: r == {"id": 1, "ok": {"format": "dogelib-oracle/6"}})
    expect("malformed line", '{"id":2,\n', lambda r: r["id"] is None and r["error"]["kind"] == "request")
    expect("blank lines, then a request", '\n  \n{"id":"three","op":"oracle.version"}\n',
           lambda r: r == {"id": "three", "ok": {"format": "dogelib-oracle/6"}})
    proc.stdin.write('{"id":null,"op":"oracle.version"}')
    proc.stdin.close()
    resp = read_line()
    if resp != {"id": None, "ok": {"format": "dogelib-oracle/6"}}:
        failures += 1
        print(f"FAIL process, final line without newline: {resp}")
    if proc.wait(TIMEOUT) != 0 or proc.stdout.read() != "":
        failures += 1
        print("FAIL process: exit status or output after the last response")
    version = subprocess.run([oracle, "--version"], capture_output=True, text=True, timeout=TIMEOUT)
    if version.returncode != 0 or json.loads(version.stdout) != {"format": "dogelib-oracle/6"}:
        failures += 1
        print(f"FAIL --version: {version.stdout!r}")
    print(f"process: {failures} failures")
    return failures


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    oracle = sys.argv[1]
    failures = (check_fixtures(oracle) + check_sighash_corpus(oracle) + check_tx_corpus(oracle)
                + check_witness_corpus(oracle) + check_hash_block_fixtures(oracle) + check_process(oracle) + check_script_adapter_limits(oracle))
    print("PASS" if failures == 0 else f"FAIL: {failures} failures")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
