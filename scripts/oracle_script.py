"""Deterministic Script requests for the oracle and pinned Core harness.

The corpus supplies exact scripts and flags, rather than expected EvalScript
results: its expectations describe VerifyScript with transaction checkers.
"""

import json
import pathlib
import random
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT_SEED = 20261105
ERROR_NAMES = re.findall(r'SCRIPT_ERROR\(SCRIPT_ERR_[A-Z0-9_]+, "([A-Z0-9_]+)"\)',
                        (ROOT / "harness/core/script_error_names.inc").read_text())


def corpus_records():
    return [json.loads(line) for line in (ROOT / "tests/script/corpus/script_tests.jsonl").read_text().splitlines()]


def evaluation(script, flags=0, stack=()):
    return {"op": "script.eval", "bytes_hex": script.hex(), "flags": flags, "stack_hex": list(stack)}


def push(data):
    n = len(data)
    return (bytes([n]) if n < 76 else b"\x4c" + bytes([n]) if n < 256 else
            b"\x4d" + n.to_bytes(2, "little")) + data


def script_sets():
    individual = [evaluation(bytes.fromhex(r[field]), r["effective_flags_mask"])
                  for r in corpus_records() for field in ("scriptSig_hex", "scriptPubKey_hex")]
    reader = []
    # Every opcode, each length-field truncation, and every payload truncation.
    scripts = [bytes([op]) for op in range(256)]
    scripts += [push(bytes(range(n))) for n in (0, 1, 75, 76, 255)]
    scripts += [b"\x4c\x01\x07", b"\x4d\x01\x00\x07", b"\x4e\x01\x00\x00\x00\x07",
                b"\x4e\xff\xff\xff\xff", b"\x4d\x00\x01" + bytes(256)]
    for script in scripts:
        for n in range(len(script) + 1):
            reader.append({"op": "script.read_op", "bytes_hex": script[:n].hex(), "cursor": 0})
    for script in (b"\x03\x4d\x01\x00\x61", b"\x4e\x01\x00\x00\x00\x07\x51"):
        reader.extend({"op": "script.read_op", "bytes_hex": script.hex(), "cursor": pc}
                      for pc in range(len(script) + 1))
    limits = []
    for n in (200, 201, 202):
        limits += [evaluation(b"\x61" * n), evaluation(b"\x00\x63" + b"\x61" * n + b"\x68")]
    for n in (519, 520, 521):
        limits += [evaluation(push(bytes(n))), evaluation(b"\x00\x63" + push(bytes(n)) + b"\x68")]
    for n in (999, 1000, 1001):
        for script in (b"", b"\x61", b"\x75", b"\x00", b"\x6b", b"\x00\x63\x61\x68"):
            limits.append(evaluation(script, stack=[""] * n))
        limits.append(evaluation(b"\x00" * n))
    for n in (9999, 10000, 10001):
        # Large pushes reach SCRIPT_SIZE or PUSH_SIZE without opcode-count masking.
        limits.append(evaluation(push(bytes(n - 3))))
    for n in (9999, 10000, 10001):
        bulk = push(bytes(520)) * 19
        script = bulk + push(bytes(n - len(bulk) - 1))
        assert len(script) == n
        limits.append(evaluation(script))
    # Explicit capability and error cases keep mutation tests independent of corpus order.
    limits += [evaluation(b"\xac", stack=["", ""]), evaluation(b"\xae"),
               evaluation(b"\x51\xb1", 512), evaluation(b"\x51\xb2", 1024),
               evaluation(b"\x51", 64), evaluation(b"\x51\x8b"), evaluation(b"\x00\xa6"),
               evaluation(b"\x6a"), evaluation(b"\x00"), evaluation(b"\x51\x63\x00\x63\x68\x68")]
    rng = random.Random(SCRIPT_SEED)
    fragments = [b"\x00", b"\x51", b"\x60", b"\x4f", push(b"\x80"), push(b"\x01\x00"),
                 b"\x61", b"\x69", b"\x6a", b"\x6b", b"\x6c", b"\x75", b"\x76", b"\x77",
                 b"\x78", b"\x79", b"\x7a", b"\x7b", b"\x7c", b"\x7d", b"\x82", b"\x87", b"\x88", b"\xab",
                 b"\x8b", b"\x93", b"\xa6", b"\xa8"]
    def block(depth):
        if depth and rng.randrange(3) == 0:
            return rng.choice([b"\x00", b"\x51"]) + rng.choice([b"\x63", b"\x64"]) + block(depth - 1) + b"\x67" + block(depth - 1) + b"\x68"
        return b"".join(rng.choice(fragments) for _ in range(rng.randrange(1, 8)))
    randoms = [evaluation(block(4), rng.choice([0, 1, 3, 31, 512, 1024, 1567]),
                          [rng.choice(["", "01", "80", "0100"]) for _ in range(rng.randrange(5))])
               for _ in range(2000)]
    return [("Script corpus individual base", [{**r, "checker": "base"} for r in individual]),
            (f"Script random base seed {SCRIPT_SEED}", [{**r, "checker": "base"} for r in randoms]),
            ("Script resource boundaries base", [{**r, "checker": "base"} for r in limits]),
            ("Script corpus individual", individual), ("Script reader truncations", reader),
            ("Script resource boundaries", limits), (f"Script random seed {SCRIPT_SEED}", randoms)]


def instruction_opcodes(script_hex):
    """Read opcode positions independently, without treating payload bytes as opcodes."""
    script = bytes.fromhex(script_hex)
    cursor, opcodes = 0, set()
    while cursor < len(script):
        opcode = script[cursor]
        opcodes.add(opcode)
        cursor += 1
        if opcode <= 78:
            width = {76: 1, 77: 2, 78: 4}.get(opcode, 0)
            if cursor + width > len(script):
                break
            size = int.from_bytes(script[cursor:cursor + width], "little") if width else opcode
            cursor += width + size
    return opcodes


def validate_eval(request, response, allow_unsupported):
    """Reject malformed evaluation results before any unsupported exemption."""
    if set(response) != {"id", "ok"} or not isinstance(response["ok"], dict):
        return "evaluation response must contain id and ok"
    value = response["ok"]
    result = value.get("result")
    if result == "accepted":
        if set(value) != ({"result", "script_error", "stack_hex"} if request["op"] == "script.eval" else {"result", "script_error"}) or value["script_error"] != "OK":
            return "invalid accepted result"
        stack = value.get("stack_hex", [])
        if not isinstance(stack, list) or any(not isinstance(x, str) or len(x) % 2 or
                any(c not in "0123456789abcdef" for c in x) for x in stack):
            return "invalid final stack"
    elif result == "rejected":
        if set(value) != {"result", "script_error"} or value["script_error"] not in ERROR_NAMES[1:]:
            return "invalid Script rejection"
    elif result == "unsupported" and allow_unsupported:
        reason = value.get("reason")
        if not isinstance(reason, str):
            return "invalid unsupported reason type"
        spend = request["op"] == "script.verify_legacy"
        checker = request.get("checker", "none")
        allowed = {"flags"}
        if spend and checker == "transaction":
            allowed.add("signature_verifier")
        elif not spend and checker == "none":
            allowed.update(("signature_opcode", "check_lock_time_verify", "check_sequence_verify"))
        extra = {"flags": "bits", "signature_opcode": "opcode", "signature_verifier": "opcode"}.get(reason)
        if reason not in allowed:
            return "invalid unsupported reason"
        if set(value) != {"result", "reason"} | ({extra} if extra else set()):
            return "invalid unsupported fields"
        if extra and (type(value[extra]) is not int or not 0 <= value[extra] <= (0xffffffff if extra == "bits" else 255)):
            return "invalid unsupported argument"
        if extra == "opcode" and value["opcode"] not in (172, 173, 174, 175):
            return "invalid signature opcode"
        if reason == "signature_opcode" and value["opcode"] not in instruction_opcodes(request["bytes_hex"]):
            return "unsupported opcode is absent from the script instructions"
        if reason == "flags" and value["bits"] != request["flags"] & (0xffffffff ^ 1567):
            return "invalid unsupported flag bits"
        if reason == "flags" and value["bits"] == 0:
            return "empty unsupported flag bits"
    else:
        return "invalid evaluation result class"
    return None


def adapter_limit_cases():
    """Boundary requests with expectations from the adapter contract."""
    limit = {"kind": "adapter", "reason": "resource_limit"}
    cases = []
    for n in (4096, 4097):
        req = evaluation(b"", stack=[""] * n)
        cases.append((req, {"ok": {"result": "accepted", "script_error": "OK", "stack_hex": req["stack_hex"]}}
                      if n == 4096 else {"error": limit}))
    for stack in (["00" * 1048576], ["00" * 1048577], ["00" * 1048576] * 4,
                  ["00" * 1048576] * 4 + ["00"]):
        req = evaluation(b"", stack=stack)
        within = len(stack[0]) <= 2097152 and sum(map(len, stack)) <= 8388608
        cases.append((req, {"ok": {"result": "accepted", "script_error": "OK", "stack_hex": stack}}
                      if within else {"error": limit}))
    for n in (1048576, 1048577):
        cases.append((evaluation(bytes(n)), {"ok": {"result": "rejected", "script_error": "SCRIPT_SIZE"}}
                      if n == 1048576 else {"error": limit}))
        cases.append(({"op": "script.read_op", "bytes_hex": "00" * n, "cursor": n},
                      {"ok": {"result": "at_end", "cursor": n}} if n == 1048576 else {"error": limit}))
    for checker in ("base", "transaction"):
        for n in (1048576, 1048577):
            for field in ("scriptSig", "scriptPubKey"):
                req = {"op": "script.verify_legacy", "tx_hex": spend_tx(bytes(n) if field == "scriptSig" else b""),
                       "input_index": 0, "prevout_script_hex": bytes(n).hex() if field == "scriptPubKey" else "51",
                       "flags": 0, "checker": checker}
                cases.append((req, {"ok": {"result": "rejected", "script_error": "SCRIPT_SIZE"}}
                              if n == 1048576 else {"error": limit}))
    return cases


SPEND_SEED = 20261106


def legacy_request(record, checker):
    """Use the exact spending transaction and previous-output script of a corpus record."""
    return {"op": "script.verify_legacy", "tx_hex": record["context"]["spending_tx_base_hex"],
            "input_index": record["context"]["input_index"], "prevout_script_hex": record["scriptPubKey_hex"],
            "flags": record["effective_flags_mask"], "checker": checker}


def spend_tx(script_sig, version=1, sequence=0xffffffff, lock_time=0):
    """Serialize a synthetic one-input base transaction, with a fresh script length."""
    n = len(script_sig)
    count = bytes([n]) if n < 253 else b"\xfd" + n.to_bytes(2, "little") if n < 65536 else b"\xfe" + n.to_bytes(4, "little")
    return (version.to_bytes(4, "little") + b"\x01" + bytes(32) + bytes(4) + count + script_sig +
            sequence.to_bytes(4, "little") + b"\x01" + bytes(8) + b"\x00" + lock_time.to_bytes(4, "little")).hex()


def legacy_sets():
    """Whole-spend corpus and seeded mutations, separately for each checker."""
    records = [r for r in corpus_records() if r["classification"]["milestone"] == "inside"]
    rng = random.Random(SPEND_SEED)
    mutations = []
    for _ in range(2000):
        record = rng.choice(records)
        sig, spk = bytes.fromhex(record["scriptSig_hex"]), bytes.fromhex(record["scriptPubKey_hex"])
        target = rng.randrange(6)
        version, sequence, lock_time = 1, 0xffffffff, 0
        if target in (0, 1):
            data = bytearray(sig if target == 0 else spk)
            if data and rng.randrange(2):
                data[rng.randrange(len(data))] ^= 1 << rng.randrange(8)
            else:
                data.extend(rng.choice([b"\xac", b"\xae", b"\x51\xb1", b"\x51\xb2", b"\x00", b"\x6a"]))
            if target == 0:
                sig = bytes(data)
            else:
                spk = bytes(data)
        elif target == 2:
            version = rng.choice([0, 1, 2, 0x80000000, 0xffffffff])
        elif target == 3:
            sequence = rng.choice([0, 1, 0xffff, 0x400000, 0x80000000, 0xffffffff])
        elif target == 4:
            lock_time = rng.choice([0, 1, 499999999, 500000000, 0xffffffff])
        flags = rng.choice([0, 1, 3, 31, 512, 1024, 1567, 64]) if target == 5 else record["effective_flags_mask"]
        mutations.append({"op": "script.verify_legacy", "tx_hex": spend_tx(sig, version, sequence, lock_time),
                          "input_index": 0, "prevout_script_hex": spk.hex(), "flags": flags})
    return [(f"Script legacy corpus {checker}", [legacy_request(r, checker) for r in records])
            for checker in ("base", "transaction")] + [
        (f"Script legacy mutations {checker} seed {SPEND_SEED}", [{**r, "checker": checker} for r in mutations])
        for checker in ("base", "transaction")]



def tx_spend_records():
    """Transaction inputs with runner-derived expectations, including unknown outcomes."""
    return [json.loads(line) for line in (ROOT / "tests/script/corpus/tx_spends.jsonl").read_text().splitlines()]


def tx_spend_sets():
    """Keep accept requirements separate from inputs with unknown expectations."""
    records = [r for r in tx_spend_records() if r["classification"]["milestone"] == "inside"]
    assert len(records) == 159
    return [(f"Script tx spends {expectation} {checker}", [
        {"op": "script.verify_legacy", "tx_hex": r["tx_hex"], "input_index": r["input_index"],
         "prevout_script_hex": r["prevout_scriptPubKey_hex"], "flags": r["flags_mask"], "checker": checker}
        for r in records if (r["per_input_expectation"] == "accept") == (expectation == "accept")])
        for checker in ("base", "transaction") for expectation in ("accept", "unknown")]


LOCK_SEED = 20261107


def locktime_sets():
    """Each request reaches its named opcode after one operand push (D3, lines 350–427)."""
    rng = random.Random(LOCK_SEED)
    sets = []
    for opcode, flag, label, operands, values in (
        (177, 512, "CLTV", [-1, 0, 1, 499999998, 499999999, 500000000, 500000001, 0xffffffff, 0x100000000],
         [0, 1, 499999999, 500000000, 500000001, 0xffffffff]),
        (178, 1024, "CSV", [-1, 0, 1, 65535, 65536, 0x400000, 0x400001, 0x40ffff, 0x80000000, 0x80400001, 0xffffffff],
         [0, 1, 65535, 65536, 0x400000, 0x400001, 0x40ffff, 0x80000000, 0x80400001, 0xffffffff])):
        # Cartesian boundaries guarantee equal operands, type mismatches and final sequences.
        cases = [(v, t, q, n) for v in (1, 2, 0x80000000, 0xffffffff) for t in values
                 for q in ((0, 0xffffffff) if opcode == 177 else (t,)) for n in operands]
        cases += [(rng.getrandbits(32), rng.getrandbits(32), rng.getrandbits(32),
                   rng.choice(operands) if rng.randrange(2) else rng.getrandbits(33)) for _ in range(500)]
        requests = []
        for version, value, sequence, operand in cases:
            magnitude = abs(operand)
            data = magnitude.to_bytes((magnitude.bit_length() + 7) // 8, "little")
            if data and data[-1] & 128:
                data += b"\x00"
            if operand < 0:
                data = data[:-1] + bytes([data[-1] | 128])
            # DROP TRUE avoids an unrelated false-top rejection when the operand is zero.
            script = push(data) + bytes([opcode, 117, 81])
            requests.append({"op": "script.verify_legacy", "tx_hex": spend_tx(b"", version, sequence, value if opcode == 177 else 0),
                             "input_index": 0, "prevout_script_hex": script.hex(), "flags": flag, "checker": "transaction"})
        sets.append((f"Script targeted {label} transaction seed {LOCK_SEED}", requests))
    return sets


def base_spend_domain(tx_hex, index):
    """Check complete base decoding and bounds before the harness flag guard (D4)."""
    if not isinstance(tx_hex, str) or not re.fullmatch(r"(?:[0-9a-fA-F]{2})*", tx_hex):
        return False
    data, pos = bytes.fromhex(tx_hex), 0

    def take(n):
        nonlocal pos
        if pos + n > len(data):
            raise ValueError("truncated")
        result = data[pos:pos + n]
        pos += n
        return result

    def size():
        tag = take(1)[0]
        if tag < 253:
            return tag
        n = int.from_bytes(take({253: 2, 254: 4, 255: 8}[tag]), "little")
        if n < {253: 253, 254: 65536, 255: 4294967296}[tag] or n > 0x02000000:
            raise ValueError("CompactSize")
        return n

    try:
        take(4)
        inputs = size()
        script_sizes = []
        for _ in range(inputs):
            take(36)
            n = size()
            script_sizes.append(n)
            take(n)
            take(4)
        outputs = size()
        for _ in range(outputs):
            take(8)
            take(size())
        take(4)
        return (pos == len(data) and 0 <= index < inputs < 2**32 and outputs < 2**32
                and script_sizes[index] <= 1048576)
    except (ValueError, TypeError):
        return False


def harness_refused(request):
    """Core's VerifyScript asserts these flag dependencies, before it can return a verdict."""
    required = {"op", "tx_hex", "input_index", "prevout_script_hex", "flags", "checker"}
    if (set(request) - {"id"} != required or request.get("op") != "script.verify_legacy" or
            type(request["input_index"]) is not int):
        return False
    flags = request["flags"]
    unsafe = bool((flags & 2048 and not flags & 1) or
                  (flags & 256 and (not flags & 1 or not flags & 2048)))
    if not unsafe:
        return False
    script = request.get("prevout_script_hex")
    return (request.get("checker") in ("base", "transaction") and
            isinstance(script, str) and len(script) <= 2097152 and
            re.fullmatch(r"(?:[0-9a-fA-F]{2})*", script) is not None and
            base_spend_domain(request.get("tx_hex"), request.get("input_index")))


def refused_set():
    """Well-formed spends whose flags violate Core's assertion domain."""
    return [{"op": "script.verify_legacy", "tx_hex": spend_tx(b""), "input_index": 0,
             "prevout_script_hex": "51", "checker": checker, "flags": flags}
            for checker in ("base", "transaction") for flags in (256, 2048, 2304, 257)]


def refusal_precedence_set():
    """Earlier decoding and index errors retain their ordinary comparison path."""
    valid = refused_set()[0]
    return [{**valid, **change} for change in (
        {"tx_hex": ""}, {"tx_hex": "0100000001"},
        {"tx_hex": valid["tx_hex"] + "00"}, {"input_index": 1},
        {"tx_hex": "01000000000000000000"},
        {"tx_hex": valid["tx_hex"][:8] + "fd0100" + valid["tx_hex"][10:]},
        {"tx_hex": valid["tx_hex"][:8] + "fe01000002" + valid["tx_hex"][10:]})]
