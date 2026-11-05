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
    return [("Script corpus individual", individual), ("Script reader truncations", reader),
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
        if set(value) != {"result", "script_error", "stack_hex"} or value["script_error"] != "OK":
            return "invalid accepted result"
        stack = value["stack_hex"]
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
        extra = {"flags": "bits", "signature_opcode": "opcode"}.get(reason)
        if reason not in ("flags", "signature_opcode", "check_lock_time_verify", "check_sequence_verify"):
            return "invalid unsupported reason"
        if set(value) != {"result", "reason"} | ({extra} if extra else set()):
            return "invalid unsupported fields"
        if extra and (type(value[extra]) is not int or not 0 <= value[extra] <= (0xffffffff if extra == "bits" else 255)):
            return "invalid unsupported argument"
        if extra == "opcode" and value["opcode"] not in instruction_opcodes(request["bytes_hex"]):
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
    return cases
