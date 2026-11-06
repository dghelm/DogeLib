"""Self-test of scripts/compare_core.py. It needs the oracle, not Dogecoin Core.

Usage: python3 -I scripts/test_compare_core.py <dogelib-oracle>

A wrapper around the oracle stands in for the Core harness. With no change it
answers the harness's projection of each response, and the comparison must
pass on the full request stream. Each mutation then changes one response or
the wrapper's behaviour, and the comparison must fail with the failure code
that the mutation targets.

The script also runs as that wrapper:
    test_compare_core.py --wrap <mode> <role> <dogelib-oracle> [--version]
"""

import json
import os
import pathlib
import subprocess
import sys
import tempfile
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent
COMPARE = ROOT / "scripts" / "compare_core.py"
sys.path.insert(0, str(ROOT / "scripts"))
from oracle_script import harness_refused, refused_set, refusal_precedence_set, tx_spend_sets, locktime_sets, spend_tx

# mode: (role of the wrapper, expected failure code). The role "core" stands
# in for the harness, "oracle" for dogelib-oracle.
MUTATIONS = {
    "pow_reconstruction": ("core", "AUXPOW_RECONSTRUCTION"),
    "pow_mined_reconstruction": ("core", "AUXPOW_POW_RECONSTRUCTION"),
    "pow_scrypt": ("core", "SCRYPT_DIGEST"),
    "pow_reader": ("core", "FULL_HEADER"),
    "pow_auxpow": ("core", "AUXPOW_VERDICT"),
    "pow_verdict": ("core", "HEADER_POW"),
    "pow_split": ("core", "HEADER_POW"),
    "pow_version": ("core", "HEADER_VERSION"),
    "pubkey_valid": ("core", "PUBKEY_VALID"),
    "signature_verdict": ("core", "SIGNATURE_VERDICT"),
    "targeted_early_error": ("both", "TARGETED_OPCODE"),
    "tx_valid_core_rejection": ("core", "TX_VALID_CORE"),
    "refused_core_verdict": ("core", "HARNESS_REFUSAL"),
    "refused_oracle_verdict": ("oracle", "ORACLE_REFUSAL"),
    "legacy_class": ("core", "MISMATCH"),
    "legacy_rejection": ("core", "MISMATCH"),
    "legacy_stack": ("core", "SCRIPT_RESULT"),
    "legacy_core_unsupported": ("core", "SCRIPT_RESULT"),
    "legacy_base_verifier": ("oracle", "SCRIPT_RESULT"),
    "legacy_locktime_unsupported": ("oracle", "SCRIPT_RESULT"),
    **{name: ("core", "MISMATCH") for name in (
        "script_cursor", "script_opcode", "script_bytes", "script_pushed", "script_part", "script_read_class",
        "script_eval_class", "script_stack", "script_rejection")},
    **{name: ("oracle", "SCRIPT_RESULT") for name in (
        "script_unsupported_reason", "script_unsupported_bits", "script_unsupported_opcode", "script_unsupported_extra", "script_unsupported_absent")},
    "script_core_unsupported": ("core", "SCRIPT_RESULT"),
    "script_success_error": ("core", "SCRIPT_RESULT"),
    "composition_stack": ("core", "MISMATCH"),
    **{name: ("core", "MISMATCH") for name in (
        "hash_ripemd160", "hash_hash160", "hash_sha1", "header_version", "header_time", "header_bits",
        "header_nonce", "header_prev_block_hex", "header_prev_block_display", "header_merkle_root_hex",
        "header_merkle_root_display", "header_bytes", "header_hash_hex", "header_hash_display",
        "header_consumed", "header_rest", "header_truncated", "merkle_root_hex", "merkle_root_display", "merkle_mutated")},
    **{name: ("core", "MISMATCH") for name in
       ("work_value", "work_negative", "work_overflow", "work_compact", "work_calculate_bits", "work_next_bits")},
    "wtxid": ("core", "MISMATCH"),
    "witnesses": ("core", "MISMATCH"),
    "has_witness": ("core", "MISMATCH"),
    "digest_display": ("core", "MISMATCH"),
    "digest_hex": ("core", "PREIMAGE"),
    "plan": ("core", "MISMATCH"),
    "reason": ("core", "MISMATCH"),
    "ok_to_error": ("core", "MISMATCH"),
    "consumed": ("core", "MISMATCH"),
    "consumed_bool": ("core", "MISMATCH"),
    "rest_hex": ("core", "MISMATCH"),
    "error_to_ok": ("core", "MISMATCH"),
    "request_error": ("core", "REQUEST_ERROR"),
    "core_preimage": ("core", "PROJECTION"),
    "drop": ("core", "COUNT"),
    "extra": ("core", "COUNT"),
    "id": ("core", "ID"),
    "malformed": ("core", "MALFORMED"),
    "exit": ("core", "EXIT"),
    "hang": ("core", "TIMEOUT"),
    "version": ("core", "VERSION"),
    "oracle_no_preimage": ("oracle", "PREIMAGE"),
    "oracle_fixed_preimage": ("oracle", "PREIMAGE"),
    "oracle_preimage_bytes": ("oracle", "PREIMAGE"),
    "oracle_preimage_malformed": ("oracle", "PREIMAGE"),
}


def mutate_first(responses: list[dict], test, change) -> None:
    for resp in responses:
        if test(resp):
            change(resp)
            return
    raise SystemExit("wrapper: no response to mutate")


def replace_ok(resp: dict, error: dict) -> None:
    del resp["ok"]
    resp["error"] = error


def is_plan(plan):
    return lambda r: r.get("ok", {}).get("plan") == plan


def wrap(mode: str, role: str, oracle: str, args: list[str]) -> int:
    if mode == "exit":
        sys.stdin.read()
        return 5
    if mode == "hang":
        pidfile = os.environ["COMPARE_SELFTEST_PIDFILE"]
        child = subprocess.Popen(["sleep", "1000"])
        pathlib.Path(pidfile).write_text(str(child.pid))
        time.sleep(1000)
        return 0
    oracle_format = json.loads(subprocess.run([oracle, "--version"], capture_output=True,
                                              text=True, check=True).stdout)["format"]
    projected_format = oracle_format + {"core": "-core-projection", "rust": "-rust-compactsize", "oracle": ""}[role]
    if mode == "version" and role in ("core", "rust"):
        projected_format = oracle_format
    if role == "rust":
        if args[:2] != ["--oracle-format", oracle_format]:
            return 2
        args = args[2:]
    if args == ["--auxpow-pow-fixtures"]:
        from oracle_header_pow import mined_fixture
        document = {k: v for k, v in mined_fixture().items() if k not in ("generator", "capture_date")}
        if mode == "pow_mined_reconstruction":
            document["cases"][0]["bytes_hex"] = "00" * 80
        print(json.dumps(document))
        return 0
    if args == ["--check-auxpow-fixtures"]:
        from oracle_header_pow import payload_cases
        rows = [{**{k: c[k] for k in ("line", "payload_hex", "hash_aux_block_hex", "chain_id", "strict_chain_id", "expected")},
                 "valid": c["expected"]} for c in payload_cases()[:26]]
        if mode == "pow_reconstruction":
            rows[0]["payload_hex"] = "00"
        print(json.dumps(rows))
        return 0
    if args == ["--version"]:
        print(json.dumps({"format": projected_format}, separators=(",", ":")))
        return 0
    data = sys.stdin.read()
    out = subprocess.run([oracle], input=data, capture_output=True, text=True, check=True).stdout
    responses = [json.loads(line) for line in out.splitlines()]
    requests = [json.loads(line) for line in data.splitlines()]
    for request, resp in zip(requests, responses):
        ok = resp.get("ok", {})
        if "format" in ok:
            ok["format"] = projected_format
        if role == "core" and mode != "core_preimage":
            ok.pop("preimage_hex", None)
            ok.pop("diagnostic", None)
        if role == "core" and harness_refused(request):
            resp.pop("ok", None)
            resp["error"] = {"kind": "request", "message": "Core VerifyScript flag dependencies are not satisfied"}
            continue
        if role == "core" and ok.get("result") == "unsupported":
            # An informational Core outcome can differ from an unsupported oracle.
            resp["ok"] = {"result": "accepted", "script_error": "OK"}
            if request["op"] == "script.eval":
                resp["ok"]["stack_hex"] = []

    # Data mutations preserve the version handshake so they reach the comparison.
    if responses and all("format" in r.get("ok", {}) for r in responses):
        print("\n".join(json.dumps(r, separators=(",", ":")) for r in responses))
        return 0

    def set_ok(field, value):
        return lambda r: r["ok"].__setitem__(field, value)

    if mode == "targeted_early_error":
        target = locktime_sets()[0][1][0]
        ids = {r["id"] for r in requests if {k: v for k, v in r.items() if k != "id"} == target}
        # Auxiliary adapter-limit and composition calls contain no targeted request.
        if ids:
            mutate_first(responses, lambda r: r["id"] in ids,
                         lambda r: r.update(ok={"result": "rejected", "script_error": "BAD_OPCODE"}))
    elif mode == "pubkey_valid":
        mutate_first(responses, lambda r: "valid" in r.get("ok", {}),
                     lambda r: r["ok"].__setitem__("valid", not r["ok"]["valid"]))
    elif mode == "signature_verdict":
        from oracle_pubkey import signature_spends
        ids = {r["id"] for r in requests if {k: v for k, v in r.items() if k != "id"} in signature_spends()}
        mutate_first(responses, lambda r: r["id"] in ids,
                     lambda r: r.update(ok={"result": "rejected", "script_error": "EVAL_FALSE"}))
    elif mode == "tx_valid_core_rejection":
        eligible = tx_spend_sets()[2][1]
        ids = {r["id"] for r in requests if any({k: v for k, v in r.items() if k != "id"} == q for q in eligible)}
        mutate_first(responses, lambda r: r["id"] in ids,
                     lambda r: r.update(ok={"result": "rejected", "script_error": "EVAL_FALSE"}))
    elif mode.startswith("refused_"):
        ids = {max((r["id"] for r in requests if harness_refused(r)), key=lambda value: int(value[1:]))}
        def alter_refused(r):
            r.pop("error", None)
            r["ok"] = {"result": "accepted", "script_error": "OK"}
        mutate_first(responses, lambda r: r["id"] in ids, alter_refused)
    elif mode.startswith("legacy_"):
        by_id = {r["id"]: r for r in requests}
        def eligible(r):
            req = by_id[r["id"]]
            if req["op"] != "script.verify_legacy":
                return False
            value = r.get("ok", {})
            if mode == "legacy_base_verifier":
                return req["checker"] == "base" and "ok" in r
            return value.get("result") == ("rejected" if mode == "legacy_rejection" else "accepted")
        def alter(r):
            if mode == "legacy_class":
                r["ok"] = {"result": "rejected", "script_error": "OP_RETURN"}
            elif mode == "legacy_rejection":
                r["ok"]["script_error"] = "VERIFY" if r["ok"]["script_error"] != "VERIFY" else "OP_RETURN"
            elif mode == "legacy_stack":
                r["ok"]["stack_hex"] = []
            elif mode == "legacy_locktime_unsupported":
                r["ok"] = {"result": "unsupported", "reason": "check_lock_time_verify"}
            elif mode in ("legacy_base_verifier", "legacy_core_unsupported"):
                r["ok"] = {"result": "unsupported", "reason": "removed_verifier_reason", "opcode": 172}
            else:
                r["ok"]["extra"] = 1
        mutate_first(responses, eligible, alter)
    elif mode == "composition_stack":
        requests = [json.loads(line) for line in data.splitlines()]
        ids = {r["id"] for r in requests if str(r["id"]).startswith("composition-") and r.get("stack_hex")}
        if any(r["id"] in ids and r.get("ok", {}).get("result") == "accepted" for r in responses):
            mutate_first(responses, lambda r: r["id"] in ids and r.get("ok", {}).get("result") == "accepted",
                         lambda r: r["ok"]["stack_hex"].append("ff"))
    elif mode.startswith("script_"):
        requests = [json.loads(line) for line in data.splitlines()]
        by_id = {r["id"]: r for r in requests}
        field = {"script_cursor": "cursor", "script_opcode": "opcode", "script_bytes": "bytes_hex",
                 "script_pushed": "pushed_hex", "script_part": "part", "script_read_class": "result"}.get(mode)
        def eligible(r):
            value = r.get("ok", {})
            if field:
                return by_id[r["id"]]["op"] == "script.read_op" and field in value
            if mode.startswith("script_unsupported"):
                extra = "bits" if mode.endswith("bits") else "opcode" if mode.endswith(("opcode", "absent")) else "reason"
                return value.get("result") == "unsupported" and extra in value
            target = "rejected" if mode == "script_rejection" else "accepted"
            return by_id[r["id"]]["op"] == "script.eval" and value.get("result") == target
        def alter(r):
            value = r["ok"]
            if field:
                old = value[field]
                value[field] = old + 1 if type(old) is int else old + "00" if field.endswith("hex") else "changed"
            elif mode == "script_eval_class":
                r["ok"] = {"result": "rejected", "script_error": "OP_RETURN"}
            elif mode == "script_stack":
                value["stack_hex"].append("ff")
            elif mode == "script_rejection":
                value["script_error"] = "VERIFY" if value["script_error"] != "VERIFY" else "OP_RETURN"
            elif mode == "script_success_error":
                value["script_error"] = "OP_RETURN"
            elif mode == "script_core_unsupported":
                r["ok"] = {"result": "unsupported", "reason": "signature_opcode", "opcode": 172}
            else:
                if mode == "script_unsupported_absent":
                    # An absent opcode cannot identify an executed capability.
                    value["opcode"] = next(op for op in range(256) if f"{op:02x}" not in by_id[r["id"]]["bytes_hex"])
                    return
                key = mode.removeprefix("script_unsupported_")
                value[key] = "changed" if key == "reason" else True if key == "opcode" else 0
        mutate_first(responses, eligible, alter)
    elif mode.startswith(("hash_", "header_", "merkle_")):
        requests = [json.loads(line) for line in data.splitlines()]
        if mode.startswith("hash_"):
            op, field = "hash." + mode[5:], "digest_hex"
        elif mode.startswith("merkle_"):
            op, field = "merkle.compute", mode[7:]
        elif mode == "header_bytes":
            op, field = "header.encode", "bytes_hex"
        elif mode.startswith("header_hash_"):
            op, field = "header.hash", mode[7:]
        else:
            op, field = "header.read", mode[7:]
        field = {"rest": "rest_hex", "truncated": "reason"}.get(field, field)
        ids = {r["id"] for r in requests if r["op"] == op}
        def eligible(r):
            if r["id"] not in ids:
                return False
            if field == "reason":
                return r.get("error", {}).get("reason") == "truncated"
            ok = r.get("ok", {})
            return "header" in ok or field in ok
        def alter(r):
            obj = r.get("error") if field == "reason" else r["ok"].get("header", r["ok"])
            if field not in obj:
                obj = r["ok"]
            value = obj[field]
            obj[field] = (not value if type(value) is bool else value ^ 1 if type(value) is int else
                          "too_large" if field == "reason" else ("01" if value[:2] != "01" else "00") + value[2:])
        mutate_first(responses, eligible, alter)
    elif mode in ("work_value", "work_negative", "work_overflow", "work_compact"):
        field = {"work_value": "value_hex", "work_negative": "negative",
                 "work_overflow": "overflow", "work_compact": "compact"}[mode]
        def alter(r):
            value = r["ok"][field]
            r["ok"][field] = (not value if type(value) is bool else
                              value ^ 1 if type(value) is int else "f" * 64)
        mutate_first(responses, lambda r: field in r.get("ok", {}), alter)
    elif mode in ("work_calculate_bits", "work_next_bits"):
        requests = [json.loads(line) for line in data.splitlines()]
        op = "work.calculate_next" if mode == "work_calculate_bits" else "work.next"
        ids = {r["id"] for r in requests if r["op"] == op}
        mutate_first(responses, lambda r: r["id"] in ids and "bits" in r.get("ok", {}),
                     lambda r: r["ok"].__setitem__("bits", r["ok"]["bits"] ^ 1))
    elif mode == "wtxid":
        mutate_first(responses, lambda r: "wtxid_hex" in r.get("ok", {}), set_ok("wtxid_hex", "00" * 32))
    elif mode == "witnesses":
        mutate_first(responses, lambda r: r.get("ok", {}).get("has_witness") is True,
                     lambda r: r["ok"]["witnesses"][0].append("ff"))
    elif mode == "has_witness":
        mutate_first(responses, lambda r: "has_witness" in r.get("ok", {}),
                     lambda r: r["ok"].__setitem__("has_witness", not r["ok"]["has_witness"]))
    elif mode == "digest_display":
        mutate_first(responses, is_plan("hash_bytes"), set_ok("digest_display", "00" * 32))
    elif mode == "digest_hex":
        mutate_first(responses, is_plan("hash_bytes"), set_ok("digest_hex", "00" * 32))
    elif mode == "plan":
        mutate_first(responses, is_plan("fixed_digest"), set_ok("plan", "hash_bytes"))
    elif mode == "reason":
        mutate_first(responses, lambda r: r.get("error", {}).get("reason") == "truncated",
                     lambda r: r["error"].__setitem__("reason", "too_large"))
    elif mode == "ok_to_error":
        mutate_first(responses, lambda r: "consumed" in r.get("ok", {}),
                     lambda r: replace_ok(r, {"kind": "read", "reason": "truncated"}))
    elif mode == "consumed":
        mutate_first(responses, lambda r: "consumed" in r.get("ok", {}),
                     lambda r: r["ok"].__setitem__("consumed", r["ok"]["consumed"] + 1))
    elif mode == "consumed_bool":
        # Python's == treats True as 1; the comparison must not.
        mutate_first(responses, lambda r: r.get("ok", {}).get("consumed") == 1, set_ok("consumed", True))
    elif mode == "rest_hex":
        mutate_first(responses, lambda r: r.get("ok", {}).get("rest_hex"),
                     lambda r: r["ok"].__setitem__("rest_hex", r["ok"]["rest_hex"][:-2]))
    elif mode == "error_to_ok":
        mutate_first(responses, lambda r: r.get("error", {}).get("kind") == "read",
                     lambda r: (r.pop("error"), r.__setitem__("ok", {"value": "0", "consumed": 1, "rest_hex": ""})))
    elif mode == "request_error":
        mutate_first(responses, lambda r: "ok" in r and "format" not in r["ok"],
                     lambda r: replace_ok(r, {"kind": "request", "message": "test"}))
    elif mode == "core_preimage":
        pass
    elif mode == "drop":
        responses.pop(len(responses) // 2)
    elif mode == "extra":
        responses.append(dict(responses[-1]))
    elif mode == "id":
        responses[len(responses) // 2]["id"] = "wrong"
    elif mode == "oracle_no_preimage":
        mutate_first(responses, is_plan("hash_bytes"), lambda r: r["ok"].pop("preimage_hex"))
    elif mode == "oracle_fixed_preimage":
        mutate_first(responses, is_plan("fixed_digest"), set_ok("preimage_hex", "00"))
    elif mode == "oracle_preimage_bytes":
        def flip_last(r):
            p = r["ok"]["preimage_hex"]
            r["ok"]["preimage_hex"] = p[:-2] + ("00" if p[-2:] != "00" else "01")
        mutate_first(responses, is_plan("hash_bytes"), flip_last)
    elif mode == "oracle_preimage_malformed":
        mutate_first(responses, is_plan("hash_bytes"), set_ok("preimage_hex", "zz"))
    if mode.startswith("pow_") and mode not in ("pow_reconstruction", "pow_mined_reconstruction"):
        op, field = {"pow_scrypt": ("scrypt.hash", "digest_hex"),
                     "pow_reader": ("block.header.read", "consumed"),
                     "pow_auxpow": ("auxpow.check", "valid"),
                     "pow_verdict": ("block.check_pow", "valid"),
                     "pow_split": ("block.check_pow", "valid"),
                     "pow_version": ("block.check_version", "valid")}[mode]
        for request, response in zip(requests, responses):
            if request["op"] == op and "ok" in response and (mode != "pow_split" or "payload_hex" in request):
                value = response["ok"][field]
                response["ok"][field] = (not value) if type(value) is bool else (value + 1 if type(value) is int else "00" * 32)
                break
        else:
            raise SystemExit("wrapper: no header PoW response to mutate")
    lines = [json.dumps(r, separators=(",", ":")) for r in responses]
    if mode == "malformed":
        lines[len(lines) // 2] = "{"
    print("\n".join(lines))
    return 0


def wrapper(tmp: pathlib.Path, mode: str, role: str, oracle: str) -> str:
    path = tmp / f"{role}-{mode}"
    path.write_text(f'#!/bin/sh\nexec "{sys.executable}" -I "{__file__}" --wrap {mode} {role} "{oracle}" "$@"\n')
    path.chmod(0o755)
    return str(path)


def compare(oracle: str, harness: str, extra: list[str], env=None, driver=COMPARE) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-I", str(driver), *extra, oracle, harness],
                          capture_output=True, text=True, env=env, timeout=900)


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "--compare-sanity-gap":
        # Move one required acceptance into the actual refusal path, without a verdict error.
        import compare_core
        original_sets = compare_core.request_sets

        def fewer_checks():
            sets, excluded = original_sets()
            for name, requests in sets:
                if name == "Script tx spends accept transaction":
                    requests[0] = {**requests[0], "flags": 256}
            return sets, excluded

        compare_core.request_sets = fewer_checks
        del sys.argv[1]
        return compare_core.main()
    if len(sys.argv) >= 5 and sys.argv[1] == "--wrap":
        return wrap(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:])
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    oracle = str(pathlib.Path(sys.argv[1]).resolve())
    failures = 0
    from compare_core import compare as compare_response
    request = {"op": "auxpow.check"}
    assert compare_response(request, {"id": 1, "ok": {"valid": True, "diagnostic": "Lean only"}},
                            {"id": 1, "ok": {"valid": True}}) is None
    assert compare_response(request, {"id": 1, "ok": {"valid": True, "diagnostic": None}},
                            {"id": 1, "ok": {"valid": 1}})[0] == "AUXPOW_VERDICT"
    assert compare_response({"op": "block.header.read"},
                            {"id": 1, "ok": {"consumed": 80, "diagnostic": "stray"}},
                            {"id": 1, "ok": {"consumed": 80}})[0] == "FULL_HEADER"
    assert all(harness_refused(r) for r in refused_set())
    assert not any(harness_refused(r) for r in refusal_precedence_set())
    # Empty-input base transactions and script bounds precede the flag refusal.
    valid = refused_set()[0]
    assert not harness_refused({**valid, "tx_hex": valid["tx_hex"] + "00"})
    assert not harness_refused({**valid, "tx_hex": "01000000000000000000"})
    assert not harness_refused({**valid, "prevout_script_hex": "00" * 1048577})
    assert harness_refused({**valid, "tx_hex": spend_tx(bytes(1048576))})
    assert not harness_refused({**valid, "tx_hex": spend_tx(bytes(1048577))})
    assert not harness_refused({**valid, "extra": 1})
    assert not harness_refused({**valid, "input_index": False})
    assert not harness_refused({**valid, "input_index": 0.0})
    assert not harness_refused({k: v for k, v in valid.items() if k != "checker"})
    assert harness_refused({**valid, "id": "optional-id"})
    # Each stream names its target and constructs one push before that opcode.
    for name, requests in locktime_sets():
        op = 177 if "CLTV" in name else 178
        assert requests
        for r in requests:
            script = bytes.fromhex(r["prevout_script_hex"])
            assert script[0] <= 5 and script[1 + script[0]:] == bytes([op, 117, 81])
            assert r["checker"] == "transaction" and not harness_refused(r)
    print("ok   refusal precedence and reached timelock constructions")
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = pathlib.Path(tmpdir)

        # Positive control on the full stream, whose input and output exceed a pipe's capacity.
        result = compare(oracle, wrapper(tmp, "none", "core", oracle), [])
        total = [line for line in result.stdout.splitlines() if line.startswith("total:")]
        if result.returncode != 0 or not total or not total[0].endswith(" 0 failures"):
            failures += 1
            print(f"FAIL positive control: exit {result.returncode}\n{result.stdout[-2000:]}{result.stderr[-2000:]}")
        else:
            print(f"ok   positive control: {total[0]}")

        result = compare(oracle, wrapper(tmp, "none", "core", oracle),
                         ["--compare-sanity-gap", "--quick"], driver=__file__)
        codes = {line.split()[1] for line in result.stdout.splitlines() if line.startswith("FAIL ")}
        if (result.returncode != 1 or codes != {"TX_VALID_CORE_COUNT"} or
                "FAIL TX_VALID_CORE_COUNT 90 acceptance checks, expected 91" not in result.stdout):
            failures += 1
            print(f"FAIL acceptance check count: exit {result.returncode}\n{result.stdout[-2000:]}{result.stderr[-2000:]}")
        else:
            print("ok   acceptance check count: FAIL TX_VALID_CORE_COUNT")

        rust_modes = {"none": None, "version": "VERSION", "consumed": "MISMATCH", "reason": "MISMATCH",
                      "rest_hex": "MISMATCH", "request_error": "REQUEST_ERROR", "drop": "COUNT",
                      "id": "ID", "malformed": "MALFORMED"}
        for mode, code in rust_modes.items():
            result = compare(oracle, wrapper(tmp, "none", "core", oracle),
                             ["--rust-compactsize", wrapper(tmp, mode, "rust", oracle)])
            codes = {line.split()[1] for line in result.stdout.splitlines() if line.startswith("FAIL ")}
            if result.returncode != (1 if code else 0) or (code and code not in codes):
                failures += 1
                print(f"FAIL Rust {mode}: exit {result.returncode}\n{result.stdout[-1500:]}{result.stderr[-1500:]}")
            else:
                print(f"ok   Rust {mode}: {code or 'positive control'}")

        for mode, (role, code) in MUTATIONS.items():
            env = dict(os.environ)
            pidfile = tmp / f"{mode}.pid"
            env["COMPARE_SELFTEST_PIDFILE"] = str(pidfile)
            if role == "both":
                oracle_side, harness_side = wrapper(tmp, mode, "oracle", oracle), wrapper(tmp, mode, "core", oracle)
            else:
                w = wrapper(tmp, mode, role, oracle)
                oracle_side, harness_side = (w, wrapper(tmp, "none", "core", oracle)) if role == "oracle" else (oracle, w)
            extra = ([] if mode in ("composition_stack", "targeted_early_error") else ["--quick"]) + ["--timeout", "5" if mode == "hang" else "120"]
            result = compare(oracle_side, harness_side, extra, env)
            codes = {line.split()[1] for line in result.stdout.splitlines() if line.startswith("FAIL ")}
            if result.returncode != 1 or code not in codes:
                failures += 1
                print(f"FAIL {mode}: expected exit 1 with FAIL {code}, got exit {result.returncode}, codes {sorted(codes)}")
                print(result.stdout[-1500:] + result.stderr[-1500:])
                continue
            if mode == "targeted_early_error" and codes != {"TARGETED_OPCODE"}:
                failures += 1
                print(f"FAIL {mode}: expected matching early errors, got failure codes {sorted(codes)}")
                continue
            if mode.startswith("refused_"):
                summaries = [line for line in result.stdout.splitlines() if line.startswith("Script harness refusal domain:")]
                if not summaries or "8 requests, 0 compared, 0 unsupported, 8 harness-refused, 1 disagreements" not in summaries[0]:
                    failures += 1
                    print(f"FAIL {mode}: failed refusal counted as compared: {summaries}")
                    continue
            if mode == "hang":
                # The wrapper's child must be gone with it.
                pid = int(pidfile.read_text())
                time.sleep(0.2)
                try:
                    os.kill(pid, 0)
                    failures += 1
                    print(f"FAIL hang: child {pid} of the wrapper still runs")
                    os.kill(pid, 9)
                    continue
                except ProcessLookupError:
                    pass
            print(f"ok   {mode}: FAIL {code}")
    print(f"{len(MUTATIONS) + len(rust_modes) + 2} cases, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
