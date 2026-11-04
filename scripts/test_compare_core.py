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
ORACLE_FORMAT = "dogelib-oracle/2"
HARNESS_FORMAT = "dogelib-oracle/2-core-projection"

# mode: (role of the wrapper, expected failure code). The role "core" stands
# in for the harness, "oracle" for dogelib-oracle.
MUTATIONS = {
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
    projected_format = HARNESS_FORMAT if role == "core" else ORACLE_FORMAT
    if mode == "version" and role == "core":
        projected_format = ORACLE_FORMAT
    if args == ["--version"]:
        print(json.dumps({"format": projected_format}, separators=(",", ":")))
        return 0
    data = sys.stdin.read()
    out = subprocess.run([oracle], input=data, capture_output=True, text=True, check=True).stdout
    responses = [json.loads(line) for line in out.splitlines()]
    for resp in responses:
        ok = resp.get("ok", {})
        if "format" in ok:
            ok["format"] = projected_format
        if role == "core" and mode != "core_preimage":
            ok.pop("preimage_hex", None)

    def set_ok(field, value):
        return lambda r: r["ok"].__setitem__(field, value)

    if mode == "wtxid":
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


def compare(oracle: str, harness: str, extra: list[str], env=None) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-I", str(COMPARE), *extra, oracle, harness],
                          capture_output=True, text=True, env=env, timeout=900)


def main() -> int:
    if len(sys.argv) >= 5 and sys.argv[1] == "--wrap":
        return wrap(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:])
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    oracle = str(pathlib.Path(sys.argv[1]).resolve())
    failures = 0
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

        for mode, (role, code) in MUTATIONS.items():
            env = dict(os.environ)
            pidfile = tmp / f"{mode}.pid"
            env["COMPARE_SELFTEST_PIDFILE"] = str(pidfile)
            w = wrapper(tmp, mode, role, oracle)
            oracle_side, harness_side = (w, wrapper(tmp, "none", "core", oracle)) if role == "oracle" else (oracle, w)
            extra = ["--quick", "--timeout", "5" if mode == "hang" else "120"]
            result = compare(oracle_side, harness_side, extra, env)
            codes = {line.split()[1] for line in result.stdout.splitlines() if line.startswith("FAIL ")}
            if result.returncode != 1 or code not in codes:
                failures += 1
                print(f"FAIL {mode}: expected exit 1 with FAIL {code}, got exit {result.returncode}, codes {sorted(codes)}")
                print(result.stdout[-1500:] + result.stderr[-1500:])
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
    print(f"{len(MUTATIONS) + 1} cases, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
