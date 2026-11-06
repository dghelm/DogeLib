"""Capture pinned Core header-PoW fixtures without running Lean.

Usage: python3 -I scripts/capture_header_pow.py CORE_ORACLE OUTPUT_DIR --capture-date YYYY-MM-DD

The capture writes new files in OUTPUT_DIR. Tests never invoke it to overwrite expectations.
"""

import argparse
import hashlib
import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
CORE_REVISION = "e0a1c157791544e818c901bd9341896965afbf9d"


def full_headers():
    """All headers used by HeaderPow.lean, from the committed raw fixtures."""
    out = [(int(h), bytes.fromhex(raw)) for h, raw in
           (line.split() for line in (ROOT / "tests/work/mainnet-headers/headers.txt").read_text().splitlines())]
    out += [(r["height"], bytes.fromhex(r["header"])) for r in
            json.loads((ROOT / "tests/block/mainnet.json").read_text())]
    out += [(r["height"], bytes.fromhex(r["block"])[:r["headerLength"]]) for r in
            json.loads((ROOT / "tests/block/auxpow-headers.json").read_text())]
    return out


def capture(harness, output, date):
    headers = full_headers()
    requests = [{"id": height, "op": "block.check_pow", "bytes_hex": raw.hex(),
                 "mode": "allow_witness", "network": "mainnet", "selection_height": height}
                for height, raw in headers]
    process = subprocess.run([harness], input="".join(json.dumps(r) + "\n" for r in requests),
                             text=True, capture_output=True, check=True, timeout=600)
    responses = [json.loads(line) for line in process.stdout.splitlines()]
    if len(responses) != len(headers):
        raise ValueError("Core did not return one response per historical header")
    cases = []
    for (height, raw), response in zip(headers, responses):
        if response != {"id": height, "ok": {"valid": True}} or type(response["ok"]["valid"]) is not bool:
            raise ValueError(f"Core did not accept historical header {height}: {response}")
        cases.append({"height": height, "header_sha256": hashlib.sha256(raw).hexdigest(),
                      "selection_height": height, "valid": response["ok"]["valid"]})
    historical = {
        "core_revision": CORE_REVISION, "network": "mainnet", "mode": "allow_witness",
        "scrypt_variant": "generic, --disable-scrypt-sse2",
        # Mainnet's three PoW fields in pinned chainparams.cpp (SOURCES.md D14).
        "params": {"nAuxpowChainId": 98, "fStrictChainId": True, "powLimit_hex": "00000" + "f" * 59},
        "operation": "CheckAuxPowProofOfWork",
        "inputs": "Exact header bytes and heights in mainnet.json, auxpow-headers.json and ../work/mainnet-headers/headers.txt",
        "cases": cases,
    }
    mined = json.loads(subprocess.run([harness, "--auxpow-pow-fixtures"], text=True,
                                     capture_output=True, check=True, timeout=600).stdout)
    if mined["core_revision"] != CORE_REVISION or len(mined["cases"]) != 12 or len(mined["mining_checks"]) != 11:
        raise ValueError("unexpected Core auxpow_pow capture")
    if any(type(c["valid"]) is not bool or c["valid"] != c["expected"]
           for c in mined["cases"] + mined["mining_checks"]):
        raise ValueError("Core auxpow_pow assertion failed")
    if mined["hash_checks"] != [{"line": 436, "valid": True}, {"line": 438, "valid": True}]:
        raise ValueError("Core auxpow_pow version/hash assertion failed")
    output.mkdir(parents=True, exist_ok=True)
    for name, document in (("core-header-pow.json", historical), ("auxpow-pow.json", mined)):
        document["generator"] = "scripts/capture_header_pow.py"
        document["capture_date"] = date
        (output / name).write_text(json.dumps(document, indent=2) + "\n")
    print(f"captured {len(cases)} historical headers, 12 mined cases, 11 mining checks and two hash checks")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("harness")
    parser.add_argument("output", type=pathlib.Path)
    parser.add_argument("--capture-date", required=True)
    args = parser.parse_args()
    capture(str(pathlib.Path(args.harness).resolve()), args.output, args.capture_date)


if __name__ == "__main__":
    main()
