"""Fixture requests and independent expectations for the hash and block oracle operations.

Inputs and digest expectations come from the committed fixtures and their provenance.
Header fields follow the fixed layout of Core's CPureBlockHeader serialization.
No function calls the oracle or produces a hash expectation from DogeLib.
"""

import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent


def header_fields(raw: bytes) -> dict:
    """Read the six raw fields by D10's fixed offsets, independently of either executable."""
    assert len(raw) == 80
    return {"version": int.from_bytes(raw[:4], "little"), "prev_block_hex": raw[4:36].hex(),
            "merkle_root_hex": raw[36:68].hex(), "time": int.from_bytes(raw[68:72], "little"),
            "bits": int.from_bytes(raw[72:76], "little"), "nonce": int.from_bytes(raw[76:80], "little")}


def hash_fields(name: str, internal_hex: str) -> dict:
    return {name + "_hex": internal_hex, name + "_display": bytes.fromhex(internal_hex)[::-1].hex()}


def header_records() -> list[tuple[bytes, str]]:
    """All 315 recorded pure headers with their independently recorded display hashes."""
    lines = (ROOT / "tests/work/mainnet-headers/headers.txt").read_text().splitlines()
    headers = [bytes.fromhex(line.split()[1]) for line in lines]
    last_hash = (ROOT / "tests/block/last-header-hash.txt").read_text().strip()
    records = [(raw, headers[i + 1][4:36][::-1].hex() if i + 1 < len(headers) else last_hash)
               for i, raw in enumerate(headers)]
    records.extend((bytes.fromhex(r["header"]), r["blockHash"])
                   for r in json.loads((ROOT / "tests/block/mainnet.json").read_text()))
    assert len(records) == 315
    return records


def header_fixtures() -> list[tuple[dict, dict]]:
    cases = []
    for raw, display in header_records():
        fields = header_fields(raw)
        result = {**fields, "prev_block_display": raw[4:36][::-1].hex(),
                  "merkle_root_display": raw[36:68][::-1].hex()}
        cases.extend([
            ({"op": "header.read", "bytes_hex": raw.hex()},
             {"header": result, "consumed": 80, "rest_hex": ""}),
            ({"op": "header.encode", "header": fields}, {"bytes_hex": raw.hex()}),
            ({"op": "header.hash", "header": fields}, hash_fields("hash", bytes.fromhex(display)[::-1].hex())),
            ({"op": "header.read", "bytes_hex": raw.hex() + "00ffab"},
             {"header": result, "consumed": 80, "rest_hex": "00ffab"}),
        ])
    return cases


def merkle_fixtures() -> list[tuple[dict, dict]]:
    records = json.loads((ROOT / "tests/block/merkle.json").read_text())
    # The fixture hashes are in display order, as its README and Lean test driver specify.
    cases = [({"op": "merkle.compute", "leaves_hex": [bytes.fromhex(h)[::-1].hex() for h in r["leaves"]]},
              {**hash_fields("root", bytes.fromhex(r["root"])[::-1].hex()), "mutated": r["mutated"]})
             for r in records]
    for r in json.loads((ROOT / "tests/block/mainnet.json").read_text()):
        cases.append(({"op": "merkle.compute", "leaves_hex": [bytes.fromhex(h)[::-1].hex() for h in r["txids"]]},
                      {**hash_fields("root", r["header"][72:136]), "mutated": False}))
    assert len(cases) == 37
    return cases


def fixture_message(record: dict) -> bytes:
    encoding = record["encoding"]
    if encoding == "hex":
        return bytes.fromhex(record["message"])
    if encoding == "repeat_a":
        return b"a" * int(record["message"])
    if encoding == "core_long":
        return bytes((i >> shift) & 255 for i in range(200000) for shift in (0, 4, 8, 12, 16))
    raise ValueError(f"unknown message encoding: {encoding}")


def hash_fixtures() -> list[tuple[dict, dict]]:
    records = json.loads((ROOT / "tests/cryptography/ripemd160/vectors.json").read_text())
    cases = [({"op": "hash." + r["algorithm"], "bytes_hex": fixture_message(r).hex()},
              {"digest_hex": r["digest"]}) for r in records]
    return cases


def sha1_fixtures() -> list[tuple[dict, dict]]:
    """NIST short, long and final Monte Carlo inputs, plus Core's ten SHA-1 vectors."""
    import hashlib

    cases = []
    base = ROOT / "tests/cryptography/sha1/cavp"
    for filename, count in (("SHA1ShortMsg.rsp", 65), ("SHA1LongMsg.rsp", 64)):
        pending = {}
        start = len(cases)
        for line in (base / filename).read_text().splitlines():
            if " = " not in line:
                continue
            key, value = line.split(" = ", 1)
            pending[key] = value
            if key == "MD":
                bits = int(pending["Len"])
                assert bits % 8 == 0
                message = bytes.fromhex(pending["Msg"])[:bits // 8]
                cases.append(({"op": "hash.sha1", "bytes_hex": message.hex()}, {"digest_hex": value}))
                pending = {}
        assert len(cases) - start == count

    # Independently derive each checkpoint's final input with hashlib.
    # The expected final digest comes from NIST, rather than from the oracle.
    seed = None
    count = 0
    for line in (base / "SHA1Monte.rsp").read_text().splitlines():
        if line.startswith("Seed = "):
            seed = bytes.fromhex(line[7:])
        elif line.startswith("COUNT = "):
            assert int(line[8:]) == count
        elif line.startswith("MD = "):
            assert seed is not None
            a = b = c = seed
            for _ in range(999):
                a, b, c = b, c, hashlib.sha1(a + b + c).digest()
            message = a + b + c
            expected = line[5:]
            assert hashlib.sha1(message).hexdigest() == expected
            cases.append(({"op": "hash.sha1", "bytes_hex": message.hex()}, {"digest_hex": expected}))
            seed = bytes.fromhex(expected)
            count += 1
    assert count == 100

    # Core e0a1c15, crypto_tests.cpp lines 220-233, sha1_testvectors (MIT).
    # Input messages match its RIPEMD-160 vector order, including LongTestString.
    records = json.loads((ROOT / "tests/cryptography/ripemd160/vectors.json").read_text())
    messages = [fixture_message(r) for r in records if r["source"] == "core_crypto_tests"]
    digests = ["da39a3ee5e6b4b0d3255bfef95601890afd80709", "a9993e364706816aba3e25717850c26c9cd0d89d",
               "c12252ceda8be8994d5fa0290a47231c1d16aae3", "d4d6d2f0ebe317513bbd8d967d89bac5819c2f60",
               "f2b6650569ad3a8720348dd6ea6c497dee3a842a", "84983e441c3bd26ebaae4aa1f95129e5e54670f1",
               "4f0ea5cd0585a23d028abdc1a6684e5a8094dc49", "fb679f23e7d1ce053313e66e127ab1b444397057",
               "34aa973cd4c4daa4f61eeb2bdbad27316534016f", "b7755760681cbfd971451668f32af5774f4656b5"]
    assert len(messages) == len(digests) == 10
    # Core uses an algorithm-specific sentence for the fifth input.
    messages[4] = b"SHA1 is considered to be safe"
    cases.extend(({"op": "hash.sha1", "bytes_hex": m.hex()}, {"digest_hex": d})
                 for m, d in zip(messages, digests))
    assert len(cases) == 239
    return cases
