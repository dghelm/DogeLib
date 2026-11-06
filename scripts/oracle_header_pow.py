"""Header PoW fixture requests and deterministic mutations, independent of the executables."""

import hashlib
import json
import pathlib
import random
import re

from capture_header_pow import full_headers

ROOT = pathlib.Path(__file__).resolve().parent.parent
SEED = 20261108
CODES = {"scrypt.hash": "SCRYPT_DIGEST", "block.header.read": "FULL_HEADER",
         "auxpow.check": "AUXPOW_VERDICT", "block.check_pow": "HEADER_POW",
         "block.check_version": "HEADER_VERSION"}


def child_hash_transaction(raw):
    return hashlib.sha256(hashlib.sha256(raw).digest()).digest()


def child_hash(raw):
    return child_hash_transaction(raw[:80])


def payload_cases():
    return json.loads((ROOT / "tests/block/check-auxpow.json").read_text())["cases"]


def pow_request(raw, height=0, network="mainnet"):
    return {"op": "block.check_pow", "bytes_hex": raw.hex(), "mode": "allow_witness",
            "network": network, "selection_height": height}


def aux_request(case):
    return {"op": "auxpow.check", "bytes_hex": case["payload_hex"], "mode": "allow_witness",
            "hash_hex": case["hash_aux_block_hex"], "chain_id": case["chain_id"],
            "strict_chain_id": case["strict_chain_id"]}


def mined_fixture():
    """The Core-mined components and assertion results from the pinned auxpow_pow test."""
    document = json.loads((ROOT / "tests/block/auxpow-pow.json").read_text())
    assert document["core_revision"] == "e0a1c157791544e818c901bd9341896965afbf9d"
    assert document["network"] == "regtest" and document["selection_height"] == 371337
    assert document["mode"] == "allow_witness" and document["scrypt_variant"] == "generic, --disable-scrypt-sse2"
    assert document["params"] == {"nAuxpowChainId": 98, "fStrictChainId": True, "powLimit_hex": "7" + "f" * 63}
    assert [c["line"] for c in document["cases"]] == [372, 378, 382, 386, 394, 398, 400, 420, 423, 439, 448, 450]
    assert [c["expected"] for c in document["cases"]] == [True, False, True, False, False, True, False, False, True, False, True, False]
    assert len(document["mining_checks"]) == 11
    assert document["hash_checks"] == [{"line": 436, "valid": True}, {"line": 438, "valid": True}]
    for case in document["cases"] + document["mining_checks"]:
        assert type(case["valid"]) is bool and case["valid"] == case["expected"]
        assert len(bytes.fromhex(case["bytes_hex"])) == 80
    return document


def fixture_cases():
    """Requests with independent committed expectations, separate from differential mutations."""
    out = [(aux_request(c), {"valid": c["expected"]}) for c in payload_cases()]
    report = json.loads((ROOT / "tests/block/core-header-pow.json").read_text())
    headers = full_headers()
    assert report["core_revision"] == "e0a1c157791544e818c901bd9341896965afbf9d"
    assert report["network"] == "mainnet" and report["scrypt_variant"] == "generic, --disable-scrypt-sse2"
    assert report["params"] == {"nAuxpowChainId": 98, "fStrictChainId": True, "powLimit_hex": "00000" + "f" * 59}
    assert report["mode"] == "allow_witness" and report["operation"] == "CheckAuxPowProofOfWork"
    assert report["cases"] == [{"height": h, "header_sha256": hashlib.sha256(raw).hexdigest(),
                                "selection_height": h, "valid": True} for h, raw in headers]
    for height, raw in headers:
        out.append((pow_request(raw, height), {"valid": True}))
        if len(raw) > 80:
            out.append(({"op": "auxpow.check", "bytes_hex": raw[80:].hex(), "mode": "allow_witness",
                         "hash_hex": child_hash(raw).hex(), "chain_id": int.from_bytes(raw[:4], "little", signed=True) >> 16,
                         "strict_chain_id": True}, {"valid": True}))
    # Core's inputhex and display-order expected pairs, independently committed in Lean.
    text = (ROOT / "tests/KnownAnswers/ScryptPow.lean").read_text()
    pairs = re.findall(r'\("([0-9a-f]{160})",\s*"([0-9a-f]{64})"\)', text)
    assert len(pairs) == 5
    out += [({"op": "scrypt.hash", "bytes_hex": raw}, {"digest_hex": bytes.fromhex(digest)[::-1].hex()})
            for raw, digest in pairs]
    mined = mined_fixture()
    for case in mined["cases"]:
        raw = bytes.fromhex(case["bytes_hex"])
        request = {**pow_request(raw, mined["selection_height"], mined["network"]), "payload_hex": case["payload_hex"]}
        out.append((request, {"valid": case["valid"]}))
        if bool(int.from_bytes(raw[:4], "little") & 256) == (case["payload_hex"] is not None):
            full = raw + (bytes.fromhex(case["payload_hex"]) if case["payload_hex"] is not None else b"")
            out.append((pow_request(full, mined["selection_height"], mined["network"]), {"valid": case["valid"]}))
    out += [({"op": "scrypt.hash", "bytes_hex": c["bytes_hex"]}, {"digest_hex": c["pow_hash_hex"]})
            for c in mined["mining_checks"]]
    return out


def key(request):
    return json.dumps({k: v for k, v in request.items() if k != "id"}, sort_keys=True)


EXPECTATIONS = {key(r): e for r, e in fixture_cases()}


def header_pow_sets():
    fixtures = [r for r, _ in fixture_cases()]
    read, versions, mutations = [], [], []
    headers = full_headers()
    # Complete decoded fields in both modes and every prefix of each AuxPoW header.
    for _, raw in headers:
        for mode in ("base", "allow_witness"):
            read.append({"op": "block.header.read", "bytes_hex": raw.hex() + "00ff", "mode": mode})
            if len(raw) > 80:
                read.extend({"op": "block.header.read", "bytes_hex": raw[:i].hex(), "mode": mode}
                            for i in range(len(raw)))
    for network, activation, heights in (("mainnet", 371337, [0, 144999, 145000, 371336, 371337, 371338, 0x7fffffff]),
                                         ("testnet", 158100, [0, 144999, 145000, 157499, 157500, 158099, 158100, 158101, 0x7fffffff]),
                                         ("regtest", 20, [0, 9, 10, 19, 20, 21, 0x7fffffff])):
        for height in heights:
            for v in [0, 1, 2, 3, 0x100, 0x620002, 0x620102, 0x80000000, 0xffffffff]:
                raw = v.to_bytes(4, "little") + bytes(76)
                r = {"op": "block.check_version", "bytes_hex": raw.hex(), "network": network,
                     "selection_height": height}
                versions.append(r)
                EXPECTATIONS[key(r)] = {"valid": not ((height >= activation and v in (1, 2)) or
                                                         (height < activation and v & 256 != 0))}
                mutations.append(pow_request(raw, height, network))
    rng = random.Random(SEED)
    # Payload bytes include scripts, hashes, branch indices and parent fields.
    for _ in range(256):
        case = rng.choice(payload_cases())
        r = aux_request(case)
        raw = bytearray.fromhex(r["bytes_hex"])
        raw[rng.randrange(len(raw))] ^= 1 << rng.randrange(8)
        mutations.append({**r, "bytes_hex": raw.hex()})
    # Keep the coinbase-to-parent binding intact while mutating search bytes.
    boundary = next(c for c in payload_cases() if c.get("name") == "trailing-8")
    for _ in range(100):
        r = aux_request(boundary)
        raw = bytearray.fromhex(r["bytes_hex"])
        script_length = raw[41]
        tx_end = 4 + 1 + 36 + 1 + script_length + 4 + 1 + 4
        raw[42 + rng.randrange(script_length)] ^= 1 << rng.randrange(8)
        raw[-44:-12] = child_hash_transaction(raw[:tx_end])
        mutations.append({**r, "bytes_hex": raw.hex()})
    for _ in range(256):
        height, raw = rng.choice(headers)
        raw = bytearray(raw)
        # Deliberately target version, nonce, child bits, parent bits and parent nonce.
        offset = rng.choice([rng.randrange(4), rng.randrange(72, 80)] +
                            ([len(raw) - 8 + rng.randrange(8)] if len(raw) > 80 else []))
        raw[offset] ^= 1 << rng.randrange(8)
        mutations.append(pow_request(raw, height))
        mutations.append({"op": "scrypt.hash", "bytes_hex": raw[:80].hex()})
    # Base and witness transactions, noncanonical empty witness and optional-data errors.
    pure = (0x620102).to_bytes(4, "little") + bytes(76)
    tail = bytes(32) + b'\x00' + bytes(4) + b'\x00' + bytes(4) + bytes(80)
    txs = [bytes.fromhex(s) for s in [
        "01000000000000000000", "010000000001000000000000", "0100000000020000000000",
        "01000000000101" + "00" * 36 + "00ffffffff000000000000",
        "01000000000101" + "00" * 36 + "00ffffffff000101aa00000000"]]
    for tx in txs:
        for mode in ("base", "allow_witness"):
            read.append({"op": "block.header.read", "bytes_hex": (pure + tx + tail).hex(), "mode": mode})
    # Malformed vector counts immediately after a known complete transaction and hashBlock.
    case = payload_cases()[0]
    raw = bytes.fromhex(case["payload_hex"])
    tx_end = 4 + 1 + 36 + 1 + raw[41] + 4 + 1 + 4
    for count in [b'\xfd\x00\x00', b'\xfe\x01\x00\x00\x02', b'\xff', b'\xfd']:
        changed = raw[:tx_end + 32] + count + raw[tx_end + 33:]
        read.append({"op": "block.header.read", "bytes_hex": (pure + changed).hex(), "mode": "base"})
    return [("header PoW fixtures", fixtures), ("full header readers", read),
            ("header version boundaries", versions), ("header PoW mutations seed 20261108", mutations)]
