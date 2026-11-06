#!/usr/bin/env python3
"""Write tests/block/check-auxpow.json from Core's check_auxpow test.

The script transcribes the deterministic construction of `check_auxpow` in
src/test/auxpow_tests.cpp (lines 186 to 323) at Core commit
e0a1c157791544e818c901bd9341896965afbf9d. It uses Python's hashlib and its own
writers of Core's stream format. It does not read DogeLib.

Each record is one BOOST_CHECK: the payload bytes that `get()` would build,
the arguments of `check`, and the Boolean that the assertion expects.

Usage: python3 -I tests/block/import_check_auxpow.py tests/block/check-auxpow.json
"""

import copy
import hashlib
import json
import struct
import sys

CORE_COMMIT = "e0a1c157791544e818c901bd9341896965afbf9d"

# src/auxpow.h, line 24.
MERGED_MINING_HEADER = bytes([0xFA, 0xBE, ord("m"), ord("m")])
# src/primitives/pureheader.h: VERSION_CHAIN_START.
VERSION_CHAIN_START = 1 << 16
# src/chainparams.cpp, lines 120 and 121: the mainnet record that
# GetConsensus(371337) returns.
MAINNET_AUXPOW_CHAIN_ID = 0x0062
MAINNET_STRICT_CHAIN_ID = True
# src/script/script.h.
OP_0 = 0x00
OP_1 = 0x51
OP_2 = 0x52
OP_PUSHDATA1 = 0x4C


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def u32(n: int) -> bytes:
    return struct.pack("<I", n & 0xFFFFFFFF)


def i32(n: int) -> bytes:
    """An `int` in memory on a little-endian host, as two's complement."""
    return struct.pack("<I", n & 0xFFFFFFFF)


def compact_size(n: int) -> bytes:
    if n < 0xFD:
        return bytes([n])
    if n <= 0xFFFF:
        return b"\xfd" + struct.pack("<H", n)
    if n <= 0xFFFFFFFF:
        return b"\xfe" + struct.pack("<I", n)
    return b"\xff" + struct.pack("<Q", n)


def arith_to_uint256(n: int) -> bytes:
    """ArithToUint256: the internal bytes of a uint256 are little-endian."""
    return (n % (1 << 256)).to_bytes(32, "little")


def tamper_with(num: bytes) -> bytes:
    """tamperWith (lines 31 to 37): add one to the arith_uint256 value."""
    return arith_to_uint256(int.from_bytes(num, "little") + 1)


# --- CScript (src/script/script.h) ---

def scriptnum_serialize(n: int) -> bytes:
    """CScriptNum::serialize."""
    if n == 0:
        return b""
    neg = n < 0
    absvalue = -n if neg else n
    out = bytearray()
    while absvalue:
        out.append(absvalue & 0xFF)
        absvalue >>= 8
    if out[-1] & 0x80:
        out.append(0x80 if neg else 0x00)
    elif neg:
        out[-1] |= 0x80
    return bytes(out)


def push_data(b: bytes) -> bytes:
    """CScript::operator<<(const std::vector<unsigned char>&), for the sizes used here."""
    assert len(b) < OP_PUSHDATA1
    return bytes([len(b)]) + b


def push_int64(n: int) -> bytes:
    """CScript::push_int64."""
    if n == -1 or 1 <= n <= 16:
        return bytes([n + (OP_1 - 1)])
    if n == 0:
        return bytes([OP_0])
    return push_data(scriptnum_serialize(n))


COINBASE_FLAGS = b""  # src/validation.cpp, line 100. Only miner.cpp and RPC read it.


# --- Transactions and blocks ---

def tx_serialize(tx) -> bytes:
    """SerializeTransaction without witness data: none of these transactions has any."""
    out = u32(tx["version"]) + compact_size(len(tx["vin"]))
    for script in tx["vin"]:
        out += bytes(32) + u32(0xFFFFFFFF)  # COutPoint::SetNull
        out += compact_size(len(script)) + script
        out += u32(0xFFFFFFFF)  # CTxIn::SEQUENCE_FINAL, the default
    out += compact_size(0)  # no outputs
    out += u32(0)  # nLockTime
    return out


def coinbase(script: bytes):
    """setCoinbase (lines 120 to 130): CMutableTransaction with version 1 and one null input."""
    return {"version": 1, "vin": [script]}


def txid(tx) -> bytes:
    return sha256d(tx_serialize(tx))


def merkle_levels(leaves):
    levels = [list(leaves)]
    while len(levels[-1]) > 1:
        level = levels[-1]
        if len(level) % 2:
            level = level + [level[-1]]
        levels.append([sha256d(level[i] + level[i + 1]) for i in range(0, len(level), 2)])
    return levels


def merkle_root(leaves) -> bytes:
    return merkle_levels(leaves)[-1][0]


def merkle_branch(leaves, position: int):
    branch = []
    for level in merkle_levels(leaves)[:-1]:
        sibling = position ^ 1
        branch.append(level[sibling] if sibling < len(level) else level[position])
        position >>= 1
    return branch


class Block:
    def __init__(self):
        self.version = 0
        self.hash_prev = bytes(32)
        self.hash_merkle_root = bytes(32)
        self.time = 0
        self.bits = 0
        self.nonce = 0
        self.vtx = []

    def header(self) -> bytes:
        return (i32(self.version) + self.hash_prev + self.hash_merkle_root
                + u32(self.time) + u32(self.bits) + u32(self.nonce))

    def set_chain_id(self, chain_id: int):
        """SetChainId: nVersion %= VERSION_CHAIN_START, then the chain ID in the high bits."""
        self.version = (self.version % VERSION_CHAIN_START) | (chain_id * VERSION_CHAIN_START)


# --- CAuxPow helpers (src/auxpow.cpp, lines 163 to 206) ---

def get_expected_index(nonce: int, chain_id: int, h: int) -> int:
    rand = nonce & 0xFFFFFFFF
    rand = (rand * 1103515245 + 12345) & 0xFFFFFFFF
    rand = (rand + chain_id) & 0xFFFFFFFF
    rand = (rand * 1103515245 + 12345) & 0xFFFFFFFF
    # `1 << h` is an int. For h = 31 GCC gives INT_MIN, which the usual
    # arithmetic conversions turn into 2^31. check never reaches h = 31.
    modulus = (1 << h) & 0xFFFFFFFF
    result = rand % modulus
    assert result < (1 << 31)
    return result


def check_merkle_branch(h: bytes, branch, index: int) -> bytes:
    if index == -1:
        return bytes(32)
    for b in branch:
        if index & 1:
            h = sha256d(b + h)
        else:
            h = sha256d(h + b)
        index >>= 1  # Python's shift of a negative int is arithmetic.
    return h


# --- CAuxpowBuilder (lines 39 to 177) ---

class Builder:
    def __init__(self, base_version: int, chain_id: int):
        self.parent = Block()
        self.parent.version = base_version | (chain_id * VERSION_CHAIN_START)  # SetBaseVersion
        self.chain_branch = []
        self.chain_index = -1

    def set_coinbase(self, script: bytes):
        self.parent.vtx = [coinbase(script)]
        self.parent.hash_merkle_root = merkle_root([txid(t) for t in self.parent.vtx])

    def build_auxpow_chain(self, hash_aux: bytes, h: int, index: int) -> bytes:
        self.chain_index = index
        self.chain_branch = [arith_to_uint256(i) for i in range(h)]
        return check_merkle_branch(hash_aux, self.chain_branch, index)[::-1]

    def get(self, tx=None) -> bytes:
        """get(tx): the serialized CAuxPow. InitMerkleBranch(parentBlock, 0) always uses position 0."""
        if tx is None:
            tx = self.parent.vtx[0]
        header = self.parent.header()
        branch = merkle_branch([txid(t) for t in self.parent.vtx], 0)
        out = tx_serialize(tx)
        out += sha256d(header)  # hashBlock = parentBlock.GetHash()
        out += compact_size(len(branch)) + b"".join(branch)
        out += i32(0)  # nIndex
        out += compact_size(len(self.chain_branch)) + b"".join(self.chain_branch)
        out += i32(self.chain_index)
        out += header
        return out


def build_coinbase_data(header: bool, aux_root: bytes, h: int, nonce: int) -> bytes:
    res = MERGED_MINING_HEADER if header else b""
    res += aux_root
    res += i32(1 << h)  # `const int size = (1 << h)`: INT_MIN for h = 31 with GCC
    res += i32(nonce)
    return res


# For each failing BOOST_CHECK, the line of the `return error` in src/auxpow.cpp
# that the case reaches first. These come from reading the construction and
# CAuxPow::check (lines 80 to 161), not from running any implementation.
ERROR_LINES = {
    213: 106,  # no inputs
    219: 106,  # the coinbase of line 213 still has no inputs
    220: 106,  # likewise
    231: 102,  # the second transaction's ID with the coinbase's branch
    238: 88,   # parent has our chain ID
    248: 91,   # 31 hashes
    254: 102,  # tampered Merkle root
    273: 137,  # our root starts at offset 42, without a marker
    277: 129,  # marker at 42, our root at 1
    279: 129,  # marker at 1, our root at 46
    283: 127,  # two markers
    285: 127,  # two markers
    302: 145,  # seven bytes after the root
    306: 152,  # size word 2^29 for 30 hashes
    310: 158,  # wrong nonce
    317: 120,  # the script holds the root of slot index + 1
}


def boundary_cases():
    """Boundary cases of design record 0004, stage 3, built with the helpers above.

    Each case has one coinbase transaction, so the coinbase branch is empty.
    The expected result and error line follow from CAuxPow::check by reading.
    """
    chain_id = MAINNET_AUXPOW_CHAIN_ID
    hash_aux = bytes(range(32))  # not a palindrome
    nonce = 7
    out = []

    def payload(script: bytes, h: int, chain_index, chain_id=chain_id, nonce=nonce, root_index=None,
                parent_chain_id=42):
        """A payload whose script holds `script(root, size_and_nonce)`."""
        b = Builder(5, parent_chain_id)
        if chain_index is None:
            chain_index = get_expected_index(nonce, chain_id, h)
        if root_index is None:
            root_index = chain_index
        b.chain_branch = [arith_to_uint256(i) for i in range(h)]
        root = check_merkle_branch(hash_aux, b.chain_branch, root_index)
        assert root_index == -1 or root != root[::-1]
        b.chain_index = chain_index
        words = i32(1 << h) + i32(nonce)
        b.set_coinbase(script(root[::-1], words, root))
        return b.get()

    def add(name, data, expected, error_line, note, chain_id=chain_id, strict=True):
        out.append({
            "kind": "boundary",
            "name": name,
            "error_line": error_line,
            "note": note,
            "payload_hex": data.hex(),
            "hash_aux_block_hex": hash_aux.hex(),
            "chain_id": chain_id,
            "strict_chain_id": strict,
            "expected": expected,
        })

    marker = MERGED_MINING_HEADER
    with_marker = lambda r, w, _: marker + r + w
    add("branch-30", payload(with_marker, 30, None), True, None, "chain branch of 30 hashes (line 90)")
    add("branch-31", payload(with_marker, 31, 0), False, 91, "chain branch of 31 hashes (line 90)")

    add("offset-20", payload(lambda r, w, _: bytes(20) + r + w, 2, None), True, None,
        "no marker, root at offset 20 (line 136)")
    add("offset-21", payload(lambda r, w, _: bytes(21) + r + w, 2, None), False, 137,
        "no marker, root at offset 21 (line 136)")
    add("second-marker", payload(lambda r, w, _: marker + r + w + marker, 2, None), False, 127,
        "a second marker after the size and nonce (line 126)")
    add("root-before-marker", payload(lambda r, w, _: r + w + marker, 2, None), False, 129,
        "root at offset 0, marker at offset 40 (line 128)")
    add("trailing-7", payload(lambda r, w, _: marker + r + w[:7], 2, None), False, 145,
        "seven bytes after the root (line 144)")
    add("trailing-8", payload(lambda r, w, _: marker + r + w, 2, None), True, None,
        "exactly eight bytes after the root (line 144)")
    add("root-internal-order", payload(lambda r, w, root: marker + root + w, 2, None), False, 120,
        "the root in internal byte order, not reversed (lines 96 to 97 and 116 to 120)")

    expected_index = get_expected_index(nonce, chain_id, 2)
    add("chain-index-minus-1", payload(with_marker, 2, -1), False, 158,
        "nChainIndex -1: the zero root is in the script, and -1 is not the expected index (lines 157 to 158)")
    add("chain-index-minus-2", payload(with_marker, 2, -2), False, 158,
        "nChainIndex -2, root with the arithmetic shift (lines 157 to 158)")
    add("chain-index-2^h", payload(with_marker, 2, expected_index + 4), False, 158,
        "nChainIndex = expected + 2^h, out of range for h = 2 (lines 157 to 158)")
    add("chain-index-other-slot", payload(with_marker, 2, (expected_index + 1) % 4), False, 158,
        "nChainIndex in range but not the expected slot (lines 157 to 158)")

    add("not-strict-same-chain", payload(with_marker, 2, None, parent_chain_id=chain_id), True, None,
        "parent with our chain ID and fStrictChainId false, as on testnet (line 87)", strict=False)
    add("strict-same-chain", payload(with_marker, 2, None, parent_chain_id=chain_id), False, 88,
        "parent with our chain ID and fStrictChainId true (line 87)")
    add("negative-chain-id", payload(with_marker, 2, None, chain_id=-1), True, None,
        "chain ID -1, converted modulo 2^32 in getExpectedIndex (line 183)", chain_id=-1)
    return out


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2

    cases = []

    def record(line, payload, hash_aux, chain_id, expected, note):
        cases.append({
            "kind": "check_auxpow",
            "line": line,
            "error_line": ERROR_LINES.get(line),
            "note": note,
            "payload_hex": payload.hex(),
            "hash_aux_block_hex": hash_aux.hex(),
            "chain_id": chain_id,
            "strict_chain_id": MAINNET_STRICT_CHAIN_ID,
            "expected": expected,
        })

    builder = Builder(5, 42)
    hash_aux = arith_to_uint256(12345)
    our_chain_id = MAINNET_AUXPOW_CHAIN_ID
    height = 30
    nonce = 7

    # Lines 198 to 204.
    index = get_expected_index(nonce, our_chain_id, height)
    aux_root = builder.build_auxpow_chain(hash_aux, height, index)
    data = build_coinbase_data(True, aux_root, height, nonce)
    scr = push_int64(2809) + push_int64(2013) + COINBASE_FLAGS
    scr = scr + bytes([OP_2]) + push_data(data)
    builder.set_coinbase(scr)
    record(204, builder.get(), hash_aux, our_chain_id, True, "valid payload, branch of 30 hashes, marker")

    # Lines 208 to 213.
    builder.parent.vtx = [{"version": 1, "vin": []}]
    builder.parent.hash_merkle_root = merkle_root([txid(t) for t in builder.parent.vtx])
    record(213, builder.get(), hash_aux, our_chain_id, False, "coinbase without inputs")

    # Lines 217 to 220.
    modified_aux = tamper_with(hash_aux)
    record(219, builder.get(), modified_aux, our_chain_id, False, "tampered merge-mined hash; the coinbase from line 213 still has no inputs")
    record(220, builder.get(), hash_aux, our_chain_id + 1, False, "chain ID plus one; the coinbase from line 213 still has no inputs")

    # Lines 224 to 231. `scr << 5` appends OP_5 to scr itself.
    old_coinbase = builder.parent.vtx[0]
    scr = scr + push_int64(5)
    builder.set_coinbase(scr)
    builder.parent.vtx.append(old_coinbase)
    builder.parent.hash_merkle_root = merkle_root([txid(t) for t in builder.parent.vtx])
    record(229, builder.get(builder.parent.vtx[0]), hash_aux, our_chain_id, True,
           "coinbase of a two-transaction parent")
    record(231, builder.get(builder.parent.vtx[1]), hash_aux, our_chain_id, False,
           "second transaction with the coinbase's branch")

    # Lines 234 to 238.
    builder2 = copy.deepcopy(builder)
    builder2.parent.set_chain_id(100)
    record(236, builder2.get(), hash_aux, our_chain_id, True, "parent chain ID 100")
    builder2.parent.set_chain_id(our_chain_id)
    record(238, builder2.get(), hash_aux, our_chain_id, False, "parent with our chain ID")

    # Lines 241 to 248.
    builder2 = copy.deepcopy(builder)
    index = get_expected_index(nonce, our_chain_id, height + 1)
    aux_root = builder2.build_auxpow_chain(hash_aux, height + 1, index)
    data = build_coinbase_data(True, aux_root, height + 1, nonce)
    scr = push_int64(2809) + push_int64(2013) + COINBASE_FLAGS
    scr = scr + bytes([OP_2]) + push_data(data)
    builder2.set_coinbase(scr)
    record(248, builder2.get(), hash_aux, our_chain_id, False, "chain branch of 31 hashes")

    # Lines 251 to 254.
    builder2 = copy.deepcopy(builder)
    record(252, builder2.get(), hash_aux, our_chain_id, True, "copy of the two-transaction parent")
    builder2.parent.hash_merkle_root = tamper_with(builder2.parent.hash_merkle_root)
    record(254, builder2.get(), hash_aux, our_chain_id, False, "tampered parent Merkle root")

    # Lines 257 to 264.
    builder2 = copy.deepcopy(builder)
    index = get_expected_index(nonce, our_chain_id, height)
    aux_root = builder2.build_auxpow_chain(hash_aux, height, index)
    data = build_coinbase_data(False, aux_root, height, nonce)
    scr = push_int64(2809) + push_int64(2013) + COINBASE_FLAGS
    scr = scr + bytes([OP_2]) + push_data(data)
    builder2.set_coinbase(scr)
    record(264, builder2.get(), hash_aux, our_chain_id, True, "no marker, root within 20 bytes")

    # Lines 268 to 292.
    wrong_aux_root = builder2.build_auxpow_chain(modified_aux, height, index)
    data2 = build_coinbase_data(False, wrong_aux_root, height, nonce)
    builder2.set_coinbase(push_data(data) + push_data(data2))
    record(271, builder2.get(), hash_aux, our_chain_id, True, "no markers, our root first")
    builder2.set_coinbase(push_data(data2) + push_data(data))
    record(273, builder2.get(), hash_aux, our_chain_id, False, "no markers, our root second")

    data2 = build_coinbase_data(True, wrong_aux_root, height, nonce)
    builder2.set_coinbase(push_data(data) + push_data(data2))
    record(277, builder2.get(), hash_aux, our_chain_id, False, "our root without marker, other root with marker")
    builder2.set_coinbase(push_data(data2) + push_data(data))
    record(279, builder2.get(), hash_aux, our_chain_id, False, "other root with marker first")

    data = build_coinbase_data(True, aux_root, height, nonce)
    builder2.set_coinbase(push_data(data) + push_data(data2))
    record(283, builder2.get(), hash_aux, our_chain_id, False, "two markers, our root first")
    builder2.set_coinbase(push_data(data2) + push_data(data))
    record(285, builder2.get(), hash_aux, our_chain_id, False, "two markers, our root second")

    data2 = build_coinbase_data(False, wrong_aux_root, height, nonce)
    builder2.set_coinbase(push_data(data) + push_data(data2))
    record(290, builder2.get(), hash_aux, our_chain_id, True, "our root with marker, other root without")
    builder2.set_coinbase(push_data(data2) + push_data(data))
    record(292, builder2.get(), hash_aux, our_chain_id, True, "other root without marker first, then ours with marker")

    # Lines 296 to 310.
    data = build_coinbase_data(True, aux_root, height, nonce)
    builder2.set_coinbase(push_data(data))
    record(298, builder2.get(), hash_aux, our_chain_id, True, "marker, root, size and nonce")

    data = data[:-1]
    builder2.set_coinbase(push_data(data))
    record(302, builder2.get(), hash_aux, our_chain_id, False, "seven bytes after the root")

    data = build_coinbase_data(True, aux_root, height - 1, nonce)
    builder2.set_coinbase(push_data(data))
    record(306, builder2.get(), hash_aux, our_chain_id, False, "size word for 29 hashes")

    data = build_coinbase_data(True, aux_root, height, nonce + 3)
    builder2.set_coinbase(push_data(data))
    record(310, builder2.get(), hash_aux, our_chain_id, False, "nonce plus three")

    # Lines 314 to 322. These two calls change `builder`, not `builder2`.
    aux_root = builder.build_auxpow_chain(hash_aux, height, index + 1)
    data = build_coinbase_data(True, aux_root, height, nonce)
    builder2.set_coinbase(push_data(data))
    record(317, builder2.get(), hash_aux, our_chain_id, False, "root of the next slot")

    aux_root = builder.build_auxpow_chain(hash_aux, height, index)
    data = build_coinbase_data(True, aux_root, height, nonce)
    builder2.set_coinbase(push_data(data))
    record(322, builder2.get(), hash_aux, our_chain_id, True, "root of the expected slot again")

    assert len(cases) == 26, len(cases)
    cases.extend(boundary_cases())
    doc = {
        "source": f"dogecoin/dogecoin {CORE_COMMIT} src/test/auxpow_tests.cpp, check_auxpow, lines 186 to 323",
        "generator": "tests/block/import_check_auxpow.py",
        "payload_format": "CAuxPow serialization, witness-allowed stream; no transaction has witness data",
        "hash_order": "hash_aux_block_hex is in internal (serialized) byte order",
        "expected": "check_auxpow: the Boolean of the BOOST_CHECK at `line`. boundary: argued from CAuxPow::check",
        "error_line": "the line of src/auxpow.cpp whose `return error` the case reaches, from reading the source; null on acceptance",
        "cases": cases,
    }
    with open(sys.argv[1], "w", encoding="utf-8") as f:
        json.dump(doc, f, indent=2)
        f.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
