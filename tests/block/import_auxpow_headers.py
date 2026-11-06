"""Build tests/block/auxpow-headers.json from Blockchair raw blocks, with independent checks.

Usage: python3 -I tests/block/import_auxpow_headers.py <fetch-dir> tests/block/auxpow-headers.json
       python3 -I tests/block/import_auxpow_headers.py --self-test

The parser below is written from Dogecoin Core's stream format (D41, D54, D4, D1), not from DogeLib.
`<fetch-dir>/<height>.json` is the response of
`curl -s "https://api.blockchair.com/dogecoin/raw/block/<checkpoint hash>"`.
"""
import hashlib
import json
import sys

CHECKPOINTS = {
    371337: "60323982f9c5ff1b5a954eac9dc1269352835f47c2c5222691d80f0d50dcf053",
    450000: "d279277f8f846a224d776450aa04da3cf978991a182c6f3075db4c48b173bbd7",
    771275: "1b7d789ed82cbdc640952e7e7a54966c6488a32eaad54fc39dff83f310dbaaed",
    1000000: "6aae55bea74235f0c80bd066349d4440c31f2d0f27d54265ecd484d8c1d11b47",
    2000000: "9914f0e82e39bbf21950792e8816620d71b9965bdbbc14e72a95e3ab9618fea8",
    3000000: "195a83b091fb3ee7ecb56f2e63d01709293f57f971ccf373d93890c8dc1033db",
}


def dsha(b):
    return hashlib.sha256(hashlib.sha256(b).digest()).digest()


class R:
    def __init__(self, b):
        self.b, self.i = b, 0

    def take(self, n):
        if self.i + n > len(self.b):
            raise ValueError("truncated")
        out = self.b[self.i:self.i + n]
        self.i += n
        return out

    def u8(self):
        return self.take(1)[0]

    def u32(self):
        return int.from_bytes(self.take(4), "little")

    def i32(self):
        return int.from_bytes(self.take(4), "little", signed=True)

    def cs(self):
        f = self.u8()
        if f < 253:
            n = f
        elif f == 253:
            n = int.from_bytes(self.take(2), "little")
            assert n >= 253
        elif f == 254:
            n = int.from_bytes(self.take(4), "little")
            assert n >= 0x10000
        else:
            n = int.from_bytes(self.take(8), "little")
            assert n >= 0x100000000
        assert n <= 0x02000000
        return n


def read_tx(r):
    """Core's UnserializeTransaction with witness allowed (D4, lines 210 to 243).

    Returns (raw bytes, base bytes). The base bytes are what Core's base-mode writer emits.
    """
    start = r.i
    version = r.take(4)
    flags = 0
    vin_start = r.i
    nin = r.cs()
    if nin == 0:
        flags = r.u8()
        if flags == 0:
            # Zero flags: no inputs and no outputs, and no output count to read (lines 222 to 226).
            lock = r.take(4)
            return r.b[start:r.i], version + bytes([0x00, 0x00]) + lock
        vin_start = r.i
        nin = r.cs()
    for _ in range(nin):
        r.take(36)
        r.take(r.cs())
        r.take(4)
    nout = r.cs()
    for _ in range(nout):
        r.take(8)
        r.take(r.cs())
    lists_end = r.i
    if flags & 1:
        for _ in range(nin):
            for _ in range(r.cs()):
                r.take(r.cs())
        flags ^= 1
    assert flags == 0
    lock = r.take(4)
    raw = r.b[start:r.i]
    base = version + r.b[vin_start:lists_end] + lock
    return raw, base


def self_test():
    """Hand-written transactions from Core's format, each followed by one extra byte that must remain."""
    one_input = bytes([0x01]) + bytes(36) + bytes([0x00, 0xFF, 0xFF, 0xFF, 0xFF])
    cases = [
        # Empty input list, flags 00: Core reads the lock time next.
        (bytes.fromhex("01000000" "00" "00" "0d000000"), bytes.fromhex("01000000" "0000" "0d000000")),
        # One input, no outputs, base form.
        (bytes.fromhex("01000000") + one_input + b"\x00" + bytes(4),
         bytes.fromhex("01000000") + one_input + b"\x00" + bytes(4)),
        # The same transaction in the extended form with one empty stack.
        (bytes.fromhex("01000000" "0001") + one_input + b"\x00" + b"\x00" + bytes(4),
         bytes.fromhex("01000000") + one_input + b"\x00" + bytes(4)),
    ]
    for raw, base in cases:
        r = R(raw + b"\xaa")
        got_raw, got_base = read_tx(r)
        assert got_raw == raw and got_base == base and r.b[r.i:] == b"\xaa", raw.hex()


def merkle_root(ids):
    level = list(ids)
    if not level:
        return bytes(32)
    while len(level) > 1:
        if len(level) % 2:
            level.append(level[-1])
        level = [dsha(level[k] + level[k + 1]) for k in range(0, len(level), 2)]
    return level[0]


def main(fetch_dir, out_path):
    self_test()
    rows = []
    for height, block_hash in sorted(CHECKPOINTS.items()):
        data = json.load(open(f"{fetch_dir}/{height}.json"))["data"][block_hash]
        raw = bytes.fromhex(data["raw_block"])
        dec = data["decoded_raw_block"]
        assert dsha(raw[:80])[::-1].hex() == block_hash, height
        assert dec["hash"] == block_hash and dec["height"] == height
        version = int.from_bytes(raw[:4], "little")
        flag = bool(version & 0x100)
        r = R(raw)
        r.take(80)
        payload = None
        if flag:
            tx_raw, tx_base = read_tx(r)
            hash_block = r.take(32)
            mb = [r.take(32) for _ in range(r.cs())]
            index = r.i32()
            cmb = [r.take(32) for _ in range(r.cs())]
            chain_index = r.i32()
            parent = r.take(80)
            a = dec["auxpow"]
            assert a["tx"]["hex"] == tx_raw.hex()
            assert a["tx"]["txid"] == dsha(tx_base)[::-1].hex()
            assert a["tx"]["blockhash"] == dsha(parent)[::-1].hex()
            assert a["merklebranch"] == [h[::-1].hex() for h in mb]
            assert a["chainmerklebranch"] == [h[::-1].hex() for h in cmb]
            assert a["index"] == index and a["chainindex"] == chain_index
            assert a["parentblock"] == parent.hex()
            payload = {
                "txHex": tx_raw.hex(),
                "txid": dsha(tx_base)[::-1].hex(),
                "hashBlock": hash_block.hex(),
                "merkleBranch": [h.hex() for h in mb],
                "index": index,
                "chainMerkleBranch": [h.hex() for h in cmb],
                "chainIndex": chain_index,
                "parentBlock": parent.hex(),
            }
        header_len = r.i
        ntx = r.cs()
        ids = []
        for _ in range(ntx):
            _, base = read_tx(r)
            ids.append(dsha(base))
        assert r.i == len(raw), "trailing bytes after the block"
        assert [i[::-1].hex() for i in ids] == dec["tx"]
        assert merkle_root(ids) == raw[36:68], "merkle root"
        rows.append({
            "height": height,
            "blockHash": block_hash,
            "auxpowFlag": flag,
            "headerLength": header_len,
            "txCount": ntx,
            "block": raw.hex(),
            "payload": payload,
        })
        print(height, len(raw), header_len, ntx, flag)
    with open(out_path, "w") as f:
        json.dump(rows, f, indent=2)
        f.write("\n")


if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
        print("self-test passed")
    else:
        main(sys.argv[1], sys.argv[2])
