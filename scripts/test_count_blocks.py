#!/usr/bin/env python3
"""Tests of scripts/count_blocks.py on synthetic blocks, without a network.

Usage: python3 -I scripts/test_count_blocks.py

Each expected count below is derived by hand from the blocks that the test builds, not from the
script under test.
"""

import hashlib
import io
import json
import pathlib
import sys
import tempfile
import unittest
from contextlib import redirect_stdout

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import count_blocks as cb  # noqa: E402
import fetch_blocks as fb  # noqa: E402
from test_fetch_blocks import auxpow_payload, genesis_block, header, u32  # noqa: E402


def compact(n: int) -> bytes:
    if n < 253:
        return bytes([n])
    if n <= 0xFFFF:
        return b"\xfd" + n.to_bytes(2, "little")
    return b"\xfe" + n.to_bytes(4, "little")


def tx(prevouts: list[tuple[bytes, int]], scripts: list[bytes], lock: int = 0, witness: bool = False):
    """A transaction with the given outpoints and output scripts, and its ID."""
    ins = compact(len(prevouts)) + b"".join(txid + u32(n) + b"\x00" + u32(0xFFFFFFFF) for txid, n in prevouts)
    outs = compact(len(scripts)) + b"".join(u32(1000) + u32(0) + compact(len(s)) + s for s in scripts)
    base = u32(1) + ins + outs + u32(lock)
    raw = base
    if witness:
        stacks = b"".join(b"\x01\x02\xaa\xbb" for _ in prevouts)
        raw = u32(1) + b"\x00\x01" + ins + outs + stacks + u32(lock)
    return raw, fb.sha256d(base)


def coinbase(tag: int, scripts: list[bytes]):
    return tx([(bytes(32), 0xFFFFFFFF)], scripts, lock=tag)


def block(txs, auxpow: bool = False) -> bytes:
    version = 0x00620104 if auxpow else 0x00620004
    head = header(version, b"\x11" * 32, b"\x22" * 32, 1700000000, 0x1A01CD2D, 0)
    return head + (auxpow_payload() if auxpow else b"") + compact(len(txs)) + b"".join(raw for raw, _ in txs)


def write_fixture(directory: pathlib.Path, blocks: list[tuple[int, bytes]]) -> pathlib.Path:
    directory.mkdir(parents=True)
    data = b"".join(h.to_bytes(4, "little") + len(raw).to_bytes(4, "little") + raw for h, raw in blocks)
    (directory / "blocks.bin").write_bytes(data)
    (directory / "manifest.json").write_text("{}\n")
    sums = "".join(f"{hashlib.sha256((directory / n).read_bytes()).hexdigest()}  {n}\n"
                   for n in ("blocks.bin", "manifest.json"))
    (directory / "SHA256SUMS").write_text(sums)
    return directory


P2PKH = b"\x76\xa9\x14" + b"\x01" * 20 + b"\x88\xac"  # 25 bytes
P2PK = b"\x21" + b"\x02" * 33 + b"\xac"  # 35 bytes
WIDE = b"\x51" * 40  # 40 bytes, spendable
NULL_DATA = b"\x6a\x04data"  # OP_RETURN
OVERSIZE = b"\x51" * 10001  # above MAX_SCRIPT_SIZE
EXTERNAL = b"\xee" * 32


def chain():
    """Heights 0 to 2. The comments give the counts of each block."""
    cb1 = coinbase(1, [P2PKH, NULL_DATA])  # 2 outputs, 1 enters the set
    a = tx([(EXTERNAL, 0), (EXTERNAL, 1)], [P2PKH, WIDE, P2PKH])  # 2 external inputs, 3 outputs
    b = tx([(a[1], 1)], [P2PKH])  # 1 internal input, in the block of its funding transaction
    cb2 = coinbase(2, [P2PK])
    c = tx([(a[1], 0), (b[1], 0)], [OVERSIZE], witness=True)  # 2 internal inputs, 0 outputs enter
    return [(0, genesis_block()), (1, block([cb1, a, b])), (2, block([cb2, c], auxpow=True))], dict(
        cb1=cb1, a=a, b=b, cb2=cb2, c=c)


class Counts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = pathlib.Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def test_counts_and_coin_set(self):
        blocks, _ = chain()
        fixture = write_fixture(self.dir / "f", blocks)
        result = cb.count([str(fixture)], coin_set=True)
        expected = dict(
            blocks=3, bytes=sum(len(raw) for _, raw in blocks), transactions=6, inputs=5,
            inputs_internal=3, inputs_external=2, max_inputs=2, outputs=9,
            # Not the genesis output, the OP_RETURN output or the oversized script.
            outputs_entering_set=6, external_txids=1)
        for key, value in expected.items():
            self.assertEqual(result[key], value, key)
        # Left: cb1:0 (25 bytes), a:2 (25 bytes, after two spent slots), cb2:0 (35 bytes).
        self.assertEqual(result["coin_set"], dict(height=2, txouts=3, transactions=3, slots=5,
                                                  scripts_over_28_bytes=1, script_bytes=85,
                                                  replaced_txids=0))

    def test_two_fixtures_and_last(self):
        blocks, _ = chain()
        first = write_fixture(self.dir / "f1", blocks[:2])
        second = write_fixture(self.dir / "f2", blocks[2:])
        self.assertEqual(cb.count([str(first), str(second)], coin_set=True),
                         cb.count([str(write_fixture(self.dir / "all", blocks))], coin_set=True))
        stopped = cb.count([str(first), str(second)], coin_set=True, last=1)
        # After height 1: cb1:0, a:0, a:2 and b:0. b spent a:1.
        self.assertEqual((stopped["blocks"], stopped["inputs"], stopped["coin_set"]["txouts"]), (2, 3, 4))

    def test_replaced_coinbase(self):
        blocks, txs = chain()
        blocks.append((3, block([txs["cb1"]])))  # the ID of cb1, whose output 0 is unspent
        result = cb.count([str(write_fixture(self.dir / "f", blocks))], coin_set=True)
        self.assertEqual(result["coin_set"]["replaced_txids"], 1)
        self.assertEqual(result["coin_set"]["txouts"], 3)

    def test_range_above_zero(self):
        blocks, _ = chain()
        result = cb.count([str(write_fixture(self.dir / "f", blocks[2:]))])
        # c spends a:0 and b:0, which the range does not create.
        self.assertEqual((result["inputs_internal"], result["inputs_external"], result["external_txids"]), (0, 2, 2))
        self.assertEqual(result["outputs_entering_set"], 1)
        with self.assertRaisesRegex(fb.FetchError, "starts at height 0"):
            cb.count([str(self.dir / "f")], coin_set=True)

    def test_gap_and_changed_file(self):
        blocks, _ = chain()
        gap = write_fixture(self.dir / "gap", [blocks[0], blocks[2]])
        with self.assertRaisesRegex(fb.FetchError, "consecutive"):
            cb.count([str(gap)], coin_set=True)
        changed = write_fixture(self.dir / "changed", blocks)
        data = bytearray((changed / "blocks.bin").read_bytes())
        data[-1] ^= 1
        (changed / "blocks.bin").write_bytes(bytes(data))
        with self.assertRaisesRegex(fb.FetchError, "SHA256SUMS mismatch"):
            cb.count([str(changed)])

    def test_trailing_bytes(self):
        blocks, _ = chain()
        fixture = write_fixture(self.dir / "f", [(1, blocks[1][1] + b"\x00")])
        with self.assertRaisesRegex(fb.FetchError, "trailing"):
            cb.count([str(fixture)])


class Sample(unittest.TestCase):
    def test_heights(self):
        heights = cb.sample_heights(2500, 1000, 7)
        self.assertEqual(len(heights), 3)
        self.assertEqual([h // 1000 for h in heights], [0, 1, 2])
        self.assertEqual(heights, cb.sample_heights(2500, 1000, 7))
        self.assertLessEqual(heights[-1], 2500)

    def test_estimate(self):
        _, txs = chain()
        one = block([txs["cb1"]])  # 1 transaction, 0 inputs, 2 outputs
        three = block([txs["cb1"], txs["a"], txs["b"]])  # 3 transactions, 3 inputs, 6 outputs
        with tempfile.TemporaryDirectory() as tmp:
            # Heights 0 to 4 in strata of 2: {0, 1}, {2, 3}, {4}.
            fixture = write_fixture(pathlib.Path(tmp) / "s", [(1, one), (2, three), (4, three)])
            result = cb.estimate(str(fixture), last=4, stride=2)
            self.assertEqual(result["estimate"], dict(
                bytes=2 * len(one) + 2 * len(three) + len(three),
                transactions=2 + 6 + 3, inputs=0 + 6 + 3, outputs=4 + 12 + 6, outputs_entering_set=2 + 10 + 5))
            # One pair, strata 0 and 1; stratum 2 has no partner. Scaled by the stride 2.
            self.assertEqual(result["standard_error"]["transactions"], 4)
            self.assertEqual([band["transactions"] for band in result["bands"]], [11])
            with self.assertRaisesRegex(fb.FetchError, "2 of the 3 strata"):
                cb.estimate(str(write_fixture(pathlib.Path(tmp) / "t", [(1, one), (2, three)])), last=4, stride=2)

    def test_command_line(self):
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(cb.main(["--sample-heights", "--last", "2500", "--seed", "7"]), 0)
        self.assertEqual(out.getvalue().strip(), ",".join(map(str, cb.sample_heights(2500, 1000, 7))))


if __name__ == "__main__":
    unittest.main()
