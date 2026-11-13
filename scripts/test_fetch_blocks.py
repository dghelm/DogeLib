#!/usr/bin/env python3
"""Tests of scripts/fetch_blocks.py, without a node and without a network.

Usage: python3 -I scripts/test_fetch_blocks.py

The tests build the mainnet genesis block from its published fields, and
synthetic blocks at heights that no pinned source covers. A fake transport
serves them in the place of a Dogecoin Core node. Each planted fault must
fail with a message that names the fault.
"""

import base64
import datetime
import hashlib
import io
import json
import pathlib
import sys
import tempfile
import traceback
import unittest
import urllib.error

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks as fb  # noqa: E402

GENESIS_HASH = "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
# No pinned source of the repository covers a height from BASE.
BASE = 6000000
USER = "tester"
PASSWORD = "s3cret-Passw0rd-93b1"
TOKEN = base64.b64encode(f"{USER}:{PASSWORD}".encode()).decode()
REAL_PINS = fb.Pins.load()
NOW = datetime.datetime(2026, 11, 13, 12, 0, 0, tzinfo=datetime.timezone.utc)


def u32(value: int) -> bytes:
    return value.to_bytes(4, "little")


def var_bytes(data: bytes) -> bytes:
    assert len(data) < 253
    return bytes([len(data)]) + data


def header(version: int, previous: bytes, root: bytes, time: int, bits: int, nonce: int) -> bytes:
    return u32(version) + previous + root + u32(time) + u32(bits) + u32(nonce)


def genesis_block(nonce: int = 99943) -> bytes:
    """The mainnet genesis block, built from its fields."""
    script_sig = bytes.fromhex("04ffff001d0104") + var_bytes(b"Nintondo")
    script = var_bytes(bytes.fromhex(
        "040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b"
        "10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9"
    )) + b"\xac"
    coinbase = (
        u32(1) + b"\x01" + bytes(32) + u32(0xFFFFFFFF) + var_bytes(script_sig) + u32(0xFFFFFFFF)
        + b"\x01" + (88 * 10**8).to_bytes(8, "little") + var_bytes(script) + u32(0)
    )
    root = fb.sha256d(coinbase)
    return header(1, bytes(32), root, 1386325540, 0x1E0FFFF0, nonce) + b"\x01" + coinbase


def make_tx(tag: int, witness: bool = False) -> tuple[bytes, bytes]:
    """A synthetic transaction and its transaction ID.

    With `witness`, the bytes use the extended format, and the ID is still
    the hash of the base serialization.
    """
    inputs = b"\x01" + hashlib.sha256(u32(tag)).digest() + u32(tag % 3) + var_bytes(b"\x51" * (tag % 5)) + u32(0xFFFFFFFE)
    outputs = b"\x02" + (tag * 1000).to_bytes(8, "little") + var_bytes(b"\x76\xa9") + bytes(8) + var_bytes(b"")
    base = u32(2) + inputs + outputs + u32(tag)
    raw = base
    if witness:
        stack = b"\x02" + var_bytes(b"\xaa" * 7) + var_bytes(b"")
        raw = u32(2) + b"\x00\x01" + inputs + outputs + stack + u32(tag)
    return raw, fb.sha256d(base)


def auxpow_payload() -> bytes:
    """A payload with the layout of `CAuxPow`. Its content has no meaning."""
    return (
        make_tx(900)[0] + b"\x21" * 32
        + b"\x02" + b"\x31" * 32 + b"\x32" * 32 + u32(0)
        + b"\x01" + b"\x41" * 32 + u32(5)
        + header(2, b"\x51" * 32, b"\x52" * 32, 1400000000, 0x1B00FFFF, 7)
    )


def make_block(previous: bytes, txs: list[tuple[bytes, bytes]], auxpow: bool = False, nonce: int = 0) -> bytes:
    """A synthetic block. Its Merkle root comes from the given IDs."""
    root, _ = fb.merkle_root([txid for _, txid in txs])
    version = 0x00620104 if auxpow else 0x00620004
    head = header(version, previous, root, 1700000000 + nonce, 0x1A01CD2D, nonce)
    payload = auxpow_payload() if auxpow else b""
    return head + payload + bytes([len(txs)]) + b"".join(raw for raw, _ in txs)


def block_hash(raw: bytes) -> bytes:
    return fb.sha256d(raw[:80])


BEFORE_BASE = b"\x77" * 32


def make_chain(count: int, first: int = BASE, previous: bytes = BEFORE_BASE) -> dict[int, bytes]:
    """Linked synthetic blocks with 1 to 5 transactions each.

    The second block has an AuxPoW payload. The third block has a
    transaction in the extended format.
    """
    blocks = {}
    for index in range(count):
        txs = [make_tx(100 * index + k, witness=(index == 2 and k == 1)) for k in range(index % 5 + 1)]
        raw = make_block(previous, txs, auxpow=(index == 1), nonce=index)
        blocks[first + index] = raw
        previous = block_hash(raw)
    return blocks


class FakeNode:
    """A JSON-RPC transport that serves blocks from a table."""

    def __init__(self, blocks: dict[int, bytes], hashes: dict[int, bytes] | None = None):
        self.blocks = dict(blocks)
        # Hashes for heights without a block, and planted wrong hashes.
        self.hashes = {BASE - 1: BEFORE_BASE, **(hashes or {})}
        self.tip = max(blocks)
        self.requests = []
        self.error = None

    def hash_at(self, height: int) -> bytes:
        if height in self.hashes:
            return self.hashes[height]
        return block_hash(self.blocks[height])

    def transport(self, url: str, body: bytes, headers: dict[str, str]) -> bytes:
        self.requests.append((url, headers))
        if self.error is not None:
            raise self.error(url, headers)
        request = json.loads(body)
        method, params = request["method"], request["params"]
        if method == "getblockcount":
            result = self.tip
        elif method == "getblockhash":
            result = fb.display(self.hash_at(params[0]))
        elif method == "getblock":
            assert params[1] is False
            by_hash = {fb.display(self.hash_at(height)): raw for height, raw in self.blocks.items()}
            result = by_hash[params[0]].hex()
        elif method == "getnetworkinfo":
            result = {"version": 1140900, "subversion": "/Shibetoshi:1.14.9/"}
        else:
            raise AssertionError(method)
        return json.dumps({"result": result, "error": None, "id": request["id"]}).encode()

    def rpc(self) -> fb.Rpc:
        return fb.Rpc("http://node.invalid:22555", USER, PASSWORD, self.transport)


def write_sums(directory: pathlib.Path) -> None:
    """Write a `SHA256SUMS` that matches the two other files."""
    lines = [
        f"{hashlib.sha256((directory / name).read_bytes()).hexdigest()}  {name}\n"
        for name in (fb.BLOCKS_FILE, fb.MANIFEST_FILE)
    ]
    (directory / fb.SUMS_FILE).write_text("".join(lines))


class Case(unittest.TestCase):
    def setUp(self):
        self._directory = tempfile.TemporaryDirectory()
        self.addCleanup(self._directory.cleanup)
        self.dir = pathlib.Path(self._directory.name) / "fixture"

    def run_main(self, arguments, node=None, pins=REAL_PINS, env=None, password_file=None):
        out, err = io.StringIO(), io.StringIO()
        status = fb.main(
            arguments,
            env={fb.PASSWORD_VARIABLE: PASSWORD} if env is None else env,
            transport=node.transport if node else None,
            pins=pins,
            password_file=password_file or self.dir.parent / "absent.env",
            out=out,
            err=err,
        )
        return status, out.getvalue(), err.getvalue()

    def fetch(self, node, selection, pins=REAL_PINS):
        return fb.fetch(node.rpc(), selection, self.dir, pins, now=NOW)

    def fetch_range(self, node, pins=REAL_PINS):
        heights = sorted(node.blocks)
        return self.fetch(node, {"kind": "range", "first": heights[0], "last": heights[-1]}, pins)

    def assert_fetch_fails(self, node, pattern, pins=REAL_PINS):
        """The fetch of every block fails, and leaves no fixture file."""
        with self.assertRaisesRegex(fb.FetchError, pattern):
            self.fetch_range(node, pins)
        self.assertFalse(self.dir.exists() and list(self.dir.iterdir()))

    def manifest(self) -> dict:
        return json.loads((self.dir / fb.MANIFEST_FILE).read_text())


class PinnedSources(Case):
    def test_genesis_block_has_the_pinned_hash(self):
        block = fb.Block(genesis_block())
        self.assertEqual(fb.display(block.hash), GENESIS_HASH)
        sources = REAL_PINS.lookup(0)
        self.assertEqual(
            sorted(name for name, _ in sources),
            sorted([fb.PREV_HASHES, "tests/work/mainnet-genesis-headers", fb.CHECKPOINT_SOURCE]),
        )
        for _, pinned in sources:
            self.assertEqual(pinned, block.hash)
        self.assertEqual(REAL_PINS.prev_hashes[:32], block.hash)

    def test_sources_agree_where_they_overlap(self):
        seen = {}
        compared = 0
        for table in REAL_PINS.tables.values():
            for height, pinned in table.items():
                for _, other in REAL_PINS.lookup(height):
                    self.assertEqual(other, pinned, height)
                compared += height in seen or height < fb.PREV_HASHES_COUNT
                seen[height] = pinned
        # Heights 0 to 12 and 144719 to 144999 of the header fixtures, the
        # checkpoints 0 and 104679 below 145,000, and the checkpoints 145000
        # and 371337 inside two header fixtures.
        self.assertEqual(compared, 13 + 281 + 2 + 2)

    def test_heights_of_the_sources(self):
        self.assertEqual(len(REAL_PINS.prev_hashes), 32 * 145000)
        self.assertEqual(REAL_PINS.lookup(145000 - 1)[0][0], fb.PREV_HASHES)
        names = lambda height: [name for name, _ in REAL_PINS.lookup(height)]
        self.assertEqual(names(145000), ["tests/work/mainnet-headers", fb.CHECKPOINT_SOURCE])
        self.assertEqual(names(145001), ["tests/work/mainnet-headers"])
        self.assertEqual(names(371336), ["tests/block/mainnet-auxpow-activation-headers"])
        self.assertEqual(names(1034383), ["tests/block/mainnet-bip66-headers"])
        self.assertEqual(names(3464751), ["tests/block/mainnet-bip65-headers"])
        for height in (599999, 600000, 600001, 10001 + 145030, BASE):
            self.assertEqual(names(height), [])
        self.assertEqual(len(fb.CHECKPOINTS), 23)


class GoodFetches(Case):
    def test_genesis_is_pinned(self):
        node = FakeNode({0: genesis_block()})
        status, out, err = self.run_main(["--range", "0", "0", "--output", str(self.dir)], node)
        self.assertEqual((status, err), (0, ""))
        self.assertIn("pinned: 1, linked: 0", out)
        manifest = self.manifest()
        self.assertEqual(manifest["blocks"], [
            {"height": 0, "hash": GENESIS_HASH, "size": 224, "transactions": 1, "auth": "pinned"}
        ])
        self.assertEqual(manifest["runs"], [{"first": 0, "last": 0, "previous": "genesis"}])
        self.assertEqual(sorted(manifest["pinned_by"]), sorted(
            [fb.PREV_HASHES, "tests/work/mainnet-genesis-headers", fb.CHECKPOINT_SOURCE]))
        self.assertEqual(self.run_main(["--check", str(self.dir)])[0], 0)

    def test_range_of_linked_blocks(self):
        blocks = make_chain(7)
        node = FakeNode(blocks)
        status, out, err = self.run_main(
            ["--range", str(BASE), str(BASE + 6), "--output", str(self.dir)], node)
        self.assertEqual((status, err), (0, ""))
        total = sum(len(raw) for raw in blocks.values())
        largest = max(blocks, key=lambda height: len(blocks[height]))
        self.assertIn(f"blocks: 7, bytes: {total}\n", out)
        self.assertIn(f"largest block: {len(blocks[largest])} bytes at height {largest}\n", out)
        self.assertIn("blocks with an AuxPoW payload: 1\n", out)
        self.assertIn("pinned: 0, linked: 7\n", out)

        self.assertEqual(sorted(p.name for p in self.dir.iterdir()), ["SHA256SUMS", "blocks.bin", "manifest.json"])
        self.assertEqual(dict(fb.read_blocks(self.dir / "blocks.bin")), blocks)
        expected = b"".join(u32(h) + u32(len(raw)) + raw for h, raw in blocks.items())
        self.assertEqual((self.dir / "blocks.bin").read_bytes(), expected)
        manifest = self.manifest()
        self.assertEqual(manifest["format"], "dogelib-blocks/1")
        self.assertEqual((manifest["selection"], manifest["first"], manifest["last"]), ("range", BASE, BASE + 6))
        self.assertEqual((manifest["count"], manifest["bytes"]), (7, total))
        self.assertEqual(manifest["node_version"], "/Shibetoshi:1.14.9/ (1140900)")
        self.assertRegex(manifest["fetch_date"], r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$")
        self.assertEqual(manifest["tip_height"], BASE + 6)
        self.assertEqual(manifest["tip_hash"], fb.display(block_hash(blocks[BASE + 6])))
        self.assertEqual(manifest["runs"], [{"first": BASE, "last": BASE + 6, "previous": "node"}])
        self.assertEqual(manifest["pinned_by"], {})
        self.assertEqual(
            [b["transactions"] for b in manifest["blocks"]], [1, 2, 3, 4, 5, 1, 2])
        for record in manifest["blocks"]:
            raw = blocks[record["height"]]
            self.assertEqual(record["hash"], fb.display(block_hash(raw)))
            self.assertEqual((record["size"], record["auth"]), (len(raw), "linked"))
        sums = (self.dir / "SHA256SUMS").read_text().splitlines()
        self.assertEqual(sums, [
            f"{hashlib.sha256((self.dir / name).read_bytes()).hexdigest()}  {name}"
            for name in ("blocks.bin", "manifest.json")
        ])

        status, out, err = self.run_main(["--check", str(self.dir)])
        self.assertEqual((status, err), (0, ""))
        self.assertIn("pinned: 0, linked: 7\n", out)

    def test_pinned_blocks_and_pinned_previous_hash(self):
        blocks = make_chain(4)
        pins = fb.Pins(tables={"test-pins": {
            BASE - 1: BEFORE_BASE, BASE + 1: block_hash(blocks[BASE + 1]), BASE + 2: block_hash(blocks[BASE + 2]),
        }})
        # The node's hash for BASE - 1 is wrong. The pinned value replaces it.
        node = FakeNode(blocks, {BASE - 1: b"\x00" * 32})
        self.fetch_range(node, pins)
        manifest = self.manifest()
        self.assertEqual([b["auth"] for b in manifest["blocks"]], ["linked", "pinned", "pinned", "linked"])
        self.assertEqual(manifest["pinned_by"], {"test-pins": [[BASE + 1, BASE + 2]]})
        self.assertEqual(manifest["runs"], [{"first": BASE, "last": BASE + 3, "previous": "pinned"}])
        fb.check_fixture(self.dir, pins)
        # With other pinned values, the manifest no longer matches.
        with self.assertRaisesRegex(fb.FetchError, "'runs' does not match"):
            fb.check_fixture(self.dir, REAL_PINS)

    def test_recent_stops_below_the_tip(self):
        blocks = make_chain(70)
        node = FakeNode(blocks)
        status, out, err = self.run_main(["--recent", "5", "--output", str(self.dir)], node)
        self.assertEqual((status, err), (0, ""))
        manifest = self.manifest()
        self.assertEqual(
            (manifest["selection"], manifest["first"], manifest["last"], manifest["confirmations"]),
            ("recent", BASE + 5, BASE + 9, 60))
        self.assertEqual(manifest["tip_height"], BASE + 69)
        self.assertEqual([b["height"] for b in manifest["blocks"]], list(range(BASE + 5, BASE + 10)))
        self.assertEqual(self.run_main(["--check", str(self.dir)])[0], 0)

        status, _, _ = self.run_main(
            ["--recent", "3", "--confirmations", "2", "--output", str(self.dir)], node)
        self.assertEqual(status, 0)
        self.assertEqual([b["height"] for b in self.manifest()["blocks"]], [BASE + 65, BASE + 66, BASE + 67])

    def test_height_list_with_gaps(self):
        blocks = make_chain(9)
        node = FakeNode(blocks)
        listed = f"{BASE + 7},{BASE + 1},{BASE + 2},{BASE + 5}"
        status, _, err = self.run_main(["--heights", listed, "--output", str(self.dir)], node)
        self.assertEqual((status, err), (0, ""))
        manifest = self.manifest()
        self.assertEqual(manifest["selection"], "heights")
        self.assertEqual(manifest["heights"], [BASE + 1, BASE + 2, BASE + 5, BASE + 7])
        self.assertEqual(manifest["runs"], [
            {"first": BASE + 1, "last": BASE + 2, "previous": "node"},
            {"first": BASE + 5, "last": BASE + 5, "previous": "node"},
            {"first": BASE + 7, "last": BASE + 7, "previous": "node"},
        ])
        self.assertEqual(self.run_main(["--check", str(self.dir)])[0], 0)

    def test_height_above_the_tip(self):
        node = FakeNode(make_chain(3))
        status, _, err = self.run_main(
            ["--range", str(BASE), str(BASE + 3), "--output", str(self.dir)], node)
        self.assertEqual(status, 1)
        self.assertIn(f"height {BASE + 3} is above the node's tip {BASE + 2}", err)


class Parser(Case):
    def test_auxpow_block(self):
        txs = [make_tx(1), make_tx(2)]
        plain = fb.Block(make_block(BEFORE_BASE, txs))
        raw = make_block(BEFORE_BASE, txs, auxpow=True)
        block = fb.Block(raw)
        self.assertTrue(block.auxpow)
        self.assertFalse(plain.auxpow)
        self.assertEqual(block.txids, [txid for _, txid in txs])
        self.assertEqual(block.size, plain.size + len(auxpow_payload()))
        self.assertEqual(block.hash, block_hash(raw))
        # Without the flag, the parser reads the payload as transactions.
        unflagged = bytearray(raw)
        unflagged[1] = 0
        with self.assertRaises(fb.FetchError):
            fb.Block(bytes(unflagged))

    def test_witness_transaction_id_excludes_the_witness(self):
        plain, txid = make_tx(7)
        extended, extended_txid = make_tx(7, witness=True)
        self.assertEqual(txid, extended_txid)
        self.assertEqual(txid, fb.sha256d(plain))
        self.assertNotEqual(plain, extended)
        self.assertEqual(extended[4:6], b"\x00\x01")
        reader = fb.Reader(extended)
        self.assertEqual(fb.read_transaction(reader), txid)
        self.assertEqual(reader.pos, len(extended))

        coinbase = make_tx(1)
        blocks = {BASE: make_block(BEFORE_BASE, [coinbase, (extended, txid)])}
        self.fetch_range(FakeNode(blocks))
        self.assertEqual(self.manifest()["blocks"][0]["transactions"], 2)

    def test_merkle_root_over_witness_bytes_fails(self):
        coinbase = make_tx(1)
        extended, _ = make_tx(7, witness=True)
        blocks = {BASE: make_block(BEFORE_BASE, [coinbase, (extended, fb.sha256d(extended))])}
        self.assert_fetch_fails(FakeNode(blocks), "Merkle root mismatch")

    def test_empty_transaction_and_unknown_flags(self):
        empty = u32(1) + b"\x00\x00" + u32(0)
        reader = fb.Reader(empty)
        self.assertEqual(fb.read_transaction(reader), fb.sha256d(empty))
        self.assertEqual(reader.pos, len(empty))
        raw, _ = make_tx(7, witness=True)
        with self.assertRaisesRegex(fb.FetchError, "unknown transaction flags"):
            fb.read_transaction(fb.Reader(raw[:5] + b"\x03" + raw[6:]))

    def test_compact_size(self):
        self.assertEqual(fb.Reader(b"\xfc").compact_size(), 252)
        self.assertEqual(fb.Reader(b"\xfd\xfd\x00").compact_size(), 253)
        self.assertEqual(fb.Reader(b"\xfe\x00\x00\x01\x00").compact_size(), 0x10000)
        self.assertEqual(fb.Reader(b"\xfe\x00\x00\x00\x02").compact_size(), 0x02000000)
        for data in (b"\xfd\xfc\x00", b"\xfe\xff\xff\x00\x00", b"\xff" + b"\xff" * 4 + bytes(4)):
            with self.assertRaisesRegex(fb.FetchError, "non-canonical CompactSize"):
                fb.Reader(data).compact_size()
        with self.assertRaisesRegex(fb.FetchError, "CompactSize above"):
            fb.Reader(b"\xfe\x01\x00\x00\x02").compact_size()
        with self.assertRaisesRegex(fb.FetchError, "truncated"):
            fb.Reader(b"\xfd\x00").compact_size()

    def test_merkle_root(self):
        a, b, c = (bytes([value]) * 32 for value in (1, 2, 3))
        h = fb.sha256d
        self.assertEqual(fb.merkle_root([a]), (a, False))
        self.assertEqual(fb.merkle_root([a, b]), (h(a + b), False))
        self.assertEqual(fb.merkle_root([a, b, c]), (h(h(a + b) + h(c + c)), False))
        self.assertEqual(fb.merkle_root([a, b, c, c]), (h(h(a + b) + h(c + c)), True))
        self.assertEqual(fb.merkle_root([a, a]), (h(a + a), True))
        # Two equal hashes in different pairs are not the duplication.
        self.assertFalse(fb.merkle_root([a, b, b, c])[1])
        # The duplication above the leaves: six leaves repeat their last two.
        d, e, f = (bytes([value]) * 32 for value in (4, 5, 6))
        six, eight = fb.merkle_root([a, b, c, d, e, f]), fb.merkle_root([a, b, c, d, e, f, e, f])
        self.assertEqual((six[0], six[1], eight[1]), (eight[0], False, True))


class PlantedFaults(Case):
    def setUp(self):
        super().setUp()
        self.blocks = make_chain(5)

    def test_wrong_hash_from_getblockhash(self):
        wrong = bytearray(block_hash(self.blocks[BASE + 2]))
        wrong[0] ^= 1
        node = FakeNode(self.blocks, {BASE + 2: bytes(wrong)})
        self.assert_fetch_fails(
            node, f"height {BASE + 2}: the header hash .* is not the hash .* from getblockhash")

    def test_changed_transaction_byte(self):
        raw = bytearray(self.blocks[BASE + 3])
        raw[-10] ^= 0x40
        self.blocks[BASE + 3] = bytes(raw)
        self.assert_fetch_fails(FakeNode(self.blocks), f"height {BASE + 3}: Merkle root mismatch")

    def test_duplicated_last_transaction(self):
        txs = [make_tx(1), make_tx(2), make_tx(3)]
        honest = make_block(block_hash(self.blocks[BASE + 3]), txs)
        last = txs[-1][0]
        forged = honest[:80] + b"\x04" + honest[81:] + last
        self.assertEqual(block_hash(forged), block_hash(honest))
        self.blocks[BASE + 4] = honest
        self.fetch_range(FakeNode(self.blocks))
        for path in self.dir.iterdir():
            path.unlink()
        self.blocks[BASE + 4] = forged
        self.assert_fetch_fails(FakeNode(self.blocks), rf"height {BASE + 4}: duplicated transactions .*CVE-2012-2459")

    def test_broken_link_inside_a_range(self):
        self.blocks[BASE + 2] = make_block(b"\x99" * 32, [make_tx(5)])
        self.assert_fetch_fails(
            FakeNode(self.blocks),
            f"height {BASE + 2}: broken link: .*the block at height {BASE + 1} has the hash",
        )

    def test_broken_link_to_the_node_hash_below_a_range(self):
        node = FakeNode(self.blocks, {BASE - 1: b"\x66" * 32})
        self.assert_fetch_fails(node, rf"height {BASE}: broken link: .*\(the node's getblockhash\)")

    def test_broken_link_to_a_pinned_hash_below_a_range(self):
        pins = fb.Pins(tables={"test-pins": {BASE - 1: b"\x66" * 32}})
        self.assert_fetch_fails(FakeNode(self.blocks), rf"height {BASE}: broken link: .*\(test-pins\)", pins)

    def test_genesis_with_another_hash(self):
        node = FakeNode({0: genesis_block(nonce=99944)})
        self.assert_fetch_fails(node, f"height 0: the hash .* is not the pinned hash {GENESIS_HASH} of ")
        status, _, err = self.run_main(["--range", "0", "0", "--output", str(self.dir)], node)
        self.assertEqual(status, 1)
        self.assertIn("is not the pinned hash", err)

    def test_genesis_with_a_previous_hash(self):
        raw = genesis_block()
        node = FakeNode({0: raw[:4] + b"\x01" * 32 + raw[36:]})
        self.assert_fetch_fails(node, "height 0: broken link: .*null hash of a genesis block", fb.Pins())

    def test_pinned_hash_mismatch(self):
        pins = fb.Pins(prev_hashes=bytes(32 * 3), tables={"test-pins": {BASE + 1: b"\x66" * 32}})
        self.assert_fetch_fails(
            FakeNode(self.blocks), f"height {BASE + 1}: the hash .* is not the pinned hash .* of test-pins", pins)
        blocks = make_chain(2, first=1, previous=bytes(32))
        self.assert_fetch_fails(
            FakeNode(blocks), f"height 1: the hash .* is not the pinned hash .* of {fb.PREV_HASHES}", pins)

    def test_trailing_bytes(self):
        self.blocks[BASE + 1] += b"\x00"
        self.assert_fetch_fails(
            FakeNode(self.blocks), f"height {BASE + 1}: 1 trailing bytes after the last transaction")

    def test_truncated_block(self):
        for cut in (3, 50, len(self.blocks[BASE + 4]) - 79):
            blocks = dict(self.blocks)
            blocks[BASE + 4] = blocks[BASE + 4][:-cut]
            self.assert_fetch_fails(FakeNode(blocks), f"height {BASE + 4}: truncated block")

    def test_block_without_transactions(self):
        raw = header(4, block_hash(self.blocks[BASE + 3]), bytes(32), 0, 0, 0) + b"\x00"
        self.blocks[BASE + 4] = raw
        self.assert_fetch_fails(FakeNode(self.blocks), f"height {BASE + 4}: the block has no transaction")

    def test_malformed_node_answers(self):
        node = FakeNode(self.blocks)
        honest = node.transport

        def replace(method, result):
            def transport(url, body, headers):
                request = json.loads(body)
                if request["method"] != method:
                    return honest(url, body, headers)
                return json.dumps({"result": result, "error": None, "id": request["id"]}).encode()
            return transport

        for method, result, pattern in (
            ("getblockcount", "12", "getblockcount: the result is not a height"),
            ("getblockhash", "zz" * 32, "getblockhash .*: the result is not a hash"),
            ("getblockhash", "ab", "getblockhash .*: the result is not a hash"),
            ("getblock", {"hash": "00"}, "getblock .*: the result is not hexadecimal"),
            ("getnetworkinfo", None, "getnetworkinfo: malformed result"),
        ):
            node.transport = replace(method, result)
            self.assert_fetch_fails(node, pattern)
        node.transport = lambda url, body, headers: b'{"result": 1, "error": null, "id": 999}'
        self.assert_fetch_fails(node, "getblockcount: malformed response")
        node.transport = lambda url, body, headers: b'{"result": null, "error": {"code": -8, "message": "Block height out of range"}, "id": 1}'
        self.assert_fetch_fails(node, "getblockcount: Block height out of range")


class CheckMode(Case):
    def setUp(self):
        super().setUp()
        self.blocks = make_chain(5)
        self.fetch_range(FakeNode(self.blocks))
        self.path = self.dir / fb.BLOCKS_FILE

    def assert_check_fails(self, pattern):
        with self.assertRaisesRegex(fb.FetchError, pattern):
            fb.check_fixture(self.dir, REAL_PINS)
        status, out, err = self.run_main(["--check", str(self.dir)])
        self.assertEqual((status, out), (1, ""))
        self.assertRegex(err, "^error: ")

    def offset(self, height: int) -> int:
        """The offset in `blocks.bin` of the record for `height`."""
        return sum(8 + len(raw) for h, raw in self.blocks.items() if h < height)

    def test_good_fixture(self):
        verifier = fb.check_fixture(self.dir, REAL_PINS)
        self.assertEqual(len(verifier.blocks), 5)

    def test_corrupted_blocks_file(self):
        data = bytearray(self.path.read_bytes())
        data[-10] ^= 1
        self.path.write_bytes(bytes(data))
        self.assert_check_fails("blocks.bin: SHA256SUMS mismatch")
        # The block checks still find the change behind a matching digest.
        write_sums(self.dir)
        self.assert_check_fails(f"height {BASE + 4}: Merkle root mismatch")

    def test_corrupted_header_behind_a_matching_digest(self):
        data = bytearray(self.path.read_bytes())
        data[self.offset(BASE + 2) + 8 + 70] ^= 1
        self.path.write_bytes(bytes(data))
        write_sums(self.dir)
        self.assert_check_fails(f"height {BASE + 3}: broken link")

    def test_corrupted_last_header_behind_a_matching_digest(self):
        data = bytearray(self.path.read_bytes())
        data[self.offset(BASE + 4) + 8 + 79] ^= 1
        self.path.write_bytes(bytes(data))
        write_sums(self.dir)
        self.assert_check_fails("'blocks' does not match the blocks .first at height 6000004")

    def test_wrong_sums(self):
        sums = self.dir / fb.SUMS_FILE
        original = sums.read_text()
        lines = original.splitlines()
        sums.write_text(f"{'0' * 64}  blocks.bin\n{lines[1]}\n")
        self.assert_check_fails("blocks.bin: SHA256SUMS mismatch")
        sums.write_text(f"{lines[0]}\n{'0' * 64}  manifest.json\n")
        self.assert_check_fails("manifest.json: SHA256SUMS mismatch")
        sums.write_text(lines[0] + "\n")
        self.assert_check_fails("SHA256SUMS: lists .'blocks.bin'., expected")
        sums.write_text(original + "garbage\n")
        self.assert_check_fails("SHA256SUMS: malformed line")
        sums.unlink()
        self.assert_check_fails("SHA256SUMS: cannot read")

    def test_truncated_blocks_file(self):
        data = self.path.read_bytes()
        self.path.write_bytes(data[:-5])
        write_sums(self.dir)
        self.assert_check_fails(f"truncated block at height {BASE + 4}")
        self.path.write_bytes(data[:self.offset(BASE + 4) + 3])
        write_sums(self.dir)
        self.assert_check_fails("truncated record header")

    def test_removed_and_reordered_records(self):
        data = self.path.read_bytes()
        cut, end = self.offset(BASE + 3), self.offset(BASE + 4)
        self.path.write_bytes(data[:cut] + data[end:])
        write_sums(self.dir)
        self.assert_check_fails("a range selection has a gap|does not match the blocks")
        self.path.write_bytes(data[:cut] + data[end:] + data[cut:end])
        write_sums(self.dir)
        self.assert_check_fails(f"height {BASE + 3}: the height does not follow height {BASE + 4}")

    def test_changed_height_field(self):
        data = bytearray(self.path.read_bytes())
        data[0:4] = u32(BASE - 1)
        self.path.write_bytes(bytes(data))
        write_sums(self.dir)
        self.assert_check_fails("does not match the blocks|has a gap")

    def test_changed_manifest(self):
        path = self.dir / fb.MANIFEST_FILE
        original = json.loads(path.read_text())
        changes = {
            "format": "dogelib-blocks/0",
            "selection": "all",
            "first": BASE + 1,
            "count": 6,
            "bytes": original["bytes"] + 1,
            "runs": [{"first": BASE, "last": BASE + 4, "previous": "pinned"}],
            "pinned_by": {"core-checkpoints": [[BASE, BASE]]},
        }
        for key, value in changes.items():
            path.write_text(json.dumps({**original, key: value}))
            write_sums(self.dir)
            with self.subTest(key=key):
                self.assert_check_fails("format is not|unknown selection|does not match the blocks")
        blocks = [dict(block) for block in original["blocks"]]
        blocks[1]["auth"] = "pinned"
        path.write_text(json.dumps({**original, "blocks": blocks}))
        write_sums(self.dir)
        self.assert_check_fails(f"'blocks' does not match the blocks .first at height {BASE + 1}")

    def test_pinned_genesis_fixture_with_another_block(self):
        for path in self.dir.iterdir():
            path.unlink()
        self.fetch_range(FakeNode({0: genesis_block()}))
        fb.check_fixture(self.dir, REAL_PINS)
        other = genesis_block(nonce=5)
        self.path.write_bytes(u32(0) + u32(len(other)) + other)
        write_sums(self.dir)
        self.assert_check_fails("height 0: the hash .* is not the pinned hash")


class Password(Case):
    def assert_no_secret(self, *texts):
        for text in texts:
            self.assertNotIn(PASSWORD, text)
            self.assertNotIn(TOKEN, text)

    def test_header_is_built_in_memory(self):
        node = FakeNode(make_chain(2))
        status, out, err = self.run_main(
            ["--range", str(BASE), str(BASE + 1), "--output", str(self.dir), "--user", USER], node)
        self.assertEqual(status, 0)
        self.assertTrue(node.requests)
        for url, headers in node.requests:
            self.assertEqual(headers["Authorization"], "Basic " + TOKEN)
            self.assertEqual(url, fb.DEFAULT_URL)
        self.assert_no_secret(out, err, *(path.read_text(errors="replace") for path in self.dir.iterdir()))

    def test_http_error_does_not_show_the_password(self):
        def http_error(url, headers):
            body = json.dumps({"error": {"message": f"denied for {USER}:{PASSWORD}, {headers}"}})
            return urllib.error.HTTPError(
                f"http://{USER}:{PASSWORD}@node.invalid/", 401,
                f"Unauthorized {PASSWORD} {headers['Authorization']}", headers, io.BytesIO(body.encode()))

        def url_error(url, headers):
            return urllib.error.URLError(f"refused {headers}")

        def os_error(url, headers):
            return OSError(f"socket failure with {headers} and {PASSWORD}")

        for make, expected in (
            (http_error, "getblockcount: HTTP status 401: denied for [redacted], "),
            (url_error, "getblockcount: request failed: URLError: refused {'Authorization': 'Basic [redacted]'"),
            (os_error, "getblockcount: request failed: OSError"),
        ):
            node = FakeNode(make_chain(2))
            node.error = make
            with self.subTest(make=make.__name__):
                with self.assertRaises(fb.FetchError) as caught:
                    node.rpc().block_count()
                error = caught.exception
                self.assertIn(expected, str(error))
                self.assertIsNone(error.__cause__)
                self.assertTrue(error.__suppress_context__)
                self.assert_no_secret(str(error), repr(error), "".join(traceback.format_exception(error)))

                status, out, err = self.run_main(
                    ["--range", str(BASE), str(BASE + 1), "--output", str(self.dir), "--user", USER], node)
                self.assertEqual(status, 1)
                self.assertIn(expected, err)
                self.assert_no_secret(out, err)
                self.assertFalse(self.dir.exists() and list(self.dir.iterdir()))

    def test_rpc_error_message_does_not_show_the_password(self):
        node = FakeNode(make_chain(2))
        node.transport = lambda url, body, headers: json.dumps(
            {"result": None, "error": {"code": -1, "message": f"echo {headers['Authorization']}"}, "id": 1}).encode()
        with self.assertRaises(fb.FetchError) as caught:
            node.rpc().block_count()
        self.assertEqual(str(caught.exception), "getblockcount: echo Basic [redacted]")

    def test_url_with_credentials_is_refused(self):
        for url in (f"http://{USER}:{PASSWORD}@node.invalid:22555", "ftp://node.invalid", "node.invalid:22555"):
            with self.assertRaises(fb.FetchError) as caught:
                fb.Rpc(url, USER, PASSWORD, None)
            self.assert_no_secret(str(caught.exception))

    def test_missing_password(self):
        node = FakeNode(make_chain(2))
        absent = self.dir.parent / "absent.env"
        empty = self.dir.parent / "empty.env"
        empty.write_text("# no password here\nOTHER=1\nDOGE_RPCPASSWORD=\n")
        for env, password_file in (({}, absent), ({fb.PASSWORD_VARIABLE: ""}, absent), ({}, empty)):
            status, out, err = self.run_main(
                ["--range", str(BASE), str(BASE + 1), "--output", str(self.dir)], node,
                env=env, password_file=password_file)
            self.assertEqual((status, out), (2, ""))
            self.assertIn("DOGE_RPCPASSWORD", err)
            self.assertIn(str(password_file), err)
            self.assertEqual(node.requests, [])
            self.assertFalse(self.dir.exists())
        self.assertEqual(str(fb.PASSWORD_FILE), "~/.config/dogelib/node-rpc.env")

    def test_password_file_forms(self):
        path = self.dir.parent / "node-rpc.env"
        for text in (
            f"DOGE_RPCPASSWORD={PASSWORD}\n",
            f"# comment\nDOGE_RPCUSER=x\nexport DOGE_RPCPASSWORD={PASSWORD}\n",
            f'DOGE_RPCPASSWORD="{PASSWORD}"\n',
            f"  export  DOGE_RPCPASSWORD='{PASSWORD}'  \r\n",
        ):
            path.write_text(text)
            self.assertEqual(fb.read_password({}, path), PASSWORD, text)
        path.write_text("DOGE_RPCPASSWORD=from-file\n")
        self.assertEqual(fb.read_password({fb.PASSWORD_VARIABLE: PASSWORD}, path), PASSWORD)
        node = FakeNode(make_chain(2))
        path.write_text(f"DOGE_RPCPASSWORD={PASSWORD}\n")
        status, out, err = self.run_main(
            ["--range", str(BASE), str(BASE + 1), "--output", str(self.dir), "--user", USER], node,
            env={}, password_file=path)
        self.assertEqual(status, 0)
        self.assertEqual(node.requests[0][1]["Authorization"], "Basic " + TOKEN)
        self.assert_no_secret(out, err)

    def test_check_needs_no_password(self):
        self.fetch_range(FakeNode(make_chain(2)))
        status, _, err = self.run_main(["--check", str(self.dir)], env={})
        self.assertEqual((status, err), (0, ""))


if __name__ == "__main__":
    unittest.main()
