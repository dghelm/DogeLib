#!/usr/bin/env python3
"""Fetch raw mainnet blocks from a Dogecoin Core node, and check them.

Usage:
  python3 -I scripts/fetch_blocks.py --range START END --output DIR
  python3 -I scripts/fetch_blocks.py --recent N [--confirmations M] --output DIR
  python3 -I scripts/fetch_blocks.py --heights H1,H2,... --output DIR
  python3 -I scripts/fetch_blocks.py --check DIR

The fetch modes read blocks over JSON-RPC with `getblockcount`,
`getblockhash`, `getblock <hash> false` and `getnetworkinfo`. The password
comes from the environment variable DOGE_RPCPASSWORD. If the variable is not
set, the script reads the line `DOGE_RPCPASSWORD=...` of the file
~/.config/dogelib/node-rpc.env. The script does not print the password.

The script checks every block before it writes the block:

1. The block parses exactly. It has an 80-byte header, then the AuxPoW
   payload when bit 8 of the version is set. A CompactSize count and that
   many transactions follow.
2. The double SHA-256 of the header is the hash that `getblockhash` returned.
3. The Merkle root of the transaction IDs is the Merkle root field of the
   header. No level of the tree has two equal hashes in one pair, which is
   the duplication of CVE-2012-2459.
4. The previous-hash field is the hash of the block at the previous height.
5. The hash equals each pinned value that the repository has for the height.

The pinned values of check 5 come from three kinds of source:

- `tests/block/mainnet-subsidy-prev-hashes/prev-hashes.bin`, heights 0 to
  144,999.
- The committed header fixtures that `HEADER_FIXTURES` lists.
- The mainnet checkpoints of Dogecoin Core, in `CHECKPOINTS`.

The manifest gives each block one of two labels in `auth`:

- `pinned`: the block hash equals a pinned value. With checks 1 and 3, the
  pinned value commits to every transaction ID of the block. That statement
  assumes that SHA-256 is collision resistant.
- `linked`: no pinned value covers the height. The block is consistent with
  its own header, and it links to the other fetched blocks of its run.
  Nothing connects it to a pinned hash, and this script does not check proof
  of work. So its bytes rest on the node. The Core comparison later checks
  the proof of work of each block.

A run is a sequence of consecutive heights. Check 4 compares the first block
of a run with a pinned hash of the height below it, when one exists. If none
exists, the fetch compares it with the node's own `getblockhash` answer, and
the manifest records `"previous": "node"`. That comparison shows only that
the node is consistent.

The transaction ID of check 3 excludes witness data. So the pinned value
does not commit to the witness stacks of a transaction in the extended
format. It also does not commit to the bytes of an AuxPoW payload.

Output in DIR:

- `blocks.bin`: for each block in height order, the height and the length
  as 4-byte little-endian integers, then the raw block.
- `manifest.json`: the format name, the selection, the node version, the
  fetch date, the tip, and one record for each block.
- `SHA256SUMS`: the SHA-256 of the two other files.

`--check DIR` reads a fixture without a network connection. It checks
`SHA256SUMS`, repeats checks 1 to 5, and compares the result with the
manifest. Check 2 then compares each hash with the manifest. Check 4 cannot
repeat a comparison that the manifest records as `"previous": "node"`.
"""

import argparse
import base64
import datetime
import hashlib
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FORMAT = "dogelib-blocks/1"
DEFAULT_URL = "http://dogecoin.public.dappnode:22555"
DEFAULT_USER = "dappnode"
PASSWORD_VARIABLE = "DOGE_RPCPASSWORD"
PASSWORD_FILE = Path("~/.config/dogelib/node-rpc.env")
DEFAULT_CONFIRMATIONS = 60
# Core's MAX_SIZE (src/serialize.h). ReadCompactSize rejects a larger value.
MAX_SIZE = 0x02000000
AUXPOW_FLAG = 0x100
BLOCKS_FILE, MANIFEST_FILE, SUMS_FILE = "blocks.bin", "manifest.json", "SHA256SUMS"

PREV_HASHES = "tests/block/mainnet-subsidy-prev-hashes"
PREV_HASHES_COUNT = 145000
# Each directory has `headers.txt`, with a height and an 80-byte header in
# hexadecimal on each line, and a `SHA256SUMS` file. The README of each
# directory gives its heights and its provenance.
HEADER_FIXTURES = (
    "tests/work/mainnet-genesis-headers",  # heights 0 to 12
    "tests/work/mainnet-headers",  # heights 144719 to 145030
    "tests/block/mainnet-auxpow-activation-headers",  # heights 371320 to 371340
    "tests/block/mainnet-bip66-headers",  # heights 1032483 to 1034390
    "tests/block/mainnet-bip65-headers",  # heights 3464739 to 3464760
)
CHECKPOINT_SOURCE = "core-checkpoints"
# The `checkpointData` of the main network, in display order. Source:
# Dogecoin Core v1.14.9, commit e0a1c157791544e818c901bd9341896965afbf9d,
# src/chainparams.cpp, lines 180 to 205 (SOURCES.md D9).
CHECKPOINTS = {
    0: "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691",
    104679: "35eb87ae90d44b98898fec8c39577b76cb1eb08e1261cfc10706c8ce9a1d01cf",
    145000: "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72",
    371337: "60323982f9c5ff1b5a954eac9dc1269352835f47c2c5222691d80f0d50dcf053",
    450000: "d279277f8f846a224d776450aa04da3cf978991a182c6f3075db4c48b173bbd7",
    771275: "1b7d789ed82cbdc640952e7e7a54966c6488a32eaad54fc39dff83f310dbaaed",
    1000000: "6aae55bea74235f0c80bd066349d4440c31f2d0f27d54265ecd484d8c1d11b47",
    1250000: "00c7a442055c1a990e11eea5371ca5c1c02a0677b33cc88ec728c45edc4ec060",
    1500000: "f1d32d6920de7b617d51e74bdf4e58adccaa582ffdc8657464454f16a952fca6",
    1750000: "5c8e7327984f0d6f59447d89d143e5f6eafc524c82ad95d176c5cec082ae2001",
    2000000: "9914f0e82e39bbf21950792e8816620d71b9965bdbbc14e72a95e3ab9618fea8",
    2031142: "893297d89afb7599a3c571ca31a3b80e8353f4cf39872400ad0f57d26c4c5d42",
    2250000: "0a87a8d4e40dca52763f93812a288741806380cd569537039ee927045c6bc338",
    2510150: "77e3f4a4bcb4a2c15e8015525e3d15b466f6c022f6ca82698f329edef7d9777e",
    2750000: "d4f8abb835930d3c4f92ca718aaa09bef545076bd872354e0b2b85deefacf2e3",
    3000000: "195a83b091fb3ee7ecb56f2e63d01709293f57f971ccf373d93890c8dc1033db",
    3250000: "7f3e28bf9e309c4b57a4b70aa64d3b2ea5250ae797af84976ddc420d49684034",
    3500000: "eaa303b93c1c64d2b3a2cdcf6ccf21b10cc36626965cc2619661e8e1879abdfb",
    3606083: "954c7c66dee51f0a3fb1edb26200b735f5275fe54d9505c76ebd2bcabac36f1e",
    3854173: "e4b4ecda4c022406c502a247c0525480268ce7abbbef632796e8ca1646425e75",
    3963597: "2b6927cfaa5e82353d45f02be8aadd3bfd165ece5ce24b9bfa4db20432befb5d",
    4303965: "ed7d266dcbd8bb8af80f9ccb8deb3e18f9cc3f6972912680feeb37b090f8cee0",
    5050000: "e7d4577405223918491477db725a393bcfc349d8ee63b0a4fde23cbfbfd81dea",
}


class FetchError(Exception):
    """A failed check, a failed request or a malformed fixture."""


class PasswordMissing(Exception):
    """Neither the environment variable nor the file gives a password."""


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def display(block_hash: bytes) -> str:
    """The hash in display order: the bytes reversed, in hexadecimal."""
    return block_hash[::-1].hex()


# Block parser


class Reader:
    """A cursor over the bytes of one block."""

    def __init__(self, data: bytes):
        self.data = data
        self.pos = 0

    def take(self, size: int) -> bytes:
        end = self.pos + size
        if end > len(self.data):
            raise FetchError(
                f"truncated block: a field of {size} bytes at offset {self.pos} "
                f"passes the end at {len(self.data)}"
            )
        value = self.data[self.pos:end]
        self.pos = end
        return value

    def compact_size(self) -> int:
        """A CompactSize in its shortest form, at most MAX_SIZE, as in Core."""
        offset = self.pos
        tag = self.take(1)[0]
        if tag < 253:
            return tag
        width, least = {253: (2, 253), 254: (4, 0x10000), 255: (8, 0x100000000)}[tag]
        value = int.from_bytes(self.take(width), "little")
        if value < least:
            raise FetchError(f"non-canonical CompactSize at offset {offset}")
        if value > MAX_SIZE:
            raise FetchError(f"CompactSize above {MAX_SIZE} at offset {offset}")
        return value

    def hashes(self) -> None:
        """Skip a counted vector of 32-byte hashes."""
        for _ in range(self.compact_size()):
            self.take(32)


def read_transaction(reader: Reader) -> bytes:
    """Read one transaction, and return its transaction ID.

    The steps follow Core's `UnserializeTransaction` with witness data
    allowed (src/primitives/transaction.h, lines 211 to 243). The ID is the
    double SHA-256 of the base serialization. That serialization has the
    version, the inputs, the outputs and the lock time. It omits the marker,
    the flags and the witness stacks.
    """
    version = reader.take(4)
    body_start = reader.pos
    inputs = reader.compact_size()
    flags = 0
    if inputs == 0:
        flags = reader.take(1)[0]
        if flags != 0:
            body_start = reader.pos
            inputs = reader.compact_size()
    if inputs != 0 or flags != 0:
        for _ in range(inputs):
            reader.take(36)
            reader.take(reader.compact_size())
            reader.take(4)
        for _ in range(reader.compact_size()):
            reader.take(8)
            reader.take(reader.compact_size())
    # With no input and flags 0, the two bytes read are the two empty counts.
    body = reader.data[body_start:reader.pos]
    if flags & 1:
        flags ^= 1
        for _ in range(inputs):
            for _ in range(reader.compact_size()):
                reader.take(reader.compact_size())
    if flags:
        raise FetchError(f"unknown transaction flags before offset {reader.pos}")
    lock_time = reader.take(4)
    return sha256d(version + body + lock_time)


def merkle_root(hashes: list[bytes]) -> tuple[bytes, bool]:
    """The Merkle root, and whether a level has two equal hashes in one pair.

    The last hash of an odd level is paired with itself, as in Core's
    `ComputeMerkleRoot` (src/consensus/merkle.cpp). The second result is
    Core's `mutated` flag for CVE-2012-2459.
    """
    if not hashes:
        return bytes(32), False
    mutated = False
    level = list(hashes)
    while len(level) > 1:
        for i in range(0, len(level) - 1, 2):
            if level[i] == level[i + 1]:
                mutated = True
        if len(level) % 2:
            level.append(level[-1])
        level = [sha256d(level[i] + level[i + 1]) for i in range(0, len(level), 2)]
    return level[0], mutated


class Block:
    """The parts of one parsed block that the checks read."""

    def __init__(self, raw: bytes):
        reader = Reader(raw)
        header = reader.take(80)
        self.size = len(raw)
        self.hash = sha256d(header)
        self.previous = header[4:36]
        self.merkle_root = header[36:68]
        self.auxpow = bool(int.from_bytes(header[:4], "little") & AUXPOW_FLAG)
        if self.auxpow:
            # CAuxPow (src/auxpow.h): the coinbase transaction, the block
            # hash, the coinbase branch and its index, the chain branch and
            # its index, and the parent header.
            read_transaction(reader)
            reader.take(32)
            reader.hashes()
            reader.take(4)
            reader.hashes()
            reader.take(4)
            reader.take(80)
        self.txids = [read_transaction(reader) for _ in range(reader.compact_size())]
        if reader.pos != len(raw):
            raise FetchError(
                f"{len(raw) - reader.pos} trailing bytes after the last transaction"
            )


# Pinned hashes


def check_sums(directory: Path, names: tuple[str, ...]) -> None:
    """Check that `SHA256SUMS` lists exactly `names`, with the right hashes."""
    try:
        lines = (directory / SUMS_FILE).read_text().splitlines()
    except (OSError, UnicodeDecodeError) as error:
        raise FetchError(f"{directory / SUMS_FILE}: cannot read: {type(error).__name__}") from None
    listed = {}
    for line in lines:
        digest, separator, name = line.partition("  ")
        if not separator or name in listed:
            raise FetchError(f"{directory / SUMS_FILE}: malformed line {line!r}")
        listed[name] = digest
    if sorted(listed) != sorted(names):
        raise FetchError(f"{directory / SUMS_FILE}: lists {sorted(listed)}, expected {sorted(names)}")
    for name in names:
        actual = hashlib.sha256()
        try:
            with open(directory / name, "rb") as stream:
                for chunk in iter(lambda: stream.read(1 << 20), b""):
                    actual.update(chunk)
        except OSError as error:
            raise FetchError(f"{directory / name}: cannot read: {type(error).__name__}") from None
        if actual.hexdigest() != listed[name]:
            raise FetchError(f"{directory / name}: SHA256SUMS mismatch")


class Pins:
    """The pinned block hashes, by height.

    `prev_hashes` holds 32-byte records: record `k` is the hash of the block
    at height `k`, in the byte order of the double SHA-256. `tables` maps a
    source name to a table from height to hash, in the same byte order.
    """

    def __init__(self, prev_hashes: bytes = b"", tables: dict[str, dict[int, bytes]] | None = None):
        self.prev_hashes = prev_hashes
        self.tables = tables or {}

    @classmethod
    def load(cls, root: Path = ROOT) -> "Pins":
        """Read the committed sources, after a check of each `SHA256SUMS`."""
        directory = root / PREV_HASHES
        check_sums(directory, ("prev-hashes.bin",))
        prev_hashes = (directory / "prev-hashes.bin").read_bytes()
        if len(prev_hashes) != 32 * PREV_HASHES_COUNT:
            raise FetchError(f"{directory}: prev-hashes.bin has {len(prev_hashes)} bytes")
        tables = {}
        for name in HEADER_FIXTURES:
            directory = root / name
            check_sums(directory, ("headers.txt",))
            table = {}
            for line in (directory / "headers.txt").read_text().splitlines():
                height, _, header = line.partition(" ")
                if not height.isdecimal() or len(header) != 160 or int(height) in table:
                    raise FetchError(f"{directory}: malformed line for height {height!r}")
                table[int(height)] = sha256d(bytes.fromhex(header))
            tables[name] = table
        tables[CHECKPOINT_SOURCE] = {
            height: bytes.fromhex(value)[::-1] for height, value in CHECKPOINTS.items()
        }
        return cls(prev_hashes, tables)

    def lookup(self, height: int) -> list[tuple[str, bytes]]:
        """Each source that has `height`, with its hash."""
        found = []
        if 0 <= height < len(self.prev_hashes) // 32:
            found.append((PREV_HASHES, self.prev_hashes[32 * height:32 * height + 32]))
        for name, table in self.tables.items():
            if height in table:
                found.append((name, table[height]))
        return found


# Checks


def ranges(heights: list[int]) -> list[list[int]]:
    """The sorted heights as inclusive ranges `[first, last]`."""
    result = []
    for height in heights:
        if result and result[-1][1] == height - 1:
            result[-1][1] = height
        else:
            result.append([height, height])
    return result


class Verifier:
    """Checks 1 to 5 on a sequence of blocks in height order."""

    def __init__(self, pins: Pins, node_hash=None):
        """`node_hash(height)` is the node's hash for a height, in a fetch."""
        self.pins = pins
        self.node_hash = node_hash
        self.blocks = []
        self.runs = []
        self.pinned_by = {}
        self.auxpow = 0
        self.largest = (0, 0)
        self.last = None

    def add(self, height: int, raw: bytes, claimed: bytes | None = None) -> dict:
        """Check one block, and return its manifest record.

        `claimed` is the hash that `getblockhash` returned, if the block comes
        from a node.
        """
        try:
            record = self._add(height, raw, claimed)
        except FetchError as error:
            raise FetchError(f"block at height {height}: {error}") from None
        self.blocks.append(record)
        return record

    def _add(self, height: int, raw: bytes, claimed: bytes | None) -> dict:
        if self.last is not None and height <= self.last[0]:
            raise FetchError(f"the height does not follow height {self.last[0]}")
        block = Block(raw)
        if claimed is not None and block.hash != claimed:
            raise FetchError(
                f"the header hash {display(block.hash)} is not the hash "
                f"{display(claimed)} from getblockhash"
            )
        if not block.txids:
            raise FetchError("the block has no transaction")
        root, mutated = merkle_root(block.txids)
        if root != block.merkle_root:
            raise FetchError(
                f"Merkle root mismatch: the transactions give {root.hex()}, "
                f"the header has {block.merkle_root.hex()}"
            )
        if mutated:
            raise FetchError("duplicated transactions in the Merkle tree (CVE-2012-2459)")
        self._check_link(height, block)
        sources = self.pins.lookup(height)
        for name, pinned in sources:
            if block.hash != pinned:
                raise FetchError(
                    f"the hash {display(block.hash)} is not the pinned hash "
                    f"{display(pinned)} of {name}"
                )
            self.pinned_by.setdefault(name, []).append(height)
        self.last = (height, block.hash)
        self.auxpow += block.auxpow
        self.largest = max(self.largest, (block.size, height))
        return {
            "height": height,
            "hash": display(block.hash),
            "size": block.size,
            "transactions": len(block.txids),
            "auth": "pinned" if sources else "linked",
        }

    def _check_link(self, height: int, block: Block) -> None:
        """Check 4. The first block of a run adds a record to `runs`."""
        if self.last is not None and self.last[0] == height - 1:
            if block.previous != self.last[1]:
                raise FetchError(
                    f"broken link: the previous-hash field is {display(block.previous)}, "
                    f"the block at height {height - 1} has the hash {display(self.last[1])}"
                )
            self.runs[-1]["last"] = height
            return
        if height == 0:
            source, expected = "genesis", [("the null hash of a genesis block", bytes(32))]
        else:
            source, expected = "pinned", self.pins.lookup(height - 1)
            if not expected:
                source = "node"
                if self.node_hash is not None:
                    expected = [("the node's getblockhash", self.node_hash(height - 1))]
        for name, value in expected:
            if block.previous != value:
                raise FetchError(
                    f"broken link: the previous-hash field is {display(block.previous)}, "
                    f"the hash at height {height - 1} is {display(value)} ({name})"
                )
        self.runs.append({"first": height, "last": height, "previous": source})

    def derived(self) -> dict:
        """The manifest fields that the blocks alone decide."""
        return {
            "count": len(self.blocks),
            "bytes": sum(block["size"] for block in self.blocks),
            "runs": self.runs,
            "pinned_by": {name: ranges(heights) for name, heights in sorted(self.pinned_by.items())},
            "blocks": self.blocks,
        }

    def summary(self) -> str:
        pinned = sum(block["auth"] == "pinned" for block in self.blocks)
        size, height = self.largest
        return (
            f"blocks: {len(self.blocks)}, bytes: {sum(b['size'] for b in self.blocks)}\n"
            f"largest block: {size} bytes at height {height}\n"
            f"blocks with an AuxPoW payload: {self.auxpow}\n"
            f"pinned: {pinned}, linked: {len(self.blocks) - pinned}"
        )


# Fixture files


def read_blocks(path):
    """Yield `(height, raw_bytes)` for each record of a `blocks.bin` file."""
    with open(path, "rb") as stream:
        while True:
            head = stream.read(8)
            if not head:
                return
            if len(head) != 8:
                raise FetchError(f"{path}: truncated record header")
            height = int.from_bytes(head[:4], "little")
            length = int.from_bytes(head[4:], "little")
            if length > MAX_SIZE:
                raise FetchError(f"{path}: the record of height {height} claims {length} bytes")
            raw = stream.read(length)
            if len(raw) != length:
                raise FetchError(f"{path}: truncated block at height {height}")
            yield height, raw


def manifest_text(manifest: dict) -> str:
    """The manifest as JSON, with one line for each block."""
    head = {key: value for key, value in manifest.items() if key != "blocks"}
    lines = ",\n".join("    " + json.dumps(block) for block in manifest["blocks"])
    return json.dumps(head, indent=2)[:-2] + ',\n  "blocks": [\n' + lines + "\n  ]\n}\n"


def write_atomic(path: Path, data: bytes) -> None:
    temporary = path.with_name(path.name + ".tmp")
    try:
        with open(temporary, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def selection_fields(selection: dict, heights: list[int]) -> dict:
    if selection["kind"] == "heights":
        return {"selection": "heights", "heights": heights}
    fields = {"selection": selection["kind"], "first": heights[0], "last": heights[-1]}
    if selection["kind"] == "recent":
        fields["confirmations"] = selection["confirmations"]
    return fields


def check_fixture(directory, pins: Pins) -> Verifier:
    """Check a fixture directory without a network connection."""
    directory = Path(directory)
    check_sums(directory, (BLOCKS_FILE, MANIFEST_FILE))
    try:
        manifest = json.loads((directory / MANIFEST_FILE).read_text())
    except (OSError, ValueError) as error:
        raise FetchError(f"{directory / MANIFEST_FILE}: cannot read: {type(error).__name__}") from None
    if not isinstance(manifest, dict) or manifest.get("format") != FORMAT:
        raise FetchError(f"{directory / MANIFEST_FILE}: the format is not {FORMAT}")
    verifier = Verifier(pins)
    for height, raw in read_blocks(directory / BLOCKS_FILE):
        verifier.add(height, raw)
    if not verifier.blocks:
        raise FetchError(f"{directory / BLOCKS_FILE}: no block")
    heights = [block["height"] for block in verifier.blocks]
    expected = dict(verifier.derived())
    kind = manifest.get("selection")
    if kind == "heights":
        expected.update(selection="heights", heights=heights)
    elif kind in ("range", "recent"):
        expected.update(selection=kind, first=heights[0], last=heights[-1])
        if len(verifier.runs) != 1:
            raise FetchError(f"{directory}: a {kind} selection has a gap in its heights")
    else:
        raise FetchError(f"{directory / MANIFEST_FILE}: unknown selection {kind!r}")
    for key, value in expected.items():
        if manifest.get(key) != value:
            detail = ""
            if key == "blocks" and isinstance(manifest.get(key), list):
                differing = [b["height"] for a, b in zip(manifest[key], value) if a != b]
                detail = f" (first at height {differing[0]})" if differing else " (the counts differ)"
            raise FetchError(
                f"{directory / MANIFEST_FILE}: the field {key!r} does not match the blocks{detail}"
            )
    return verifier


# JSON-RPC


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Refuse a redirect, so that no other host receives the credentials."""

    def redirect_request(self, *args, **kwargs):
        return None


def http_transport(timeout: float):
    """A transport that posts one request body, and returns the response body.

    It uses no proxy and follows no redirect.
    """
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), NoRedirect())

    def transport(url: str, body: bytes, headers: dict[str, str]) -> bytes:
        request = urllib.request.Request(url, data=body, headers=headers, method="POST")
        with opener.open(request, timeout=timeout) as response:
            return response.read()

    return transport


class Rpc:
    """A JSON-RPC client that keeps the credentials out of every message."""

    def __init__(self, url: str, user: str, password: str, transport):
        parts = urllib.parse.urlsplit(url)
        if parts.scheme not in ("http", "https") or not parts.hostname or "@" in parts.netloc:
            raise FetchError("the URL must be http or https, with a host and no credentials")
        self.url = url
        self.transport = transport
        token = base64.b64encode(f"{user}:{password}".encode()).decode()
        self._headers = {"Authorization": "Basic " + token, "Content-Type": "application/json"}
        self._secrets = [f"{user}:{password}", password, token]
        self._id = 0

    def _clean(self, text: object) -> str:
        """`text` as one short line, without the password or the header."""
        text = str(text)
        for secret in self._secrets:
            if secret:
                text = text.replace(secret, "[redacted]")
        return " ".join(text.split())[:200]

    def call(self, method: str, *params):
        self._id += 1
        body = json.dumps({"jsonrpc": "1.0", "id": self._id, "method": method, "params": list(params)})
        # Each new error drops the original exception, which can hold the
        # request and its headers.
        try:
            data = self.transport(self.url, body.encode(), dict(self._headers))
        except urllib.error.HTTPError as error:
            message = f"{method}: HTTP status {error.code}"
            try:
                detail = json.loads(error.read())["error"]["message"]
                message += f": {self._clean(detail)}"
            except Exception:
                pass
            error.close()
            raise FetchError(message) from None
        except Exception as error:
            reason = getattr(error, "reason", "")
            message = f"{method}: request failed: {type(error).__name__}"
            if reason:
                message += f": {self._clean(reason)}"
            raise FetchError(message) from None
        try:
            response = json.loads(data)
            error, result = response["error"], response["result"]
            if response["id"] != self._id:
                raise ValueError
        except (ValueError, KeyError, TypeError):
            raise FetchError(f"{method}: malformed response") from None
        if error is not None:
            detail = error.get("message") if isinstance(error, dict) else error
            raise FetchError(f"{method}: {self._clean(detail)}")
        return result

    def block_count(self) -> int:
        count = self.call("getblockcount")
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            raise FetchError("getblockcount: the result is not a height")
        return count

    def block_hash(self, height: int) -> bytes:
        """The node's hash for `height`, in the byte order of the digest."""
        value = self.call("getblockhash", height)
        try:
            if not isinstance(value, str) or len(value) != 64:
                raise ValueError
            return bytes.fromhex(value)[::-1]
        except ValueError:
            raise FetchError(f"getblockhash {height}: the result is not a hash") from None

    def block(self, block_hash: bytes) -> bytes:
        value = self.call("getblock", display(block_hash), False)
        try:
            if not isinstance(value, str):
                raise ValueError
            return bytes.fromhex(value)
        except ValueError:
            raise FetchError(f"getblock {display(block_hash)}: the result is not hexadecimal") from None

    def version(self) -> str:
        info = self.call("getnetworkinfo")
        if not isinstance(info, dict):
            raise FetchError("getnetworkinfo: malformed result")
        return self._clean(f"{info.get('subversion')} ({info.get('version')})")


def read_password(env, password_file: Path) -> str:
    """The password from the environment, or else from the file."""
    password = env.get(PASSWORD_VARIABLE, "")
    if not password:
        try:
            lines = password_file.read_text().splitlines()
        except (OSError, UnicodeDecodeError):
            lines = []
        for line in lines:
            line = line.strip().removeprefix("export ").lstrip()
            name, separator, value = line.partition("=")
            if separator and name.strip() == PASSWORD_VARIABLE:
                value = value.strip()
                if len(value) >= 2 and value[0] == value[-1] and value[0] in "'\"":
                    value = value[1:-1]
                password = value
    if not password:
        raise PasswordMissing(
            f"no RPC password: set the environment variable {PASSWORD_VARIABLE}, "
            f"or write the line {PASSWORD_VARIABLE}=... to {password_file}"
        )
    return password


# Fetch


def fetch(rpc: Rpc, selection: dict, output, pins: Pins, now=None, progress=None) -> Verifier:
    """Fetch the selected blocks, check them, and write the fixture.

    `selection` has a `kind`: `range` with `first` and `last`, `recent` with
    `count` and `confirmations`, or `heights` with a list `heights`.
    """
    output = Path(output)
    tip = rpc.block_count()
    tip_hash = rpc.block_hash(tip)
    if selection["kind"] == "recent":
        last = tip - selection["confirmations"]
        heights = list(range(last - selection["count"] + 1, last + 1))
    elif selection["kind"] == "range":
        heights = list(range(selection["first"], selection["last"] + 1))
    else:
        heights = sorted(set(selection["heights"]))
    if not heights or heights[0] < 0:
        raise FetchError("the selection has no block, or a height below 0")
    if heights[-1] > tip:
        raise FetchError(f"height {heights[-1]} is above the node's tip {tip}")
    version = rpc.version()
    date = (now or datetime.datetime.now(datetime.timezone.utc)).strftime("%Y-%m-%dT%H:%M:%SZ")

    verifier = Verifier(pins, node_hash=rpc.block_hash)
    output.mkdir(parents=True, exist_ok=True)
    temporary = output / (BLOCKS_FILE + ".tmp")
    digest = hashlib.sha256()
    try:
        with open(temporary, "wb") as stream:
            for index, height in enumerate(heights, 1):
                claimed = rpc.block_hash(height)
                raw = rpc.block(claimed)
                verifier.add(height, raw, claimed)
                record = height.to_bytes(4, "little") + len(raw).to_bytes(4, "little") + raw
                stream.write(record)
                digest.update(record)
                if progress and index % 500 == 0:
                    progress(f"{index} of {len(heights)} blocks")
            stream.flush()
            os.fsync(stream.fileno())
        manifest = {
            "format": FORMAT,
            "network": "mainnet",
            **selection_fields(selection, heights),
            "node_version": version,
            "fetch_date": date,
            "tip_height": tip,
            "tip_hash": display(tip_hash),
            **verifier.derived(),
        }
        text = manifest_text(manifest).encode()
        sums = (
            f"{digest.hexdigest()}  {BLOCKS_FILE}\n"
            f"{hashlib.sha256(text).hexdigest()}  {MANIFEST_FILE}\n"
        )
        os.replace(temporary, output / BLOCKS_FILE)
        write_atomic(output / MANIFEST_FILE, text)
        write_atomic(output / SUMS_FILE, sums.encode())
    finally:
        temporary.unlink(missing_ok=True)
    return verifier


def parse_heights(text: str) -> list[int]:
    try:
        heights = [int(part) for part in text.split(",")]
    except ValueError:
        raise argparse.ArgumentTypeError("expected heights with commas between them") from None
    if not heights or min(heights) < 0:
        raise argparse.ArgumentTypeError("expected heights of 0 or more")
    return heights


def main(argv=None, env=None, transport=None, pins=None, password_file=None, out=None, err=None) -> int:
    """Run the command line. The other parameters replace parts in a test."""
    out = out or sys.stdout
    err = err or sys.stderr
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--range", nargs=2, type=int, metavar=("START", "END"), help="inclusive heights")
    mode.add_argument("--recent", type=int, metavar="N", help="the N blocks that end below the tip")
    mode.add_argument("--heights", type=parse_heights, metavar="H1,H2,...")
    mode.add_argument("--check", metavar="DIR", help="check a fixture without a network connection")
    parser.add_argument("--output", metavar="DIR")
    parser.add_argument(
        "--confirmations", type=int, default=DEFAULT_CONFIRMATIONS,
        help="with --recent, the last block is this number below the tip (default %(default)s)",
    )
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--user", default=DEFAULT_USER)
    parser.add_argument("--timeout", type=float, default=120.0, help="seconds for each request")
    args = parser.parse_args(argv)

    try:
        if args.check is not None:
            verifier = check_fixture(args.check, pins or Pins.load())
            print(verifier.summary(), file=out)
            print(f"checked {args.check}", file=out)
            return 0
        if args.output is None:
            parser.error("a fetch needs --output DIR")
        if args.range is not None:
            if not 0 <= args.range[0] <= args.range[1]:
                parser.error("--range needs 0 <= START <= END")
            selection = {"kind": "range", "first": args.range[0], "last": args.range[1]}
        elif args.recent is not None:
            if args.recent < 1 or args.confirmations < 0:
                parser.error("--recent needs N >= 1 and --confirmations >= 0")
            selection = {"kind": "recent", "count": args.recent, "confirmations": args.confirmations}
        else:
            selection = {"kind": "heights", "heights": args.heights}
        try:
            password = read_password(
                os.environ if env is None else env,
                password_file or PASSWORD_FILE.expanduser(),
            )
        except PasswordMissing as error:
            print(f"error: {error}", file=err)
            return 2
        rpc = Rpc(args.url, args.user, password, transport or http_transport(args.timeout))
        verifier = fetch(
            rpc, selection, args.output, pins or Pins.load(),
            progress=lambda text: print(text, file=err),
        )
        print(verifier.summary(), file=out)
        print(f"wrote {args.output}", file=out)
        return 0
    except FetchError as error:
        print(f"error: {error}", file=err)
        return 1


if __name__ == "__main__":
    sys.exit(main())
