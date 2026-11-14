#!/usr/bin/env python3
"""Fetch the mainnet headers that `block.contextual_check_body` needs for the real-block ranges.

Core's `ContextualCheckBlock` reads the version-bits state at the block's aligned boundary.
So the comparison on a real block needs the contiguous headers from that boundary (and its ten
predecessors, for the boundary's median time past) up to the block's predecessor. This script
fetches those header runs for the recent range and the rule-change blocks of design record 0010,
section 4, shared between blocks that have the same boundary.

The headers that the committed block fixtures already hold are not stored again: each run ends just
below the first committed block of its group. The chain builder joins this run to those blocks.

Usage:
  python3 -I scripts/fetch_version_bits_headers.py [--url URL] [--user USER] [OUT]
  python3 -I scripts/fetch_version_bits_headers.py --check [OUT]

The default OUT is tests/block/mainnet-blocks/version-bits-headers. The fetch reads headers from
the maintainer's node (the URL and user of scripts/fetch_blocks.py), hashes each one, checks the
intra-run links, the join to the committed block, and the pinned checkpoints that fall in a run.
The password is read as scripts/fetch_blocks.py reads it, and is never printed.
"""
import argparse
import base64
import hashlib
import json
import os
import pathlib
import struct
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from fetch_blocks import read_password, PASSWORD_FILE, DEFAULT_URL, DEFAULT_USER  # noqa: E402

PERIOD = 10080
DEFAULT_OUT = ROOT / "tests/block/mainnet-blocks/version-bits-headers"
RULE_RUNS = [(144998, 145001), (371336, 371338), (599998, 600001), (1034382, 1034384), (3464750, 3464752)]
RECENT = (6455302, 6456301)
# Display-order mainnet checkpoints (D9), to authenticate any header that falls on one.
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
}


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def display(block_hash: bytes) -> str:
    return block_hash[::-1].hex()


def aligned_boundary(height: int) -> int:
    return (height - 1) - (height % PERIOD)


def needed_runs() -> list[tuple[int, int, int]]:
    """Each fetched run as (first, last, committed_first): the headers below the first committed block.

    The run covers the aligned boundary (and its ten predecessors) of the group down to just below
    the group's first committed block. `committed_first` is the first block the committed fixture holds.
    """
    runs = []
    for first, last in RULE_RUNS + [RECENT]:
        low = min(aligned_boundary(h) - 10 for h in range(first, last + 1))
        runs.append((low, first - 1, first))
    return runs


def rpc_batch(url: str, auth: str, calls, timeout: float) -> list:
    body = json.dumps([{"jsonrpc": "1.0", "id": i, "method": m, "params": p}
                       for i, (m, p) in enumerate(calls)]).encode()
    req = urllib.request.Request(url, data=body, method="POST",
                                 headers={"Content-Type": "application/json", "Authorization": auth})
    with urllib.request.urlopen(req, timeout=timeout) as response:
        results = json.loads(response.read())
    results.sort(key=lambda r: r["id"])
    out = []
    for r in results:
        if r.get("error"):
            raise SystemExit(f"RPC error: {r['error']}")
        out.append(r["result"])
    return out


def fetch_run(url, auth, first, last, timeout, batch=2000) -> list[bytes]:
    """The raw 80-byte headers of heights `first` to `last`, hashed and link-checked."""
    headers, prev_hash, height = [], None, first
    while height <= last:
        count = min(batch, last - height + 1)
        hashes = rpc_batch(url, auth, [("getblockhash", [h]) for h in range(height, height + count)], timeout)
        raws = rpc_batch(url, auth, [("getblockheader", [h, False]) for h in hashes], timeout)
        for h, claimed, raw_hex in zip(range(height, height + count), hashes, raws):
            raw = bytes.fromhex(raw_hex)[:80]
            if len(raw) != 80 or display(sha256d(raw)) != claimed:
                raise SystemExit(f"height {h}: header bytes do not hash to the claimed hash")
            if h in CHECKPOINTS and claimed != CHECKPOINTS[h]:
                raise SystemExit(f"height {h}: checkpoint mismatch")
            if prev_hash is not None and display(raw[4:36]) != prev_hash:
                raise SystemExit(f"height {h}: previous-hash field does not link")
            headers.append(raw)
            prev_hash = claimed
        height += count
        print(f"  run {first}-{last}: fetched to {height - 1}", file=sys.stderr)
    return headers


def node_header(url: str, auth: str, height: int, timeout: float) -> bytes:
    """The 80-byte header of a block from the node, checked to hash to its height's hash."""
    [hash_] = rpc_batch(url, auth, [("getblockhash", [height])], timeout)
    [raw_hex] = rpc_batch(url, auth, [("getblockheader", [hash_, False])], timeout)
    raw = bytes.fromhex(raw_hex)[:80]
    if display(sha256d(raw)) != hash_:
        raise SystemExit(f"height {height}: node header does not hash to its hash")
    return raw


def rule_change_header(committed_first: int) -> bytes | None:
    """The first committed rule-change block's header, for the offline join check, or None for the recent range."""
    if committed_first >= RECENT[0]:
        return None
    from oracle_block_check import fixture_blocks
    for record, raw in fixture_blocks(DEFAULT_OUT.parent / "rule-changes"):
        if record["height"] == committed_first:
            return raw[:80]
    raise SystemExit(f"committed rule-change block {committed_first} not found")


def write_fixture(out: pathlib.Path, runs, headers_by_run) -> None:
    out.mkdir(parents=True, exist_ok=True)
    blob = b"".join(b"".join(headers_by_run[first]) for first, _, _ in runs)
    (out / "headers.bin").write_bytes(blob)
    manifest = {
        "format": "dogelib-version-bits-headers/1",
        "network": "mainnet",
        "runs": [{"first": first, "count": last - first + 1, "links_to": committed_first}
                 for first, last, committed_first in runs],
        "bytes": len(blob),
        "checkpoints": {str(h): c for h, c in CHECKPOINTS.items()
                        if any(first <= h <= last for first, last, _ in runs)},
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    digests = {"headers.bin": hashlib.sha256(blob).hexdigest(),
               "manifest.json": hashlib.sha256((out / "manifest.json").read_bytes()).hexdigest()}
    (out / "SHA256SUMS").write_text("".join(f"{d}  {name}\n" for name, d in sorted(digests.items())))


def load_fixture(out: pathlib.Path) -> dict[int, bytes]:
    """Height -> 80-byte header, for every fetched header of the fixture."""
    manifest = json.loads((out / "manifest.json").read_text())
    blob = (out / "headers.bin").read_bytes()
    expected = sum(run["count"] for run in manifest["runs"]) * 80
    if len(blob) != expected:
        raise SystemExit(f"headers.bin has {len(blob)} bytes, not the {expected} the manifest runs require")
    result, offset = {}, 0
    for run in manifest["runs"]:
        for i in range(run["count"]):
            result[run["first"] + i] = blob[offset:offset + 80]
            offset += 80
    return result


def check_fixture(out: pathlib.Path) -> None:
    """Re-check the committed fixture: hashes, intra-run links, the join and the checkpoints."""
    manifest = json.loads((out / "manifest.json").read_text())
    headers = load_fixture(out)
    for run in manifest["runs"]:
        prev_hash = None
        for h in range(run["first"], run["first"] + run["count"]):
            raw = headers[h]
            claimed = display(sha256d(raw))
            if str(h) in manifest["checkpoints"] and claimed != manifest["checkpoints"][str(h)]:
                raise SystemExit(f"height {h}: checkpoint mismatch")
            if prev_hash is not None and display(raw[4:36]) != prev_hash:
                raise SystemExit(f"height {h}: previous-hash field does not link")
            prev_hash = claimed
        committed = rule_change_header(run["links_to"])
        if committed is not None:  # the recent range's committed blocks are a download, not committed; its join was checked at fetch
            join = headers[run["first"] + run["count"] - 1]
            if display(committed[4:36]) != display(sha256d(join)):
                raise SystemExit(f"run ending at {run['first'] + run['count'] - 1}: does not join block {run['links_to']}")
    print(f"version-bits headers: {sum(r['count'] for r in manifest['runs'])} headers in {len(manifest['runs'])} runs, "
          f"linked to the committed blocks and the pinned checkpoints")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("out", nargs="?", default=str(DEFAULT_OUT))
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--user", default=DEFAULT_USER)
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    out = pathlib.Path(args.out)

    if args.check:
        check_fixture(out)
        return 0

    password = read_password(os.environ, PASSWORD_FILE.expanduser())
    auth = "Basic " + base64.b64encode(f"{args.user}:{password}".encode()).decode()
    runs = needed_runs()
    headers_by_run = {}
    for first, last, committed_first in runs:
        run_headers = fetch_run(args.url, auth, first, last, args.timeout)
        committed = node_header(args.url, auth, committed_first, args.timeout)
        if display(committed[4:36]) != display(sha256d(run_headers[-1])):
            raise SystemExit(f"run ending at {last}: does not join block {committed_first}")
        headers_by_run[first] = run_headers
    write_fixture(out, runs, headers_by_run)
    total = sum(len(v) for v in headers_by_run.values())
    print(f"wrote {total} headers ({total * 80} bytes) to {out}")
    check_fixture(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
