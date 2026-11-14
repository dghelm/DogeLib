#!/usr/bin/env python3
"""Compare Lean's full version-bits walk with Core's VersionBitsState on the real header chain.

This run is outside continuous integration (design record 0010, section 4). It fetches the
version and time of every mainnet header from the genesis block up to a target through the
CSV window, and compares `block.version_bits_state` of the oracle with Core's
`VersionBitsState` in the harness, for CSV and SegWit.

Usage:
  python3 -I scripts/compare_version_bits_walk.py ORACLE HARNESS [--host H] [--port P]
  python3 -I scripts/compare_version_bits_walk.py --self-test ORACLE HARNESS

The fetch reads headers from the maintainer's node over JSON-RPC, in batches of
`getblockhash` and `getblockheader`. The node's data is untrusted, so the script checks
each header's `previousblockhash` link and the pinned checkpoints before it compares.
The password comes from the environment variable DOGE_RPCPASSWORD, or the file
~/.config/dogelib/node-rpc.env, as in scripts/fetch_blocks.py. The script does not print it.

The period is 10,080 blocks. The targets are period boundaries: a few below the CSV start
(2016-05-01), several through the window, and a few at or after the CSV timeout (2017-05-01).
A target request sends the headers from the genesis block to that boundary, oldest first.
"""
import argparse
import json
import os
import pathlib
import subprocess
import sys
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
from fetch_blocks import read_password, PASSWORD_FILE, DEFAULT_URL, DEFAULT_USER  # noqa: E402

PERIOD = 10080
CSV_START = 1462060800
CSV_TIMEOUT = 1493596800
# Display-order checkpoints from Core's mainnet table (D9), to authenticate the fetch.
CHECKPOINTS = {
    0: "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691",
    104679: "35eb87ae90d44b98898fec8c39577b76cb1eb08e1261cfc10706c8ce9a1d01cf",
    145000: "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72",
    1000000: "6aae55bea74235f0c80bd066349d4440c31f2d0f27d54265ecd484d8c1d11b47",
    1250000: "00c7a442055c1a990e11eea5371ca5c1c02a0677b33cc88ec728c45edc4ec060",
    1500000: "f1d32d6920de7b617d51e74bdf4e58adccaa582ffdc8657464454f16a952fca6",
    1750000: "5c8e7327984f0d6f59447d89d143e5f6eafc524c82ad95d176c5cec082ae2001",
}


def run_op(program: str, request: dict, timeout: float) -> dict:
    data = json.dumps(request) + "\n"
    proc = subprocess.run([program], input=data, capture_output=True, text=True, timeout=timeout)
    if proc.returncode != 0:
        raise SystemExit(f"{program} exited {proc.returncode}: {proc.stderr[:400]}")
    return json.loads(proc.stdout.splitlines()[0])


def rpc_batch(url: str, auth: str, calls: list[tuple[str, list]], timeout: float) -> list:
    """One JSON-RPC batch request. `calls` is a list of (method, params)."""
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


def sha256d(data: bytes) -> bytes:
    import hashlib
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def fetch_headers(url: str, auth: str, last: int, timeout: float, batch: int = 2000) -> list[dict]:
    """The version and time of heights 0 to `last`, derived from the raw header bytes.

    The script fetches the serialized 80-byte header, hashes it and binds the hash to the
    checked links and checkpoints. So the compared version and time come from the authenticated
    bytes, not from a field the node could change while keeping the hash."""
    headers = []
    height = 0
    prev_hash = None
    while height <= last:
        count = min(batch, last - height + 1)
        hashes = rpc_batch(url, auth, [("getblockhash", [h]) for h in range(height, height + count)], timeout)
        raws = rpc_batch(url, auth, [("getblockheader", [h, False]) for h in hashes], timeout)
        for h, claimed, raw_hex in zip(range(height, height + count), hashes, raws):
            raw = bytes.fromhex(raw_hex)
            if len(raw) < 80:
                raise SystemExit(f"height {h}: header shorter than 80 bytes")
            computed = sha256d(raw[:80])[::-1].hex()
            if computed != claimed:
                raise SystemExit(f"height {h}: header bytes do not hash to the claimed hash")
            if h in CHECKPOINTS and claimed != CHECKPOINTS[h]:
                raise SystemExit(f"height {h}: checkpoint mismatch")
            prev_field = raw[4:36][::-1].hex()
            if h > 0 and prev_field != prev_hash:
                raise SystemExit(f"height {h}: previous-hash field does not link")
            version = int.from_bytes(raw[0:4], "little")
            time = int.from_bytes(raw[68:72], "little")
            headers.append({"version": version, "time": time})
            prev_hash = claimed
        height += count
        print(f"  fetched {height} headers", file=sys.stderr)
    return headers


STATES = {"defined", "started", "locked_in", "active", "failed"}


def valid_states(ok) -> bool:
    """A successful version-bits response with both state fields present and known."""
    return (isinstance(ok, dict) and set(ok) == {"csv", "segwit"}
            and ok["csv"] in STATES and ok["segwit"] in STATES)


def compare_at(oracle: str, harness: str, headers: list[dict], targets: list[int], timeout: float) -> int:
    failures = 0
    for target in targets:
        chain = headers[:target]  # the genesis block to the predecessor at index target-1
        request = {"id": str(target), "op": "block.version_bits_state", "chain": chain}
        ours = run_op(oracle, request, timeout).get("ok")
        core = run_op(harness, request, timeout).get("ok")
        if not valid_states(ours) or not valid_states(core):
            print(f"height {target - 1}: oracle {ours} core {core} ERROR")
            failures += 1
            continue
        agree = ours == core
        print(f"height {target - 1}: oracle {ours} core {core} {'AGREE' if agree else 'DIFF'}")
        if not agree:
            failures += 1
    return failures


def self_test(oracle: str, harness: str, timeout: float) -> int:
    """Synthetic non-signalling chains, without the node, for the gate's self-test."""
    def chain(n, t0):
        return [{"version": 1, "time": t0 + 60 * i} for i in range(n)]
    cases = [("below start", chain(2 * PERIOD, 1400000000), {"csv": "defined", "segwit": "defined"}),
             ("in window", chain(2 * PERIOD, 1480000000), {"csv": "started", "segwit": "failed"}),
             ("after timeout", chain(2 * PERIOD, 1500000000), {"csv": "failed", "segwit": "failed"})]
    failures = 0
    for name, c, expected in cases:
        request = {"id": name, "op": "block.version_bits_state", "chain": c}
        ours = run_op(oracle, request, timeout).get("ok")
        core = run_op(harness, request, timeout).get("ok")
        ok = ours == core == expected
        print(f"{name}: oracle {ours} core {core} expected {expected} {'OK' if ok else 'FAIL'}")
        if not ok:
            failures += 1
    return failures


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("oracle")
    parser.add_argument("harness")
    parser.add_argument("--url", default=DEFAULT_URL)
    parser.add_argument("--user", default=DEFAULT_USER)
    parser.add_argument("--last", type=int, default=1720080,
                        help="the greatest height to fetch, a period boundary past the CSV timeout")
    parser.add_argument("--timeout", type=float, default=1200.0)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)

    if args.self_test:
        failures = self_test(args.oracle, args.harness, args.timeout)
        print("PASS" if failures == 0 else f"FAIL: {failures}")
        return 1 if failures else 0

    password = read_password(os.environ, PASSWORD_FILE.expanduser())
    import base64
    auth = "Basic " + base64.b64encode(f"{args.user}:{password}".encode()).decode()
    print(f"fetching headers 0 to {args.last} from the node", file=sys.stderr)
    headers = fetch_headers(args.url, auth, args.last, args.timeout)
    # Targets: period boundaries around the CSV window, as indices into the oldest-first chain.
    boundaries = [i for i in range(PERIOD, len(headers) + 1, PERIOD)]
    window = [b for b in boundaries if CSV_START - 94608000 <= headers[b - 1]["time"]]
    targets = sorted(set([boundaries[0], boundaries[len(boundaries) // 2]] +
                         window[:: max(1, len(window) // 8)] + [boundaries[-1]]))
    print(f"comparing at {len(targets)} period boundaries")
    failures = compare_at(args.oracle, args.harness, headers, targets, args.timeout)
    print("PASS" if failures == 0 else f"FAIL: {failures} disagreements")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
