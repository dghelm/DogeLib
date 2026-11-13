#!/usr/bin/env python3
"""Fetch and check the previous block hashes of mainnet heights 1 to 145,000.

Usage: python3 -I scripts/fetch_subsidy_prev_hashes.py [--host HOST] [--port PORT] OUTPUT

The script reads the 145,001 mainnet headers at heights 0 to 145,000 from a
public Electrum server, over TLS with the default certificate checks. The
server's data is untrusted, so the script checks the headers before it writes
anything:

- Every header has 80 bytes.
- The previous-hash field of each header from height 1 is the double SHA-256
  of the header before it.
- The hashes at heights 0, 104679 and 145000 are the checkpoints of Dogecoin
  Core at the pin (SOURCES.md D9, src/chainparams.cpp lines 182 to 184).

OUTPUT then holds 145,000 records of 32 bytes. Record k, counted from zero, is
the hash of the block at height k, in the byte order of Core's uint256. It is
the previous block hash of height k + 1.

tests/block/mainnet-subsidy-prev-hashes/README.md records the fetch that made
the committed fixture. No comparison runs this script.
"""

import argparse
import hashlib
import json
import socket
import ssl
import sys

FIRST, LAST = 0, 145000
CHUNK = 2016
# Display-order hashes from Core's mainnet checkpoint table (D9).
CHECKPOINTS = {
    0: "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691",
    104679: "35eb87ae90d44b98898fec8c39577b76cb1eb08e1261cfc10706c8ce9a1d01cf",
    145000: "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72",
}


def sha256d(data: bytes) -> bytes:
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def fetch(host: str, port: int) -> list[bytes]:
    context = ssl.create_default_context()
    headers = []
    with socket.create_connection((host, port), timeout=60) as raw:
        with context.wrap_socket(raw, server_hostname=host) as conn:
            stream = conn.makefile("rwb")
            start = FIRST
            while start <= LAST:
                count = min(CHUNK, LAST - start + 1)
                request = {"id": start, "method": "blockchain.block.headers", "params": [start, count]}
                stream.write(json.dumps(request).encode() + b"\n")
                stream.flush()
                response = json.loads(stream.readline())
                result = response.get("result")
                if response.get("id") != start or not isinstance(result, dict):
                    raise SystemExit(f"error: unexpected response at height {start}: {str(response)[:200]}")
                data = bytes.fromhex(result["hex"])
                if result.get("count") != count or len(data) != 80 * count:
                    raise SystemExit(f"error: the server returned {result.get('count')} headers at height {start}, expected {count}")
                headers.extend(data[i:i + 80] for i in range(0, len(data), 80))
                start += count
    return headers


def check(headers: list[bytes]) -> list[bytes]:
    """The block hash of every header, after the link and checkpoint checks."""
    if len(headers) != LAST - FIRST + 1:
        raise SystemExit(f"error: {len(headers)} headers, expected {LAST - FIRST + 1}")
    hashes = [sha256d(header) for header in headers]
    for height in range(1, len(headers)):
        if headers[height][4:36] != hashes[height - 1]:
            raise SystemExit(f"error: header {height} does not link to header {height - 1}")
    for height, display in CHECKPOINTS.items():
        if hashes[height][::-1].hex() != display:
            raise SystemExit(f"error: the hash at height {height} is not Core's checkpoint")
    return hashes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--host", default="dogecoin.stackwallet.com")
    parser.add_argument("--port", type=int, default=50022)
    parser.add_argument("output")
    args = parser.parse_args()
    hashes = check(fetch(args.host, args.port))
    data = b"".join(hashes[:LAST])
    with open(args.output, "wb") as out:
        out.write(data)
    print(f"wrote {len(data)} bytes, sha256 {hashlib.sha256(data).hexdigest()}")
    print(f"links checked: {LAST}, checkpoints checked: {sorted(CHECKPOINTS)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
