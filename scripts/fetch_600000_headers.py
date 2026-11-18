#!/usr/bin/env python3
"""Fetch and cross-check the mainnet headers at heights 599,998 to 600,001.

Usage:
  python3 -I scripts/fetch_600000_headers.py [--url URL] [--user USER] [OUT]

The command reads each header from the maintainer's node and from both
approved TLS Electrum servers. It writes the fixture only if all three
sources return the same four pure headers. It refuses an existing output
directory, so it never overwrites committed expectations.

The node password is read as scripts/fetch_blocks.py reads it, and is never
printed. The Electrum responses contain full headers, including each AuxPoW
payload. This command uses scripts/check_full_headers.py to split them.
"""

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import socket
import ssl
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fetch_blocks as fb  # noqa: E402
from check_full_headers import Reader as FullHeaderReader  # noqa: E402

FIRST = 599998
COUNT = 4
HEIGHTS = tuple(range(FIRST, FIRST + COUNT))
SERVERS = (
    ("dogecoin.stackwallet.com", 50022),
    ("electrum2.cipig.net", 20060),
)
DEFAULT_OUT = ROOT / "tests/block/mainnet-600000-headers"
MAX_RESPONSE = 1 << 20


def server_name(server: tuple[str, int]) -> str:
    return f"{server[0]}:{server[1]}"


def check_header_set(headers: list[bytes], source: str) -> None:
    """Require exactly the four consecutive 80-byte pure headers."""
    if len(headers) != COUNT:
        raise fb.FetchError(f"{source}: returned {len(headers)} headers, expected {COUNT}")
    previous = None
    for height, header in zip(HEIGHTS, headers):
        if not isinstance(header, bytes) or len(header) != 80:
            raise fb.FetchError(f"{source}: height {height} is not an 80-byte header")
        if previous is not None and header[4:36] != previous:
            raise fb.FetchError(f"{source}: height {height} does not link to height {height - 1}")
        previous = fb.sha256d(header)


def node_headers(rpc: fb.Rpc) -> list[bytes]:
    """Read the four headers from a node, and check each claimed hash."""
    headers = []
    for height in HEIGHTS:
        claimed = rpc.block_hash(height)
        block = rpc.block(claimed)
        header = block[:80]
        if len(header) != 80:
            raise fb.FetchError(f"node: block at height {height} has no complete header")
        if fb.sha256d(header) != claimed:
            raise fb.FetchError(f"node: header at height {height} does not match getblockhash")
        headers.append(header)
    check_header_set(headers, "node")
    return headers


def read_response(stream, request_id: int, source: str):
    """Read one bounded newline-terminated Electrum JSON-RPC response."""
    line = stream.readline(MAX_RESPONSE + 1)
    if not line:
        raise fb.FetchError(f"{source}: response {request_id} is absent")
    if len(line) > MAX_RESPONSE:
        raise fb.FetchError(f"{source}: response {request_id} is too large")
    if not line.endswith(b"\n"):
        raise fb.FetchError(f"{source}: response {request_id} has no newline")
    try:
        response = json.loads(line)
    except (UnicodeDecodeError, json.JSONDecodeError):
        raise fb.FetchError(f"{source}: response {request_id} is not JSON") from None
    if not isinstance(response, dict) or response.get("id") != request_id:
        raise fb.FetchError(f"{source}: response {request_id} has the wrong JSON-RPC id")
    if response.get("error") is not None:
        raise fb.FetchError(f"{source}: response {request_id} reports an error")
    if "result" not in response:
        raise fb.FetchError(f"{source}: response {request_id} is malformed")
    return response["result"]


def electrum_exchange(server: tuple[str, int], timeout: float):
    """Send the version and header requests over certificate-checked TLS."""
    host, port = server
    source = server_name(server)
    requests = (
        {"id": 1, "method": "server.version", "params": ["DogeLib", "1.4"]},
        {"id": 2, "method": "blockchain.block.headers", "params": [FIRST, COUNT]},
    )
    try:
        with socket.create_connection((host, port), timeout=timeout) as connection:
            context = ssl.create_default_context()
            with context.wrap_socket(connection, server_hostname=host) as tls:
                stream = tls.makefile("rwb")
                results = []
                for request in requests:
                    body = json.dumps(request, separators=(",", ":")) + "\n"
                    stream.write(body.encode())
                    stream.flush()
                    results.append(read_response(stream, request["id"], source))
                return tuple(results)
    except fb.FetchError:
        raise
    except Exception as error:
        raise fb.FetchError(f"{source}: request failed: {type(error).__name__}") from None


def electrum_headers(server: tuple[str, int], timeout: float, exchange=electrum_exchange) -> list[bytes]:
    """Read and split one server's four full-header records."""
    source = server_name(server)
    version, result = exchange(server, timeout)
    if not (isinstance(version, list) and len(version) == 2 and all(isinstance(v, str) for v in version)):
        raise fb.FetchError(f"{source}: server.version result is malformed")
    if not isinstance(result, dict) or result.get("count") != COUNT:
        raise fb.FetchError(f"{source}: header result has the wrong count")
    value = result.get("hex")
    if not isinstance(value, str) or len(value) % 2 or re.fullmatch(r"[0-9a-fA-F]*", value) is None:
        raise fb.FetchError(f"{source}: header result is not hexadecimal")
    data = bytes.fromhex(value)
    reader = FullHeaderReader(data)
    headers = []
    try:
        for _ in HEIGHTS:
            headers.append(reader.full_header()[:80])
    except (KeyError, ValueError) as error:
        raise fb.FetchError(f"{source}: malformed full-header stream: {error}") from None
    if reader.pos != len(data):
        raise fb.FetchError(f"{source}: trailing bytes after four full headers")
    check_header_set(headers, source)
    return headers


def authenticate(node_fetch=node_headers, electrum_fetch=electrum_headers, rpc=None, timeout=30.0) -> list[bytes]:
    """Return the node headers only after both Electrum sources agree."""
    local = node_fetch(rpc)
    check_header_set(local, "node")
    for server in SERVERS:
        remote = electrum_fetch(server, timeout)
        if remote != local:
            differing = next(height for height, a, b in zip(HEIGHTS, local, remote) if a != b)
            raise fb.FetchError(f"{server_name(server)}: header disagrees with the node at height {differing}")
    return local


def fixture_text(headers: list[bytes]) -> str:
    return "".join(f"{height} {header.hex()}\n" for height, header in zip(HEIGHTS, headers))


def write_fixture(output: pathlib.Path, headers: list[bytes]) -> None:
    """Publish both fixture files atomically to a new directory."""
    output = pathlib.Path(output)
    if output.exists():
        raise fb.FetchError(f"{output}: output already exists")
    output.parent.mkdir(parents=True, exist_ok=True)
    stage = pathlib.Path(tempfile.mkdtemp(prefix=f".{output.name}.tmp-", dir=output.parent))
    try:
        data = fixture_text(headers).encode()
        (stage / "headers.txt").write_bytes(data)
        digest = hashlib.sha256(data).hexdigest()
        (stage / "SHA256SUMS").write_text(f"{digest}  headers.txt\n")
        os.rename(stage, output)
    finally:
        if stage.exists():
            shutil.rmtree(stage)


def fetch_fixture(output: pathlib.Path, rpc=None, timeout=30.0,
                  node_fetch=node_headers, electrum_fetch=electrum_headers) -> list[bytes]:
    """Authenticate all sources, then publish the complete fixture."""
    headers = authenticate(node_fetch, electrum_fetch, rpc, timeout)
    write_fixture(output, headers)
    return headers


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("out", nargs="?", default=str(DEFAULT_OUT))
    parser.add_argument("--url", default=fb.DEFAULT_URL)
    parser.add_argument("--user", default=fb.DEFAULT_USER)
    parser.add_argument("--timeout", type=float, default=30.0)
    args = parser.parse_args(argv)
    try:
        password = fb.read_password(os.environ, fb.PASSWORD_FILE.expanduser())
        rpc = fb.Rpc(args.url, args.user, password, fb.http_transport(args.timeout))
        headers = fetch_fixture(pathlib.Path(args.out), rpc=rpc, timeout=args.timeout)
    except fb.PasswordMissing as error:
        print(error, file=sys.stderr)
        return 2
    except (fb.FetchError, OSError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    hashes = ", ".join(f"{height}:{fb.display(fb.sha256d(header))}" for height, header in zip(HEIGHTS, headers))
    print(f"wrote {len(headers)} headers to {args.out}")
    print(hashes)
    return 0


if __name__ == "__main__":
    sys.exit(main())
