#!/usr/bin/env python3
"""Fetch the mainnet block ranges that a GitHub release stores, and check them.

Usage:
  python3 -I scripts/fetch_release_blocks.py [--output DIR] [--assets DIR]
  python3 -I scripts/fetch_release_blocks.py --pack FIXTURE_DIR NAME --assets DIR

Two block ranges are too large for the repository: mainnet heights 0 to
10,000, and 1,000 recent blocks (design record 0010, decision 2). A GitHub
release holds each range as two assets, the `blocks.bin` and the
`manifest.json` of a `scripts/fetch_blocks.py` fixture, each compressed with
xz. The committed file `tests/block/mainnet-blocks/release.json` names the
release and gives the size and the SHA-256 of each asset and of each file.

The default mode writes one fixture directory for each range under DIR,
which is `build/mainnet-blocks` by default. For each file it does this:

1. It keeps a file that is already in the directory with the committed
   SHA-256.
2. Otherwise it reads the asset from the release. With `--assets DIR` it
   reads the asset from that directory, and uses no network connection.
3. It requires the committed size and SHA-256 of the asset, decompresses the
   asset, and requires the committed size and SHA-256 of the file.

It then writes the `SHA256SUMS` file of the fixture from the committed
values, and runs every check of `scripts/fetch_blocks.py --check` on the
directory. So each block is checked against its header, its Merkle root, its
neighbours and the pinned hashes of the repository. The range must have the
heights and the number of blocks that `release.json` gives.

A download sends no credentials. The release is public.

`--pack FIXTURE_DIR NAME --assets DIR` is the step that made the assets. It
checks the fixture, writes the two compressed assets of the range NAME to
DIR, and prints the entry for `release.json`.
"""

import argparse
import hashlib
import json
import lzma
import sys
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks as fb  # noqa: E402

FORMAT = "dogelib-block-assets/1"
RELEASE_FILE = ROOT / "tests/block/mainnet-blocks/release.json"
DEFAULT_OUTPUT = ROOT / "build/mainnet-blocks"
FILES = (fb.BLOCKS_FILE, fb.MANIFEST_FILE)
ATTEMPTS = 3


class AssetError(Exception):
    """A failed check, a failed download or a malformed `release.json`."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_sha256(value) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def is_count(value) -> bool:
    return type(value) is int and value >= 0


def is_name(value) -> bool:
    """A file or directory name of letters, digits, `.`, `-` and `_`."""
    return (isinstance(value, str) and value not in ("", ".", "..")
            and all(c.isascii() and (c.isalnum() or c in ".-_") for c in value))


def load_release(path: Path = RELEASE_FILE) -> dict:
    """Read and validate `release.json`."""
    try:
        release = json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise AssetError(f"{path}: cannot read: {type(error).__name__}") from None
    if not isinstance(release, dict) or release.get("format") != FORMAT:
        raise AssetError(f"{path}: the format is not {FORMAT}")
    repository, tag, ranges = release.get("repository"), release.get("tag"), release.get("ranges")
    if (not isinstance(repository, str) or len(repository.split("/")) != 2
            or not all(is_name(part) for part in repository.split("/")) or not is_name(tag)):
        raise AssetError(f"{path}: malformed repository or tag")
    if not isinstance(ranges, list) or not ranges:
        raise AssetError(f"{path}: no range")
    names = set()
    for entry in ranges:
        if (not isinstance(entry, dict) or not is_name(entry.get("name")) or entry["name"] in names
                or not all(is_count(entry.get(key)) for key in ("first", "last", "blocks"))
                or not isinstance(entry.get("files"), dict) or sorted(entry["files"]) != sorted(FILES)):
            raise AssetError(f"{path}: malformed range entry")
        names.add(entry["name"])
        for record in entry["files"].values():
            if (not isinstance(record, dict) or not is_name(record.get("asset"))
                    or not is_count(record.get("bytes")) or not is_count(record.get("asset_bytes"))
                    or not is_sha256(record.get("sha256")) or not is_sha256(record.get("asset_sha256"))):
                raise AssetError(f"{path}: malformed file record in the range {entry['name']}")
    return release


def asset_url(release: dict, asset: str) -> str:
    return f"https://github.com/{release['repository']}/releases/download/{release['tag']}/{asset}"


def download(url: str, size: int, timeout: float) -> bytes:
    """The body of `url`. A body of more than `size` bytes fails."""
    last = None
    for _ in range(ATTEMPTS):
        try:
            with urllib.request.urlopen(url, timeout=timeout) as response:
                data = response.read(size + 1)
            if len(data) > size:
                raise AssetError(f"{url}: the asset has more than {size} bytes")
            return data
        except urllib.error.HTTPError as error:
            last = f"HTTP status {error.code}"
            error.close()
        except (OSError, urllib.error.URLError) as error:
            last = type(error).__name__
    raise AssetError(f"{url}: download failed after {ATTEMPTS} attempts: {last}")


def decompress(data: bytes, size: int) -> bytes:
    """The content of one xz stream, which must have exactly `size` bytes."""
    decompressor = lzma.LZMADecompressor(format=lzma.FORMAT_XZ)
    try:
        content = decompressor.decompress(data, max_length=size + 1)
    except lzma.LZMAError:
        raise AssetError("the asset is not an xz stream") from None
    if len(content) != size or not decompressor.eof or decompressor.unused_data:
        raise AssetError(f"the asset does not decompress to exactly {size} bytes")
    return content


def restore_file(release: dict, record: dict, target: Path, assets: Path | None, fetcher, timeout: float) -> str:
    """Write one file of a range to `target`, and say where it came from."""
    if target.is_file() and target.stat().st_size == record["bytes"] and sha256_file(target) == record["sha256"]:
        return "kept"
    asset = record["asset"]
    if assets is not None:
        try:
            data = (assets / asset).read_bytes()
        except OSError as error:
            raise AssetError(f"{assets / asset}: cannot read: {type(error).__name__}") from None
        source = "read"
    else:
        data = fetcher(asset_url(release, asset), record["asset_bytes"], timeout)
        source = "downloaded"
    if len(data) != record["asset_bytes"] or hashlib.sha256(data).hexdigest() != record["asset_sha256"]:
        raise AssetError(f"{asset}: the size or the SHA-256 is not the committed value")
    try:
        content = decompress(data, record["bytes"])
    except AssetError as error:
        raise AssetError(f"{asset}: {error}") from None
    if hashlib.sha256(content).hexdigest() != record["sha256"]:
        raise AssetError(f"{asset}: the decompressed file does not have the committed SHA-256")
    fb.write_atomic(target, content)
    return source


def sums_text(entry: dict) -> str:
    """The `SHA256SUMS` file of a range, from the committed values."""
    return "".join(f"{entry['files'][name]['sha256']}  {name}\n" for name in FILES)


def check_range(entry: dict, directory: Path, pins: fb.Pins) -> fb.Verifier:
    """Run the fixture checks, and compare the range with its entry."""
    try:
        verifier = fb.check_fixture(directory, pins)
    except fb.FetchError as error:
        raise AssetError(f"range {entry['name']}: {error}") from None
    heights = [block["height"] for block in verifier.blocks]
    if len(verifier.runs) != 1 or [heights[0], heights[-1], len(heights)] != [entry["first"], entry["last"], entry["blocks"]]:
        raise AssetError(
            f"range {entry['name']}: the fixture has {len(heights)} blocks from {heights[0]} to {heights[-1]}, "
            f"release.json gives {entry['blocks']} from {entry['first']} to {entry['last']}"
        )
    return verifier


def restore(release: dict, output: Path, assets: Path | None = None, pins: fb.Pins | None = None,
            fetcher=download, timeout: float = 120.0, out=None) -> None:
    """Write and check the fixture directory of every range under `output`."""
    out = out or sys.stdout
    pins = pins or fb.Pins.load()
    for entry in release["ranges"]:
        directory = output / entry["name"]
        directory.mkdir(parents=True, exist_ok=True)
        for name in FILES:
            source = restore_file(release, entry["files"][name], directory / name, assets, fetcher, timeout)
            print(f"{entry['name']}/{name}: {source}", file=out)
        fb.write_atomic(directory / fb.SUMS_FILE, sums_text(entry).encode())
        verifier = check_range(entry, directory, pins)
        print(verifier.summary(), file=out)
        print(f"checked {directory}", file=out)


def pack(fixture: Path, name: str, assets: Path, pins: fb.Pins | None = None) -> dict:
    """Check a fixture, write its two assets to `assets`, and return its entry."""
    if not is_name(name):
        raise AssetError(f"the range name {name!r} has a character other than letters, digits, '.', '-' and '_'")
    try:
        verifier = fb.check_fixture(fixture, pins or fb.Pins.load())
    except fb.FetchError as error:
        raise AssetError(str(error)) from None
    if len(verifier.runs) != 1:
        raise AssetError(f"{fixture}: the heights have a gap")
    heights = [block["height"] for block in verifier.blocks]
    assets.mkdir(parents=True, exist_ok=True)
    files = {}
    for file_name in FILES:
        content = (fixture / file_name).read_bytes()
        data = lzma.compress(content, format=lzma.FORMAT_XZ, preset=9 | lzma.PRESET_EXTREME)
        asset = f"mainnet-blocks-{name}.{file_name}.xz"
        fb.write_atomic(assets / asset, data)
        files[file_name] = {
            "asset": asset,
            "asset_bytes": len(data),
            "asset_sha256": hashlib.sha256(data).hexdigest(),
            "bytes": len(content),
            "sha256": hashlib.sha256(content).hexdigest(),
        }
    return {"name": name, "first": heights[0], "last": heights[-1], "blocks": len(heights), "files": files}


def main(argv=None, out=None, err=None, release_file: Path = RELEASE_FILE, pins=None, fetcher=download) -> int:
    """Run the command line. The other parameters replace parts in a test."""
    out = out or sys.stdout
    err = err or sys.stderr
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", metavar="DIR", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--assets", metavar="DIR", type=Path, help="read the assets from DIR, or write them with --pack")
    parser.add_argument("--pack", nargs=2, metavar=("FIXTURE_DIR", "NAME"))
    parser.add_argument("--timeout", type=float, default=120.0, help="seconds for each download")
    args = parser.parse_args(argv)
    try:
        if args.pack is not None:
            if args.assets is None:
                parser.error("--pack needs --assets DIR")
            entry = pack(Path(args.pack[0]), args.pack[1], args.assets, pins)
            print(json.dumps(entry, indent=2), file=out)
            return 0
        restore(load_release(release_file), args.output, args.assets, pins, fetcher, args.timeout, out)
        return 0
    except AssetError as error:
        print(f"error: {error}", file=err)
        return 1


if __name__ == "__main__":
    sys.exit(main())
