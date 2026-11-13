#!/usr/bin/env python3
"""Tests of scripts/fetch_release_blocks.py, without a network connection.

Usage: python3 -I scripts/test_fetch_release_blocks.py

The tests pack a fixture of synthetic blocks into assets, and restore it from
a directory and from a fake download. Each planted fault must fail with a
message that names the fault. The tests also read the committed
`tests/block/mainnet-blocks/release.json`.
"""

import hashlib
import io
import json
import lzma
import pathlib
import sys
import tempfile
import unittest
import urllib.error
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import fetch_blocks as fb  # noqa: E402
import fetch_release_blocks as frb  # noqa: E402
import test_fetch_blocks as tfb  # noqa: E402

NAME = "synthetic-5"
PINS = tfb.REAL_PINS


def xz(content: bytes) -> bytes:
    return lzma.compress(content, format=lzma.FORMAT_XZ)


class Case(unittest.TestCase):
    def setUp(self):
        self._directory = tempfile.TemporaryDirectory()
        self.addCleanup(self._directory.cleanup)
        self.tmp = pathlib.Path(self._directory.name)
        self.fixture, self.assets, self.output = self.tmp / "fixture", self.tmp / "assets", self.tmp / "output"
        self.blocks = tfb.make_chain(5)
        node = tfb.FakeNode(self.blocks)
        fb.fetch(node.rpc(), {"kind": "range", "first": tfb.BASE, "last": tfb.BASE + 4}, self.fixture, PINS, now=tfb.NOW)
        self.entry = frb.pack(self.fixture, NAME, self.assets, PINS)
        self.release = {"format": frb.FORMAT, "repository": "owner/repo", "tag": "fixtures-1", "ranges": [self.entry]}
        self.release_file = self.tmp / "release.json"
        self.write_release()

    def write_release(self):
        self.release_file.write_text(json.dumps(self.release))

    def record(self, name=fb.BLOCKS_FILE) -> dict:
        return self.entry["files"][name]

    def asset(self, name=fb.BLOCKS_FILE) -> pathlib.Path:
        return self.assets / self.record(name)["asset"]

    def replace_asset(self, data: bytes, name=fb.BLOCKS_FILE, commit: bool = True):
        """Write other bytes as an asset. With `commit`, release.json gets their size and hash."""
        self.asset(name).write_bytes(data)
        if commit:
            self.record(name).update(asset_bytes=len(data), asset_sha256=hashlib.sha256(data).hexdigest())
            self.write_release()

    def run_main(self, arguments=None, fetcher=None):
        out, err = io.StringIO(), io.StringIO()
        if arguments is None:
            arguments = ["--output", str(self.output), "--assets", str(self.assets)]
        status = frb.main(arguments, out=out, err=err, release_file=self.release_file, pins=PINS,
                          fetcher=fetcher or self.no_network)
        return status, out.getvalue(), err.getvalue()

    def no_network(self, *args):
        raise AssertionError("the test must not download")

    def assert_fails(self, pattern, arguments=None, fetcher=None):
        status, out, err = self.run_main(arguments, fetcher)
        self.assertEqual(status, 1, out + err)
        self.assertRegex(err, "^error: ")
        self.assertRegex(err, pattern)

    def restored(self, name=fb.BLOCKS_FILE) -> pathlib.Path:
        return self.output / NAME / name


class Good(Case):
    def test_pack_entry(self):
        self.assertEqual((self.entry["name"], self.entry["first"], self.entry["last"], self.entry["blocks"]),
                         (NAME, tfb.BASE, tfb.BASE + 4, 5))
        for name in frb.FILES:
            record, content = self.record(name), (self.fixture / name).read_bytes()
            self.assertEqual(record["asset"], f"mainnet-blocks-{NAME}.{name}.xz")
            self.assertEqual((record["bytes"], record["sha256"]), (len(content), hashlib.sha256(content).hexdigest()))
            data = self.asset(name).read_bytes()
            self.assertEqual((record["asset_bytes"], record["asset_sha256"]), (len(data), hashlib.sha256(data).hexdigest()))
            self.assertEqual(lzma.decompress(data), content)

    def test_restore_from_a_directory(self):
        status, out, err = self.run_main()
        self.assertEqual((status, err), (0, ""))
        self.assertIn(f"{NAME}/blocks.bin: read", out)
        self.assertIn("blocks: 5,", out)
        for name in (*frb.FILES, fb.SUMS_FILE):
            self.assertEqual(self.restored(name).read_bytes(), (self.fixture / name).read_bytes())
        # A second run keeps the files, and needs no asset.
        status, out, err = self.run_main(["--output", str(self.output), "--assets", str(self.tmp / "absent")])
        self.assertEqual((status, err), (0, ""))
        self.assertIn(f"{NAME}/blocks.bin: kept", out)
        self.assertIn(f"{NAME}/manifest.json: kept", out)

    def test_restore_from_a_download(self):
        calls = []

        def fetcher(url, size, timeout):
            calls.append((url, size))
            return (self.assets / url.rsplit("/", 1)[1]).read_bytes()

        status, out, err = self.run_main(["--output", str(self.output)], fetcher)
        self.assertEqual((status, err), (0, ""))
        self.assertIn(f"{NAME}/blocks.bin: downloaded", out)
        self.assertEqual(calls, [
            (f"https://github.com/owner/repo/releases/download/fixtures-1/{self.record(name)['asset']}",
             self.record(name)["asset_bytes"]) for name in frb.FILES])
        self.assertEqual(self.restored().read_bytes(), (self.fixture / fb.BLOCKS_FILE).read_bytes())

    def test_changed_output_file_is_replaced(self):
        self.assertEqual(self.run_main()[0], 0)
        self.restored().write_bytes(b"other")
        status, out, _ = self.run_main()
        self.assertEqual(status, 0)
        self.assertIn(f"{NAME}/blocks.bin: read", out)
        self.assertIn(f"{NAME}/manifest.json: kept", out)
        self.assertEqual(self.restored().read_bytes(), (self.fixture / fb.BLOCKS_FILE).read_bytes())

    def test_committed_release_file(self):
        release = frb.load_release()
        self.assertEqual(release["repository"], "dghelm/DogeLib")
        self.assertEqual([(e["first"], e["last"], e["blocks"]) for e in release["ranges"]],
                         [(0, 10000, 10001), (6455302, 6456301, 1000)])
        for entry in release["ranges"]:
            for name, record in entry["files"].items():
                self.assertEqual(record["asset"], f"mainnet-blocks-{entry['name']}.{name}.xz")
                self.assertLess(record["asset_bytes"], record["bytes"])


class PlantedFaults(Case):
    def test_missing_asset(self):
        self.asset().unlink()
        self.assert_fails("blocks.bin.xz: cannot read")

    def test_changed_asset_byte(self):
        data = bytearray(self.asset().read_bytes())
        data[len(data) // 2] ^= 1
        self.replace_asset(bytes(data), commit=False)
        self.assert_fails("size or the SHA-256 is not the committed value")
        self.assertFalse(self.restored().exists())

    def test_download_of_other_bytes(self):
        self.assert_fails("size or the SHA-256 is not the committed value", ["--output", str(self.output)],
                          lambda url, size, timeout: xz(b"other"))

    def test_asset_is_not_xz(self):
        self.replace_asset(b"not an xz stream")
        self.assert_fails("not an xz stream")

    def test_truncated_asset(self):
        self.replace_asset(self.asset().read_bytes()[:-8])
        self.assert_fails("not an xz stream|does not decompress to exactly")

    def test_bytes_after_the_stream(self):
        self.replace_asset(self.asset().read_bytes() + b"\x00")
        self.assert_fails("does not decompress to exactly")

    def test_longer_content(self):
        self.replace_asset(xz((self.fixture / fb.BLOCKS_FILE).read_bytes() + b"\x00"))
        self.assert_fails("does not decompress to exactly")

    def test_shorter_content(self):
        self.replace_asset(xz((self.fixture / fb.BLOCKS_FILE).read_bytes()[:-1]))
        self.assert_fails("does not decompress to exactly")

    def test_other_content_of_the_same_size(self):
        content = bytearray((self.fixture / fb.BLOCKS_FILE).read_bytes())
        content[100] ^= 1
        self.replace_asset(xz(bytes(content)))
        self.assert_fails("decompressed file does not have the committed SHA-256")
        self.assertFalse(self.restored().exists())

    def test_committed_hashes_of_a_block_that_fails_its_checks(self):
        # release.json commits to a blocks file in which one transaction byte differs.
        content = bytearray((self.fixture / fb.BLOCKS_FILE).read_bytes())
        content[-1] ^= 1
        self.replace_asset(xz(bytes(content)))
        self.record().update(sha256=hashlib.sha256(bytes(content)).hexdigest())
        self.write_release()
        self.assert_fails(f"range {NAME}: .*Merkle root mismatch")

    def test_other_heights_in_the_release_file(self):
        for key, value in (("first", tfb.BASE + 1), ("last", tfb.BASE + 5), ("blocks", 4)):
            original = self.entry[key]
            self.entry[key] = value
            self.write_release()
            self.assert_fails("release.json gives")
            self.entry[key] = original

    def test_malformed_release_file(self):
        good = json.loads(json.dumps(self.release))

        def changed(change):
            release = json.loads(json.dumps(good))
            change(release)
            return release

        cases = [
            lambda r: r.update(format="dogelib-block-assets/0"),
            lambda r: r.update(repository="owner"),
            lambda r: r.update(repository="owner/repo/../other"),
            lambda r: r.update(tag="a/b"),
            lambda r: r.update(ranges=[]),
            lambda r: r["ranges"].append(r["ranges"][0]),
            lambda r: r["ranges"][0].update(name="../outside"),
            lambda r: r["ranges"][0].update(blocks=True),
            lambda r: r["ranges"][0]["files"].pop(fb.MANIFEST_FILE),
            lambda r: r["ranges"][0]["files"][fb.BLOCKS_FILE].update(asset="dir/asset.xz"),
            lambda r: r["ranges"][0]["files"][fb.BLOCKS_FILE].update(sha256="00"),
            lambda r: r["ranges"][0]["files"][fb.BLOCKS_FILE].update(asset_bytes=-1),
        ]
        for change in cases:
            self.release = changed(change)
            self.write_release()
            self.assert_fails("release.json: ")
        self.release_file.write_text("{")
        self.assert_fails("cannot read")
        self.assertFalse(self.output.exists())

    def test_pack_refuses_a_bad_fixture_and_a_bad_name(self):
        with self.assertRaisesRegex(frb.AssetError, "range name"):
            frb.pack(self.fixture, "a/b", self.assets, PINS)
        data = bytearray((self.fixture / fb.BLOCKS_FILE).read_bytes())
        data[-1] ^= 1
        (self.fixture / fb.BLOCKS_FILE).write_bytes(bytes(data))
        with self.assertRaisesRegex(frb.AssetError, "SHA256SUMS mismatch"):
            frb.pack(self.fixture, NAME, self.assets, PINS)


class Response:
    def __init__(self, data: bytes):
        self.data = data

    def __enter__(self):
        return self

    def __exit__(self, *args):
        return False

    def read(self, size: int) -> bytes:
        return self.data[:size]


class Download(unittest.TestCase):
    def test_body_within_the_size(self):
        with mock.patch.object(frb.urllib.request, "urlopen", return_value=Response(b"12345")) as urlopen:
            self.assertEqual(frb.download("https://host.invalid/a", 5, 3.0), b"12345")
        urlopen.assert_called_once_with("https://host.invalid/a", timeout=3.0)

    def test_body_above_the_size(self):
        with mock.patch.object(frb.urllib.request, "urlopen", return_value=Response(b"123456")):
            with self.assertRaisesRegex(frb.AssetError, "more than 5 bytes"):
                frb.download("https://host.invalid/a", 5, 3.0)

    def test_failure_after_every_attempt(self):
        error = urllib.error.URLError("unreachable")
        with mock.patch.object(frb.urllib.request, "urlopen", side_effect=error) as urlopen:
            with self.assertRaisesRegex(frb.AssetError, f"failed after {frb.ATTEMPTS} attempts: URLError"):
                frb.download("https://host.invalid/a", 5, 3.0)
        self.assertEqual(urlopen.call_count, frb.ATTEMPTS)

    def test_success_after_a_failure(self):
        results = [urllib.error.URLError("unreachable"), Response(b"1")]
        with mock.patch.object(frb.urllib.request, "urlopen", side_effect=results):
            self.assertEqual(frb.download("https://host.invalid/a", 5, 3.0), b"1")


if __name__ == "__main__":
    unittest.main()
