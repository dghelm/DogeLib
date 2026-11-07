#!/usr/bin/env python3
"""Check full mainnet header boundaries, pure bytes, links and pinned anchors."""

import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RANGES = (
    ('auxpow-activation', 371320, 371340, 371337,
     '60323982f9c5ff1b5a954eac9dc1269352835f47c2c5222691d80f0d50dcf053'),
    ('bip66', 1032483, 1034390, 1032483,
     '80d1364201e5df97e696c03bdd24dc885e8617b9de51e453c10a4f629b1e797a'),
    ('bip65', 3464739, 3464760, 3464751,
     '34cd2cbba4ba366f47e5aa0db5f02c19eba2adf679ceb6653ac003bdc9a0ef1f'),
)


def sha256d(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


class Reader:
    """Read the base transaction and CAuxPow layout without DogeLib code."""

    def __init__(self, data):
        self.data = data
        self.pos = 0

    def take(self, size):
        end = self.pos + size
        if end > len(self.data):
            raise ValueError('truncated payload')
        value = self.data[self.pos:end]
        self.pos = end
        return value

    def compact(self):
        tag = self.take(1)[0]
        if tag < 253:
            return tag
        width = {253: 2, 254: 4, 255: 8}[tag]
        value = int.from_bytes(self.take(width), 'little')
        if value < {253: 253, 254: 65536, 255: 4294967296}[tag]:
            raise ValueError('nonminimal CompactSize')
        if value > 0x02000000:
            raise ValueError('oversized CompactSize')
        return value

    def script(self):
        self.take(self.compact())

    def full_header(self):
        start = self.pos
        pure = self.take(80)
        if int.from_bytes(pure[:4], 'little') & 256:
            self.take(4)  # Coinbase transaction version, base serialization.
            inputs = self.compact()
            if inputs != 1:
                raise ValueError('expected one coinbase input')
            if self.take(36) != bytes(32) + bytes.fromhex('ffffffff'):
                raise ValueError('expected coinbase outpoint')
            self.script()
            self.take(4)
            for _ in range(self.compact()):
                self.take(8)
                self.script()
            self.take(4)  # Transaction lock time.
            self.take(32)  # CMerkleTx.hashBlock.
            self.take(32 * self.compact())
            self.take(4)
            self.take(32 * self.compact())
            self.take(4)
            self.take(80)  # Parent pure header.
        return self.data[start:self.pos]


def check():
    total = 0
    for name, first, last, anchor_height, anchor_hash in RANGES:
        base = ROOT / 'tests/block' / f'mainnet-{name}-headers'
        full = ROOT / 'tests/block' / f'mainnet-{name}-full-headers'
        pure_rows = base.joinpath('headers.txt').read_text().splitlines()
        rows = full.joinpath('headers.txt').read_text().splitlines()
        if len(rows) != last - first + 1 or len(rows) != len(pure_rows):
            raise ValueError(f'{name}: wrong count')
        previous = None
        for height, row, pure_row in zip(range(first, last + 1), rows, pure_rows):
            number, raw = row.split()
            pure_number, pure_hex = pure_row.split()
            data = bytes.fromhex(raw)
            reader = Reader(data)
            if reader.full_header() != data or reader.pos != len(data):
                raise ValueError(f'{name}/{height}: trailing bytes')
            if int(number) != height or number != pure_number or data[:80].hex() != pure_hex:
                raise ValueError(f'{name}/{height}: pure header mismatch')
            digest = sha256d(data[:80])
            if previous is not None and data[4:36] != previous:
                raise ValueError(f'{name}/{height}: broken predecessor link')
            if height == anchor_height and digest[::-1].hex() != anchor_hash:
                raise ValueError(f'{name}: wrong anchor')
            # Check the work-bearing pure header, without asserting AuxPoW commitments.
            work_header = data[-80:] if int.from_bytes(data[:4], 'little') & 256 else data[:80]
            bits = int.from_bytes(data[72:76], 'little')
            exponent, mantissa = bits >> 24, bits & 0x7fffff
            target = mantissa << (8 * (exponent - 3)) if exponent >= 3 else mantissa >> (8 * (3 - exponent))
            if bits & 0x800000 or target == 0 or target >= 2**256:
                raise ValueError(f'{name}/{height}: invalid target')
            work = hashlib.scrypt(work_header, salt=work_header, n=1024, r=1, p=1, dklen=32)
            if int.from_bytes(work, 'little') > target:
                raise ValueError(f'{name}/{height}: insufficient scrypt work')
            previous = digest
            total += 1
    print(f'Full headers: {total} records, exact splits, pure bytes, links, anchors and scrypt work passed')


if __name__ == '__main__':
    check()
