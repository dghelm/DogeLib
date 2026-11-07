# Mainnet headers up to BIP66Height

`headers.txt` contains the 1908 raw 80-byte Dogecoin mainnet pure headers at heights 1032483–1034390.
Each line contains a decimal height, one space and the header as 160 hexadecimal digits.
The layout is the same as in [`../../work/mainnet-headers`](../../work/mainnet-headers/README.md).
The headers give real contexts for the contextual header check around `BIP66Height`, 1034383.
The file is about 315 KiB, because the range starts at the block that the anchor hash identifies.

## Source

The source is the public Electrum server `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
The fetch date is 2026-11-07 (UTC).
One newline-terminated JSON-RPC request fetched the range:

```json
{"id":1,"method":"blockchain.block.headers","params":[1032483,1908]}
```

The response's `result.count` was 1908.
Its `result.hex` contained each raw header, followed by its AuxPoW payload when bit 8 of the version is set.
So the server does not return 80-byte pure headers at AuxPoW heights.

An independent Python script split the bytes into records.
After each header with bit 8 set, it skipped one payload in the serialization of `CAuxPow` (D54, `src/auxpow.h`).
That payload is a `CMerkleTx`, the chain Merkle branch, the chain index and the 80-byte parent header.
The script consumed every byte of the response and found exactly 1908 headers.
The fixture keeps the first 80 bytes of each record and prefixes each record with its height.
No contextual check reads the AuxPoW payload, so the fixture omits it.

On the same date, a second public Electrum server, `electrum2.cipig.net`, TCP port `20060`, with TLS, returned the same response bytes.
That server requires a `server.version` request before the header request.
For a repeat fetch, send the request above over a TLS connection to either host and port.
The test never fetches data or overwrites expectations.

The sources are untrusted.
Before the fixture entered the repository, an independent Python `hashlib` check confirmed every predecessor link and the anchor hash.
`lake test` repeats those checks through DogeLib's compiled `PureBlockHeader.getHash`.

Licence: the headers are public chain data, not server software or explorer text.
The anchor hash comes from MIT-licensed Dogecoin Core at the pin below.
Core's licence is in [`LICENSES/dogecoin-core-MIT.txt`](../../../LICENSES/dogecoin-core-MIT.txt).

## The anchor

Core's `BIP34Hash` and the comment on `BIP66Height` give the hash `80d1364201e5df97e696c03bdd24dc885e8617b9de51e453c10a4f629b1e797a` (D14, `src/chainparams.cpp`, lines 85 and 87).
Both sit next to the height 1034383.
The hash is not the hash of the block at 1034383.
It is the hash of the block at 1032483, 1900 blocks earlier, and that block has the version `0x00620103`.

The block at 1034383 has the hash `251f53c3e66f122347b7667c45aaadfffb52c2a05b8c80edcce68450b639f7f6`.
The fixture starts at 1032483, so that its predecessor links connect the anchor to the headers around 1034383.
No contextual check reads either hash, and the code uses only the height 1034383.

## Checks and coverage

Core `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d`, supplies these references:

- D10, `src/primitives/pureheader.h`, lines 29–54: the six header fields in serialization order. Lines 88–95: `GetBaseVersion`.
- D14, `src/chainparams.cpp`, lines 85–87: `BIP34Hash`, `BIP65Height` and `BIP66Height`.
- D33, `src/validation.cpp`, lines 3066–3119: `ContextualCheckBlockHeader`.

`lake test` requires exactly these heights, parses each header, checks the 1907 predecessor links and compares the hash at 1032483 in display order.
The anchor authenticates only the block at 1032483.
The later headers link forward from it, so their provenance relies on the two public sources, and the fixture digest pins their bytes.

The headers at 1034382 and 1034383 have the version `0x00620103`, with base version 3.

Chain acceptance gives the expected results.
Mainnet accepted each header.
So checks 1, 2, 3, 5 and 7 of `ContextualCheckBlockHeader` pass for every candidate with 11 predecessors in the fixture, from 1032494.
The test chooses the adjusted time and the known checkpoints, and derives the results of checks 4 and 6 by hand from D33.
The version mutations at 1034382 and 1034383 and their expected results are in `tests/KnownAnswers/ContextualCheck.lean`.
These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.

`SHA256SUMS` pins `headers.txt`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
