# Mainnet headers around BIP65Height

`headers.txt` contains the 22 raw 80-byte Dogecoin mainnet pure headers at heights 3464739–3464760.
Each line contains a decimal height, one space and the header as 160 hexadecimal digits.
The layout is the same as in [`../../work/mainnet-headers`](../../work/mainnet-headers/README.md).
The headers give real contexts for the contextual header check around `BIP65Height`, 3464751.

## Source

The source is the public Electrum server `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
The fetch date is 2026-11-07 (UTC).
One newline-terminated JSON-RPC request fetched the range:

```json
{"id":1,"method":"blockchain.block.headers","params":[3464739,22]}
```

The response's `result.count` was 22.
Its `result.hex` contained each raw header, followed by its AuxPoW payload when bit 8 of the version is set.
So the server does not return 80-byte pure headers at AuxPoW heights.

An independent Python script split the bytes into records.
After each header with bit 8 set, it skipped one payload in the serialization of `CAuxPow` (D54, `src/auxpow.h`).
That payload is a `CMerkleTx`, the chain Merkle branch, the chain index and the 80-byte parent header.
The script consumed every byte of the response and found exactly 22 headers.
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

## Checks and coverage

Core `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d`, supplies these references:

- D10, `src/primitives/pureheader.h`, lines 29–54: the six header fields in serialization order. Lines 88–95: `GetBaseVersion`.
- D14, `src/chainparams.cpp`, line 86: `BIP65Height`, with the comment hash `34cd2cbba4ba366f47e5aa0db5f02c19eba2adf679ceb6653ac003bdc9a0ef1f`, "first v4 block after the last v3 block".
- D33, `src/validation.cpp`, lines 3066–3119: `ContextualCheckBlockHeader`.

`lake test` requires exactly these heights, parses each header, checks the 21 predecessor links and compares the hash at 3464751 in display order.
The comment hash is the hash of the block at 3464751.
It anchors the headers at 3464739–3464751, because their links lead to it.
The headers at 3464752–3464760 link forward from it, so their provenance relies on the two public sources, and the fixture digest pins their bytes.

The header at 3464750 has the version `0x00620103`, with base version 3, and every other header has `0x00620104`.

Chain acceptance gives the expected results.
Mainnet accepted each header.
So checks 1, 2, 3, 5 and 7 of `ContextualCheckBlockHeader` pass for every candidate with 11 predecessors in the fixture, from 3464750.
The test chooses the adjusted time and the known checkpoints, and derives the results of checks 4 and 6 by hand from D33.
The version mutations at 3464750 and 3464751 and their expected results are in `tests/KnownAnswers/ContextualCheck.lean`.
These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.

`SHA256SUMS` pins `headers.txt`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
