# Mainnet headers from genesis for median-time-past known answers

`headers.txt` contains the 13 raw 80-byte Dogecoin mainnet headers at heights 0–12.
Each line contains a decimal height, one space and the header as 160 hexadecimal digits.
The layout is the same as in [`../mainnet-headers`](../mainnet-headers/README.md).
The file is about 2 KiB, so tests need no network access.

## Source

The source is the public Electrum server `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
The fetch date is 2026-11-07 (UTC).
One newline-terminated JSON-RPC request fetched the range:

```json
{"id":1,"method":"blockchain.block.headers","params":[0,13]}
```

The response's `result.hex` contained the concatenated raw headers, and `result.count` was 13.
The fixture splits those bytes into 80-byte records and prefixes each record with its height.
The bytes are raw headers from that response, not headers rebuilt from explorer fields.

On the same date, a second public Electrum server, `electrum2.cipig.net`, TCP port `20060`, with TLS, returned the same 13 headers byte for byte.
That server requires a `server.version` request before the header request.
For a repeat fetch, send the request above over a TLS connection to either host and port.
The test never fetches data or overwrites expectations.

The sources are untrusted.
An independent Python `hashlib` check confirmed all predecessor links and the genesis hash before the fixture entered the repository.
`lake test` repeats those checks through DogeLib's compiled `Sha256d.hash`.

Licence: the headers are public chain data, not server software or explorer text.
The genesis hash comes from MIT-licensed Dogecoin Core at the pin below.
Core's licence is in [`LICENSES/dogecoin-core-MIT.txt`](../../../LICENSES/dogecoin-core-MIT.txt).

## Checks and coverage

Core `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d`, supplies these references:

- D10, `src/primitives/pureheader.h`, lines 29–54: version, previous hash, Merkle root, time, bits and nonce, in serialization order.
- D9, `src/chainparams.cpp`, lines 160 and 182: the mainnet genesis hash `1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691`, as an assertion and as checkpoint 0.
- D18, `src/chain.h`, lines 284–298: `GetMedianTimePast`, which collects at most 11 times, sorts them and returns the element at index `count / 2`.

`lake test` requires exactly these heights and record count.
It parses every header field, hashes each header and checks all 12 predecessor links.
It requires the null previous hash at height 0, and compares the genesis hash in reversed display order.
It requires that the times increase strictly from height 0 to height 12.

For each height `h` from 0 to 12, the view holds the headers from `h` down to 0, newest first.
The expected median is the time of the header at the height in the table below.
The table comes by hand from the strict order of the times and from D18.
The `min(11, h + 1)` collected times are already in order, so index `count / 2` selects a height.
The values are not computed by DogeLib.

| `h` | Times collected | Count | Index | Median: time at height |
| ---: | --- | ---: | ---: | ---: |
| 0 | 0 | 1 | 0 | 0 |
| 1 | 0–1 | 2 | 1 | 1 |
| 2 | 0–2 | 3 | 1 | 1 |
| 3 | 0–3 | 4 | 2 | 2 |
| 4 | 0–4 | 5 | 2 | 2 |
| 5 | 0–5 | 6 | 3 | 3 |
| 6 | 0–6 | 7 | 3 | 3 |
| 7 | 0–7 | 8 | 4 | 4 |
| 8 | 0–8 | 9 | 4 | 4 |
| 9 | 0–9 | 10 | 5 | 5 |
| 10 | 0–10 | 11 | 5 | 5 |
| 11 | 1–11 | 11 | 5 | 6 |
| 12 | 2–12 | 11 | 5 | 7 |

The odd heights from 1 to 9 give even counts.
For them, the expected value is the upper median, and the lower median is a different, smaller time.

Chain acceptance gives a second expected result.
`ContextualCheckBlockHeader` rejects a header whose time is at most the median time past of its predecessor (`src/validation.cpp`, D33, lines 3103–3104).
Mainnet accepted the headers at heights 1–12, so each time must be greater than the median of the view below it.

The test also requires the adapter error `shortView` for views that lack required history.
An example is the view at height 12 without its last two entries.
It requires that the view at height 12 truncated to its first 11 entries gives the same median as the full view.

The genesis hash anchors only height 0.
The headers at heights 1–12 link forward from genesis, so the genesis hash does not authenticate them.
Their provenance relies on the two public sources, and the fixture digest pins their bytes.
These checks do not establish proof of work, full header validity or agreement with compiled Core.

`SHA256SUMS` pins `headers.txt`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
