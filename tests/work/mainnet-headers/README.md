# Mainnet headers for next-work known answers

`headers.txt` contains 312 raw 80-byte Dogecoin mainnet headers at heights 144719–145030.
Each line contains a decimal height, one space and the header as 160 hexadecimal digits.
The heights make gaps and the checkpoint position visible without duplicate hashes or JSON metadata.
The file is about 52 KiB, so tests need no network access.

## Source

The source is the public Electrum server `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
The fetch date is 2026-11-04 (UTC).
One newline-terminated JSON-RPC request fetched the range:

```json
{"id":1,"method":"blockchain.block.headers","params":[144719,312]}
```

The response's `result.hex` contained the concatenated raw headers, and `result.count` was 312.
The fixture splits those bytes into 80-byte records and prefixes each record with its height.
The bytes are raw headers from that response, not headers rebuilt from explorer fields.
For a repeat fetch, send the request above over a TLS connection to that host and port.
The test never fetches data or overwrites expectations.

The source is untrusted.
An independent Python `hashlib` check confirmed all predecessor links and checkpoint 145000 before the fixture entered the repository.
`lake test` repeats those checks through DogeLib's compiled `Sha256d.hash`.
Those checks connect the ancestors to Core's checkpoint rather than rely on the server's claims.

Licence: the headers are public chain data, not server software or explorer text.
The checkpoint value comes from MIT-licensed Dogecoin Core at the pin below.
Core's licence is in [`LICENSES/dogecoin-core-MIT.txt`](../../../LICENSES/dogecoin-core-MIT.txt).

## Checks and coverage

Core `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d`, supplies these references:

- D10, `src/primitives/pureheader.h`, lines 29–54: version, previous hash, Merkle root, time, bits and nonce, in serialization order.
- D9, `src/chainparams.cpp`, line 184: mainnet checkpoint 145000, `cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72`.
- D17, `src/pow.cpp`, lines 32–88: next-work selection, including the full interval lookback after the first retarget.
- D17, `src/pow.cpp`, lines 124–125: target range check, without the supplied-hash comparison.

`lake test` requires exactly these heights and record count.
It parses every header field, hashes each header, checks all 311 predecessor links and compares the checkpoint hash in reversed display order.
It requires target validity for every header with the mainnet parameters selected at that header's height.
It then calls `nextWorkRequired .mainnet` with a newest-first view of earlier headers and the candidate's own time.
The expected result is that candidate's `nBits` from the fixture.

| Branch | Candidate heights | Checks |
| --- | --- | ---: |
| Legacy difficulty copies | 144721–144959 and 144961–144999 | 278 |
| Interval-240 retarget | 144960 | 1 |
| DigiShield retargets | 145000–145030 | 31 |

The substantive retarget evidence is height 144960 plus 31 DigiShield blocks.
The range includes the last legacy retarget, its successor, heights 144990–145010 across activation, and twenty further DigiShield blocks.
Retarget 144960 needs ancestor 144719: 240 blocks before its predecessor at 144959.
Height 144719 supplies context only.
Retarget 144720 lacks its required ancestor, so the test requires `missingAncestor` rather than compares `nBits`.

The checkpoint anchors headers through 145000 by their hash links, subject to the hash commitment assumption.
It does not authenticate the later headers, whose provenance still relies on the public source.
Those headers link forward from the checkpoint.
The fixture digest pins their bytes.

These headers supply finite known answers, not an equivalence theorem or a comparison with compiled Core.
The checks do not establish proof of work, AuxPoW validity, full header validity or validity of any transaction.
The fixture contains no AuxPoW data.

`SHA256SUMS` pins `headers.txt`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
