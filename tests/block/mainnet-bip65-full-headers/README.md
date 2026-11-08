# Mainnet full headers: bip65

`headers.txt` contains heights 3464739–3464760, including each AuxPoW payload when the version has bit 8 set.
Each line contains a decimal height, one space and the hexadecimal bytes of one full header.
The existing [pure fixture](../mainnet-bip65-headers/README.md) retains the same heights and bytes.

## Provenance (D82)

The primary source is `dogecoin.stackwallet.com`, TCP port `50022`, with TLS.
The fetch date is 2026-11-07 (UTC).
A second fetch from `electrum2.cipig.net`, TCP port `20060`, with TLS, returned identical complete response bytes on that date.
Both connections used this newline-terminated handshake, followed by the header request:

```json
{"id":0,"method":"server.version","params":["DogeLib-fixtures","1.4"]}
{"id":1,"method":"blockchain.block.headers","params":[3464739,22]}
```

Both responses reported `result.count = 22`.
The fetch split `result.hex` with the independent base-transaction and AuxPoW reader in `scripts/check_full_headers.py`.
The split consumed every response byte.
No fixture byte comes from DogeLib or the Core harness.
The servers are untrusted sources of public chain data.

The anchor is height 3464751, display hash `34cd2cbba4ba366f47e5aa0db5f02c19eba2adf679ceb6653ac003bdc9a0ef1f`.
The [pure fixture README](../mainnet-bip65-headers/README.md) records its pinned Core source and the limits of its authentication.
The anchor authenticates its backward links, but does not authenticate headers after it.
Two-server agreement and `SHA256SUMS` pin the fetched bytes, without establishing every consensus rule.

## Checks

Run these commands from the repository root:

```bash
python3 -I scripts/check_full_headers.py
(cd tests/block/mainnet-bip65-full-headers && sha256sum -c SHA256SUMS)
```

The Python check compares every 80-byte prefix with the existing pure fixture and checks all predecessor links and the anchor hash.
It parses each base coinbase transaction, both Merkle branches, both indices and the parent header through the exact record boundary.
The check also compares the work-bearing header's `hashlib.scrypt` digest with the child target.
It does not check AuxPoW commitments or execute header-sequence validation.
`lake test` runs single steps of `acceptBlockHeader` and sequences of `processNewBlockHeaders` on these headers (`tests/KnownAnswers/HeaderSequence.lean`, `checkMainnetSteps` and `checkMainnetSequences`).
No oracle or comparator consumes them yet.

Core revision `e0a1c157791544e818c901bd9341896965afbf9d` fixes the layouts in `src/primitives/pureheader.h:29-54` and `src/auxpow.h:79-85,153-160`.
The work check follows `src/dogecoin.cpp:101-119` and `src/pow.cpp:115-129` at that revision.
Licence: public chain data.
Core references use the [Dogecoin Core MIT licence](../../../LICENSES/dogecoin-core-MIT.txt).
