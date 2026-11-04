# Oracle fixtures

`requests.jsonl` holds 106 requests to `dogelib-oracle`, and `expected.jsonl` holds the expected response on the same line.
`scripts/test_oracle.py` compares them, with two exceptions.
It compares a `request` error by kind only.
An expected `preimage_hex` of `"*"` requires a preimage whose double SHA-256 is the digest.
`docs/oracle.md` defines the format.

No expected value comes from the oracle. The sources, by the `id` of the request:

| `id` | Source of the expected value |
| --- | --- |
| `version` | `docs/oracle.md` |
| `cs-encode-*` | The forms of `WriteCompactSize` (D1). A value below 253 is one byte. Below 2^16 it is `fd` and 2 bytes, below 2^32 `fe` and 4 bytes, and otherwise `ff` and 8 bytes, little-endian. Written by hand for 252, 253, 65536, 2^53 + 1 and 2^64 − 1. |
| `cs-read-*` | `ReadCompactSize` (D1) and `CDataStream::read` (D21): the non-canonical check, then the `MAX_SIZE` check against `0x02000000`, and truncation as "end of data". |
| `tx-decode`, `tx-read-prefix` | The smallest base-mode record of Core's `tx_valid.json` (D28, record 98 of the vendored file). The fields were read from its bytes by hand, in the order of `CTransaction`'s serialization (D4). Its ID is the double SHA-256 of the bytes, computed with Python's `hashlib`, and reversed for display (D11). |
| `tx-decode-trailing`, `tx-decode-truncated`, `tx-decode-too-many-inputs` | The same bytes with one extra byte, cut to 10 bytes, and a version followed by the input count `fe 01 00 00 02`, which is above `MAX_SIZE`. |
| `sighash-458`, `sighash-458-unsigned` | Record 458 of Core's `sighash.json` (D26), with its hash type −107131905, and again with the same value plus 2^32. Both expect Core's digest. |
| `sighash-index-*`, `sighash-single-past-outputs` | Core's `SignatureHash` (D3, `src/script/interpreter.cpp` lines 1225 to 1235) returns `uint256S("00…01")` when `nIn` names no input, or no output under `SIGHASH_SINGLE`. That value is `01` followed by 31 zero bytes in serialization order. The transaction with two inputs and one output was written by hand. `5.0`, `5e0` and `50e-1` are the integer 5 by the rule of `docs/oracle.md`. |
| `sighash-bad-tx` | `00` is one byte of a 4-byte version: truncated. |
| `witness-*` except `witness-request-*` | Hand-built cases following D4, `UnserializeTransaction`, `SerializeTransaction` and `HasWitness`, and D23, `GetWitnessHash`. The flag and error-order cases follow `tests/KnownAnswers.lean`, `Witness.cases`, with a zero outpoint. The input has an empty script and sequence `0xffffffff`. The output has value 0 and an empty script. Stacks include `ab`, an empty item, and no items. Empty stacks normalize to base serialization. Python's `hashlib` computes `txid` from the base form and `wtxid` from the extended form when a stack is not empty. Otherwise `wtxid` hashes the base form. Prefix and trailing-byte expectations follow the consumed lengths. |
| The other ids, and requests with no `id` | Request errors and the `id` rules of `docs/oracle.md`. `dup-a` repeats a key: Lean core's parser keeps the last value. |

`scripts/test_oracle.py` also sends two of Core's corpora to the oracle.
Each record of `sighash.json` must give Core's digest.
Each base-mode record of `tx_valid.json` and `tx_invalid.json` must give its own bytes back, and the ID that `hashlib` computes.

Every record of both transaction corpus files also passes through `tx.read_witness` and `tx.decode_witness`.
The test separates base fields and witness stacks directly from the known bytes, by D4's field layout.
It checks the stacks, `has_witness`, serialization, both hashes and the prefix consumption.
The hashes come from Python's `hashlib`.
