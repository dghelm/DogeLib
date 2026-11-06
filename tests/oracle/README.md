# Oracle fixtures

`requests.jsonl` holds 312 requests to `dogelib-oracle`, and `expected.jsonl` holds the expected response on the same line.
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
| `work-d16-*` | Core D16, `src/test/arith_uint256_tests.cpp`, `bignum_SetCompact`, lines 412–538. The literal magnitudes, flags and compact results come from Core's assertions. The final overflow has magnitude zero because its shift discards all bits (D13). `work-d16-direct-80` is the assignment at line 490. |
| `work-d7-*` | Core D7, `src/test/dogecoin_tests.cpp`, the six `get_next_work_*` cases, lines 123–210. Inputs and expected compact results are Core's literals. |
| `work-null-*` | D17, null-tip return, and D14, network `powLimit`. Mainnet and testnet encode as `0x1e0fffff`. Regtest encodes as `0x207fffff`. |
| `work-view-*` | `Work.validateWorkView` and `Work.getNextWorkRequiredFromView`: height bounds, adjacency checks and missing history. These typed adapter errors have no Core consensus counterpart. |
| `work-request-*` | Argument rules of `docs/oracle.md`, with unknown fields, missing fields, wrong types, fractional numbers and range endpoints. |
| The other ids, and requests with no `id` | Request errors and the `id` rules of `docs/oracle.md`. `dup-a` repeats a key: Lean core's parser keeps the last value. |

`scripts/test_oracle.py` also sends two of Core's corpora to the oracle.
Each record of `sighash.json` must give Core's digest.
Each base-mode record of `tx_valid.json` and `tx_invalid.json` must give its own bytes back, and the ID that `hashlib` computes.

Every record of both transaction corpus files also passes through `tx.read_witness` and `tx.decode_witness`.
The test separates base fields and witness stacks directly from the known bytes, by D4's field layout.
It checks the stacks, `has_witness`, serialization, both hashes and the prefix consumption.
The hashes come from Python's `hashlib`.

## Hash and block operations

The `/4` fixtures add empty hash inputs, an empty Merkle list and raw zero-header encoding.
Empty hash digests come from the committed hash vectors and their documented published sources.
Core's `MerkleComputation` defines the empty root and mutation flag (SOURCES.md D42).
The zero header bytes and numeric-notation case follow the six-field layout in D10.
Request-error fixtures cover missing, unknown, malformed and out-of-range fields, including nested header fields and exact leaf lengths.
Header truncation fixtures use D10's 80-byte layout and D21's stream error.

`scripts/oracle_hash_block.py` supplies fixture requests to the oracle tests and Core comparison.
It reads all 315 recorded headers, their expected hash links, the 34 Merkle cases and three mainnet transaction-ID lists.
It also reads the committed hash fixtures, including generated million-byte messages from their recorded encodings.
Their expectations retain the provenance in `tests/block/README.md` and the cryptography fixture READMEs.
The helper never calls DogeLib to produce an expectation.

The SHA-1 cases include all 129 NIST short and long vectors and ten Core messages from `src/test/crypto_tests.cpp`, lines 220–233.
Core's numerical expectations retain the MIT terms in `LICENSES/dogecoin-core-MIT.txt`.
The input construction reuses the recorded RIPEMD-160 messages, except Core's algorithm-specific sentence.
That sentence is fixture data, not a SHA-1 security claim.
The Core notice is:

```text
Copyright (c) 2014-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
```

For all 100 NIST Monte Carlo checkpoints, hashlib derives the final 60-byte input independently.
The oracle must return NIST's expected checkpoint digest for that input.
This fixture comparison does not chain the oracle's intermediate digests.
`lake test` checks the full chain separately.

## Script operations

The `script-read-*` fixtures follow `GetOp2` (SOURCES.md D24), with exact push bytes and failure cursors read from its branches.
The `script-eval-*` fixtures follow `EvalScript` (D3): stack effects, false-top acceptance, `OP_RETURN`, skipped signature opcodes and unsupported capabilities.
Request errors follow the argument rules in [the oracle format](../../docs/oracle.md#script-arguments-and-results).
`scripts/test_oracle.py` also checks eighteen generated adapter resource boundaries, with expectations from the documented limits.
These fixtures do not treat Core's spending corpus expectations as individual `EvalScript` results.

## Legacy Script verification

The `/6` fixtures select `base` for CHECKSIG, zero-of-zero multisig with a nonempty dummy, and CLTV.
D25's `BaseSignatureChecker` returns false for signatures and lock times.
D3's multisig branch accepts a nonempty dummy without NULLDUMMY and rejects it with `SIG_NULLDUMMY` under NULLDUMMY.
The P2SH fixture spends a push of `OP_1` against its HASH160 template (D3, D48).
Python hashlib supplies that digest independently.

The transaction-checker fixture supplies a nonempty signature and a 33-byte compressed public-key encoding.
It reaches the unavailable verifier and reports `signature_verifier`, without a spend verdict.
The key encoding need not represent a curve point for this unsupported result.
The remaining cases follow the `/6` argument, complete-decoding and index contracts in `docs/oracle.md`.
