# The Core harness and comparators

This document describes the Dogecoin Core harness, its boundary with `dogelib-oracle`, its response projections and the comparison tools.
See [docs/oracle.md](oracle.md) for the `dogelib-oracle/1` wire format and [docs/comparison-evidence.md](comparison-evidence.md) for recorded comparison counts and replays.
See [docs/soundness/oracle-and-harness.md](soundness/oracle-and-harness.md) for the Gap B4 trust boundaries.

## Operation boundary

- Boundary:
  - The comparison and campaign drivers invoke both the Lean oracle and the Core harness over JSONL.
  - Both executables live in this repository and run as separate operating-system processes.
- Owns:
  - The oracle specification owns the `dogelib-oracle/1` wire format and its JSON record schema.
  - The Core harness owns the `dogelib-oracle/1-core-projection` format and its build stamp.
  - The block-validation layer owns the `dogelib-coins/1` snapshot record layout and manifest fields.
  - The caller owns request streams, network choices, `u32` and `u64` inputs, and data files.
- Operations:
  - The oracle answers 36 pure and stateful operations over `dogelib-oracle/1` on standard input.
  - The proposal executable adds revision hooks for block validation and contextual body checks.
  - The Core harness answers 35 operations through pinned Dogecoin Core C++ code on each request.
  - The comparator self-test wraps the oracle as a stand-in harness and injects response mutations.
- Laws:
  - On supported inputs in the comparison domain, both programs agree on verdicts and digests.
  - No machine-checked theorem equates the Lean specification, the compiled binary or the Core C++ binary.
  - The trust model documents the foreign boundary, compiler, runtime and digest-collision assumptions.
- Failure:
  - A response object carries either an `ok` result or an `error`. Its `kind` selects its other fields ([errors](oracle.md#errors)). For example, a request error has a free-text `message` and no `reason`.
  - A serialization error in a block stops evaluation before any consensus check of that block.
    `block.validate` reads and validates its blocks one at a time, from `blocks_hex` or from `blocks_file`. So a decoding error in a later block can come after the consensus checks of earlier blocks.
  - Adapter errors report resource, view or domain limits and are separate from consensus rejection.
  - An unmapped Core exception or mismatch ends the harness with exit status 3 and fails the run.
  - Outside checked flag-dependency refusals, any request error from either program fails comparison.
- Guarantees:
  - Agreement shows that the compiled Lean binary and Core match on the compared requests.
  - Agreement covers only the tested stream and does not imply equivalence on untested inputs.
  - An unsupported Lean capability excludes verdict comparison and implies no consensus rejection.
- Assumes:
  - Both programs run against the pinned Core revision, Boost 1.70.0 and generic scrypt without SSE2.
  - Snapshot comparisons assume that the start snapshot matches Core's coin set at its height.
  - Double SHA-256 coin-set digests assume collision resistance to conclude equal coin sets.
  - Bisection assumes that each request produces the same response regardless of prior requests.
- Readings:
  - Core asserts script flag dependencies, so the harness refuses unsafe flags ([D3][d3-flags]).
  - Core adds `int64_t` amounts unchecked, so the oracle stops before overflow ([D114][d114-sums]).
  - Core adds 7,200 to adjusted time, so inputs stay at most `INT64_MAX - 7200` ([D72][d72-time]).
  - Witness serialization is wire-only because witness rules stay inactive ([D36][d36-witness]).

[d3-flags]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1508-L1520
[d114-sums]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1783-L2009
[d72-time]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/timedata.cpp
[d36-witness]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3002-L3008

## The Core harness

`harness/core/core_oracle.cpp` answers the same requests by running Dogecoin Core's own code.
It is built against Core v1.14.9 at commit `e0a1c15`, the pin in [SOURCES.md](../SOURCES.md).
`scripts/compare_core.py` runs the harness and the oracle on one stream of requests and requires their responses to agree.
CI runs workflow `core` with four jobs: `self-test`, `compare`, `csv-forced` and `impact`.
They run the comparator self-test, the Core comparison, the forced-CSV comparison of `RelativeLockTime` and the historical impact checks.

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle
python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The build also produces `core-signer`, a fixture generator that calls Core's `SignatureHash`, `CKey::Sign` and `VerifyScript`.
Its fixed private keys are public test data.
[Signed recovery-template fixtures](../tests/script/signed-spends/README.md) record its inputs, signatures, Core verdicts and reproduction commands.
`core-signer --fixed-digest` generates the [fixed-digest fixtures](../tests/script/signed-spends/README.md#fixed-digest-spends) of the same directory.
It runs outside the oracle comparison loop.

The build script exports the pinned commit from the clone with `git archive`.
The clone must contain that commit, but its working tree may be at any other.
It configures Core as `scripts/build_core_node.sh` does, with the daemon enabled and no wallet, GUI, tests or ZMQ.
It builds Core's server, common, utility, consensus, cryptography, UniValue, LevelDB and secp256k1 libraries, and never links `dogecoind`.
It needs autoconf, automake, libtool, pkg-config and the development files of OpenSSL and libevent (`libssl-dev` and `libevent-dev` on Ubuntu).

`scripts/core_boost.sh` supplies Boost 1.70.0 for both build scripts: it downloads the archive, checks its SHA-256 and builds five libraries into `<build-dir>/boost`.
`BOOST_ROOT` selects an installed Boost, and `BOOST_ARCHIVE` names a local copy of the archive.

The harness links the libraries of `dogecoind` in the order of `dogecoind_LDADD` (`src/Makefile.am`, lines 395 to 408), with Boost, OpenSSL and libevent.
`harness/core/core_validation.cpp` includes Core's `src/validation.cpp` and `src/timedata.cpp` as text.
The compiler sees both files unchanged, and the unit can name what they keep internal:

- The static function `AcceptBlockHeader`.
- The sets `gFailedBlocks` and `setDirtyBlockIndex` of the anonymous namespace.
- The static variable `nTimeOffset`.

The unit defines every symbol of both files, so the link takes neither `validation.o` nor `timedata.o` from the server library.
Its four functions contain no validation logic.
The server library brings in Core's network, RPC, database and memory-pool objects.
The harness runs none of that code: it opens no database, starts no thread and creates no data directory.

`core-signer` keeps its earlier link.
It uses the objects of `pow.cpp`, `chain.cpp`, `dogecoin.cpp`, `chainparams.cpp`, `chainparamsbase.cpp`, `auxpow.cpp` and `checkpoints.cpp`, compiled apart from the server library.
Function and data sections, with linker garbage collection, discard unrelated functions and their dependencies.
That link assumes GNU ld for `--gc-sections`, as Linux CI does.
These pinned sources supply the work functions and parameter constructors:

| Source | Role |
| --- | --- |
| [D17, `src/pow.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pow.cpp) | `GetNextWorkRequired` |
| [D35, `src/chain.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp) | `BuildSkip`, `GetAncestor` and the skip-height guard |
| [D6, `src/dogecoin.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp) | `CalculateDogecoinNextWorkRequired` and minimum-difficulty permission |
| [D14, `src/chainparams.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp) | Network parameter records, `SelectParams` and `GetConsensus` |
| [D67, `src/checkpoints.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/checkpoints.cpp) | `Checkpoints::GetLastCheckpoint` |
| [D39, `src/chainparamsbase.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparamsbase.cpp) | `SelectBaseParams`, called by `SelectParams` |

## What the harness runs

Each row maps one harness operation to the Dogecoin Core code it calls and to its citations in [SOURCES.md](../SOURCES.md).

| `op` | Core's code | Sources |
| --- | --- | --- |
| `auxpow.check` | `CAuxPow::check` on a payload that Core's stream code reads | D41 and D54, the full-header and payload readers. D55, `CAuxPow::check`. D6, `CheckAuxPowProofOfWork`. D14, `GetConsensus`. D33, only the two version gates, with D10's `IsLegacy` and `IsAuxpow`. `harness/core/auxpow_fixtures.inc` adapts D56's deterministic construction and runtime-mined cases, and checks their exact bytes and verdicts. |
| `block.check` | `SelectParams` for mainnet, then `CheckBlock` on a `CBlock` that Core's stream code reads from the request, with the two flags of the request. Then `GetLegacySigOpCount` for each transaction, `GetSerializeSize` in base mode and `GetHash` | D14, D21, D106, D108 |
| `block.check_pow` | `SelectParams`, `Params().GetConsensus(selection_height)`, then `CheckAuxPowProofOfWork` with generic scrypt | D41 and D54, the full-header and payload readers. D55, `CAuxPow::check`. D6, `CheckAuxPowProofOfWork`. D14, `GetConsensus`. D33, only the two version gates, with D10's `IsLegacy` and `IsAuxpow`. `harness/core/auxpow_fixtures.inc` adapts D56's deterministic construction and runtime-mined cases, and checks their exact bytes and verdicts. |
| `block.check_version` | `Params().GetConsensus(selection_height)` for `fAllowLegacyBlocks`, then the two version gates of `ContextualCheckBlockHeader` through Core's `IsLegacy` and `IsAuxpow` | D41 and D54, the full-header and payload readers. D55, `CAuxPow::check`. D6, `CheckAuxPowProofOfWork`. D14, `GetConsensus`. D33, only the two version gates, with D10's `IsLegacy` and `IsAuxpow`. `harness/core/auxpow_fixtures.inc` adapts D56's deterministic construction and runtime-mined cases, and checks their exact bytes and verdicts. |
| `block.contextual_check` | `ContextualCheckBlockHeader` on index entries that the harness builds from the request | D33, `ContextualCheckBlockHeader`, lines 3066 to 3119. D67 and D69 for the checkpoint state |
| `block.contextual_check_body` | `SelectParams` for mainnet, then `ContextualCheckBlock` on a `CBlock` that Core's stream code reads, with a predecessor that the harness builds from the chain. `VersionBitsState` reads the aligned boundary's median time, and the harness seeds `THRESHOLD_FAILED` at a boundary at or after the CSV timeout. With `force_csv_active`, the harness seeds `THRESHOLD_ACTIVE` for CSV, a state that no mainnet chain reaches ([the forced CSV state](#core-with-the-csv-state-forced-to-active)) | D14, D102, D103, D110 |
| `block.header.read` | `CBlockHeader` read from a `CDataStream` in the requested stream mode | D41 and D54, the full-header and payload readers. D55, `CAuxPow::check`. D6, `CheckAuxPowProofOfWork`. D14, `GetConsensus`. D33, only the two version gates, with D10's `IsLegacy` and `IsAuxpow`. `harness/core/auxpow_fixtures.inc` adapts D56's deterministic construction and runtime-mined cases, and checks their exact bytes and verdicts. |
| `block.header_sequence` | `AcceptBlockHeader` once for each header, which calls `CheckBlockHeader`, `ContextualCheckBlockHeader` and `AddToBlockIndex`, on an index that the harness builds from the request | D33, `AcceptBlockHeader`, lines 3205 to 3267, which calls `CheckBlockHeader`, `ContextualCheckBlockHeader` and `AddToBlockIndex`. D35, `BuildSkip`. D103, the state that the textual include reaches |
| `block.subsidy` | `SelectParams` for mainnet, then `GetDogecoinBlockSubsidy` with `Params().GetConsensus(height)` for each case, as `ConnectBlock` calls it (D101, line 1996) | D14, D101, D104 |
| `block.validate` | `SelectParams` for mainnet. Then, for each block that Core's stream code reads: `CheckBlockHeader` when `check_pow` is true, `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock`, and `ConnectBlock` with `fJustCheck` true on a new `CCoinsViewCache` over the carried set. The first two do not run for the genesis hash. `UpdateCoins` on a second cache gives the changes of an accepted block ([choices](#block-validation-in-the-harness)) | D33, `CheckBlockHeader` and `ContextualCheckBlockHeader`. D106, `CheckBlock`. D110, `ContextualCheckBlock`. D114, `ConnectBlock`. D113, `CCoinsViewCache`, `UpdateCoins` and the coin view. D116, `InitSignatureCache`. D35, `BuildSkip` and `GetAncestor`. D102 and D103, the version-bits cache and the state that the textual include reaches |
| `block.version_bits_state` | `SelectParams` for mainnet, then `VersionBitsState` for CSV and SegWit on a `CBlockIndex` chain that the harness builds from the request, with an empty version-bits cache. The consensus parameters are those of the height after the last entry | D14, D100, D102 |
| `compactsize.encode` | `WriteCompactSize` into a `CDataStream` | D1, `WriteCompactSize` and `ReadCompactSize`. D21, `CDataStream` |
| `compactsize.read` | `ReadCompactSize` from a `CDataStream` | D1, `WriteCompactSize` and `ReadCompactSize`. D21, `CDataStream` |
| `hash.hash160` | `CHash160::Write` and `Finalize` | `src/crypto/ripemd160.cpp`, `CRIPEMD160::Write`, `Finalize`. D8, `CHash160::Write`, `Finalize`. `src/crypto/sha1.cpp`, `CSHA1::Write`, `Finalize`. All at the Dogecoin pin. |
| `hash.ripemd160` | `CRIPEMD160::Write` and `Finalize` | `src/crypto/ripemd160.cpp`, `CRIPEMD160::Write`, `Finalize`. D8, `CHash160::Write`, `Finalize`. `src/crypto/sha1.cpp`, `CSHA1::Write`, `Finalize`. All at the Dogecoin pin. |
| `hash.sha1` | `CSHA1::Write` and `Finalize` | `src/crypto/ripemd160.cpp`, `CRIPEMD160::Write`, `Finalize`. D8, `CHash160::Write`, `Finalize`. `src/crypto/sha1.cpp`, `CSHA1::Write`, `Finalize`. All at the Dogecoin pin. |
| `header.encode` | `CPureBlockHeader` written to a `CDataStream` | D10, `CPureBlockHeader::SerializationOp`. D21, `CDataStream`. D40, `CPureBlockHeader::GetHash`. |
| `header.hash` | `CPureBlockHeader::GetHash` | D10, `CPureBlockHeader::SerializationOp`. D21, `CDataStream`. D40, `CPureBlockHeader::GetHash`. |
| `header.read` | `CPureBlockHeader` read from a `CDataStream` | D10, `CPureBlockHeader::SerializationOp`. D21, `CDataStream`. D40, `CPureBlockHeader::GetHash`. |
| `merkle.compute` | `ComputeMerkleRoot`, including its `mutated` output argument (at most 2^31 internal-order leaves) | D42, `ComputeMerkleRoot` and `MerkleComputation`, with at most 2^31 internal-order leaves. |
| `pubkey.verify` | `CPubKey::Verify`, with storage-order `uint256` digest bytes | D50 |
| `script.eval` | `EvalScript` with the caller stack and flags, `BaseSignatureChecker` and `SIGVERSION_BASE` | D3, `EvalScript` with `SIGVERSION_BASE`. D25, `BaseSignatureChecker`. |
| `script.read_op` | `CScript::GetOp` on the exact script bytes, with iterator `begin() + cursor` | D24 |
| `script.verify_legacy` | `VerifyScript` with a null witness and the selected `BaseSignatureChecker` or `TransactionSignatureChecker`. `CPubKey::Verify` and `ECCVerifyHandle` use libsecp256k1 | D3, `VerifyScript` and `TransactionSignatureChecker`. D25, `BaseSignatureChecker`. D50, `CPubKey::Verify` and `ECCVerifyHandle`. |
| `scrypt.hash` | `scrypt_1024_1_1_256_sp_generic` (generic scrypt, `--disable-scrypt-sse2`) | D40 and D61, `scrypt_1024_1_1_256_sp_generic`, with its output bytes. D62 supplies the five independent digest vectors. |
| `sighash.legacy` | `tx_hex` read as by `tx.decode_base`. Then `SignatureHash` with amount 0 and `SIGVERSION_BASE` | D3, `SignatureHash` with `SIGVERSION_BASE` |
| `tx.check` | `CheckTransaction` on a `CTransaction` that Core's stream code reads from the request in the mode of the request. Then `GetLegacySigOpCount` and `GetSerializeSize` in base mode | D4, D21, D106 |
| `tx.decode_base` | `CMutableTransaction` read from a `CDataStream` with `SERIALIZE_TRANSACTION_NO_WITNESS`, then a check that the stream is empty. The transaction written back to a stream of the same version, and `CTransaction::GetHash` | D4, `UnserializeTransaction` and `SerializeTransaction`, with `SERIALIZE_TRANSACTION_NO_WITNESS`. D23, `CTransaction::ComputeHash`. D11, `base_blob::GetHex` |
| `tx.decode_witness` | `CMutableTransaction` read from a `CDataStream` without `SERIALIZE_TRANSACTION_NO_WITNESS`, requiring an empty stream. Writes with witness data allowed and calls `CTransaction::HasWitness`, `GetHash` and `GetWitnessHash` | D4, `UnserializeTransaction`, `SerializeTransaction` and `CTransaction::HasWitness`, without `SERIALIZE_TRANSACTION_NO_WITNESS`. D23, `CTransaction::GetHash` and `GetWitnessHash`. D11, `base_blob::GetHex` |
| `tx.read_base` | `CMutableTransaction` read from a `CDataStream` whose version has `SERIALIZE_TRANSACTION_NO_WITNESS`, so `UnserializeTransaction` reads base mode | D4, `UnserializeTransaction` and `SerializeTransaction`, with `SERIALIZE_TRANSACTION_NO_WITNESS`. D23, `CTransaction::ComputeHash`. D11, `base_blob::GetHex` |
| `tx.read_witness` | `CMutableTransaction` read from a `CDataStream` without `SERIALIZE_TRANSACTION_NO_WITNESS`. Writes with witness data allowed and calls `CTransaction::HasWitness`, `GetHash` and `GetWitnessHash` | D4, `UnserializeTransaction`, `SerializeTransaction` and `CTransaction::HasWitness`, without `SERIALIZE_TRANSACTION_NO_WITNESS`. D23, `CTransaction::GetHash` and `GetWitnessHash`. D11, `base_blob::GetHex` |
| `work.calculate_next` | `SelectParams`, `Params().GetConsensus(selection_height)`, then `CalculateDogecoinNextWorkRequired` on an explicit `CBlockIndex` | D6, `CalculateDogecoinNextWorkRequired`, lines 41–87. D14, `SelectParams` and `GetConsensus`. Known answers: D7, `get_next_work_*`, lines 123–210. |
| `work.get_compact` | `arith_uint256::GetCompact` | D13, `arith_uint256::SetCompact` and `GetCompact`, lines 204–245. Known answers: D16, `bignum_SetCompact`, lines 412–538. |
| `work.next` | `SelectParams`, candidate-height `GetConsensus`, then `GetNextWorkRequired` on linked `CBlockIndex` objects | D17, `GetNextWorkRequired`, lines 32–88. D18, `CBlockIndex`. D35, `BuildSkip` and `GetAncestor`, with `GetSkipHeight` only as a guard on suffix construction. D14, candidate-height parameters. |
| `work.set_compact` | `arith_uint256::SetCompact` | D13, `arith_uint256::SetCompact` and `GetCompact`, lines 204–245. Known answers: D16, `bignum_SetCompact`, lines 412–538. |

Core's consensus archive supplies `primitives/pureheader.cpp` and `consensus/merkle.cpp`.
The same archive contains `script/interpreter.cpp`, `script/script.cpp` and `script/script_error.cpp`.
Its cryptography archive supplies RIPEMD-160, SHA-256 and SHA-1.
The harness implements no replacement hash or Merkle algorithm.

The harness compares `work.next` only on contiguous views with enough history for the required retarget ancestor or recovery walk.
It rejects a request outside that domain before it calls Core.
Core can assert on a missing ancestor, and a truncated recovery walk can return a different result.
The comparison excludes every `work_view` fixture and checks those errors only against the oracle fixtures.
The oracle reads chain heights as `u32` and returns `work_view` with `height_out_of_range` from 2147483647.
The harness instead returns a `request` error for those heights, outside its caller domain.

The harness sets each supplied entry's `pprev`, `nHeight`, `nTime` and `nBits`.
It computes Core's `GetSkipHeight` only to decide whether to call `BuildSkip` within the supplied suffix.
When that destination precedes the suffix, the skip pointer stays null.
Core's `GetAncestor` then follows `pprev`, so this guard changes no result.
The traversal cannot diverge through a retained skip pointer because Core follows `pskip` only when its skip height is at least the target.
The `work missing skip traversal` comparison retargets from height 479 to ancestor 239 across height 256, whose skip pointer is null.

**Script.**
For `script.read_op`, the harness obtains the cursor from Core's iterator and derives `opcode` and `part` from the original opcode.

For `script.eval`, the harness calls Core's own `EvalScript` with `SIGVERSION_BASE` and `BaseSignatureChecker`.
That checker returns false for signature, locktime and sequence checks.
The harness uses this checker for either evaluation selection.
An unsupported Lean result makes no claim about Core's verdict on that request.

For `script.verify_legacy`, the harness calls Core's `VerifyScript` with a null witness and the selected checker.
`TransactionSignatureChecker` receives the immutable transaction, input index and amount zero, which legacy hashing does not use.
An `ECCVerifyHandle` lives for the request loop and initializes Core's verification context.
Pinned `src/pubkey.cpp`, `CPubKey::Verify` and `ECCVerifyHandle` (D50), use that context for key parsing and libsecp256k1 verification.
The harness signs nothing and does not call `ECC_Start`.
Core's binary and libsecp256k1 remain trusted runtime components, without a Lean refinement theorem.

Core asserts that WITNESS implies P2SH (D3, line 1519), and CLEANSTACK implies both P2SH and WITNESS (lines 1508 and 1509).
The harness rejects flag combinations that violate these dependencies as request errors, without changing flags.
The Lean oracle still reports those unsupported flags.

The comparator classifies these combinations as `harness-refused` only after complete base decoding, input bounds and script limits pass.
The classifier requires the operation's exact arguments, permits an optional `id`, and requires an integer `input_index`.
Earlier decode or adapter errors retain their ordinary comparison path.
The comparator requires a harness request error and an exact Lean unsupported-flags result, or fails the request.
A checked refusal counts as neither agreement nor disagreement.
A failed refusal check fails the run and stays outside the compared count.

**Header checks.**
For `block.check_version`, the Core harness reads the field from Core's `Params().GetConsensus(selection_height)`.
It transcribes the two branches from D33 and calls Core's own `IsLegacy` and `IsAuxpow` predicates.
It does not call the complete contextual validator, which needs chain state and checks other rules.

For the header proof-of-work predicates, Core returns only `valid`.
The comparator excludes only Lean's `diagnostic`, and compares Boolean verdicts without coercion.

For `block.contextual_check`, the harness refuses inputs outside its comparison domain before it calls Core's helpers.
The comparator checks `valid` and `reject_reason`, including signed base-version formatting such as `bad-version(0xffffff03)`.
It excludes only the Lean diagnostic.

**Header sequences.**
For `block.header_sequence`, the comparator compares every response field except `diagnostic`.
It compares all other fields first, including the failure position and accepted prefix.
It excludes `marked_failed_child` only for an agreed step-6 failed-ancestor rejection at `failed_at`.
The rejecting header's predecessor must have at least two distinct failed-list members among its ancestors.
The ancestry includes entries added in the accepted prefix.

Other rejection steps and accepted calls retain the mark comparison.
Duplicate members of the failed list do not satisfy that condition alone.
A failed member below an anchor is no ancestor under the finite-index convention.
All other fields remain comparable in the excluded-mark cases.

**Block validation totals and domain.**
For `block.validate`, the harness adds the amounts of the coins of its own `CCoins` entries, in 128-bit arithmetic.

The harness's sum is an `unsigned __int128`.
Before it adds an amount, the harness requires `MoneyRange`, so each amount is at most `MAX_MONEY`, 10^18 koinu, which is below 2^60.
For a set of fewer than 2^64 coins, the sum is below 2^124, so it cannot wrap.
The harness counts the coins in a `uint64_t` without a check, so the bound has that precondition.
The recorded set at the tip has 202,470,869 coins.
Part 7 of `scripts/test_core_pass.py` tests a set of 19,999,999,999,999,999,999 koinu in both programs. That is above 2^64, and a binary64 double does not hold it exactly.

For a request that starts at the genesis block, with the empty chain and no coins, the comparators also check the bound of `chain_issuance_bound`.
Both programs answer `block.subsidy` for each accepted height from 1, with the hash of the accepted block before it, and the subsidies must agree.
Each `set_value` must be at most the sum of the subsidies of the heights from 1 to its height.
The genesis block adds no coin, so its term is 0.
`scripts/compare_core.py --mainnet-blocks` reports a failure of this check as `ISSUANCE`, and `scripts/replay_blocks.py` checks it as its fifth step.

When the oracle ends a `blocks_hex` range at `out_of_domain_at`, the comparator sends the harness the request without that block and the blocks after it.
A file request has no `blocks_hex` list to shorten.
So the comparison fails if the oracle ends the range of a file at a block outside the arithmetic domain.

## How its responses differ

The harness answers a projection of `dogelib-oracle/1`, not the format itself:

- `--version` and `oracle.version` give the format `dogelib-oracle/1-core-projection`.
- `script.eval` and `script.verify_legacy` never return `unsupported` from the harness.
  It returns Core's verdict with the operation's checker, even when Lean reports an unsupported capability.
  An unmapped `ScriptError` stops the harness with an unmapped-Core error.
- For a truncated `script.read_op`, the harness derives `opcode` and `part` from the input and cursor.
  Core does not return these diagnostics.
- `tx.check` and `block.check` have no `diagnostic`. Core reports the reject reason, and not the Lean error or the position of a rejected transaction.
  The harness builds a new `CBlock` for each request, so `fChecked` is false at the call.
  It stops with an unmapped-Core error if that member is set.
- The block records of `block.validate` have no `diagnostic`, and `out_of_domain_at` is always null.
  Core has no test for the overflow of its sums, so the harness cannot report one.
- `block.subsidy` has no `redraws`, because Core does not report the rejected words.
  It has `boost_version` instead: the release of the Boost headers that Core's function was compiled with, such as `1.70.0`.
- `sighash.legacy` has no `preimage_hex`.
  `SignatureHash` hashes its preimage as it writes it and does not return it.
- `plan` is a label that the harness computes from the conditions of Core's two early returns, in `src/script/interpreter.cpp` lines 1225 to 1235.
  It is not observed from Core.
  If the label is `fixed_digest` and Core's digest is not the value one, the harness stops with exit status 3.
- The harness passes the hash type to Core's `int nHashType` as the same 32 bits, read as a two's complement value.
  It passes `input_index` to `unsigned int nIn` unchanged.
- Core reports a read error as a `std::ios_base::failure`.
  The harness maps four messages to `read` errors: `CDataStream::read(): end of data` to `truncated`, `non-canonical ReadCompactSize()` to `non_canonical`, `ReadCompactSize(): size too large` to `too_large`, and `Unknown transaction optional data` to `unknown_optional_data`.
  It accepts each message alone or followed by `: iostream error`, which libstdc++ appends.
  Any other exception stops the harness with exit status 3, so it fails the comparison.

The harness checks request arguments by the rules of [`docs/oracle.md`](oracle.md).
Twenty-two adapter-limit boundary requests check both programs against the documented expectations, including `adapter/resource_limit` errors.
Other argument checks have oracle fixtures but no Core comparison.

## Testing the proposal executable

See [the proposal executable](oracle.md#the-proposal-executable) for the `revision` wire contract.
The executable has one test, which needs no Dogecoin Core:

```bash
lake build dogelib-oracle dogelib-proposal-oracle proposal-test-oracle
python3 -I scripts/test_proposal_oracle.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle .lake/build/bin/proposal-test-oracle
```

The checks of a revision run in the test build, which names all four revisions.
`dogelib-proposal-oracle` refuses each example, and it writes the bytes of the test build on every request that names `RelativeLockTime`.

- Without `revision`, each proposal executable writes the bytes of `dogelib-oracle` on the 42 `block.validate` requests of the full comparison and on 34 requests with `blocks_file`. With `--mainnet-blocks build/mainnet-blocks`, the test adds the replay of mainnet heights 0 to 10,000.
- Without `revision`, each proposal executable also writes the bytes of `dogelib-oracle` on the 22 `block.contextual_check_body` requests of the comparison. With a revision and no activation height, each `revised` object has `active` false and the baseline verdict. The examples change no lock-time argument, so the same holds for them from height 0.
- `dogelib-oracle` refuses `revision`, and the proposal executable refuses 18 malformed values of it.
- With no activation height, each `revised` object has the verdict, the reject reason and the changes digest of its baseline record. The check covers the 119 block records of those 42 requests, for each revision.
- From height 0 on the same requests, the response without the `revised` objects is the baseline response. No block goes from rejected to accepted under the two revisions with a restriction theorem.
- One request of the comparison has five blocks that fail the five checks in Core's order. Each `revised` object names the check in `step`, and the transaction at 1 in `tx` for the duplicate inputs and for the missing coin.
- Eleven made blocks give `revised` objects that the test states by hand from the text of each rule. Each block stands on a committed rule-change block and spends a supplied coin. For eight of them the script of the coin holds the rule of an example. A negative operand of each rule changes an accepted block to rejected. The counterexample of the faulty variant changes a rejected block to accepted. Three blocks are for the sequence locks of `RelativeLockTime`, with a transaction of version 2. A height lock that is met leaves the block accepted. A height lock that is one block short gives the reason `bad-txns-nonfinal`. A time lock on a coin above the block gives `unsupported` with the reason `RelativeLockTime: coinAboveBlock`.

- Without `revision`, each proposal executable also writes the bytes of `dogelib-oracle` on 33 of those requests with their coins in a `coins_file`. With `--snapshot-request`, the test adds one range request from a snapshot, such as the short range, for `dogelib-proposal-oracle`. A request with a revision gives the same `revised` objects with `coins_file` as with `coins`.

## Historical impact tooling

`scripts/impact_run.py` runs a revision on a range of mainnet blocks in `dogelib-proposal-oracle`, or an example in the test build `proposal-test-oracle`.
The examples run on the short range alone.
It implements the self-test of [design record 0011](design/0011-mainnet-ranges.md), section 10.3, and the counts of [design record 0012](design/0012-relative-lock-time.md), section 10.3.

`impact_run.py request` writes the range request:

| Range | Heights | Coins at the start |
| --- | --- | --- |
| `genesis-10000`, `genesis-145000` | 0 to 10,000, and 0 to 145,000 | The empty set |
| `short`, `S` | 9,001 to 10,000, and 100,001 to 101,000 | The snapshot that the harness writes at 9,000 or 100,000, with its committed manifest |
| The configured ranges of design record 0011 | Section 4 of design record 0011 | The Core pass's snapshot at the range start, with its committed manifest. The request equals the request of `scripts/run_range.py` |

`scripts/impact_candidates.py` lists the candidate blocks of each range from that request, without DogeLib code ([the lists](../tests/proposals/impact/README.md)).
A candidate covers spends only.
The scripts of a spend are its `scriptSig`, the spent `scriptPubKey` and the P2SH redeem script.
A block is a candidate when a script of one of its spends holds the opcode of the revision.
A missing coin of a spend also makes a candidate.

For `RelativeLockTime`, a cutoff transaction of BIP 113 and a sequence candidate of BIP 68 also make a candidate.
A created `scriptPubKey` does not make its block a candidate.
The list is committed before the runs of its range.

`impact_run.py run` sends the request with `revision` and checks the response:

- The candidate list is committed, and it names the blocks file of the request by SHA-256.
- The response has one block record for each block of the blocks file, with its height and its hash, and `out_of_domain_at` is null.
- The baseline accepts every block. With `--baseline`, the response without the `revised` objects equals that response of `dogelib-oracle` to the same request.
- Case 1, with no activation height: each `revised` object has `active` false. It has the verdict, the reject reason and the changes digest of its block record.
- Case 2, from an activation height: every changed block is a candidate, and every change goes from accepted to rejected. An accepted block has the changes digest of the baseline.

A changed block is a block whose two verdicts differ. An unsupported result is not a change.

`impact_run.py check` runs the same checks on a saved response of `impact_run.py run`.

`scripts/test_impact.py` plants one candidate of each kind in a made block, in the form of a range request.
The kinds are `0xb9`, `0xb3`, `0xb2`, a sequence lock that is one block short, and a lock time at the median time past.
The scan lists each block, and the test build of the proposal executable rejects each one, which the baseline accepts.
The run check fails when the list leaves the block out.

The `revised` verdicts have no Core comparison, and an empty report is not a compatibility proof (design record 0011, section 10.4).
[Historical impact runs](comparison-evidence.md#historical-impact-runs) records the completed runs and their digests.

## Core with the CSV state forced to `ACTIVE`

This evidence has its own label: Core at `e0a1c15` with the CSV state forced to `ACTIVE`.
It is about the proposed revision `RelativeLockTime` alone. It is not a Core comparison of the baseline, and it is not evidence about mainnet.

Dogecoin Core 1.14.9 holds the code of BIP 113, BIP 112 and BIP 68, and its version-bits state for CSV never becomes `ACTIVE` on mainnet (`csv_never_lockedIn`).
`block.contextual_check_body` and `block.validate` of the Core harness take one more argument, the Boolean `force_csv_active` ([design record 0012](design/0012-relative-lock-time.md), section 10.2 and decision 12).
With the value true, the harness seeds `THRESHOLD_ACTIVE` for CSV in Core's version-bits cache, at the boundary that the block reads.
Core's own `ContextualCheckBlock` then takes the median time past of the predecessor as the lock-time cutoff (D110, lines 3134 and 3135).
In `block.validate`, Core's own `ConnectBlock` also sets `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` (D114, lines 1906 to 1911), so opcode `0xb2` is `OP_CHECKSEQUENCEVERIFY`.
It also passes `LOCKTIME_VERIFY_SEQUENCE` to `SequenceLocks` (lines 1948 to 1959), so each transaction that is not a coinbase has the sequence locks of BIP 68.
No line of Core's source changes.

The harness seeds nothing for a block that is not applicable: one without a predecessor, or one whose header has the hash of the genesis block.
Below height 10,080 the aligned boundary is null, which is also the cache key of a block without a predecessor.
The harness clears the cache before and after each request.
With the argument, the `chain` must hold the eleven predecessors, or every predecessor below height 11, and the harness refuses a shorter chain.
`dogelib-oracle` and `dogelib-proposal-oracle` refuse the argument, and the harness and `dogelib-oracle` refuse `revision`.

```bash
python3 -I scripts/fetch_release_blocks.py
python3 -I scripts/relative_lock_time_candidates.py --check
python3 -I scripts/compare_csv_forced.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle build/core-harness/core-oracle
```

`scripts/compare_csv_forced.py` sends each block to the harness with `force_csv_active`, and to the proposal executable with `RelativeLockTime` from activation height 1.
It compares the forced result of Core with the `revised` object: verdict, reject reason, score and reject code.

With `force_csv_active` true, `block.validate` of the harness runs each block twice on the state before it.
The first run has the seed, and its result is the object `forced` of the block record.
The second run has no seed. It gives the other fields of the record, and it alone carries the coin set and the chain to the next block.
So the response without its objects `forced` is the response of the request without the argument.

| Field of `forced` | Value |
| --- | --- |
| `valid`, `reject_reason`, `dos`, `reject_code` | The verdict of the five checks with the CSV state forced to `ACTIVE`, as in the block record. |
| `changes_digest_hex`, `spent`, `created` | For an accepted block, the digest and the counts of its coin changes. Null otherwise. |
| `unsupported` | Null, or one of `ancestorOutsideView`, `coinAboveBlock` and `heightOutOfDomain`: a read of `SequenceLocks` that is outside the model of the revision. Every other field is then null. |

A block that is not applicable gets no seed, and its `forced` object is the result without it.
The comparison reads `forced` against the `revised` object of the proposal executable: verdict, reject reason, score, reject code and the digest of the changes.

With the forced state, Core's `ConnectBlock` also runs `SequenceLocks` of BIP 68 (D114, lines 1948 to 1959), which the revision has as `sequenceLocks`.
Each of the 36 made blocks of the opcode passes that test, in Core and in the revision: its coin is far below the block, or its lock is 0.

Three reads of `SequenceLocks` are outside the model of the revision (design record 0012, section 6.3), and the harness does not let Core make them.

| `unsupported` | Read |
| --- | --- |
| `heightOutOfDomain` | An input with a lock spends a coin at a height from 2^31 - 65535. Core computes `c + n - 1` from the left in `int`, and `c + 65535` can then overflow. |
| `coinAboveBlock` | A time lock on a coin above the block. For a coin one block above, Core reads the median time past of the block itself. For a higher coin, `GetAncestor` returns null, and Core dereferences it. |
| `ancestorOutsideView` | A time lock whose ancestor, or one of its ten predecessors, is below the supplied chain. |

Before the forced `ConnectBlock`, the harness scans the block in the order of the revision: the transactions in block order, the inputs in input order, and for one input the order of the table.
On the first such read it does not run `ConnectBlock` with the seed. The object `forced` then has that name in `unsupported`, and no verdict.
The comparison requires the verdict `unsupported` of the `revised` object, with the same reason.
So for these blocks the comparison checks that the two programs draw the limit of the model at the same place. It is no comparison of a verdict, because Core gives none.
For a coin one block above the block, Core has a defined result, which neither program gives.

The scan follows the lookup of the inputs on a second cache, and it ends at a transaction whose inputs are missing.
At a transaction that would overwrite unspent outputs of its own transaction ID, the scan clears the entry and goes on, as Core's `ConnectBlock` does when its own cache lacks the entry.
It does not follow the other exits of `ConnectBlock`: BIP30, the scripts, the count of signature operations and the amounts of an earlier transaction, and an earlier transaction that fails its own sequence lock.
So it can name a read on a block that Core would reject before that read, where the revision gives the rejection. The comparison then fails, and it sends no such block.
For example, let the transaction at 1 have a height lock that is one block short, and the transaction at 2 a time lock on a coin above the block. The scan names `coinAboveBlock`, and the revision rejects the transaction at 1.

[Forced-CSV results](comparison-evidence.md#core-with-the-csv-state-forced-to-active-results) records the request counts, made-block totals and mainnet counts of this comparison.

## Block validation in the harness

`block.validate` keeps state in the harness for the length of one request: a block index, a coin set, and Core's version-bits cache.
`harness/core/core_block_validate.inc` holds the code.
Every verdict comes from Core's five functions.
The code builds their inputs, and makes these choices (design record 0010, section 5):

- **Script checks.** `nScriptCheckThreads` is 0 and `hashAssumeValid` is null, which are Core's values before `init.cpp` reads the node's options. So `ConnectBlock` checks every script of every input, in input order, with no check queue (D114, lines 1827 to 1849 and 1924).
  `main` calls `InitSignatureCache`, because `ConnectBlock` stores accepted signatures in that cache.
- **`fJustCheck`.** `ConnectBlock` runs with `fJustCheck` true on a new `CCoinsViewCache` over the carried set. With that flag it calls `CheckBlock` with both flags false (line 1804), and it returns before it writes undo data or the transaction index (line 2009).
- **Commit.** After an accepted block, the harness calls `SetBestBlock` and `Flush` on the cache, because `fJustCheck` returns at line 2009, before `SetBestBlock` (line 2035). After a rejected block, the cache is discarded, because `UpdateCoins` runs before the coinbase check (lines 1988 and 1996).
- **The carried set.** The set is a `CCoinsView` over a `std::map`, as `CCoinsViewTest` of Core's `src/test/coins_tests.cpp`, without that class's random choices. A flush erases an entry that is pruned. With `coins_db`, the set is in Core's `CCoinsViewDB` instead ([the Core pass](#the-core-pass)).
- **The block index.** The harness builds one `CBlockIndex` for each entry of `chain` and for each accepted block, with Core's skip list where the skip target is inside the chain. `mapBlockIndex` holds the entry of the last accepted block alone, which `CheckInputs` reads for the spend height (lines 1407 to 1411).
- **The BIP34 ancestor.** `ConnectBlock` reads the hash of the ancestor at `BIP34Height` (line 1877). Inside the supplied chain, the entry of that height gets the supplied hash. Below the chain, the oldest entry gets a predecessor that is its own predecessor and skip entry, as for `block.header_sequence`, so that `GetAncestor` returns it for every lower height.
- **Refusals.** The harness refuses a request whose chain is too short for Core's other reads: the median time, the retarget history, and the aligned version-bits boundary with its ten predecessors. So Core never reads the added predecessor as history.
- **Version bits.** The harness seeds `THRESHOLD_FAILED` at a boundary at or after the CSV timeout, as for `block.contextual_check_body` (design record 0010, decision 3). Below the CSV start, Core's walk stops at the aligned boundary.
- **The CSV window.** Inside the window, Core's `VersionBitsState` walks back one period at a time to a boundary whose median time is below the CSV start. It counts the versions of the blocks above that boundary (`versionbits.cpp`, lines 44 to 108). So the chain must reach the boundary and its ten predecessors, and each supplied entry above it needs a `version`. Otherwise the request is a request error. Each accepted block has the version of its header.
- **Restored state.** Every exit clears `mapBlockIndex` and the version-bits cache, and restores `fCheckpointsEnabled` and the mock time.
- **Snapshots.** With `coins_file`, the harness loads every record of the snapshot into the carried set, and reports the digest and the number of the records. Its checks and their order are those of the oracle's reader.

The harness alone takes more arguments ([design record 0011](design/0011-mainnet-ranges.md), section 3.2):

- `snapshot_heights` with `snapshot_dir`: a list of heights in increasing order, and the path of a directory. After the accepted block at each listed height, the harness writes the carried set as the snapshot `coins-<height>.bin` in that directory. It writes a temporary file first and renames it.
- `digest_heights`: a list of heights in increasing order. After the accepted block at each listed height, the harness computes the digest of the whole set.
- `version_bits_heights`: as in the oracle. The predecessor at each listed height can be the supplied one or an accepted block. The harness reports Core's `VersionBitsState` of CSV and SegWit for the block after it, with the checks of the CSV window above.
- `coins_db`, `coins_db_cache_mb` and `coins_db_continue`: the coin database of the Core pass ([the Core pass](#the-core-pass)).

The result then has `snapshots`, `set_digests` and `version_bits_states`, one entry for each listed height that the request reached, in order.
Both programs take `version` in an entry of `chain` and `version_bits_heights` ([the CSV window](oracle.md#the-csv-window)).
An entry of `set_digests` has `height`, `set_digest_hex`, `set_coins`, `set_value`, and two values of Core's `GetUTXOStats` for the same set (`rpc/blockchain.cpp`, lines 874 to 905): `hash_serialized` and `transactions`.

`hash_serialized` is the hash in the byte order of the `gettxoutsetinfo` output. It covers the best block, and each transaction ID with the index, the amount and the script of each of its coins. It does not cover the height or the coinbase flag.
`transactions` is the number of transaction IDs with a coin.
An entry of `version_bits_states` has `height`, `csv` and `segwit`, with the names of `block.version_bits_state`.
An entry of `snapshots` has those fields, the hash of the block as `hash_hex` and `hash_display`, and `file`, `bytes` and `sha256` of the written file.
`scripts/snapshot_range.py` writes the manifest from that entry, after it computes each value again from the file.
The oracle returns a request error for the other arguments of this list.

One function of the harness, `visitSet`, walks the carried set, one `CCoins` entry at a time in the order of the transaction IDs.
The digest of the whole set and the snapshot writer read the set through it alone.

The harness reads the changes of an accepted block from a second `CCoinsViewCache` over the set before the block.
For each transaction in order, it reads the entry of each input, calls Core's `UpdateCoins`, and reads the new entry.
So the spent and created coins are Core's own entries, as they are just before and just after each transaction.
The harness then requires that the second cache and the cache of `ConnectBlock` hold equal entries for every transaction ID that the block names.
It stops with exit status 3 if they differ.

### The Core pass

[Stage 0](comparison-evidence.md#measurements-for-the-core-pass) chose Core's `CCoinsViewDB` for the Core pass, because the map does not fit in memory at the tip.
With `coins_db`, the path of a directory, the harness carries the set in a `CCoinsViewDB` in `<coins_db>/chainstate`, under one `CCoinsViewCache`.
Each block's cache reads that cache, as it reads the map otherwise.
After an accepted block, the harness writes the cache to the database when its `DynamicMemoryUsage` is above `coins_db_cache_mb` megabytes, 1,024 by default.
Core writes the coins and the best block in one LevelDB batch.
So the database always holds the set after one accepted block, and names that block.

For `visitSet`, the harness first writes the cache, and then walks the database's cursor.
The cursor visits the keys in LevelDB's byte order. A key is the byte `c` and the 32 bytes of the ID, so that is the order of the transaction IDs (`src/txdb.cpp`, lines 32 and 93 to 104).

Without `coins_db_continue`, the harness empties the database first, and loads `coins` or `coins_file` into it.
With `coins_db_continue` true, the request has neither, and the set is the one in the database.
The first block must then name the database's best block as its previous hash, or the request fails with the error `coins_db_best_block`.

A request with `coins_db` has no digest of the whole set in its block records.
Its result has `coins_db_start_display` and `coins_db_best_display`: the best block of the database at the start and at the end, in display order.
The harness writes one line to standard error after each accepted block whose height is a multiple of 10,000.
`coins_db_unusable` is the error of a directory that does not exist, or of a database that does not open.

`scripts/core_pass.py` runs the pass of design record 0011, section 3.2, with these arguments.
Each segment is one request, of at most 100,000 blocks and 4 GB.
The database persists from one segment to the next, so a segment does not load a snapshot.
This persistent database is how the pass implements the segments of section 3.2, as a detail of decision 3.
Each segment starts from the database with `coins_db_continue`.
So the harness requires that the database's best block is the last block of the segment before.
Each segment reports the digest of the whole set at its end.

The pass writes a snapshot at each range start and at each multiple of 500,000, and keeps only the newest of the latter.
A stopped harness can leave the database at another height than the pass's state. The pass then starts again from its newest snapshot below that height, which it loads into an empty database with `coins_file`.

The pass keeps the header of every accepted block. It builds the `chain` of each segment from them, with the version of each entry. Inside the window the chain reaches back to the boundary below the CSV start.
It requires each checkpoint of Core, and the digests of heights 100,000, 101,000 and 145,000 of the recorded runs of stage 1.
It requests Core's version-bits state at each period boundary.
With `--version-bits`, the script checks each state of a boundary in the CSV window. Both programs compute it again with `block.version_bits_state` on the kept headers from the genesis block.

With `--seed DIR --seed-height H`, the script starts a new state from the kept snapshot at height `H` of the pass in `DIR`, which it only reads.
It copies that snapshot and checks it against its manifest, and copies the headers to `H`.
The first segment then loads the snapshot with `coins_file`, as after a restart.
The new pass must reach each digest that the seed pass recorded above `H`, at its range ends and its segment ends.
It must also reach each version-bits state that the seed pass recorded.
It stops on any difference, and its state lists the heights that it checked.

The pass runs `core-oracle-trap`, which `scripts/build_core_harness.sh --trap-overflow` builds beside `core-oracle`.
That build compiles Core's `src/validation.cpp` and `src/coins.cpp`, which hold the sums of `ConnectBlock`, with `-fsanitize=signed-integer-overflow -fno-sanitize-recover=signed-integer-overflow`.
A signed overflow in those files then ends the program with a report, in the place of undefined behaviour (design record 0011, section 3.2).
Its `--version` output has `"trap_overflow": true`.

`scripts/test_core_pass.py` tests these parts in CI on the released heights 0 to 10,000:

- Three synthetic chains reach every state from `defined` to `failed`. At each of their boundaries, `version_bits_states` of `block.validate` equals `block.version_bits_state` of both programs on the whole chain. A chain one entry too short, and an entry in the window without a version, are request errors.
- Each small request of the [full comparison](comparison-evidence.md#block-validation-comparison-evidence) gives one response with `coins_db` and a cache of 1 MB, and with the map. The digests of the block records are not compared.
- The pass of heights 0 to 10,000 runs in segments of 2,500 blocks. It reaches the digest of the map at heights 9,000 and 10,000, and so does its restart from the snapshot at 9,000. A wrong best block gives `coins_db_best_block`.
- `hash_serialized` and `transactions` at height 9,000 equal the values that the test computes from the snapshot file by the definition of `GetUTXOStats`.
- `scripts/run_range.py` runs heights 9,001 to 9,200 from the pass's snapshot at 9,000 in both programs, which reach the pass's digest at 9,200. A changed hash list and a changed committed manifest each fail.
- `scripts/restrict_coins.py` writes the *restricted coins* of those 200 blocks: 8,648 of the 114,056 coins of the snapshot. The restricted coins are the coins of the start snapshot whose transaction ID the blocks name, the set `T` of the [snapshot path](oracle.md#coin-set-snapshots). The oracle gives the recorded block records on them. `scripts/compare_range.py` then runs both programs on them, and they agree. The restricted set ends with a digest other than the pass's. A missing coin entry, other expected records and a changed request without a new `SHA256SUMS` each fail. `scripts/restrict_coins.py` also fails when the source request of the run no longer has the SHA-256 of its summary.
- The trap build stops on the two requests of the arithmetic-domain cases whose sums leave the `int64_t` range, once in `validation.cpp` and once in `coins.cpp`. It gives the response of the ordinary build on the other requests of those cases.
- Nineteen supplied coins of `MAX_MONEY` and one of `MAX_MONEY - 1` give a set of 19,999,999,999,999,999,999 koinu, above 2^64. Both programs give that exact `set_value` with the coins in the request and in `coins_file`. The harness also gives it with `coins_db` and in the manifest of a written snapshot. The comparator accepts both responses, and they agree with its model.

### The coverage build

The coverage build measures which lines of Core's `src/validation.cpp` a set of requests executes (design record 0013, section 9.2, and decision 13).
It is a measurement tool outside CI, and no verdict comes from it.
`scripts/build_core_harness.sh --coverage` builds `core-oracle-coverage` beside `core-oracle`.
The option and `--trap-overflow` can come in either order, before `--revision`.

The build compiles `harness/core/core_validation.cpp`, the unit that includes `src/validation.cpp`, with gcc's `--coverage` at `-O0`.
At `-O0` each line of Core's source keeps its own count.
The other units and the libraries are those of `core-oracle`.
The object and its notes file `core_validation.gcno` stay in `<build-dir>/coverage`.
Each run of `core-oracle-coverage` adds its counts to `core_validation.gcda` in that directory, and a new build removes the old counts.

`scripts/core_coverage.py` runs the `block.validate` requests of the full comparison, or the requests of another operation with `--op`:

```bash
scripts/build_core_harness.sh --coverage <dogecoin-git-clone> build/core-harness
python3 -I scripts/core_coverage.py --output build/core-coverage/validate .lake/build/bin/dogelib-oracle build/core-harness
```

The script removes the old counts first.
Then `core-oracle` and `core-oracle-coverage` answer the same requests, which the comparison would send to the harness.
Their responses must be equal as JSON values, and each must agree with the oracle under the agreement function of `scripts/compare_core.py`.
Then gcov writes `validation.cpp.gcov` with the count of each line and each branch.

The script also writes `report.md` and `report.json`.
The report gives the executed lines and the taken branches of each function of design record 0013, section 3.2.
It lists the lines of those functions that no request executed.
It also gives the count of each reject site of sections 3.2 and 3.3.

## Comparator and self-test mechanics

`scripts/compare_core.py` gives each request its own `id` and sends both programs the same text, with one exception.
For a `block.validate` request in which the oracle reports `out_of_domain_at`, the harness gets the request without that block and the blocks after it ([the arithmetic domain](oracle.md#the-arithmetic-domain)).
For supported requests, the two responses must be equal as JSON values, subject to the signature-preimage and Lean-diagnostic projections below.
For `script.eval` and `script.verify_legacy`, an unsupported Lean result excludes that request from verdict agreement.
The comparator validates both result shapes and the checker-specific unsupported reasons, then reports the unsupported reason and Core outcome separately.
An adapter error is not an unsupported result.

For `sighash.legacy` with plan `hash_bytes`, the double SHA-256 of the oracle's `preimage_hex` must equal Core's `digest_hex`.
This checks the preimage against Core's digest, not byte by byte against a preimage from Core.
Outside the checked `harness-refused` category, a request error from either program fails the comparison.

`scripts/test_compare_core.py` checks that the comparison can fail.
A wrapper around the oracle stands in for the harness.
Unchanged, it must pass on the full stream. Each response mutation must fail with the failure code that it targets.
One case drops a `compactsize.encode` request from the full stream, and the run must fail with `REQUEST_COUNT` alone.

Only those two cases run the full stream.
Every mutation of the oracle and Core comparison runs the comparator with `--quick`.
Such a run has a reduced stream of 22,667 requests and the two-call composition of the first 32 corpus records.
It also makes the version and AuxPoW reconstruction calls.
A mutation changes one response of that run, or the wrapper's behaviour as a process.
A response mutation that finds no response to change fails its case.

The cases are separate runs of the comparator, four at a time by default, and `--jobs N` changes that number.
Each full-stream case holds about 3.5 GB of memory.

The witness mutations change `wtxid_hex`, a stack and `has_witness`.
The work mutations change the magnitude, both flags, the encoded compact and each work operation's result bits.

Hash mutations change each digest operation.
Block mutations change every header field, encoding, both hash orders, consumption, remainder and truncation.
They also change both Merkle root orders and the mutation flag.
Script mutations change reader fields, evaluation classes, rejection errors, success errors, final stacks and unsupported fields.
An informational Core result for an unsupported request can differ without a comparison failure.

One mutation corrupts a successful second-call stack of the composition path, and the failure must name that path.
Another gives an unsupported result an opcode absent from the script instructions.
Legacy mutations corrupt verdicts, add a forbidden stack, and invent unsupported results for either checker or Core.

Two refusal mutations replace either the required Core refusal or Lean's unsupported-flags answer with a verdict.
Each must fail with its own refusal error code, and the failed refusal must stay outside the compared count.
A transaction-corpus mutation makes Core reject an input with an acceptance requirement.
That mutation must fail the independent Core acceptance requirement.

Another mutation moves one required acceptance into the refusal path and must fail the acceptance-check count.
A targeted-stream mutation gives both programs the same `BAD_OPCODE` rejection and must fail the reached-opcode check.
Classifier assertions cover argument keys, index types and the `scriptSig` size boundary at 1,048,576 and 1,048,577 bytes.

The comparator self-test also includes a three-way positive control and eight Rust-side mutations.
These mutations change consumption, the read error, the remainder, request acceptance, response count, response ID, JSON syntax and the version label.
Each mutation must fail with its expected code.

[The comparison](comparison-evidence.md#the-comparison) records the stream counts, request sets and finite comparison evidence.
