# Soundness: Oracle Adapters and the Core Harness

This file holds the per-operation trust boundaries of `dogelib-oracle`, `dogelib-proposal-oracle`, the Core harness, and the comparator scripts under Gap B4.
See [SOUNDNESS.md](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries) for the general B4 policy and Gaps A to D, and [docs/oracle.md](../oracle.md) for the wire protocol.

- **Scope**: JSON and hexadecimal adapters in `Exports` and `ProposalExports`, `harness/core/core_oracle.cpp`, `core-signer`, `scripts/compare_core.py`, and snapshot and forced-CSV comparisons.
- **Adapter and harness code**: `DogeLib.Exports`, `DogeLib.Proposals.Exports`, `harness/core/*`, and `scripts/compare_*.py`.
- **Key boundaries**: No theorem covers the JSON adapters, the Core harness, or file IO, and comparisons give finite evidence on sent inputs only (B4).
  Digests of coin sets and block hashes establish equal data only under collision resistance of double SHA-256 (A4).

## Header-sequence oracle and comparison

`Block.Exports.headerSequence` converts JSON to the existing sequence specification.
It checks initial keys and `checkWellFormed` before processing, and reports adapter limits as request errors.
The adapter has no refinement theorem.
It reports final prefix insertions with chain work and the marking loop's visited hashes, including flags already set and entries added in the call.
It supplies no node-state authentication.

The harness calls Core's `AcceptBlockHeader` (D33, lines 3205 to 3267) once for each header.
That function runs Core's own proof-of-work check, contextual check and index insertion.
`harness/core/core_validation.cpp` includes `validation.cpp` as text, so the compiled function is Core's.

The harness builds the initial index in Core's `mapBlockIndex`, fills `gFailedBlocks`, and sets the checkpoint option and the adjusted time.
It restores Core's mock time and time offset after each request.

Core's set visits the failed list in address order.
Each anchor above height 0 gets a placeholder predecessor, which stands for the ancestors that the request does not name.
Users trust the index construction, JSON conversion, the placeholder and the preflight refusal of short histories (A1, B4).
Agreement on the tested inputs does not prove agreement on all inputs.
The [comparison streams](../oracle.md#header-sequence-comparison-evidence) record the finite evidence and seeds.

The comparison excludes Lean diagnostics.
All other fields must agree before the comparator decides whether to exclude child marks.
It excludes them only for a step-6 failed-ancestor rejection at the agreed failure position.
At least two distinct failed members must be ancestors of that header's predecessor, including entries added in the accepted prefix.

Other rejection steps and accepted calls retain the mark comparison.
The verdict, failure position, reason, score, code, last hash and every added entry remain compared.
On a well-formed index, `failedAncestor_verdict_perm` proves that the order of the failed list changes no verdict, except the member that a `failedAncestor` rejection names.
It covers the Lean definition, not Core's loop.
Initial state, adjusted time and the checkpoint option remain execution boundaries.
The adapter adds no axiom or compiler substitution.

## Per-operation oracle and harness boundaries

The base operations and the transaction argument of `sighash.legacy` convert hex bytes to a slice once.
`tx.read_base` uses `Transaction.readBaseSlice`.
`tx.decode_base` and `sighash.legacy` use `Transaction.decodeBaseCompleteSlice`.
`Transaction.abstractRead_readBaseSlice` preserves errors, fields and remainder bytes for every slice.
`Transaction.decodeBaseCompleteSlice_eq` preserves the complete reader's result, including errors and trailing-byte counts, for every slice.
The list readers remain the specification.

`ByteSlice.toList_ofByteArray` identifies the bytes in each whole-array slice that the adapter constructs with `ByteSlice.ofByteArray`.
These equalities do not cover the hex or JSON conversions.
The witness operations use list readers.

The witness operations convert `WitnessTransaction` stacks to arrays of item hex strings.
They expose `hasWitness`, witness-allowed serialization, the transaction ID and the witness hash.
No theorem covers these JSON conversions.
Core comparisons check these fields, consumption and errors on the recorded requests only.

The work operations convert target magnitudes in most-significant-byte-first hexadecimal and preserve compact values as UInt32 fields.
They select network parameters and pass UInt32 times to the retarget arithmetic.
`work.next` converts a newest-first JSON array to the specification's finite view.
Its `work_view` errors are adapter errors, not Core consensus rejection codes.
The harness checks caller preconditions before it invokes Core and excludes those errors from the comparison.
Its skip-height guard leaves unavailable skip destinations null, so Core uses predecessor links instead.

No theorem covers these JSON conversions, the harness guard or correspondence to Core's traversal.

The hash operations convert exact hex bytes to ByteArray and return twenty digest bytes without reversal.
The header operations preserve raw u32 fields and both hash byte orders.
The header prefix reader maps codec failure to `read/truncated` and returns the exact suffix.
The Merkle adapter requires exact 32-byte internal-order leaves and rejects arrays larger than 2^31 entries before computation.

These JSON conversions have no refinement theorem.
The Core harness calls the pinned hash classes, pure header methods and `ComputeMerkleRoot` directly.
Finite fixture and boundary comparisons cover the recorded inputs only.
They establish no all-input Core equivalence, cryptographic security, AuxPoW validity, scrypt result or full block validity.

The Script adapters call `readInstruction`, `evalScript`, `verifyScript` and `verifyLegacySpend`.
Evaluation selects no checker or `baseChecker`. Legacy verification selects `baseChecker` or `transactionChecker` with `coreVerifier`.
They encode Script errors with the names in the [shared table](../../harness/core/script_error_names.inc).

No theorem covers their JSON conversions.
Adapter limits allow scripts above 10,000 bytes and caller stacks above 1,000 items, so those specification boundaries remain observable.
The adapter bounds scripts and individual items to 1 MiB, stacks to 4,096 items, and total caller item bytes to 4 MiB.
`pubkey.verify` bounds each key and signature to 1 MiB and requires exactly 32 storage-order digest bytes.
It calls `coreVerify`, while the harness calls `CPubKey::Verify`.
These bounds imply fewer than 2^31 items and at most `UINT_MAX` bytes per item, the documented Core-correspondence domains.

JSON parsing and line allocation occur before these execution limits.
The limits do not bound transport memory or the Lean runtime's allocations.

The Core harness calls `GetOp` and `EvalScript` in `SIGVERSION_BASE` with `BaseSignatureChecker`.
That checker fails every signature, locktime and sequence check.
Unsupported Lean calls have no compared verdict.
The comparator reports their reasons and Core outcomes separately, and compares supported calls regardless of the opcode support set.

Two-call corpus compositions pass only the successful main stack between calls.
They ignore each record's witness and do not run `VerifyScript`, evaluate P2SH or reproduce a transaction signature checker.

Separate legacy streams call `VerifyScript` on inside-milestone corpus records and seeded mutations with each checker.
The transaction selection checks the index and InputContext count bounds before execution.
It uses the supplied previous-output script, without a UTXO lookup.
Lean decides each reached signature check with `coreVerifier`.
With the transaction checker, only unsupported flags exclude a verdict from comparison agreement.

Core uses `TransactionSignatureChecker`, `CPubKey::Verify` and libsecp256k1, with `ECCVerifyHandle` for the request loop (D3, D50).
The harness signs nothing and does not need `ECC_Start`.
These libraries, their key and signature parsing, and their compiled binary form a trusted runtime boundary, not a Lean proof.

The harness rejects flag combinations that violate Core's WITNESS and CLEANSTACK assertions without altering the flags.
The comparator counts these requests separately as `harness-refused` only after it checks both the refusal and Lean's unsupported-flags answer.
Neither outcome is comparison agreement or a Script verdict.
Finite comparisons establish neither full transaction validity nor equivalence to Core on all inputs.

A wrong conversion could make the oracle and Core disagree, or agree, for a reason outside the specification.

The Core harness, `harness/core/core_oracle.cpp`, is the other side of the comparison ([docs/oracle.md](../oracle.md#the-core-harness)).
A user of the comparison trusts these parts of it:

- Core's libraries at the pin, compiled by the compiler of the machine that runs the comparison: GCC 13 in CI, on `ubuntu-24.04`.
  Core v1.14.9 was released for older compilers.
  The build script uses `-O2 -ffunction-sections -fdata-sections`, and Core's configure selects C++11.
  GNU ld discards unused sections with `--gc-sections`.
- The harness's own code. It converts hexadecimal text and JSON numbers to Core's arguments, writes Core's results as JSON, and maps four exception messages to read errors.
  Any other exception from Core stops the harness, so it cannot pass as a result.
- The `plan` label of `sighash.legacy`. The harness computes it from Core's conditions instead of observing it. It stops if the label is `fixed_digest` and Core's digest is not the value one.
- The comparator, `scripts/compare_core.py`.
  Its self-test, [`scripts/test_compare_core.py`](../../scripts/test_compare_core.py), reports 152 cases: two passing controls, 149 negative checks and one upfront assertion group.
  The negative checks are 137 stream mutations, eight Rust-side mutations, one acceptance-count gap, one request-count gap and two `--mainnet-blocks` fixture checks.
  Each negative check must fail with the code that it targets.
- For `sighash.legacy`, the oracle's preimage is checked by hashing it, not byte by byte: Core does not expose its preimage.

The separate `core-signer` tool generates [signed recovery-template fixtures](../../tests/script/signed-spends/README.md) with Core's `SignatureHash` and `CKey::Sign`.
Each expected verdict comes from Core's `VerifyScript`, with the digest and transaction recorded.
Fixture users trust the generator's template construction, high-S conversion, serialization and Core build.
The generator records its source blob and uses Core's randomness code with a stderr logging adapter.
Byte-for-byte regeneration checks reproducibility, but does not establish agreement with DogeLib.

`core-signer --fixed-digest` generates the [fixed-digest fixtures](../../tests/script/signed-spends/README.md#fixed-digest-spends) from `harness/core/core_signer_fixed_digest.cpp` in the same way.
Its users trust the generator's script and transaction construction in the same way, and its records have no source blob.

`scripts/convert_script_tests.py` transcribes Core's `BuildCreditingTransaction` and `BuildSpendingTransaction` (D46) into its `context` function.
The [Script corpus](../../tests/script/corpus/README.md) commits the transaction bytes that this function generates for each record.
`lake test`, the oracle and the Core harness all receive those generated bytes, and the transaction checker hashes them.
So agreement between the oracle and Core on them does not check that they are the transactions of Core's test runner.
Fixture users trust that transcription, which a reader checks against D46 (A1).

`lake test` runs all 25 signed fixtures through `verifyLegacySpend` with `coreVerifier` and each record's flags.
It compares both the Boolean verdict and the ScriptError name against Core's recorded values.
The oracle and live Core also compare all 25 records through `script.verify_legacy` with the transaction checker.
These checks cover the three 2-of-3 signer pairs, the recovery branch and every recorded mutation.
They provide finite comparison evidence, without a theorem about all signed spends.

`lake test` also runs the 44 fixed-digest records through the same comparison, and compares `legacySignatureHash` with the 142 digests that Core recorded.
The oracle and live Core compare the 44 spends and their 71 signature hashes.

Both programs could be wrong in the same way on an input that the comparison does not send.

The five header PoW operations are IO-adapter entry points into the existing specification definitions.
Their JSON conversion and Lean diagnostic strings have no refinement theorem.
The Core harness transcribes the two version branches for `block.check_version`.
For `block.contextual_check` it calls Core's `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
Users trust the transcription of the two version branches, and the entries that the harness puts into `mapBlockIndex` with its setting of `fCheckpointsEnabled` (D67, D69).
The harness turns off Core's debug log and log timestamps, which changes no consensus predicate.

The build disables SSE2, and its stamp records the generic scrypt variant and configure options.
The comparison still assumes Core's little-endian header memory layout and arithmetic shift of signed versions.
The contextual operation checks `ContextualCheckBlockHeader` on the stated input domain.
The caller supplies the predecessor view, adjusted time and known checkpoint state.
The contextual operation checks no node-state condition in `AcceptBlockHeader` or full-block validity.
The sequence operation adds the header-acceptance state transitions, with Core's `AcceptBlockHeader` and the placeholder predecessor described [above](#header-sequence-oracle-and-comparison).

For `block.subsidy` the harness calls Core's `GetDogecoinBlockSubsidy` with `Params().GetConsensus(height)` on mainnet, as `ConnectBlock` does (D101, line 1996).
It adds `boost_version`, the release of the Boost headers that Core's function was compiled with.
The oracle adds `redraws`, the number of words that the draw rejected.
Core does not report that number, so the comparison checks only its form.
The adapter refuses more than 65,536 cases in one request, a limit that Core does not have.

For `tx.check` the harness calls Core's `CheckTransaction` on a `CTransaction` that Core's stream code reads from the request.
For `block.check` it selects mainnet and calls Core's `CheckBlock` on a `CBlock` that Core's stream code reads.
The block is a new object in each request, so its member `fChecked` is false at the call.
The harness stops if that member is set.

The harness also calls `GetLegacySigOpCount` and `GetSerializeSize`, and reports their values for every verdict.
The oracle adds `diagnostic`, the Lean error with the position of a rejected transaction.
Core does not report it, so the comparison checks only its form.
The oracle reads blocks and transactions as byte lists, and `block.check` has no size limit of its own.

For `block.contextual_check_body` the harness selects mainnet and calls Core's `ContextualCheckBlock` on a `CBlock` that Core's stream code reads.
The request's `chain` is a view from the predecessor, newest first, with the height, time and `nBits` of each entry.
The harness requires consecutive heights, each from 0 to 2147483646, and builds a synthetic `CBlockIndex` for each entry with only these three fields.
It links each entry to the next older entry, and builds a skip pointer only when its target lies in the chain.
It passes the newest entry as the predecessor, or a null predecessor for an empty chain.

Before the call, the harness takes the aligned version-bits boundary at height `p - (p + 1) mod 10080` for the predecessor height `p`, when that height is not negative.
If the boundary's median time is at or after the CSV timeout 1493596800, the harness seeds the boundary entry in `versionbitscache`.
The seed is `THRESHOLD_FAILED` for CSV and SegWit.
If that median time is at or after the CSV start 1462060800 and before the timeout, the harness refuses the request.
The harness clears `versionbitscache` before and after each request.
The comparison trusts this seed ([the contextual block body](blocks.md#the-contextual-block-body)).

`block.contextual_check_body` and `block.validate` of the harness also take the argument `force_csv_active` ([design record 0012](../design/0012-relative-lock-time.md), section 10.2).
With the value true, the harness seeds `THRESHOLD_ACTIVE` for CSV at the boundary that the block reads, or at the null key below the first period.
Core's own `ContextualCheckBlock` then takes the median-time cutoff of lines 3134 and 3135, and no line of Core's source changes.
In `block.validate`, Core's own `ConnectBlock` then sets `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` and runs `SequenceLocks` (D114, lines 1906 to 1911 and 1948 to 1959).
The harness seeds nothing for a block without a predecessor, or for a block whose header has the genesis hash.

`block.validate` runs each block twice on the state before it: with the seed, for the object `forced` of the block record, and without it.
The harness removes the seed after the forced run, and that run flushes no coin.
So the carried coin set, the chain and every other field of the response are those of a request without the argument.
The comparison checks that equality on each made block.
A time lock of BIP 68 reads an ancestor at the height of the spent coin.

Three reads of `SequenceLocks` are outside the model of the revision: an ancestor below the supplied chain, a time lock on a coin above the block, and a coin height from 2^31 - 65535.
The harness scans each block for such a read before the forced `ConnectBlock`, and does not run Core on it. The object `forced` then names the reason, and has no verdict.
The scan is harness code, not Core's code. A user trusts that it finds each such read: a read that it misses reaches Core, which can then dereference a null pointer or leave the supplied chain.
The scan does not follow every exit of `ConnectBlock`, such as an earlier transaction that fails its own sequence lock. So it can name a read on a block that Core would reject earlier ([docs/oracle.md](../oracle.md#core-with-the-csv-state-forced-to-active)).
Agreement on such a block shows that the two programs draw the limit of the model at one place. It shows nothing about a verdict of Core.

The two seeds differ in kind.
`csv_never_lockedIn` supports `THRESHOLD_FAILED` as Core's own result on a mainnet chain, under its hypothesis.
No theorem supports `THRESHOLD_ACTIVE`, and no mainnet chain reaches it.
So the seed is a harness input, and the run shows what Core's code does in a state that Core never enters.
The result is evidence about the proposed revision `RelativeLockTime` alone ([COVERAGE.md](../../COVERAGE.md#proposed-revisions)). It is not evidence about mainnet, and it is not a Core comparison of the baseline.
`scripts/test_core_harness.py` checks that a request without the argument, after a request with it, gets the baseline result.

The oracle computes the candidate height and the two states from the same chain:

- It refuses a predecessor at height 2147483646 or above.
  Core can represent the candidate height 2147483647, and the harness accepts a predecessor at 2147483646.
  So this limit is the oracle's own, and narrower than Core's domain.
- It gives each state from the median time of the aligned boundary through `versionBitsStateFromBoundary`, and an adapter error between the CSV start and timeout.
- It passes the median time of the aligned boundary to the body in place of the median time of the predecessor.
  `versionBitsStateFromBoundary` never returns `ACTIVE`, and the body reads that value only when CSV is active.
- It gives the adapter error `noCoinbase` for a block with no transaction, or whose first transaction has no input.

The comparator fails on a response without a verdict, so these adapter errors and harness refusals are outside the comparison domain.

For `block.version_bits_state` the request's `chain` is a sequence of version and time pairs, oldest first.
Both programs take entry `i` as the block at height `i`, so the first entry is the genesis block.
Neither program checks that the sequence is a header chain or that it starts at the real genesis block.
So the comparison trusts the caller's sequence.

The harness builds a synthetic `CBlockIndex` for each entry with only its height, version and time.
It links each entry to the previous entry, builds its skip pointer and clears `versionbitscache` before and after each request.
It calls Core's `VersionBitsState` for CSV and SegWit on the last entry with the record of the next height, and seeds no state.
For an empty chain it returns `DEFINED` for both without a call.

The oracle computes `versionBitsStateFull` on the same sequence.
`scripts/compare_version_bits_walk.py` checks the links and the pinned checkpoints of the headers that it fetches before it compares.

For `block.validate` the harness calls Core's five checks of a new block on each block, in Core's order: `CheckBlockHeader`, `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock` and `ConnectBlock`.
It carries a coin set and a block index through the request.
[docs/oracle.md](../oracle.md#block-validation-in-the-harness) lists its choices.
Users trust these parts of the harness, which no Core function supplies:

- The coin view over a `std::map`, and the commit after an accepted block. `ConnectBlock` runs with `fJustCheck` true, so Core's own `SetBestBlock` and its writes do not run.
- The block index. It has one entry for each supplied chain entry and each accepted block, and `mapBlockIndex` holds one entry. An added predecessor carries the hash of the ancestor at `BIP34Height`. The harness refuses a request whose chain is too short for Core's other reads.
- The seed of `THRESHOLD_FAILED`, as for `block.contextual_check_body`.
- The digests. The harness reads the spent and created coins from a second cache, on which it calls Core's `UpdateCoins`. It requires that this cache ends equal to the cache of `ConnectBlock`.

Core runs with no script-check threads and a null `hashAssumeValid`, so the comparison covers that configuration alone.
The comparison of the coins is a comparison of digests.
The two programs agree on the chained double SHA-256 digests of the coin records and on the counts, and the comparator does not read the records.
So agreement shows equal coins only if double SHA-256 is collision resistant, which DogeLib does not model (A4).
The harness cannot observe a signed overflow in Core.
The comparator therefore sends it no block that the oracle reports as `outOfDomain`, and agreement says nothing about such a block.
The oracle keeps a whole request in memory, and `block.validate` has no size limit of its own.
A `block.validate` request with `blocks_file` is the exception: both programs read the named file one block at a time.
For that request the `dogelib-oracle` executable opens a file that the caller names, which no other operation does.
The read is in `Block.Exports.blockValidateFile`, an `IO` function outside the specification, and each block then goes through `validateStep`, the same function as a block of `blocks_hex`.
The comparison trusts that the file holds the intended blocks.
`scripts/replay_blocks.py` checks each block against a pinned hash before a replay.
That check shows the intended transactions only if SHA-256 is collision resistant, which DogeLib does not model (A4).

A request with `coins_file` also opens a coin-set snapshot that the caller names, and the oracle reads it twice.
The reads, the choice of the coins that the blocks name and the merge of the last digest are in `Block.Exports.blockValidateSnapshot`, an `IO` function outside the specification.
The blocks again go through `validateStep`.
The oracle with `coins_in_memory` runs the same request without the choice and the merge, and `scripts/snapshot_range.py` requires equal results of the two forms on its ranges.
A snapshot is a supplied state.
A comparison from it shows agreement on the blocks of the range only if the snapshot is Core's coin set at its height ([design record 0011](../design/0011-mainnet-ranges.md), section 3.4).

The harness wrote each snapshot of the recorded runs, with its own map and its own writer, which are harness code and not Core's.
The snapshot at height 145,000 has the digest that the oracle reached from the empty set in the recorded replay from the genesis block.
For the snapshot at height 9,000, the replay of heights 0 to 10,000 in CI compares the same digest between the oracle and the harness.
The recorded replay also compared the digest at height 100,000 between the two programs, with an earlier build of the harness.
Its record does not state the value.
Neither program checks that a snapshot file stays the same during a request, except that the oracle requires one number of records in both reads.

The ranges A, B, C, D, F and H of stage 2 start from the snapshots of the Core pass ([record](../oracle.md#ranges-a-to-h)).
The ranges E1 and E2 of stage 4 start from the snapshots of a second pass, which started from the snapshot of range D ([record](../oracle.md#the-csv-window-ranges-e1-and-e2)).
Each range from `a + 1` to `b` agrees under section 3.4 of [design record 0011](../design/0011-mainnet-ranges.md).

So each range shows a conditional statement.
Suppose that the snapshot at `a` is Core's coin set at height `a`.
Then the Lean definitions and Core give the same verdict and the same coin changes on each block of the range.
They also give the same set at `b`.
Equal digests show equal sets only if double SHA-256 is collision resistant.

For ranges B, C, D, E1, E2, F and H, no comparison discharges the hypothesis.
These arguments support it, range by range:

- **Range A**, from the snapshot at 145,000. The snapshot has the digest that the oracle reached from the empty set in the recorded replay. So range A needs no assumed start state beyond that digest.
- **Ranges B, C, D, F and H**, from the snapshots at 370,336, 598,999, 1,033,382, 3,463,750 and 5,049,000. The harness ran Core's `ConnectBlock` on every block from the genesis block to `a`. The oracle checked the blocks up to height 145,000 and inside the earlier ranges, and no others. An error of the Lean definitions on a block between the ranges stays unseen.
- **Ranges E1 and E2**, from the snapshots at 1,198,519 and 1,702,519 of the second pass. The second pass started from the first pass's snapshot at 1,033,382 and ran Core's `ConnectBlock` on every block above it. It reached the first pass's digest at 1,035,382 and at the seven segment ends of the first pass from 1,099,999 to 1,699,999. So the two passes agree at those heights, and the arguments of range D hold for both snapshots.
- **The set.** Core's `CCoinsViewDB` and `CCoinsViewCache` carried the set in the pass. The harness's reads of the coin changes, its snapshot writer and its digest are harness code. A fault there can give both programs one wrong start state.
- **The tip.** At height 6,465,793, Core's `hash_serialized`, `transactions` and number of coins of the pass's set equal those of the maintainer's node (decision 7). So the two sets have the same coins, with the same amounts and scripts, if double SHA-256 is collision resistant. That hash does not cover the height or the coinbase flag of a coin, so the equality does not extend to them. The agreement at the tip does not show the set at an earlier range start.
- **The arithmetic.** The pass ran the build that ends on a signed overflow in `validation.cpp` and `coins.cpp`, and it did not end. So no sum of `ConnectBlock` left the `int64_t` range, if the sanitizer finds every such overflow.
- **The context.** The chain, the ancestor hash and the block below the range come from the headers that the pass kept. Both programs get the same context.
- **The blocks.** The pass required each checkpoint of Core. The committed hash list of each range is on the chain of the first checkpoint above it ([fixtures](../../tests/block/mainnet-blocks/README.md#range-hash-lists)).

The request of 10,001 real blocks has about 88 MB of JSON.
