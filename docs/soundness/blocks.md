# Soundness: Block Validation, Subsidy, and Coin Sets

This file states what the subsidy, `CheckTransaction`, `CheckBlock`, version-bits, contextual-body, `ConnectBlock`, and block-restriction proofs establish.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: Block subsidy, block codec, `CheckTransaction`, `CheckBlock`, version bits, `ContextualCheckBlock`, `ConnectBlock`, `validateBlock`, issuance bounds, and coin-set restriction.
- **Specification modules**: `DogeLib.Block.Subsidy`, `Block`, `Check`, `VersionBits`, `ContextualBody`, `Coins`, `TxInputs`, `SigOpCost`, `Connect`, `Validate`, and `DogeLib.Transaction.Check` and `SigOps`.
- **Proof modules**: `DogeLib.Block.Proofs.*` (`Subsidy`, `Block`, `Check`, `VersionBits`, `ContextualBody`, `SigOpCost`, `Connect`, `ConnectProperties`, `Restrict`), `DogeLib.Transaction.Proofs.Check`, and `SigOps`.
- **Key boundaries**: `ContextualCheckBlock`, `ConnectBlock`, `validateBlock`, and `getDogecoinBlockSubsidy` model mainnet rules only, with random subsidies pinned to Boost 1.70.0 (A5, D2).
  No theorem proves that the real mainnet chain satisfies `csv_never_lockedIn` or that C++ signed sums never overflow outside `connect_fits`.

## Block subsidy

`getDogecoinBlockSubsidy` in `DogeLib.Block.Subsidy` follows Core's `GetDogecoinBlockSubsidy` (D104, lines 127 to 149) with the mainnet records, design record 0010, stage 0010a.
Below height 145,000 the subsidy is `(1 + rand) * COIN`, and `rand` is one value of `boost::uniform_int<>(1, maxReward)` from a `boost::mt19937`.
`subsidySeed` reads the seed from characters 7 to 13 of the display form of the previous block hash.
From 145,000 the subsidy is `(500000 * COIN) >> (nHeight / 100000)`, and from 600,000 it is `10000 * COIN`.
The source review, not a theorem, connects these definitions to Core and to Boost.

Core's text does not contain the random value.
It comes from Boost, which is no part of the Core pin: Core accepts Boost 1.60 or later.
`Mt19937` and `uniformInt` follow Boost 1.70.0 (BO1 to BO3), the release that the Core harness builds.
A Core built with a Boost release that draws in another way can pay other subsidies, and no claim here covers it.
[SOURCES.md](../../SOURCES.md#reference-pins) records the Boost pin.

`uniformInt` covers one branch of Boost's `generate_uniform_int`: `int` bounds, a 32-bit engine and `2 ≤ maxValue ≤ 2^31 - 1`.
On mainnet `maxReward` is 999,999 or 499,999, so `getDogecoinBlockSubsidy` stays in that branch.
The definitions use natural numbers where Boost uses 32-bit unsigned values.
On the stated domain no step of Boost's arithmetic wraps. That statement is a comment in the source, not a theorem.

The domain of `getDogecoinBlockSubsidy` is a height from 0 to `2^31 - 1`.
It has the mainnet records only.

Boost's rejection loop has no bound, and the library has no proof that it ends.
So `uniformInt` takes fuel, and `getDogecoinBlockSubsidy` returns `fuelExhausted` when the draw rejects that many words.
`fuelExhausted` is no result of Core.
The oracle uses `subsidyFuel`, 624 words.
A run outside CI compares all `2^28` seeds for both ranges, and the oracle returns a value for each ([COVERAGE.md](../../COVERAGE.md#operations), *Block subsidy*).
That run is test evidence for the compiled code, not a theorem about `uniformInt`.

`uniformInt_preimages` is about one word of the draw, `uniformIntAccept`, on the two mainnet ranges.
The bucket sizes are 4,294 and 8,589, and `maxReward * bucket ≤ 2^32`.
A word gives `value` exactly when `1 ≤ value ≤ maxReward` and the word lies in `[(value - 1) * bucket, value * bucket)`.
A word is rejected exactly when it is at least `maxReward * bucket`.
So each value has exactly `bucket` words, and a draw by remainder or with another bucket size fails the statement.

The theorem does not relate `uniformIntAccept` to Boost's code.
It says nothing about the generator or about the number of words that a draw reads.

`Mt19937.output_seed_10000` shows that output 10,000 of the default seed 5489 is 4123659995, the value that the C++11 draft requires of `mt19937` (S3).
It is one output of one seed.
The kernel evaluates the array updates of `seed` and `twist` slowly, so the proof evaluates a list evaluator in their place.
`Mt19937.output_seed_eq` proves that the evaluator gives the outputs of `seed`, `twist` and `next` for every seed and every output number.
The evaluator is in the proof library, and no compiled code runs it.

No theorem states a distribution of the subsidy, and none bounds its value.
`getDogecoinBlockSubsidy` does not read a coinbase.
`connectBlock` adds the fees to the subsidy and compares the sum with the coinbase value (D101, line 1996).
[`connect_value_bound`](#connect_value_bound-a-block-adds-at-most-its-subsidy) bounds the value that an accepted block adds by its subsidy, on a coin set whose amounts are in range.

The comparison evidence is in [COVERAGE.md](../../COVERAGE.md#operations).
`lake test` runs Core's three subsidy tests (D105) through the compiled code.
The oracle operation `block.subsidy` compares the definition with Core's own function ([B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)).
Its cases include every mainnet height from 1 to 145,000.
[docs/reviews/subsidy.md](../reviews/subsidy.md) records a model read of the definitions against Core and Boost.

By `#print axioms`, `Mt19937.output_seed_eq` and `Mt19937.output_seed_10000` depend on `propext` and `Quot.sound`.
`uniformInt_preimages` depends on `propext`, `Classical.choice` and `Quot.sound`.

## Block codec, `CheckTransaction` and `CheckBlock`

`Block.read` and `Block.encode` in `DogeLib.Block.Block` follow `CBlock::SerializationOp` (D108): a full header, a CompactSize count and the transactions.
`checkTransaction` in `DogeLib.Transaction.Check` follows Core's `CheckTransaction`, and `checkBlock` in `DogeLib.Block.Check` follows `CheckBlock` (D106).
`Transaction.getLegacySigOpCount` in `DogeLib.Transaction.SigOps` follows `GetLegacySigOpCount` with `CScript::GetSigOpCount(false)` (D106, D107).
They are the second part of design record 0010, stage 0010a.
The source review, not a theorem, connects these definitions to Core.

Each check returns Core's first failure in source order.
An error has the reject reason, the denial-of-service score and the reject code that Core's `CValidationState` holds, and `checkBlock` also gives `CorruptionPossible`.
`checkBlock` reports each failure of the header check as `high-hash`, as `CheckBlockHeader` does.

The definitions differ from the C++ in these places:

- `CheckBlock` returns true at once when the memory-only member `fChecked` is set. `checkBlock` has no such state. It is the check of a block with `fChecked` false. A block that Core reads into a new `CBlock` has that state. The reader does not clear the member, so a read into an object with `fChecked` set is outside the definition.
- `checkOutputs` adds the output amounts in the integers. Core adds in `int64_t`, and the sum there is at most `2 * MAX_MONEY`, below `2^63`. That bound is an argument in the module documentation, not a theorem.
- The counts of signature operations are natural numbers. Core counts in `unsigned int`. `checkBlock` reduces the product with `WITNESS_SCALE_FACTOR` modulo `2^32` before the comparison, so the two agree for every count.
- `hasDuplicate` inserts a numeric key of each outpoint into a `Std.TreeSet`, where Core inserts the outpoints into a `std::set`. The order of the keys is not Core's order of outpoints, and the test does not depend on the order. `hasDuplicate_eq_hasDuplicateScan` proves it equal to `hasDuplicateScan`, which compares every pair, and `hasDuplicate_eq_not_nodup` proves that it is true exactly when two inputs have the same outpoint.
- The instruction reader of the sigop count covers a script of fewer than `2^31` bytes, the domain of `readOp`. The count reads with `nextOp`, and `nextOp_view` proves that `nextOp` reads the instructions that `readOp` reads.
- `checkBlock` takes the network of its header check as a parameter. The oracle and the comparison use mainnet, and testnet and regtest have no comparison evidence here.

No statement of `CheckTransaction` or `CheckBlock` reads a witness stack, so the definitions take the base fields of each transaction.
A block with witness data can pass `checkBlock`. `ContextualCheckBlock` rejects such a block on main and test, and DogeLib defines that function for mainnet only ([the contextual block body](#the-contextual-block-body)).

`Block.read_encode_allowWitness` and `Block.read_encode_base` are round trips over encoder output, under the conditions `Block.RoundTripsAllowWitness` and `Block.RoundTripsBase`.
Those conditions bound every count by `MAX_SIZE` and require a payload exactly when the AuxPoW flag is set.
In the witness-allowed mode each transaction must also have witness data, or an input, or no output.
The base-mode reader returns the base projection of the block, without witness stacks.
Neither theorem says that an accepted byte string is the encoding of its result, and neither says which error the reader reports.

`MerkleDuplication.root_eq_and_mutated` is about `merkleRoot` and `merkleMutated`.
`MerkleDuplication xs ys` holds when `ys` comes from `xs` by one or more duplications of a trailing subtree.
One step appends a copy of the last `2^k` hashes of a list of `2^k * c` hashes, for an odd `c` of at least 3.
The theorem shows that `ys` has the root of `xs` and sets the mutation flag.
It assumes nothing about SHA-256.

`checkBlock_rejects_merkleDuplication` carries that result to blocks.
Let `checkBlock` accept a block with the Merkle check, and let a second block have the same header and a `MerkleDuplication` of its transaction IDs.
Then `checkBlock` rejects the second block with `duplicateTransactions`, the reject reason `bad-txns-duplicate`.
A definition that compared only the root would accept both blocks, which is the fault of CVE-2012-2459.
The theorem does not cover two lists with one root for another cause, such as a hash collision.
It is a statement about `checkBlock`, and it does not show that Core's `CheckBlock` has the property.

`Script.getSigOpCount_le` bounds the count of a script by 20 times the number of its bytes.
It does not bound the count of a block, and no theorem shows that Core's `unsigned int` count never wraps.
`checkBlock` needs no such theorem, because it takes the product modulo `2^32`.

No theorem relates `checkTransaction` to a property of the outputs, and none states which failure comes first.
The comparison with Core tests the order of the failures ([COVERAGE.md](../../COVERAGE.md#operations)).

The comparison evidence is in [COVERAGE.md](../../COVERAGE.md#operations).
`lake test` runs Core's corpus, Core's sigop test and the genesis block through the compiled code.
Two records of `tx_invalid.json` have comments that name `MAX_MONEY`, with amounts near the bound of Bitcoin, 2,100,000,000,000,000.
Dogecoin's bound is `10^18`, so `CheckTransaction` accepts both records, and they fail Core's test for another reason.
The oracle operations `tx.check` and `block.check` compare the definitions with Core's own functions ([B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)).

`block.check` also runs on 11,018 real mainnet blocks, with both flags.
[D3](../../SOUNDNESS.md#d3-wrong-fixtures) states how each block is authenticated.
It also states what the comparison shows for a block with no pinned hash.
[docs/reviews/blockcheck.md](../reviews/blockcheck.md) records a model read of the definitions against Core.

By `#print axioms`, `MerkleDuplication.root_eq_and_mutated` and `Script.getSigOpCount_le` depend on `propext` and `Quot.sound`.
`Script.getSigOpCount_eq_scanOps`, `nextOp_view` and `foldOps_eq` depend on `propext` and `Quot.sound`.
`OutPoint.key_inj` depends on `propext` and `Quot.sound`, and `hasDuplicateScan_eq_not_nodup` on `propext` only.
`hasDuplicateFrom_iff`, `hasDuplicate_eq_not_nodup` and `hasDuplicate_eq_hasDuplicateScan` depend on `propext`, `Classical.choice` and `Quot.sound`.
`checkBlock_rejects_merkleDuplication`, `Block.read_encode_allowWitness` and `Block.read_encode_base` depend on `propext`, `Classical.choice` and `Quot.sound`.

## Version bits

`DogeLib.Block.VersionBits` models Core's `VersionBitsState`, as `AbstractThresholdConditionChecker::GetStateFor` computes it (D102).
A deployment has a start time, a timeout, a signalling bit, a confirmation window and an activation threshold.
`versionBitsCondition` is Core's `Condition`: a block signals a deployment when the top three version bits are `001` and the deployment's bit is set.
`versionBitsWalk` folds `thresholdStep` over the period boundaries from the genesis period.
`thresholdStep` folds the reset of Core's backward walk into one step: a boundary whose median time is below the start time gives `DEFINED` whatever the state before it.
So the fold over every boundary equals `GetStateFor` at the last boundary.
The source review, not a theorem, connects the fold to the imperative algorithm of Core, and the run outside continuous integration gives the empirical evidence.
That run of 2026-11-13 compared the full walk with Core at 11 period boundaries through the CSV window on the real mainnet header chain, and agreed at each for CSV and SegWit, across `DEFINED`, `STARTED` and `FAILED`.

`csv_never_lockedIn` takes a chain of full headers from the mainnet genesis in which every header passed `checkBlockHeader .mainnet`.
On mainnet `checkBlockHeader` runs `CheckAuxPowProofOfWork` with a strict chain ID of `0x62`.
That check accepts a header only if it is legacy, with version 1 or 2, or has the chain ID `0x62`.
Both leave the top three version bits `000`, so `versionBitsCondition_false_of_checkBlockHeader` shows that no such header signals.
With no signals every period has a zero count, and a walk with no signals never leaves `DEFINED`, `STARTED` or `FAILED`.
So the CSV and SegWit states are never `LOCKED_IN` or `ACTIVE`.

The hypothesis is about a genesis-rooted chain whose headers pass the check, and an arbitrary supplied index does not meet it.
No theorem shows that the real mainnet chain meets the hypothesis.
The median time of each boundary comes from the chain, so the conclusion holds whatever the times are.
The theorem does not cover testnet, where `fStrictChainId` is false, or regtest.

`versionBits_shortcut` takes a positive threshold, a boundary list with no signals and the shortcut's result at the last boundary.
When the median is below the start time the state is `DEFINED`, and when it is at or after the timeout the state is `FAILED`.
The `FAILED` case uses `walk_notLockedIn`: with a positive threshold, a walk over boundaries with no signals is never `LOCKED_IN` or `ACTIVE`.
So the state before the last boundary is `DEFINED`, `STARTED` or `FAILED`, and each goes to `FAILED` at or after the timeout.
The threshold hypothesis is necessary: with a threshold of 0, a period with no signals can enter `LOCKED_IN`.

`versionBitsWalk_reset` shows that a boundary whose median time is below the start time resets the walk.
Take any boundaries before such a boundary and any boundaries after it.
Then the walk over all of them gives the state of the walk over the boundaries after it, from `DEFINED`.
The theorem holds for every threshold and every signal count.
`versionBitsStateFull_of_reset` applies it to the boundaries of a chain from the genesis block.
The reset is the stop of Core's backward walk: Core walks forward only over the boundaries above the latest boundary below the start time.

`block.validate` uses this walk in the case-3 gap of CSV (design record 0011, stage 4).
Its adapter `csvWindowState` walks back from the aligned boundary to the latest boundary whose median time is below the CSV start.
For each boundary above that one, it reads the median time and the CSV signal count from the request's chain view and versions.
Then it returns `versionBitsWalk` over those boundaries.

No theorem shows that these boundaries are those of `chainBoundaries` of the chain from the genesis block.
The adapter computes them from a finite view, and the request supplies that view, as for every other context of `block.validate`.
A comparison gives the evidence for the adapter.
In `scripts/test_core_pass.py`, the oracle and the harness report the same state in `block.validate` at 16 boundaries of three synthetic chains.
The states cover all five, and each equals both full walks.
The ranges E1 and E2 compare the states on mainnet ([recorded runs](../oracle.md#the-csv-window-ranges-e1-and-e2)). Both programs report `DEFINED` and `STARTED` in E1, and `STARTED` and `FAILED` in E2.
The walk can give `ACTIVE` on a made chain that signals. `block.validate` then returns the error `outside_model` before the checks of the block, because its context holds the aligned boundary's median time and not the predecessor's.

On mainnet the walk changes no verdict.
`block.validate` reads the state only to test whether CSV is active, and `csv_never_lockedIn` shows that it is not, on a chain that meets its hypothesis.
The walk lets a request whose boundary is in the gap get a result in the place of an adapter error.

By `#print axioms`, `csv_never_lockedIn` and `versionBitsCondition_false_of_checkBlockHeader` depend on `propext`, `Classical.choice` and `Quot.sound`, and `versionBits_shortcut` depends on `propext` and `Quot.sound`.
`versionBitsWalk_reset` and `versionBitsStateFull_of_reset` depend on `propext` and `Quot.sound`.

## The contextual block body

`DogeLib.Block.ContextualBody` models Core's `ContextualCheckBlock` on mainnet (D110), the third part of design record 0010, stage 0010a.
`contextualCheckBlockBody` checks the finality of every transaction, the BIP34 coinbase height from 1,034,383, the absence of witness data, and the block weight, in Core's order.
The source review, not a theorem, connects the definition to Core.

The body takes the CSV and SegWit states as inputs, where Core calls `VersionBitsState`, and reads only whether each state is `ACTIVE`.
`csv_never_lockedIn` and `segwit_never_active` show that neither is active on a header chain from the mainnet genesis in which every header passed `checkBlockHeader .mainnet`.
No theorem shows that the real mainnet chain meets this hypothesis.
On a chain that meets it, the lock-time cutoff is always the block time, and the witness-commitment branch never runs.
So on such a chain the two reasons behind that branch, `bad-witness-nonce-size` and `bad-witness-merkle-match`, are unreachable.
This body returns the adapter error `segwitActive` on an active SegWit state, which the mainnet comparison never sends, and it never returns those two reasons.

The harness builds the block's predecessor and the aligned version-bits boundary from the request's chain, and lets Core compute `VersionBitsState`.
At a boundary whose median time is at or after the CSV timeout, the harness installs `THRESHOLD_FAILED` for CSV and SegWit.
It writes the state into `versionbitscache` for that request only.
The seed lets the harness answer without the dense block history that Core's walk would otherwise read.

For `block.contextual_check_body`, a boundary in the gap between the CSV start and timeout is an adapter error, outside the comparison domain.
So no continuous-integration request depends on the seed in that gap.
`block.validate` walks the gap in both programs from a chain with versions, and the harness installs no seed there (see *Version bits* above).
This seed is a harness input, so the comparison trusts it.

`csv_never_lockedIn` shows that the state is never `LOCKED_IN` or `ACTIVE` on a chain that meets its hypothesis.
With Core's positive threshold, `versionBits_shortcut` then shows that the full walk gives `FAILED` at a boundary at or after the timeout.
The source review connects the walk to Core's `GetStateFor`, so on such a chain `FAILED` is Core's own result.

No theorem shows that the real mainnet chain meets the hypothesis.
The version-bits walk outside continuous integration gives finite evidence for the real chain.
On 2026-11-13 it agreed with Core's `VersionBitsState`, which ran on the full chain without the seed, at 11 period boundaries through the CSV window.
The boundaries include some at or after the timeout, and the run compared both CSV and SegWit.
The run checks the links and the pinned checkpoints of the fetched headers.
It does not run `checkBlockHeader` on them, and it compares only those 11 boundaries.

`bad-blk-weight` is reachable when the body runs alone, because the body has no base-size check.
`contextualBody_badBlkWeight_unreachable_after_checkBlock` shows that `block.validate` of stage 0010b, which runs `CheckBlock` first, cannot reach it when the AuxPoW payload transaction has no witness data.

After `CheckBlock` accepts a block, the base size is at most `MAX_BLOCK_BASE_SIZE`.
If any transaction has witness data, the witness check returns `unexpected-witness` before the weight check.
Otherwise, under the hypothesis that the AuxPoW payload transaction has no witness data, the full size equals the base size, so the weight is four times the base size and at most `MAX_BLOCK_WEIGHT`.
That hypothesis excludes some real mainnet blocks: pull request #152 found that the AuxPoW parent coinbase of blocks 6,455,642, 6,456,071 and 6,456,247 carries witness data that Core accepts.
The theorem does not cover a block whose AuxPoW payload transaction has witness data.

The comparison evidence is in [COVERAGE.md](../../COVERAGE.md#operations) and [docs/oracle.md](../oracle.md#contextual-block-body-comparison-evidence).
`block.contextual_check_body` compares the verdict, the reject reason, the denial-of-service score and the reject code with Core's own `ContextualCheckBlock` ([B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)).
[docs/reviews/contextualbody.md](../reviews/contextualbody.md) records a model read of the definitions against Core.

By `#print axioms`, `contextualBody_badBlkWeight_unreachable_after_checkBlock` and `segwit_never_active` depend on `propext`, `Classical.choice` and `Quot.sound`.

## The coin set, `CheckTxInputs` and `ConnectBlock`

Five modules model Core's `ConnectBlock` on mainnet and the functions that it calls: `DogeLib.Block.Coins`, `TxInputs`, `SigOpCost`, `Connect` and `Validate` (D113 to D116, design record 0010, stage 0010b).
`Validate` also gives the order of the five checks of a new block.
The source review, not a theorem, connects the definitions to Core.
[docs/reviews/connect.md](../reviews/connect.md) records a model read of the definitions against Core.

**The coin set.**
`CoinSet` has one `TxCoins` entry for each transaction ID, as Core's `CCoins`.
It leaves out `nVersion`, `Cleanup`, the cache flags and the layers of caches, and it removes an entry that becomes pruned.
Each read of validation goes through `IsAvailable` or `IsPruned`, so none of these differences changes a result that the definitions use.
No theorem states this.
The map is `Std.TreeMap` of Lean's standard library, which `lake exe check-decls` accepts as code that the kernel can unfold.

**The arithmetic domain.**
Core adds `int64_t` amounts in four places before any range check (design record 0010, section 3):

- `GetValueIn` adds the amounts of a transaction's coins.
- `ConnectBlock` adds each fee to `nFees` before `CheckInputs` runs.
- `ConnectBlock` adds the subsidy to `nFees`.
- `CheckTxInputs` adds each amount before it tests the amount and the sum.

A sum outside the `int64_t` range is undefined behaviour in C++, so Core's source does not define its result on such a block.
The definitions compute in the integers.
When one of those sums leaves the range, `connectBlock` returns `outOfDomain`.
That result is not a verdict, and it claims nothing about Core.

`connect_fits` proves that `connectBlock` never returns `outOfDomain` under two hypotheses:

1. `CoinSet.ValuesInRange`: every output that the coin set holds has an amount from 0 to `MAX_MONEY`.
2. `spentValue`, plus `MAX_MONEY` and the subsidy, is below `2^63`.

`spentValue` adds the amounts of the coins that all input occurrences of the block spend.
It values each transaction against the set just before it, with the unchecked change `applyTransaction` between transactions.
So it counts a coin that an earlier transaction of the block created.
It is defined for every block, so the bound also covers a block that `connectBlock` rejects.

Hypothesis 1 holds for the empty set, and the oracle refuses a supplied amount above `MAX_MONEY`.
`connectBlock` runs `CheckTransaction` on every transaction before it changes the set.
`applyTransaction_range` shows that the change of one such transaction keeps hypothesis 1.
`connect_valuesInRange` shows that the result of an accepted `connectBlock` keeps it.
Hypothesis 2 holds for real blocks by a wide margin.
It does not hold for the total supply, which is above `2^63` koinu, so the theorem is about one block and not about a chain.

`connect_fits` is a statement about the Lean sums.
It does not prove that Core's compiled code computes those sums, or that a compiler keeps the source order of Core's additions.

**The unreachable fee reasons.**
`checkTxInputs_ne_feeNegative` and `checkTxInputs_ne_feeOutOfRange` prove that `checkTxInputs` never returns the two fee failures.
The second holds for an output total that is not negative.
`connectBlock_ne_feeNegative` and `connectBlock_ne_feeOutOfRange` prove that `connectBlock` never rejects a block with either reason.
They hold for every verifier, context, coin set and block.

**The sequence-lock reason.**
The reason `bad-txns-nonfinal` of `ConnectBlock` has no theorem, and `connectBlock` has no such test.
The module `DogeLib.Block.Connect` cites the argument.
Without an active CSV state, Core's lock pair is (-1, -1), and no height or median time past is below 0.
With an active CSV state `connectBlock` returns `csvActive`, which is outside the model.
`csv_never_lockedIn` shows that this state does not occur on a mainnet header chain whose headers pass the header checks.

**Results outside the model.**
`connectBlock` returns six results that are not Core's: `outOfDomain`, `csvActive`, `scriptUnsupported`, `subsidy`, `newCoinsExist` and `contextBounds`.
`newCoinsExist` marks a transaction that is not a coinbase and has the ID of an entry that is not pruned.
Core's `ModifyNewCoins` then throws `std::logic_error` or replaces the entry, by the state of its cache.

With BIP30 enforced, an earlier transaction of the same block made that entry, so two transactions of the block have one ID.
Two equal transactions do not reach the result, because the second finds its inputs spent.
So only a collision of double SHA-256 reaches it.
With BIP30 skipped, an entry of an earlier block also reaches it.
No theorem states this, and no comparison request reaches the result.

**Script verification.**
`connectBlock` takes the elliptic-curve check as the parameter `verify`, as `verifyLegacySpend` does.
The oracle passes `coreVerifier`.
The agreement of `coreVerifier` with Core is the A1 claim of [Secp256k1 public-key parser and Core's verifier](cryptography.md#secp256k1-public-key-parser-and-cores-verifier).

The definition describes Core with no script-check threads and no assumed-valid block, where Core checks every script in input order.
With check threads, the reject reason is that of the first failing check that a thread reports.
With an assumed-valid block, Core skips the scripts.
Neither configuration is modelled.

**The readers of the signature-operation cost.**
`getSigOpCountAccurate` and `p2shSigOpCount` read scripts with `nextOp`, in steps linear in the length of the script (issue #149).
`getSigOpCountAccurate_eq_scanOps` proves the accurate count equal to `accurateSigOps` over the opcodes of `scanOps`.
`p2shSigOpCount_eq_lastPushFrom` proves the P2SH count equal to the same count with the loop `lastPushFrom`, which reads with `readInstruction`.
By `#print axioms`, `getSigOpCountAccurate_eq_scanOps` depends on `propext` and `Quot.sound`.
`lastPushFrom_eq_lastPushLoop` and `p2shSigOpCount_eq_lastPushFrom` depend on `propext`, `Classical.choice` and `Quot.sound`.

**Block validation.**
`validateBlock` is the composition of the five checks in the order of `AcceptBlockHeader`, `AcceptBlock` and `ConnectBlock`.
It is not Core's `AcceptBlock` or `ProcessNewBlock`: it has no block index, it chooses no chain, and it writes nothing.
The caller supplies the view of the predecessor and establishes that `hashPrevBlock` names it.

The comparison evidence is in [COVERAGE.md](../../COVERAGE.md#operations) and [docs/oracle.md](../oracle.md#block-validation-comparison-evidence).
`block.validate` compares each block's verdict, reason, score and code with Core's own functions, and compares the digests of the coins ([B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)).

By `#print axioms`, `connect_fits`, `checkTxInputs_ne_feeNegative`, `checkTxInputs_ne_feeOutOfRange`, `connectBlock_ne_feeNegative` and `connectBlock_ne_feeOutOfRange` depend on `propext`, `Classical.choice` and `Quot.sound`.

## `connect_spends_available`: each input spends a present coin

`connect_spends_available` (in `DogeLib.Block.Proofs.ConnectProperties`) is the first property of design record 0010, section 6.
Suppose that `connectBlock` accepts a block on a coin set, and that the block's hash is not the hash of the mainnet genesis block.
Let `tx` be a transaction of the block that is not a coinbase.
`coinsBefore` is the set just before `tx`: the first set after the changes of the earlier transactions of the block.
So a coin that an earlier transaction of the block created is in `coinsBefore`, unless a transaction between them spent it.
The theorem has three conclusions:

1. The outpoints of the inputs of `tx` are pairwise different.
2. Every input of `tx` has a coin in `coinsBefore`.
3. After the spends of `tx`, no input of `tx` has a coin.

Conclusion 1 is the part that excludes the bug class of CVE-2018-17144, in which one transaction of a block names an outpoint twice.
Without it, conclusion 2 holds for two inputs that name one present coin.
The proof takes conclusion 1 from the duplicate-input check of `checkTransaction`, which `checkBlock` runs inside `connectBlock`.

The theorem holds for every verifier, both values of `fJustCheck`, every context and every coin set.
It does not need `CoinSet.ValuesInRange`.
`connectBlock_ok_coins` shows that `coinsBefore` at the end of the block is the new set of the result.

**The genesis hash.**
`connectBlock` accepts a block with the hash of the mainnet genesis block after `checkBlock` accepts it and before the transaction loop.
Core's `ConnectBlock` does the same (D114, lines 1804 and 1821 to 1825).
`connectBlock_genesis` states that case: the result is the unchanged set, with no change.

Conclusions 2 and 3 describe the transaction loop, which does not run in that case.
So the theorem has the hypothesis that the hash is another one.
The hypothesis follows Core's own special case.

**Coins as created, not outpoints.**
Conclusion 3 is about the set after the spends of `tx` and before the outputs of `tx` enter.
A later transaction with the same ID can create another coin at an outpoint that was spent.
That can occur when every coin of the earlier entry is spent, or for a coinbase with BIP30 skipped.
The theorem does not exclude a spend of the later coin, because it is another coin at the same outpoint.

The theorem does not say that the scripts of the inputs pass, that a coinbase coin is mature, or that the amounts suffice.
`connectBlock` tests those conditions, and no theorem here states them.

## `connect_value_bound`: a block adds at most its subsidy

`connect_value_bound` is the second property of design record 0010, section 6.
`CoinSet.totalValue` is the sum of the amounts of all the outputs that the entries of a set hold, in the integers with no bound.
Suppose that the coin set has amounts in range (`CoinSet.ValuesInRange`), and that `connectBlock` accepts a block on it.
Then the total value of the new set is at most the total value of the first set plus `subsidyValue` of the context.

The total counts each coin that `CoinSet.coin` returns once.
It also counts an output that `CoinSet.coin` cannot return.
Such an output is in an entry whose key is not `txidKey` of a transaction ID, or it has an index of `2^32` or more.
`CoinSet.addTx` stores each entry under `txidKey` of its transaction ID, and no theorem states that a set has no such output.
An extra output only raises the total, so the bounds of this section also bound the coins that `CoinSet.coin` returns, for amounts that are not negative.

Design record 0010 also lists a successful subsidy and the arithmetic domain of its section 3 as assumptions.
For a block whose hash is not the genesis hash, `connectBlock_ok` derives from acceptance that the subsidy has a value.
Acceptance also means that the result is not `outOfDomain`, so each sum that the run tested was in the `int64_t` range.
Acceptance does not give the bound of `connect_fits`, which is a sufficient condition for that domain and not a necessary one.
So the theorem has `CoinSet.ValuesInRange` as its only hypothesis besides acceptance.
For a block with the genesis hash, the set does not change, and the bound holds because a subsidy is not negative.

The proof follows the fees.
A transaction that is not a coinbase removes the coins of its inputs and adds its outputs, and `nFees` grows by the difference.
`checkBlock` accepts one coinbase, in the first position, and `connectBlock` accepts it only when it pays at most `nFees` plus the subsidy.
The proof needs the pairwise different outpoints of `connect_spends_available`: a coin that two inputs name would count twice in `nFees` and leave the set once.

The bound is an upper bound only, for three reasons:

- A coinbase can pay less than `nFees` plus the subsidy.
- An unspendable output does not enter the set.
- A new entry replaces an earlier entry of the same transaction ID, whose coins leave the set. The proof uses `CoinSet.ValuesInRange` here, and only for the lower bound 0.

`connect_valuesInRange` proves that the new set has amounts in range, so the hypothesis holds again for the next block.
The theorem relates two Lean sums.
It does not show that Core's coin database has that total.
`subsidyValue` is the subsidy of the supplied context, whether or not the context belongs to the block.

## `chain_issuance_bound`: a chain holds at most the sum of its subsidies

`chain_issuance_bound` is the third property of design record 0010, section 6.
`connectChain` runs `connectBlock` on a list of blocks in order, each with its own context, and gives each block the set of the block before.

Take a block with the hash of the mainnet genesis block, and a list of blocks after it.
Suppose that `connectChain` accepts all of them from the empty set.
Suppose also that the contexts are linked (`ChainLinked`).
So the heights are 1, 2 and so on, and each previous hash is the hash of the block before.
Then the total value of the final set is at most `chainSubsidy`, the sum of the subsidies of those heights and hashes.

The genesis block adds no coin, so its subsidy is not in the sum.
The empty set has amounts in range, and `connect_valuesInRange` keeps that property, so the theorem has no hypothesis on amounts.
The sum is an integer with no `int64_t` bound, because the supply is above `2^63` koinu.
The bound is an upper bound only, for the three reasons of `connect_value_bound`.

`connectChain_issuance_bound` is the same bound for any supplied contexts, from any set with amounts in range.
In that statement a height can repeat, so it is not a statement about a chain without `ChainLinked`.

The theorem is about `connectBlock` block by block, on the Lean definitions.
It does not include the header checks or `ContextualCheckBlock`, and it does not say which chain a node selects.
`ChainLinked` does not require that `hashPrevBlock` of a header is the hash of the block before, because `connectBlock` does not read that field.
The fields `bip34Ancestor` and `csvActive` of each context are free.

`lake test` pins `CoinSet.totalValue` and `chainSubsidy` on a chain of the genesis block and one block at height 1 ([COVERAGE.md](../../COVERAGE.md#operations)).

The comparison with Core on real blocks checks the bound by execution, not by proof.
On a replay from the genesis block, `block.validate` reports `CoinSet.totalValue` at each multiple of 1,000 and at the end.
Core's harness reports the sum of its own coin view at the same points, and the two must be equal.
Each total must also be at most the sum of the subsidies from height 1 to its height ([oracle](../oracle.md#total-value)).
The comparator computes that sum from `block.subsidy`, so it checks the statement of `chain_issuance_bound` on these blocks with `getDogecoinBlockSubsidy` in the place of `subsidyValue`.
The two are equal whenever the subsidy has fuel, and a subsidy without fuel is a request error of `block.subsidy`.

By `#print axioms`, `connect_spends_available`, `connect_valuesInRange`, `connect_value_bound`, `connectChain_issuance_bound` and `chain_issuance_bound` depend on `propext`, `Classical.choice` and `Quot.sound`.

## `validateBlock_restrict`: a block on the coins that it names

`validateBlock_restrict` (in `DogeLib.Block.Proofs.Restrict`) is the theorem target of design record 0011, section 3.3 and decision 2.
A block *names* a transaction ID when the ID is the ID of one of its transactions, or the ID in the outpoint of one of its inputs.
`validateBlock` reads and changes the coin set only at the IDs that the block names.

A coin set stores the entry of an ID under `txidKey` of the ID, and `txidKey_inj` shows that different IDs have different keys.
The theorem is about keys.
Let `keep` be a predicate on keys that holds for the key of every ID that the block names (`NamesWithin`).
`s.restrict keep` has the entries of the set `s` whose key satisfies `keep`.
Then `validateBlock` returns the same error on `s` and on `s.restrict keep`, or it accepts the block on both.
When it accepts, four statements hold:

1. The two results have the same coin changes.
2. The two new sets have equal entries at every key that satisfies `keep`.
3. The new set of the restriction has no entry at any other key.
4. The new set of `s` has the entries of `s` at every other key.

So the restricted run and the old set together determine the new set of `s`.

The theorem holds for every verifier, both flags, every context and every coin set.
The design record expected a hypothesis that each entry is under the key of its own ID.
The theorem needs no such hypothesis: the restriction selects an entry by its key, and `validateBlock` reads no `TxCoins.txid` field of an entry.
An equal error includes the results outside the model, such as `outOfDomain`.

`validateBlock_agree` is the general form of statements 1 and 2, for any two sets with equal entries at the keys of `keep`.
Its conclusion repeats its hypothesis on the sets, so it applies again to the next block when `keep` also holds the keys of that block.
`validateBlock_frame` is statement 4 for any accepted block and any key that the block does not name.

The theorems do not cover these parts of a `block.validate` request with `coins_file` ([oracle](../oracle.md#coin-set-snapshots)):

- **A list of blocks.** No theorem here is about a range. The oracle keeps the coins of the IDs that all blocks of the request name. Before each block, it checks that the kept IDs hold the names of that block. An induction over `validateBlock_agree` and `validateBlock_frame` would state the claim for the range, and it is not written.
- **The adapter.** `validateStep` also carries the chain view, and no theorem relates its two runs.
- **The files.** The reads of the snapshot, the choice of the kept coins and the merge that gives the last digest are `IO` code ([B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)). The comparison of the two forms of the request is their evidence.
- **Core.** The theorems are about the Lean definitions. The harness loads the whole snapshot.

The proofs use `validateBlockAt`, which is `validateBlock` with the hash of the genesis block as a parameter.
`validateBlock_eq_at` shows that `validateBlock` is that function at the hash of mainnet, by reflexivity.
The definition exists because the kernel otherwise evaluates the hash from its hexadecimal string when a proof unfolds `validateBlock`, which takes minutes.

By `#print axioms`, `validateBlock_restrict`, `validateBlock_agree` and `validateBlock_frame` depend on `propext`, `Classical.choice` and `Quot.sound`.
