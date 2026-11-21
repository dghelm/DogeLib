# Brief of the sequence locks read

This text is the prompt that produced [the record](../sequencelocks.md).
It is exact, except that placeholders replace the DogeLib and Core clone paths of the maintainer's machine.

````markdown
# Model read: the sequence locks of BIP 68 against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides. Do not edit any file, and do not build or run anything.

- DogeLib (read-only): <DogeLib clone> (the current worktree)
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

**Lean**, definitions outside `Proofs/`: DogeLib/Proposals/RelativeLockTime/SequenceLocks.lean (`inputLock`, `ancestorMedianTimePast`, `calculateSequenceLocks`, `evaluateSequenceLocks`, `sequenceLocksWith`, `sequenceLocks`, `RevisionError`, `Reason`), and in DogeLib/Proposals/RelativeLockTime.lean the definitions `txTest`, `blockRevision`, `connectEmbedding` and `validateEmbedding`. They use `Work.medianTimePast` of DogeLib/Work/MedianTimePast.lean, `validateWorkView` of DogeLib/Work/NextWork.lean, the sequence constants of DogeLib/Script/Signature.lean, `Coin` of DogeLib/Block/Coins.lean, and the place of the transaction test in `connectTransactionWith` and `connectBlockWith` of DogeLib/Proposals/Framework/Block.lean. Read those as far as the definitions depend on them.

Also read the glue of the proposal executable, in DogeLib/Proposals/Exports/Validate.lean: `relativeLockTimeRevision`, `relativeLockTimeFields` and `describeRelativeLockTimeReason`. Confirm that the view that the test reads is the view of the predecessor of the block, and that the reject reason, the DoS score and the reject code of a failed sequence lock are Core's.

**Core**: src/validation.cpp (`CalculateSequenceLocks`, `EvaluateSequenceLocks` and `SequenceLocks`, lines 309 to 384; `ConnectBlock`, lines 1906 to 1911 for `nLockTimeFlags` and lines 1935 to 1970 for the place of the test in the transaction loop, with its reject reason); src/chain.h (`GetMedianTimePast`, lines 284 to 298; `GetBlockTime`); src/chain.cpp (`GetAncestor`, lines 113 to 147); src/primitives/transaction.h (the sequence constants, lines 76 to 99; `nVersion`); src/consensus/consensus.h (`LOCKTIME_VERIFY_SEQUENCE`); src/coins.h (`CCoins::nHeight`, and the height that `ConnectBlock` gives the coins of a transaction of the same block through `UpdateCoins`).

The revision states a rule that Core's code holds and that never runs on mainnet: `ConnectBlock` passes `LOCKTIME_VERIFY_SEQUENCE` only when the version-bits state of CSV is `ACTIVE`. Compare the Lean definitions with what Core's code does in that state. The Lean argument `active` stands for that state.

The module documentation states the declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core. Documented choices: unbounded integers in the place of `int` and `int64_t`; the result `heightOutOfDomain` for a coin height of at least `2^31 - 65535` on an input with bit 31 clear; the result `coinAboveBlock` for a time lock on a coin above the block; the result `ancestorOutsideView` when the view is short, starts at another height or has no median; acceptance on an empty view; the first reason in input order, also when an earlier input has a lock that is not met; no write of 0 into `prevHeights`. Say for each of them whether the stated reason holds.

## Method

For each Core function, find the Lean counterpart and compare:
- `CalculateSequenceLocks`: the start (-1, -1); `fEnforceBIP68` with the unsigned version comparison and the flag; the test of `SEQUENCE_LOCKTIME_DISABLE_FLAG`; the test of `SEQUENCE_LOCKTIME_TYPE_FLAG`; the mask `SEQUENCE_LOCKTIME_MASK`; the shift by `SEQUENCE_LOCKTIME_GRANULARITY`; both subtractions of 1; both maxima; the ancestor height `std::max(nCoinHeight-1, 0)` and the block index that `GetAncestor` is called on.
- `EvaluateSequenceLocks`: which block index gives `nHeight` and which gives `GetMedianTimePast`, and both `>=` comparisons.
- The ancestor read: that the entry at depth `height - 1 - (c - 1)` of the view of the predecessor, with natural subtraction, is the ancestor at height `max(c - 1, 0)` of the block for every coin height `c` from 0 to `height`, and that `medianTimePast` of the view from that entry is that ancestor's `GetMedianTimePast`.
- `ConnectBlock`: that the test runs for each transaction that is not a coinbase, after the lookup of the inputs and before the count of signature operations; the height `prevheights[j]` for a coin of an earlier block and for a coin that the same block created; the reject reason `bad-txns-nonfinal`, DoS 100 and the reject code.
- The C++ types and conversions in every sum and comparison (`int`, `int64_t`, `uint32_t`, `size_t`), and whether a result of the Lean definition that is not outside the model can differ from Core because of a wrap or a conversion.

Pay special attention to any input inside the declared domain on which `sequenceLocks` and Core's `SequenceLocks` would give different verdicts. Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: the sequence locks of BIP 68

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-20
- DogeLib: 58a30eb. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: <files>

## Result
<two or three sentences: discrepancies found, yes or no; overall confidence>

## Findings
<one entry per discrepancy or suspected discrepancy: Lean file:line, Core file:line, what differs, a concrete input if known, severity (consensus-divergent / domain-boundary / documentation-only), confidence>

## Checked and agreeing
| Core construct (file:lines) | Lean definition (file:line) | Notes |
<one row per function or step you actually compared>

## Not checked
<anything in scope you did not compare, and why>
```

Be terse. Don't pad the agreeing table with prose.
````
