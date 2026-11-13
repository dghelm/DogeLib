# Brief of the version bits and ContextualCheckBlock read

This text is the prompt that produced [the record](../contextualbody.md).
It is exact, except that the DogeLib and Core clone paths are those of the maintainer's machine.

````markdown
# Model read: version bits and ContextualCheckBlock against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides. Do not edit any file, and do not build or run anything.

- DogeLib (read-only): /home/dgh/dev/DogeOS69/DogeLib-worktrees/feat-contextual-check (the current worktree)
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): /home/dgh/dev/DogeOS69/DogeLib-worktrees/core-pin

## Scope

**Lean**, definitions outside `Proofs/` and `Exports/`: DogeLib/Block/VersionBits.lean and DogeLib/Block/ContextualBody.lean. They use `Script.ScriptNum.encode` of DogeLib/Script/Number.lean, `Block.encode`/`baseSize` of DogeLib/Block/Block.lean, `encodeTx`/`BlockHeader.encode` of DogeLib/Block/AuxPow.lean, `WitnessTransaction.encode`/`hasWitness` of DogeLib/Transaction/Witness.lean, and the transaction fields of DogeLib/Transaction/Types.lean. Read those as far as the two modules depend on them.

Also read the oracle glue, in DogeLib/Block/Exports/Oracle.lean: `bodyStates`, `contextualCheckBody`, `versionBitsStateOp`. Confirm that the candidate height, the version-bits states and the lock-time cutoff passed to `contextualCheckBlockBody` match what Core computes from a predecessor.

**Core**: src/validation.cpp (`IsFinalTx`, lines 258 to 269; `ContextualCheckBlock`, lines 3121 to 3203); src/versionbits.cpp (`AbstractThresholdConditionChecker::GetStateFor`, lines 24 to 106; `VersionBitsConditionChecker::Condition`, lines 153 to 156); src/versionbits.h (`VERSIONBITS_TOP_BITS`, `VERSIONBITS_TOP_MASK`); src/chainparams.cpp (the mainnet `DEPLOYMENT_CSV` and `DEPLOYMENT_SEGWIT` parameters, `nMinerConfirmationWindow`, `nRuleChangeActivationThreshold`, `BIP34Height`, lines 79 to 123); src/primitives/block.cpp (`GetBlockWeight`, lines 43 to 49); src/consensus/consensus.h (`MAX_BLOCK_WEIGHT`, `WITNESS_SCALE_FACTOR`); src/script/script.h (`CScript::push_int64`, `CScriptNum::serialize`, `LOCKTIME_THRESHOLD`); src/primitives/transaction.h (`SEQUENCE_FINAL`, `HasWitness`); src/chain.h (`GetMedianTimePast`, `GetAncestor`).

Each Lean module's doc comments state its declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core. Documented choices: `contextualCheckBlockBody` is mainnet only and reads the CSV and SegWit states only through whether they are `ACTIVE`; it treats an active SegWit state and a block with no coinbase input as adapter errors. `thresholdStep` folds Core's backward-walk reset into one step. The weight uses three times the base size plus the full size. Say for each of them whether the stated reason holds.

## Method

For each Core function, find the Lean counterpart and compare:
- `IsFinalTx`: the lock-time-of-zero case, the `LOCKTIME_THRESHOLD` branch that selects the height or the time, the `< cutoff` comparison with `int64_t` widening, and the all-inputs-final loop with `SEQUENCE_FINAL`.
- `ContextualCheckBlock`: the order of the checks; the lock-time cutoff from the CSV state; the finality loop and `bad-txns-nonfinal` with DoS 10; the BIP34 coinbase-height prefix `CScript() << nHeight` and `bad-cb-height` with DoS 100; the SegWit witness-commitment branch and the two reasons behind it; the `unexpected-witness` scan over `block.vtx` and DoS 100; the `GetBlockWeight(block) > MAX_BLOCK_WEIGHT` check and `bad-blk-weight` with DoS 100. Check the reject code 16 for each.
- `GetStateFor`: the alignment to a period boundary; the backward walk and its two base cases (null, and median below the start time); the forward switch for `DEFINED`, `STARTED`, `LOCKED_IN`, `ACTIVE` and `FAILED`; the signal count against the threshold. Check that `thresholdStep` reproduces each transition, that the reset to `DEFINED` matches Core's break, and that the fold over all boundaries from genesis gives `GetStateFor` at the last boundary.
- `Condition`: the top-three-bits test against `VERSIONBITS_TOP_BITS`/`VERSIONBITS_TOP_MASK` and the deployment bit.
- `GetBlockWeight`: the base and full serialization sizes, and that `Block.fullSize`/`Block.baseSize` measure the right modes.
- the coinbase-height prefix: `push_int64` for a height above 16, `CScriptNum::serialize`, and the push length byte; whether `coinbaseHeightPrefix` matches for every mainnet BIP34 height.
- the mainnet deployment parameters: the CSV and SegWit bit, start time and timeout; the window 10,080 and the threshold 9,576.

Pay special attention to:
- the C++ types and conversions in every comparison (`int`, `int64_t`, `uint32_t`, `size_t`), and whether the Lean `Int`/`Nat` widths match;
- whether the lock-time cutoff, the candidate height and the version-bits states that the oracle passes are what Core derives from the same predecessor and chain;
- any input where `contextualCheckBlockBody` and Core would return different verdicts.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: version bits and ContextualCheckBlock

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: cc15d98 (plus the uncommitted changes of this worktree). Core: e0a1c157791544e818c901bd9341896965afbf9d
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
