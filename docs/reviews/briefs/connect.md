# Brief of the coin set, CheckTxInputs and ConnectBlock read

This text is the prompt that produced [the record](../connect.md).
It is exact, except that placeholders replace the DogeLib and Core clone paths and the DogeLib revision.

````markdown
# Model read: the coin set, CheckTxInputs and ConnectBlock against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides. Do not edit any file, and do not build or run anything.

- DogeLib (read-only): <DogeLib clone> (the current worktree)
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

**Lean**, definitions outside `Proofs/`: DogeLib/Block/Coins.lean, DogeLib/Block/TxInputs.lean, DogeLib/Block/SigOpCost.lean, DogeLib/Block/Connect.lean and DogeLib/Block/Validate.lean, and `ScriptError.description` in DogeLib/Script/Error.lean. They use `checkBlock` of DogeLib/Block/Check.lean, `contextualCheckBlockBody` of DogeLib/Block/ContextualBody.lean, `contextualCheckBlockHeader` of DogeLib/Block/ContextualCheck.lean, `checkBlockHeader` of DogeLib/Block/ProofOfWork.lean, `getDogecoinBlockSubsidy` of DogeLib/Block/Subsidy.lean, `verifyLegacySpend`, `isPayToScriptHash` and `readInstruction` of DogeLib/Script, `scanOps` of DogeLib/Transaction/LegacySighash.lean and `Transaction.txid`. Read those as far as the five modules depend on them. Earlier reads cover their own bodies.

Also read the oracle glue in DogeLib/Block/Exports/Validate.lean (`blockValidate`, `argCoins`, `coinEntry`, `coinRecord`, `changesDigest`, `setDigest`) and the harness in harness/core/core_block_validate.inc, with the definition of the digests in docs/oracle.md, section "Block validation". Confirm that the two programs give `validateBlock` and Core's functions the same inputs for the same request, that the state each carries from an accepted block is the same, and that the two compute each digest from the same bytes in the same order.

**Core**: src/validation.cpp (`GetP2SHSigOpCount` and `GetTransactionSigOpCost`, lines 489 to 521; `CalculateSequenceLocks`, `EvaluateSequenceLocks` and `SequenceLocks`, lines 309 to 384; `UpdateCoins`, lines 1366 to 1396; `CScriptCheck::operator()` and `GetSpendHeight`, lines 1398 to 1412; `Consensus::CheckTxInputs`, lines 1415 to 1460; `CheckInputs`, lines 1462 to 1518; `ConnectBlock`, lines 1783 to 2040; `AcceptBlockHeader`, lines 3205 to 3267; `AcceptBlock`, lines 3288 to 3366; `TestBlockValidity`, lines 3412 to 3433); src/coins.h (`CCoins`, lines 74 to 243; `CCoinsViewCache`); src/coins.cpp (`CCoins::Spend`, `FetchCoins`, `ModifyCoins`, `ModifyNewCoins`, `AccessCoins`, `GetOutputFor`, `GetValueIn`, `HaveInputs`); src/script/script.h (`IsUnspendable`, `MAX_SCRIPT_SIZE`, `DecodeOP_N`, the opcode values); src/script/script.cpp (`CScript::GetSigOpCount`, both overloads, lines 156 to 201; `IsPayToScriptHash`); src/script/script_error.cpp (`ScriptErrorString`); src/policy/policy.h (`STANDARD_SCRIPT_VERIFY_FLAGS`, `STANDARD_NOT_MANDATORY_VERIFY_FLAGS`) and src/script/standard.h (`MANDATORY_SCRIPT_VERIFY_FLAGS`); src/script/interpreter.cpp (`CountWitnessSigOps`, and how `VerifyScript` uses the witness without `SCRIPT_VERIFY_WITNESS`); src/primitives/transaction.h and transaction.cpp (`CTxOut::SetNull` and `IsNull`, `GetValueOut`); src/chainparams.cpp (the mainnet `nCoinbaseMaturity`, `BIP34Height`, `BIP34Hash`, `BIP65Height`, `BIP66Height`, the genesis hash); src/amount.h (`MAX_MONEY`, `MoneyRange`); src/consensus/consensus.h (`MAX_BLOCK_SIGOPS_COST`, `WITNESS_SCALE_FACTOR`); src/consensus/validation.h (`CValidationState::DoS` and `Invalid`, the reject codes); src/dogecoin.cpp (`GetDogecoinBlockSubsidy`, only its call).

Each Lean module's doc comments state its declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core. Documented choices:

- `CoinSet` has one entry for each transaction ID, with `none` for a null output. It leaves out `nVersion`, `Cleanup`, pruned entries, the cache flags and the cache layers.
- `checkTxInputs` takes the coins that the caller found, and has no `HaveInputs` test.
- The definitions compute amounts in unbounded integers, and return `outOfDomain` when a sum that Core computes in `int64_t` with no earlier range check leaves the `int64_t` range.
- `connectBlock` is mainnet only, for no script-check threads and a null `hashAssumeValid`. It has no sequence-lock test, and returns `csvActive` on an active CSV state. It returns `newCoinsExist` where `ModifyNewCoins` would throw or replace an entry for a transaction that is not a coinbase.
- `validateBlock` is the composition of five checks, with `ConnectBlock` at `fJustCheck` true, and is not `AcceptBlock`.
- The harness runs `ConnectBlock` with `fJustCheck` true on a new cache, commits it after an accepted block, and reads the changes of the block from a second cache on which it calls `UpdateCoins`.

Say for each of them whether the stated reason holds.

## Method

For each Core function, find the Lean counterpart and compare:

- `CCoins`, `FromTx`, `ClearUnspendable`, `IsAvailable`, `IsPruned`, `Spend`, and the reads `AccessCoins`, `HaveInputs` and `GetOutputFor`: whether every read of validation gives the same answer on `CoinSet` as on Core's cache, including after an entry is fully spent, after `Cleanup`, and after a coinbase replaces an entry.
- `IsUnspendable`: the `OP_RETURN` first byte and the size bound.
- `UpdateCoins`: the order of the spends and the new entry, and which outputs enter the set.
- `Consensus::CheckTxInputs`: the order of the checks for each input, the maturity selected by the height of the coin, the comparison `nSpendHeight - coins->nHeight < nCoinbaseMaturity` in `int`, the addition before the two `MoneyRange` tests, the three tests after the loop, and the score and code of each failure (`state.Invalid` against `state.DoS`).
- `CheckInputs`: that `CheckTxInputs` runs before any script, the script loop in input order, the second run without `STANDARD_NOT_MANDATORY_VERIFY_FLAGS`, which error's text the reason carries, and the score and code of the two reasons. Check each bit of `standardNotMandatoryVerifyFlags` against Core's constants.
- `ScriptErrorString`: every case, and the two enumerators that take the default.
- `CScript::GetSigOpCount(bool)` with `fAccurate` true, `GetSigOpCount(const CScript&)`, `GetP2SHSigOpCount` and `GetTransactionSigOpCost`: the role of `lastOpcode`, `DecodeOP_N`, what a failed `GetOp` and an opcode above `OP_16` give, the data of the last instruction, the `unsigned int` arithmetic and the conversion to `int64_t`, and the comparison with `MAX_BLOCK_SIGOPS_COST`.
- `ConnectBlock`: the order of every statement up to the `fJustCheck` return; the flags of its `CheckBlock` call; the genesis case; `fEnforceBIP30` and the BIP30 loop; the script flags by height; for each transaction, the `HaveInputs` test, the sigop cost and its limit, the fee added before `CheckInputs`, `CheckInputs`, and `UpdateCoins`; the block reward and `bad-cb-amount`. Check the score and code of each failure, and that a failure inside `CheckBlock` or `CheckInputs` keeps the state of that function.
- The sequence-lock argument in the module documentation of DogeLib/Block/Connect.lean: whether `SequenceLocks` can return false with `nLockTimeFlags` 0.
- `AcceptBlockHeader`, `AcceptBlock` and `ConnectBlock` against `validateBlock`: the order of the five checks, the genesis case, and what the composition leaves out.

Pay special attention to:

- the C++ types and conversions in every comparison and sum (`int`, `unsigned int`, `int64_t`, `CAmount`, `size_t`), and whether the Lean `Int` and `Nat` computations match, including where Core's arithmetic wraps;
- every place where Core adds amounts with no earlier range check, and whether the Lean definitions return `outOfDomain` for exactly the sums that leave `int64_t`, in Core's order of evaluation;
- any block and coin set, inside the documented domain, for which `connectBlock` and Core's `ConnectBlock` would return different verdicts, reasons, scores or codes, or leave different coin sets;
- any request for which the oracle and the harness would give their validation functions different inputs, carry different state, or compute a digest from different bytes.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: the coin set, CheckTxInputs and ConnectBlock

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-17
- DogeLib: <DogeLib revision>. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: <files>

## Result
<two or three sentences: discrepancies found, yes or no; overall confidence>

## Findings
<one entry per discrepancy or suspected discrepancy: Lean file:line, Core file:line, what differs, a concrete input if known, severity (consensus-divergent / domain-boundary / documentation-only), confidence>

## Checked and agreeing
<a table: Core construct (file:lines) | Lean definition (file:line) | Notes>

## Not checked
<what you did not compare, and why>
```
Be terse. Don't pad the agreeing table with prose.
````
