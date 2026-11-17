# Model read: the coin set, CheckTxInputs and ConnectBlock

- Reader: OpenAI Codex (GPT-5), an independent model reviewer, not a human
- Date: 2026-11-17
- DogeLib: 8748567. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `Coins.lean`, `TxInputs.lean`, `SigOpCost.lean`, `Connect.lean`, `Validate.lean`, `Script/Error.lean`, validation oracle glue and Core harness, with the listed dependencies

## Result

I found no consensus-verdict discrepancy inside the stated supported domain. I found three domain-boundary or state-model discrepancies and one incorrect documentation claim. Confidence is high from line-by-line source inspection.

## Findings

1. **Failed `connectBlock` calls do not expose Core’s partially changed coin view.**  
   Lean: [Connect.lean:302](../../DogeLib/Block/Connect.lean#L302), [Connect.lean:341](../../DogeLib/Block/Connect.lean#L341). Core: [validation.cpp:1936](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1936), [validation.cpp:1988](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1988). Core keeps every earlier `UpdateCoins` mutation when a later transaction or reward check fails. Lean returns only an error, so the caller retains the original immutable `CoinSet`. Concrete input: a valid coinbase followed by a transaction with a missing input. Core returns `bad-txns-inputs-missingorspent` with the coinbase already added to `view`; Lean returns the same rejection without a changed set. The harness correctly neutralizes this difference by discarding its per-candidate cache. **Severity:** domain-boundary. **Confidence:** high.

2. **A corrupt-block failure inside standalone `ConnectBlock` changes Core’s state to an error.**  
   Lean: [Connect.lean:343](../../DogeLib/Block/Connect.lean#L343). Core: [validation.cpp:1804](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1804), [validation.cpp:1589](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1589). With `fJustCheck = false`, a bad Merkle root makes `CheckBlock` set `CorruptionPossible`; Core then calls `AbortNode`, starts shutdown and changes `CValidationState` to `MODE_ERROR`. Lean reports an ordinary `.checkBlock .merkleRoot` rejection. This path cannot occur in `blockValidate`, where the earlier `CheckBlock` catches the fault and `ConnectBlock` uses `fJustCheck = true`. **Severity:** domain-boundary. **Confidence:** high.

3. **The Lean oracle rejects one candidate height that the Core harness accepts.**  
   Lean: [Oracle.lean:328](../../DogeLib/Block/Exports/Oracle.lean#L328), [Oracle.lean:338](../../DogeLib/Block/Exports/Oracle.lean#L338). Harness: [core_block_validate.inc:156](../../harness/core/core_block_validate.inc#L156), [core_block_validate.inc:264](../../harness/core/core_block_validate.inc#L264). A predecessor height of `2147483646` gives candidate height `2147483647`, which is still representable by Core’s signed `int`. The Lean adapter rejects predecessors at `2147483646` or above; the harness permits `2147483646` and calls Core at `INT_MAX`. A contiguous request with sufficient history and that tip settles the difference. **Severity:** domain-boundary. **Confidence:** high.

4. **The oracle documentation incorrectly says the `BIP34Hash` equality never occurs on mainnet.**  
   Documentation: [docs/oracle.md:711](../../docs/oracle.md#L711). Core: [chainparams.cpp:84](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L84), [validation.cpp:1877](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1877). Core configures `BIP34Hash` as the canonical mainnet hash at `BIP34Height`; above that ancestor, the equality is precisely the canonical-chain fast path that disables BIP30. Lean’s `enforceBip30` behavior itself agrees. **Severity:** documentation-only. **Confidence:** high.

## Checked and agreeing

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `CCoins`, `FromTx`, availability and pruning (`coins.h:74-234`) | `TxCoins`, `ofTx`, `available`, `isPruned` (`Coins.lean:90-117`) | Cleanup, trailing nulls and omitted pruned entries are observationally equivalent for validation reads. |
| Cache reads and replacement (`coins.cpp:72-170,265-296`) | `accessCoins`, `coin`, `haveUnspent`, `addTx` (`Coins.lean:130-167`) | Includes fully spent entries and coinbase replacement. |
| `IsUnspendable` (`script.h:635-638`) | `isUnspendable` (`Coins.lean:64-75`) | First byte `OP_RETURN`, or size greater than 10,000. |
| `UpdateCoins` (`validation.cpp:1366-1396`) | `spendInputs`, `addTx`, `createdCoins` (`Connect.lean:293-321`) | Input order, then new entry; only non-null outputs enter the set. |
| `CheckTxInputs` (`validation.cpp:1415-1460`) | `checkInputValues`, `checkTxInputs` (`TxInputs.lean:114-140`) | Maturity, arithmetic order, `MoneyRange`, reasons, scores and codes agree. |
| `CheckInputs` (`validation.cpp:1462-1518`) | `checkInputScript(s)`, `checkInputs` (`Connect.lean:242-280`) | Cheap checks precede scripts; first-run error text is retained during reclassification. |
| Standard and mandatory flags (`policy.h:88-105`, `standard.h:43`, `interpreter.h:30-108`) | `standardNotMandatoryVerifyFlags` (`Connect.lean:97-105`) | Every included and excluded bit agrees. |
| `ScriptErrorString` (`script_error.cpp:8-95`) | `ScriptError.description` (`Error.lean:168-211`) | All texts agree. `UNKNOWN_ERROR` and unhandled `CLEANSTACK` use `unknown error`; the count sentinel is not a Lean error. |
| Script sigop counts (`script.cpp:156-211`) | `getSigOpCountAccurate`, `p2shSigOpCount` (`SigOpCost.lean:61-108`) | `lastOpcode`, failed reads, `DecodeOP_N` and last pushed data agree. |
| Transaction sigop cost (`validation.cpp:489-521`) | `getP2SHSigOpCount`, `getTransactionSigOpCost` (`SigOpCost.lean:110-129`) | Unsigned 32-bit products and wraparound agree; witness term is zero. |
| Sequence locks with flags zero (`validation.cpp:309-384`) | Connect module restriction (`Connect.lean:60-67`) | Returns `(-1,-1)` and cannot fail against nonnegative height and median time. |
| Mainnet activation constants (`chainparams.cpp:84-131`) | `coinbaseMaturity`, activation heights and BIP34 hash | Heights, maturity selection and internal hash order agree. |
| `ConnectBlock` through `fJustCheck` (`validation.cpp:1783-2009`) | `connectBlock` (`Connect.lean:341-361`) | Check order, flags, genesis, BIP30, transaction loop, fees, scripts, sigops and reward agree on success and verdicts. |
| `AcceptBlockHeader`, `AcceptBlock`, `TestBlockValidity` (`validation.cpp:3205-3433`) | `validateBlock` (`Validate.lean:119-138`) | Five-check order and genesis behavior agree; omitted index, storage and chain-selection work is documented. |
| Coin request conversion | `coinEntry`, `argCoins` (`Exports/Validate.lean:62-99`) | Same fields, bounds, null gaps, duplicate checks and spendability test. |
| Accepted-block state | `core_block_validate.inc:289-388` | The same block index facts and semantic coin entries carry forward. Rejected candidate caches are discarded. |
| Digest record and chaining | `core_block_validate.inc:55-80` | `coinRecord`, `changesDigest`, `setDigest` (`Exports/Validate.lean:35-56`) | Same bytes, SHA256d chaining and ordering. |
| Documented `CoinSet` omissions | `Coins.lean:37-50` | Reason holds. |
| Caller-supplied coins/no `HaveInputs` in `checkTxInputs` | `TxInputs.lean:13-16` | Reason holds. |
| Integer `outOfDomain` results | `TxInputs.lean:18-27`, `Connect.lean:49-58` | Reason and evaluation order hold. |
| Mainnet/no threads/null assume-valid/CSV restriction/`newCoinsExist` | `Connect.lean:43-58` | Reasons hold. |
| Five-check composition, not `AcceptBlock` | `Validate.lean:23-33` | Reason holds. |
| Harness cache, commit and shadow-cache choices | `docs/oracle.md:979-1001` | Reasons hold, apart from finding 3’s height boundary. |

## Not checked

- `Proofs/`, as excluded by scope.
- Core work after the `fJustCheck` return boundary, including undo, disk and transaction-index writes.
- The internal cryptographic correctness of `coreVerifier`; only its use and supplied transaction context were compared.
- No build, test, executable, generator or dynamic experiment was run, as requested.

## After the read

This section is an addendum, not part of the read. The line numbers in the findings refer to DogeLib `8748567`.

- Finding 1 (the view after a failure). The module documentation of `DogeLib.Block.Connect` has the section *What a failure leaves out*, which states that `connectBlock` returns no changed set with an error, and that a caller of Core must discard the view.
- Finding 2 (`AbortNode`). The same section states that `connectBlock` does not model `AbortNode` for `fJustCheck` false, and why `validateBlock` cannot reach it.
- Finding 3 (the greatest height). The harness refuses a chain entry at height 2147483646, as the oracle's adapter does. Both programs then return a request error for that predecessor.
- Finding 4 (`BIP34Hash`) is not correct, and the document is unchanged. `BIP34Hash` is `80d13642…1e797a`, the hash of block 1,032,483 ([fixture](../../tests/block/mainnet-bip66-headers/README.md)). The block at `BIP34Height`, 1,034,383, has the hash `251f53c3…39f7f6` in the committed rule-change fixture. So the ancestor at `BIP34Height` never has the hash `BIP34Hash` on mainnet, as design record 0010, section 2, says.

No finding is consensus-divergent.
