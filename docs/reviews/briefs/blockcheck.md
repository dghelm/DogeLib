# Brief of the block check read

This text is the prompt that produced [the record](../blockcheck.md).
It is exact, except that three placeholders replace the DogeLib revision and the local paths.

````markdown
# Model read: Block codec, CheckTransaction and CheckBlock against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides. Do not edit any file, and do not build or run anything.

- DogeLib (read-only): <DogeLib clone> at commit <DogeLib revision>
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

**Lean**, definitions outside `Proofs/` and `Exports/`: DogeLib/Transaction/Check.lean, DogeLib/Transaction/SigOps.lean, DogeLib/Block/Block.lean, DogeLib/Block/Check.lean. They use `readOp` and `scanOps` of DogeLib/Transaction/LegacySighash.lean, `readTx`, `encodeTx`, `BlockHeader.read` and `BlockHeader.encode` of DogeLib/Block/AuxPow.lean, `blockMerkleRoot` of DogeLib/Block/Merkle.lean, and `checkBlockHeader` of DogeLib/Block/ProofOfWork.lean. Read those as far as the four modules depend on them.

**Core**: src/validation.cpp (GetLegacySigOpCount, lines 475 to 487; CheckTransaction, 527 to 574; CheckBlockHeader, 2927 to 2937; CheckBlock, 2939 to 3000); src/script/script.cpp (CScript::GetSigOpCount(bool), 156 to 177); src/script/script.h (GetOp, GetOp2, MAX_PUBKEYS_PER_MULTISIG, the opcode values); src/primitives/block.h (CBlock, its SerializationOp and fChecked); src/primitives/transaction.h (COutPoint::IsNull and operator<, CTransaction::IsCoinBase, WITNESS_SCALE_FACTOR, the serialization functions); src/serialize.h (the vector reader Unserialize_impl, the shared_ptr reader, ReadCompactSize, GetSerializeSize); src/consensus/consensus.h; src/amount.h; src/consensus/validation.h (CValidationState: DoS, Invalid, the reject code and CorruptionPossible); src/consensus/merkle.cpp (BlockMerkleRoot)

Each Lean module's doc comments state its declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core. Documented choices: `checkBlock` is the function for a block with `fChecked` false. The sigop counts are natural numbers and `checkBlock` reduces the product modulo 2^32. `checkOutputs` adds in the integers. Only `GetSigOpCount(false)` is defined. Say for each of them whether the stated reason holds.

## Method

For each Core function, find the Lean counterpart and compare:
- the order of the checks, and which failure comes first when two apply;
- the reject reason, the DoS score, the reject code and the corruption flag of every failure, including the `state.Invalid` call of line 2985;
- the C++ types of every intermediate value (`CAmount`, `unsigned int`, `size_t`, `int64_t`, `int`), their conversions, and the usual arithmetic conversions in each comparison, including `nSigOps * WITNESS_SCALE_FACTOR > MAX_BLOCK_SIGOPS_COST`;
- bounds and off-by-one cases: both size limits, the transaction count limit, the coinbase script length, `MAX_MONEY`;
- whether the running output sum can overflow `int64_t` or go negative;
- the duplicate-input test against `std::set<COutPoint>` and `operator<`;
- `IsCoinBase` and `IsNull`;
- which serialization each size test measures, including the transaction of an AuxPoW payload under `SERIALIZE_TRANSACTION_NO_WITNESS`;
- the block reader: the order of the fields, the count bound, the element loop, the read mode of each transaction, and what the reader returns for a count above `MAX_SIZE`;
- the sigop loop: which opcodes count, what a failed `GetOp` does to the count, push data, and the last-opcode logic that `fAccurate` false skips;
- whether any statement of `CheckTransaction` or `CheckBlock` reads witness data.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it. The project's differential comparison (`scripts/compare_core.py`, operations `tx.check` and `block.check`) can test it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: Block codec, CheckTransaction and CheckBlock

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: <DogeLib revision>. Core: e0a1c157791544e818c901bd9341896965afbf9d
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
