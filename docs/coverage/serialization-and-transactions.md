# Coverage: Serialization and Transactions

This file holds the per-operation coverage detail for `Base`, `Serialization`, `Transaction`, and the Rust CompactSize refinement.
See [COVERAGE.md](../../COVERAGE.md#operations) for the compact matrix and [COVERAGE.md](../../COVERAGE.md#legend) for field meanings and theorem tags.
See [docs/soundness/serialization.md](../soundness/serialization.md), [docs/soundness/transactions.md](../soundness/transactions.md), and [docs/soundness/blocks.md](../soundness/blocks.md#block-codec-checktransaction-and-checkblock) for theorem hypotheses and boundaries.
See [docs/comparison-evidence.md](../comparison-evidence.md) for finite Core comparison counts and streams.

## Byte slice reads

- **Definition**: `ByteSlice.toList`, `ByteSlice.take`, `ByteSlice.drop`, `ByteSlice.uncons` in `Base.ByteSlice`
- **Theorems**: `toList_take`, `toList_drop`, `toList_of_uncons_some`, `toList_of_uncons_none`: each read agrees with the list operation on `toList`, for every slice
- **Comparison**: None
- **Refinement**: None
- **Excluded**: None

## Codec composition

- **Definition**: `Serialization.instCodecProd`, `Serialization.Codec.ofEquiv`
- **Theorems**: `instLawfulCodecProd`: the pair of two lawful codecs is lawful. `LawfulCodec.ofEquiv`: transport is lawful if the two functions are inverse to each other (a hypothesis). `encode_injective` for every lawful codec
- **Comparison**: None
- **Refinement**: None
- **Excluded**: None

## CompactSize, Core's bounded reader

- **Definition**: `Serialization.CompactSize.decodeBounded`, `maxSize`, `ReadError`, and the packed form `decodeBoundedSlice`
- **Theorems**: For every input: `decodeBounded_eq_ok_iff_valid`, it accepts exactly the inputs of the separate relation `ValidCompactSizePrefix`, with its value and exact remainder. `decodeBounded_eq_ok_iff_decode`: it accepts exactly what `CompactSize.decode` accepts with a value up to `0x02000000`. `decodeBounded_eq_error_tooLarge_iff`: it reports `tooLarge` exactly when `decode` accepts a larger value. `decodeBounded_encode`: round trip for every value up to `0x02000000`. `decodeBounded_maxSize_succ`: it rejects `fe 01 00 00 02`
- **Comparison**: `lake test`: Core's `compactsize` sweep and `noncanonical` cases (D20, lines 231 to 291), truncation, and values above `MAX_SIZE`, through the compiled code. Expected results from Core's assertions and a reading of D1 and D21. `lake test` does not run Core. The same bounded cases through `decodeBoundedSlice` at offset 3 of a buffer. See `tests/KnownAnswers/Serialization.lean`. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). It runs `ReadCompactSize` on every prefix of the encodings at each boundary of the forms and of `MAX_SIZE`. It also reads each encoding followed by two bytes, and the counts inside every transaction of the comparison. All agree. `scripts/compare_core.py --rust-compactsize PATH`: compiled Rust agrees with Core and the oracle on 404 reader requests (seven fixtures and 397 generated cases). Errors, values, consumed counts and remainders agree. The Rust crate has no encoder.
- **Refinement**: `abstractRead_decodeBoundedSlice`: the packed form `decodeBoundedSlice` gives the same error, or the same value and remainder bytes, as `decodeBounded` on every slice. `Refinement.Rust.CompactSize.decode_refines`: the Aeneas model of the Rust reader agrees with `decodeBounded` on every Rust-representable slice, including every error, value and remainder. `consumed_bounds`: a successful count fits the input and is 1, 3, 5 or 9. Rust integration tests run the same 20 bounded cases and 52-value sweep
- **Excluded**: No separate characterization of `truncated` or `nonCanonical`. The Rust refinement preserves both errors relative to `decodeBounded`. Rust slice lengths fit `usize`. Extraction and runtime remain trusted. Truncation models `CDataStream` (D21). Other stream classes are not compared.

## CompactSize, generic canonical codec

- **Definition**: `Serialization.CompactSize.encode`, `CompactSize.decode`, `CompactSize.codec`
- **Theorems**: `lawfulCodec` (`decode_encode`, `decode_canonical`): round trip and canonicality on every `UInt64`, every input and every remainder. `decode_eq_some_iff`: `decode` accepts exactly the inputs of the separate relation `CanonicalCompactSizePrefix`. `encode_length_le`: at most 9 bytes. `encode_head`: only 0 starts with `0x00`
- **Comparison**: `lake test`: the encoder bytes at the boundaries of the forms, derived from `WriteCompactSize` (D1). The decoder on canonical encodings above `MAX_SIZE`. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). The encoder agrees with `WriteCompactSize` at 21 boundary values.
- **Refinement**: None
- **Excluded**: Not Core's reader: it accepts values above `MAX_SIZE`. Not a registered `Codec UInt64` instance.

## Counted lists, Core's bounded reader

- **Definition**: `Serialization.CountedList.decodeBounded`, `decodeBoundedBytes`, `readElemsBounded`, `readElemsBoundedLoop`, `readByte`, `readBytes`, `decodeBoundedSlice`, `decodeBoundedBytesSlice`, `readBytesSlice`, `readElemsBoundedSliceLoop`
- **Theorems**: `readElemsBoundedLoop_nil`: the loop form that `decodeBounded` runs returns what `readElemsBounded` returns, for every element reader and input. For every element reader that accepts exactly what a codec accepts: `decodeBounded_eq_ok_iff`, it accepts exactly what the generic `CountedList.decode` accepts with at most `0x02000000` elements. `decodeBounded_encode`: round trip for lawful element codecs and lists of at most `0x02000000` elements. For every element reader: `decodeBounded_of_count_error`, an error of the count is the error of the list. `decodeBoundedBytes_eq`: the block read of bytes is `decodeBounded readByte`. `readBytes_eq_ite`: `readBytes`, which tests the length of the first `n` bytes, is the read with the test `n ≤ bs.length`. `decodeBoundedBytes_maxSize_succ`: the count `fe 01 00 00 02` is `tooLarge`
- **Comparison**: `lake test`, through the compiled code: the two scripts of the genesis coinbase and an empty list. Also a `UInt16` list, counts above and at `MAX_SIZE`, a non-canonical count, and truncation. A list of 3,000,000 bytes, whole and one byte short. Expected results from Core's bytes (D9) and a reading of D1 and D21. `lake test` does not run Core. See `tests/KnownAnswers/Serialization.lean`. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). Through `tx.read_base` and `tx.decode_base`, it reads the input, output and script counts in 60,780 requests on count and fixed-field variants. Another 100,828 requests read transaction prefixes. All agree.
- **Refinement**: `abstractRead_decodeBoundedSlice`, `abstractRead_decodeBoundedBytesSlice`, `abstractRead_readBytesSlice`, `abstractRead_readElemsBoundedSliceLoop`: preserve complete list-reader results, including errors and remainder bytes. Element loops assume complete-result agreement of element readers, for every count and accumulator.
- **Excluded**: No theorem says which error an element failure gives: it is the error of the element reader. `MAX_SIZE` elements not run. Stack use is observed, not proved: the list loop read 16,000,000 elements in one manual run of the `lake test` driver, where the recursive form overflowed. No large-count stack observation covers the slice loop.

## Counted lists, generic codec

- **Definition**: `Serialization.CountedList`, `CountedList.encode`, `CountedList.decode`, `decodeElemsLoop`, `instCodecCountedList`
- **Theorems**: `decodeElemsLoop_nil`, and `readElemsLoop_nil` for the packed reader: the loop forms return what `decodeElems` and `readElems` return. For every lawful element codec: `instLawfulCodecCountedList` (`decode_encode`, `decode_canonical`), round trip and canonicality on every counted list, every input and every remainder. `decode_eq_some_iff`: it accepts exactly a canonical count followed by that many elements
- **Comparison**: `lake test`: the two scripts of the genesis coinbase and a `UInt16` list, as above. A list of 3,000,000 bytes, whole and one byte short
- **Refinement**: None
- **Excluded**: Not Core's reader: it accepts counts above `MAX_SIZE`. Stack use is observed, not proved.

## Fixed-length byte strings and `Hash256`

- **Definition**: `Bytes`, `Hash256` in `Base.Bytes`. `Serialization.decodeBytes`, `instCodecBytes`
- **Theorems**: `instLawfulCodecBytes` (`decodeBytes_encode`, `decodeBytes_canonical`): round trip and canonicality for every `n`, every value, input and remainder. `decodeBytes_eq_none_iff`: rejects exactly the inputs with fewer than `n` bytes. `decodeBytes_eq_dite`: the decoder, which tests the length of the first `n` bytes, is the read with the test `n ≤ bs.length`. `Bytes.ofListExact?_eq_some_iff`
- **Comparison**: `lake test`: the genesis merkle root from the header and the null prevout hash from the coinbase, through the compiled code. See `tests/KnownAnswers/Serialization.lean`.
- **Refinement**: None
- **Excluded**: None

## Fixed-width little-endian integers

- **Definition**: `Serialization.instCodecUInt8` to `instCodecUInt64`, `Serialization.bitVecCodecLE`
- **Theorems**: `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`: round trip and canonicality on every value, every input and every remainder
- **Comparison**: `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers/Serialization.lean`.
- **Refinement**: None
- **Excluded**: None

## Hash display order

- **Definition**: `Hash256.displayBytes`, `Hash256.ofDisplayBytes?` in `Base.Bytes`
- **Theorems**: `ofDisplayBytes?_displayBytes`, `displayBytes_ofDisplayBytes?`: the two conversions are inverse, for every hash and every list
- **Comparison**: `lake test`: the genesis merkle root in Core's display order (D9)
- **Refinement**: None
- **Excluded**: Hexadecimal text

## Legacy signature hash

- **Definition**: `Transaction.legacySignatureHash`, `legacySignatureHashPlan`, `LegacyHashPlan`, `legacyPreimage`, `legacyPreimageBytes` in `Transaction.LegacySighash`
- **Theorems**: `legacySignatureHashPlan_eq_fixedDigest_iff`: the plan is the fixed digest `one` exactly when `nIn` is out of range. For SINGLE, an `nIn` with no output is also out of range. `legacySignatureHashPlan_eq_hashBytes`: otherwise it hashes `legacyPreimage`. `legacyPreimage_eq`: the preimage is a body that depends on the hash type only through its three flags, then the 4 bytes of the hash type. `HashType.flags_eq_of_and`: the flags depend only on the bits `0x9f`. `LegacyHashPlan.digest_hashBytes_val`: the digest is the double SHA-256 of the preimage. `legacySignatureHash_eq_digest`: `legacySignatureHash`, which hashes the packed preimage `legacyPreimageBytes`, is the digest of the plan. `toList_legacyPreimageBytes`: the packed preimage has the bytes of `legacyPreimage`. `legacySignatureHash_eq_legacyOne`, `legacySignatureHash_eq_of_reachesFixedDigest`: under `ReachesFixedDigest`, the condition of the fixed digest, the digest is `legacyOne`. So two such requests have equal digests for any script codes, transactions, input indices and hash types. Conditional: `legacySignatureHashPlan_eq_reference_of_readBase`, `legacySignatureHashPlan_eq_reference_of_decodeBaseComplete` and `legacySignatureHashPlan_eq_reference_of_readAllowWitness` discharge the count bounds from a successful read. Each still requires fully parsed script code. `Script.MultisigRecoverySpend.sigAccepted_ordinary_iff_reference` and `sigAccepted_recovery_iff_reference` discharge it for the script code of the multisig-with-recovery template, under `MultisigRecoverySpend`. The corresponding `legacySignatureHash_eq_reference_of_readBase`, `legacySignatureHash_eq_reference_of_decodeBaseComplete` and `legacySignatureHash_eq_reference_of_readAllowWitness` equate the digests. Witness-allowed reads give `SIGVERSION_BASE` hashing on `w.tx` only
- **Comparison**: `lake test`: all 500 records of Core's `sighash.json` (D26), digests only, none with the fixed digest. 27 hand-derived signature-hash checks. They cover each hash type with and without ANYONECANPAY, and the raw hash types 0, 4, `0x21`, `0x22`, `0x103` and −1. They also cover null outputs, zero sequences, both fixed-digest cases, and short pushes in the script code. Expected preimages written by hand from D3 and D24. `lake test` does not run Core. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). `SignatureHash` runs on 4,496 requests. They include the 500 records of `sighash.json`, 1,589 at the boundaries of the input index and the hash type, and 2,000 random script codes. 71 are the signature hashes of the fixed-digest spends (*Script worked property, fixed digest of `SIGHASH_SINGLE`*). The other 336 come from the request fixtures and the large structured base set. Both early returns occur. The digests are equal, and each preimage of the oracle hashes to Core's digest. Core does not expose its preimage, so the bytes are not compared.
- **Refinement**: `legacySignatureHashPlan_eq_reference`: the field-by-field preimage construction is proved equal to the transaction-transformation reference `legacyReferencePlan` (`SignatureHashOld`) for every input index and hash type. The hypotheses: no instruction of the script code fails to parse, and the transaction has fewer than 2^32 inputs and 2^32 outputs. `legacySignatureHash_eq_reference`: the digests are equal under the same hypotheses. The plan constructs the whole preimage as a byte list. `legacySignatureHash` writes the same bytes into a `ByteArray` and hashes them, with no incremental hash sink. `block.validate` on the 1,000 mainnet blocks from height 111,001 took 1,974 s before this change and the linear byte readers, and 290 s after them. That is one run of each, on one core of a shared machine
- **Excluded**: `SIGVERSION_WITNESS_V0`. The wrapper `TransactionSignatureChecker::CheckSig` and the caller's preparation of the script code. Scripts of 2^32 bytes or more, which Core cannot hold.

## Legacy signature hash, transformation reference

- **Definition**: `Transaction.legacyReferencePlan`, `referenceTransaction`, `referenceInputs`, `referenceSequencedInputs`, `referenceOutputs`, `referenceScriptCode` in `Transaction.LegacySighashReference`
- **Theorems**: `referenceInputs_length_le`, `referenceOutputs_length_le`: the copy never has more inputs or outputs. See Refinement of *Legacy signature hash* for the equality
- **Comparison**: `lake test`: the 500 records of Core's `sighash.json` (D26), which all parse. The hand-derived preimages of *Legacy signature hash*, and two short-push cases where its expected preimage keeps the whole push
- **Refinement**: None
- **Excluded**: Counts are `Nat` values, not Core's `unsigned int` values

## Legacy signature hash, what ALL commits to

- **Definition**: `Transaction.HashType.IsAllOnly`, `TxIn.signedFields`, `legacyAllFields` in `Transaction.Proofs.LegacySighashCommitment`
- **Theorems**: For an `IsAllOnly` hash type (ANYONECANPAY clear, low five bits neither NONE nor SINGLE) and an input index of `tx`: `legacyReferencePlan_allOnly_commits`: equal transformation plans give equal `legacyAllFields` (version, lock time, each input's outpoint and sequence, outputs), with no other hypothesis. `legacySignatureHashPlan_allOnly_commits`: the same for production plans, with a fully parsed script code and fewer than 2^32 inputs and outputs in both transactions. `legacySignatureHashPlan_eq_of_allFields`, `legacyReferencePlan_eq_of_allFields`: the converse, with no other hypothesis. `legacyReferencePlan_eq_iff_allFields`, `legacySignatureHashPlan_eq_iff_allFields`. `legacySignatureHash_eq_of_allFields`: equal committed fields give equal digests. No digest-level converse, which would need collision resistance. `legacyReferencePlan_allOnly_index_eq`: with a nonempty copy of the script code, equal plans have the same input index. `legacySignatureHashPlan_eq_of_anyoneCanPay`, `legacySignatureHashPlan_eq_of_none`, `legacySignatureHashPlan_eq_of_single` and three corollaries: the fields that ALL with ANYONECANPAY, NONE and SINGLE leave open. `legacySignatureHashPlan_eq_of_none_anyoneCanPay`, `legacySignatureHashPlan_eq_of_single_anyoneCanPay`: under NONE and SINGLE with ANYONECANPAY, two transactions that agree on the version, the lock time and the outpoint and sequence of input `n`, and for SINGLE also on output `n`, have equal plans
- **Comparison**: `lake test`: mutations of the transactions of Core's 500 `sighash.json` records (D26) through the production digest, a test of DogeLib against itself. Their expected results come from these theorems, not from Core, and an expected difference assumes no collision. 240 ALL records each get a new lock time (digest changes) and new scriptSigs (unchanged). ALL with ANYONECANPAY: 187 other-input outpoints (unchanged) and 239 input-`nIn` sequences (changes). NONE: 4 records each with the outputs removed (unchanged), the input-`nIn` sequence (changes) and another sequence (unchanged). SINGLE: 4 records each with another output (unchanged) and output `nIn` (changes). Two hand cases: with an empty script code, indices 0 and 1 give the same preimage, and with `76 ab ac` they differ
- **Refinement**: None
- **Excluded**: The production forward direction without a fully parsed script code. Forward characterizations of NONE, SINGLE and ANYONECANPAY, alone or combined. Collision resistance

## Legacy signature-operation count

- **Definition**: `Transaction.Script.getSigOpCount`, `opcodeSigOps`, `Transaction.getLegacySigOpCount` in `Transaction.SigOps`, with the linear reader `nextOp`, `foldOps` and `dropExact`. Core's `GetLegacySigOpCount` (D106) and `CScript::GetSigOpCount(false)` (D107), as natural numbers
- **Theorems**: `Script.getSigOpCount_le` (*property*): the count of a script is at most 20 times the number of its bytes. No theorem bounds the count of a block. `Script.getSigOpCount_eq_scanOps`: the count equals the sum over the instructions of `scanOps`. `nextOp_view`: `nextOp` reads the instruction that `readOp` reads
- **Comparison**: `lake test`: the four counts of Core's test `GetSigOpCount` with `fAccurate` false (D109). `tx.check` and `block.check` compare `legacy_sigops` on every request, 724 of them built for the count. `scripts/compare_core.py` against Core's own function at `e0a1c15`: [evidence](../comparison-evidence.md#transaction-and-block-check-comparison-evidence). The count is also compared on the 11,018 real mainnet blocks of *Block check*, where the largest count of a block is 3,367.
- **Refinement**: None
- **Excluded**: `fAccurate` true and the P2SH count, which are in *Signature-operation cost*. Scripts of `2^31` bytes or more

## Packed codec composition

- **Definition**: `Serialization.instPackedCodecProd`, `Serialization.PackedCodec.ofEquiv`
- **Theorems**: See Refinement
- **Comparison**: None
- **Refinement**: `instLawfulPackedCodecProd`, `LawfulPackedCodec.ofEquiv`: agree with `instCodecProd` and `Codec.ofEquiv` when the components agree
- **Excluded**: None

## Packed CompactSize codec

- **Definition**: `Serialization.CompactSize.encodeInto`, `CompactSize.decodeSlice`, `CompactSize.packedCodec`
- **Theorems**: See Refinement
- **Comparison**: `lake test`: one encoding and one decoding at a nonzero offset, through the compiled code
- **Refinement**: `lawfulPackedCodec`: agrees with `CompactSize.codec` on every value and every slice, in failure, value and remainder bytes
- **Excluded**: The packed form of the bounded reader is in the row *CompactSize, Core's bounded reader*

## Packed counted-list codecs

- **Definition**: `Serialization.instPackedCodecCountedList`, `instPackedCodecCountedListBytes`
- **Theorems**: See Refinement
- **Comparison**: `lake test`: the two genesis coinbase scripts at nonzero offsets, through the byte instance and through `CountedList.decodeSlice`. A list of 3,000,000 `UInt16` values, whole and one byte short
- **Refinement**: `instLawfulPackedCodecCountedList`: agrees with `instCodecCountedList` for every packed element codec that agrees with its codec. `instLawfulPackedCodecCountedListBytes`: the byte instance, which reads the bytes as one block, agrees with the same codec. Both on every value and every slice, in failure, value and remainder bytes
- **Excluded**: Stack use of the generic packed decoder is observed, not proved.

## Packed fixed-length byte strings

- **Definition**: `Serialization.pushBytes`, `readBytes`, `instPackedCodecBytes`
- **Theorems**: See Refinement
- **Comparison**: `lake test`: the merkle root at offset 36 and the null prevout hash appended at offset 5
- **Refinement**: `instLawfulPackedCodecBytes` (`toList_pushBytes`, `abstractParse_readBytes`): agrees with `instCodecBytes` for every `n`, on every value and every slice
- **Excluded**: None

## Packed fixed-width little-endian integers

- **Definition**: `Serialization.instPackedCodecUInt8` to `instPackedCodecUInt64`, `Serialization.packedBitVecLE`
- **Theorems**: See Refinement
- **Comparison**: `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers/Serialization.lean`.
- **Refinement**: `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `lawfulPackedCodec_packedBitVecLE`: agree with the list codecs on every value and every slice, in failure, value and remainder bytes
- **Excluded**: None

## Packed transaction codecs

- **Definition**: `Transaction.instPackedCodecOutPoint`, `instPackedCodecScript`, `instPackedCodecTxIn`, `instPackedCodecTxOut`, `instPackedCodecTransaction`
- **Theorems**: See Refinement
- **Comparison**: `lake test`: the genesis coinbase at offset 3, read and written. The 159 base-mode records of Core's transaction corpus, read
- **Refinement**: `instLawfulPackedCodecOutPoint` to `instLawfulPackedCodecTransaction`: agree with the codecs on every value and every slice, by transport
- **Excluded**: Base serialization only

## Reader combinators

- **Definition**: `Serialization.readFixed`, `readPair`, `readMap`, `readFixedSlice`, `readPairSlice`, `readMapSlice`
- **Theorems**: `readPair_agrees`, `readMap_agrees`: each preserves `ReaderAgrees`, the agreement of a reader with a codec under a condition. `readFixed_agrees`: `readFixed` agrees with its codec under the condition `True`. `readMap_agrees` needs `toFun (invFun b) = b` for every `b`
- **Comparison**: Through the transaction readers below
- **Refinement**: `abstractRead_readFixedSlice`, `abstractRead_readPairSlice`, `abstractRead_readMapSlice`: preserve complete results for lawful packed codecs and agreeing readers
- **Excluded**: No independent classification of errors. A `CDataStream` read whose position plus size reaches 2^32, where Core's `unsigned int` position wraps

## Script code serialization

- **Definition**: `Transaction.scriptCodeBytes`, `readOp`, `scanOps`, `lengthFieldWidth`, `pushSize`, `leValue` in `Transaction.LegacySighash`
- **Theorems**: `readOp_eq_op_iff`: `readOp` reads an instruction exactly when the bytes start with an opcode, its length field and its data. `readOp_eq_stop_iff`: it stops exactly on a short push or the empty script. `readOp_op_append`, `readOp_stop_prefix`, `readOp_stop_nil`: the bytes of one call and its input. `scanOps_prefix`: the bytes of the instructions, then the bytes of the failing call, start the script. `scanOps_eq_of_complete`: when no instruction parse failed, the instructions make the whole script. `scriptCodeBytes_eq_encode`: then, with no `OP_CODESEPARATOR` instruction, the script code is written as the ordinary script encoding
- **Comparison**: `lake test`: 13 hand-derived script codes: separators as instructions and inside push data, whole pushes, and short pushes of each push opcode. The corpus scripts contain separators but no short pushes.
- **Refinement**: None
- **Excluded**: No theorem about the bytes written for a script with a short push: known answers only. Scripts of 2^31 bytes or more, where `readOp` has no claim about `GetOp2`

## Transaction check, `CheckTransaction`

- **Definition**: `Transaction.checkTransaction`, `CheckTransactionError` with `rejectReason`, `dosScore` and `rejectCode`, `checkOutputs`, `hasDuplicate`, `hasDuplicateFrom`, `hasDuplicateScan`, `OutPoint.key`, `Transaction.isCoinBase`, `OutPoint.isNull` in `Transaction.Check`. Core's `CheckTransaction` (D106), with `fCheckDuplicateInputs` as a parameter
- **Theorems**: `hasDuplicate_eq_hasDuplicateScan`: the duplicate-input test with a `Std.TreeSet` equals the test of every pair. `hasDuplicate_eq_not_nodup`: it is true exactly when two outpoints are equal
- **Comparison**: `lake test`: all 118 records of `tx_valid.json` pass, as Core's test `tx_valid` requires (D30). Nine records of `tx_invalid.json` under "Tests for CheckTransaction()" give the result of their named rule. Two of them name `MAX_MONEY` with amounts near Bitcoin's bound, and Dogecoin's rule accepts them. `tx.check`: 1,384 requests. `scripts/compare_core.py` against Core's own function at `e0a1c15`: [evidence](../comparison-evidence.md#transaction-and-block-check-comparison-evidence). `block.check` also runs the check on every transaction of the 11,018 real mainnet blocks of *Block check*. Every reason of `CheckTransaction` is reached
- **Refinement**: None
- **Excluded**: Contextual transaction rules: finality, inputs and fees

## Transaction ID

- **Definition**: `Transaction.Transaction.txid`
- **Theorems**: `txid_val`: the bytes of the ID are the double SHA-256 digest of the base serialization, for every transaction
- **Comparison**: `lake test`: the ID of the genesis coinbase is the merkle root that Core asserts (D9). `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). Each `tx.decode_base` request that reads a transaction compares its ID with `CTransaction::GetHash`. All agree.
- **Refinement**: None
- **Excluded**: The witness hash `GetWitnessHash`. `GetHash` of a default-constructed `CTransaction()` or a copy of it, which is Core's cached zero

## Transactions, Core's base-mode reader

- **Definition**: `Transaction.Transaction.readBase`, `decodeBaseComplete`, `decodeBaseCompleteSlice`, `OutPoint.read`, `Script.read`, `TxIn.read`, `TxOut.read`, `Transaction.Transaction.readBaseSlice`, `OutPoint.readSlice`, `Script.readSlice`, `TxIn.readSlice`, `TxOut.readSlice`
- **Theorems**: For every input: `readBase_eq_ok_iff`, it accepts exactly what the codec accepts with every count within `MAX_SIZE` (`WithinMaxSize`). `readBase_encode`: round trip for `WithinMaxSize` transactions. `decodeBaseComplete_eq_ok_iff`: the complete reader accepts exactly a read with no remainder
- **Comparison**: `lake test`: the genesis coinbase, a transaction with no inputs, too-large and non-canonical counts for inputs, outputs and both scripts, error order, truncation, and trailing bytes. Expected results from Core's bytes (D9) and a reading of D1, D4 and D21. The 159 base-mode records of Core's `tx_valid.json` and `tx_invalid.json` (D28, D29), each read whole. `lake test` does not run Core. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). Core's reader runs on 175,024 requests. They cover every proper prefix of the 659 transactions of both corpora, and each with trailing bytes. In 259 of them, each count and length is replaced by non-canonical, too-large and truncated forms, and each fixed field by boundary values. They also cover transactions with no inputs, no outputs or empty scripts, and 5,000 transactions with one to three random byte changes each. All agree in result, error reason, bytes consumed and remainder. Slice checks cover the same genesis and signed-field values, every truncated genesis prefix, count errors, and nonzero offsets. The two base readers agree on complete results for all 159 base-mode and 39 witness-format corpus records.
- **Refinement**: `Transaction.abstractRead_readBaseSlice`: for every slice, the packed reader equals `readBase` through `abstractRead`, including errors, fields and remainder bytes. The field readers and bounded vector readers have the same agreement. `Transaction.decodeBaseCompleteSlice_eq`: for every slice, complete-result equality with `decodeBaseComplete s.toList`, including errors and trailing-byte counts.
- **Excluded**: The witness-allowed format, in its own row. No theorem classifies all errors against an independent Core error relation.

## Transactions, Core's witness-allowed reader

- **Definition**: `Transaction.Transaction.readAllowWitness`, `decodeAllowWitnessComplete`, `readSections`, `readStacks`, `WitnessReadError`, `CompleteWitnessReadError`, `WitnessTransaction`, `WitnessStack`, `WitnessStack.read`, `WitnessTransaction.encode` in `Transaction.Witness`
- **Theorems**: `readAllowWitness_eq_readBase`: for every input whose first input list is not empty, the reader is `readBase`. It adds an empty stack per input, and keeps the error. `WitnessTransaction.readAllowWitness_encode`: round trip under `WithinMaxSize`, for a transaction with witness data, or an input, or no output. `noInputsExample_not_roundTrip`: a transaction with no inputs and one output is not read back. `readAllowWitness_flags_two`, `readAllowWitness_flags_three`: flags `02` and `03` give `unknownOptionalData`. `readAllowWitness_flags_zero`, `readStacks_length`
- **Comparison**: `lake test`: the 39 witness-format records of Core's `tx_valid.json` and `tx_invalid.json` (D28, D29), each read whole and written again in the extended form. The 159 base-mode records through `readAllowWitness`. 24 hand-built cases of the error order: lists and stacks, then flag bits, then the lock time. Expected results from a reading of D4, D1 and D21. `lake test` does not run Core. `scripts/compare_core.py` runs both witness operations against Core at `e0a1c15` on all 198 corpus records, with the 39 extended records separately. It sends 26,526 prefix requests, 234 suffix requests, 50,860 count, length and stack mutations, 100 flag and stack cases, and 10,000 seeded byte-mutation requests. All agree, including fields, stacks, serialization, hashes, errors and remainders.
- **Refinement**: None
- **Excluded**: Consensus acceptance of witness data. Core rejects blocks with witness data on main and test at the pin (D9, D36). SOUNDNESS.md records the separate consensus mechanisms. Validity, witness programs and the witness signature hash. No packed reader.

## Transactions, base serialization codec

- **Definition**: `Transaction.OutPoint`, `Script`, `TxIn`, `TxOut`, `Transaction`, and their `Codec` instances
- **Theorems**: `instLawfulCodecOutPoint` to `instLawfulCodecTransaction`: round trip and canonicality on every value, input and remainder, by composition. `TxOut.toInt_amount`, `Transaction.toInt_signedVersion`: the signed values are the two's-complement readings of the bits
- **Comparison**: `lake test`: the genesis coinbase fields from `CreateGenesisBlock`, written again byte for byte. Versions and amounts with the high bit set. The 159 base-mode records of Core's transaction corpus (D28, D29), each written again byte for byte. `scripts/compare_core.py` runs Core at `e0a1c15` on the same requests ([docs/core-harness.md](../core-harness.md#the-core-harness)). Each `tx.decode_base` request that reads a transaction compares `serialized_hex` with Core's base serialization of it. All agree.
- **Refinement**: None
- **Excluded**: Witness data. Not Core's reader: it accepts counts above `MAX_SIZE`.

## Witness hash

- **Definition**: `Transaction.WitnessTransaction.wtxid`, `WitnessTransaction.hasWitness` in `Transaction.Witness`
- **Theorems**: `wtxid_of_hasWitness_false`: without witness data it is the transaction ID
- **Comparison**: `lake test`: the genesis coinbase, which has no witness data. `bash scripts/test_oracle.sh`: both hashes from independent bytes and Python hashlib for all 198 corpus records and hand-built fixtures. `scripts/compare_core.py`: every successful witness operation compares both hash orders with Core's `GetHash` and `GetWitnessHash` at `e0a1c15`
- **Refinement**: None
- **Excluded**: A serialization format only. Core rejects blocks with witness data on main and test at the pin (D9, D36). See SOUNDNESS.md for the separate consensus mechanisms. `GetWitnessHash` of a default-constructed `CTransaction()` or a copy of it, which is Core's cached zero
