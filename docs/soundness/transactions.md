# Soundness: Transactions and Legacy Signature Hashing

This file states what the transaction reader and legacy signature-hash proofs establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: Base-mode and packed-slice transaction readers, witness-allowed serialization, legacy signature hashing, transformation reference equivalence, and `SIGHASH_ALL` commitments.
- **Specification modules**: `DogeLib.Transaction.Types`, `Serialization`, `Txid`, `Witness`, `LegacySighash`, and `LegacySighashReference`.
- **Proof modules**: `DogeLib.Transaction.Proofs.*` (except `Check` and `SigOps`) and `DogeLib.Serialization.Proofs.Reader`.
- **Key boundaries**: Witness serialization models the wire format only and makes no consensus acceptance claim (A5).
  Forward commitment theorems require no hash assumption, while collision resistance of double SHA-256 remains outside the proofs (A4).

## Packed base-mode transaction reader

`Transaction.readBaseSlice` implements the base-mode prefix reader over `ByteSlice`.
`Transaction.abstractRead_readBaseSlice` states, for every slice `s`:

```lean
abstractRead (Transaction.readBaseSlice s) = Transaction.readBase s.toList
```

The equality preserves every error, every transaction field and every remainder byte.
It has no success hypothesis or bound on the input slice.
The theorem composes complete-result agreement for fixed fields, reader combinators, bounded vectors and script bytes.

The bounded vector theorem assumes complete-result agreement of the element readers.
Its loop theorem covers every element count and every array accumulator.
The script reader checks `s.size` before it copies the consumed bytes.
The list reader remains the specification.

`lake test` exercises the slice reader on the genesis coinbase, signed fields, every proper genesis prefix and count errors at each field.
It compares complete base-mode results on the 159 base-mode and 39 witness-format corpus records.
These comparisons use nonzero slice offsets with bytes outside both bounds.
A base-mode read of a witness-format record does not establish witness parsing.

The benchmark in BUILDING.md measures generated workloads separately from this conformance evidence.
There is no theorem about execution time, allocation or stack use.
Core's compiled byte-array operations remain trusted (B1, B2).

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `abstractRead_readFixedSlice`, `abstractRead_readPairSlice`, `abstractRead_readMapSlice`, `CountedList.abstractRead_readElemsBoundedSliceLoop` | `propext` |
| `CountedList.abstractRead_decodeBoundedSlice`, `CountedList.abstractRead_readBytesSlice`, `CountedList.abstractRead_decodeBoundedBytesSlice`, `OutPoint.abstractRead_readSlice`, `Script.abstractRead_readSlice`, `TxIn.abstractRead_readSlice`, `TxOut.abstractRead_readSlice`, `Transaction.abstractRead_readBaseSlice` | `propext`, `Classical.choice`, `Quot.sound` |

## Transactions

`DogeLib.Transaction` defines the fields of a transaction and its base serialization, the format without witness data (SOURCES.md, D4).
The types keep the raw bits of every field and check nothing.
`TxOut.value` and `Transaction.version` are the bits of Core's `int64_t` and `int32_t`.
`TxOut.toInt_amount` and `Transaction.toInt_signedVersion` say that the signed values are their two's-complement readings.
The theorems are in `DogeLib.Transaction.Proofs` and `DogeLib.Serialization.Proofs.Reader`.

Each codec is the codec of the tuple of its fields, carried to the structure by `Codec.ofEquiv`.
So the codec laws (`instLawfulCodecOutPoint` to `instLawfulCodecTransaction`) and the packed agreement (`instLawfulPackedCodecOutPoint` to `instLawfulPackedCodecTransaction`) follow by composition.
The codec reads counts with the generic CompactSize decoder, so it is not Core's reader.

`Transaction.readBase` is Core's `UnserializeTransaction` with `SERIALIZE_TRANSACTION_NO_WITNESS`.
It is built from readers of the fields with `readFixed`, `readPair`, `readMap` and `CountedList.decodeBounded`.
`ReaderAgrees c r P` says that the reader `r` accepts exactly what the codec `c` accepts with a value that satisfies `P`, with the same value and remainder.
`readFixed_agrees` gives it for `readFixed` with the condition `True`.
The other constructions preserve it (`readPair_agrees`, `readMap_agrees`, `CountedList.decodeBounded_agrees`), and `readMap_agrees` needs `toFun (invFun b) = b` for every `b`.

`Transaction.WithinMaxSize` says that the number of inputs, the number of outputs and the length of each script are at most `0x02000000`.
For all bytes, transactions and remainders:

- `Transaction.readBase_eq_ok_iff`: `readBase bs = ok (tx, rest)` exactly when the codec decodes `bs` as `(tx, rest)` and `tx.WithinMaxSize`.
- `Transaction.readBase_encode`: for every `tx` with `WithinMaxSize`, `readBase (encode tx ++ rest) = ok (tx, rest)`.
- `Transaction.decodeBaseComplete_eq_ok_iff`: the complete reader returns `tx` exactly when `readBase` returns `tx` with no remainder.

`Transaction.txid_val` says that the bytes of the transaction ID are the double SHA-256 digest of the base serialization.
So `txid` never takes the fallback branch of `digestToHash256`.
This says nothing about which values a digest can take.

`txid` is `CTransaction::ComputeHash`, and Core's `GetHash` returns a cached value.
The default constructor `CTransaction()` stores zero there (D23, lines 78 to 81), and a copy of an object copies its cache.
The constructors from `CMutableTransaction` and from a stream store `ComputeHash()`.
So `txid` is `GetHash`, and `WitnessTransaction.wtxid` is `GetWitnessHash`, for every `CTransaction` except a default-constructed one and its copies.
Core's deserialization and its conversion from `CMutableTransaction` compute the cache, so no decoded transaction has the zero cache.

These theorems relate the reader to the codec, and the codec to a reading of D4 (A1).
No theorem classifies every error against an independent Core error relation, or proves that the order of reads is Core's.
`lake test` checks the errors and their order on short inputs.
It also reads the genesis coinbase, whose ID must be the merkle root that Core asserts (D9).
Core itself does not run.

`lake test` also runs the base-mode records of Core's `tx_valid.json` and `tx_invalid.json` (D28, D29): 159 transactions.
For each one, `readBase` reads the whole transaction and `decodeBaseComplete` accepts it.
The codec writes the same bytes again, and the packed codec reads the same transaction.
Core's own tests check scripts, not these four properties, so these are DogeLib's checks on Core's bytes.

A record is in base mode when byte 4, the first byte of its input count, is not `00`. Then Core never reads a flags byte (D4, lines 219 to 230).
The 39 other records use the witness-allowed format, which the next section covers.

`readBase` is the base mode only.
Without `SERIALIZE_TRANSACTION_NO_WITNESS`, Core reads an empty input list as a marker and then a flags byte (A5).
A transaction with no inputs, `01000000 00 01 …`, has a different reading in that mode.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `TxOut.toInt_amount`, `Transaction.toInt_signedVersion` | None |
| `ReaderAgrees.congr`, `readFixed_agrees`, `readMap_agrees` | `propext` |
| `readPair_agrees`, `CountedList.readElemsBounded_eq_ok_iff_of_agrees`, `CountedList.readByte_agrees`, `instLawfulCodecOutPoint`, `instLawfulCodecScript`, `instLawfulCodecTxIn`, `instLawfulCodecTxOut`, `instLawfulCodecTransaction`, `OutPoint.read_agrees`, `Transaction.decodeBaseComplete_eq_ok_iff`, `digestToHash256_val`, `Transaction.txid_val` | `propext`, `Quot.sound` |
| `CountedList.decodeBounded_agrees`, `CountedList.decodeBoundedBytes_agrees`, `instLawfulPackedCodecOutPoint` to `instLawfulPackedCodecTransaction`, `Script.read_agrees`, `TxIn.read_agrees`, `TxOut.read_agrees`, `Transaction.readBase_agrees`, `Transaction.readBase_eq_ok_iff`, `Transaction.readBase_encode`, `Transaction.decodeBaseComplete_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream files use no `bv_decide` (C2).

## Transactions: the witness-allowed format

`DogeLib.Transaction.Witness` models the format that Core reads and writes without `SERIALIZE_TRANSACTION_NO_WITNESS` (D4, lines 211 to 272).
It models a serialization format only.
At the pinned commit, `IsWitnessEnabled` returns false on every network (`src/validation.cpp`, lines 3002 to 3008, D36).
`ConnectBlock` uses that function, so it never enables `SCRIPT_VERIFY_WITNESS` (lines 1913 to 1917).
Separately, `ContextualCheckBlock` checks `DEPLOYMENT_SEGWIT` through versionbits directly for witness commitments (lines 3163 to 3181).
Without a checked commitment, it rejects witness data as `unexpected-witness` (lines 3183 to 3187).

The deployment timeout is 0 on main and test, and 999999999999 on regtest (`src/chainparams.cpp`, lines 111, 267 and 408, D9).
Thus main and test reject blocks with witness data.
Regtest's deployment parameters do not enable witness script verification.
No definition or theorem here says that a transaction in this format is valid, or that a network accepts it.

`WitnessTransaction` holds a `Transaction` and one `WitnessStack` per input. Its field `witnesses_length` requires the count.
`Transaction.readAllowWitness` follows Core's order of reads.
It reads the version and the input list, then the flags byte if that list is empty.
Then come the lists, the stacks, the check of the other flag bits, and the lock time.
`WitnessTransaction.WithinMaxSize` adds the bounds of each stack, its item count and each item's length, to `Transaction.WithinMaxSize`.

- `Transaction.readAllowWitness_eq_readBase`: suppose the first input list of the bytes is not empty.
  Then the reader returns what `readBase` returns, with an empty stack per input, and the same error.
- `WitnessTransaction.readAllowWitness_encode`: for every `w` with `WithinMaxSize`, `readAllowWitness (w.encode ++ rest) = ok (w, rest)`, if `w` has witness data, or an input, or no output.
- `noInputsExample_not_roundTrip`: a transaction with no inputs, one output and no witness data is not read back. The complete reader reports 7 bytes left over.
- `Transaction.readAllowWitness_flags_zero`: a zero input count and zero flags give a transaction with no inputs and no outputs.
- `readAllowWitness_flags_two`, `readAllowWitness_flags_three`: two complete transactions with flags `02` and `03` fail with `unknownOptionalData`.
- `readStacks_length`: the reader finds one stack per input, so its last check never fails.
- `WitnessTransaction.wtxid_of_hasWitness_false`: without witness data, the witness hash is the transaction ID.

No theorem says which error the reader reports.
`lake test` checks the error order on hand-built inputs, with expected results from a reading of D4.
The lists and stacks fail first, the other flag bits next, and the lock time last.

`lake test` also reads and writes again the 39 witness-format records of Core's corpus.
Each of them has witness data, so the writer uses the extended form.
`lake test` does not run Core.
`bash scripts/test_oracle.sh` checks both hashes against Python hashlib on all 198 corpus records, including the 39 with witness data.
`scripts/compare_core.py` compares both witness operations with pinned Core, including those 39 records and their malformed variants.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_length`, `WitnessStack.isEmpty_iff` | `propext` |
| `instLawfulCodecWitnessStack`, `readStacks_length`, `Transaction.readAllowWitness_eq_readBase`, `noInputsExample_not_roundTrip`, `readAllowWitness_flags_two`, `readAllowWitness_flags_three`, `WitnessTransaction.wtxid_of_hasWitness_false` | `propext`, `Quot.sound` |
| `WitnessStack.read_agrees`, `WitnessTransaction.readAllowWitness_encode`, `Transaction.readAllowWitness_flags_zero` | `propext`, `Classical.choice`, `Quot.sound` |

## Legacy signature hash

`DogeLib.Transaction.LegacySighash` specifies Core's `SignatureHash` with `SIGVERSION_BASE` (SOURCES.md, D3).
`legacySignatureHashPlan` returns a `LegacyHashPlan`: the fixed digest `legacyOne`, or the bytes to hash with double SHA-256.
The preimage is written field by field after `CTransactionSignatureSerializer`, not by transforming a transaction and serializing it.
The theorems are in `DogeLib.Transaction.Proofs.LegacySighash`, except `readOp_rest_length`, `readPush_op_append` and `readOp_op_append`. Those are in the specification module, because `scanOps` and `findAndDelete` need them to terminate.
For every script code, transaction, input index and hash type:

- `legacySignatureHashPlan_eq_fixedDigest_iff`: the plan is `fixedDigest legacyOne` exactly when `nIn` is at least the number of inputs. With SINGLE, it is also `legacyOne` when `nIn` is at least the number of outputs.
- `legacySignatureHashPlan_eq_hashBytes`: otherwise the plan is `hashBytes (legacyPreimage …)`.
- `legacySignatureHash_eq_legacyOne`: under `ReachesFixedDigest`, the condition of the first item, the digest is `legacyOne`.
  `legacySignatureHash_eq_of_reachesFixedDigest`: so two such requests have equal digests, for any script codes, transactions, input indices and hash types.
  [The fixed digest of `SIGHASH_SINGLE`](script.md#script-worked-property-the-fixed-digest-of-sighash_single) states the result for a whole spend.
- `legacySignatureHash_eq_digest`: `legacySignatureHash` is the digest of `legacySignatureHashPlan`.
  `legacySignatureHash` hashes `legacyPreimageBytes`, a `ByteArray` that the packed encoders write, and `toList_legacyPreimageBytes` says that its bytes are `legacyPreimage`.
- `legacyPreimage_eq`: the preimage is a body, then the 4 bytes of the hash type. The body depends on the hash type only through its ANYONECANPAY, NONE and SINGLE flags. `HashType.flags_eq_of_and` says that the flags depend only on the bits `0x9f`.
- `scriptCodeBytes_eq_encode`: when no instruction parse failed and no instruction is `OP_CODESEPARATOR`, the script code is written as the ordinary encoding of the script.
- `readOp_eq_op_iff` and `readOp_eq_stop_iff`: `readOp` reads an instruction exactly when the bytes start with an opcode, its length field and its data. The field has the width that the opcode requires, and the data has the size that they give. It stops exactly on a short push or the empty script.

Two plans that are equal give equal digests for any hash function, so no collision assumption is needed for that equality.
No theorem says anything about which digests a plan can produce.

These theorems relate parts of the definition to each other. That the definition is Core's rests on a reading of D3 and D24 (A1) and on the known answers.
`lake test` runs all 500 records of Core's `sighash.json` (D26), which give digests only.
No record reaches the fixed digest. The generator in `sighash_tests.cpp` (D2, line 104) gives a SINGLE transaction as many outputs as inputs.

Hand-derived preimages cover the fixed digest, the other cases, and scripts that end in a short push, which the corpus does not contain.
Core itself does not run.

The definition makes three choices where Core's types decide the result.
`nIn`, the input count, the output count and `nIn + 1` are reduced modulo 2^32, as Core's `unsigned int` variables are.
That changes the result only for a transaction with 2^32 inputs or outputs, or for SINGLE with `nIn = 0xffffffff`.
The script-code count is computed in `Nat`. A `CScript` cannot hold 2^32 bytes, so that case has no Core counterpart.

Not specified: the `SIGVERSION_WITNESS_V0` branch.
The caller of `legacySignatureHash` prepares the script code. Core's interpreter passes the script after the last executed `OP_CODESEPARATOR`, with the signature removed by `FindAndDelete`.
A theorem about a supplied script code says nothing about that preparation (A5).
[Script signature-code preparation](script.md#script-signature-code-preparation) specifies the preparation, and [the checker](script.md#script-signature-opcodes-and-the-checker) specifies `TransactionSignatureChecker::CheckSig`, which takes the hash type from the last byte of a signature.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readPush_stop` | None |
| `readPush_op_append`, `readOp_op_append`, `readOp_stop_nil`, `lengthFieldWidth_of_gt`, `lengthFieldWidth_of_lt`, `pushSize_of_gt` | `propext` |
| `readPush_eq_op_iff`, `readPush_eq_stop_iff`, `ByteArray.toList_toByteArray_eq` | `propext`, `Quot.sound` |
| `readOp_cons_eq`, `readOp_eq_op_iff`, `readOp_eq_stop_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `readOp_rest_length`, `readOp_stop_prefix`, `scanOps_prefix`, `scanOps_eq_of_complete`, `legacySignatureHashPlan_eq_fixedDigest_iff`, `legacySignatureHashPlan_eq_hashBytes`, `legacySignatureHash_eq_legacyOne`, `legacySignatureHash_eq_of_reachesFixedDigest`, `legacyPreimage_eq`, `HashType.flags_eq_of_and`, `LegacyHashPlan.digest_fixedDigest`, `LegacyHashPlan.digest_hashBytes_val` | `propext`, `Quot.sound` |
| `scriptCodeBytes_eq_encode`, `toList_legacyInputInto`, `toList_legacyInputsLoop`, `toList_legacyInputsInto`, `toList_legacySingleOutputsLoop`, `toList_legacyOutputsInto`, `toList_legacyPreimageBytes`, `legacySignatureHash_eq_digest` | `propext`, `Classical.choice`, `Quot.sound` |

## Legacy signature hash: transformation reference

`DogeLib.Transaction.LegacySighashReference` defines the same commitment a second way.
`legacyReferencePlan` follows `SignatureHashOld` (SOURCES.md, D2), Core's copy of the old `SignatureHash`.
It copies the transaction and removes the separators from the script code with `findAndDelete` (D24).
Then it blanks scripts, sequences and outputs, and serializes the copy with the base codec.

The production plan constructs the whole preimage as a byte list, field by field, before hashing.
An incremental hash sink is later work.
The two definitions share `readOp`, `Script.empty`, `TxOut.null`, `legacyOne`, the hash-type flags and the field codecs.

`legacySignatureHashPlan_eq_reference` says that the two plans are equal, for every input index and every hash type, under three hypotheses:

- No instruction of the script code fails to parse: `(scanOps sc.bytes.val).2 = []`.
- The transaction has fewer than 2^32 inputs.
- The transaction has fewer than 2^32 outputs.

`legacySignatureHash_eq_reference` gives the equality of the digests.
The equality is between two Lean definitions. It says nothing about memory use or speed, and nothing about C++ object code.

`DogeLib.Transaction.Proofs.LegacySighashReader` connects successful Core-compatible reads to these equalities.
`Transaction.WithinMaxSize.inputs_lt` and `Transaction.WithinMaxSize.outputs_lt` turn the reader bound `0x02000000` into the required strict bound 2^32.
`Transaction.readBase_eq_ok_iff` supplies `WithinMaxSize` for a successful base read.
`Transaction.decodeBaseComplete_eq_ok_iff` supplies the base read with an empty remainder for a successful complete read.
`Transaction.readAllowWitness_withinMaxSize` supplies the same bounds on `w.tx` after a successful witness-allowed read.
Its private helper `readSections_withinMaxSize` covers the ordinary input list, the lists after nonzero flags, and the zero-flags branch with empty lists.

For each reader, `legacySignatureHashPlan_eq_reference_of_readBase`, `legacySignatureHashPlan_eq_reference_of_decodeBaseComplete` and `legacySignatureHashPlan_eq_reference_of_readAllowWitness` equate the plans.
The corresponding digest theorems are `legacySignatureHash_eq_reference_of_readBase`, `legacySignatureHash_eq_reference_of_decodeBaseComplete` and `legacySignatureHash_eq_reference_of_readAllowWitness`.
Each corollary holds for every input index and hash type, including fixed-digest cases.
The caller must still establish `hParse`: `(scanOps sc.bytes.val).2 = []`.
A successful transaction read does not establish this condition on the supplied script code.

The witness-reader corollaries apply `SIGVERSION_BASE` hashing to `w.tx`, the base fields only.
They establish nothing about segregated witness or consensus acceptance of witness data.

Each hypothesis is needed for a reason.
The production serializer reduces the counts modulo 2^32, and `SignatureHashOld` does not.

Take a script that ends in a short push.
The serializer writes its bytes up to the cursor of the failed `GetOp`, and omits the unread rest. `FindAndDelete` keeps the rest.
`legacyPlans_differ_shortPush` shows this on the script `4c 05 aa`.
So for such a script the two Core functions commit to different bytes, and only the production function is consensus code.

`lake test` runs Core's 500 corpus records and the hand-derived preimages through both plans.
Every corpus script parses fully, so the corpus does not test the difference.

Core's `FindAndDelete` counts the copies it removes in an `int`, and `findAndDelete` counts them in a `Nat`.
The Core compatibility of `findAndDelete` excludes a count that overflows an `int`.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `take_one_set_zero` | None |
| `CountedList.encodeElems_eq_flatten`, `CountedList.encode_eq_flatten`, `readOp_separator`, `readOp_cons_opcode` | `propext` |
| `dropMatches_length_le`, `findAndDeleteLoop_length_le`, `findAndDelete_length_le`, `referenceInputs_length_le`, `referenceOutputs_length_le`, `TxIn.encode_eq`, `Transaction.encode_eq`, `Script.encode_eq`, `scanOps_of_op`, `scanOps_of_stop`, `dropMatches_nil`, `dropMatches_separator_cons`, `dropMatches_separator_of_ne`, `findAndDeleteLoop_of_op`, `findAndDeleteLoop_of_stop`, `findAndDeleteLoop_separator_cons`, `legacyPlans_differ_shortPush` | `propext`, `Quot.sound` |
| `findAndDeleteLoop_separator`, `keptBytes_length_add`, `findAndDelete_separator`, `encode_referenceScriptCode`, `referenceSequencedInputs_map_encode`, `encode_referenceInputs`, `encode_referenceOutputs`, `legacySignatureHashPlan_eq_reference`, `legacySignatureHash_eq_reference` | `propext`, `Classical.choice`, `Quot.sound` |

The reader corollaries and their supporting bounds have these axiom dependencies, by `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `Transaction.WithinMaxSize.inputs_lt`, `Transaction.WithinMaxSize.outputs_lt` | `propext`, `Quot.sound` |
| `readSections_withinMaxSize` (private), `Transaction.readAllowWitness_withinMaxSize` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_readBase`, `legacySignatureHash_eq_reference_of_readBase` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_decodeBaseComplete`, `legacySignatureHash_eq_reference_of_decodeBaseComplete` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_readAllowWitness`, `legacySignatureHash_eq_reference_of_readAllowWitness` | `propext`, `Classical.choice`, `Quot.sound` |

`DogeLib.Transaction.Proofs.ScanOps` proves that the hypothesis `hParse` survives the operations that build script code.
An instruction that `readOp` reads depends only on its own bytes (`readOp_append`, `readOp_bytes`).
So after a fully parsed head, a concatenation parses exactly as its tail does (`scanOps_append`, `scanOps_append_snd`).

`scanOps_drop`: in a fully parsed script, the suffix from a cursor at an instruction boundary parses completely.
The cursor is at a boundary when the bytes before it parse completely.
`findAndDelete_scanOps`: `FindAndDelete` keeps a fully parsed script fully parsed, when the pattern parses completely or is longer than the script.

The pattern hypothesis is needed.
The script `02 4c 01` parses as one push. The pattern `02` matches at its start, and the bytes that remain, `4c 01`, are a short `OP_PUSHDATA1`.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `scanOps_nil` | `propext`, `Quot.sound` |
| `readOp_append`, `readOp_bytes`, `scanOps_bytes`, `scanOps_opcode`, `scanOps_append`, `scanOps_append_snd`, `scanOps_drop`, `dropMatches_scanOps`, `findAndDeleteLoop_scanOps`, `findAndDelete_scanOps` | `propext`, `Classical.choice`, `Quot.sound` |

## Legacy signature hash: what ALL commits to

`DogeLib.Transaction.Proofs.LegacySighashCommitment` states what a legacy preimage commits to when the hash type is ALL without ANYONECANPAY.
Design record 0003, section 7, leaves that restriction to the hypotheses of a bridge property, and these theorems give it.

`HashType.IsAllOnly h` holds when the ANYONECANPAY bit `0x80` of `h` is clear and its low five bits are neither 2 (NONE) nor 3 (SINGLE).
That is the test of Core's serializer (D3), so the class includes the undefined low values, such as `0x00`, `0x04` and `0x21`.
Under `STRICTENC`, the encoding check rejects undefined hash types, and `0x01` is the only member that a signature can carry.
`legacyAllFields tx` is the version, the lock time, each input's outpoint and sequence in order, and the outputs.
It includes no scriptSig.

For the same script code `sc`, input index `n` and hash type `h` with `IsAllOnly h`:

- `legacyReferencePlan_allOnly_commits`: if `n` is an input index of `tx` and the transformation plans of `tx` and `tx'` are equal, then `legacyAllFields tx = legacyAllFields tx'`.
  There is no other hypothesis. The reference preimage is the base encoding of the copy, then the hash type, and `encode_injective` recovers the copy.
- `legacySignatureHashPlan_allOnly_commits`: the same for the production plans.
  It also needs the hypotheses of `legacySignatureHashPlan_eq_reference` for both transactions: a fully parsed script code, and fewer than 2^32 inputs and outputs in each.
- `legacySignatureHashPlan_eq_of_allFields` and `legacyReferencePlan_eq_of_allFields`: the converse, with no hypothesis beyond `IsAllOnly`.
  It also covers the fixed digest.
- `legacyReferencePlan_eq_iff_allFields` and `legacySignatureHashPlan_eq_iff_allFields` join the two directions.
- `legacyReferencePlan_allOnly_index_eq`: let `n` be an input index of `tx`, and let the copy of the script code, `referenceScriptCode sc`, be nonempty.
  Then equal transformation plans at indices `n` and `n'` give `n = n'`.

The index and count restrictions are needed. This proof additionally requires a fully parsed script code.
When `n` is an input index of neither transaction, both plans are the fixed digest `one`.

The production serializer writes the counts modulo 2^32, and only that many inputs or outputs.
So a transaction with 2^32 inputs or more commits to fewer inputs.
With an empty script code, every input of the copy has the empty script.
Then a transaction with two inputs has the same preimage at indices 0 and 1, as a known answer shows.

The production forward direction takes `hParse` from the transfer to the reference. A direct proof on the production body could drop it, and is not done.

`legacySignatureHash_eq_of_allFields` gives equal digests from equal committed fields.
No theorem goes from equal digests to equal fields: that needs collision resistance of double SHA-256, which DogeLib does not assume (A4).
The forward theorems are about the bytes that are hashed, so they need no assumption about the hash.

The weaker modes leave fields open. Each of these theorems gives equal production plans from agreement on fewer fields, with no other hypothesis:

- `legacySignatureHashPlan_eq_of_anyoneCanPay`, for ALL with ANYONECANPAY: the version, the lock time, the outputs, and the outpoint and sequence of input `n`. The other inputs and the input count are open.
- `legacySignatureHashPlan_eq_of_none`, for NONE without ANYONECANPAY: the version, the lock time, every outpoint and the sequence of input `n`. The outputs and the other sequences are open.
- `legacySignatureHashPlan_eq_of_single`, for SINGLE without ANYONECANPAY: the same inputs fields as NONE, and output `n`. The other outputs and the other sequences are open.
- `legacySignatureHashPlan_eq_of_none_anyoneCanPay`, for NONE with ANYONECANPAY: the version, the lock time, and the outpoint and sequence of input `n`. The outputs, the other inputs and the input count are open.
- `legacySignatureHashPlan_eq_of_single_anyoneCanPay`, for SINGLE with ANYONECANPAY: the same fields as NONE with ANYONECANPAY, and output `n`. The other outputs, the other inputs and the input count are open.

In the theorems with ANYONECANPAY, input `n` may be missing from both transactions. The SINGLE theorems also let output `n` be missing from both. In each such case both plans are the fixed digest `one`.
So they cover the case of design record 0009, section 11. There `n` is an input index of both transactions, and for SINGLE both have more than `n` outputs.

`legacySignatureHashPlan_anyoneCanPay_set_other`, `legacySignatureHashPlan_none_outputs` and `legacySignatureHashPlan_single_set_other_output` name one open field of each mode.

`lake test` mutates the transactions of Core's 500 `sighash.json` records and recomputes the production digest.
For each mode it changes one committed and one open field, and expects a different or the same digest.
These checks test DogeLib against itself: the expected results come from these theorems, not from Core.
An expected difference assumes no collision on those inputs.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `legacyAllFields_eq_iff`, `legacyInputBytes_congr`, `legacyInputsBytes_anyoneCanPay_congr`, `legacyOutputsBytes_all_congr`, `referenceTransaction_inputs_allOnly`, `referenceTransaction_outputs_allOnly`, `legacyReferencePlan_eq_hashBytes_of_allOnly`, `lt_of_legacyReferencePlan_eq`, `referenceTransaction_eq_of_legacyReferencePlan_eq`, `HashType.isSingle_eq_false_of_isNone`, `HashType.isNone_eq_false_of_isSingle`, `legacySignatureHashPlan_eq_of_anyoneCanPay`, `legacySignatureHashPlan_anyoneCanPay_set_other`, `legacySignatureHashPlan_eq_of_none_anyoneCanPay` | `propext`, `Quot.sound` |
| `mapIdx_eq_of_getElem`, `legacyInputsBytes_congr`, `legacyOutputsBytes_single_congr`, `legacySignatureHashPlan_eq_of_allFields`, `referenceSequencedInputs_false_eq`, `referenceSequencedInputs_signedFields`, `referenceTransaction_eq_of_allFields`, `legacyReferencePlan_eq_of_allFields`, `legacyAllFields_eq_of_referenceTransaction_eq`, `legacyReferencePlan_allOnly_commits`, `legacySignatureHashPlan_allOnly_commits`, `legacyReferencePlan_eq_iff_allFields`, `legacySignatureHashPlan_eq_iff_allFields`, `legacySignatureHash_eq_of_allFields`, `legacyReferencePlan_allOnly_index_eq`, `legacySignatureHashPlan_eq_of_none`, `legacySignatureHashPlan_eq_of_single`, `legacySignatureHashPlan_none_outputs`, `legacySignatureHashPlan_single_set_other_output`, `legacySignatureHashPlan_eq_of_single_anyoneCanPay` | `propext`, `Classical.choice`, `Quot.sound` |
