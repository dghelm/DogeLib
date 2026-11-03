# Coverage

What DogeLib implements, per operation and per kind of evidence ([CONTRIBUTING.md](CONTRIBUTING.md#coverage-and-status)). Each column records a separate claim. A blank cell means nothing exists.

SHA-256, double SHA-256, the codec foundations of the `Base` and `Serialization` layers, and CompactSize are implemented.
No Dogecoin data structure, such as a transaction or a block header, is implemented yet.

## Legend

| Column | Meaning |
| --- | --- |
| Definition | An executable definition exists in the specification target |
| Theorems | Named theorems, each with its domain and hypotheses or a link to them |
| Comparison | Comparison evidence: which implementation, which corpus, which revision, which run |
| Refinement | A proved relationship to another implementation, naming that implementation |
| Excluded | Inputs, modes, or eras deliberately outside the current claims |

Use *conditional* in the Theorems column when a theorem depends on a hypothesis that no caller yet discharges.

## Operations

Add rows in sorted order by operation name. Change only the cells your evidence supports.

| Operation | Definition | Theorems | Comparison | Refinement | Excluded |
| --- | --- | --- | --- | --- | --- |
| Byte slice reads | `ByteSlice.toList`, `ByteSlice.take`, `ByteSlice.drop`, `ByteSlice.uncons` in `Base.ByteSlice` | `toList_take`, `toList_drop`, `toList_of_uncons_some`, `toList_of_uncons_none`: each read agrees with the list operation on `toList`, for every slice | None | None | None |
| Codec composition | `Serialization.instCodecProd`, `Serialization.Codec.ofEquiv` | `instLawfulCodecProd`: the pair of two lawful codecs is lawful. `LawfulCodec.ofEquiv`: transport is lawful if the two functions are inverse to each other (a hypothesis). `encode_injective` for every lawful codec | None | None | None |
| CompactSize, Core's bounded reader | `Serialization.CompactSize.decodeBounded`, `maxSize`, `ReadError` | For every input: `decodeBounded_eq_ok_iff_valid`, it accepts exactly the inputs of the separate relation `ValidCompactSizePrefix`, with its value and exact remainder. `decodeBounded_eq_ok_iff_decode`: it accepts exactly what `CompactSize.decode` accepts with a value up to `0x02000000`. `decodeBounded_eq_error_tooLarge_iff`: it reports `tooLarge` exactly when `decode` accepts a larger value. `decodeBounded_encode`: round trip for every value up to `0x02000000`. `decodeBounded_maxSize_succ`: it rejects `fe 01 00 00 02` | `lake test`: Core's `compactsize` sweep and `noncanonical` cases (D20, lines 231 to 291), truncation, and values above `MAX_SIZE`, through the compiled code. Expected results from Core's assertions and a reading of D1 and D21. Core itself does not run. See `tests/KnownAnswers.lean`. | None | No theorem says which inputs give `truncated` or `nonCanonical`: known answers only. No packed form. Truncation is modeled as `CDataStream` reports it (D21). Other stream classes are not compared. |
| CompactSize, generic canonical codec | `Serialization.CompactSize.encode`, `CompactSize.decode`, `CompactSize.codec` | `lawfulCodec` (`decode_encode`, `decode_canonical`): round trip and canonicality on every `UInt64`, every input and every remainder. `decode_eq_some_iff`: `decode` accepts exactly the inputs of the separate relation `CanonicalCompactSizePrefix`. `encode_length_le`: at most 9 bytes. `encode_head`: only 0 starts with `0x00` | `lake test`: the encoder bytes at the boundaries of the forms, derived from `WriteCompactSize` (D1). The decoder on canonical encodings above `MAX_SIZE`. | None | Not Core's reader: it accepts values above `MAX_SIZE`. Not a registered `Codec UInt64` instance. |
| Double SHA-256 | `Cryptography.Hash.Sha256d.hash` | `size_hash`: 32 bytes. `hash_eq_spec`: equals the FIPS 180-4 model applied twice, for messages shorter than 2^61 bytes | `lake test`: the genesis coinbase txid and the three genesis block hashes that Dogecoin Core asserts | None | Messages of 2^61 bytes or more |
| Fixed-width little-endian integers | `Serialization.instCodecUInt8` to `instCodecUInt64`, `Serialization.bitVecCodecLE` | `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`: round trip and canonicality on every value, every input and every remainder | `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers.lean`. | None | None |
| Packed codec composition | `Serialization.instPackedCodecProd`, `Serialization.PackedCodec.ofEquiv` | See Refinement | None | `instLawfulPackedCodecProd`, `LawfulPackedCodec.ofEquiv`: agree with `instCodecProd` and `Codec.ofEquiv` when the components agree | None |
| Packed CompactSize codec | `Serialization.CompactSize.encodeInto`, `CompactSize.decodeSlice`, `CompactSize.packedCodec` | See Refinement | `lake test`: one encoding and one decoding at a nonzero offset, through the compiled code | `lawfulPackedCodec`: agrees with `CompactSize.codec` on every value and every slice, in failure, value and remainder bytes | The bounded reader has no packed form |
| Packed fixed-width little-endian integers | `Serialization.instPackedCodecUInt8` to `instPackedCodecUInt64`, `Serialization.packedBitVecLE` | See Refinement | `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers.lean`. | `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `lawfulPackedCodec_packedBitVecLE`: agree with the list codecs on every value and every slice, in failure, value and remainder bytes | None |
| SHA-256 | `Cryptography.Hash.Sha256.hash` | `hash_eq_spec`: equals a separate FIPS 180-4 model, for messages shorter than 2^61 bytes | `lake test`: 129 NIST CAVP vectors (CAVS 11.0) through the compiled code | None | Messages of 2^61 bytes or more, and inputs that are not whole bytes |
