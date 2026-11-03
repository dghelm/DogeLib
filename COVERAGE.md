# Coverage

What DogeLib implements, per operation and per kind of evidence ([CONTRIBUTING.md](CONTRIBUTING.md#coverage-and-status)). Each column records a separate claim. A blank cell means nothing exists.

SHA-256, double SHA-256 and the codec foundations of the `Base` and `Serialization` layers are implemented.
No Dogecoin-specific wire structure is implemented yet.

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
| Double SHA-256 | `Cryptography.Hash.Sha256d.hash` | `size_hash`: 32 bytes. `hash_eq_spec`: equals the FIPS 180-4 model applied twice, for messages shorter than 2^61 bytes | `lake test`: the genesis coinbase txid and the three genesis block hashes that Dogecoin Core asserts | None | Messages of 2^61 bytes or more |
| Fixed-width little-endian integers | `Serialization.instCodecUInt8` to `instCodecUInt64`, `Serialization.bitVecCodecLE` | `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`: round trip and canonicality on every value, every input and every remainder | `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers.lean`. | None | None |
| Packed codec composition | `Serialization.instPackedCodecProd`, `Serialization.PackedCodec.ofEquiv` | See Refinement | None | `instLawfulPackedCodecProd`, `LawfulPackedCodec.ofEquiv`: agree with `instCodecProd` and `Codec.ofEquiv` when the components agree | None |
| Packed fixed-width little-endian integers | `Serialization.instPackedCodecUInt8` to `instPackedCodecUInt64`, `Serialization.packedBitVecLE` | See Refinement | `lake test`: fields of the main-network genesis header and the genesis coinbase, through the compiled code. See `tests/KnownAnswers.lean`. | `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `lawfulPackedCodec_packedBitVecLE`: agree with the list codecs on every value and every slice, in failure, value and remainder bytes | None |
| SHA-256 | `Cryptography.Hash.Sha256.hash` | `hash_eq_spec`: equals a separate FIPS 180-4 model, for messages shorter than 2^61 bytes | `lake test`: 129 NIST CAVP vectors (CAVS 11.0) through the compiled code | None | Messages of 2^61 bytes or more, and inputs that are not whole bytes |
