# Soundness: Serialization and Rust Refinement

This file states what the codec, CompactSize, counted-list, and Rust refinement proofs establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: `LawfulCodec`, `LawfulPackedCodec`, CompactSize decoders, the Aeneas Rust refinement of `CompactSize.decodeBounded`, and counted lists.
- **Specification and refinement modules**: `DogeLib.Serialization.*`, `Refinement.Rust.Generated.DogelibCompactsize`, and `Refinement.Rust.CompactSize` (from `Refinement/Rust/src/lib.rs`).
- **Proof modules**: `DogeLib.Serialization.Proofs.*` and `Refinement.Rust.CompactSize`.
- **Key boundaries**: Core's `CDataStream` wraps its read position above 2^32 bytes, and compiled packed codecs rely on Lean core's `ByteArray` primitives (B2).
  The Rust refinement theorem covers the extracted Lean model, while Charon, Aeneas, the Rust compiler, and runtime remain trusted (B6).

## Codecs

A codec has an encoder `encode : α → List UInt8` and a prefix decoder `decode : List UInt8 → Option (α × List UInt8)`.
The class `LawfulCodec` in `DogeLib.Serialization.Proofs.Codec` states two laws:

- `decode_encode`: for every value `a` and all bytes `rest`, `decode (encode a ++ rest) = some (a, rest)`.
- `decode_canonical`: for all bytes `bs`, if `decode bs = some (a, rest)`, then `bs = encode a ++ rest`.

The laws hold with no hypothesis for the codecs of `UInt8`, `UInt16`, `UInt32` and `UInt64` (`instLawfulCodecUInt8` to `instLawfulCodecUInt64`).
They also hold for the little-endian codec of `BitVec (8 * n)`, for every `n` (`lawfulCodec_bitVecCodecLE`).
They hold for a pair of lawful codecs (`instLawfulCodecProd`).
`LawfulCodec.ofEquiv` proves them for a codec carried along two functions, under the hypothesis that the functions are inverse to each other.
Each fixed-width instance discharges that hypothesis by `rfl`.
`encode_injective` follows from the round trip for every lawful codec.

The laws also hold for the codec of byte strings of a fixed length `n`, for every `n` (`instLawfulCodecBytes`), and so for `Hash256`, which is `Bytes 32`.
`decodeBytes_eq_none_iff` says that this decoder rejects exactly the inputs with fewer than `n` bytes.
`decodeBytes` tests the length of the first `n` bytes, so a read takes steps in `n`, not in the length of the input.
`decodeBytes_eq_dite` proves it equal to the read with the test `n ≤ bs.length`.

A decoder that satisfies these laws rejects every input that does not start with a canonical encoding.
The laws do not say which values a Dogecoin rule accepts.
For example, Core's CompactSize reader rejects some canonical encodings, so `CompactSize.decodeBounded` is not a codec and has its own contract (see *CompactSize*).
A decoder returns a remainder, and a client that needs the whole input consumed checks that the remainder is empty (D1).

The byte order of the integer codecs follows Core's `ser_writedata16` to `ser_writedata64` and `ser_readdata16` to `ser_readdata64`, by a reading of the source code (A1).
`lake test` checks the compiled list and packed codecs against fields of the main-network genesis header and the genesis coinbase.
Their bytes are hexadecimal literals whose double SHA-256 is the digest that Core asserts, and their values are the arguments of `CreateGenesisBlock` (SOURCES.md, D9).
These known answers cover `UInt8` to `UInt64`, pairs, truncated input, and slices that start at a nonzero offset.
They are not a comparison with Core on other inputs.

Core's `CDataStream` holds its read position in an `unsigned int`, and computes the next position in that type (D21, lines 151 and 347).
The list decoders return the exact remainder, and the packed decoders hold a natural-number offset.
With a 32-bit `unsigned int`, they agree with the stream while the read position plus the size of the read is below 2^32.
Above that bound Core's position wraps, and the codecs and readers make no claim about the stream.

## Packed codecs

A packed codec encodes into a `ByteArray` and decodes from a `ByteSlice`.
The class `LawfulPackedCodec` in `DogeLib.Serialization.Proofs.PackedCodec` states its agreement with a list codec:

- `toList_encodeInto`: for every value `a` and buffer `acc`, the bytes of `encodeInto a acc` are the bytes of `acc` followed by `encode a`.
- `abstractParse_decodeSlice`: for every slice `s`, the packed decoder fails exactly when `decode s.toList` fails.
  If both succeed, they return the same value, and the bytes of the remaining slice equal the remainder of `decode`.

Agreement holds with no hypothesis for the packed codecs of `UInt8` to `UInt64` (`instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`).
It also holds for the packed little-endian codec of `BitVec (8 * n)`, for every `n` (`lawfulPackedCodec_packedBitVecLE`).
It holds for a pair of agreeing packed codecs (`instLawfulPackedCodecProd`), and for every transport (`LawfulPackedCodec.ofEquiv`).
It holds for the packed codec of `Bytes n`, for every `n` (`instLawfulPackedCodecBytes`).
`LawfulPackedCodec.toList_encode` and `LawfulPackedCodec.abstractParse_decode` give the same agreement for a whole byte array.

The agreement theorems are about the Lean definitions of the packed codecs.
The compiled packed codecs run core's `@[extern]` implementations of `ByteArray.push` and `ByteArray.get`, and advance slices without copying.
`ByteSlice.toList`, the abstraction function of the agreement laws, copies the bytes in view through `ByteArray.extract`, which runs `ByteArray.copySlice`.
The packed decoder of byte lists also calls it to read its bytes.
The tests call `toList` to compare results, so they run that copy too.
No theorem covers these implementations (B1, B2).

## Axioms of the codec theorems

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `Bytes.length_val`, `Bytes.encode_length` | None |
| `LawfulCodec.ofEquiv`, `LawfulPackedCodec.ofEquiv`, `encode_injective`, `setWidth_setWidth_eq_self`, `instLawfulCodecBytes`, `decodeBytes_encode`, `decodeBytes_canonical`, `decodeBytes_eq_dite`, `Bytes.ofListExact?_eq_some_iff`, `Bytes.ofListExact?_val`, `Bytes.val_reverse`, `Bytes.reverse_reverse`, `Hash256.length_displayBytes`, `Hash256.ofDisplayBytes?_displayBytes`, `Hash256.displayBytes_ofDisplayBytes?` | `propext` |
| `instLawfulCodecProd`, `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`, `decodeBitVecLE_encodeBitVecLE`, `decodeBitVecLE_canonical`, `instLawfulPackedCodecProd`, `toList_pushBitVecLE`, `LawfulPackedCodec.toList_encode`, `ByteArray.toList_eq_data_toList`, `decodeBytes_eq_none_iff`, `toList_pushBytes` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `abstractParse_readBitVecLE`, `LawfulPackedCodec.abstractParse_decode`, `LawfulPackedCodec.abstractParse_decode_toByteArray`, `ByteSlice.toList_of_uncons_some`, `ByteSlice.toList_drop`, `instLawfulPackedCodecBytes`, `abstractParse_readBytes` | `propext`, `Classical.choice`, `Quot.sound` |

The source files are adapted from btc-verified at commit `ecf4f0d`. None of them uses `bv_decide` (C2).

## CompactSize

`DogeLib.Serialization.CompactSize` defines two decoders of the CompactSize format.
`decode` is the generic canonical decoder, and `decodeBounded` is Core's `ReadCompactSize` (SOURCES.md, D1).
The theorems are in `DogeLib.Serialization.Proofs.CompactSize`.

The generic codec `CompactSize.codec` satisfies both codec laws on every `UInt64` (`lawfulCodec`, from `decode_encode` and `decode_canonical`).
The packed codec `CompactSize.packedCodec` agrees with it on every value and every slice (`lawfulPackedCodec`).
`encode_length_le` says that an encoding has at most 9 bytes.
`encode_head` says that an encoding starts with a byte that is `0x00` only for the value 0.

Two relations state the accepted bytes without reference to a decoder.
`CanonicalCompactSizePrefix bytes value rest` lists the four forms.
For each form it gives the marker, the number of payload bytes, the little-endian value of the payload, and the smallest value.
`rest` is the bytes after the encoding.
`ValidCompactSizePrefix` adds `value ≤ 0x02000000`.
Each of these theorems holds for all bytes, values and remainders:

- `decode_eq_some_iff`: `decode bytes = some (value, rest)` exactly when `CanonicalCompactSizePrefix bytes value rest`.
- `decodeBounded_eq_ok_iff_valid`: `decodeBounded bytes = ok (value, rest)` exactly when `ValidCompactSizePrefix bytes value rest`.
- `decodeBounded_eq_ok_iff_decode`: `decodeBounded bytes = ok (value, rest)` exactly when `decode bytes = some (value, rest)` and `value ≤ 0x02000000`.
- `decodeBounded_eq_error_tooLarge_iff`: `decodeBounded bytes` is the error `tooLarge` exactly when `decode` accepts `bytes` with a value above `0x02000000`.
- `decodeBounded_encode`: for every `n ≤ 0x02000000` and all bytes `rest`, `decodeBounded (encode n ++ rest) = ok (n, rest)`.

The bound of the round trip is necessary.
`decodeBounded_encode_maxSize_succ` says that `decodeBounded (encode 0x02000001)` is `tooLarge`, and `decode_maxSize_succ` that `decode` accepts the same bytes, `fe 01 00 00 02`.

No theorem says which inputs give the errors `truncated` and `nonCanonical`.
The known answers check these errors on Core's `noncanonical` cases and on truncated inputs.
The order of Core's checks comes from a reading of `ReadCompactSize` (A1).
The relations are a second statement of the format, written from the same reading of D1, so a misreading of Core can be in both.
The known answers guard against that on the inputs they cover.

`lake test` runs Core's `compactsize` sweep of the powers of two up to `MAX_SIZE` and the cases of its `noncanonical` test (D20) through the compiled code.
The expected results are Core's assertions, or derived from D1 and from `CDataStream::read` (D21).
Core itself does not run, so this is not a Core comparison.

The packed codec runs core's `ByteArray.push` and `ByteArray.get`, as the other packed codecs do (B2).

`decodeBoundedSlice` is Core's reader over a `ByteSlice`.
`abstractRead_decodeBoundedSlice` compares it with `decodeBounded` on the bytes of each slice.
On every slice, it gives the same error, or the same value and remainder bytes.
`abstractRead` is the `Except` counterpart of `abstractParse`.
`lake test` runs the bounded cases through it at offset 3 of a buffer.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `maxSize_toNat` | None |
| `encode_maxSize_succ`, `encodeFixedWidth_length`, `abstractRead_error`, `abstractRead_ok` | `propext` |
| `lawfulCodec`, `decode_encode`, `decode_canonical`, `encode_length_le`, `encode_head`, `toUInt8_lt_fd`, `toUInt8_ne_zero`, `toList_encodeInto`, `readCanonical_toOption`, `decodeBounded_eq_error_tooLarge_iff`, `decode_maxSize_succ`, `decodeBounded_maxSize_succ`, `decodeBounded_encode_maxSize_succ` | `propext`, `Quot.sound` |
| `abstractRead_readPayloadSlice`, `abstractRead_readCanonicalSlice`, `abstractRead_decodeBoundedSlice`, `lawfulPackedCodec`, `abstractParse_decodeSlice`, `decode_eq_some_iff`, `decodeBounded_eq_ok_iff_decode`, `decodeBounded_eq_ok_iff_valid`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

Upstream proves two small facts in `decode_encode` and `encode_head` with `bv_decide`.
Here `toUInt8_lt_fd` and `toUInt8_ne_zero` prove them: each converts the bytes to natural numbers and closes the goal with `omega` (C2).

## Rust bounded CompactSize reader

`Refinement.Rust.CompactSize.decode_refines` compares the extracted Rust model `DogeLibRust.decode` with `CompactSize.decodeBounded`.
For every Rust-representable byte slice, the abstraction equals `some` of the specification's complete result.
The abstraction preserves `truncated`, `nonCanonical`, `tooLarge`, the decoded value and the remainder after the consumed count.
It maps a Rust panic or divergence to `none`, so the theorem also excludes those outcomes.
The theorem has no acceptance precondition.

`consumed_bounds` says that a successful consumed count is at most the input length and belongs to 1, 3, 5 or 9.
Both theorems hold on 32- and 64-bit platforms.
Their proofs do not select a platform word size.
B6 records the slice representation and extraction boundaries.

The Rust integration tests run the 20 bounded cases from `tests/KnownAnswers/Serialization.lean` and Core's 52-value power-of-two sweep.
The expected values and errors come from Core's assertions and a reading of D1 and D21.
These tests run the compiled Rust reader, without running Core or the generated Lean model.

By `#print axioms` with Lean `v4.35.0`:

| Declaration | Axioms |
| --- | --- |
| `DogeLibRust.join`, `DogeLibRust.decode`, `Refinement.Rust.CompactSize.abstractResult`, `Refinement.Rust.CompactSize.decode_refines`, `Refinement.Rust.CompactSize.consumed_bounds` | `propext`, `Classical.choice`, `Quot.sound` |

## Counted lists

`DogeLib.Serialization.CountedList` defines a counted list: a CompactSize count, then that many elements.
A `CountedList α` is a list with fewer than `2 ^ 64` elements.
As for CompactSize, there are two decoders.
`CountedList.decode` is the generic decoder, and `decodeBounded` is Core's `Unserialize_impl` for vectors (SOURCES.md, D1).
The theorems are in `DogeLib.Serialization.Proofs.CountedList`.

For every lawful element codec, the codec of counted lists satisfies both codec laws on every counted list (`instLawfulCodecCountedList`, from `decode_encode` and `decode_canonical`).
`decode_eq_some_iff` says that `decode` accepts exactly a count read by `CompactSize.decode`, followed by that many elements.
For every packed element codec that agrees with its codec, the packed codec of counted lists agrees with the codec (`instLawfulPackedCodecCountedList`).
The packed codec of byte lists does not call the element codec for each byte, and agrees with the same codec (`instLawfulPackedCodecCountedListBytes`).
Its decoder reads the bytes with `ByteSlice.toList`, so the compiled decoder runs `ByteArray.copySlice` (B2).
Its encoder appends each byte with `ByteArray.push`.

`decodeBounded` takes an element reader `elem`.
Its contract assumes that `elem` accepts exactly what the element codec accepts: `(elem bs).toOption = Codec.decode bs` for all bytes `bs`.
`readByte_toOption` discharges the assumption for `readByte` and `UInt8`.
Under the assumption, and for all bytes, counted lists and remainders:

- `decodeBounded_eq_ok_iff`: `decodeBounded elem bs = ok (cl, rest)` exactly when `decode bs = some (cl, rest)` and `cl` has at most `0x02000000` elements.
- `decodeBounded_encode`: if the element codec is also lawful and `cl` has at most `0x02000000` elements, then `decodeBounded elem (encode cl ++ rest) = ok (cl, rest)`.

Two theorems need no assumption on `elem`.
`decodeBounded_of_count_error` says that an error of Core's count reader is the error of the list reader.
So a count above `MAX_SIZE` is `tooLarge`, and no element is read.
`decodeBoundedBytes_eq` says that the block read of bytes, `decodeBoundedBytes`, is `decodeBounded readByte` on every input, including its errors.
Its block read `readBytes` tests the length of the first `n` bytes, and `readBytes_eq_ite` proves it equal to the read with the test `n ≤ bs.length`.

No theorem says which error an element failure gives.
It is the error of `elem`, and a later layer that defines an element reader states it.
Core grows a vector in blocks of about 5 MB, and the definitions do not.
A reading of D1 and D21 says that the blocks change neither the elements read nor the error (A1).

`lake test` runs the two scripts of the genesis coinbase through the generic, packed and bounded decoders, at nonzero offsets.
It also runs short inputs for each error of the bounded reader.
The expected results are Core's bytes (D9), or derived from D1 and D21.
Core itself does not run, so this is not a Core comparison.

`decode`, `decodeSlice` and `decodeBounded` read the elements with loop forms: `decodeElemsLoop`, `readElemsLoop` and `readElemsBoundedLoop`.
Each one calls itself in tail position and keeps the values read so far in an array.
`decodeElemsLoop_nil`, `readElemsLoop_nil` and `readElemsBoundedLoop_nil` prove that each returns what the recursive form returns, including every failure and error.
So every theorem about `decodeElems`, `readElems` and `readElemsBounded` holds for the readers.

These theorems are about results, not about stack use. Stack use is an observation of the compiled code (B1).
In one manual run of the `lake test` driver, the recursive forms overflowed the stack at 16,000,000 elements, and the loop forms read 16,000,000.
In `lake env lean --run`, the recursive forms overflowed at 5,000,000.
An element reader that itself recurses deeply can still use more stack, and `MAX_SIZE` itself (33,554,432 elements) was not run.
CI reads lists of 3,000,000 elements through the three readers, which checks results, not stack use.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_toOption` | None |
| `ofList?_eq_some`, `val_of_ofList?`, `decodeElems_encodeElems`, `toList_pushElems`, `readBytes_eq_ite`, `readElemsBounded_readByte`, `readElemsBoundedLoop_eq`, `readElemsBoundedLoop_nil` | `propext` |
| `decodeElemsLoop_eq`, `decodeElemsLoop_nil`, `readElemsLoop_eq`, `readElemsLoop_nil`, `instLawfulCodecCountedList`, `decode_encode`, `decode_canonical`, `decode_eq_some_iff`, `decodeElems_length`, `decodeElems_canonical`, `abstractParse_readElems`, `encode_uint8`, `decode_uint8_cons`, `decode_uint8_nil`, `encodeElems_uint8`, `decodeElems_uint8`, `decodeBounded_eq_ok_iff_parts`, `decodeBounded_of_count_error`, `readByte_toOption`, `decodeBoundedBytes_eq`, `decodeBoundedBytes_maxSize_succ`, `decode_maxSize_succ` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecCountedList`, `instLawfulPackedCodecCountedListBytes`, `abstractParse_readByteList`, `decodeBounded_eq_ok_iff`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream file uses no `bv_decide` (C2).
