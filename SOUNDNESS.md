# Soundness

This document says what the proofs of DogeLib establish, and what a user of DogeLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem. Both are assumed to match something outside Lean: the Dogecoin behavior, the code that runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of EthLib's [`SOUNDNESS.md`](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/SOUNDNESS.md), which follows s2n-bignum's.

[COVERAGE.md](COVERAGE.md) lists the definitions and their theorems.
Each section states the mitigations that exist today, and the policy for definitions that are not written yet.
A lane that adds a definition, a theorem, an execution path or a dependency updates the affected rows in the same change.

## Ways to use DogeLib

Each way of using DogeLib trusts a different set of things, so the summary table marks which risks apply to which use.
There are four uses:

- **P**: a Lean proof that imports the specification.
- **R**: a Lean program that runs the specification, such as the oracle.
- **I**: an implementation that is proved to refine the specification, such as extracted Rust.
- **F**: a client that compares against the fixtures in `tests/`.

## Summary

The risks fall into four gaps, one per link in the chain from Dogecoin behavior to client.
Gap A asks whether the definition says what Dogecoin does and what the client needs.
Gap B asks whether the code that runs matches the definitions.
Gap C asks whether the proof itself is sound.
Gap D asks whether the use of DogeLib holds together.

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match the pinned Dogecoin behavior | Source mappings, independent known answers and comparisons with pinned Core guard against a wrong definition. Lean model equivalence still requires source review. See [A1](#a1-a-wrong-definition) and [operation evidence](COVERAGE.md#operations). | P R I F |
| A2 | A theorem holds only under a hypothesis | Policy: each conditional theorem lists its hypotheses here and in `COVERAGE.md` | P I |
| A3 | Timing reveals secret data | None: no constant-time claim | R I |
| A4 | A security theorem idealises a primitive | None: no security theorem yet | P |
| A5 | A rule depends on a protocol context that the definition does not model | Policy: each operation records its mode, network and era in `SOURCES.md` | P R I F |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | Known answers and Core comparisons exercise the compiled specification on finite inputs. They do not prove compiler or runtime correctness. See [B1](#b1-the-compilers-and-the-runtime) and [operation evidence](COVERAGE.md#operations). | R |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R |
| B3 | Elaboration runs native code | None yet | P |
| B4 | The oracle's IO adapter or a foreign boundary is wrong | Oracle fixtures and Core comparisons check adapter results on the recorded inputs, and the declaration check includes `Exports`. See [B4](#b4-the-oracle-and-foreign-boundaries) for the trusted conversions and harness boundaries. | R F |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R |
| B6 | Extraction or the Rust toolchain is wrong | `decode_refines` relates the extracted Rust reader model to `decodeBounded`. Charon, Aeneas, library models, the Rust compiler and runtime remain trusted. See [B6](#b6-extraction-and-the-rust-toolchain). | I |
| C1 | The Lean kernel or its axioms are unsound | `lake exe check-decls` rejects transitive axiom dependencies outside the allowed set, including imported unfinished proofs. Kernel soundness and axiom consistency remain trusted. | P I |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any use | P I |
| C3 | A declaration reached the environment unchecked | No kernel replay. The declaration check requires every production module to be reachable from its default roots. | P I |
| D1 | A client misuses an operation, such as a prefix decoder where complete consumption is required | Policy: each public operation documents its input domain and consumption contract | R I |
| D2 | A dependency changes | Source and toolchain pins constrain dependency changes. The root package has no Lake dependencies, while the separate refinement package owns Aeneas and Mathlib. See [D2](#d2-dependency-changes). | P R I |
| D3 | The fixtures are wrong | Each fixture records its provenance. The NIST CAVP files and Core's `sighash.json` are pinned by digest, and CI checks the pins. Core's test cases are copied into `tests/KnownAnswers.lean` with their file and line. | F |

## What the proofs say

Each operation with a theorem has a subsection here.
It says what is proved, under which hypotheses and over which input domain, and what is not proved.
[COVERAGE.md](COVERAGE.md) gives the per-operation status. This section explains its meaning and limits.

### SHA-256

`hash_eq_spec` says that `hash` equals `Spec.hash` on every message shorter than 2^61 bytes.
`Spec.hash` restates FIPS 180-4 over 32-bit bit vectors, independently of the executable code.
The theorem depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.

The theorem does not show that `Spec.hash` matches FIPS 180-4.
A reader checks that by comparing the model with the standard (A1).
`lake test` runs the 129 byte-oriented NIST CAVP vectors through the compiled `hash` (B1).
The vectors come from NIST, not from the code under test, and `tests/cryptography/sha256/cavp/README.md` records their provenance.
They test the compiled code only on those inputs.
Both files are adapted from EthLib at commit `6a93711`.

### Double SHA-256

`Sha256d.hash` is `CHash256` of Dogecoin Core (SOURCES.md, D8): SHA-256 applied to the SHA-256 digest of the message.
`size_hash` says that the digest has 32 bytes.
`hash_eq_spec` says that `Sha256d.hash` equals the FIPS 180-4 model applied twice, on every message shorter than 2^61 bytes.
The inner digest has 32 bytes, so the outer application needs no hypothesis of its own.
`hash_eq_spec` depends on `propext`, `Classical.choice` and `Quot.sound`, and `size_hash` on `propext` and `Quot.sound`, by `#print axioms`.

`lake test` checks the compiled `Sha256d.hash` against four values that Dogecoin Core asserts.
They are the genesis merkle root and the genesis block hashes of the main, test and regression-test networks.
The bytes to hash are derived by hand from `src/chainparams.cpp`, and the derivation is in `tests/KnownAnswers.lean`.

Neither theorem says how Dogecoin orders the bytes of a hash for display, or which bytes it hashes.
Those belong to the definitions of the objects that are hashed.

### Codecs

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

A decoder that satisfies these laws rejects every input that does not start with a canonical encoding.
The laws do not say which values a Dogecoin rule accepts.
For example, Core's CompactSize reader rejects some canonical encodings, so `CompactSize.decodeBounded` is not a codec and has its own contract (see *CompactSize*).
A decoder returns a remainder, and a client that needs the whole input consumed checks that the remainder is empty (D1).

The byte order of the integer codecs follows Core's `ser_writedata16` to `ser_writedata64` and `ser_readdata16` to `ser_readdata64`, by a reading of the source code (A1).
`lake test` checks the compiled list and packed codecs against fields of the main-network genesis header and the genesis coinbase.
Their bytes are hexadecimal literals whose double SHA-256 is the digest that Core asserts, and their values are the arguments of `CreateGenesisBlock` (SOURCES.md, D9).
These known answers cover `UInt8` to `UInt64`, pairs, truncated input, and slices that start at a nonzero offset.
They are not a comparison with Core on other inputs.

### Packed codecs

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

### Axioms of the codec theorems

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `Bytes.length_val` | None |
| `LawfulCodec.ofEquiv`, `LawfulPackedCodec.ofEquiv`, `encode_injective`, `setWidth_setWidth_eq_self`, `instLawfulCodecBytes`, `decodeBytes_encode`, `decodeBytes_canonical`, `Bytes.encode_length`, `Bytes.ofListExact?_eq_some_iff`, `Bytes.ofListExact?_val`, `Bytes.val_reverse`, `Bytes.reverse_reverse`, `Hash256.length_displayBytes`, `Hash256.ofDisplayBytes?_displayBytes`, `Hash256.displayBytes_ofDisplayBytes?` | `propext` |
| `instLawfulCodecProd`, `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`, `decodeBitVecLE_encodeBitVecLE`, `decodeBitVecLE_canonical`, `instLawfulPackedCodecProd`, `toList_pushBitVecLE`, `LawfulPackedCodec.toList_encode`, `ByteArray.toList_eq_data_toList`, `decodeBytes_eq_none_iff`, `toList_pushBytes` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `abstractParse_readBitVecLE`, `LawfulPackedCodec.abstractParse_decode`, `LawfulPackedCodec.abstractParse_decode_toByteArray`, `ByteSlice.toList_of_uncons_some`, `ByteSlice.toList_drop`, `instLawfulPackedCodecBytes`, `abstractParse_readBytes` | `propext`, `Classical.choice`, `Quot.sound` |

The source files are adapted from btc-verified at commit `ecf4f0d`. None of them uses `bv_decide` (C2).

### Packed base-mode transaction reader

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

### CompactSize

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
### Rust bounded CompactSize reader

`Refinement.Rust.CompactSize.decode_refines` compares the extracted Rust model `DogeLibRust.decode` with `CompactSize.decodeBounded`.
For every Rust-representable byte slice, the abstraction equals `some` of the specification's complete result.
The abstraction preserves `truncated`, `nonCanonical`, `tooLarge`, the decoded value and the remainder after the consumed count.
It maps a Rust panic or divergence to `none`, so the theorem also excludes those outcomes.
The theorem has no acceptance precondition.

`consumed_bounds` says that a successful consumed count is at most the input length and belongs to 1, 3, 5 or 9.
Both theorems hold on 32- and 64-bit platforms.
Their proofs do not select a platform word size.
B6 records the slice representation and extraction boundaries.

The Rust integration tests run the 20 bounded cases from `tests/KnownAnswers.lean` and Core's 52-value power-of-two sweep.
The expected values and errors come from Core's assertions and a reading of D1 and D21.
These tests run the compiled Rust reader, without running Core or the generated Lean model.

By `#print axioms` with Lean `v4.35.0`:

| Declaration | Axioms |
| --- | --- |
| `DogeLibRust.join`, `DogeLibRust.decode`, `Refinement.Rust.CompactSize.abstractResult`, `Refinement.Rust.CompactSize.decode_refines`, `Refinement.Rust.CompactSize.consumed_bounds` | `propext`, `Classical.choice`, `Quot.sound` |

### Counted lists

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
In `lake test`, the recursive forms overflowed the stack at 16,000,000 elements, and the loop forms read 16,000,000.
In `lake env lean --run`, the recursive forms overflowed at 5,000,000.
An element reader that itself recurses deeply can still use more stack, and `MAX_SIZE` itself (33,554,432 elements) was not run.
CI reads lists of 3,000,000 elements through the three readers, which checks results, not stack use.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_toOption` | None |
| `ofList?_eq_some`, `val_of_ofList?`, `decodeElems_encodeElems`, `toList_pushElems`, `readElemsBounded_readByte`, `readElemsBoundedLoop_eq`, `readElemsBoundedLoop_nil` | `propext` |
| `decodeElemsLoop_eq`, `decodeElemsLoop_nil`, `readElemsLoop_eq`, `readElemsLoop_nil`, `instLawfulCodecCountedList`, `decode_encode`, `decode_canonical`, `decode_eq_some_iff`, `decodeElems_length`, `decodeElems_canonical`, `abstractParse_readElems`, `encode_uint8`, `decode_uint8_cons`, `decode_uint8_nil`, `encodeElems_uint8`, `decodeElems_uint8`, `decodeBounded_eq_ok_iff_parts`, `decodeBounded_of_count_error`, `readByte_toOption`, `decodeBoundedBytes_eq`, `decodeBoundedBytes_maxSize_succ`, `decode_maxSize_succ` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecCountedList`, `instLawfulPackedCodecCountedListBytes`, `abstractParse_readByteList`, `decodeBounded_eq_ok_iff`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream file uses no `bv_decide` (C2).

### Transactions

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
Each construction preserves it (`readFixed_agrees`, `readPair_agrees`, `readMap_agrees`, `CountedList.decodeBounded_agrees`).
`Transaction.WithinMaxSize` says that the number of inputs, the number of outputs and the length of each script are at most `0x02000000`.
For all bytes, transactions and remainders:

- `Transaction.readBase_eq_ok_iff`: `readBase bs = ok (tx, rest)` exactly when the codec decodes `bs` as `(tx, rest)` and `tx.WithinMaxSize`.
- `Transaction.readBase_encode`: for every `tx` with `WithinMaxSize`, `readBase (encode tx ++ rest) = ok (tx, rest)`.
- `Transaction.decodeBaseComplete_eq_ok_iff`: the complete reader returns `tx` exactly when `readBase` returns `tx` with no remainder.

`Transaction.txid_val` says that the bytes of the transaction ID are the double SHA-256 digest of the base serialization.
So `txid` never takes the fallback branch of `digestToHash256`.
This says nothing about which values a digest can take.

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

### Transactions: the witness-allowed format

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

### Legacy signature hash

`DogeLib.Transaction.LegacySighash` specifies Core's `SignatureHash` with `SIGVERSION_BASE` (SOURCES.md, D3).
`legacySignatureHashPlan` returns a `LegacyHashPlan`: the fixed digest `legacyOne`, or the bytes to hash with double SHA-256.
The preimage is written field by field after `CTransactionSignatureSerializer`, not by transforming a transaction and serializing it.
The theorems are in `DogeLib.Transaction.Proofs.LegacySighash`, except `readOp_rest_length`, `readPush_op_append` and `readOp_op_append`. Those are in the specification module, because `scanOps` and `findAndDelete` need them to terminate.
For every script code, transaction, input index and hash type:

- `legacySignatureHashPlan_eq_fixedDigest_iff`: the plan is `fixedDigest legacyOne` exactly when `nIn` is at least the number of inputs. With SINGLE, it is also `legacyOne` when `nIn` is at least the number of outputs.
- `legacySignatureHashPlan_eq_hashBytes`: otherwise the plan is `hashBytes (legacyPreimage …)`.
- `legacyPreimage_eq`: the preimage is a body, then the 4 bytes of the hash type. The body depends on the hash type only through its ANYONECANPAY, NONE and SINGLE flags. `HashType.flags_eq_of_and` says that the flags depend only on the bits `0x9f`.
- `scriptCodeBytes_eq_encode`: when no instruction parse failed and no instruction is `OP_CODESEPARATOR`, the script code is written as the ordinary encoding of the script.

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

Not specified: the `SIGVERSION_WITNESS_V0` branch, and `TransactionSignatureChecker::CheckSig`, which takes the hash type from the last byte of a signature.
The caller prepares the script code. Core's interpreter passes the script after the last executed `OP_CODESEPARATOR`, with the signature removed by `FindAndDelete`.
A theorem about a supplied script code says nothing about that preparation (A5).

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readPush_stop` | None |
| `readPush_op_append`, `readOp_op_append`, `readOp_stop_nil` | `propext` |
| `readOp_rest_length`, `readOp_stop_prefix`, `scanOps_prefix`, `scanOps_eq_of_complete`, `legacySignatureHashPlan_eq_fixedDigest_iff`, `legacySignatureHashPlan_eq_hashBytes`, `legacyPreimage_eq`, `HashType.flags_eq_of_and`, `LegacyHashPlan.digest_fixedDigest`, `LegacyHashPlan.digest_hashBytes_val` | `propext`, `Quot.sound` |
| `scriptCodeBytes_eq_encode` | `propext`, `Classical.choice`, `Quot.sound` |

### Legacy signature hash: transformation reference

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

### Compact encoding and difficulty retarget

The `Work` layer specifies Core's `SetCompact`, `GetCompact` and `CalculateDogecoinNextWorkRequired` (SOURCES.md, D6, D12, D13).

For every 256-bit value `a`, `setCompact_getCompact_le` says that decoding the compact encoding of `a` gives at most `a`.
`setCompact_getCompact_flags` says that the decoder reports no sign and no overflow for it.
`getCompact_setCompact_getCompact` says that encoding the decoded value again gives the same compact.
`setCompact_getCompact_of_lt` says that the round trip is exact for `a < 2^23`.
`getCompact_assertions` says that the two `assert` statements of `GetCompact` hold for every value.

`getCompact_setCompact_iff` says that a 32-bit compact survives decoding and encoding again exactly when `GetCompact` produces it.
Core's tests contain compacts that do not survive, and three theorems record them, such as `0x04923456`, which encodes again as `0x04123456`.
`setCompact_fOverflow` says that `SetCompact` sets its overflow flag exactly when the encoded number is at least 2^256.

`modulatedTimespan_mem` says that the clamped timespan lies within the bounds of its regime, for every input.
Four theorems state those bounds for DigiShield and for each height range before it, and two state them for the mainnet parameters.
`retarget_decoded_le_powLimit` says that the new compact target decodes to at most `powLimit`, with neither flag set, for every input.
The input includes old targets above `powLimit` and 256-bit products that wrap.

The signed arithmetic is specified in `Int`, with `Int.tdiv` for the C++ division.
`signedSteps_fit` says that no `int64_t` step overflows when both block times are in `[0, 2^32)` and the target timespan is below 2^61.
`modulatedTimespan_eq_int64` says that Lean's `Int64` operations compute the same timespan on that domain.
Outside it, a C++ signed overflow is undefined behavior, and the `Int` result is a choice of this specification.

The 256-bit product at line 80 is reduced modulo 2^256, as Core reduces it.
`retarget_eq_of_no_wrap` gives the exact result when the product does not wrap.
`no_wrap_of_le_powLimit` and `mainnet_limit` say that it does not wrap for the mainnet parameters when the old target is at most `powLimit`.
`retarget_wrap_example` shows a wrap for an old target of 2^255: a longer actual timespan gives a smaller target.

`validProofOfWorkTarget_iff` supplies the old-target bound from Core's separate target check, as the supplied-hash subsection explains.
The finite-view caller checks coherent heights without establishing target validity.
A claim about a validated chain still assumes that the previous block passed the required check.

The axioms of the 45 theorems in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `mainnet_limit`, `filteredTimespan_rounding` |
| `propext` | `pow256`, `getCompact_setCompact_zero_mantissa`, `getCompact_setCompact_negative`, `setCompact_overflow_example`, `retargetTimespan_pos` |
| `propext`, `Quot.sound` | `byteLength_bounds`, `byteLength_eq`, `byteLength_le`, `and_two_pow_ne_zero`, `sign_bit`, `tdiv_eq`, `timespanLimits_le` |
| `propext`, `Classical.choice`, `Quot.sound` | Every other theorem in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, including `modulatedTimespan_mem`, `retarget_decoded_le_powLimit`, `setCompact_getCompact_le`, `getCompact_setCompact_iff`, `setCompact_fOverflow`, `signedSteps_fit`, `retarget_eq_of_no_wrap` and `no_wrap_of_le_powLimit` |
Some concrete examples use `decide +kernel`, which the kernel checks without compiled code.

These parts are not proved and not specified:

- Scrypt, full header validity and AuxPoW.
  The supplied-hash check is specified separately below.

The word-model refinements below cover multiplication, division, both shifts, bit length and low-64-bit extraction.
They also cover division's comparison, addition, negation and subtraction dependencies.
The correspondence between Core's source and the Lean models remains subject to review (A1).

`lake test` runs the six `get_next_work_*` cases of `dogecoin_tests.cpp` and the 21 steps of `bignum_SetCompact` through the compiled code (B1).
It also runs 17 cases of the `multiply`, `divide` and `methods` tests of `arith_uint256_tests.cpp` (D16) through `mulUInt32`, `div` and `getLow64`.
All 17 cases also run through the corresponding word models.
The word division model also runs the two zero-divisor cases.

### Target validity and supplied-hash proof of work

`Work.ProofOfWork` specifies `CheckProofOfWork` at D17, `src/pow.cpp` lines 115-132.
The inputs are a supplied `Hash256`, a UInt32 compact target and a parameter record, of which only `powLimit` is read.
`hashToArith256` uses the eight little-endian `UintToArith256` word reads.
`hashToArith256_eq` proves equality to the independent radix-256 interpretation for every supplied hash.
The input bytes have Core's internal order, with byte zero least significant for the arithmetic comparison.

`validProofOfWorkTarget_iff` characterizes acceptance of the target check for every compact and parameter record.
The decoded target must be nonzero, at most `powLimit`, and have neither the negative nor overflow flag set.
The check permits noncanonical compacts, such as `0x04000001`, which decodes to 256.
`checkProofOfWork_iff` adds the condition that the supplied hash is at most the target.
`validProofOfWorkTarget_iff_exists_hash` proves that target validity is equivalent to acceptance of some supplied hash, with zero as a witness.
`checkProofOfWork_mono` proves that a smaller hash remains accepted for a fixed compact and parameter record.

`no_wrap_of_validProofOfWorkTarget` supplies the previous-target bound to `no_wrap_of_le_powLimit`.
It retains the numerical hypothesis `powLimit * 4T < 2^256`, where `T` is the target timespan.
`retarget_eq_of_validProofOfWorkTarget` also assumes `T < 2^30`, and gives the existing exact closed form for all retarget inputs.
The mainnet and testnet `*_proofOfWork_bounds` theorems discharge both numerical hypotheses at every UInt32 parameter-selection height.
They cover every selected record, including the AuxPoW eras, by kernel computation on the records after the selection proof.
Their `*_no_wrap_of_validProofOfWorkTarget` and `*_retarget_eq_of_validProofOfWorkTarget` corollaries retain only previous-target validity.

Selection height and retarget height remain explicit independent inputs.

Both regtest records fail the conservative `powLimit * 4T` bound, because their limit is `2^255 - 1`.
`regtestDigishield_modulatedTimespan` proves that the DigiShield record's multiplier is exactly one for every height and actual timespan.
`regtest_no_wrap` and `regtest_retarget_eq` therefore cover every compact at all regtest selection heights from ten, without a target-validity hypothesis.

`legacy_regtest_wrap_example` records a valid compact `0x207fffff`, actual timespan 901 and retarget height one.
The isolated retarget with the legacy regtest record returns `0x1f02467a`, after the product exceeds 2^256.
This wrap is Core's own behavior: `src/dogecoin.cpp` line 80 calls multiplication modulo 2^256 in `src/arith_uint256.cpp` lines 55-65.
DogeLib models that behavior.
The example is reachable through the isolated `CalculateDogecoinNextWorkRequired` API with that record.
The normally selected regtest `GetNextWorkRequired` caller cannot reach a legacy retarget: the legacy record applies below height ten, with interval 14400.

`lake test` runs 20 synthetic branch and boundary cases derived from D17 lines 124-129.
It also requires target validity for all 312 pinned mainnet headers.
Core's `src/test/auxpow_tests.cpp` lines 333-355 mines passing and failing digests at runtime, rather than supplies fixed digest fixtures.
The Lean tests do not compute scrypt or compare with compiled Core.
A supplied-hash check does not establish that the hash is the correct scrypt digest, or that a header or AuxPoW is valid.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Work.Proofs.ProofOfWork` |
| --- | --- |
| None | `mainnet_proofOfWork_bounds` |
| `propext`, `Quot.sound` | `hashToArith256_eq`, `hashToArith256_zero`, `testnet_proofOfWork_bounds` |
| `propext`, `Classical.choice`, `Quot.sound` | All other theorems, including the target characterizations, monotonicity, retarget corollaries and legacy regtest example |

### 256-bit word arithmetic

`ArithUint256.Words` models Core's eight little-endian `UInt32` words as a function from `Fin 8`.
`ofArith_toArith` and `toArith_ofArith` prove that the word and arithmetic representations have inverse conversions.
The model follows the pinned loops in `arith_uint256.cpp` and the `GetLow64()` expression in `arith_uint256.h` (D12, D13).

`mulUInt32_toArith`, `shiftLeft_toArith`, `shiftRight_toArith`, `bits_toArith` and `getLow64_toArith` relate the word models to the arithmetic definitions.
They quantify over every eight-word input.
Multiplication also quantifies over every `UInt32` multiplier, and both shift theorems cover every natural shift.
Core takes an unsigned 32-bit shift, so that domain is included.
The corresponding `*_ofArith` theorems start from every `ArithUint256` value.
`bits_le` bounds the scan's result by 256.

`mul_intermediate_lt` proves that `carry + b32 * pn[i]` fits in 64 bits when the carry fits in 32 bits.
`mul_step` proves that the `UInt64` operations preserve that exact value.
`mulLoop_value` accounts for the full product, including the final carry, for every word count and initial carry below 2^32.
The exported multiplication theorem discards that carry modulo 2^256.

The axioms of the 24 public theorems in `Work.Proofs.ArithUint256Words`, by `#print axioms` with Lean `v4.35.0`:
All theorem names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `eval_lt`, `digits_eval`, `value_lt`, `ofArith_toArith`, `mul_intermediate_lt`, `mul_step`, `mulLoop_value`, `mulUInt32_toArith`, `getLow64_toArith`, `eval_high`, `eval_testBit`, `shiftRight_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `eval_digits`, `toArith_ofArith`, `mulUInt32_ofArith`, `getLow64_ofArith`, `bitScan_eq`, `bitsLoop_eq`, `bits_toArith`, `bits_ofArith`, `bits_le`, `shiftLeft_toArith`, `shiftLeft_ofArith`, `shiftRight_ofArith` |

`lake test` runs the four multiply and three low-64-bit cases from D16 through both representations.
It also runs 1,792 shift cases from D16 lines 159-196 and 30 zero-result cases at shifts of at least 256.
Core's independent byte helpers (D16 lines 125-154) supply expected bytes for the shift cases.
The boundary cases expect zero from Core's word-index guards (D13 lines 30-33 and 47-50).

These theorems relate Lean models, rather than Core's compiled code.
The correspondence between Core's source and each word model remains subject to review (A1).
Core's bit scan tests `pn[pos] & 1 << bits` with a signed `int` literal.
For a 32-bit `int`, N3337 section 5.8 paragraph 2 leaves `1 << 31` undefined (S1).
The model expresses the intended `0x80000000` mask with `testBit`.
No theorem assigns semantics to undefined C++ execution.

### 256-bit word division

`Work.ArithUint256Division` models Core's comparison, addition, negation, subtraction and division loops over the same eight words (D12, D13).
`compareTo_eq` compares their natural values.
`addLoop_value` accounts for the final carry, with an initial carry of at most one.
`add_step` proves that this carry and two words sum exactly in 64 bits.
`add_value`, `neg_value` and `sub_value` give addition, two's-complement negation and subtraction modulo 2^256 for every word input.
Negation follows Core's complement and prefix increment, including every wrapped word.

`divide_toArith` and `divide_ofArith` equate word division with `ArithUint256.div` for every dividend and nonzero divisor.
`divLoop_spec` preserves `num + quotient * original divisor` and leaves `num` below the original divisor.
Its hypotheses require aligned divisor words, the numerator bound at the current shift, and zero low quotient bits.
`divide_value` establishes these hypotheses from Core's bit-length alignment and zero initial quotient.
The bound also proves that the initial left shift and each accepted subtraction preserve the exact natural value.

`divide_eq_none_iff` proves that the model returns `none` exactly when the divisor's value is zero.
Core zeroes its quotient before the zero-divisor test, then throws `uint_error("Division by zero")` (D13 lines 88-92).
The model represents the exception without the operand state after the throw.
Its separate early-return branch returns the zero quotient when the divisor has more bits than the dividend.
The arithmetic `div` requires a nonzero proof and excludes the exception branch.

The quotient bit update uses Core's intended unsigned mask.
Core writes the signed expression `1 << (shift & 31)` (D13 line 100).
At bit 31, the same N3337 5.8 paragraph 2 boundary applies as for `bitScan` (S1).
No theorem assigns semantics to undefined C++ execution.
The correspondence between Core's source and these Lean models remains subject to review (A1).
No proof covers Core's compiled code or Lean's compiler and runtime (B1, B2).

`lake test` runs all ten nonzero divide cases from D16 lines 357-367 through both models.
It also checks `none` for both `BOOST_CHECK_THROW` cases at lines 362 and 368.
The expected quotients and exceptions come from Core's test file.

`readWords_ofFn` proves that the vector copy at each loop boundary preserves every word.
This copy prevents repeated evaluation of function-valued words from earlier loop states.
It adds Lean core vector and array operations to the compiled path (B2).

The axioms of all 24 public theorems in `Work.Proofs.ArithUint256Division`, by `#print axioms` with Lean `v4.35.0`:
All names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `add_step`, `addLoop_value`, `add_value`, `shiftRight_value` |
| `propext`, `Classical.choice`, `Quot.sound` | `readWords_ofFn`, `compareLoop_eq`, `compareTo_eq`, `incrementLoop_digits`, `incrementLoop_value`, `complement_value`, `neg_value`, `sub_value`, `sub_value_of_le`, `shiftLeft_value`, `quotient_mask`, `quotient_or_value`, `quotient_add_value`, `divLoop_spec`, `bits_eq_zero_iff`, `bits_value_bounds`, `divide_eq_none_iff`, `divide_value`, `divide_toArith`, `divide_ofArith` |

### Remaining word paths of the retarget

`Work.ArithUint256Compact` models Core's uint64 constructor, assignment, `SetCompact` and `GetCompact` over eight words (D12, D13).
`Words.ofUInt64_value` proves that construction stores every input exactly.
`ofUInt64_toArith` and `assignUInt64_toArith` equate construction and assignment with the arithmetic embedding, for every uint64 input and previous word array.
`assignUInt64` describes the explicit base-class overload at D12 lines 88-95, which sets every word.

The implicit `arith_uint256` copy assignment hides this base overload.
Thus `*this = nWord` in `SetCompact` and `num = 0x80` in D16 construct a temporary through D12 line 257, then copy it.
The temporary uses the uint64 constructor at D12 lines 51-57, and the base copy assignment copies its words at lines 44-49.

`Words.setCompact_toArith` equates the complete decoder result with `ArithUint256.setCompact` for every compact input.
The conclusion includes the magnitude and both flags.
For small exponents, both flags read the mantissa after the right shift, as Core does.
`Words.getCompact_toArith` equates the word encoder with `ArithUint256.getCompact` for every word array and both sign arguments.
These models use the proved word shifts, bit scan and low-64-bit extraction.

`Work.ArithUint256Bytes` gives an independent radix-256 interpretation of a 32-byte target.
`Words.uintToArith256_toArith` proves that eight grouped `ReadLE32` reads give that interpretation, for every 32-byte input (D13, D37).
`Words.readLE32_toNat` proves that each group fits exactly in its word.
The portable meaning of Core's `memcpy` and `le32toh` remains a source-review boundary.
Memory layout and Core's compiled code are not proved.

`targetBytesOfHex` models Core's backwards nibble scan for `0x` followed by exactly 64 ASCII hexadecimal digits (D11).
It rejects every other format.
It does not specify Core's general whitespace, prefix and truncation behavior.

Seven `*_powLimit_literal` theorems start from Core's literal strings at D14 lines 88, 248 and 392.
They prove the resulting `Words.toArith` interpretations equal the existing network parameter limits, including inherited DigiShield and AuxPoW limits.
The kernel checks these concrete computations with `decide +kernel`.
The literals come from Core, rather than from the arithmetic values under test.
The hex parser is checked only on the three concrete network strings, with two distinct spellings.

`calculateDogecoinNextWorkRequiredWords_eq` proves that word retarget returns `some` of the arithmetic target for every existing parameter record and input.
The executable model preserves division's `Option`, and the proof uses the positive-timespan field to exclude the exception.
It includes the divisor constructor, compact operations, multiplication, division and word comparison with the limit.
`calculateDogecoinNextWorkRequiredWithWords_eq` covers every explicit word limit, with that limit's arithmetic interpretation.
`calculateDogecoinNextWorkRequiredBytes_eq` also covers every 32-byte limit, through `UintToArith256` and its independent interpretation.

`retarget_mainnet_literal`, `retarget_testnet_literal` and `retarget_regtest_literal` connect each literal directly to the byte retarget.
At every network selection height, each corollary exhibits parsed bytes and proves retarget equality for every retarget input.
These corollaries cover all ten tree records, including the records that share work fields.

The signed timespan calculation reuses Core's lines 41-74 through `Work.Retarget`.
The equality of the Lean retargets has no additional signed-arithmetic hypothesis.
Agreement with Core's signed execution retains the existing block-time and target-timespan bounds from `signedSteps_fit` and `modulatedTimespan_eq_int64`.
The inherited bit-scan and division-mask models retain their intended-unsigned-mask boundary under S1.
The models' correspondence to Core's source remains subject to review (A1), and compiler and runtime trust remains (B1, B2).

The retarget materialises intermediate words with the vector copy from the division model.
`readWords_ofFn` proves that each copy preserves the words.
The copy avoids repeated computation of earlier word operations and retains the Lean core array execution boundary (B2).

`lake test` runs all 21 D16 compact cases through both arithmetic and word models, including both flags.
The derived assignment case at line 490 exercises uint64 construction, followed by a copy whose value is unchanged.
All six D7 retarget cases run through the arithmetic function and both word entry points.
The byte entry point starts from Core's mainnet hexadecimal limit.
These expectations come from Core's tests and are not a comparison with Core's compiled code.

The axioms of all 22 public theorems in `Work.Proofs.ArithUint256Compact`, `Work.Proofs.ArithUint256Bytes` and `Work.Proofs.RetargetWords`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `Words.ofUInt64_value`, `Words.ofUInt64_toArith`, `Words.assignUInt64_toArith`, `Words.readLE32_toNat`, `Words.uintToArith256_value`, `Words.uintToArith256_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `Words.setCompact_toArith`, `Words.getCompact_toArith`, all seven `*_powLimit_literal` theorems, `Words.compareTo_gt`, `calculateDogecoinNextWorkRequiredWithWords_eq`, `calculateDogecoinNextWorkRequiredWords_eq`, `calculateDogecoinNextWorkRequiredBytes_eq`, `retarget_mainnet_literal`, `retarget_testnet_literal`, `retarget_regtest_literal` |

The `Words` and literal theorem names are in `DogeLib.Work.ArithUint256`.
The retarget and network corollary names are in `DogeLib.Work`.

### Next-work selection and work parameters

`DogeLib.Work.Consensus` projects the work fields from Core's parameter records (D14, D15).
`ConsensusTree.getConsensus` follows the left and right search links and checks the right candidate's effective height before accepting it.
The three `getConsensus_*` theorems give the projected work fields at every UInt32 target height.
Mainnet changes at 145000, testnet at 145000 and 157500, and regtest at 10.
AuxPoW records retain separate effective heights but repeat these fields.
The projection makes no claim about the other consensus fields.

`DogeLib.Work.NextWork` specifies the caller of the retarget (D17, lines 32-88).
`nextWorkRequired` selects the candidate height's parameters, as validation and mining do (D33, D34).
The local interval becomes one at previous height 145000.
`retargetInterval_no_recovery` proves that the non-retarget branch cannot execute from that previous height, for every parameter record.

The recovery loop uses the record's interval instead of that local interval.
`retargetInterval_eq_record_of_nonretarget` proves that the local and record intervals agree whenever the caller is off a retarget boundary, for every record.
Recovery requires that condition, so no input can reach recovery with different intervals.
At previous height 144999, the candidate's DigiShield record already has interval one.

The all-block minimum rule checks previous height at least 157500 and a strict delay greater than twice the spacing (D6, lines 26-39).
Selected testnet parameters permit minimum difficulty from candidate height 157500, so that candidate still retargets and candidate 157501 can use the delay rule.
This caller ignores `fPowNoRetargeting`, including on regtest.
It also ignores `fPowAllowDigishieldMinDifficultyBlocks`.

The view is a newest-first list of explicit height, UInt32 time and compact target fields.
The adapter checks consecutive heights and bounds every height below 2147483647.
The last entry may be above genesis, so the view need not contain all history.
A walk that still needs a predecessor returns `missingAncestor` at a truncated suffix.
Core's corresponding ancestor assertion aborts when the required index is absent.

The model omits skip links and uses the predecessor path for ancestor lookup (D35).
No theorem relates Core's skip-pointer traversal to that path.

`blocksToGoBack_le` excludes the negative-first-height assertion when the interval is positive and divides the next height.
The adapter checks `zeroInterval` before the retarget boundary and underflow checks.
Thus `firstHeightUnderflow` is unreachable for every validated view: a positive interval at a retarget satisfies `blocksToGoBack_le`.
Malformed-view errors are separate from both assertion cases.
These errors are adapter contracts, not Core rejection codes.
The UInt32 times widen to Int, and the fixed network spacings of 1 or 60 keep the delay arithmetic within int64_t.

`getNextWorkRequired_genesis` proves the null-tip result for every record and candidate time.
`getNextWorkRequired_minDifficulty` proves the minimum result when validation succeeds and the all-block minimum condition holds.
`recoverLastNonMinDifficulty_mem` proves that a successful recovery returns a supplied entry's compact, without a header-validity hypothesis.
These caller claims do not establish target validity.
The separate target-check theorem supplies the old-target bound when target validity is assumed.

`lake test` includes source-derived network and branch examples and all six D7 retarget answers through synthetic contiguous views.
The intermediate entries are synthetic, not historical headers.
These examples do not run Core or prove equality to its compiled caller.

`lake test` also reads 312 real mainnet headers at heights 144719–145030 from a public Electrum server.
The [fixture README](tests/work/mainnet-headers/README.md) records the source, date and exact request.
The test hashes all headers with compiled `Sha256d`, checks all predecessor links and requires Core's checkpoint hash at 145000 (D9).
It compares `nextWorkRequired .mainnet` with 278 difficulty copies, the interval-240 retarget at 144960 and 31 DigiShield retargets at 145000–145030.
The substantive retarget evidence is 144960 plus those 31 DigiShield blocks.

The first header supplies context.
Retarget 144720 lacks an ancestor, so the test requires `missingAncestor` there.
The test also requires target validity for all 312 headers with the selected mainnet parameters.
Those finite checks establish the old-target bound for these inputs, but neither proof of work nor AuxPoW validity.
They do not run Core or prove equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `getConsensus_mainnet`, `getConsensus_regtest` |
| `propext` | `retargetInterval_after`, `blocksToGoBack_first`, `blocksToGoBack_later`, `recoverLastNonMinDifficulty_mem`, `retargetInterval_no_recovery` |
| `propext`, `Quot.sound` | `getConsensus_testnet`, `retargetInterval_before`, `blocksToGoBack_le`, `retargetInterval_eq_record_of_nonretarget` |
| `propext`, `Classical.choice`, `Quot.sound` | `getNextWorkRequired_genesis`, `getNextWorkRequired_minDifficulty` |

### What cannot be proved yet

A `partial` definition, an `opaque` constant, or a definition that unfolds to one cannot be evaluated by the kernel.
CONTRIBUTING.md says to avoid `partial` definitions in the specification library (*Specification code*), and requires explicit treatment of `opaque` (*Proofs*).
Each such definition that remains is listed here with its reason.

## Gap A: does the definition say what Dogecoin does and what the client needs?

### A1. A wrong definition

A definition can differ from Dogecoin's behavior while every theorem about it holds, because the theorems are proved about the definition, not about Dogecoin Core.
Three things guard against that.
Each definition is named and shaped after its source in `SOURCES.md`, so that a reader can compare them line by line.
Fixtures come from pinned Core tests, primary specifications or documented historical data, never from the implementation under test.
Core comparisons run the compiled oracle against the pinned Core revision.

The source registry exists. The fixtures are listed per operation in the *Comparison* column of [COVERAGE.md](COVERAGE.md), and each records its provenance.
The Core comparison runs the compiled oracle and Core's own code at the pin on the same requests, for the operations of the oracle ([docs/oracle.md](docs/oracle.md#the-core-harness)).
It shows agreement on the requests it sends, and nothing about other inputs.

The real mainnet headers test next-work selection across DigiShield activation against historical `nBits` values.
The next-work subsection states the exact branch counts.
Hash links connect headers through 145000 to the pinned Core checkpoint, subject to the hash commitment assumption.
The checkpoint does not authenticate later headers, whose provenance still relies on the public source.
The fixture digest pins all bytes, and the compiled test checks links through 145030.
Neither check establishes proof of work, AuxPoW validity or full header validity.

The multiplication, shift, bit-length and low-64-bit models have arithmetic equivalence proofs, as the *256-bit word arithmetic* subsection states.
A reader still checks their correspondence to Core's source.
The division, comparison and subtraction models also have arithmetic equivalence proofs, as the *256-bit word division* subsection states.
The word division model represents Core's zero-divisor exception.
The arithmetic definition takes a nonzero proof.

The compact, uint64 construction and byte conversion models have arithmetic equivalence proofs, as the *Remaining word paths of the retarget* subsection states.
The composed word retarget uses these models and the proved `CompareTo` model.
Its equality with the arithmetic specification holds for every existing input.
Network powLimit proofs start from Core's hexadecimal literals, through the restricted hex parser and word conversion.
A reader still checks the models against Core's source.

A Dogecoin rule can differ from the Bitcoin rule it descends from.
A definition or proof adopted from btc-verified is evidence to investigate, not a compatibility proof for Dogecoin.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
`legacySignatureHashPlan_eq_reference` equates the field-by-field production plan with the transaction-transformation reference for every input index and hash type.
It requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
The transformation-reference subsection states these hypotheses and explains the short-push difference.
Whatever those hypotheses leave unproved is part of what a reader trusts.

`no_wrap_of_validProofOfWorkTarget` discharges the old-target bound of `no_wrap_of_le_powLimit` from Core's target-validity predicate.
Its numerical bound holds for every selected mainnet and testnet record.
Regtest DigiShield uses a separate exact-multiplier argument, and legacy regtest permits wrap in the isolated retarget.
The supplied-hash subsection states the network corollaries and the caller boundary.

A chain-level application still assumes that the previous block passed Core's check with the relevant `powLimit`.
The header path supplies `GetConsensus(0)` to `CheckAuxPowProofOfWork` (D33, `src/validation.cpp` line 2933).
That function passes the record to `CheckProofOfWork` (D6, `src/dogecoin.cpp` lines 107 and 118).
Every record within a network has the same `powLimit` (D14, the record copies at lines 126-136, 282-300 and 425-432).

The chain-level application also requires that the supplied hash is the correct scrypt digest.
No theorem here establishes that digest computation, AuxPoW validity or full header validity.

### A3. Side channels

DogeLib makes no constant-time claim.
The specification is a reference for behavior, not for timing.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
DogeLib has no security theorem, so it has no idealisation.
Equality of two hash plans needs no assumption about the hash function.
A claim that different preimages give different digests needs a named collision hypothesis or a computational model.

### A5. Protocol context

Some rules apply only under a serialization mode, a network, an activation state or a historical era.
A definition that leaves out its context can be right in one era and wrong in another.
The first operations, base codecs and legacy signature hashing, have few context dependencies.

The transaction readers model two serialization modes of Core's reader: base mode and the witness-allowed format.
The witness-allowed format models serialization only.
Core rejects blocks with witness data on main and test at the pin.
The witness-format subsection records the separate script-verification and commitment mechanisms (D36), with their deployment parameters (D9).
No DogeLib theorem establishes consensus acceptance of witness data.

The legacy signature hash is the `SIGVERSION_BASE` mode of `SignatureHash`, and its script code is an input: the interpreter's preparation of it is not specified.

The work-parameter search covers each network and height, and the next-work wrapper selects the candidate height.
The caller's hard-coded activation checks use the previous height, as the next-work subsection explains.
Script and ledger work will need explicit context.

## Gap B: does the code that runs match the definitions?

DogeLib's theorems are about the Lean definitions, and everything between them and the running code is trusted.
A refinement proof relates the extracted functional Lean model to the specification.
Extraction and compiled Rust remain trusted boundaries (B6).

```text
 Dogecoin behavior --A-- Lean definition == proof == theorem
                              |
                              B
                              |
            compiled oracle, extracted Rust --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.
Known answers and Core comparisons through the compiled code test it end to end, only on the inputs they cover.
`lake test` runs the 129 NIST CAVP SHA-256 vectors through the compiled `hash`.

### B2. Lean core's own implementations

Lean core implements some `Array`, `ByteArray` and `Nat` operations with `@[implemented_by]` or `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Lean core is a declared trusted baseline.
The packed encoders and decoders run two `@[extern]` operations of core: `ByteArray.push` and `ByteArray.get`.
`ByteSlice.toList` and the tests that call it also run `ByteArray.copySlice`, through `ByteArray.extract`.
The packed decoders of byte lists and of `Bytes n`, `instPackedCodecCountedListBytes` and `instPackedCodecBytes`, call `ByteSlice.toList` to read their bytes, so they run `ByteArray.copySlice` too.

The base-mode slice reader uses `ByteArray.size` (`lean_sarray_size`) for the bounds checks of `ByteSlice.slice` and `ByteArray.toList`.
Its fixed integer reads use `ByteArray.get` (`lean_byte_array_fget`) through `ByteSlice.get`.
Its hash and script reads use `ByteArray.copySlice` (`lean_byte_array_copy_slice`) through `ByteArray.extract` and `ByteSlice.toList`.
`ByteArray.toList` also calls `ByteArray.get!` (`lean_byte_array_get`).

`ByteSlice.size` subtracts its offsets, and `ByteSlice.take` and `ByteSlice.drop` use `ByteSlice.slice` to construct views.
Those slice operations have no separate `@[extern]` or `@[implemented_by]` body in Lean `v4.35.0`.
Only conversion of consumed hash or script bytes to a list copies bytes in this reader.

### B3. Native code during elaboration

If a library sets `precompileModules := true`, then `#eval` or an evaluating tactic in a module that imports it runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The oracle and foreign boundaries

The oracle reads fixture records and writes results through IO.
That adapter is outside the specification library, and no theorem covers it.

The oracle is `dogelib-oracle`, in the `Exports` library ([docs/oracle.md](docs/oracle.md)).
The adapter calls specification functions and converts their arguments and results:

- Lean core's `Json.parse` reads each request, and `Json.compress` writes each response. Both are trusted as Lean core is (B2).
- The adapter's own code converts hexadecimal text to bytes and back, JSON numbers and decimal strings to integers, and the specification's errors to JSON objects.
  The tests check these conversions at their boundaries, against expected values from Core's files, Core's source and Python's `hashlib`.
- The loop over standard input uses `repeat`, which Lean core defines with `partial`. `lake exe check-decls` exempts the `Exports` modules from its check of reachable opaque constants, and checks their axioms and their own declarations.

The base operations and the transaction argument of `sighash.legacy` convert hex bytes to a slice once.
`tx.read_base` uses `Transaction.readBaseSlice`.
`tx.decode_base` and `sighash.legacy` use `Transaction.decodeBaseCompleteSlice`.
`Transaction.abstractRead_readBaseSlice` preserves errors, fields and remainder bytes for every slice.
`Transaction.decodeBaseCompleteSlice_eq` preserves the complete reader's result, including errors and trailing-byte counts, for every slice.
The list readers remain the specification.

`ByteSlice.toList_ofByteArray` identifies the bytes in each whole-array slice that the adapter constructs with `ByteSlice.ofByteArray`.
These equalities do not cover the hex or JSON conversions.
The witness operations use list readers.

The witness operations convert `WitnessTransaction` stacks to arrays of item hex strings.
They expose `hasWitness`, witness-allowed serialization, the transaction ID and the witness hash.
No theorem covers these JSON conversions.
Core comparisons check these fields, consumption and errors on the recorded requests only.

The work operations convert target magnitudes in most-significant-byte-first hexadecimal and preserve compact values as UInt32 fields.
They select network parameters and pass UInt32 times to the retarget arithmetic.
`work.next` converts a newest-first JSON array to the specification's finite view.
Its `work_view` errors are adapter errors, not Core consensus rejection codes.
The harness checks caller preconditions before it invokes Core and excludes those errors from the comparison.
Its skip-height guard leaves unavailable skip destinations null, so Core uses predecessor links instead.

No theorem covers these JSON conversions, the harness guard or correspondence to Core's traversal.

A wrong conversion could make the oracle and Core disagree, or agree, for a reason outside the specification.

The Core harness, `harness/core/core_oracle.cpp`, is the other side of the comparison ([docs/oracle.md](docs/oracle.md#the-core-harness)).
A user of the comparison trusts these parts of it:

- Core's libraries at the pin, compiled by the compiler of the machine that runs the comparison: GCC 13 in CI, on `ubuntu-24.04`.
  Core v1.14.9 was released for older compilers.
  The build script uses `-O2 -ffunction-sections -fdata-sections`, and Core's configure selects C++11.
  GNU ld discards unused sections with `--gc-sections`.
- The harness's own code. It converts hexadecimal text and JSON numbers to Core's arguments, writes Core's results as JSON, and maps four exception messages to read errors.
  Any other exception from Core stops the harness, so it cannot pass as a result.
- The `plan` label of `sighash.legacy`. The harness computes it from Core's conditions instead of observing it. It stops if the label is `fixed_digest` and Core's digest is not the value one.
- The comparator, `scripts/compare_core.py`.
  Its self-test, `scripts/test_compare_core.py`, requires two passing controls and 39 mutations that each fail with the code they target.
- For `sighash.legacy`, the oracle's preimage is checked by hashing it, not byte by byte: Core does not expose its preimage.

Both programs could be wrong in the same way on an input that the comparison does not send.

Any later foreign boundary, such as a C or Rust binding, is listed here with its size and its error handling.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust. The code that runs is still not the definition a reader reads.

The `DogeLib`, `Proofs` and `Refinement` libraries have no `@[extern]`, `@[implemented_by]` or `@[csimp]` declarations, by `lake exe check-decls`.
Their safe declarations depend on at most `propext`, `Classical.choice` and `Quot.sound`.
The fixtures in `scripts/CheckDeclsTest` contain them on purpose, to test the check, and no library imports them.

| Declaration | Kind | Proof-backed | Justification |
| --- | --- | --- | --- |

### B6. Extraction and the Rust toolchain

A refinement theorem about extracted Rust is about the Lean model that Charon and Aeneas produce.
It trusts the extraction, any manually modeled dependency, and the Rust compiler and runtime.
The extracted model is an implementation artifact.
It never becomes the specification.

`Refinement/Rust/src/lib.rs` implements the bounded CompactSize reader.
Charon and Aeneas at the pins in SOURCES.md produce `Refinement/Refinement/Rust/Generated/DogelibCompactsize.lean`.
`Refinement/Rust/regenerate.sh --check` compares a fresh extraction with the committed model.
The refinement theorem is about that Lean model, not a proof of the extractors or compiled Rust.
The Rust compiler, standard-library models, extraction tools and runtime remain trusted.

The native example `Refinement/Rust/examples/compactsize_oracle.rs` calls the public Rust reader through a JSON Lines adapter.
`scripts/compare_core.py --rust-compactsize PATH` compares it with the oracle and Core at the pinned revision.
The three programs agree on 404 CompactSize reads: seven existing fixtures and 397 generated boundary, truncation, non-canonical and suffix cases.
The comparison preserves errors, values, consumed counts and remainders on these inputs.

The comparison provides evidence about the compiled binary on these inputs.
No theorem covers the compiled binary or its JSON adapter.
The adapter's `serde_json` development dependency remains outside the extracted library model.

Aeneas represents each input byte with an eight-bit vector and each decoded value with a 64-bit vector.
The abstraction maps those vectors directly to Lean `UInt8` and `UInt64`.
Aeneas slices carry a proof that their length fits Rust `usize`.
This length bound limits the input representation, not the acceptance behavior of the reader.

Rust usize is modeled through Lean core's opaque platform word size.
The refinement holds on both 32- and 64-bit platforms.
The proof does not case on that word size, and it assumes neither 32 nor 64 separately.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set. A theorem may use fewer.

`lake exe check-decls` checks the transitive axiom dependencies of safe declarations under `DogeLib` and `Refinement`, including private proof bodies.
It rejects `sorryAx` even when an unfinished proof comes from an imported module outside that scope.
Unsafe declarations are reported separately.
Detection does not require attribution to a declaration that uses the axiom directly.
It does not check the kernel, and it does not show that the axioms are consistent.

The named platform-size exception permits exactly `System.Platform.getNumBits` as a reachable opaque from `Refinement` modules.
This Lean core parameter supplies the word size of Rust `usize`.
The exception does not permit an opaque declaration in either library, another reachable opaque, or this parameter in a `DogeLib` specification definition.
The self-test rejects those cases, imported Aeneas axioms and native proofs.
The allowed axioms remain the same three standard axioms.

Aeneas and Mathlib belong only to the separate refinement package and remain outside the checked module namespaces.
The checker still follows their transitive axiom dependencies at each in-scope use.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

CONTRIBUTING.md does not allow these tactics (*Proofs*).
btc-verified allows the axioms that `bv_decide` records, and its `CompactSize.decode_encode` and `encode_head` use `bv_decide`.
A proof adopted from btc-verified has those steps replaced by proofs the kernel checks alone (design record 0002, section 5).
In `DogeLib.Serialization.Proofs.CompactSize`, `toUInt8_lt_fd` and `toUInt8_ne_zero` replace them.

No theorem in the `DogeLib`, `Proofs` and `Refinement` libraries uses them, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` use them on purpose.

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
An independent checker that replays the environment, such as `lean4checker`, would catch it, but none runs yet.

The default declaration check loads `DogeLib`, `DogeLib.Proofs`, `DogeLib.Exports` and `Refinement` with their private proof bodies.
It requires every `.lean` source under `DogeLib/` and `Refinement/Refinement/`, plus their library roots, to appear in that imported environment.
An unreachable module fails the check, including a leaf omitted from its layer root.
This reachability check does not replay kernel checks or detect a metaprogram that bypassed them.
The default imports, checked namespaces and file inventory include the extracted model and its proof.

The default check fails if the separate refinement package is missing, unbuilt or cannot load every requested module.
`--skip-refinement` checks only DogeLib and prints `Refinement NOT checked` in the summary.
Production CI never uses this flag.

## Gap D: does the use of DogeLib hold together?

### D1. Misuse by a client

A correct definition gives a wrong answer when a client calls it outside its input domain.
A prefix decoder returns a remainder, and a client that ignores it accepts trailing bytes.
Each public operation documents its input domain, its failure behavior and whether it consumes the whole input.

### D2. Dependency changes

A change to a pinned dependency can change a definition or a proof that DogeLib relies on.
`SOURCES.md` records the pins, and a pin changes only in a reviewed change of its own.
The root DogeLib package has no Lake dependencies.
The separate package under `Refinement/` requires DogeLib and the pinned Aeneas backend, which brings Mathlib.
[ARCHITECTURE.md](ARCHITECTURE.md#lake-libraries) explains the import boundaries, and [BUILDING.md](BUILDING.md#build-and-check) gives the build sequence.

### D3. Wrong fixtures

A fixture with a wrong expected value makes a wrong implementation pass.
Each fixture records its provenance, and a test runner compares results with the committed expectations rather than overwriting them.
