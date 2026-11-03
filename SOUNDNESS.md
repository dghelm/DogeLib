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
| A1 | A definition does not match the pinned Dogecoin behavior | Source mapping in `SOURCES.md`, by review only. SHA-256 has a proof against a FIPS 180-4 model, and NIST CAVP known answers. Known answers from Core's genesis data test the integer codecs. Core's own test cases are known answers for CompactSize, the compact encoding and the difficulty retarget. The scripts of the genesis coinbase are known answers for counted lists. No comparison against a running Core yet. | P R I F |
| A2 | A theorem holds only under a hypothesis | Policy: each conditional theorem lists its hypotheses here and in `COVERAGE.md` | P I |
| A3 | Timing reveals secret data | None: no constant-time claim | R I |
| A4 | A security theorem idealises a primitive | None: no security theorem yet | P |
| A5 | A rule depends on a protocol context that the definition does not model | Policy: each operation records its mode, network and era in `SOURCES.md` | P R I F |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | `lake test` runs the NIST CAVP SHA-256 vectors, Core's compact-encoding and retarget test cases, and the codec known answers through the compiled code | R |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R |
| B3 | Elaboration runs native code | None yet | P |
| B4 | The oracle's IO adapter or a foreign boundary is wrong | None yet | R F |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R |
| B6 | Extraction or the Rust toolchain is wrong | None: no extraction yet | I |
| C1 | The Lean kernel or its axioms are unsound | None | P I |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any use | P I |
| C3 | A declaration reached the environment unchecked | None | P I |
| D1 | A client misuses an operation, such as a prefix decoder where complete consumption is required | Policy: each public operation documents its input domain and consumption contract | R I |
| D2 | A dependency changes | Pins in `SOURCES.md` and `lean-toolchain`. The package has no Lake dependencies. | P R I |
| D3 | The fixtures are wrong | Each fixture records its provenance. The NIST CAVP files are pinned by digest, and CI checks the pin. Core's test cases are copied into `tests/KnownAnswers.lean` with their file and line. | F |

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

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `maxSize_toNat` | None |
| `encode_maxSize_succ`, `encodeFixedWidth_length` | `propext` |
| `lawfulCodec`, `decode_encode`, `decode_canonical`, `encode_length_le`, `encode_head`, `toUInt8_lt_fd`, `toUInt8_ne_zero`, `toList_encodeInto`, `readCanonical_toOption`, `decodeBounded_eq_error_tooLarge_iff`, `decode_maxSize_succ`, `decodeBounded_maxSize_succ`, `decodeBounded_encode_maxSize_succ` | `propext`, `Quot.sound` |
| `lawfulPackedCodec`, `abstractParse_decodeSlice`, `decode_eq_some_iff`, `decodeBounded_eq_ok_iff_decode`, `decodeBounded_eq_ok_iff_valid`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

Upstream proves two small facts in `decode_encode` and `encode_head` with `bv_decide`.
Here `toUInt8_lt_fd` and `toUInt8_ne_zero` prove them: each converts the bytes to natural numbers and closes the goal with `omega` (C2).
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

The element-at-a-time readers recurse once for each element.
In one run of `lake env lean --run`, the generic decoder of a byte list overflowed the stack at 4,000,000 elements, below `MAX_SIZE`.
The block readers of bytes read 30,000,000 bytes in the same run.
No theorem covers stack use. Issue #19 tracks readers whose stack use does not grow with the count.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_toOption` | None |
| `ofList?_eq_some`, `val_of_ofList?`, `decodeElems_encodeElems`, `toList_pushElems`, `readElemsBounded_readByte` | `propext` |
| `instLawfulCodecCountedList`, `decode_encode`, `decode_canonical`, `decode_eq_some_iff`, `decodeElems_length`, `decodeElems_canonical`, `abstractParse_readElems`, `encode_uint8`, `decode_uint8_cons`, `decode_uint8_nil`, `encodeElems_uint8`, `decodeElems_uint8`, `decodeBounded_eq_ok_iff_parts`, `decodeBounded_of_count_error`, `readByte_toOption`, `decodeBoundedBytes_eq`, `decodeBoundedBytes_maxSize_succ`, `decode_maxSize_succ` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecCountedList`, `instLawfulPackedCodecCountedListBytes`, `abstractParse_readByteList`, `decodeBounded_eq_ok_iff`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream file uses no `bv_decide` (C2).

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
No theorem shows that a valid chain never reaches such a target, because block-index walking and header validity are not specified.

The axioms of the 45 theorems of the layer, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `mainnet_limit`, `filteredTimespan_rounding` |
| `propext` | `pow256`, `getCompact_setCompact_zero_mantissa`, `getCompact_setCompact_negative`, `setCompact_overflow_example`, `retargetTimespan_pos` |
| `propext`, `Quot.sound` | `byteLength_bounds`, `byteLength_eq`, `byteLength_le`, `and_two_pow_ne_zero`, `sign_bit`, `tdiv_eq`, `timespanLimits_le` |
| `propext`, `Classical.choice`, `Quot.sound` | every other theorem of the layer, including `modulatedTimespan_mem`, `retarget_decoded_le_powLimit`, `setCompact_getCompact_le`, `getCompact_setCompact_iff`, `setCompact_fOverflow`, `signedSteps_fit`, `retarget_eq_of_no_wrap` and `no_wrap_of_le_powLimit` |
Some concrete examples use `decide +kernel`, which the kernel checks without compiled code.

These parts are not proved and not specified:

- Which parameters apply at which height, `Consensus::Params::GetConsensus`.
- When a retarget happens and which first block it uses, `GetNextWorkRequired`, and its walk over `CBlockIndex`.
- The minimum-difficulty rules of the test networks.
- Header validity, including `CheckProofOfWork`, and AuxPoW.

The relation between Core's word-by-word loops in `arith_uint256.cpp` and the arithmetic results that the definitions state is checked by review (A1).
`lake test` runs the six `get_next_work_*` cases of `dogecoin_tests.cpp` and the 21 steps of `bignum_SetCompact` through the compiled code (B1).

### What cannot be proved yet

A `partial` definition, an `opaque` constant, or a definition that unfolds to one cannot be evaluated by the kernel.
CONTRIBUTING.md says to avoid `partial` definitions in the specification library (*Specification code*), and requires explicit treatment of `opaque` (*Proofs*).
Each such definition that remains is listed here with its reason.

## Gap A: does the definition say what Dogecoin does and what the client needs?

### A1. A wrong definition

A definition can differ from Dogecoin's behavior while every theorem about it holds, because the theorems are proved about the definition, not about Dogecoin Core.
Three things guard against that, once they exist.
Each definition is named and shaped after its source in `SOURCES.md`, so that a reader can compare them line by line.
Fixtures come from pinned Core tests, primary specifications or documented historical data, never from the implementation under test.
Core comparisons run the compiled oracle against the pinned Core revision.
The source registry exists. The fixtures are listed per operation in the *Comparison* column of [COVERAGE.md](COVERAGE.md), and each records its provenance. No Core comparison exists yet.

A Dogecoin rule can differ from the Bitcoin rule it descends from.
A definition or proof adopted from btc-verified is evidence to investigate, not a compatibility proof for Dogecoin.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
The first planned one is the signature-preimage equivalence, which may require fully parsed script code (ROADMAP.md, milestone C).
Whatever those hypotheses leave unproved is part of what a reader trusts.

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
Script, ledger and activation work will need explicit context.

## Gap B: does the code that runs match the definitions?

DogeLib's theorems are about the Lean definitions, and everything between them and the running code is trusted.
A proof about extracted Rust narrows that gap for the extracted code only.

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

### B3. Native code during elaboration

If a library sets `precompileModules := true`, then `#eval` or an evaluating tactic in a module that imports it runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The oracle and foreign boundaries

The oracle reads fixture records and writes results through IO.
That adapter is outside the specification library, and no theorem covers it.
Any later foreign boundary, such as a C or Rust binding, is listed here with its size and its error handling.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust. The code that runs is still not the definition a reader reads.

The `DogeLib` and `Proofs` libraries have none of the three, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` contain them on purpose, to test the check, and no library imports them.

| Declaration | Kind | Proof-backed | Justification |
| --- | --- | --- | --- |

### B6. Extraction and the Rust toolchain

A refinement theorem about extracted Rust is about the Lean model that Charon and Aeneas produce.
It trusts the extraction, any manually modeled dependency, and the Rust compiler and runtime.
The extracted model is an implementation artifact. It never becomes the specification.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set. A theorem may use fewer.

`lake exe check-decls` checks dependencies: no declaration may depend on an axiom outside that set.
It does not check the kernel, and it does not show that the axioms are consistent.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

CONTRIBUTING.md does not allow these tactics (*Proofs*).
btc-verified allows the axioms that `bv_decide` records, and its `CompactSize.decode_encode` and `encode_head` use `bv_decide`.
A proof adopted from btc-verified has those steps replaced by proofs the kernel checks alone (design record 0002, section 5).
In `DogeLib.Serialization.Proofs.CompactSize`, `toUInt8_lt_fd` and `toUInt8_ne_zero` replace them.

No theorem in the `DogeLib` and `Proofs` libraries uses them, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` use them on purpose.

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
An independent checker that replays the environment, such as `lean4checker`, would catch it, but none runs yet.

## Gap D: does the use of DogeLib hold together?

### D1. Misuse by a client

A correct definition gives a wrong answer when a client calls it outside its input domain.
A prefix decoder returns a remainder, and a client that ignores it accepts trailing bytes.
Each public operation documents its input domain, its failure behavior and whether it consumes the whole input.

### D2. Dependency changes

A change to a pinned dependency can change a definition or a proof that DogeLib relies on.
`SOURCES.md` records the pins, and a pin changes only in a reviewed change of its own.

### D3. Wrong fixtures

A fixture with a wrong expected value makes a wrong implementation pass.
Each fixture records its provenance, and a test runner compares results with the committed expectations rather than overwriting them.
