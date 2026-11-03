module

/-!
# `Serialization.Codec`

Codecs: an encoder to bytes and a prefix decoder from bytes, over `List UInt8`.

A *codec* for a type `α` has two operations:

- `encode : α → List UInt8` writes a value as bytes.
- `decode : List UInt8 → Option (α × List UInt8)` reads a value from the start of the bytes.
  It returns the value and the remainder, the bytes after the ones it consumed, or `none` when it rejects the input.

Because `decode` returns the remainder, codecs compose: the decoder of a pair decodes its first component, then decodes its second component from the remainder.
This module defines these codecs:

- `instCodecProd`: the pair of two codecs, one encoding after the other.
- `Codec.ofEquiv`: the codec of a type carried to another type by a pair of conversion functions.
- `encodeBitVecLE` and `decodeBitVecLE`: a `BitVec (8 * n)` as `n` little-endian bytes, low byte first.
- `instCodecUInt8` to `instCodecUInt64`: the fixed-width unsigned integers as 1, 2, 4 and 8 little-endian bytes.

For example, the `UInt32` value `0x12345678` encodes as four bytes, low byte first:

```text
encode 0x12345678                = [0x78, 0x56, 0x34, 0x12]
decode [0x78, 0x56, 0x34, 0x12, 0xff] = some (0x12345678, [0xff])
decode [0x78, 0x56, 0x34]        = none
```

Dogecoin Core `v1.14.9` uses the same little-endian byte order for these integers, in `ser_writedata16` to `ser_writedata64` and `ser_readdata16` to `ser_readdata64` of `src/serialize.h` (SOURCES.md, D1).
That agreement comes from a reading of the source code.
`lake test` also checks the compiled codecs on fields of Dogecoin's genesis block, and `tests/KnownAnswers.lean` records their provenance.

## Specification and properties

This module holds only the executable operations.
Their laws are properties, so they are in `DogeLib.Serialization.Proofs.Codec`, in the `Proofs` library.
That module defines the class `LawfulCodec`, with two laws:

- Round trip: `decode (encode a ++ rest) = some (a, rest)`.
- Canonicality: if `decode bs = some (a, rest)`, then `bs = encode a ++ rest`.

The proof library proves both laws for each codec here.
For `Codec.ofEquiv`, it needs the hypothesis that the two conversion functions are inverse to each other.
The split follows Lean core's `BEq` and `LawfulBEq`, where a class with operations has a separate class of laws.

## Source

Adapted from btc-verified, [`BtcVerified/Serialize/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Codec.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- The upstream `Codec` class has the two laws as fields.
  Here `Codec` has only `encode` and `decode`, and the laws are the class `LawfulCodec` of the proof library.
- Upstream `Codec.ofEquiv` takes a Mathlib `Equiv`.
  Here it takes the two conversion functions, and the proof library takes their inverse laws as hypotheses.
  This removes the dependency on Mathlib.
- The theorems of the upstream file are in `DogeLib/Serialization/Proofs/Codec.lean`.
- The upstream instance for `BitVec 256` is not adapted, because nothing in DogeLib uses it yet.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/--
The operations of a codec for `α`: an encoder and a prefix decoder.

`decode` returns the decoded value and the remainder, so that codecs compose by passing the remainder to the next decoder.
The laws that relate the two operations are in the class `LawfulCodec` of `DogeLib.Serialization.Proofs.Codec`.
-/
class Codec (α : Type) where
  /-- The bytes of a value. -/
  encode : α → List UInt8
  /-- A value read from the start of the bytes, with the remainder, or `none` when the decoder rejects the bytes. -/
  decode : List UInt8 → Option (α × List UInt8)

/-! ## Pairs -/

/-- Decode an `α`, then a `β` from the remainder, and return the pair with the second remainder. -/
def decodeProd {α β : Type} [Codec α] [Codec β]
    (bs : List UInt8) : Option ((α × β) × List UInt8) := do
  let (a, rest) ← Codec.decode (α := α) bs
  let (b, rest') ← Codec.decode (α := β) rest
  return ((a, b), rest')

/--
The codec of a pair: the encoding of the first component, then the encoding of the second.
The decoder is `decodeProd`.
-/
instance instCodecProd {α β : Type} [Codec α] [Codec β] : Codec (α × β) where
  encode p := Codec.encode p.1 ++ Codec.encode p.2
  decode := decodeProd

/-! ## Transport -/

/--
The codec of `α`, made from a codec of `β` and two conversion functions.

`encode` converts a value with `toFun` and encodes the result.
`decode` decodes a `β` and converts it with `invFun`.
The codec is lawful if the two functions are inverse to each other (`LawfulCodec.ofEquiv`).
-/
@[reducible] def Codec.ofEquiv {α β : Type} (toFun : α → β) (invFun : β → α) (cb : Codec β) :
    Codec α where
  encode a := cb.encode (toFun a)
  decode bs := (cb.decode bs).map (fun p => (invFun p.1, p.2))

/-! ## Bytes and little-endian fixed-width values

The smallest unit is one byte.
One little-endian construction encodes every `BitVec (8 * n)` as `n` bytes, low byte first.
Each fixed-width integer codec is this construction, carried by `Codec.ofEquiv` along the conversion to `BitVec`.
So the byte order is defined in one place.
-/

/-- The first byte and the rest of the bytes, or `none` when there are no bytes. -/
def decodeByte : List UInt8 → Option (UInt8 × List UInt8)
  | [] => none
  | b :: bs => some (b, bs)

/-- The `n` little-endian bytes of a `BitVec (8 * n)`, low byte first. -/
def encodeBitVecLE : (n : Nat) → BitVec (8 * n) → List UInt8
  | 0, _ => []
  | n + 1, v => UInt8.ofBitVec (v.setWidth 8) :: encodeBitVecLE n ((v >>> 8).setWidth (8 * n))

/-- A `BitVec (8 * n)` read from the first `n` bytes, low byte first, with the remainder, or `none` when there are fewer than `n` bytes. -/
def decodeBitVecLE : (n : Nat) → List UInt8 → Option (BitVec (8 * n) × List UInt8)
  | 0, bs => some (0#0, bs)
  | n + 1, bs => do
    let (b, bs') ← decodeByte bs
    let (hi, rest) ← decodeBitVecLE n bs'
    return (hi ++ b.toBitVec, rest)

/-- The little-endian codec of `BitVec (8 * n)`: every fixed-width codec here is built from it. -/
@[reducible] def bitVecCodecLE (n : Nat) : Codec (BitVec (8 * n)) where
  encode := encodeBitVecLE n
  decode := decodeBitVecLE n

/-- A `UInt8` as one byte. -/
instance instCodecUInt8 : Codec UInt8 :=
  Codec.ofEquiv UInt8.toBitVec UInt8.ofBitVec (bitVecCodecLE 1)

/-- A `UInt16` as 2 little-endian bytes. -/
instance instCodecUInt16 : Codec UInt16 :=
  Codec.ofEquiv UInt16.toBitVec UInt16.ofBitVec (bitVecCodecLE 2)

/-- A `UInt32` as 4 little-endian bytes. -/
instance instCodecUInt32 : Codec UInt32 :=
  Codec.ofEquiv UInt32.toBitVec UInt32.ofBitVec (bitVecCodecLE 4)

/-- A `UInt64` as 8 little-endian bytes. -/
instance instCodecUInt64 : Codec UInt64 :=
  Codec.ofEquiv UInt64.toBitVec UInt64.ofBitVec (bitVecCodecLE 8)

end DogeLib.Serialization
