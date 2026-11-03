module

public import DogeLib.Base.ByteSlice
public import DogeLib.Serialization.Codec

/-!
# `Serialization.PackedCodec`

Packed codecs: the codecs of `DogeLib.Serialization.Codec`, over byte arrays instead of lists.

A `Codec` works on `List UInt8`, which is simple to reason about but slow to run: each byte is a separate list cell.
A *packed codec* has the same two operations over packed bytes:

- `encodeInto` appends the encoding of a value to a `ByteArray`.
- `decodeSlice` reads a value from the start of a `ByteSlice`, and returns the value and the rest of the slice.
  The rest is a view of the same array, so decoding copies no bytes.

The constructions follow those of `Codec` one for one: pairs (`instPackedCodecProd`), transport (`PackedCodec.ofEquiv`), the little-endian primitive (`pushBitVecLE` and `readBitVecLE`), and the fixed-width integers.

## Specification and properties

A packed codec is an implementation of a `Codec`, and it has no laws of its own.
`DogeLib.Serialization.Proofs.PackedCodec`, in the `Proofs` library, states its agreement with the `Codec` as the class `LawfulPackedCodec`:

- `toList_encodeInto`: the packed encoder appends exactly the bytes of `Codec.encode`.
- `abstractParse_decodeSlice`: the packed decoder rejects exactly the inputs that `Codec.decode` rejects.
  On the other inputs, it returns the same value, and a remainder with the same bytes.

The proof library proves both agreement laws for each packed codec here.
A property of the `Codec`, such as its round trip, carries over to the packed codec by a rewrite with these two laws.
No separate theorem states the round trip of a packed codec.

## Source

Adapted from btc-verified, [`BtcVerified/Packed/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/Codec.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- The upstream `PackedCodec` class takes a `Codec` instance and has the two agreement laws as fields.
  Here `PackedCodec` has only `encodeInto` and `decodeSlice`.
  The agreement laws are the class `LawfulPackedCodec` of the proof library, which names the `Codec` that the packed codec agrees with.
- Upstream `PackedCodec.ofEquiv` takes a Mathlib `Equiv`. Here it takes the two conversion functions, as `Codec.ofEquiv` does.
- `abstractParse` and the theorems of the upstream file are in `DogeLib/Serialization/Proofs/PackedCodec.lean`.
- The upstream instance for `BitVec 256` is not adapted, because nothing in DogeLib uses it yet.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/--
The operations of a packed codec for `α`: an encoder that appends to a `ByteArray`, and a prefix decoder that reads a `ByteSlice`.

The class `LawfulPackedCodec` of `DogeLib.Serialization.Proofs.PackedCodec` relates these operations to a `Codec α`.
-/
class PackedCodec (α : Type) where
  /-- The output buffer, with the encoding of the value appended. -/
  encodeInto : α → ByteArray → ByteArray
  /-- A value read from the start of the slice, with the rest of the slice, or `none` when the decoder rejects the bytes. -/
  decodeSlice : ByteSlice → Option (α × ByteSlice)

namespace PackedCodec

/-- The encoding of a value, in a new `ByteArray`. -/
def encode {α : Type} [PackedCodec α] (a : α) : ByteArray :=
  encodeInto a ByteArray.empty

/--
A value read from the start of a byte array, with the remainder as a slice of the same array.
The result is `none` when the decoder rejects the bytes.
-/
def decode {α : Type} [PackedCodec α] (bytes : ByteArray) : Option (α × ByteSlice) :=
  decodeSlice (ByteSlice.ofByteArray bytes)

end PackedCodec

/-! ## Pairs -/

/--
The packed codec of a pair.
The encoder appends the first component, then the second.
The decoder reads the first component, then the second from the rest of the slice.
-/
instance instPackedCodecProd {α β : Type} [PackedCodec α] [PackedCodec β] :
    PackedCodec (α × β) where
  encodeInto p acc := PackedCodec.encodeInto p.2 (PackedCodec.encodeInto p.1 acc)
  decodeSlice s := do
    let (a, s1) ← PackedCodec.decodeSlice s
    let (b, s2) ← PackedCodec.decodeSlice s1
    return ((a, b), s2)

/-! ## Transport -/

/--
The packed codec of `α`, made from a packed codec of `β` and two conversion functions, as `Codec.ofEquiv` makes a codec.
-/
@[reducible] def PackedCodec.ofEquiv {α β : Type} (toFun : α → β) (invFun : β → α)
    (pb : PackedCodec β) : PackedCodec α where
  encodeInto a acc := pb.encodeInto (toFun a) acc
  decodeSlice s := (pb.decodeSlice s).map fun p => (invFun p.1, p.2)

/-! ## Little-endian fixed-width values -/

/-- A `BitVec (8 * n)` read from the first `n` bytes of the slice, low byte first, with the rest of the slice: the packed form of `decodeBitVecLE`. -/
def readBitVecLE : (n : Nat) → ByteSlice → Option (BitVec (8 * n) × ByteSlice)
  | 0, s => some (0#0, s)
  | n + 1, s => do
    let (b, s1) ← s.uncons
    let (hi, rest) ← readBitVecLE n s1
    return (hi ++ b.toBitVec, rest)

/-- The buffer with the `n` little-endian bytes of a `BitVec (8 * n)` appended, low byte first: the packed form of `encodeBitVecLE`. -/
def pushBitVecLE : (n : Nat) → BitVec (8 * n) → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, v, acc =>
    pushBitVecLE n ((v >>> 8).setWidth (8 * n)) (acc.push (UInt8.ofBitVec (v.setWidth 8)))

/-- The packed little-endian codec of `BitVec (8 * n)`, the packed form of `bitVecCodecLE n`. -/
@[reducible] def packedBitVecLE (n : Nat) : PackedCodec (BitVec (8 * n)) where
  encodeInto := pushBitVecLE n
  decodeSlice := readBitVecLE n

/-- A `UInt8` as one packed byte, the packed form of `instCodecUInt8`. -/
instance instPackedCodecUInt8 : PackedCodec UInt8 :=
  PackedCodec.ofEquiv UInt8.toBitVec UInt8.ofBitVec (packedBitVecLE 1)

/-- A `UInt16` as 2 packed little-endian bytes, the packed form of `instCodecUInt16`. -/
instance instPackedCodecUInt16 : PackedCodec UInt16 :=
  PackedCodec.ofEquiv UInt16.toBitVec UInt16.ofBitVec (packedBitVecLE 2)

/-- A `UInt32` as 4 packed little-endian bytes, the packed form of `instCodecUInt32`. -/
instance instPackedCodecUInt32 : PackedCodec UInt32 :=
  PackedCodec.ofEquiv UInt32.toBitVec UInt32.ofBitVec (packedBitVecLE 4)

/-- A `UInt64` as 8 packed little-endian bytes, the packed form of `instCodecUInt64`. -/
instance instPackedCodecUInt64 : PackedCodec UInt64 :=
  PackedCodec.ofEquiv UInt64.toBitVec UInt64.ofBitVec (packedBitVecLE 8)

end DogeLib.Serialization
