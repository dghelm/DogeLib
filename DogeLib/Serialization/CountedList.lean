module

public import DogeLib.Serialization.Codec
public import DogeLib.Serialization.CompactSize
public import DogeLib.Serialization.PackedCodec

/-!
# `Serialization.CountedList`

Counted lists: a CompactSize count, then that many elements, each encoded after the one before.

Dogecoin serializes every variable-length sequence in this form.
Examples are the inputs and outputs of a transaction, the bytes of a script, and the transactions of a block.
Core writes a `std::vector` or a `prevector` with `WriteCompactSize(v.size())` and then each element, in `src/serialize.h` (SOURCES.md, D1).
For example, the list of two `UInt16` values `[1, 0x0302]` encodes as a count of 2 and then the two values, low byte first:

```text
encode [1, 0x0302]                           = [0x02, 0x01, 0x00, 0x02, 0x03]
decode [0x02, 0x01, 0x00, 0x02, 0x03, 0xff]  = some ([1, 0x0302], [0xff])
decode [0x02, 0x01, 0x00, 0x02]              = none
```

A `CountedList α` is a `List α` whose length is below `2 ^ 64`, so that a CompactSize count can state it.
This bound is a limit of the encoding, not of the protocol.

As for CompactSize, this module defines two decoders with different contracts.

- `CountedList.decode` is the generic decoder. It reads the count with the generic `CompactSize.decode`, which accepts every canonical count.
  With `CountedList.encode`, it is the codec `instCodecCountedList`.
  `instPackedCodecCountedList` is its packed form, and `instPackedCodecCountedListBytes` is a faster packed form for lists of bytes.
- `CountedList.decodeBounded` is the reader of Dogecoin Core, `Unserialize_impl` for `std::vector` and `prevector` in `src/serialize.h` (D1).
  It reads the count with Core's `ReadCompactSize`, `CompactSize.decodeBounded`, so it rejects a count above `MAX_SIZE = 0x02000000` before it reads any element.
  It reads each element with a reader that the caller passes, and returns a typed error, `CompactSize.ReadError`.
  `decodeBoundedBytes` reads a list of bytes as one block, as Core does for `unsigned char`.

The two decoders differ on lists with more than `0x02000000` elements.
For example, `fe 01 00 00 02` is the count `0x02000001`.
The generic decoder reads it, then tries to read that many elements.
The bounded reader rejects it as `tooLarge` and reads no element.

`DogeLib.Serialization.Proofs.CountedList` proves the codec laws, the agreement of the packed codecs, and the contract of the bounded reader.

## Source

The generic codec and its packed forms are adapted from btc-verified, [`BtcVerified/Serialize/CountedList.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CountedList.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
`pushBytes` is adapted from `BtcVerified/Serialize/Bytes.lean` of the same commit.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
The adapted material is `CountedList`, `ofList?`, `encodeElems`, `decodeElems`, `encode`, `decode`, `instCodecCountedList`, `pushElems`, `readElems`, `encodeInto`, `decodeSlice`, `instPackedCodecCountedList`, `pushBytes`, `readByteList` and `instPackedCodecCountedListBytes`.
These are the changes:

- Upstream keeps the definitions and the theorems in one file.
  Here the definitions are in this file, and the theorems are in `DogeLib/Serialization/Proofs/CountedList.lean`.
- Upstream `instCodecCountedList` and the packed instances have the laws as fields.
  Here they have only the operations, and the laws are instances of `LawfulCodec` and `LawfulPackedCodec` in the proof library.
- Upstream names the operations `encodeCountedList`, `decodeCountedList`, `pushCountedList` and `readCountedList`.
  Here they are `CountedList.encode`, `CountedList.decode`, `CountedList.encodeInto` and `CountedList.decodeSlice`.
- Upstream writes the operations of the byte instance inside the instance.
  Here they are the named functions `encodeIntoBytes` and `decodeSliceBytes`.
- The namespace, the module header and the doc comments are DogeLib's.

`readElemsBounded`, `readByte`, `readBytes`, `decodeBounded` and `decodeBoundedBytes` are DogeLib's.
They follow `Unserialize_impl` for `std::vector` and `prevector` of Dogecoin Core `v1.14.9`, commit `e0a1c15`, `src/serialize.h`, lines 592 to 624 and 660 to 692 (D1).
-/

@[expose] public section

namespace DogeLib.Serialization

/--
A list that a CompactSize count can state: its length is below `2 ^ 64`.

The bound is a limit of the encoding.
Dogecoin's limits on the number of inputs, outputs or script bytes are far lower, and other layers state them.
-/
abbrev CountedList (α : Type) := { l : List α // l.length < 2 ^ 64 }

namespace CountedList

/-- The list as a `CountedList` when its length is below `2 ^ 64`, and `none` otherwise. -/
def ofList? {α : Type} (l : List α) : Option (CountedList α) :=
  if h : l.length < 2 ^ 64 then some ⟨l, h⟩ else none

/-! ## The generic codec -/

/-- The encodings of the values of a list, one after the other, without a count. -/
def encodeElems {α : Type} [Codec α] : List α → List UInt8
  | [] => []
  | x :: xs => Codec.encode x ++ encodeElems xs

/--
Exactly `n` values, each read from the remainder of the one before, with the last remainder.
The result is `none` when the element decoder rejects one of them.
-/
def decodeElems {α : Type} [Codec α] : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (x, rest) ← Codec.decode (α := α) bs
    let (xs, rest') ← decodeElems n rest
    return (x :: xs, rest')

/-- The canonical CompactSize encoding of the length, then the encodings of the elements. -/
def encode {α : Type} [Codec α] (cl : CountedList α) : List UInt8 :=
  CompactSize.encode (UInt64.ofNat cl.val.length) ++ encodeElems cl.val

/--
The generic decoder: a count read with the generic `CompactSize.decode`, then that many elements.

The result is `none` when the count or an element is rejected.
The count can be any `UInt64`, including counts above `MAX_SIZE`.
The check `ofList?` never fails here, because the list has as many elements as the count.
-/
def decode {α : Type} [Codec α] (bs : List UInt8) : Option (CountedList α × List UInt8) := do
  let (count, rest) ← CompactSize.decode bs
  let (xs, rest') ← decodeElems count.toNat rest
  let cl ← ofList? xs
  return (cl, rest')

end CountedList

/--
The generic codec of a counted list: `CountedList.encode` and `CountedList.decode`.
The laws are `instLawfulCodecCountedList` of `DogeLib.Serialization.Proofs.CountedList`, for every lawful element codec.
-/
instance instCodecCountedList {α : Type} [Codec α] : Codec (CountedList α) where
  encode := CountedList.encode
  decode := CountedList.decode

namespace CountedList

/-! ## The packed generic codec -/

/-- The buffer with the encodings of the values of a list appended, one after the other: the packed form of `encodeElems`. -/
def pushElems {α : Type} [PackedCodec α] : List α → ByteArray → ByteArray
  | [], acc => acc
  | x :: xs, acc => pushElems xs (PackedCodec.encodeInto x acc)

/-- Exactly `n` values read from the start of the slice, with the rest of the slice: the packed form of `decodeElems`. -/
def readElems {α : Type} [PackedCodec α] : Nat → ByteSlice → Option (List α × ByteSlice)
  | 0, s => some ([], s)
  | n + 1, s => do
    let (x, s1) ← PackedCodec.decodeSlice s
    let (xs, s2) ← readElems n s1
    return (x :: xs, s2)

/-- The buffer with the encoding of a counted list appended: the packed form of `encode`. -/
def encodeInto {α : Type} [PackedCodec α] (cl : CountedList α) (acc : ByteArray) : ByteArray :=
  pushElems cl.val (CompactSize.encodeInto (UInt64.ofNat cl.val.length) acc)

/-- A counted list read from the start of the slice, with the rest of the slice: the packed form of `decode`. -/
def decodeSlice {α : Type} [PackedCodec α] (s : ByteSlice) :
    Option (CountedList α × ByteSlice) := do
  let (count, s1) ← CompactSize.decodeSlice s
  let (xs, s2) ← readElems count.toNat s1
  let cl ← ofList? xs
  return (cl, s2)

/-! ## The packed codec of byte lists

A list of bytes encodes as the bytes themselves after the count.
So the packed codec of a `CountedList UInt8` can copy the bytes as one block, instead of calling the element codec once for each byte.
-/

/-- The buffer with the bytes of a list appended. -/
def pushBytes (bs : List UInt8) (acc : ByteArray) : ByteArray :=
  bs.foldl ByteArray.push acc

/-- The first `n` bytes of the slice as a list, with the rest of the slice, or `none` when the slice has fewer than `n` bytes. -/
def readByteList (n : Nat) (s : ByteSlice) : Option (List UInt8 × ByteSlice) :=
  if n ≤ s.size then some ((s.take n).toList, s.drop n) else none

/-- The buffer with the encoding of a counted list of bytes appended, with the bytes copied as one block. -/
def encodeIntoBytes (cl : CountedList UInt8) (acc : ByteArray) : ByteArray :=
  pushBytes cl.val (CompactSize.encodeInto (UInt64.ofNat cl.val.length) acc)

/-- A counted list of bytes read from the start of the slice, with the bytes read as one block. -/
def decodeSliceBytes (s : ByteSlice) : Option (CountedList UInt8 × ByteSlice) := do
  let (count, s1) ← CompactSize.decodeSlice s
  let (bytes, s2) ← readByteList count.toNat s1
  let cl ← ofList? bytes
  return (cl, s2)

end CountedList

/--
The packed codec of a counted list: `CountedList.encodeInto` and `CountedList.decodeSlice`.
Its agreement with `instCodecCountedList` is `instLawfulPackedCodecCountedList`, for every lawful packed element codec.
-/
instance instPackedCodecCountedList {α : Type} [PackedCodec α] : PackedCodec (CountedList α) where
  encodeInto := CountedList.encodeInto
  decodeSlice := CountedList.decodeSlice

/--
The packed codec of a counted list of bytes, which copies the bytes as one block.
It has a higher priority than `instPackedCodecCountedList`, so it is the instance for `CountedList UInt8`.
Its agreement with `instCodecCountedList` is `instLawfulPackedCodecCountedListBytes`.
-/
instance (priority := high) instPackedCodecCountedListBytes : PackedCodec (CountedList UInt8) where
  encodeInto := CountedList.encodeIntoBytes
  decodeSlice := CountedList.decodeSliceBytes

namespace CountedList

open CompactSize (ReadError)

/-! ## Core's bounded reader -/

/--
Exactly `n` values, each read by `elem` from the remainder of the one before, with the last remainder.
The result is the first error of `elem`, if there is one.

It models the element loop of `Unserialize_impl` for a vector of any type except `unsigned char`.
That loop is at `src/serialize.h` lines 676 to 692 for `std::vector`, and at lines 608 to 624 for `prevector` (D1).
Core grows the vector in steps of `5000000 / sizeof(T)` elements.
So a large count with too few bytes does not allocate memory for the whole count.
The steps do not change which elements Core reads or which error it reports, so this definition reads one element at a time.
-/
def readElemsBounded {α : Type} (elem : List UInt8 → Except ReadError (α × List UInt8)) :
    Nat → List UInt8 → Except ReadError (List α × List UInt8)
  | 0, bs => .ok ([], bs)
  | n + 1, bs =>
    match elem bs with
    | .error e => .error e
    | .ok (x, rest) =>
      match readElemsBounded elem n rest with
      | .error e => .error e
      | .ok (xs, rest') => .ok (x :: xs, rest')

/-- One byte, or `truncated` when there are no bytes: Core's read of one `unsigned char` from a `CDataStream` (D21). -/
def readByte : List UInt8 → Except ReadError (UInt8 × List UInt8)
  | [] => .error .truncated
  | b :: bs => .ok (b, bs)

/--
The first `n` bytes and the bytes after them, or `truncated` when there are fewer than `n` bytes.

It models the element loop of `Unserialize_impl` for a vector of `unsigned char`.
That loop is at `src/serialize.h` lines 660 to 674 for `std::vector`, and at lines 592 to 606 for `prevector` (D1).
Core reads the bytes in blocks of at most 5000000.
The blocks do not change the result: the read fails exactly when fewer than `n` bytes remain (`CDataStream::read`, D21).
-/
def readBytes (n : Nat) (bs : List UInt8) : Except ReadError (List UInt8 × List UInt8) :=
  if n ≤ bs.length then .ok (bs.take n, bs.drop n) else .error .truncated

/--
Dogecoin Core's reader of a vector, `Unserialize_impl` in `src/serialize.h` (D1), over a byte list.

It reads the count with Core's `ReadCompactSize`, `CompactSize.decodeBounded`.
If that fails, the result is its error, and no element is read.
So a count above `MAX_SIZE = 0x02000000` is `tooLarge`, whatever bytes follow it.
Otherwise it reads that many elements with `elem`, and returns the first error of `elem`, if there is one.

The final check `ofList?` never fails, because the list has at most `0x02000000` elements.
If it failed, the result would be `tooLarge`.

The contract, proved in `DogeLib.Serialization.Proofs.CountedList`, for an element reader `elem` that accepts exactly what a codec accepts:

- `decodeBounded_eq_ok_iff`: the reader returns `(cl, rest)` exactly when the generic `CountedList.decode` returns `(cl, rest)` and `cl` has at most `0x02000000` elements.
- `decodeBounded_encode`: the round trip, for lists with at most `0x02000000` elements.

`decodeBounded_of_count_error` holds for every `elem`: an error of the count is the error of the reader.
-/
def decodeBounded {α : Type} (elem : List UInt8 → Except ReadError (α × List UInt8))
    (bs : List UInt8) : Except ReadError (CountedList α × List UInt8) :=
  match CompactSize.decodeBounded bs with
  | .error e => .error e
  | .ok (count, rest) =>
    match readElemsBounded elem count.toNat rest with
    | .error e => .error e
    | .ok (xs, rest') =>
      match ofList? xs with
      | none => .error .tooLarge
      | some cl => .ok (cl, rest')

/--
Dogecoin Core's reader of a vector of bytes, such as a script: the count, then the bytes as one block.
`decodeBoundedBytes_eq` proves that it is `decodeBounded readByte`.
-/
def decodeBoundedBytes (bs : List UInt8) : Except ReadError (CountedList UInt8 × List UInt8) :=
  match CompactSize.decodeBounded bs with
  | .error e => .error e
  | .ok (count, rest) =>
    match readBytes count.toNat rest with
    | .error e => .error e
    | .ok (xs, rest') =>
      match ofList? xs with
      | none => .error .tooLarge
      | some cl => .ok (cl, rest')

end CountedList

end DogeLib.Serialization
