module

public import DogeLib.Serialization.Codec
public import DogeLib.Serialization.PackedCodec

/-!
# `Serialization.CompactSize`

CompactSize, the variable-length unsigned integer that prefixes counts and lengths in Dogecoin serialization.

A CompactSize value has one of four forms.
The first byte, the *marker*, selects the form, and a little-endian *payload* follows it:

```text
value n                  bytes
n < 253                  [n]                              1 byte
253 <= n < 2^16          fd, n as 2 little-endian bytes   3 bytes
2^16 <= n < 2^32         fe, n as 4 little-endian bytes   5 bytes
2^32 <= n < 2^64         ff, n as 8 little-endian bytes   9 bytes
```

An encoding is *canonical* when it uses the shortest form for its value.
For example, `fd 00 00` also has the value 0, but it is not canonical, because `00` is shorter.

This module defines two decoders with different contracts.

- `decode` is the generic canonical decoder.
  It accepts every canonical encoding of a `UInt64`, and rejects every other input.
  With `encode`, it is the codec `CompactSize.codec`, and `CompactSize.packedCodec` is its packed form.
- `decodeBounded` is the reader of Dogecoin Core, `ReadCompactSize` in `src/serialize.h` (SOURCES.md, D1).
  It also rejects a value above `MAX_SIZE = 0x02000000`, and it returns a typed error, `ReadError`.

The two decoders differ on canonical encodings of values above `MAX_SIZE`.
For example, `fe 01 00 00 02` is the canonical encoding of `0x02000001`:

```text
encode 0x02000001                       = [0xfe, 0x01, 0x00, 0x00, 0x02]
decode [0xfe, 0x01, 0x00, 0x00, 0x02]        = some (0x02000001, [])
decodeBounded [0xfe, 0x01, 0x00, 0x00, 0x02] = error tooLarge
```

So the codec laws hold for `decode` on every `UInt64`, and the round trip of `decodeBounded` holds only for values up to `MAX_SIZE`.
`DogeLib.Serialization.Proofs.CompactSize` proves both, and relates `decodeBounded` to a separate statement of the accepted bytes, `ValidCompactSizePrefix`.

Neither decoder is a registered `Codec UInt64` instance.
That instance is the fixed-width codec of 8 bytes, `instCodecUInt64`.

## Source

The generic codec is adapted from btc-verified, [`BtcVerified/Serialize/CompactSize.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CompactSize.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
The adapted material is `encodeFixedWidth`, `decodeFixedWidth`, `encode`, `decode`, `codec`, `pushFixedWidth`, `readFixedWidth`, `encodeInto`, `decodeSlice` and `packedCodec`.
These are the changes:

- Upstream keeps the definitions, the theorems and the packed codec in one file.
  Here the definitions are in this file, and the theorems are in `DogeLib/Serialization/Proofs/CompactSize.lean`.
- Upstream `compactSizeCodec` is a `Codec UInt64` with the laws as fields.
  Here `codec` has only the two operations, and the laws are `lawfulCodec` in the proof library.
- Upstream names the packed operations `pushCompactSize` and `readCompactSize`.
  Here they are `encodeInto` and `decodeSlice`, because Core's `ReadCompactSize` is the bounded reader, not the generic one.
- `packedCodec` packages the packed operations as a `PackedCodec UInt64`. Upstream has no such value.
- The namespace, the module header and the doc comments are DogeLib's.

`maxSize`, `ReadError`, `readPayload`, `readCanonical` and `decodeBounded` are DogeLib's, and so are their packed forms `readPayloadSlice`, `readCanonicalSlice` and `decodeBoundedSlice`.
They follow `MAX_SIZE` and `ReadCompactSize` of Dogecoin Core `v1.14.9`, commit `e0a1c15`, `src/serialize.h` (SOURCES.md, D1).
-/

@[expose] public section

namespace DogeLib.Serialization.CompactSize

/-! ## The generic canonical codec -/

/--
The `byteWidth` little-endian bytes of the low `8 * byteWidth` bits of `n`: the payload after a marker.
-/
def encodeFixedWidth (byteWidth : Nat) (n : UInt64) : List UInt8 :=
  encodeBitVecLE byteWidth (n.toBitVec.setWidth (8 * byteWidth))

/--
A value read from a payload of `byteWidth` little-endian bytes, with the remainder.

The result is `none` when there are fewer than `byteWidth` bytes, or when the value is below `minValue`.
`minValue` is the smallest value that needs this form, so a smaller value is not canonical.
-/
def decodeFixedWidth (byteWidth minValue : Nat) (bs : List UInt8) :
    Option (UInt64 × List UInt8) := do
  let (w, rest) ← decodeBitVecLE byteWidth bs
  guard (minValue ≤ w.toNat)
  return (⟨w.setWidth 64⟩, rest)

/--
The canonical CompactSize encoding of `n`, for every `UInt64`.

The conditions choose the shortest form for `n`, as `WriteCompactSize` of Core does (D1).
-/
def encode (n : UInt64) : List UInt8 :=
  if n < 253 then [n.toUInt8]
  else if n < 2 ^ 16 then 0xFD :: encodeFixedWidth 2 n
  else if n < 2 ^ 32 then 0xFE :: encodeFixedWidth 4 n
  else 0xFF :: encodeFixedWidth 8 n

/--
The generic canonical decoder: a CompactSize value read from the start of the bytes, with the remainder.

The result is `none` when the input is empty, when the payload is incomplete, or when the encoding is not canonical.
It accepts every canonical encoding, including values above `MAX_SIZE`.
Core's reader is `decodeBounded`.
-/
def decode (bs : List UInt8) : Option (UInt64 × List UInt8) :=
  match bs with
  | [] => none
  | h :: t =>
    if h < 0xFD then some (h.toUInt64, t)
    else if h = 0xFD then decodeFixedWidth 2 253 t
    else if h = 0xFE then decodeFixedWidth 4 (2 ^ 16) t
    else if h = 0xFF then decodeFixedWidth 8 (2 ^ 32) t
    else none

/--
The generic CompactSize codec of `UInt64`: `encode` and `decode`.

It is not an instance, because the instance `Codec UInt64` is the fixed-width codec `instCodecUInt64`.
Its laws are `lawfulCodec` of `DogeLib.Serialization.Proofs.CompactSize`.
-/
@[reducible] def codec : Codec UInt64 where
  encode := encode
  decode := decode

/-! ## The packed generic codec -/

/-- The buffer with the payload `encodeFixedWidth byteWidth n` appended: the packed form of `encodeFixedWidth`. -/
def pushFixedWidth (byteWidth : Nat) (n : UInt64) (acc : ByteArray) : ByteArray :=
  pushBitVecLE byteWidth (n.toBitVec.setWidth (8 * byteWidth)) acc

/-- A value read from a payload of `byteWidth` little-endian bytes at the start of the slice: the packed form of `decodeFixedWidth`. -/
def readFixedWidth (byteWidth minValue : Nat) (s : ByteSlice) :
    Option (UInt64 × ByteSlice) := do
  let (w, rest) ← readBitVecLE byteWidth s
  guard (minValue ≤ w.toNat)
  return (⟨w.setWidth 64⟩, rest)

/-- The buffer with the canonical encoding of `n` appended: the packed form of `encode`. -/
def encodeInto (n : UInt64) (acc : ByteArray) : ByteArray :=
  if n < 253 then acc.push n.toUInt8
  else if n < 2 ^ 16 then pushFixedWidth 2 n (acc.push 0xFD)
  else if n < 2 ^ 32 then pushFixedWidth 4 n (acc.push 0xFE)
  else pushFixedWidth 8 n (acc.push 0xFF)

/-- A CompactSize value read from the start of the slice, with the rest of the slice: the packed form of `decode`. -/
def decodeSlice (s : ByteSlice) : Option (UInt64 × ByteSlice) := do
  let (h, t) ← s.uncons
  if h < 0xFD then some (h.toUInt64, t)
  else if h = 0xFD then readFixedWidth 2 253 t
  else if h = 0xFE then readFixedWidth 4 (2 ^ 16) t
  else if h = 0xFF then readFixedWidth 8 (2 ^ 32) t
  else none

/--
The packed generic CompactSize codec of `UInt64`: `encodeInto` and `decodeSlice`.

Its agreement with `codec` is `lawfulPackedCodec` of `DogeLib.Serialization.Proofs.CompactSize`.
-/
@[reducible] def packedCodec : PackedCodec UInt64 where
  encodeInto := encodeInto
  decodeSlice := decodeSlice

/-! ## Core's bounded reader -/

/--
`MAX_SIZE` of Core, `0x02000000`, in `src/serialize.h` line 26 (D1).
`ReadCompactSize` rejects a larger value.

This bound is a limit of the serialization code.
It is not the maximum size of a block.
-/
def maxSize : UInt64 := 0x02000000

/--
The reasons that `decodeBounded` rejects an input.
Each one is a failure that `ReadCompactSize` of Core throws as `std::ios_base::failure` (D1).
-/
inductive ReadError where
  /-- The input ends before the marker or before the end of the payload: the stream's "end of data" failure. -/
  | truncated
  /-- The payload holds a value that a shorter form can encode: "non-canonical ReadCompactSize()". -/
  | nonCanonical
  /-- The value is canonical and above `MAX_SIZE`: "ReadCompactSize(): size too large". -/
  | tooLarge
  deriving DecidableEq, Repr

/--
A value read from a payload of `byteWidth` little-endian bytes, as one marker branch of `ReadCompactSize` reads it.

The result is `truncated` when there are fewer than `byteWidth` bytes.
It is `nonCanonical` when the value is below `minValue`, the smallest value that needs this form.
Otherwise it is the value and the remainder.
-/
def readPayload (byteWidth minValue : Nat) (bs : List UInt8) :
    Except ReadError (UInt64 × List UInt8) :=
  match decodeBitVecLE byteWidth bs with
  | none => .error .truncated
  | some (w, rest) =>
    if w.toNat < minValue then .error .nonCanonical
    else .ok (⟨w.setWidth 64⟩, rest)

/--
The marker, the payload and the check for a canonical encoding of `ReadCompactSize`, before its check of `MAX_SIZE`.

It models `src/serialize.h`, lines 247 to 270 (D1).
Line 247 reads the marker `chSize`.
A marker below 253 is the value (lines 249 to 252).
Marker 253 reads 2 bytes and rejects a value below 253 (lines 253 to 258).
Marker 254 reads 4 bytes and rejects a value below `0x10000` (lines 259 to 264).
Every other marker, which is 255, reads 8 bytes and rejects a value below `0x100000000` (lines 265 to 270).
-/
def readCanonical (bs : List UInt8) : Except ReadError (UInt64 × List UInt8) :=
  match bs with
  | [] => .error .truncated
  | chSize :: t =>
    if chSize < 253 then .ok (chSize.toUInt64, t)
    else if chSize = 253 then readPayload 2 253 t
    else if chSize = 254 then readPayload 4 0x10000 t
    else readPayload 8 0x100000000 t

/--
Dogecoin Core's CompactSize reader, `ReadCompactSize` in `src/serialize.h`, lines 244 to 274 (D1), over a byte list.

It reads a prefix of the input, and does not require the whole input.
On success it returns the value and the remainder, the bytes after the encoding.
It rejects an input with the first failure that Core's reader meets, in Core's order:

1. `truncated`: the input is empty, or it ends before the end of the payload that the marker selects.
2. `nonCanonical`: the payload holds a value that a shorter form can encode (lines 256, 262 and 268).
3. `tooLarge`: the value is above `maxSize = 0x02000000` (lines 271 and 272).

So a non-canonical encoding of a value above `MAX_SIZE`, such as `ff ff ff ff ff 00 00 00 00`, is `nonCanonical`, not `tooLarge`.

The contract, proved in `DogeLib.Serialization.Proofs.CompactSize`:

- `decodeBounded_eq_ok_iff_valid`: the reader returns `(value, rest)` exactly when `ValidCompactSizePrefix bytes value rest` holds.
- `decodeBounded_eq_ok_iff_decode`: it returns `(value, rest)` exactly when the generic `decode` returns `(value, rest)` and `value ≤ 0x02000000`.
- `decodeBounded_encode`: for every `n ≤ 0x02000000` and all bytes `rest`, it reads `encode n ++ rest` as `(n, rest)`.

Core's `CDataStream` reports truncation with the failure "CDataStream::read(): end of data" (`src/streams.h`).
Another stream class can report it differently.
The categories of `ReadError` are the contract, and the text of the C++ failures is not.
-/
def decodeBounded (bs : List UInt8) : Except ReadError (UInt64 × List UInt8) :=
  match readCanonical bs with
  | .error e => .error e
  | .ok (nSizeRet, rest) =>
    if nSizeRet > maxSize then .error .tooLarge
    else .ok (nSizeRet, rest)

/-! ## The packed form of Core's bounded reader -/

/-- `readPayload` over a slice: the payload read with `readBitVecLE`. -/
def readPayloadSlice (byteWidth minValue : Nat) (s : ByteSlice) :
    Except ReadError (UInt64 × ByteSlice) :=
  match readBitVecLE byteWidth s with
  | none => .error .truncated
  | some (w, rest) =>
    if w.toNat < minValue then .error .nonCanonical
    else .ok (⟨w.setWidth 64⟩, rest)

/-- `readCanonical` over a slice: the marker read with `ByteSlice.uncons`, then the payload. -/
def readCanonicalSlice (s : ByteSlice) : Except ReadError (UInt64 × ByteSlice) :=
  match s.uncons with
  | none => .error .truncated
  | some (chSize, t) =>
    if chSize < 253 then .ok (chSize.toUInt64, t)
    else if chSize = 253 then readPayloadSlice 2 253 t
    else if chSize = 254 then readPayloadSlice 4 0x10000 t
    else readPayloadSlice 8 0x100000000 t

/--
Core's CompactSize reader over a slice: the packed form of `decodeBounded`.
`abstractRead_decodeBoundedSlice`, in the proof library, proves that it gives the same errors, values and remainder bytes as `decodeBounded` on every slice.
-/
def decodeBoundedSlice (s : ByteSlice) : Except ReadError (UInt64 × ByteSlice) :=
  match readCanonicalSlice s with
  | .error e => .error e
  | .ok (nSizeRet, rest) =>
    if nSizeRet > maxSize then .error .tooLarge
    else .ok (nSizeRet, rest)

end DogeLib.Serialization.CompactSize
