module

public import DogeLib.Base.ByteSlice
public import DogeLib.Base.Bytes
public import DogeLib.Serialization.Codec
public import DogeLib.Serialization.PackedCodec

/-!
# `Serialization.Bytes`

The codecs of byte strings of a fixed length, `Bytes n`, and so of `Hash256`.

A `Bytes n` encodes as its `n` bytes, with no count and no change of order.
The decoder takes the first `n` bytes of the input, and rejects an input with fewer than `n` bytes.
Core serializes a `uint256` in the same way, as its 32 bytes (`base_blob::Serialize` in `src/uint256.h`, SOURCES.md, D22).

```text
encode (b : Bytes 3)          = b.val
decode [0x01, 0x02, 0x03, 0xff] = some ([0x01, 0x02, 0x03], [0xff])     for Bytes 3
decode [0x01, 0x02]             = none                                    for Bytes 3
```

The module also defines `pushBytes`, which appends a list of bytes to a `ByteArray`.
The packed codecs of `Bytes n` and of counted lists of bytes use it.

`DogeLib.Serialization.Proofs.Bytes` proves the codec laws and the agreement of the packed codec.

## Source

Adapted from btc-verified, [`BtcVerified/Serialize/Bytes.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Bytes.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
The adapted material is `decodeBytes`, `instCodecBytes`, `pushBytes`, `readBytes` and `instPackedCodecBytes`.
These are the changes:

- Upstream proves the laws inside the instances. Here they are in `DogeLib/Serialization/Proofs/Bytes.lean`.
- Upstream `readBytes` proves the length of the bytes it reads inside the definition, with lemmas about `ByteSlice`.
  Those lemmas are in the `Proofs` library, which the specification does not import.
  Here `readBytes` checks the length with `Bytes.ofListExact?`, and the proof library shows that the check never fails.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/-- The first `n` bytes as a `Bytes n`, with the bytes after them, or `none` when there are fewer than `n` bytes. -/
def decodeBytes (n : Nat) (bs : List UInt8) : Option (Bytes n × List UInt8) :=
  if h : n ≤ bs.length then
    some (⟨bs.take n, List.length_take_of_le h⟩, bs.drop n)
  else none

/--
The codec of `Bytes n`: the `n` bytes themselves, read by `decodeBytes n`.
At `n = 32` it is the codec of `Hash256`.
Its laws are `instLawfulCodecBytes` of `DogeLib.Serialization.Proofs.Bytes`.
-/
instance instCodecBytes (n : Nat) : Codec (Bytes n) where
  encode bs := bs.val
  decode := decodeBytes n

/-- The buffer with the bytes of a list appended, in order, with `ByteArray.push`. -/
def pushBytes (bs : List UInt8) (acc : ByteArray) : ByteArray :=
  bs.foldl ByteArray.push acc

/--
The first `n` bytes of the slice as a `Bytes n`, with the rest of the slice: the packed form of `decodeBytes`.

The rest of the slice shares the array, and only the `n` bytes of the value are copied.
The check `Bytes.ofListExact?` never fails when the slice has `n` bytes (`abstractParse_readBytes`).
-/
def readBytes (n : Nat) (s : ByteSlice) : Option (Bytes n × ByteSlice) :=
  if n ≤ s.size then
    match Bytes.ofListExact? (s.take n).toList with
    | some b => some (b, s.drop n)
    | none => none
  else none

/--
The packed codec of `Bytes n`: `pushBytes` and `readBytes n`.
Its agreement with `instCodecBytes n` is `instLawfulPackedCodecBytes` of `DogeLib.Serialization.Proofs.Bytes`.
-/
instance instPackedCodecBytes (n : Nat) : PackedCodec (Bytes n) where
  encodeInto bs acc := pushBytes bs.val acc
  decodeSlice := readBytes n

end DogeLib.Serialization
