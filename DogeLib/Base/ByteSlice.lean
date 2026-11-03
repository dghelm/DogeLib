module

public import Std.Data.ByteSlice

/-!
# `Base.ByteSlice`

Reader operations on core's `ByteSlice`, and the function that reads a slice as a list of bytes.

A `ByteSlice` is a view of a region of a `ByteArray`: the base array and a start and a stop offset.
A packed decoder reads from a slice, and its remainder is the same array at a later offset, so decoding copies no bytes.
Lean core defines the view, but no list form of it and no operation that reads one byte and advances.
This module adds these operations:

- `toList`: the bytes in view, as the `List UInt8` of the codec specification.
- `take` and `drop`: the first `n` bytes in view, and the view after them.
- `uncons`: the first byte in view and the view after it, or `none` for an empty view.

`DogeLib.Base.Proofs.ByteSlice` proves that `take`, `drop` and `uncons` agree with the list operations of the same names, through `toList`.

The definitions extend core's `ByteSlice` namespace, as upstream does, so that `s.toList` works as dot notation.

Adapted from btc-verified, [`BtcVerified/Ext/ByteSlice.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteSlice.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
This file contains only the definitions of that file.
Its theorems are in `DogeLib/Base/Proofs/ByteSlice.lean`.
The other changes are the module header and the doc comments.
-/

@[expose] public section

namespace ByteSlice

/--
The bytes in view, first to last, as a list.

`toList` is the abstraction function through which the packed codecs state their agreement with the codec specification.
It copies only the bytes in view, not the whole base array.
-/
def toList (s : ByteSlice) : List UInt8 :=
  (s.byteArray.extract s.start s.stop).toList

/-- The view of the first `n` bytes of `s`, or of all of `s` when it has fewer than `n` bytes. -/
def take (s : ByteSlice) (n : Nat) : ByteSlice := s.slice 0 n

/-- The view of `s` after its first `n` bytes. It is empty when `s` has `n` bytes or fewer. -/
def drop (s : ByteSlice) (n : Nat) : ByteSlice := s.slice n s.size

/--
The first byte in view and the view after it, or `none` when the view is empty.

The result shares the base array of `s`, at an offset one byte later.
-/
def uncons (s : ByteSlice) : Option (UInt8 × ByteSlice) :=
  if h : 0 < s.size then some (s[0]'h, s.drop 1) else none

end ByteSlice
