module

/-!
# `Base.Bytes`

Byte strings of a fixed length, and the 32-byte hash.

`Bytes n` is a `List UInt8` of length `n`.
Some Dogecoin fields are byte strings whose length is part of the format, such as the 32-byte hash of an outpoint.
The type records the length, so that a definition that receives a `Bytes n` cannot get a string of another length.

`Hash256` is `Bytes 32`: the 32 bytes of a double SHA-256 digest, a transaction ID or a block hash.
The bytes are in the order that SHA-256 outputs them, which is also the order in which Core serializes a `uint256` (`base_blob::Serialize`, `src/uint256.h`, SOURCES.md, D22).
Core displays a hash with its bytes reversed (`base_blob::GetHex`, D11).
`Hash256.displayBytes` gives the bytes in that order, and `Hash256.ofDisplayBytes?` reads them back.

`DogeLib.Base.Proofs.Bytes` proves the properties of these definitions.

## Source

Adapted from btc-verified, [`BtcVerified/Serialize/Bytes.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Bytes.lean) and [`BtcVerified/Crypto/Hash256.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Crypto/Hash256.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
The adapted material is `Bytes`, `Bytes.ofListExact?`, `Bytes.reverse`, `Hash256` and `Hash256.ofBytes?`.
These are the changes:

- The theorems of the upstream files are in `DogeLib/Base/Proofs/Bytes.lean`.
- The codecs of the upstream files are in `DogeLib/Serialization/Bytes.lean`.
- The upstream constructors that pad or truncate a list are not adapted, because nothing in DogeLib uses them yet.
- Upstream `Hash256` has an `OfNat` instance for synthetic tests. It is not adapted. `Hash256.zero` is the only constant here.
- `Hash256.displayBytes` and `Hash256.ofDisplayBytes?` are DogeLib's. Upstream keeps the display order in its tests.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib

/-- A byte string of exactly `n` bytes. -/
abbrev Bytes (n : Nat) := { bytes : List UInt8 // bytes.length = n }

namespace Bytes

/-- The list as a `Bytes n` when it has exactly `n` bytes, and `none` otherwise. -/
def ofListExact? {n : Nat} (bs : List UInt8) : Option (Bytes n) :=
  if h : bs.length = n then some ⟨bs, h⟩ else none

/-- The same bytes in reverse order. -/
def reverse {n : Nat} (bs : Bytes n) : Bytes n :=
  ⟨bs.val.reverse, by rw [List.length_reverse]; exact bs.property⟩

end Bytes

/--
A 256-bit hash as its 32 bytes, in the order that SHA-256 outputs them.

This is also the order in which Core serializes a `uint256`.
A hash is compared and concatenated, not used as a number, so its type is bytes.
-/
abbrev Hash256 := Bytes 32

namespace Hash256

/-- The hash whose 32 bytes are all zero. Core's `COutPoint::SetNull` uses it (D4). -/
def zero : Hash256 := ⟨List.replicate 32 0, List.length_replicate⟩

/-- The list as a hash when it has exactly 32 bytes, and `none` otherwise. -/
def ofBytes? (bs : List UInt8) : Option Hash256 :=
  Bytes.ofListExact? bs

/-- The bytes of the hash in display order: reversed, as `base_blob::GetHex` of Core writes them (D11). -/
def displayBytes (h : Hash256) : List UInt8 :=
  h.val.reverse

/-- The hash whose display order is the list, when the list has exactly 32 bytes, and `none` otherwise. -/
def ofDisplayBytes? (bs : List UInt8) : Option Hash256 :=
  Bytes.ofListExact? bs.reverse

end Hash256

end DogeLib
