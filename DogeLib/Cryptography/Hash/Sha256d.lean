module

public import DogeLib.Cryptography.Hash.Sha256

/-!
# `Sha256d`

Double SHA-256: SHA-256 of the SHA-256 digest of a message.

Dogecoin Core computes it with `CHash256` in `src/hash.h` (SOURCES.md, D8).
`CHash256::Finalize` finishes one SHA-256, then hashes the 32-byte result again.
Transaction IDs, block header hashes and legacy signature hashes all use it.

The result is the 32 bytes of the digest in the order SHA-256 produces them.
Dogecoin Core displays a hash with those bytes reversed (`base_blob::GetHex` in `src/uint256.cpp`).
That display order is not defined here.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Sha256d

/-- Double SHA-256 of `message`: `CHash256` of Dogecoin Core. -/
def hash (message : ByteArray) : ByteArray :=
  Sha256.hash (Sha256.hash message)

end DogeLib.Cryptography.Hash.Sha256d
