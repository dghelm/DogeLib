module

public import DogeLib.Cryptography.Hash.Ripemd160
public import DogeLib.Cryptography.Hash.Sha256

/-!
# `Hash160`

Hash160 computes RIPEMD-160 of the SHA-256 digest of a message.
Dogecoin Core defines this composition in `CHash160::Finalize`, `src/hash.h`, at the compatibility pin in SOURCES.md.
The input is an arbitrary message of whole bytes.
The result is twenty bytes in digest output order, without reversal or a length prefix.
The operation has no network, activation or serialization-mode parameter.
Both component hashes reduce the encoded bit length modulo 2^64.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Hash160

/-- Hash160 of `message`, following Core's `CHash160::Finalize`. -/
def hash (message : ByteArray) : ByteArray :=
  Ripemd160.hash (Sha256.hash message)

end DogeLib.Cryptography.Hash.Hash160

namespace DogeLib.Cryptography.Hash

/-- Hash160 of a message of whole bytes, in digest output order. -/
@[inline] def hash160 (message : ByteArray) : ByteArray := Hash160.hash message

end DogeLib.Cryptography.Hash
