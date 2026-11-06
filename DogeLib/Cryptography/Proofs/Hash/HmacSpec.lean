module

public import DogeLib.Cryptography.Hash.Sha256

/-!
# HMAC model

Adapted from pyca/verified-garbage `lean/VerifiedGarbage/Spec/Hmac.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes the namespace and documentation, retains the list and bit-vector representation,
and replaces the hash instances with DogeLib's SHA-256.
The construction follows RFC 2104 §2 and FIPS 198-1 §4.
The hash function is a parameter, so this model assumes no cryptographic property.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Hmac.Spec

/-- A hash function, as HMAC uses it: its input block size `B` in bytes, and
the digest of a message. -/
structure HashFunction where
  /-- The input block size in bytes. -/
  blockSize : Nat
  /-- The digest of a byte sequence. -/
  hash : List (BitVec 8) → List (BitVec 8)

/-- The inner pad byte `0x36` of FIPS 198-1 §2.3. -/
def ipad : BitVec 8 := 0x36
/-- The outer pad byte `0x5c` of FIPS 198-1 §2.3. -/
def opad : BitVec 8 := 0x5c

/-- `k ⊕ (pad repeated)`. -/
def xorPad (k : List (BitVec 8)) (pad : BitVec 8) : List (BitVec 8) := k.map (· ^^^ pad)

variable (H : HashFunction)

/-- Steps 1–3 of FIPS 198-1 §4 normalize the key by hashing long keys and appending zeros.
The result has `B` bytes when the selected key or digest has at most `B` bytes. -/
def blockKey (key : List (BitVec 8)) : List (BitVec 8) :=
  let k := if H.blockSize < key.length then H.hash key else key
  k ++ List.replicate (H.blockSize - k.length) 0

/-- Steps 4–9, from `K₀`: `H((K₀ ⊕ opad) ‖ H((K₀ ⊕ ipad) ‖ text))`. -/
def hmacBlockKey (k0 text : List (BitVec 8)) : List (BitVec 8) :=
  H.hash (xorPad k0 opad ++ H.hash (xorPad k0 ipad ++ text))

/-- `HMAC(K, text)`. -/
def hmac (key text : List (BitVec 8)) : List (BitVec 8) := hmacBlockKey H (blockKey H key) text

/-- A byte array represented as a list of eight-bit vectors, in byte order. -/
def toBytes (b : ByteArray) : List (BitVec 8) := b.data.toList.map UInt8.toBitVec

/-- A list of eight-bit vectors represented as a byte array, in byte order. -/
def fromBytes (b : List (BitVec 8)) : ByteArray := ⟨(b.map UInt8.ofBitVec).toArray⟩

/-- SHA-256 with byte conversions and the SHA-256 block size of 64 bytes. -/
def sha256 : HashFunction := ⟨64, fun b => toBytes (Sha256.hash (fromBytes b))⟩

end DogeLib.Cryptography.Hash.Hmac.Spec
