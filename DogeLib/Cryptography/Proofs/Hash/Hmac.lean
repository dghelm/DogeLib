module

public import DogeLib.Cryptography.Proofs.Hash.Sha256
public import DogeLib.Cryptography.Hash.Hmac
public import DogeLib.Cryptography.Proofs.Hash.HmacSpec

/-!
# Proofs: HMAC-SHA-256

Every HMAC-SHA-256 tag is 32 bytes long.

The key block follows step (1) of [RFC 2104 §2](https://www.rfc-editor.org/rfc/rfc2104#section-2).

A key of at most `B = 64` bytes is padded with zero bytes to `B` bytes.

A longer key is hashed first, and its 32-byte hash is padded the same way.

So zero bytes appended to a short key do not change the tag.

The pads act byte by byte, as steps (2) and (5) of the RFC XOR the key block with `ipad` and `opad`.
Adapted from EthLib `EthLib/Cryptography/Proofs/Hash/Hmac.lean` at
`bb6dfe55198243682bc2eaf94611af2dbce1be6f`, under CC0 1.0.
The adaptation changes the namespace and documentation.
It adds byte conversions, agreement with the list model, and the bounded FIPS corollary.
The SHA-256 API requires no code changes.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Hmac

/-- Every tag is 32 bytes long, whatever the key and the message. -/
@[simp] theorem hmac_size (key message : ByteArray) : (hmac key message).size = 32 :=
  Sha256.hash_size _

/-! ## The key block -/

/-- A key of at most `B` bytes is padded with zero bytes to `B` bytes. -/
theorem blockKey_of_le {key : ByteArray} (h : key.size ≤ BLOCK_SIZE) :
    blockKey key = key ++ ⟨Array.replicate (BLOCK_SIZE - key.size) 0⟩ := by
  rw [blockKey, ite_eq_right (Nat.not_lt.mpr h)]

/-- A key longer than `B` bytes is hashed, and its hash is padded with zero bytes to `B` bytes. -/
theorem blockKey_of_lt {key : ByteArray} (h : BLOCK_SIZE < key.size) :
    blockKey key = Sha256.hash key ++ ⟨Array.replicate (BLOCK_SIZE - 32) 0⟩ := by
  rw [blockKey, ite_eq_left h, Sha256.hash_size]

/-- The key block has `B = 64` bytes. -/
theorem blockKey_size (key : ByteArray) : (blockKey key).size = BLOCK_SIZE := by
  by_cases h : BLOCK_SIZE < key.size
  · rw [blockKey_of_lt h, ByteArray.size_append, Sha256.hash_size]
    rfl
  · have h := Nat.not_lt.mp h
    rw [blockKey_of_le h, ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate] at h ⊢
    omega

/-- Zero bytes appended to a key of at most `B` bytes leave the key block unchanged. -/
theorem blockKey_append_zeros {key : ByteArray} {n : Nat} (h : key.size + n ≤ BLOCK_SIZE) :
    blockKey (key ++ ⟨Array.replicate n 0⟩) = blockKey key := by
  have h' : (key ++ ⟨Array.replicate n 0⟩).size ≤ BLOCK_SIZE := by
    rw [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate] at h ⊢
    omega
  rw [blockKey_of_le h', blockKey_of_le (by omega), ByteArray.append_assoc]
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate] at h ⊢
  rw [Array.replicate_append_replicate]
  congr 1
  omega

/-- Zero bytes appended to a key of at most `B` bytes leave the tag unchanged. -/
theorem hmac_append_zeros {key : ByteArray} {n : Nat} (h : key.size + n ≤ BLOCK_SIZE)
    (message : ByteArray) : hmac (key ++ ⟨Array.replicate n 0⟩) message = hmac key message := by
  unfold hmac
  rw [blockKey_append_zeros h]

/-! ## The pads -/

/-- XOR with a pad keeps the length. -/
theorem xorPad_size (block : ByteArray) (pad : UInt8) : (xorPad block pad).size = block.size :=
  Array.size_map ..

/-- XOR with a pad acts byte by byte. -/
theorem xorPad_getElem {block : ByteArray} {pad : UInt8} {i : Nat} (h : i < block.size) :
    (xorPad block pad)[i]'(by rw [xorPad_size]; exact h) = block[i] ^^^ pad :=
  Array.getElem_map ..

/-! ## Agreement with the list model -/

/-- Converting a byte array to the model and back preserves every byte. -/
@[simp] theorem fromBytes_toBytes (b : ByteArray) : Spec.fromBytes (Spec.toBytes b) = b := by
  cases b
  simp [Spec.fromBytes, Spec.toBytes, List.map_map, Function.comp_def]

/-- Converting a model byte list to an array and back preserves every byte. -/
@[simp] theorem toBytes_fromBytes (b : List (BitVec 8)) :
    Spec.toBytes (Spec.fromBytes b) = b := by
  simp [Spec.fromBytes, Spec.toBytes, List.map_map, Function.comp_def]

/-- Conversion preserves the byte count. -/
@[simp] theorem toBytes_length (b : ByteArray) : (Spec.toBytes b).length = b.size := by
  simp only [Spec.toBytes, List.length_map, Array.length_toList]
  rfl

/-- Conversion preserves concatenation in byte order. -/
@[simp] theorem toBytes_append (a b : ByteArray) :
    Spec.toBytes (a ++ b) = Spec.toBytes a ++ Spec.toBytes b := by
  simp [Spec.toBytes, ByteArray.data_append]

/-- Conversion preserves each XOR with a pad byte. -/
@[simp] theorem toBytes_xorPad (b : ByteArray) (pad : UInt8) :
    Spec.toBytes (xorPad b pad) = Spec.xorPad (Spec.toBytes b) pad.toBitVec := by
  simp [Spec.toBytes, xorPad, Spec.xorPad, List.map_map, UInt8.toBitVec_xor]

/-- Conversion preserves a sequence of zero bytes. -/
@[simp] theorem toBytes_zeros (n : Nat) :
    Spec.toBytes ⟨Array.replicate n 0⟩ = List.replicate n 0 := by
  simp only [Spec.toBytes, Array.toList_replicate, List.map_replicate]
  rfl

/-- The model's SHA-256 instance preserves the executable digest through conversion. -/
@[simp] theorem sha256_toBytes (b : ByteArray) :
    Spec.sha256.hash (Spec.toBytes b) = Spec.toBytes (Sha256.hash b) := by
  simp only [Spec.sha256, fromBytes_toBytes]

/-- Conversion preserves the normalized key for every key length. -/
theorem blockKey_eq_spec (key : ByteArray) :
    Spec.toBytes (blockKey key) = Spec.blockKey Spec.sha256 (Spec.toBytes key) := by
  have bs : Spec.sha256.blockSize = 64 := rfl
  by_cases h : 64 < key.size
  · rw [blockKey_of_lt h]
    simp only [Spec.blockKey, bs, toBytes_length, ite_eq_left h, sha256_toBytes,
      toBytes_append, toBytes_zeros, Sha256.hash_size, BLOCK_SIZE]
  · rw [blockKey_of_le (Nat.le_of_not_gt h)]
    simp only [Spec.blockKey, bs, toBytes_length, ite_eq_right h,
      toBytes_append, toBytes_zeros, BLOCK_SIZE]


/-- For every key and message, the executable equals the list model using executable SHA-256. -/
theorem hmac_eq_spec (key message : ByteArray) :
    Spec.toBytes (hmac key message) =
      Spec.hmac Spec.sha256 (Spec.toBytes key) (Spec.toBytes message) := by
  unfold hmac Spec.hmac Spec.hmacBlockKey
  rw [← blockKey_eq_spec]
  change Spec.toBytes (Sha256.hash _) = Spec.sha256.hash _
  have inner : Spec.xorPad (Spec.toBytes (blockKey key)) Spec.ipad ++ Spec.toBytes message =
      Spec.toBytes (xorPad (blockKey key) IPAD ++ message) := by
    rw [toBytes_append, toBytes_xorPad]
    rfl
  rw [inner, sha256_toBytes]
  have outer : Spec.xorPad (Spec.toBytes (blockKey key)) Spec.opad ++
      Spec.toBytes (Sha256.hash (xorPad (blockKey key) IPAD ++ message)) =
      Spec.toBytes (xorPad (blockKey key) OPAD ++
        Sha256.hash (xorPad (blockKey key) IPAD ++ message)) := by
    rw [toBytes_append, toBytes_xorPad]
    rfl
  rw [outer, sha256_toBytes]

/-- The list model instantiated with the FIPS 180-4 SHA-256 model. -/
def Spec.fipsSha256 : Spec.HashFunction :=
  ⟨64, fun b => Spec.toBytes (Sha256.Spec.hash (Spec.fromBytes b))⟩

/-- Below the SHA-256 byte bound, the FIPS instance equals the executable instance. -/
theorem fipsSha256_toBytes (b : ByteArray) (h : b.size < 2 ^ 61) :
    Spec.fipsSha256.hash (Spec.toBytes b) = Spec.toBytes (Sha256.hash b) := by
  simp only [Spec.fipsSha256, fromBytes_toBytes, ← Sha256.hash_eq_spec b h]

/-- A key below the SHA-256 byte bound has the same key block in the FIPS instance. -/
theorem blockKey_eq_fips (key : ByteArray) (h : key.size < 2 ^ 61) :
    Spec.blockKey Spec.fipsSha256 (Spec.toBytes key) = Spec.toBytes (blockKey key) := by
  rw [blockKey_eq_spec]
  have bs : Spec.fipsSha256.blockSize = Spec.sha256.blockSize := rfl
  simp only [Spec.blockKey, bs, toBytes_length]
  split
  · rw [fipsSha256_toBytes key h, sha256_toBytes]
  · rfl

/-- For keys below 2^61 bytes and messages with `64 + size < 2^61`, HMAC equals the FIPS-based list model. -/
theorem hmac_eq_fips (key message : ByteArray) (keyBound : key.size < 2 ^ 61)
    (messageBound : 64 + message.size < 2 ^ 61) :
    Spec.toBytes (hmac key message) =
      Spec.hmac Spec.fipsSha256 (Spec.toBytes key) (Spec.toBytes message) := by
  have innerBound : (xorPad (blockKey key) IPAD ++ message).size < 2 ^ 61 := by
    simpa only [ByteArray.size_append, xorPad_size, blockKey_size, BLOCK_SIZE] using messageBound
  have outerBound : (xorPad (blockKey key) OPAD ++
      Sha256.hash (xorPad (blockKey key) IPAD ++ message)).size < 2 ^ 61 := by
    rw [ByteArray.size_append, xorPad_size, blockKey_size, Sha256.hash_size]
    decide
  unfold Spec.hmac Spec.hmacBlockKey
  rw [blockKey_eq_fips key keyBound]
  have inner : Spec.xorPad (Spec.toBytes (blockKey key)) Spec.ipad ++ Spec.toBytes message =
      Spec.toBytes (xorPad (blockKey key) IPAD ++ message) := by
    rw [toBytes_append, toBytes_xorPad]
    rfl
  rw [inner, fipsSha256_toBytes _ innerBound]
  have outer : Spec.xorPad (Spec.toBytes (blockKey key)) Spec.opad ++
      Spec.toBytes (Sha256.hash (xorPad (blockKey key) IPAD ++ message)) =
      Spec.toBytes (xorPad (blockKey key) OPAD ++
        Sha256.hash (xorPad (blockKey key) IPAD ++ message)) := by
    rw [toBytes_append, toBytes_xorPad]
    rfl
  rw [outer, fipsSha256_toBytes _ outerBound]
  rfl

end DogeLib.Cryptography.Hash.Hmac
