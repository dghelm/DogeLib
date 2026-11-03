module

public import DogeLib.Cryptography.Hash.Sha256d
public import DogeLib.Cryptography.Proofs.Hash.Sha256

/-!
# Proofs: `Hash.Sha256d`

Double SHA-256 gives 32 bytes, and agrees with the FIPS 180-4 model of SHA-256 applied twice.

Checked claims:

- `size_hash`: the digest has 32 bytes.
- `hash_eq_spec`: on every message shorter than 2^61 bytes, `Sha256d.hash` equals `Sha256.Spec.hash` applied twice.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Sha256d

/-- The double SHA-256 digest of every message has 32 bytes. -/
@[simp] theorem size_hash (message : ByteArray) : (hash message).size = 32 := by
  simp [hash]

/-- On every message shorter than 2^61 bytes, double SHA-256 equals the FIPS 180-4 model of SHA-256 applied twice.
The inner digest has 32 bytes, so the outer application needs no hypothesis of its own. -/
theorem hash_eq_spec (message : ByteArray) (admitted : message.size < 2 ^ 61) :
    hash message = Sha256.Spec.hash (Sha256.Spec.hash message) := by
  have inner : (Sha256.hash message).size < 2 ^ 61 := by simp
  rw [hash, Sha256.hash_eq_spec _ inner, Sha256.hash_eq_spec _ admitted]

end DogeLib.Cryptography.Hash.Sha256d
