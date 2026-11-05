module

public import DogeLib.Cryptography.Hash.Hash160
public import DogeLib.Cryptography.Proofs.Hash.Ripemd160

/-!
# Proofs: `Hash.Hash160`

Hash160 gives twenty bytes and is the composition of the two executable hash definitions.
These theorems do not relate RIPEMD-160 to an independent model or prove correspondence to Core.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Hash160

/-- The Hash160 digest of every message has twenty bytes. -/
@[simp] theorem size_hash (message : ByteArray) : (hash message).size = 20 := by
  simp [hash]

/-- For every message, Hash160 is RIPEMD-160 of its SHA-256 digest. -/
theorem hash_eq_composition (message : ByteArray) :
    hash message = Ripemd160.hash (Sha256.hash message) := rfl

end DogeLib.Cryptography.Hash.Hash160
