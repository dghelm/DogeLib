module

public import DogeLib.Cryptography.Proofs.Hash.HmacSpec

/-!
# PBKDF2 list model

Adapted from pyca/verified-garbage `lean/VerifiedGarbage/Spec/Pbkdf2.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes imports, namespaces and documentation, and spells VG's `Byte` as `BitVec 8`.
It retains the list representation and the definitions.
The HMAC instance uses DogeLib's executable SHA-256 through the existing list model.

RFC 8018 §5.2 requires positive iteration counts and output lengths.
This total model also admits zero iterations as one iteration, and zero output bytes as an empty result.
Only output lengths above `(2^32 - 1) * hLen` give `none`.
The hash function carries no cryptographic assumption.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Pbkdf2.Spec

/-- `INT (i)`: a four-octet encoding of the integer `i`, most significant
octet first (§5.2, step 3). -/
def int (i : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 (i / 2 ^ 24), BitVec.ofNat 8 (i / 2 ^ 16), BitVec.ofNat 8 (i / 2 ^ 8), BitVec.ofNat 8 i]

/-- Bytewise XOR, truncated to the shorter input when the lengths differ. -/
def xorBytes (a b : List (BitVec 8)) : List (BitVec 8) := List.zipWith (· ^^^ ·) a b

variable (prf : List (BitVec 8) → List (BitVec 8))

/-- Apply `n` further PRF steps to `u`, and XOR each result into `t`.
The PRF already includes the password. -/
def iterate : Nat → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)
  | 0, _, t => t
  | n + 1, u, t => let u' := prf u; iterate n u' (xorBytes t u')

/-- Output block `Tᵢ` of RFC 8018 §5.2, step 3, with zero iterations treated as one. -/
def F (s : List (BitVec 8)) (c i : Nat) : List (BitVec 8) :=
  let u₁ := prf (s ++ int i)
  iterate prf (c - 1) u₁ u₁

/-- Concatenate output blocks and take `dkLen` bytes, or reject a length above `(2^32 - 1) * hLen`.
For a PRF with `hLen`-byte results, the accepted result has `dkLen` bytes. -/
def pbkdf2 (hLen : Nat) (s : List (BitVec 8)) (c dkLen : Nat) : Option (List (BitVec 8)) :=
  if (2 ^ 32 - 1) * hLen < dkLen then none
  else
    let l := (dkLen + hLen - 1) / hLen
    some (((List.range l).flatMap fun k => F prf s c (k + 1)).take dkLen)

/-- PBKDF2 with the HMAC-SHA-256 list model, keyed with password `p`, and `hLen = 32`. -/
def pbkdf2HmacSha256 (p s : List (BitVec 8)) (c dkLen : Nat) : Option (List (BitVec 8)) :=
  pbkdf2 (Hmac.Spec.hmac Hmac.Spec.sha256 p) 32 s c dkLen

end DogeLib.Cryptography.Hash.Pbkdf2.Spec
