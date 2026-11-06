module

public import DogeLib.Cryptography.Secp256k1.Ecdsa

/-!
# ECDSA known answer

Wycheproof P1363 case 1 at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9` accepts this signature.
The input and expectation come through EthLib `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, under CC0 1.0 for code and Apache 2.0 for vector data.
The vector licence is in `tests/cryptography/secp256k1/LICENSE`.
This file states the vector on coordinates and scalars without a public-key parser.

## Core's final test

These theorems compare `verify` with `secp256k1_ecdsa_sig_verify` of Dogecoin Core's bundled libsecp256k1 (`src/ecdsa_impl.h`, lines 207 to 275, at `e0a1c157791544e818c901bd9341896965afbf9d`).

- `verify_r_zero` and `verify_s_zero`: a zero R or S gives `false`, as Core's lines 216 to 218 do.
- `xmod_eq_iff`: for an `x` below `p` and an `r` below `n`, `x mod n = r` holds exactly when `x = r`, or `r + n < p` and `x = r + n`.
  Core's lines 244 to 272 test those two cases in Jacobian coordinates, so they test what `verify` tests on the affine `x`.
- `verify_of_valid`: for `0 < r < n`, `0 < s < n` and a key of the curve other than infinity, `verify` is the test on `Point.mulAdd`.

No theorem here says that `Point.mulAdd` computes Core's `secp256k1_ecmult`, or that `Fn.inv` gives the inverse mod `n`.
SOUNDNESS.md records that gap.
-/

@[expose] public section

namespace DogeLib.Cryptography.Secp256k1.Ecdsa

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Wycheproof P1363 case 1 verifies with the stated coordinates, digest bytes, R and S. -/
theorem wycheproof_p1363_1 :
    verify (.affine 0xb838ff44e5bc177bf21189d0766082fc9d843226887fc9760371100b7ee20a6f 0xf0c9d75bfba7b31a6bca1974496eeb56de357071955d83c4b1badaa0b21832e9)
      ⟨[0xbb, 0x5a, 0x52, 0xf4, 0x2f, 0x9c, 0x92, 0x61, 0xed, 0x43, 0x61, 0xf5, 0x94, 0x22, 0xa1, 0xe3, 0x00, 0x36, 0xe7, 0xc3, 0x2b, 0x27, 0x0c, 0x88, 0x07, 0xa4, 0x19, 0xfe, 0xca, 0x60, 0x50, 0x23], by decide⟩
      0x813ef79ccefa9a56f7ba805f0e478584fe5f0dd5f567bc09b5123ccbc9832365 0x900e75ad233fcc908509dbff5922647db37c21f4afd3203ae8dc4ae7794b0f87 = true := by
  decide +kernel

/-- A zero R gives `false`, for every key, digest and S. -/
theorem verify_r_zero (q : Point) (hash : Hash256) (s : Nat) : verify q hash 0 s = false := by
  simp [verify]

/-- A zero S gives `false`, for every key, digest and R. -/
theorem verify_s_zero (q : Point) (hash : Hash256) (r : Nat) : verify q hash r 0 = false := by
  unfold verify; split <;> simp

/-- `p` is less than `2 n`, so an `x` below `p` is at most one multiple of `n` above its remainder. -/
theorem modulus_lt_two_mul : Fp.modulus < 2 * Fn.modulus := by decide

/--
For `x < p` and `r < n`: `x mod n = r` exactly when `x = r`, or `r + n < p` and `x = r + n`.
`secp256k1_ecdsa_sig_verify` tests these two cases, because `p < 2 n`.
-/
theorem xmod_eq_iff {x r : Nat} (hx : x < Fp.modulus) (hr : r < Fn.modulus) :
    x % Fn.modulus = r ↔ x = r ∨ (r + Fn.modulus < Fp.modulus ∧ x = r + Fn.modulus) := by
  have h2 := modulus_lt_two_mul
  have hn : 0 < Fn.modulus := by decide
  constructor
  · intro h
    by_cases hlt : x < Fn.modulus
    · left; rw [Nat.mod_eq_of_lt hlt] at h; exact h
    · right
      have hsub : x % Fn.modulus = x - Fn.modulus := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro (rfl | ⟨_, rfl⟩)
    · exact Nat.mod_eq_of_lt hr
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/--
For `0 < r < n`, `0 < s < n` and a key `q` of the curve other than infinity, `verify` is the test on `u1 G + u2 Q`.
Here `e` is the digest reduced mod `n`, `u1 = e s⁻¹` and `u2 = r s⁻¹` with `Fn.inv`.
The result is `false` when the sum is infinity, and otherwise whether its `x` reduced mod `n` is `r`.
-/
theorem verify_of_valid {q : Point} {hash : Hash256} {r s : Nat} (hr : 0 < r ∧ r < Fn.modulus)
    (hs : 0 < s ∧ s < Fn.modulus) (hq : q ≠ .infinity ∧ q.isOnCurve = true) :
    verify q hash r s =
      match Point.mulAdd ((Fin.ofNat _ (hashToInt hash) : Fn) * Fn.inv ⟨s, hs.2⟩) .generator
          ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q with
      | .infinity => false
      | .affine x _ => x.val % Fn.modulus == r := by
  simp only [verify, hr, hs, hq, and_self, dite_true, ite_true, ne_eq, not_false_eq_true]
  rfl

end DogeLib.Cryptography.Secp256k1.Ecdsa
