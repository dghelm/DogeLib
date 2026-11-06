module

public import DogeLib.Cryptography.Secp256k1.PubKey

/-!
# Public-key parser

Theorems about `parsePubKey`, the parser of libsecp256k1's `secp256k1_ec_pubkey_parse`.

- `parsePubKey_valid`: a parsed key is a point of the curve other than infinity, as `Ecdsa.verify` requires.
- `parsePubKey_hybrid_even` and `parsePubKey_hybrid_odd`: a hybrid key parses exactly when the uncompressed key with the same coordinates parses and the parity of `y` matches the first byte.

These theorems are statements about the definitions.
They do not say that `parsePubKey` matches Core, and they do not say which point an encoding denotes.
-/

@[expose] public section

namespace DogeLib.Cryptography.Secp256k1

/-- Negation does not change a square in `Fp`. -/
theorem Fp.neg_mul_neg (y : Fp) : -y * -y = y * y := by grind

/-- `decompress` gives a point of the curve other than infinity. -/
theorem decompress_valid {x : Fp} {odd : Bool} {q : Point} (h : decompress x odd = some q) :
    q ≠ .infinity ∧ q.isOnCurve = true := by
  unfold decompress at h
  cases hy : Fp.sqrt (x * x * x + b) with
  | none => simp [hy] at h
  | some y =>
    simp only [hy, Option.some.injEq] at h
    subst h
    refine ⟨by simp, ?_⟩
    have hsq : y * y = x * x * x + b := by
      unfold Fp.sqrt at hy
      by_cases hc : (x * x * x + b).pow ((Fp.modulus + 1) / 4) * (x * x * x + b).pow ((Fp.modulus + 1) / 4) =
          x * x * x + b
      · simp only [hc, ↓reduceIte, Option.some.injEq] at hy; subst hy; exact hc
      · simp [hc] at hy
    split <;> simp [Point.isOnCurve, Fp.neg_mul_neg, hsq]

/--
A key that parses gives a point of the curve other than infinity.
So `Ecdsa.verify` never rejects a parsed key by its key test.
-/
theorem parsePubKey_valid {key : List UInt8} {q : Point} (h : parsePubKey key = some q) :
    q ≠ .infinity ∧ q.isOnCurve = true := by
  unfold parsePubKey at h
  generalize readCoordinate ((key.drop 1).take 32) = ox at h
  generalize readCoordinate ((key.drop 33).take 32) = oy at h
  by_cases h33 : key.length = 33 ∧ (key.getD 0 0 = 0x02 ∨ key.getD 0 0 = 0x03)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h33)] at h
    cases ox with
    | none => cases h
    | some x => exact decompress_valid h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h33)] at h
    by_cases h65 : key.length = 65 ∧ (key.getD 0 0 = 0x04 ∨ key.getD 0 0 = 0x06 ∨ key.getD 0 0 = 0x07)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h65)] at h
      match ox, oy, h with
      | some x, some y, h =>
        simp only at h
        by_cases hc : (Point.affine x y).isOnCurve = true
        · have : q = .affine x y := by
            revert h; split <;> simp_all
          subst this
          exact ⟨by simp, hc⟩
        · revert h; split <;> simp_all
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h65)] at h; cases h

/--
A hybrid key with first byte `06` parses exactly when the uncompressed key with the same 64 coordinate bytes parses with an even `y`.
The point is then the same.
-/
theorem parsePubKey_hybrid_even (c : List UInt8) :
    parsePubKey (0x06 :: c) = (parsePubKey (0x04 :: c)).filter (fun q => !q.isOddY) := by
  unfold parsePubKey
  simp only [List.getD_cons_zero, List.length_cons, List.drop_succ_cons, List.drop_zero]
  by_cases hl : c.length + 1 = 65
  · simp only [hl]
    split <;> simp_all <;> split <;> simp_all [Option.filter]
    rename_i x y _ _
    cases ho : (Point.affine x y).isOddY <;> cases (Point.affine x y).isOnCurve <;> simp [ho]
  · simp [hl]

/--
A hybrid key with first byte `07` parses exactly when the uncompressed key with the same 64 coordinate bytes parses with an odd `y`.
The point is then the same.
-/
theorem parsePubKey_hybrid_odd (c : List UInt8) :
    parsePubKey (0x07 :: c) = (parsePubKey (0x04 :: c)).filter (fun q => q.isOddY) := by
  unfold parsePubKey
  simp only [List.getD_cons_zero, List.length_cons, List.drop_succ_cons, List.drop_zero]
  by_cases hl : c.length + 1 = 65
  · simp only [hl]
    split <;> simp_all <;> split <;> simp_all [Option.filter]
    rename_i x y _ _
    cases ho : (Point.affine x y).isOddY <;> cases (Point.affine x y).isOnCurve <;> simp [ho]
  · simp [hl]

end DogeLib.Cryptography.Secp256k1
