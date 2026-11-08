module

public import DogeLib.Work.ChainWork

/-!
# Properties of the block proof

- `setCompact_value_ne_max`: no compact value decodes to 2^256 - 1.
  So the divisor `target + 1` of `GetBlockProof` is never zero, and Core's division never throws there.
- The target `blockProof_eq` of design record 0008, section 11: for a compact value whose target is not negative, does not overflow and is not zero, `blockProof` is `⌊2^256 / (t + 1)⌋` for its target `t`.
  Otherwise it is 0.
-/

@[expose] public section

namespace DogeLib.Work

open ArithUint256

/--
For every 32-bit compact value, the value that `SetCompact` stores is not 2^256 - 1.
For `nSize` of 3 or less, the value has at most 23 bits.
Otherwise it is the mantissa shifted left by at least one byte, modulo 2^256, so it is even.
The theorem holds with or without an overflow.
-/
theorem setCompact_value_ne_max (c : UInt32) : (setCompact c).value.val ≠ 2 ^ 256 - 1 := by
  have hword : c.toNat &&& 0x007fffff < 2 ^ 23 := by
    rw [show (0x007fffff : Nat) = 2 ^ 23 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  by_cases small : c.toNat >>> 24 ≤ 3
  · simp only [setCompact, small, ite_true, ofNat]
    have := Nat.shiftRight_le (c.toNat &&& 0x007fffff) (8 * (3 - c.toNat >>> 24))
    have : (c.toNat &&& 0x007fffff) >>> (8 * (3 - c.toNat >>> 24)) % 2 ^ 256 < 2 ^ 23 :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    intro h
    rw [h] at this
    simp at this
  · simp only [setCompact, small, ite_false, shiftLeft, ofNat, Nat.shiftLeft_eq]
    intro h
    have even : (c.toNat &&& 0x007fffff) % 2 ^ 256 * 2 ^ (8 * (c.toNat >>> 24 - 3)) % 2 ^ 256 % 2 = 0 := by
      rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 1 ≤ 256))]
      apply Nat.mod_eq_zero_of_dvd
      exact Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 8 * (c.toNat >>> 24 - 3))) _
    rw [h] at even
    simp at even

/--
The target `blockProof_eq` of design record 0008, section 11, for every 32-bit compact value `nBits`.
Let `t` be the target that `SetCompact` decodes from `nBits`.
If `SetCompact` reports no sign and no overflow, and `t` is not zero, `blockProof nBits` is `⌊2^256 / (t + 1)⌋`.
Otherwise it is 0.
-/
theorem blockProof_eq (nBits : UInt32) :
    (blockProof nBits).val =
      if (setCompact nBits).fNegative = false ∧ (setCompact nBits).fOverflow = false ∧
          (setCompact nBits).value.val ≠ 0 then
        2 ^ 256 / ((setCompact nBits).value.val + 1)
      else 0 := by
  have hmax := setCompact_value_ne_max nBits
  unfold blockProof
  generalize setCompact nBits = r at hmax ⊢
  obtain ⟨⟨t, ht⟩, neg, over⟩ := r
  simp only at hmax ⊢
  cases neg <;> cases over <;> simp
  by_cases t0 : t = 0
  · simp [t0]
  · have one : ((1 : ArithUint256) : Nat) = 1 := rfl
    have succ : ((⟨t, ht⟩ + 1 : ArithUint256) : Nat) = t + 1 := by
      rw [Fin.val_add, one]
      exact Nat.mod_eq_of_lt (by simp only; omega)
    have hne : (⟨t, ht⟩ + 1 : ArithUint256) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      rw [succ] at this
      simp at this
    simp only [t0, ite_false, hne, dite_false]
    rw [Fin.val_add, one]
    simp only [div, complement, succ]
    have pos : 0 < t + 1 := by omega
    have eq : 2 ^ 256 / (t + 1) = (2 ^ 256 - (t + 1)) / (t + 1) + 1 :=
      Nat.div_eq_sub_div pos (by omega)
    have small : 2 ^ 256 / (t + 1) < 2 ^ 256 :=
      Nat.div_lt_self (Nat.two_pow_pos 256) (by omega)
    rw [show 2 ^ 256 - 1 - t = 2 ^ 256 - (t + 1) by omega, ← eq, Nat.mod_eq_of_lt small]

end DogeLib.Work
