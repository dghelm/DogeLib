module

public import DogeLib.Work.ArithUint256

/-!
# Proofs: `ArithUint256`

Properties of the compact encoding of `arith_uint256` (`SetCompact` and `GetCompact`, arith_uint256.cpp lines 204-245).

The main results, for every 256-bit value `a`:

```text
setCompact_getCompact_le             SetCompact(GetCompact(a)) <= a
setCompact_getCompact_flags          SetCompact(GetCompact(a)) reports no sign and no overflow
getCompact_setCompact_getCompact     GetCompact(SetCompact(GetCompact(a))) = GetCompact(a)
setCompact_getCompact_of_lt          a < 2^23 -> SetCompact(GetCompact(a)) = a
getCompact_assertions                the two asserts of GetCompact never fail
```

`getCompact_setCompact_iff` says which 32-bit compacts survive decoding and encoding again: those that `GetCompact` produces.
Core's own tests contain compacts that do not survive, and three theorems record them.
`setCompact_fOverflow` says that the overflow flag is set exactly when the encoded number does not fit in 256 bits.

The proofs reason about `normal`, the size and mantissa that `GetCompact` packs, and split on the byte length of `a`.
-/

@[expose] public section

namespace DogeLib.Work.ArithUint256

/-- A power of 256 is a power of 2 with eight times the exponent. -/
theorem pow256 (k : Nat) : 256 ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

/-- `nSize` of `GetCompact` (line 226): the length of `a` in bytes, `(bits() + 7) / 8`. -/
def byteLength (a : ArithUint256) : Nat := (bits a + 7) / 8

/-- The byte length is zero exactly for zero. -/
theorem byteLength_eq_zero_iff (a : ArithUint256) : byteLength a = 0 ↔ a.val = 0 := by
  unfold byteLength bits; split <;> omega

/-- A nonzero value of byte length `n` lies in `[256^(n-1), 256^n)`. -/
theorem byteLength_bounds (a : ArithUint256) (h : a.val ≠ 0) :
    256 ^ (byteLength a - 1) ≤ a.val ∧ a.val < 256 ^ byteLength a := by
  unfold byteLength bits
  simp only [h, ite_false, pow256]
  constructor
  · exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.log2_self_le h)
  · exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) (by omega))

/-- A nonzero value in `[256^(n-1), 256^n)` has byte length `n`. -/
theorem byteLength_eq (a : ArithUint256) (n : Nat) (h : a.val ≠ 0)
    (lo : 256 ^ (n - 1) ≤ a.val) (hi : a.val < 256 ^ n) : byteLength a = n := by
  unfold byteLength bits
  simp only [h, ite_false]
  rw [pow256] at lo hi
  have l1 := (Nat.le_log2 h).mpr lo
  have l2 := (Nat.log2_lt h).mpr hi
  omega

/-- A 256-bit value has at most 32 bytes. -/
theorem byteLength_le (a : ArithUint256) : byteLength a ≤ 32 := by
  unfold byteLength bits
  split
  · omega
  · have := (Nat.log2_lt (n := a.val) (k := 256) (by omega)).mpr a.isLt
    omega

/-- A mask with one bit `i` is nonzero exactly when bit `i` is set. -/
theorem and_two_pow_ne_zero (x i : Nat) : (x &&& 2 ^ i != 0) = x.testBit i := by
  cases hb : x.testBit i
  · have : x &&& 2 ^ i = 0 := Nat.eq_of_testBit_eq fun j => by
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : i = j
      · subst hj; simp [hb]
      · simp [hj]
    simp [this]
  · have : (x &&& 2 ^ i).testBit i = true := by simp [Nat.testBit_and, hb]
    have ne : x &&& 2 ^ i ≠ 0 := fun h0 => by rw [h0, Nat.zero_testBit] at this; cases this
    simp [ne]

/-- The sign-bit test `x & 0x00800000` of the compact encoding, as arithmetic on `x`. -/
theorem sign_bit (x : Nat) : (x &&& 0x00800000 != 0) = decide (x / 2 ^ 23 % 2 = 1) := by
  rw [show (0x00800000 : Nat) = 2 ^ 23 by decide, and_two_pow_ne_zero, Nat.testBit_eq_decide_div_mod_eq]

/-- The mantissa that `GetCompact` computes before the sign-bit adjustment (lines 227-233): the top three bytes of `a`. -/
def mantissa0 (a : ArithUint256) : Nat :=
  if byteLength a ≤ 3 then a.val * 256 ^ (3 - byteLength a) else a.val / 256 ^ (byteLength a - 3)

/-- The pair `(nSize, nCompact)` that `GetCompact` holds at its assertions (line 240), after the sign-bit adjustment of lines 236-239. -/
def normal (a : ArithUint256) : Nat × Nat :=
  if 2 ^ 23 ≤ mantissa0 a then (byteLength a + 1, mantissa0 a / 256) else (byteLength a, mantissa0 a)

/-- `256^n` splits off its last three bytes. -/
private theorem pow_split {n : Nat} (h : 3 ≤ n) : 256 ^ n = 256 ^ (n - 3) * 16777216 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp [Nat.pow_add]

/-- `256^(n-1)` splits off two bytes past `256^(n-3)`. -/
private theorem pow_split' {n : Nat} (h : 3 < n) : 256 ^ (n - 1) = 256 ^ (n - 3) * 65536 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp [Nat.pow_succ, Nat.mul_assoc]

/-- For `n ≤ 3`, `256^n * 256^(3-n) = 2^24`. -/
private theorem pow_split_small {n : Nat} (h : n ≤ 3) : 256 ^ n * 256 ^ (3 - n) = 16777216 := by
  rw [← Nat.pow_add, show n + (3 - n) = 3 by omega]

/-- The mantissa before adjustment has 24 bits, at least 17 of them significant for a nonzero value, and is zero for zero. -/
theorem mantissa0_bounds (a : ArithUint256) :
    mantissa0 a < 2 ^ 24 ∧ (a.val ≠ 0 → 2 ^ 16 ≤ mantissa0 a) ∧ (a.val = 0 → mantissa0 a = 0) := by
  unfold mantissa0
  by_cases h0 : a.val = 0
  · simp [h0]
  have ⟨lo, hi⟩ := byteLength_bounds a h0
  have hpos : byteLength a ≠ 0 := fun h => h0 ((byteLength_eq_zero_iff a).mp h)
  refine ⟨?_, fun _ => ?_, fun h => absurd h h0⟩
  · split
    · rename_i hn
      have := pow_split_small hn
      have : a.val * 256 ^ (3 - byteLength a) < 256 ^ byteLength a * 256 ^ (3 - byteLength a) :=
        Nat.mul_lt_mul_of_pos_right hi (Nat.pow_pos (by decide))
      omega
    · rename_i hn
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
      rw [pow_split (by omega)] at hi
      simpa [Nat.mul_comm] using hi
  · split
    · rename_i hn
      have hk : 256 ^ (byteLength a - 1) * 256 ^ (3 - byteLength a) = 65536 := by
        rw [← Nat.pow_add, show byteLength a - 1 + (3 - byteLength a) = 2 by omega]
      have : 256 ^ (byteLength a - 1) * 256 ^ (3 - byteLength a) ≤ a.val * 256 ^ (3 - byteLength a) :=
        Nat.mul_le_mul_right _ lo
      omega
    · rename_i hn
      rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))]
      rw [pow_split' (by omega)] at lo
      simpa [Nat.mul_comm] using lo

/-- `GetCompact(false)` packs the normal form: the mantissa in the low bits and `nSize` in the top byte. -/
theorem getCompact_eq_normal (a : ArithUint256) :
    getCompact a = UInt32.ofNat ((normal a).2 + (normal a).1 * 2 ^ 24) := by
  obtain ⟨m0lt, -, -⟩ := mantissa0_bounds a
  have pre : (if (bits a + 7) / 8 ≤ 3 then (getLow64 a <<< (8 * (3 - (bits a + 7) / 8))) % 2 ^ 64 % 2 ^ 32
      else getLow64 (shiftRight a (8 * ((bits a + 7) / 8 - 3))) % 2 ^ 32) = mantissa0 a := by
    by_cases hn : (bits a + 7) / 8 ≤ 3
    · have hm : a.val * 256 ^ (3 - (bits a + 7) / 8) < 2 ^ 24 := by
        simpa [mantissa0, byteLength, hn] using m0lt
      have : a.val ≤ a.val * 256 ^ (3 - (bits a + 7) / 8) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
      simp only [mantissa0, byteLength, hn, ite_true, getLow64, Nat.shiftLeft_eq, ← pow256,
        Nat.mod_eq_of_lt (show a.val < 2 ^ 64 by omega)]
      omega
    · have hm0 : mantissa0 a = a.val / 256 ^ ((bits a + 7) / 8 - 3) := by
        simp [mantissa0, byteLength, hn]
      have hm := m0lt
      rw [hm0] at hm ⊢
      simp only [hn, ite_false, getLow64, shiftRight, Nat.shiftRight_eq_div_pow, ← pow256]
      omega
  simp only [getCompact]
  rw [pre]
  have hbit : (mantissa0 a &&& 0x00800000 != 0) = decide (2 ^ 23 ≤ mantissa0 a) := by
    rw [sign_bit]; simp only [decide_eq_decide]; omega
  have pack : ∀ m s : Nat, m < 2 ^ 24 → m ||| s <<< 24 = m + s * 2 ^ 24 := by
    intro m s hm
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hm, Nat.shiftLeft_eq]; omega
  rw [hbit]
  unfold normal byteLength
  by_cases h23 : 2 ^ 23 ≤ mantissa0 a
  · simp only [h23, decide_true, ite_true, Bool.false_and, Bool.false_eq_true, ite_false, Nat.or_zero,
      Nat.shiftRight_eq_div_pow]
    rw [pack _ _ (by omega)]
  · simp only [h23, decide_false, ite_false, Bool.false_and, Bool.false_eq_true, Nat.or_zero]
    rw [pack _ _ (by omega)]

/-- The value that `SetCompact` stores for size `s` and mantissa `m`, when the sign bit is clear. -/
def decodedValue (s m : Nat) : Nat := if s ≤ 3 then m / 256 ^ (3 - s) else m * 256 ^ (s - 3) % 2 ^ 256

/-- `SetCompact` of a packed size `s < 256` and mantissa `m < 2^23` stores `decodedValue s m` and reports no sign.
It reports no overflow when `s ≤ 33` and, for `s = 33`, `m < 2^16`. -/
theorem setCompact_packed (s m : Nat) (hm : m < 2 ^ 23) (hs : s < 256) :
    (setCompact (UInt32.ofNat (m + s * 2 ^ 24))).value.val = decodedValue s m ∧
    (setCompact (UInt32.ofNat (m + s * 2 ^ 24))).fNegative = false ∧
    (s ≤ 33 → (s = 33 → m < 2 ^ 16) → (setCompact (UInt32.ofNat (m + s * 2 ^ 24))).fOverflow = false) := by
  have hc : (UInt32.ofNat (m + s * 2 ^ 24)).toNat = m + s * 2 ^ 24 := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hsize : (m + s * 2 ^ 24) >>> 24 = s := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hword : (m + s * 2 ^ 24) &&& 0x007fffff = m := by
    rw [show (0x007fffff : Nat) = 2 ^ 23 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
  have hsign : ((m + s * 2 ^ 24) &&& 0x00800000 != 0) = false := by
    rw [sign_bit]; simp only [decide_eq_false_iff_not]; omega
  simp only [setCompact, hc, hsize, hword, hsign, Bool.and_false]
  refine ⟨?_, trivial, ?_⟩
  · unfold decodedValue
    split
    · simp [ofNat, Nat.shiftRight_eq_div_pow, ← pow256]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · simp [ofNat, shiftLeft, Nat.shiftLeft_eq, ← pow256, Nat.mod_eq_of_lt (show m < 2 ^ 256 by omega)]
  · intro h33 hm33
    split <;> simp <;> omega

/-- The facts about the normal form of `a` that the compact theorems use, in one conjunction. -/
def NormalSpec (a : ArithUint256) (s m : Nat) : Prop :=
  m < 2 ^ 23 ∧ s ≤ 33 ∧ (s = 33 → m < 2 ^ 16) ∧ decodedValue s m ≤ a.val ∧
    (a.val < 2 ^ 23 → decodedValue s m = a.val) ∧ (m = 0 ↔ a.val = 0) ∧
    (∀ h : decodedValue s m < 2 ^ 256, normal ⟨decodedValue s m, h⟩ = (s, m))

/-- The normal form of every value satisfies `NormalSpec`.
The proof splits on the byte length: up to three bytes, the mantissa is `a` shifted left, and from four bytes it is `a / 256^(n-3)`. -/
theorem normal_spec (a : ArithUint256) : NormalSpec a (normal a).1 (normal a).2 := by
  obtain ⟨m0lt, m0ge, m0zero⟩ := mantissa0_bounds a
  have nle := byteLength_le a
  by_cases h0 : a.val = 0
  · have hn : byteLength a = 0 := (byteLength_eq_zero_iff a).mpr h0
    have hm : mantissa0 a = 0 := m0zero h0
    have hnorm : normal a = (0, 0) := by simp [normal, hn, hm]
    have hdec : decodedValue 0 0 = 0 := by decide
    rw [hnorm]; dsimp only [NormalSpec]
    refine ⟨by decide, by decide, by decide, by rw [hdec]; omega, fun _ => by rw [hdec]; omega,
      by omega, fun h => ?_⟩
    have : (⟨decodedValue 0 0, h⟩ : ArithUint256) = a := Fin.ext (show decodedValue 0 0 = a.val by rw [hdec, h0])
    rw [this, hnorm]
  have m0ge := m0ge h0
  obtain ⟨lo, hi⟩ := byteLength_bounds a h0
  have npos : byteLength a ≠ 0 := fun h => h0 ((byteLength_eq_zero_iff a).mp h)
  -- When the decoded value is `a` itself, the last claim is immediate.
  have same : ∀ s m, normal a = (s, m) → decodedValue s m = a.val →
      ∀ h : decodedValue s m < 2 ^ 256, normal ⟨decodedValue s m, h⟩ = (s, m) := by
    intro s m hnorm hv h
    have : (⟨decodedValue s m, h⟩ : ArithUint256) = a := Fin.ext hv
    rw [this, hnorm]
  by_cases hsmall : byteLength a ≤ 3
  · have hm0 : mantissa0 a = a.val * 256 ^ (3 - byteLength a) := by simp [mantissa0, hsmall]
    have cases : byteLength a = 1 ∨ byteLength a = 2 ∨ byteLength a = 3 := by omega
    by_cases h23 : 2 ^ 23 ≤ mantissa0 a
    · have hnorm : normal a = (byteLength a + 1, mantissa0 a / 256) := by simp [normal, h23]
      rw [hnorm]; dsimp only [NormalSpec]
      rcases cases with hn | hn | hn
      · -- One byte with the top bit set: two zero bytes move out of the mantissa, and nothing is lost.
        rw [hn] at hm0 lo hi; simp at hm0 lo hi
        have hdec : decodedValue (byteLength a + 1) (mantissa0 a / 256) = a.val := by
          rw [hn]; simp [decodedValue]; omega
        refine ⟨by omega, by omega, by omega, by omega, fun _ => hdec, by omega,
          same _ _ hnorm hdec⟩
      · rw [hn] at hm0 lo hi; simp at hm0 lo hi
        have hdec : decodedValue (byteLength a + 1) (mantissa0 a / 256) = a.val := by
          rw [hn]; simp [decodedValue]; omega
        refine ⟨by omega, by omega, by omega, by omega, fun _ => hdec, by omega,
          same _ _ hnorm hdec⟩
      · -- Three bytes with the top bit set: the low byte is lost.
        rw [hn] at hm0 lo hi; simp at hm0 lo hi
        have hdec : decodedValue (byteLength a + 1) (mantissa0 a / 256) = a.val / 256 * 256 := by
          rw [hn]; simp [decodedValue]; omega
        refine ⟨by omega, by omega, by omega, by omega, fun h => by omega, by omega, fun h => ?_⟩
        have h' : a.val / 256 * 256 < 2 ^ 256 := by omega
        have hy : byteLength ⟨a.val / 256 * 256, h'⟩ = 3 :=
          byteLength_eq _ 3 (by simp; omega) (by simp; omega) (by simp; omega)
        have : (⟨decodedValue (byteLength a + 1) (mantissa0 a / 256), h⟩ : ArithUint256) =
            ⟨a.val / 256 * 256, h'⟩ := Fin.ext hdec
        rw [this, hn]
        simp only [normal, mantissa0, hy]
        simp only [show 3 ≤ 3 from Nat.le_refl 3, ite_true, Nat.sub_self, Nat.pow_zero, Nat.mul_one,
          show 2 ^ 23 ≤ a.val / 256 * 256 by omega]
        simp [hn, Nat.mul_div_cancel _ (show 0 < 256 by decide)]
    · have hnorm : normal a = (byteLength a, mantissa0 a) := by simp [normal, h23]
      rw [hnorm]; dsimp only [NormalSpec]
      have hdec : decodedValue (byteLength a) (mantissa0 a) = a.val := by
        simp only [decodedValue, hsmall, ite_true, hm0]
        exact Nat.mul_div_cancel _ (Nat.pow_pos (by decide))
      refine ⟨by omega, by omega, by omega, by omega, fun _ => hdec, ?_, same _ _ hnorm hdec⟩
      constructor
      · intro hm; omega
      · intro ha; exact absurd ha h0
  · -- Four bytes or more: the mantissa is `a / K` with `K = 256 ^ (byteLength a - 3)`.
    have hn3 : 3 < byteLength a := by omega
    have hpow := pow_split (n := byteLength a) (by omega)
    have hpow' := pow_split' hn3
    have K256 : 256 ≤ 256 ^ (byteLength a - 3) :=
      Nat.pow_le_pow_right (n := 256) (by decide) (show 1 ≤ byteLength a - 3 by omega)
    generalize hK : 256 ^ (byteLength a - 3) = K at hpow hpow' K256
    have Kpos : 0 < K := by omega
    have hm0 : mantissa0 a = a.val / K := by simp [mantissa0, hsmall, hK]
    have hle : a.val / K * K ≤ a.val := Nat.div_mul_le_self _ _
    rw [hpow'] at lo
    rw [hpow] at hi
    have bigA : 2 ^ 24 ≤ a.val := by omega
    have yhi : ∀ y, y ≤ a.val → y < 256 ^ byteLength a := by intro y hy; rw [hpow]; omega
    by_cases h23 : 2 ^ 23 ≤ mantissa0 a
    · have hnorm : normal a = (byteLength a + 1, mantissa0 a / 256) := by simp [normal, h23]
      rw [hnorm]; dsimp only [NormalSpec]
      have hK2 : 256 ^ (byteLength a + 1 - 3) = K * 256 := by
        rw [show byteLength a + 1 - 3 = (byteLength a - 3) + 1 by omega, Nat.pow_succ, hK]
      obtain ⟨q, hq⟩ : ∃ q, mantissa0 a / 256 = q := ⟨_, rfl⟩
      rw [hq]
      have qlo : 2 ^ 15 ≤ q := by omega
      have qhi : q < 2 ^ 16 := by omega
      have yle : q * (K * 256) ≤ a.val := by
        have h1 : q * 256 ≤ mantissa0 a := hq ▸ Nat.div_mul_le_self _ _
        have h2 := Nat.mul_le_mul_right K h1
        rw [hm0] at h2
        calc q * (K * 256) = q * 256 * K := by rw [Nat.mul_comm K, Nat.mul_assoc]
          _ ≤ a.val / K * K := h2
          _ ≤ a.val := hle
      have ylo : K * 65536 ≤ q * (K * 256) := by
        calc K * 65536 = 256 * (K * 256) := by omega
          _ ≤ q * (K * 256) := Nat.mul_le_mul_right _ (by omega)
      have hdec : decodedValue (byteLength a + 1) q = q * (K * 256) := by
        simp only [decodedValue, show ¬(byteLength a + 1 ≤ 3) by omega, ite_false, hK2]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by omega, by omega, fun _ => qhi, by rw [hdec]; exact yle, fun h => by omega,
        by omega, fun h => ?_⟩
      have h' : q * (K * 256) < 2 ^ 256 := by omega
      have : (⟨decodedValue (byteLength a + 1) q, h⟩ : ArithUint256) = ⟨q * (K * 256), h'⟩ :=
        Fin.ext hdec
      rw [this]
      have hy : byteLength ⟨q * (K * 256), h'⟩ = byteLength a :=
        byteLength_eq _ _ (by simp; omega) (by rw [hpow']; exact ylo) (yhi _ yle)
      have hdivK : q * (K * 256) / K = q * 256 := by
        rw [show q * (K * 256) = q * 256 * K by rw [Nat.mul_comm K, Nat.mul_assoc]]
        exact Nat.mul_div_cancel _ Kpos
      simp only [normal, mantissa0, hy, hsmall, ite_false, hK, hdivK,
        show 2 ^ 23 ≤ q * 256 by omega, ite_true, Nat.mul_div_cancel _ (show 0 < 256 by decide)]
    · have hnorm : normal a = (byteLength a, mantissa0 a) := by simp [normal, h23]
      rw [hnorm]; dsimp only [NormalSpec]
      have ylo : K * 65536 ≤ a.val / K * K := by
        rw [Nat.mul_comm K]; exact Nat.mul_le_mul_right _ (by omega)
      have hdec : decodedValue (byteLength a) (mantissa0 a) = a.val / K * K := by
        simp only [decodedValue, hsmall, ite_false, hK, hm0]
        exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by omega, by omega, fun h => by omega, by rw [hdec]; exact hle, fun h => by omega,
        by omega, fun h => ?_⟩
      have h' : a.val / K * K < 2 ^ 256 := by omega
      have : (⟨decodedValue (byteLength a) (mantissa0 a), h⟩ : ArithUint256) = ⟨a.val / K * K, h'⟩ :=
        Fin.ext hdec
      rw [this]
      have hy : byteLength ⟨a.val / K * K, h'⟩ = byteLength a :=
        byteLength_eq _ _ (by simp; omega) (by rw [hpow']; exact ylo) (yhi _ hle)
      simp only [normal, mantissa0, hy, hsmall, ite_false, hK, Nat.mul_div_cancel _ Kpos]
      simp only [← hm0, h23, ite_false]

/-- The two assertions of `GetCompact` (lines 240 and 241) hold for every value: the mantissa fits in 23 bits, and `nSize` is below 256. -/
theorem getCompact_assertions (a : ArithUint256) : (normal a).2 < 2 ^ 23 ∧ (normal a).1 < 256 := by
  have := normal_spec a; unfold NormalSpec at this; omega

/-- `SetCompact` of the compact encoding of `a` stores `decodedValue` of the normal form of `a`, and clears both flags. -/
private theorem decode_normal (a : ArithUint256) :
    (setCompact (getCompact a)).value.val = decodedValue (normal a).1 (normal a).2 ∧
    (setCompact (getCompact a)).fNegative = false ∧ (setCompact (getCompact a)).fOverflow = false := by
  have hs := normal_spec a
  unfold NormalSpec at hs
  obtain ⟨hv, hn, ho⟩ := setCompact_packed (normal a).1 (normal a).2 hs.1 (by omega)
  rw [getCompact_eq_normal]
  exact ⟨hv, hn, ho hs.2.1 hs.2.2.1⟩

/-- For every 256-bit value `a`, decoding its compact encoding gives a value that does not exceed `a`.
The encoding keeps the top bytes of `a` and sets the bytes below them to zero. -/
theorem setCompact_getCompact_le (a : ArithUint256) : (setCompact (getCompact a)).value ≤ a := by
  have := (normal_spec a).2.2.2.1
  rw [Fin.le_def, (decode_normal a).1]; exact this

/-- For every 256-bit value `a`, `SetCompact` reports neither a negative number nor an overflow for the compact encoding of `a`. -/
theorem setCompact_getCompact_flags (a : ArithUint256) :
    (setCompact (getCompact a)).fNegative = false ∧ (setCompact (getCompact a)).fOverflow = false :=
  (decode_normal a).2

/-- Every value below 2^23 survives the compact encoding exactly. -/
theorem setCompact_getCompact_of_lt (a : ArithUint256) (h : a.val < 2 ^ 23) :
    (setCompact (getCompact a)).value = a :=
  Fin.ext ((decode_normal a).1.trans ((normal_spec a).2.2.2.2.1 h))

/-- For every 256-bit value `a`, decoding and encoding again reproduces the compact encoding of `a`. -/
theorem getCompact_setCompact_getCompact (a : ArithUint256) :
    getCompact (setCompact (getCompact a)).value = getCompact a := by
  have hv := (decode_normal a).1
  have hy : normal (setCompact (getCompact a)).value = normal a := by
    have h := (normal_spec a).2.2.2.2.2.2 (hv ▸ (setCompact (getCompact a)).value.isLt)
    have e : (setCompact (getCompact a)).value =
        ⟨decodedValue (normal a).1 (normal a).2, hv ▸ (setCompact (getCompact a)).value.isLt⟩ :=
      Fin.ext hv
    rw [e]; exact h
  calc getCompact (setCompact (getCompact a)).value
      = UInt32.ofNat ((normal (setCompact (getCompact a)).value).2 +
          (normal (setCompact (getCompact a)).value).1 * 2 ^ 24) := getCompact_eq_normal _
    _ = UInt32.ofNat ((normal a).2 + (normal a).1 * 2 ^ 24) := by rw [hy]
    _ = getCompact a := (getCompact_eq_normal a).symm

/-- A 32-bit compact `c` survives decoding and encoding again exactly when `GetCompact` produces it for some value.
Core's own tests show compacts that `GetCompact` never produces, such as those in `getCompact_setCompact_zero_mantissa` and `getCompact_setCompact_negative`. -/
theorem getCompact_setCompact_iff (c : UInt32) :
    getCompact (setCompact c).value = c ↔ ∃ a, getCompact a = c := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨a, rfl⟩; exact getCompact_setCompact_getCompact a

/-- A compact whose mantissa bits fall below the byte length does not survive a round trip: `0x01003456` decodes to zero (Core's `bignum_SetCompact`, arith_uint256_tests.cpp line 429). -/
theorem getCompact_setCompact_zero_mantissa : getCompact (setCompact 0x01003456).value = 0 := by
  decide +kernel
/-- The value of `SetCompact` ignores the sign bit, so a negative compact encodes again without it: `0x04923456` becomes `0x04123456` (arith_uint256_tests.cpp line 517). -/
theorem getCompact_setCompact_negative : getCompact (setCompact 0x04923456).value = 0x04123456 := by
  decide +kernel
/-- `0xff123456` reports an overflow (arith_uint256_tests.cpp line 535), and its value wraps to zero modulo 2^256. -/
theorem setCompact_overflow_example :
    (setCompact 0xff123456).fOverflow = true ∧ (setCompact 0xff123456).value = 0 := by
  decide +kernel

/-- `SetCompact` reports an overflow exactly when the encoded number, mantissa times `256^(nSize - 3)`, is at least 2^256.
For `nSize ≤ 3` the factor is one, and the flag is clear.
The value that `SetCompact` stores is then the encoded number modulo 2^256. -/
theorem setCompact_fOverflow (c : UInt32) :
    (setCompact c).fOverflow = decide (2 ^ 256 ≤ c.toNat % 2 ^ 23 * 256 ^ (c.toNat / 2 ^ 24 - 3)) := by
  have hc := c.toNat_lt
  have hword : c.toNat &&& 0x007fffff = c.toNat % 2 ^ 23 := by
    rw [show (0x007fffff : Nat) = 2 ^ 23 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  simp only [setCompact, hword, Nat.shiftRight_eq_div_pow]
  generalize hn : c.toNat / 2 ^ 24 = n
  generalize hw : c.toNat % 2 ^ 23 = w
  have hn256 : n < 256 := by omega
  have hw23 : w < 2 ^ 23 := by omega
  rw [Bool.eq_iff_iff]
  by_cases small : n ≤ 3
  · simp only [small, ite_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
    rw [show n - 3 = 0 by omega, Nat.pow_zero, Nat.mul_one]
    omega
  · simp only [small, ite_false, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
    by_cases h32 : n ≤ 32
    · have : 256 ^ (n - 3) ≤ 256 ^ 29 := Nat.pow_le_pow_right (by decide) (by omega)
      have : w * 256 ^ (n - 3) ≤ w * 256 ^ 29 := Nat.mul_le_mul_left _ this
      omega
    · by_cases h33 : n = 33
      · subst h33; simp only [Nat.reduceSub, Nat.reducePow]; omega
      · by_cases h34 : n = 34
        · subst h34; simp only [Nat.reduceSub, Nat.reducePow]; omega
        · have big : 256 ^ 32 ≤ 256 ^ (n - 3) := Nat.pow_le_pow_right (by decide) (by omega)
          have : w * 256 ^ 32 ≤ w * 256 ^ (n - 3) := Nat.mul_le_mul_left _ big
          constructor
          · intro h; omega
          · intro h
            refine ⟨fun hw0 => ?_, Or.inl (by omega)⟩
            subst hw0; simp at h

end DogeLib.Work.ArithUint256
