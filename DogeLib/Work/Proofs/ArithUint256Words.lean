module

public import DogeLib.Work.ArithUint256Words

/-! # Arithmetic meaning of the word models -/

@[expose] public section

namespace DogeLib.Work.ArithUint256.Words

/-- The value of `n` words is below the radix raised to `n`. -/
theorem eval_lt (n : Nat) (pn : Fin n → UInt32) : eval n pn < 4294967296 ^ n := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    have hw := (pn 0).toNat_lt
    have ht := ih (fun i => pn i.succ)
    simp only [eval, Nat.pow_succ]
    have := Nat.mul_le_mul_left 4294967296 (show eval n (fun i => pn i.succ) + 1 ≤ 4294967296 ^ n by omega)
    omega

/-- Decoding the low `n` words of a natural number gives its value modulo the radix raised to `n`. -/
theorem eval_digits (n a : Nat) : eval n (digits n a) = a % 4294967296 ^ n := by
  induction n generalizing a with
  | zero => simp [eval, Nat.mod_one]
  | succ n ih =>
    simp only [eval, digits, Fin.cases_zero, Fin.cases_succ, UInt32.toNat_ofNat', ih]
    change a % 4294967296 + 4294967296 * (a / 4294967296 % 4294967296 ^ n) = _
    rw [Nat.pow_succ' (m := 4294967296) (n := n), Nat.mod_mul]

/-- Extracting the words from their radix value gives the original words. -/
theorem digits_eval (n : Nat) (pn : Fin n → UInt32) : digits n (eval n pn) = pn := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [digits, eval, Fin.cases_zero]
      apply UInt32.toNat_inj.mp
      have := (pn 0).toNat_lt
      simp only [UInt32.toNat_ofNat']
      omega
    · simp only [digits, eval, Fin.cases_succ]
      have h : ((pn 0).toNat + 4294967296 * eval n (fun i => pn i.succ)) / 4294967296 =
          eval n (fun i => pn i.succ) := by have := (pn 0).toNat_lt; omega
      rw [h, ih]

/-- Every eight-word value fits in 256 bits. -/
theorem value_lt (pn : Words) : value pn < 2 ^ 256 := by
  simpa [value] using eval_lt 8 pn

/-- Interpreting and then extracting eight words preserves every word. -/
theorem ofArith_toArith (pn : Words) : ofArith (toArith pn) = pn := by
  change digits 8 (value pn % 2 ^ 256) = pn
  rw [Nat.mod_eq_of_lt (value_lt pn)]
  exact digits_eval 8 pn

/-- Extracting and then interpreting words preserves every 256-bit value. -/
theorem toArith_ofArith (a : ArithUint256) : toArith (ofArith a) = a := by
  apply Fin.ext
  change eval 8 (digits 8 a.val) % 2 ^ 256 = a.val
  rw [eval_digits]
  change a.val % 2 ^ 256 % 2 ^ 256 = a.val
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt a.isLt]

/-- A 32-bit carry plus the product of two 32-bit words fits in 64 bits. -/
theorem mul_intermediate_lt (carry : UInt64) (b w : UInt32) (hc : carry.toNat < 2 ^ 32) :
    carry.toNat + b.toNat * w.toNat < 2 ^ 64 := by
  have hb := b.toNat_lt
  have hw := w.toNat_lt
  have hp := Nat.mul_le_mul (show b.toNat ≤ 2 ^ 32 - 1 by omega)
    (show w.toNat ≤ 2 ^ 32 - 1 by omega)
  omega

/-- The 64-bit intermediate has the exact mathematical value when the carry fits in 32 bits. -/
theorem mul_step (carry : UInt64) (b w : UInt32) (hc : carry.toNat < 2 ^ 32) :
    (carry + b.toUInt64 * w.toUInt64).toNat = carry.toNat + b.toNat * w.toNat := by
  have h := mul_intermediate_lt carry b w hc
  have hp : b.toNat * w.toNat < 2 ^ 64 := by omega
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt32.toNat_toUInt64,
    Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt h]

/-- The word carry loop represents the complete product, including its final carry,
for every word count and every initial carry below 2^32. -/
theorem mulLoop_value (b : UInt32) (n : Nat) (pn : Fin n → UInt32) (carry : UInt64)
    (hc : carry.toNat < 2 ^ 32) :
    eval n (mulLoop b n pn carry).1 + 4294967296 ^ n * (mulLoop b n pn carry).2.toNat =
      carry.toNat + eval n pn * b.toNat := by
  induction n generalizing carry with
  | zero => simp [eval, mulLoop]
  | succ n ih =>
    let x := carry + b.toUInt64 * (pn 0).toUInt64
    have hx : x.toNat = carry.toNat + b.toNat * (pn 0).toNat := mul_step carry b (pn 0) hc
    have hxlt := mul_intermediate_lt carry b (pn 0) hc
    have hs : (x >>> 32).toNat = x.toNat / 4294967296 := by
      simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    have hslt : (x >>> 32).toNat < 2 ^ 32 := by rw [hs]; omega
    have hi := ih (fun i => pn i.succ) (x >>> 32) hslt
    change x.toUInt32.toNat + 4294967296 * eval n (mulLoop b n (fun i => pn i.succ) (x >>> 32)).1 +
        4294967296 ^ (n + 1) * (mulLoop b n (fun i => pn i.succ) (x >>> 32)).2.toNat =
      carry.toNat + ((pn 0).toNat + 4294967296 * eval n (fun i => pn i.succ)) * b.toNat
    rw [UInt64.toNat_toUInt32, Nat.pow_succ' (m := 4294967296) (n := n)]
    rw [Nat.mul_assoc 4294967296, Nat.add_assoc, ← Nat.mul_add, hi, hs]
    have hm := Nat.mod_add_div x.toNat 4294967296
    rw [Nat.mul_add, ← Nat.add_assoc]
    rw [show x.toNat % 2 ^ 32 + 4294967296 * (x.toNat / 4294967296) = x.toNat from hm]
    rw [hx]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm b.toNat (pn 0).toNat, Nat.add_assoc]

/-- For every eight-word input and 32-bit multiplier, the word loop agrees with multiplication modulo 2^256. -/
theorem mulUInt32_toArith (pn : Words) (b : UInt32) :
    toArith (mulUInt32 pn b) = ArithUint256.mulUInt32 (toArith pn) b := by
  have hi := mulLoop_value b 8 pn 0 (by decide)
  have ht := value_lt (mulUInt32 pn b)
  apply Fin.ext
  change value (mulUInt32 pn b) % 2 ^ 256 = (value pn % 2 ^ 256 * b.toNat) % 2 ^ 256
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (value_lt pn)]
  change eval 8 (mulLoop b 8 pn 0).1 + 2 ^ 256 * (mulLoop b 8 pn 0).2.toNat =
    0 + eval 8 pn * b.toNat at hi
  simp only [Nat.zero_add] at hi
  unfold value
  rw [← hi, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt ht).symm

/-- Multiplication of the words of any 256-bit value gives the words of its arithmetic product. -/
theorem mulUInt32_ofArith (a : ArithUint256) (b : UInt32) :
    mulUInt32 (ofArith a) b = ofArith (ArithUint256.mulUInt32 a b) := by
  rw [← toArith_ofArith a, ← mulUInt32_toArith, ofArith_toArith, ofArith_toArith]

/-- For every eight-word input, Core's two-word expression gives the low 64 bits of its value. -/
theorem getLow64_toArith (pn : Words) :
    (getLow64 pn).toNat = ArithUint256.getLow64 (toArith pn) := by
  have h0 := (pn 0).toNat_lt
  have h1 := (pn 1).toNat_lt
  have hor : (pn 0).toNat ||| (pn 1).toNat <<< 32 =
      (pn 0).toNat + (pn 1).toNat * 4294967296 := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h0, Nat.shiftLeft_eq]
    omega
  have hshift : ((pn 1).toUInt64 <<< 32).toNat = (pn 1).toNat <<< 32 := by
    simp only [UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
    change ((pn 1).toNat <<< 32) % 2 ^ 64 = _
    rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  simp only [getLow64, UInt64.toNat_or, UInt32.toNat_toUInt64, hshift, hor,
    ArithUint256.getLow64, toArith, ofNat, Nat.mod_eq_of_lt (value_lt pn)]
  change (pn 0).toNat + (pn 1).toNat * 4294967296 =
    ((pn 0).toNat + 4294967296 * ((pn 1).toNat + 4294967296 *
      eval 6 (fun i => pn i.succ.succ))) % 2 ^ 64
  omega

/-- The low-64-bit word expression agrees with the arithmetic definition for every 256-bit input. -/
theorem getLow64_ofArith (a : ArithUint256) :
    (getLow64 (ofArith a)).toNat = ArithUint256.getLow64 a := by
  rw [getLow64_toArith, toArith_ofArith]

/-- The descending mask scan finds the highest bit of a nonzero word within its search range. -/
theorem bitScan_eq (w : UInt32) (k : Nat) (hz : w.toNat ≠ 0) (hk : w.toNat < 2 ^ (k + 1)) :
    bitScan w k = w.toNat.log2 + 1 := by
  induction k with
  | zero => have := (Nat.log2_lt hz).mpr hk; simp [bitScan]; omega
  | succ k ih =>
    have hl := (Nat.log2_lt hz).mpr hk
    by_cases he : w.toNat.log2 = k + 1
    · have hb : w.toNat.testBit (k + 1) = true := he ▸ Nat.testBit_log2 hz
      simp [bitScan, hb, he]
    · have hlt : w.toNat < 2 ^ (k + 1) := (Nat.log2_lt hz).mp (by omega)
      simp only [bitScan, Nat.testBit_lt_two_pow hlt, Bool.false_eq_true, ite_false]
      exact ih hlt

/-- The radix value splits into its lower words and its highest word. -/
theorem eval_high (n : Nat) (pn : Fin (n + 1) → UInt32) :
    eval (n + 1) pn = eval n (fun i => pn i.castSucc) +
      4294967296 ^ n * (pn ⟨n, by omega⟩).toNat := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    rw [eval, ih]
    simp only [eval]
    simp only [Nat.pow_succ' (m := 4294967296) (n := n), Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
    rfl

/-- The word scan gives zero for zero, and otherwise gives the highest bit position plus one. -/
theorem bitsLoop_eq (n : Nat) (pn : Fin n → UInt32) :
    bitsLoop n pn = if eval n pn = 0 then 0 else (eval n pn).log2 + 1 := by
  induction n with
  | zero => simp [bitsLoop, eval]
  | succ n ih =>
    let w := pn ⟨n, by omega⟩
    let lo := eval n (fun i => pn i.castSucc)
    have hlo : lo < 4294967296 ^ n := eval_lt n _
    have he : eval (n + 1) pn = lo + 4294967296 ^ n * w.toNat := eval_high n pn
    by_cases hw : w = 0
    · have ht : (pn ⟨n, by omega⟩ != 0) = false := by simp [← show w = pn ⟨n, by omega⟩ from rfl, hw]
      rw [bitsLoop, ht]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih, he, hw]
      simp only [UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero]
      rfl
    · have hwz : w.toNat ≠ 0 := by intro h; exact hw (UInt32.toNat_inj.mp h)
      have ht : (pn ⟨n, by omega⟩ != 0) = true := by simpa only [bne_iff_ne] using hw
      have hez : eval (n + 1) pn ≠ 0 := by
        rw [he]; have := Nat.pow_pos (show 0 < 4294967296 by decide) (n := n)
        have := Nat.mul_pos this (show 0 < w.toNat by omega)
        omega
      have hl := Nat.log2_self_le hwz
      have hh : w.toNat < 2 ^ (w.toNat.log2 + 1) := Nat.lt_log2_self
      have hp : 4294967296 ^ n = 2 ^ (32 * n) := by rw [Nat.pow_mul]
      have hlog : (eval (n + 1) pn).log2 = 32 * n + w.toNat.log2 := by
        apply (Nat.log2_eq_iff hez).mpr
        rw [he]
        constructor
        · rw [Nat.pow_add, ← hp]
          have := Nat.mul_le_mul_left (4294967296 ^ n) hl
          omega
        · rw [show 32 * n + w.toNat.log2 + 1 = 32 * n + (w.toNat.log2 + 1) by omega,
            Nat.pow_add, ← hp]
          have := Nat.mul_le_mul_left (4294967296 ^ n)
            (show w.toNat + 1 ≤ 2 ^ (w.toNat.log2 + 1) by omega)
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
      rw [bitsLoop, ht]
      simp only [ite_true, hez, ite_false]
      rw [bitScan_eq w 31 hwz w.toNat_lt, hlog]
      omega

/-- For every eight-word input, the descending scan agrees with the arithmetic bit length. -/
theorem bits_toArith (pn : Words) : bits pn = ArithUint256.bits (toArith pn) := by
  rw [bits, bitsLoop_eq]
  change (if value pn = 0 then 0 else (value pn).log2 + 1) =
    if value pn % 2 ^ 256 = 0 then 0 else (value pn % 2 ^ 256).log2 + 1
  rw [Nat.mod_eq_of_lt (value_lt pn)]

/-- For every 256-bit input, the scan of its words agrees with its arithmetic bit length. -/
theorem bits_ofArith (a : ArithUint256) : bits (ofArith a) = ArithUint256.bits a := by
  rw [bits_toArith, toArith_ofArith]

/-- The result of the eight-word scan never exceeds 256. -/
theorem bits_le (pn : Words) : bits pn ≤ 256 := by
  rw [bits_toArith]
  unfold ArithUint256.bits
  split
  · omega
  · have := (Nat.log2_lt (n := (toArith pn).val) (k := 256) (by assumption)).mpr (toArith pn).isLt
    omega

/-- A bit of a radix value is the corresponding bit of its word, or zero beyond the word array. -/
theorem eval_testBit (n : Nat) (pn : Fin n → UInt32) (j : Nat) :
    (eval n pn).testBit j =
      if h : j / 32 < n then (pn ⟨j / 32, h⟩).toNat.testBit (j % 32) else false := by
  induction n generalizing j with
  | zero => simp [eval]
  | succ n ih =>
    rw [eval, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (pn 0).toNat_lt]
    by_cases hj : j < 32
    · have hdiv : j / 32 = 0 := by omega
      simp [hj, hdiv, Nat.mod_eq_of_lt hj]
    · simp only [hj, ite_false, ih]
      have hd : (j - 32) / 32 + 1 = j / 32 := by omega
      have hm : (j - 32) % 32 = j % 32 := by omega
      by_cases hn : j / 32 < n + 1
      · have hn' : (j - 32) / 32 < n := by omega
        simp only [hn, hn', dite_true, hm]
        congr 3
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      · have hn' : ¬ (j - 32) / 32 < n := by omega
        simp [hn, hn']

private theorem word_bit_false (w : UInt32) (j : Nat) (h : 32 ≤ j) : w.toNat.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le w.toNat_lt (Nat.pow_le_pow_right (by decide) h))

private theorem word_left_bit (w : UInt32) (s r : Nat) (hs : s < 32) (hr : r < 32) :
    (w <<< UInt32.ofNat s).toNat.testBit r = (decide (s ≤ r) && w.toNat.testBit (r - s)) := by
  have hs32 : s < 2 ^ 32 := by omega
  simp only [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hs32,
    Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow, hr, decide_true, Bool.true_and, Nat.testBit_shiftLeft]

private theorem word_right_bit (w : UInt32) (s r : Nat) (hs : s < 32) :
    (w >>> UInt32.ofNat s).toNat.testBit r = w.toNat.testBit (s + r) := by
  have hs32 : s < 2 ^ 32 := by omega
  simp only [UInt32.toNat_shiftRight, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hs32,
    Nat.mod_eq_of_lt hs, Nat.testBit_shiftRight]

set_option linter.unusedSimpArgs false in
private theorem leftStep_bit (a pn : Words) (shift i j : Nat) (hi : i < 8) (hj : j < 256) :
    (value (leftStep a pn shift i)).testBit j =
      ((value pn).testBit j ||
        (decide (shift ≤ j ∧ (j - shift) / 32 = i) &&
          (a ⟨i, hi⟩).toNat.testBit ((j - shift) % 32))) := by
  have hji : j / 32 < 8 := by omega
  have hs : shift % 32 < 32 := Nat.mod_lt _ (by decide)
  have hr : j % 32 < 32 := Nat.mod_lt _ (by decide)
  have him : i % 8 = i := Nat.mod_eq_of_lt hi
  by_cases hlow : j / 32 = i + shift / 32
  · have hb : i + shift / 32 < 8 := by omega
    have hn : i + shift / 32 ≠ i + shift / 32 + 1 := by omega
    simp only [value, eval_testBit, hji, dite_true, leftStep, hb, ite_true]
    split <;> simp only [orAt, hlow, hn, ite_false, ite_true, him, UInt32.toNat_or, Nat.testBit_or,
      word_left_bit _ _ _ hs hr]
    all_goals
      congr 1
      by_cases hsr : shift % 32 ≤ j % 32
      · have he : shift ≤ j ∧ (j - shift) / 32 = i := by omega
        have hm : (j - shift) % 32 = j % 32 - shift % 32 := by omega
        simp [hsr, he, hm]
      · have he : ¬ (shift ≤ j ∧ (j - shift) / 32 = i) := by omega
        simp [hsr, he]
  · by_cases hhigh : j / 32 = i + shift / 32 + 1
    · have hb : i + shift / 32 + 1 < 8 := by omega
      by_cases hz : shift % 32 = 0
      · have he : ¬ (shift ≤ j ∧ (j - shift) / 32 = i) := by omega
        simp only [value, eval_testBit, hji, dite_true, leftStep, hz, bne_self_eq_false,
          Bool.and_false, Bool.false_eq_true, ite_false]
        split <;> simp [orAt, hlow, he]
      · have hg : (decide (i + shift / 32 + 1 < 8) && shift % 32 != 0) = true := by simp [hb, hz]
        have hsr : 32 - shift % 32 < 32 := by omega
        have hne : i + shift / 32 + 1 ≠ i + shift / 32 := by omega
        simp only [value, eval_testBit, hji, dite_true, leftStep, hg, ite_true]
        split <;> simp only [orAt, hlow, hhigh, hne, ite_false, ite_true, him,
          UInt32.toNat_or, Nat.testBit_or, word_right_bit _ _ _ hsr, Nat.mod_eq_of_lt hsr]
        all_goals
          congr 1
          by_cases hcarry : j % 32 < shift % 32
          · have he : shift ≤ j ∧ (j - shift) / 32 = i := by omega
            have hm : (j - shift) % 32 = 32 - shift % 32 + j % 32 := by omega
            simp [he, hm]
          · have he : ¬ (shift ≤ j ∧ (j - shift) / 32 = i) := by omega
            simp only [he, decide_false, Bool.false_and, Bool.or_false]
            rw [word_bit_false (a ⟨i, hi⟩) (32 - shift % 32 + j % 32) (by omega)]
    · have he : ¬ (shift ≤ j ∧ (j - shift) / 32 = i) := by omega
      simp only [value, eval_testBit, hji, dite_true, leftStep]
      split <;> split <;> simp [orAt, hlow, hhigh, he]

private theorem leftFold_bit (a pn : Words) (shift j : Nat) (hj : j < 256)
    (xs : List Nat) (hxs : ∀ i ∈ xs, i < 8) :
    (value (xs.foldl (fun pn i => leftStep a pn shift i) pn)).testBit j =
      ((value pn).testBit j ||
        (decide (shift ≤ j ∧ (j - shift) / 32 ∈ xs) &&
          (a ⟨(j - shift) / 32, by omega⟩).toNat.testBit ((j - shift) % 32))) := by
  induction xs generalizing pn with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih _ (by intro k hk; exact hxs k (by simp [hk]))]
    rw [leftStep_bit a pn shift i j (hxs i (by simp)) hj]
    by_cases he : (j - shift) / 32 = i
    · subst i
      by_cases hshift : shift ≤ j
      all_goals
        cases (value pn).testBit j <;>
          cases (a ⟨(j - shift) / 32, by omega⟩).toNat.testBit ((j - shift) % 32) <;>
          simp [hshift]
    · simp [he]

/-- For every eight-word input and natural shift, the left-shift loop agrees with multiplication by 2^shift modulo 2^256.
Core's unsigned 32-bit shift domain is included. -/
theorem shiftLeft_toArith (pn : Words) (shift : Nat) :
    toArith (shiftLeft pn shift) = ArithUint256.shiftLeft (toArith pn) shift := by
  apply Fin.ext
  change value (shiftLeft pn shift) % 2 ^ 256 = ((value pn % 2 ^ 256) <<< shift) % 2 ^ 256
  rw [Nat.mod_eq_of_lt (value_lt pn), Nat.mod_eq_of_lt (value_lt (shiftLeft pn shift))]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 256
  · rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    simp only [hj, decide_true, Bool.true_and]
    rw [shiftLeft, leftFold_bit pn (fun _ => 0) shift j hj _ (by simp)]
    have hz : value (fun _ : Fin 8 => (0 : UInt32)) = 0 := by decide +kernel
    rw [hz, Nat.zero_testBit]
    simp only [Bool.false_or, List.mem_range]
    have ht : (j - shift) / 32 < 8 := by omega
    simp only [ht, and_true]
    rw [value, eval_testBit]
    simp only [ht, dite_true]
  · have hz := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (value_lt (shiftLeft pn shift))
      (Nat.pow_le_pow_right (by decide) (by omega : 256 ≤ j)))
    rw [hz, Nat.testBit_mod_two_pow]
    simp [hj]

/-- Left shift of any 256-bit value's words gives the words of its arithmetic left shift, for every natural shift. -/
theorem shiftLeft_ofArith (a : ArithUint256) (shift : Nat) :
    shiftLeft (ofArith a) shift = ofArith (ArithUint256.shiftLeft a shift) := by
  rw [← toArith_ofArith a, ← shiftLeft_toArith, ofArith_toArith, ofArith_toArith]

set_option linter.unusedSimpArgs false in
private theorem rightStep_bit (a pn : Words) (shift i j : Nat) (hi : i < 8) (hj : j < 256) :
    (value (rightStep a pn shift i)).testBit j =
      ((value pn).testBit j ||
        (decide ((j + shift) / 32 = i) &&
          (a ⟨i, hi⟩).toNat.testBit ((j + shift) % 32))) := by
  have hji : j / 32 < 8 := by omega
  have hs : shift % 32 < 32 := Nat.mod_lt _ (by decide)
  have hr : j % 32 < 32 := Nat.mod_lt _ (by decide)
  have him : i % 8 = i := Nat.mod_eq_of_lt hi
  by_cases hlow : j / 32 + shift / 32 = i
  · have hk : shift / 32 ≤ i := by omega
    have ht : j / 32 = i - shift / 32 := by omega
    have hw : (a ⟨i, hi⟩ >>> UInt32.ofNat (shift % 32)).toNat.testBit (j % 32) =
        (decide ((j + shift) / 32 = i) && (a ⟨i, hi⟩).toNat.testBit ((j + shift) % 32)) := by
      rw [word_right_bit _ _ _ hs]
      by_cases hc : j % 32 + shift % 32 < 32
      · have he : (j + shift) / 32 = i := by omega
        have hm : (j + shift) % 32 = shift % 32 + j % 32 := by omega
        simp [he, hm]
      · have he : (j + shift) / 32 ≠ i := by omega
        rw [word_bit_false (a ⟨i, hi⟩) _ (by omega)]
        simp [he]
    simp only [value, eval_testBit, hji, dite_true, rightStep, hk, ite_true]
    split
    · rename_i hg
      have hki : shift / 32 + 1 ≤ i := by
        have hg' : shift / 32 + 1 ≤ i ∧ shift % 32 ≠ 0 := by simpa using hg
        exact hg'.1
      have hn : i - shift / 32 ≠ i - shift / 32 - 1 := by omega
      simp only [orAt, ht, hn, ite_false, ite_true, him, UInt32.toNat_or, Nat.testBit_or, hw]
    · simp only [orAt, ht, ite_true, him, UInt32.toNat_or, Nat.testBit_or, hw]
  · by_cases hhigh : j / 32 + shift / 32 + 1 = i
    · have hk : shift / 32 + 1 ≤ i := by omega
      have ht : j / 32 = i - shift / 32 - 1 := by omega
      have hn : i - shift / 32 - 1 ≠ i - shift / 32 := by omega
      by_cases hz : shift % 32 = 0
      · have he : (j + shift) / 32 ≠ i := by omega
        simp only [value, eval_testBit, hji, dite_true, rightStep, hz, bne_self_eq_false,
          Bool.and_false, Bool.false_eq_true, ite_false]
        split <;> simp [orAt, hlow, ht, hn, he]
      · have hg : (decide (shift / 32 + 1 ≤ i) && shift % 32 != 0) = true := by simp [hk, hz]
        have hsr : 32 - shift % 32 < 32 := by omega
        have hw : (a ⟨i, hi⟩ <<< UInt32.ofNat (32 - shift % 32)).toNat.testBit (j % 32) =
            (decide ((j + shift) / 32 = i) && (a ⟨i, hi⟩).toNat.testBit ((j + shift) % 32)) := by
          rw [word_left_bit _ _ _ hsr hr]
          by_cases hc : 32 - shift % 32 ≤ j % 32
          · have he : (j + shift) / 32 = i := by omega
            have hm : (j + shift) % 32 = j % 32 - (32 - shift % 32) := by omega
            simp [hc, he, hm]
          · have he : (j + shift) / 32 ≠ i := by omega
            simp [hc, he]
        simp only [value, eval_testBit, hji, dite_true, rightStep, hg, ite_true]
        split <;> simp only [orAt, ht, hn, ite_true, ite_false, him,
          UInt32.toNat_or, Nat.testBit_or, hw]
    · have he : (j + shift) / 32 ≠ i := by omega
      simp only [value, eval_testBit, hji, dite_true, rightStep]
      split
      · rename_i hk
        have hn0 : j / 32 ≠ i - shift / 32 := by omega
        split
        · rename_i hg
          have hg' : shift / 32 + 1 ≤ i ∧ shift % 32 ≠ 0 := by simpa using hg
          have hn1 : j / 32 ≠ i - shift / 32 - 1 := by omega
          simp [orAt, hn0, hn1, he]
        · simp [orAt, hn0, he]
      · rename_i hk
        have hg : ¬ shift / 32 + 1 ≤ i := by omega
        simp [hk, hg, he]

private theorem rightFold_bit (a pn : Words) (shift j : Nat) (hj : j < 256)
    (xs : List Nat) (hxs : ∀ i ∈ xs, i < 8) :
    (value (xs.foldl (fun pn i => rightStep a pn shift i) pn)).testBit j =
      ((value pn).testBit j ||
        (decide ((j + shift) / 32 ∈ xs) &&
          (a ⟨((j + shift) / 32) % 8, Nat.mod_lt _ (by decide)⟩).toNat.testBit ((j + shift) % 32))) := by
  induction xs generalizing pn with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih _ (by intro k hk; exact hxs k (by simp [hk]))]
    rw [rightStep_bit a pn shift i j (hxs i (by simp)) hj]
    by_cases he : (j + shift) / 32 = i
    · have hi : i < 8 := hxs i (by simp)
      simp only [he, Nat.mod_eq_of_lt hi, List.mem_cons, true_or, decide_true, Bool.true_and]
      cases (value pn).testBit j <;> cases (a ⟨i, hi⟩).toNat.testBit ((j + shift) % 32) <;> simp
    · simp [he]

/-- For every eight-word input and natural shift, the right-shift loop agrees with division by 2^shift rounded down.
Core's unsigned 32-bit shift domain is included. -/
theorem shiftRight_toArith (pn : Words) (shift : Nat) :
    toArith (shiftRight pn shift) = ArithUint256.shiftRight (toArith pn) shift := by
  apply Fin.ext
  change value (shiftRight pn shift) % 2 ^ 256 = (value pn % 2 ^ 256) >>> shift
  rw [Nat.mod_eq_of_lt (value_lt pn), Nat.mod_eq_of_lt (value_lt (shiftRight pn shift))]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight]
  by_cases hj : j < 256
  · rw [shiftRight, rightFold_bit pn (fun _ => 0) shift j hj _ (by simp)]
    have hz : value (fun _ : Fin 8 => (0 : UInt32)) = 0 := by decide +kernel
    rw [hz, Nat.zero_testBit]
    simp only [Bool.false_or, List.mem_range]
    rw [value, eval_testBit]
    by_cases ht : (j + shift) / 32 < 8
    · simp only [Nat.add_comm shift j, ht, dite_true, decide_true, Bool.true_and, Nat.mod_eq_of_lt ht]
    · simp only [Nat.add_comm shift j, ht, dite_false, decide_false, Bool.false_and]
  · have hz := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (value_lt (shiftRight pn shift))
      (Nat.pow_le_pow_right (by decide) (by omega : 256 ≤ j)))
    rw [hz]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (value_lt pn)
      (Nat.pow_le_pow_right (by decide) (by omega : 256 ≤ shift + j)))).symm

/-- Right shift of any 256-bit value's words gives the words of its arithmetic right shift, for every natural shift. -/
theorem shiftRight_ofArith (a : ArithUint256) (shift : Nat) :
    shiftRight (ofArith a) shift = ofArith (ArithUint256.shiftRight a shift) := by
  rw [← toArith_ofArith a, ← shiftRight_toArith, ofArith_toArith, ofArith_toArith]

end DogeLib.Work.ArithUint256.Words
