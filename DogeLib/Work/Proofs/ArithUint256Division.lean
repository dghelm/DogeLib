module

public import DogeLib.Work.ArithUint256Division
public import DogeLib.Work.Proofs.ArithUint256Words

/-! # Arithmetic meaning of word division -/

@[expose] public section

namespace DogeLib.Work.ArithUint256.Words

/-- Materialisation preserves every word, for every eight-word input. -/
theorem readWords_ofFn (a : Words) : readWords (Vector.ofFn a) = a := by
  funext i
  exact Vector.getElem_ofFn i.isLt

/-- The descending scan compares the radix values, for every word count and both word arrays. -/
theorem compareLoop_eq (n : Nat) (a b : Fin n → UInt32) :
    compareLoop n a b = compare (eval n a) (eval n b) := by
  induction n with
  | zero => simp [compareLoop, eval]
  | succ n ih =>
    have ha := eval_lt n (fun i => a i.castSucc)
    have hb := eval_lt n (fun i => b i.castSucc)
    rw [compareLoop, eval_high, eval_high]
    rw [Nat.compare_eq_ite_lt]
    have hp := Nat.pow_pos (show 0 < 4294967296 by decide) (n := n)
    split
    · next h =>
        have h : (a ⟨n, by omega⟩).toNat < (b ⟨n, by omega⟩).toNat := h
        have hm := Nat.mul_le_mul_left (4294967296 ^ n) h
        simp only [Nat.mul_succ] at hm
        simp only [show eval n (fun i => a i.castSucc) + 4294967296 ^ n * (a ⟨n, by omega⟩).toNat <
          eval n (fun i => b i.castSucc) + 4294967296 ^ n * (b ⟨n, by omega⟩).toNat by omega, ite_true]
    · split
      · next h =>
          have h : (b ⟨n, by omega⟩).toNat < (a ⟨n, by omega⟩).toNat := h
          have hm := Nat.mul_le_mul_left (4294967296 ^ n) h
          simp only [Nat.mul_succ] at hm
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      · next h h' =>
          have he : (a ⟨n, by omega⟩).toNat = (b ⟨n, by omega⟩).toNat := by
            change ¬ (a ⟨n, by omega⟩).toNat < (b ⟨n, by omega⟩).toNat at h
            change ¬ (b ⟨n, by omega⟩).toNat < (a ⟨n, by omega⟩).toNat at h'
            omega
          rw [ih, Nat.compare_eq_ite_lt, he]
          simp only [Nat.add_lt_add_iff_right]

/-- For all eight-word inputs, Core's comparison scan compares their natural values. -/
theorem compareTo_eq (a b : Words) : compareTo a b = compare (value a) (value b) :=
  compareLoop_eq 8 a b

/-- A carry of at most one and two words sum exactly in 64 bits. -/
theorem add_step (carry : UInt64) (a b : UInt32) (hc : carry.toNat ≤ 1) :
    (carry + a.toUInt64 + b.toUInt64).toNat = carry.toNat + a.toNat + b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp only [UInt64.toNat_add, UInt32.toNat_toUInt64]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The addition loop accounts for its final carry, for every word count and initial carry at most one. -/
theorem addLoop_value (n : Nat) (a b : Fin n → UInt32) (carry : UInt64)
    (hc : carry.toNat ≤ 1) :
    eval n (addLoop n a b carry).1 + 4294967296 ^ n * (addLoop n a b carry).2.toNat =
      carry.toNat + eval n a + eval n b := by
  induction n generalizing carry with
  | zero => simp [eval, addLoop]
  | succ n ih =>
    let x := carry + (a 0).toUInt64 + (b 0).toUInt64
    have hx : x.toNat = carry.toNat + (a 0).toNat + (b 0).toNat := add_step carry (a 0) (b 0) hc
    have ha := (a 0).toNat_lt
    have hb := (b 0).toNat_lt
    have hs : (x >>> 32).toNat = x.toNat / 4294967296 := by
      simp only [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
    have hi := ih (fun i => a i.succ) (fun i => b i.succ) (x >>> 32) (by rw [hs]; omega)
    change x.toUInt32.toNat + 4294967296 * eval n (addLoop n (fun i => a i.succ) (fun i => b i.succ) (x >>> 32)).1 +
      4294967296 ^ (n + 1) * (addLoop n (fun i => a i.succ) (fun i => b i.succ) (x >>> 32)).2.toNat = _
    rw [UInt64.toNat_toUInt32, Nat.pow_succ' (m := 4294967296) (n := n)]
    rw [Nat.mul_assoc 4294967296, Nat.add_assoc, ← Nat.mul_add, hi, hs]
    rw [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc]
    rw [show x.toNat % 2 ^ 32 + 4294967296 * (x.toNat / 4294967296) = x.toNat from Nat.mod_add_div _ _]
    rw [hx]
    simp only [eval]
    omega

/-- For all eight-word inputs, addition gives the sum modulo 2^256. -/
theorem add_value (a b : Words) : value (add a b) = (value a + value b) % 2 ^ 256 := by
  have hi := addLoop_value 8 a b 0 (by decide)
  have ht := value_lt (add a b)
  change value (add a b) + 2 ^ 256 * (addLoop 8 a b 0).2.toNat = 0 + value a + value b at hi
  simp only [Nat.zero_add] at hi
  rw [← hi, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]

/-- Prefix increment extracts the words of the value plus one, for every word count. -/
theorem incrementLoop_digits (n : Nat) (a : Fin n → UInt32) :
    incrementLoop n a = digits n (eval n a + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ha := (a 0).toNat_lt
    have hw : (a 0 + 1).toNat = ((a 0).toNat + 1) % 4294967296 := by
      simp only [UInt32.toNat_add]; rfl
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · apply UInt32.toNat_inj.mp
      simp only [incrementLoop, digits, Fin.cases_zero, UInt32.toNat_ofNat', eval, hw]
      omega
    · simp only [incrementLoop, digits, Fin.cases_succ, eval]
      by_cases hz : a 0 + 1 = 0
      · have hv : (a 0).toNat + 1 = 4294967296 := by
          have : (a 0 + 1).toNat = 0 := by rw [hz]; rfl
          omega
        simp only [hz, beq_self_eq_true, ite_true]
        rw [ih]
        congr 2
        omega
      · have hv : (a 0).toNat + 1 < 4294967296 := by
          have : (a 0 + 1).toNat ≠ 0 := by
            intro he; exact hz (UInt32.toNat_inj.mp he)
          omega
        simp only [show (a 0 + 1 == 0) = false from by simpa using hz, Bool.false_eq_true, ite_false]
        rw [show ((a 0).toNat + 4294967296 * eval n (fun i => a i.succ) + 1) / 4294967296 =
          eval n (fun i => a i.succ) by omega, digits_eval]

/-- The value of prefix increment is the value plus one modulo the radix power. -/
theorem incrementLoop_value (n : Nat) (a : Fin n → UInt32) :
    eval n (incrementLoop n a) = (eval n a + 1) % 4294967296 ^ n := by
  rw [incrementLoop_digits, eval_digits]

/-- Complementary words sum to one less than the radix power, for every word count. -/
theorem complement_value (n : Nat) (a : Fin n → UInt32) :
    eval n (fun i => ~~~a i) + eval n a + 1 = 4294967296 ^ n := by
  induction n with
  | zero => simp [eval]
  | succ n ih =>
    have hw : (~~~a 0).toNat = 4294967295 - (a 0).toNat := by
      exact BitVec.toNat_not (x := (a 0).toBitVec)
    have ha := (a 0).toNat_lt
    have ht := ih (fun i => a i.succ)
    have hm := congrArg (4294967296 * ·) ht
    simp only [Nat.mul_add, Nat.mul_one] at hm
    simp only [eval, hw, Nat.pow_succ']
    omega

/-- For every eight-word input, complement plus increment gives two's-complement negation modulo 2^256. -/
theorem neg_value (a : Words) : value (neg a) = (2 ^ 256 - value a) % 2 ^ 256 := by
  have hc := complement_value 8 a
  rw [neg, value, incrementLoop_value]
  change _ = (2 ^ 256 - value a) % 4294967296 ^ 8
  apply congrArg (fun x => x % 4294967296 ^ 8)
  change eval 8 (fun i => ~~~a i) + 1 = 2 ^ 256 - eval 8 a
  change eval 8 (fun i => ~~~a i) + eval 8 a + 1 = 2 ^ 256 at hc
  omega

/-- For every pair of eight-word inputs, subtraction gives their difference modulo 2^256. -/
theorem sub_value (a b : Words) :
    value (sub a b) = (value a + (2 ^ 256 - value b)) % 2 ^ 256 := by
  rw [sub, add_value, neg_value, Nat.add_mod_mod]

/-- When the subtrahend is at most the minuend, word subtraction is exact natural subtraction. -/
theorem sub_value_of_le (a b : Words) (h : value b ≤ value a) :
    value (sub a b) = value a - value b := by
  rw [sub_value]
  have ha := value_lt a
  have hb := value_lt b
  rw [show value a + (2 ^ 256 - value b) = value a - value b + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- A left shift has its arithmetic value modulo 2^256, for all words and natural shifts. -/
theorem shiftLeft_value (a : Words) (s : Nat) :
    value (shiftLeft a s) = (value a * 2 ^ s) % 2 ^ 256 := by
  have h := congrArg Fin.val (shiftLeft_toArith a s)
  simpa only [toArith, ofNat, Nat.mod_eq_of_lt (value_lt a),
    Nat.mod_eq_of_lt (value_lt (shiftLeft a s)), ArithUint256.shiftLeft, Nat.shiftLeft_eq] using h

/-- A right shift divides the value by a power of two, for all words and natural shifts. -/
theorem shiftRight_value (a : Words) (s : Nat) :
    value (shiftRight a s) = value a / 2 ^ s := by
  have h := congrArg Fin.val (shiftRight_toArith a s)
  simpa only [toArith, ofNat, Nat.mod_eq_of_lt (value_lt a),
    Nat.mod_eq_of_lt (value_lt (shiftRight a s)), ArithUint256.shiftRight, Nat.shiftRight_eq_div_pow] using h

/-- The word mask for any natural bit position contains its bit within the word. -/
theorem quotient_mask (s : Nat) :
    ((1 : UInt32) <<< UInt32.ofNat (s % 32)).toNat = 2 ^ (s % 32) := by
  have hs : s % 32 < 32 := Nat.mod_lt _ (by decide)
  have hp : 2 ^ (s % 32) < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hs
  simp only [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat']
  change (1 <<< ((s % 32 % 4294967296) % 32)) % 4294967296 = _
  rw [Nat.mod_eq_of_lt (by omega : s % 32 < 4294967296), Nat.mod_eq_of_lt hs,
    Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt hp]

/-- A quotient bit update ORs the corresponding power of two into the natural value, below bit 256. -/
theorem quotient_or_value (q : Words) (s : Nat) (hs : s < 256) :
    value (orAt q (s / 32) ((1 : UInt32) <<< UInt32.ofNat (s % 32))) = value q ||| 2 ^ s := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  simp only [value, eval_testBit]
  by_cases hj : j / 32 < 8
  · simp only [hj, dite_true, orAt]
    by_cases he : j / 32 = s / 32
    · simp only [he, ite_true, UInt32.toNat_or, Nat.testBit_or, quotient_mask, Nat.testBit_two_pow]
      have : (s % 32 = j % 32) = (s = j) := propext (by omega)
      simp only [this]
    · simp only [he, ite_false]
      have : s ≠ j := by omega
      simp only [this, decide_false, Bool.or_false]
  · simp only [hj, dite_false]
    have : s ≠ j := by omega
    simp only [this, decide_false, Bool.or_self]

/-- If the quotient's low `s + 1` bits are zero, its next bit update adds exactly 2^s. -/
theorem quotient_add_value (q : Words) (s : Nat) (hs : s < 256)
    (hq : value q % 2 ^ (s + 1) = 0) :
    value (orAt q (s / 32) ((1 : UInt32) <<< UInt32.ofNat (s % 32))) = value q + 2 ^ s := by
  rw [quotient_or_value q s hs]
  have he : value q = 2 ^ (s + 1) * (value q / 2 ^ (s + 1)) := by
    have h := Nat.mod_add_div (value q) (2 ^ (s + 1))
    omega
  have hp : 2 ^ s < 2 ^ (s + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  conv => lhs; rw [he]
  rw [← Nat.two_pow_add_eq_or_of_lt hp]
  rw [← he]

private theorem div_step_arith (b n q d s : Nat) (hd : d = b * 2 ^ s)
    (hn : n < b * 2 ^ (s + 1)) :
    (if d ≤ n then n - d else n) < b * 2 ^ s ∧
    (if d ≤ n then n - d else n) + (if d ≤ n then q + 2 ^ s else q) * b = n + q * b := by
  rw [Nat.pow_succ, ← Nat.mul_assoc] at hn
  split <;> rename_i h
  · constructor
    · omega
    · rw [Nat.add_mul, Nat.mul_comm (2 ^ s) b]
      omega
  · constructor
    · omega
    · rfl

/-- The division loop preserves numerator plus quotient times divisor and leaves a remainder below the divisor.
The hypotheses give alignment, the next numerator bound, and zero low quotient bits at every natural loop count. -/
theorem divLoop_spec (remaining : Nat) (st : DivisionState) (b : Nat)
    (_hb : 0 < b) (hr : remaining ≤ 256)
    (hd : remaining ≠ 0 → value st.divisor = b * 2 ^ (remaining - 1))
    (hn : value st.num < b * 2 ^ remaining)
    (hq : value st.quotient % 2 ^ remaining = 0) :
    value (divLoop remaining st).num < b ∧
    value (divLoop remaining st).num + value (divLoop remaining st).quotient * b =
      value st.num + value st.quotient * b := by
  induction remaining generalizing st with
  | zero => exact ⟨by simpa only [divLoop, Nat.pow_zero, Nat.mul_one] using hn, rfl⟩
  | succ s ih =>
    have hd' : value st.divisor = b * 2 ^ s := by simpa using hd (by omega)
    have hc : (compareTo st.num st.divisor != Ordering.lt) = decide (value st.divisor ≤ value st.num) := by
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne, ne_eq, compareTo_eq, Nat.compare_eq_lt, Nat.not_lt, decide_eq_true_eq]
    let next : DivisionState := if value st.divisor ≤ value st.num then
      { num := sub st.num st.divisor, divisor := shiftRight st.divisor 1,
        quotient := orAt st.quotient (s / 32) ((1 : UInt32) <<< UInt32.ofNat (s % 32)) }
      else { st with divisor := shiftRight st.divisor 1 }
    have hnext : divLoop (s + 1) st = divLoop s next := by
      by_cases h : value st.divisor ≤ value st.num <;> simp [divLoop, readWords_ofFn, hc, next, h]
    have hnval : value next.num = if value st.divisor ≤ value st.num then
        value st.num - value st.divisor else value st.num := by
      unfold next
      split <;> simp only
      next h => exact sub_value_of_le _ _ h
    have hqval : value next.quotient = if value st.divisor ≤ value st.num then
        value st.quotient + 2 ^ s else value st.quotient := by
      unfold next
      split <;> simp only
      exact quotient_add_value _ s (by omega) hq
    have hdval : value next.divisor = value st.divisor / 2 := by
      unfold next
      split <;> exact shiftRight_value _ 1
    have hstep := div_step_arith b (value st.num) (value st.quotient) (value st.divisor) s hd' hn
    have hlow : value st.quotient % 2 ^ s = 0 := by
      have h := Nat.mod_mul_right_mod (value st.quotient) (2 ^ s) 2
      rw [← Nat.pow_succ, hq] at h
      simpa using h.symm
    have hqn : value next.quotient % 2 ^ s = 0 := by
      rw [hqval]
      split
      · rw [Nat.add_mod_right, hlow]
      · exact hlow
    have hdn : s ≠ 0 → value next.divisor = b * 2 ^ (s - 1) := by
      intro hs
      rw [hdval, hd', show s = (s - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc,
        Nat.mul_div_cancel _ (by decide : 0 < 2)]
      simp only [Nat.add_sub_cancel]
    have hi := ih next (by omega) hdn (by rw [hnval]; exact hstep.1) hqn
    rw [hnext]
    exact ⟨hi.1, hi.2.trans (by rw [hnval, hqval]; exact hstep.2)⟩

/-- The word bit scan is zero exactly when the natural value is zero. -/
theorem bits_eq_zero_iff (a : Words) : bits a = 0 ↔ value a = 0 := by
  rw [bits_toArith]
  simp only [ArithUint256.bits, toArith, ofNat, Nat.mod_eq_of_lt (value_lt a)]
  split <;> simp_all

/-- The bit scan bounds every value above, and every nonzero value below by its leading power of two. -/
theorem bits_value_bounds (a : Words) :
    value a < 2 ^ bits a ∧ (value a ≠ 0 → 2 ^ (bits a - 1) ≤ value a) := by
  rw [bits_toArith]
  simp only [ArithUint256.bits, toArith, ofNat, Nat.mod_eq_of_lt (value_lt a)]
  split
  · next h => simp [h]
  · next h =>
      simp only [Nat.add_sub_cancel]
      exact ⟨Nat.lt_log2_self, fun _ => Nat.log2_self_le h⟩

/-- Word division returns the exception exactly when the divisor's value is zero, for every pair of word inputs. -/
theorem divide_eq_none_iff (a b : Words) : divide a b = none ↔ value b = 0 := by
  simp only [divide]
  split
  · next h => simp [(bits_eq_zero_iff b).mp h]
  · next h =>
      have hz := mt (bits_eq_zero_iff b).mpr h
      split <;> simp [hz]

/-- For every word dividend and nonzero word divisor, word division returns the natural quotient rounded down. -/
theorem divide_value (a b : Words) (hb : value b ≠ 0) :
    (divide a b).map value = some (value a / value b) := by
  have hbpos : 0 < value b := by omega
  have hbb : 0 < bits b := by have : bits b ≠ 0 := fun hz => hb ((bits_eq_zero_iff b).mp hz); omega
  have hab := bits_value_bounds a
  have hbbounds := bits_value_bounds b
  have hz : value (fun _ : Fin 8 => (0 : UInt32)) = 0 := by decide +kernel
  unfold divide
  rw [ite_eq_right (by omega : ¬ bits b = 0)]
  split
  · next h =>
      have hpow : 2 ^ bits a ≤ 2 ^ (bits b - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hlt : value a < value b := Nat.lt_of_lt_of_le hab.1 (Nat.le_trans hpow (hbbounds.2 hb))
      simp only [Option.map_some, hz, Nat.div_eq_of_lt hlt]
  · next h =>
      let s := bits a - bits b
      have hs : bits b + s = bits a := by dsimp [s]; omega
      have hsbound : s + 1 ≤ 256 := by have := bits_le a; dsimp [s]; omega
      have halign : value b * 2 ^ s < 2 ^ 256 := by
        have hh := Nat.mul_lt_mul_of_pos_right hbbounds.1 (Nat.two_pow_pos s)
        rw [← Nat.pow_add, hs] at hh
        exact Nat.lt_of_lt_of_le hh (Nat.pow_le_pow_right (by decide) (bits_le a))
      have hnum : value a < value b * 2 ^ (s + 1) := by
        have hh := Nat.mul_le_mul_right (2 ^ (s + 1)) (hbbounds.2 hb)
        rw [← Nat.pow_add, show bits b - 1 + (s + 1) = bits a by omega] at hh
        exact Nat.lt_of_lt_of_le hab.1 hh
      let st : DivisionState := { num := a, divisor := shiftLeft b s, quotient := fun _ => 0 }
      have hdiv : value st.divisor = value b * 2 ^ s := by
        exact (shiftLeft_value b s).trans (Nat.mod_eq_of_lt halign)
      have hi := divLoop_spec (s + 1) st (value b) hbpos hsbound
        (fun _ => by simpa only [Nat.add_sub_cancel] using hdiv) hnum (by rw [show st.quotient = (fun _ => 0) from rfl, hz]; rfl)
      have he : value (divLoop (s + 1) st).quotient = value a / value b := by
        have heq : value (divLoop (s + 1) st).num + value (divLoop (s + 1) st).quotient * value b = value a := by
          simpa only [st, hz, Nat.zero_mul, Nat.add_zero] using hi.2
        rw [← heq, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hi.1, Nat.zero_add]
      exact congrArg some he

/-- For all word inputs with a nonzero divisor, word division agrees with `ArithUint256.div`. -/
theorem divide_toArith (a b : Words) (hb : (toArith b).val ≠ 0) :
    (divide a b).map toArith = some (ArithUint256.div (toArith a) (toArith b) hb) := by
  have hv : value b ≠ 0 := by simpa only [toArith, ofNat, Nat.mod_eq_of_lt (value_lt b)] using hb
  have h := divide_value a b hv
  cases he : divide a b with
  | none => simp [he] at h
  | some q =>
    simp only [he, Option.map_some, Option.some.injEq] at h ⊢
    apply Fin.ext
    simpa only [toArith, ofNat, ArithUint256.div, Nat.mod_eq_of_lt (value_lt a),
      Nat.mod_eq_of_lt (value_lt b), Nat.mod_eq_of_lt (value_lt q)] using h

/-- Division of the words of any 256-bit inputs returns the arithmetic quotient, when the divisor is nonzero. -/
theorem divide_ofArith (a b : ArithUint256) (hb : b.val ≠ 0) :
    divide (ofArith a) (ofArith b) = some (ofArith (ArithUint256.div a b hb)) := by
  have hb' : (toArith (ofArith b)).val ≠ 0 := by rw [toArith_ofArith]; exact hb
  have h := divide_toArith (ofArith a) (ofArith b) hb'
  simp only [toArith_ofArith] at h
  have he := congrArg (Option.map ofArith) h
  simpa only [Option.map_map, Function.comp_def, ofArith_toArith, Option.map_id',
    Option.map_some] using he

end DogeLib.Work.ArithUint256.Words
