module

public import DogeLib.Script.Number

/-!
# Proofs: `Script.Number`

Theorems about `DogeLib.Script.Number`. Each holds for every input in its stated domain.

- `value_encode`: for every integer, the value of its encoding is the integer.
- `isMinimal_encode`: every encoding passes Core's minimality test.
- `isMinimal_iff_encode_value`: a byte string passes the test exactly when it is the encoding of its value. So the test accepts exactly one byte string for each integer.
- `natAbs_value_lt` and `encode_length_le_iff`: an encoding has at most `k` bytes exactly when `2 |n| < 256 ^ k`.
  `encode_length_le_four` gives four bytes within ±(2^31 − 1), and `encode_add_length_le_five` and `encode_sub_length_le_five` give five bytes for a sum or difference of two such integers.
- `decode_eq_ok_iff`, `decode_eq_overflow_iff`, `decode_eq_nonMinimal_iff`: every result of `decode`. The size check comes first.
- `decode_encode` and `decode_encode_default`: the round trip, with or without the minimal requirement.
- `decode_false`: without the requirement, a byte string within the size gives its value, also when it is not minimal.
- `decode_natAbs_lt`, `decode_default_natAbs_le`, `decode_five_natAbs_le`, `decode_int64`: the range of decoded values. With a size of at most 8 it fits `int64_t`.
- `getint_eq_max_min` and its corollaries: `getint` is the clamp to `[-2^31, 2^31 - 1]`. `getint_decode_default`: it never changes a value that a default-size decode returns.
- `castToBool_eq_false_iff_value` and `castToBool_eq_false_iff`: `castToBool` is false exactly on a zero value: zero bytes, or zero bytes and then `0x80`, at every length.
  `castToBool_encode`: the truth value of an encoding is `n ≠ 0`.

These theorems are statements about the definitions.
They do not say that the definitions match Core, or that Core's compiled code computes them.
-/

@[expose] public section

namespace DogeLib.Script.ScriptNum

/-! ## Byte facts -/

/-- A property holds for every byte when it holds for each value below 256, which `decide` can check. -/
private theorem allBytes (P : UInt8 → Prop) (h : ∀ n, n < 256 → P n.toUInt8) (b : UInt8) : P b := by
  simpa using h b.toNat b.toNat_lt

/-- For every byte, clearing the top bit leaves its value modulo 128. -/
theorem toNat_and_7f (b : UInt8) : (b &&& 0x7f).toNat = b.toNat % 128 :=
  allBytes (fun b => (b &&& 0x7f).toNat = b.toNat % 128) (by decide +kernel) b

/-- For every byte, the top bit is clear exactly when the value is below 128. -/
theorem and_80_eq_zero_iff (b : UInt8) : b &&& 0x80 = 0 ↔ b.toNat < 128 :=
  allBytes (fun b => (b &&& 0x80 = 0) ↔ b.toNat < 128) (by decide +kernel) b

/-- For every byte below 128, setting and then clearing the top bit gives it back. -/
theorem or_80_and_7f {b : UInt8} (h : b.toNat < 128) : (b ||| 0x80) &&& 0x7f = b :=
  allBytes (fun b => b.toNat < 128 → (b ||| 0x80) &&& 0x7f = b) (by decide +kernel) b h

/-- For every byte, the top bit is set after it is set. -/
theorem or_80_and_80 (b : UInt8) : (b ||| 0x80) &&& 0x80 ≠ 0 :=
  allBytes (fun b => (b ||| 0x80) &&& 0x80 ≠ 0) (by decide +kernel) b

/-- For every byte of at least 128, clearing and then setting the top bit gives it back. -/
theorem and_7f_or_80 {b : UInt8} (h : 128 ≤ b.toNat) : (b &&& 0x7f) ||| 0x80 = b :=
  allBytes (fun b => 128 ≤ b.toNat → (b &&& 0x7f) ||| 0x80 = b) (by decide +kernel) b h

/-- For every byte below 128, clearing the top bit changes nothing. -/
theorem and_7f_of_lt {b : UInt8} (h : b.toNat < 128) : b &&& 0x7f = b :=
  allBytes (fun b => b.toNat < 128 → b &&& 0x7f = b) (by decide +kernel) b h

/-- For every byte, the bits below the top bit are all zero exactly when the byte is `0x00` or `0x80`. -/
theorem toNat_and_7f_eq_zero_iff (b : UInt8) : (b &&& 0x7f).toNat = 0 ↔ b = 0 ∨ b = 0x80 :=
  allBytes (fun b => (b &&& 0x7f).toNat = 0 ↔ b = 0 ∨ b = 0x80) (by decide +kernel) b

/-- For every natural number below 256, the conversion to a byte keeps its value. -/
theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-! ## Little-endian values -/

/-- For all byte strings `xs` and `ys`, the little-endian value of `xs ++ ys` adds the value of `ys`, shifted past the bytes of `xs`. -/
theorem leNat_append (xs ys : List UInt8) : leNat (xs ++ ys) = leNat xs + 256 ^ xs.length * leNat ys := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih => simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]; grind

/-- For every byte string, the little-endian value is below `256 ^ length`. -/
theorem leNat_lt (xs : List UInt8) : leNat xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := x.toNat_lt
    omega

/-- For every byte string, the little-endian value is zero exactly when every byte is zero. -/
theorem leNat_eq_zero_iff (xs : List UInt8) : leNat xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih =>
    simp only [leNat, List.mem_cons, forall_eq_or_imp, ← ih]
    constructor
    · intro h; exact ⟨UInt8.toNat_inj.mp (by simp; omega), by omega⟩
    · rintro ⟨rfl, h⟩; simp [h]

/-- Zero has no bytes. -/
theorem leBytes_zero : leBytes 0 = [] := by simp [leBytes]

/-- For every nonzero number, the bytes are its low byte followed by the bytes of the rest. -/
theorem leBytes_of_ne_zero {n : Nat} (h : n ≠ 0) : leBytes n = (n % 256).toUInt8 :: leBytes (n / 256) := by
  rw [leBytes]; simp [h]

/-- For every natural number, the little-endian value of its bytes is the number. -/
theorem leNat_leBytes (n : Nat) : leNat (leBytes n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n = 0
    · subst h; simp [leBytes_zero, leNat]
    · rw [leBytes_of_ne_zero h, leNat, ih (n / 256) (by omega),
        toUInt8_toNat_of_lt (Nat.mod_lt _ (by omega))]
      omega

/-- For every number from 1 to 255, the bytes are that one byte. -/
theorem leBytes_of_lt {c : Nat} (h0 : c ≠ 0) (h : c < 256) : leBytes c = [c.toUInt8] := by
  rw [leBytes_of_ne_zero h0, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, leBytes_zero]

/-- Appending a nonzero high part to the little-endian value of `bs` keeps `bs` as the low bytes. -/
theorem leBytes_leNat_append (bs : List UInt8) {c : Nat} (hc : c ≠ 0) :
    leBytes (leNat bs + 256 ^ bs.length * c) = bs ++ leBytes c := by
  induction bs with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb := b.toNat_lt
    have hp : 0 < 256 ^ bs.length := Nat.pow_pos (by omega)
    have hpc : 0 < 256 ^ bs.length * c := Nat.mul_pos hp (by omega)
    simp only [leNat, List.length_cons, Nat.pow_succ, List.cons_append]
    have heq : b.toNat + 256 * leNat bs + 256 ^ bs.length * 256 * c
        = b.toNat + 256 * (leNat bs + 256 ^ bs.length * c) := by
      rw [Nat.mul_add, Nat.mul_comm (256 ^ bs.length) 256, Nat.mul_assoc]; omega
    rw [heq, leBytes_of_ne_zero (by omega)]
    congr 1
    · apply UInt8.toNat_inj.mp
      rw [toUInt8_toNat_of_lt (Nat.mod_lt _ (by omega))]; omega
    · rw [← ih]; congr 1; omega

/-- The bytes of a nonzero number end in a nonzero byte. -/
theorem leBytes_eq_concat {n : Nat} (h : n ≠ 0) :
    ∃ init last, leBytes n = init ++ [last] ∧ last ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hq : n / 256 = 0
    · refine ⟨[], n.toUInt8, ?_, ?_⟩
      · rw [leBytes_of_lt h (by omega)]; rfl
      · intro he
        have := congrArg UInt8.toNat he
        rw [toUInt8_toNat_of_lt (by omega)] at this
        exact h (by simpa using this)
    · obtain ⟨init, last, hl, hne⟩ := ih (n / 256) (by omega) hq
      exact ⟨(n % 256).toUInt8 :: init, last, by rw [leBytes_of_ne_zero h, hl]; rfl, hne⟩

/-! ## The value of a byte string -/

/-- The empty byte string has value zero. -/
theorem value_nil : value [] = 0 := rfl

/-- For every byte string split into its last byte, the value as a sign and a magnitude. -/
theorem value_concat (init : List UInt8) (last : UInt8) :
    value (init ++ [last]) =
      if last &&& 0x80 = 0 then ((leNat init + 256 ^ init.length * (last &&& 0x7f).toNat : Nat) : Int)
      else -((leNat init + 256 ^ init.length * (last &&& 0x7f).toNat : Nat) : Int) := by
  simp [value]

/-- For every byte string split into its last byte, the absolute value: the little-endian value with the top bit of the last byte cleared. -/
theorem natAbs_value_concat (init : List UInt8) (last : UInt8) :
    (value (init ++ [last])).natAbs = leNat init + 256 ^ init.length * (last.toNat % 128) := by
  rw [value_concat, toNat_and_7f]; split <;> simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- For every byte string, `2 |value| < 256 ^ length`. -/
theorem natAbs_value_lt (bytes : List UInt8) : 2 * (value bytes).natAbs < 256 ^ bytes.length := by
  rcases List.eq_nil_or_concat bytes with h | ⟨init, last, rfl⟩
  · subst h; simp [value_nil]
  · rw [List.concat_eq_append, natAbs_value_concat, List.length_append, List.length_singleton, Nat.pow_succ]
    have hl := leNat_lt init
    have hm : 256 ^ init.length * (last.toNat % 128) ≤ 256 ^ init.length * 127 :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## Encoding -/

/-- Zero encodes as the empty byte string. -/
theorem encode_zero : encode 0 = [] := by simp [encode, leBytes_zero]

/-- For every integer whose magnitude bytes end in `last`, the encoding in terms of `last` and the sign. -/
theorem encode_of_leBytes {n : Int} {init : List UInt8} {last : UInt8}
    (h : leBytes n.natAbs = init ++ [last]) :
    encode n =
      if last &&& 0x80 != 0 then init ++ [last, if n < 0 then 0x80 else 0x00]
      else if n < 0 then init ++ [last ||| 0x80]
      else init ++ [last] := by
  simp only [encode, h, List.getLast?_concat, List.dropLast_concat]
  split <;> simp

/-- The little-endian value of one byte is that byte. -/
theorem leNat_singleton (b : UInt8) : leNat [b] = b.toNat := by simp [leNat]

/-- The shape of a nonzero integer's magnitude bytes. -/
theorem natAbs_eq_of_leBytes {n : Int} {init : List UInt8} {last : UInt8}
    (h : leBytes n.natAbs = init ++ [last]) :
    n.natAbs = leNat init + 256 ^ init.length * last.toNat := by
  have := leNat_leBytes n.natAbs
  rw [h, leNat_append, leNat_singleton] at this
  exact this.symm

private theorem and_7f_80 : ((0x80 : UInt8) &&& 0x7f).toNat = 0 := by decide
private theorem and_7f_00 : ((0x00 : UInt8) &&& 0x7f).toNat = 0 := by decide

/-- For every integer `n`, the value of its encoding is `n`. -/
theorem value_encode (n : Int) : value (encode n) = n := by
  by_cases h0 : n = 0
  · subst h0; rw [encode_zero, value_nil]
  obtain ⟨init, last, hl, -⟩ := leBytes_eq_concat (Int.natAbs_ne_zero.mpr h0)
  have hm := natAbs_eq_of_leBytes hl
  rw [encode_of_leBytes hl]
  by_cases hA : last &&& 0x80 = 0
  · have hlt := (and_80_eq_zero_iff last).mp hA
    simp only [hA, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hn : n < 0
    · simp only [hn, ↓reduceIte, value_concat, or_80_and_80, or_80_and_7f hlt]
      omega
    · simp only [hn, ↓reduceIte, value_concat, hA, and_7f_of_lt hlt]
      omega
  · simp only [ne_eq, hA, not_false_eq_true, bne_iff_ne, ↓reduceIte]
    rw [← List.singleton_append, ← List.append_assoc, value_concat, leNat_append, leNat_singleton]
    by_cases hn : n < 0
    · simp only [hn, ↓reduceIte, and_7f_80]
      simp only [show ¬((0x80 : UInt8) &&& 0x80 = 0) from by decide, ↓reduceIte]; omega
    · simp only [hn, ↓reduceIte, and_7f_00]
      simp only [show ((0x00 : UInt8) &&& 0x80 = 0) from by decide, ↓reduceIte]; omega

/-! ## Minimality -/

/-- The empty byte string passes the minimality test. -/
theorem isMinimal_nil : isMinimal [] = true := rfl

/-- A one-byte string passes the minimality test exactly when its bits below the top bit are not all zero. -/
theorem isMinimal_singleton (last : UInt8) : isMinimal [last] = (last &&& 0x7f != 0) := by
  simp [isMinimal]

/-- A string of two or more bytes passes the minimality test in two cases. Its last byte has a nonzero magnitude part, or the byte before has its top bit set. -/
theorem isMinimal_concat_concat (init : List UInt8) (prev last : UInt8) :
    isMinimal (init ++ [prev, last]) = (last &&& 0x7f != 0 || prev &&& 0x80 != 0) := by
  simp [isMinimal]

/-- A byte string whose last byte has a nonzero magnitude part passes the test. -/
theorem isMinimal_concat_of_and_7f (init : List UInt8) {last : UInt8} (h : last &&& 0x7f ≠ 0) :
    isMinimal (init ++ [last]) = true := by
  simp [isMinimal, h]

private theorem and_7f_ne_zero {b : UInt8} (hne : b ≠ 0) (h : b.toNat < 128) : b &&& 0x7f ≠ 0 := by
  rwa [and_7f_of_lt h]

private theorem or_80_and_7f_ne_zero {b : UInt8} (hne : b ≠ 0) (h : b.toNat < 128) :
    (b ||| 0x80) &&& 0x7f ≠ 0 := by
  rwa [or_80_and_7f h]

/-- For every integer `n`, the encoding passes Core's minimality test. -/
theorem isMinimal_encode (n : Int) : isMinimal (encode n) = true := by
  by_cases h0 : n = 0
  · subst h0; rw [encode_zero]; rfl
  obtain ⟨init, last, hl, hne⟩ := leBytes_eq_concat (Int.natAbs_ne_zero.mpr h0)
  rw [encode_of_leBytes hl]
  by_cases hA : last &&& 0x80 = 0
  · have hlt := (and_80_eq_zero_iff last).mp hA
    simp only [hA, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split
    · exact isMinimal_concat_of_and_7f _ (or_80_and_7f_ne_zero hne hlt)
    · exact isMinimal_concat_of_and_7f _ (and_7f_ne_zero hne hlt)
  · simp only [ne_eq, hA, not_false_eq_true, bne_iff_ne, ↓reduceIte]
    rw [isMinimal_concat_concat]
    simp [hA]

/-- A byte string with a nonzero magnitude is negative exactly when its last byte has the sign bit. -/
theorem value_concat_neg_iff (init : List UInt8) (last : UInt8)
    (h : (value (init ++ [last])).natAbs ≠ 0) :
    value (init ++ [last]) < 0 ↔ last &&& 0x80 ≠ 0 := by
  rw [value_concat] at h ⊢
  split
  · rename_i hs; simp only [hs, ne_eq, not_true_eq_false, iff_false]; omega
  · rename_i hs; simp only [hs, ne_eq, not_false_eq_true, iff_true]; omega

/-- For every byte string: it passes Core's minimality test exactly when it is the encoding of its value. -/
theorem isMinimal_iff_encode_value (bytes : List UInt8) :
    isMinimal bytes = true ↔ encode (value bytes) = bytes := by
  refine ⟨fun hmin => ?_, fun h => h ▸ isMinimal_encode _⟩
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · rw [value_nil, encode_zero]
  rw [List.concat_eq_append] at hmin ⊢
  by_cases hc : last &&& 0x7f = 0
  · -- The magnitude ends in the byte before `last`, which has its top bit set.
    rcases List.eq_nil_or_concat init with rfl | ⟨init', prev, rfl⟩
    · simp [isMinimal_singleton, hc] at hmin
    rw [List.concat_eq_append] at hmin ⊢
    rw [List.append_assoc, List.singleton_append, isMinimal_concat_concat] at hmin
    simp only [hc, bne_self_eq_false, Bool.false_or, bne_iff_ne, ne_eq] at hmin
    have hprev : 128 ≤ prev.toNat := Nat.le_of_not_lt fun h => hmin ((and_80_eq_zero_iff prev).mpr h)
    have hc0 : (last &&& 0x7f).toNat = 0 := by rw [hc]; rfl
    have habs : (value (init' ++ [prev] ++ [last])).natAbs = leNat init' + 256 ^ init'.length * prev.toNat := by
      rw [natAbs_value_concat, ← toNat_and_7f, hc0, leNat_append, leNat_singleton]; simp
    have hbytes : leBytes (value (init' ++ [prev] ++ [last])).natAbs = init' ++ [prev] := by
      rw [habs, leBytes_leNat_append _ (by omega), leBytes_of_lt (by omega) prev.toNat_lt]; simp
    rw [encode_of_leBytes hbytes]
    simp only [hmin, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte]
    have hp : 0 < 256 ^ init'.length * prev.toNat := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hneg := value_concat_neg_iff (init' ++ [prev]) last (by rw [habs]; omega)
    rcases (toNat_and_7f_eq_zero_iff last).mp hc0 with rfl | rfl
    · have : ¬value (init' ++ [prev] ++ [0]) < 0 := by rw [hneg]; decide
      simp only [List.append_assoc, List.singleton_append] at this ⊢
      simp only [this, ↓reduceIte]
    · have : value (init' ++ [prev] ++ [0x80]) < 0 := by rw [hneg]; decide
      simp only [List.append_assoc, List.singleton_append] at this ⊢
      simp only [this, ↓reduceIte]
  · -- The magnitude ends in `last` without its sign bit.
    have hc' : (last &&& 0x7f).toNat ≠ 0 := fun h => hc (UInt8.toNat_inj.mp (by simpa using h))
    have hlt : (last &&& 0x7f).toNat < 128 := by rw [toNat_and_7f]; omega
    have habs : (value (init ++ [last])).natAbs = leNat init + 256 ^ init.length * (last &&& 0x7f).toNat := by
      rw [natAbs_value_concat, toNat_and_7f]
    have hbytes : leBytes (value (init ++ [last])).natAbs = init ++ [last &&& 0x7f] := by
      rw [habs, leBytes_leNat_append _ hc', leBytes_of_lt hc' (by omega)]; simp
    rw [encode_of_leBytes hbytes]
    have hs : (last &&& 0x7f) &&& 0x80 = 0 := (and_80_eq_zero_iff _).mpr hlt
    simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    have hp : 0 < 256 ^ init.length := Nat.pow_pos (by omega)
    have hpc : 0 < 256 ^ init.length * (last &&& 0x7f).toNat := Nat.mul_pos hp (Nat.pos_of_ne_zero hc')
    have hneg := value_concat_neg_iff init last (by rw [habs]; omega)
    by_cases hA : last &&& 0x80 = 0
    · have : ¬value (init ++ [last]) < 0 := by rw [hneg]; simpa using hA
      simp only [this, ↓reduceIte]
      rw [and_7f_of_lt ((and_80_eq_zero_iff last).mp hA)]
    · have : value (init ++ [last]) < 0 := by rw [hneg]; exact hA
      simp only [this, ↓reduceIte]
      rw [and_7f_or_80 (Nat.le_of_not_lt fun h => hA ((and_80_eq_zero_iff last).mpr h))]

/-- A minimal nonempty byte string has `256 ^ (length - 1) ≤ 2 |value|`. -/
theorem pow_le_two_mul_natAbs_value {bytes : List UInt8} (hmin : isMinimal bytes = true)
    (hne : bytes ≠ []) : 256 ^ (bytes.length - 1) ≤ 2 * (value bytes).natAbs := by
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl hne
  rw [List.concat_eq_append] at hmin ⊢
  rw [natAbs_value_concat, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  by_cases hc : last &&& 0x7f = 0
  · rcases List.eq_nil_or_concat init with rfl | ⟨init', prev, rfl⟩
    · simp [isMinimal_singleton, hc] at hmin
    rw [List.concat_eq_append] at hmin ⊢
    rw [List.append_assoc, List.singleton_append, isMinimal_concat_concat] at hmin
    simp only [hc, bne_self_eq_false, Bool.false_or, bne_iff_ne, ne_eq] at hmin
    have hprev : 128 ≤ prev.toNat := Nat.le_of_not_lt fun h => hmin ((and_80_eq_zero_iff prev).mpr h)
    have hc0 : last.toNat % 128 = 0 := by rw [← toNat_and_7f, hc]; rfl
    rw [hc0, leNat_append, leNat_singleton, List.length_append, List.length_singleton, Nat.pow_succ]
    have : 256 ^ init'.length * 128 ≤ 256 ^ init'.length * prev.toNat := Nat.mul_le_mul_left _ hprev
    omega
  · have hc' : 1 ≤ last.toNat % 128 := by
      rw [← toNat_and_7f]
      exact Nat.pos_of_ne_zero fun h => hc (UInt8.toNat_inj.mp (by simpa using h))
    have : 256 ^ init.length * 1 ≤ 256 ^ init.length * (last.toNat % 128) := Nat.mul_le_mul_left _ hc'
    omega

/-- For every integer `n` and length `k`: the encoding has at most `k` bytes exactly when `2 |n| < 256 ^ k`. -/
theorem encode_length_le_iff (n : Int) (k : Nat) : (encode n).length ≤ k ↔ 2 * n.natAbs < 256 ^ k := by
  constructor
  · intro h
    have := natAbs_value_lt (encode n)
    rw [value_encode] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by omega) h)
  · intro h
    refine Nat.le_of_not_lt fun hk => ?_
    have hne : encode n ≠ [] := fun he => by simp [he] at hk
    have := pow_le_two_mul_natAbs_value (isMinimal_encode n) hne
    rw [value_encode] at this
    have := Nat.pow_le_pow_right (n := 256) (by omega) (Nat.le_sub_one_of_lt hk)
    omega

/-- Every integer within ±(2^31 − 1) encodes in at most four bytes. -/
theorem encode_length_le_four {n : Int} (h : n.natAbs ≤ 2 ^ 31 - 1) : (encode n).length ≤ 4 :=
  (encode_length_le_iff n 4).mpr (by omega)

/-- For all integers `a` and `b` within ±(2^31 − 1), their sum encodes in at most five bytes. -/
theorem encode_add_length_le_five {a b : Int} (ha : a.natAbs ≤ 2 ^ 31 - 1) (hb : b.natAbs ≤ 2 ^ 31 - 1) :
    (encode (a + b)).length ≤ 5 :=
  (encode_length_le_iff _ 5).mpr (by omega)

/-- For all integers `a` and `b` within ±(2^31 − 1), their difference encodes in at most five bytes. -/
theorem encode_sub_length_le_five {a b : Int} (ha : a.natAbs ≤ 2 ^ 31 - 1) (hb : b.natAbs ≤ 2 ^ 31 - 1) :
    (encode (a - b)).length ≤ 5 :=
  (encode_length_le_iff _ 5).mpr (by omega)

/-! ## Decoding -/

/-- For all bytes, flag and size: decoding gives `n` exactly when the size fits, the bytes are minimal if required, and their value is `n`. -/
theorem decode_eq_ok_iff (bytes : List UInt8) (req : Bool) (maxSize : Nat) (n : Int) :
    decode bytes req maxSize = .ok n ↔
      bytes.length ≤ maxSize ∧ (req = true → isMinimal bytes = true) ∧ value bytes = n := by
  unfold decode
  by_cases hs : maxSize < bytes.length
  · simp only [hs, ↓reduceIte, reduceCtorEq, false_iff]; omega
  · cases req <;> cases isMinimal bytes <;> simp [hs, Except.ok.injEq] <;> omega

/-- For all bytes, flag and size: decoding fails with `overflow` exactly when there are more bytes than the size, whatever the flag and the minimality. -/
theorem decode_eq_overflow_iff (bytes : List UInt8) (req : Bool) (maxSize : Nat) :
    decode bytes req maxSize = .error .overflow ↔ maxSize < bytes.length := by
  unfold decode
  by_cases hs : maxSize < bytes.length
  · simp [hs]
  · cases req <;> cases isMinimal bytes <;> simp [hs]

/-- For all bytes, flag and size: decoding fails with `nonMinimal` exactly when the size fits, the flag is set and the minimality test fails. -/
theorem decode_eq_nonMinimal_iff (bytes : List UInt8) (req : Bool) (maxSize : Nat) :
    decode bytes req maxSize = .error .nonMinimal ↔
      bytes.length ≤ maxSize ∧ req = true ∧ isMinimal bytes = false := by
  unfold decode
  by_cases hs : maxSize < bytes.length
  · simp only [hs, ↓reduceIte, Except.error.injEq, reduceCtorEq, false_iff]; omega
  · cases req <;> cases isMinimal bytes <;> simp [hs] <;> omega

/-- Without the minimal requirement, a byte string within the size gives its value, also when it is not minimal. -/
theorem decode_false {bytes : List UInt8} {maxSize : Nat} (h : bytes.length ≤ maxSize) :
    decode bytes false maxSize = .ok (value bytes) :=
  (decode_eq_ok_iff _ _ _ _).mpr ⟨h, by simp, rfl⟩

/-- For every integer `n` with `2 |n| < 256 ^ maxSize`, decoding its encoding gives `n` back, with or without the minimal requirement. -/
theorem decode_encode (n : Int) (req : Bool) {maxSize : Nat} (h : 2 * n.natAbs < 256 ^ maxSize) :
    decode (encode n) req maxSize = .ok n :=
  (decode_eq_ok_iff _ _ _ _).mpr
    ⟨(encode_length_le_iff n maxSize).mpr h, fun _ => isMinimal_encode n, value_encode n⟩

/-- For every integer within ±(2^31 − 1), a default-size decode of its encoding gives it back, with or without the minimal requirement. -/
theorem decode_encode_default {n : Int} (req : Bool) (h : n.natAbs ≤ 2 ^ 31 - 1) :
    decode (encode n) req = .ok n :=
  decode_encode n req (by simp only [defaultMaxNumSize]; omega)

/-- Every value that a decode with size `maxSize` returns satisfies `2 |n| < 256 ^ maxSize`. -/
theorem decode_natAbs_lt {bytes : List UInt8} {req : Bool} {maxSize : Nat} {n : Int}
    (h : decode bytes req maxSize = .ok n) : 2 * n.natAbs < 256 ^ maxSize := by
  obtain ⟨hl, -, rfl⟩ := (decode_eq_ok_iff _ _ _ _).mp h
  exact Nat.lt_of_lt_of_le (natAbs_value_lt bytes) (Nat.pow_le_pow_right (by omega) hl)

/-- Every value that a default-size decode returns lies within ±(2^31 − 1). -/
theorem decode_default_natAbs_le {bytes : List UInt8} {req : Bool} {n : Int}
    (h : decode bytes req = .ok n) : n.natAbs ≤ 2 ^ 31 - 1 := by
  have := decode_natAbs_lt h
  simp only [defaultMaxNumSize] at this
  omega

/-- Every value that a decode with size 5 returns lies within ±(2^39 − 1). -/
theorem decode_five_natAbs_le {bytes : List UInt8} {req : Bool} {n : Int}
    (h : decode bytes req 5 = .ok n) : n.natAbs ≤ 2 ^ 39 - 1 := by
  have := decode_natAbs_lt h
  omega

/-- For a size of at most 8, every decoded value lies within ±(2^63 − 1), the range of `int64_t` without its minimum. -/
theorem decode_int64 {bytes : List UInt8} {req : Bool} {maxSize : Nat} {n : Int} (hs : maxSize ≤ 8)
    (h : decode bytes req maxSize = .ok n) : -(2 ^ 63 - 1) ≤ n ∧ n ≤ 2 ^ 63 - 1 := by
  have h1 := decode_natAbs_lt h
  have h2 := Nat.pow_le_pow_right (n := 256) (by omega) hs
  omega

/-! ## `getint` -/

/-- For every integer, `getint` is its clamp to `[-2^31, 2^31 - 1]`. -/
theorem getint_eq_max_min (n : Int) : getint n = max (-2 ^ 31) (min n (2 ^ 31 - 1)) := by
  unfold getint; split <;> (try split) <;> omega

/-- For every integer, `getint` leaves it unchanged exactly when it lies in `[-2^31, 2^31 - 1]`. -/
theorem getint_eq_self_iff (n : Int) : getint n = n ↔ -2 ^ 31 ≤ n ∧ n ≤ 2 ^ 31 - 1 := by
  rw [getint_eq_max_min]; omega

/-- For every integer of at least `2^31 - 1`, `getint` is `2^31 - 1`. -/
theorem getint_of_ge {n : Int} (h : 2 ^ 31 - 1 ≤ n) : getint n = 2 ^ 31 - 1 := by
  rw [getint_eq_max_min]; omega

/-- For every integer of at most `-2^31`, `getint` is `-2^31`. -/
theorem getint_of_le {n : Int} (h : n ≤ -2 ^ 31) : getint n = -2 ^ 31 := by
  rw [getint_eq_max_min]; omega

/-- For every integer, `getint` lies in `[-2^31, 2^31 - 1]`. -/
theorem getint_mem (n : Int) : -2 ^ 31 ≤ getint n ∧ getint n ≤ 2 ^ 31 - 1 := by
  rw [getint_eq_max_min]; omega

/-- On every value that a default-size decode returns, `getint` is the identity. -/
theorem getint_decode_default {bytes : List UInt8} {req : Bool} {n : Int}
    (h : decode bytes req = .ok n) : getint n = n := by
  have := decode_default_natAbs_le h
  rw [getint_eq_self_iff]; omega

end DogeLib.Script.ScriptNum

namespace DogeLib.Script

open ScriptNum

/-! ## `CastToBool` -/

/-- `castToBool` on a byte string split into its last byte: a nonzero earlier byte, or a last byte other than 0 and `0x80`. -/
theorem castToBool_concat (init : List UInt8) (last : UInt8) :
    castToBool (init ++ [last]) = (init.any (· != 0) || (last != 0 && last != 0x80)) := by
  unfold castToBool
  induction init with
  | nil => simp [castToBoolLoop]
  | cons b rest ih =>
    obtain ⟨y, ys, hr⟩ := List.exists_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil rest
      (List.cons_ne_nil last []))
    rw [List.cons_append, hr, castToBoolLoop, ← hr, ih]
    · simp [Bool.or_assoc]
    · simp

/-- For every byte string of any length, `castToBool` is false exactly when its value is zero. -/
theorem castToBool_eq_false_iff_value (bytes : List UInt8) : castToBool bytes = false ↔ value bytes = 0 := by
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · simp [castToBool, castToBoolLoop, value_nil]
  rw [List.concat_eq_append, castToBool_concat, ← Int.natAbs_eq_zero, natAbs_value_concat,
    ← toNat_and_7f]
  have hp : 0 < 256 ^ init.length := Nat.pow_pos (by omega)
  have hz : leNat init + 256 ^ init.length * (last &&& 0x7f).toNat = 0 ↔
      leNat init = 0 ∧ (last &&& 0x7f).toNat = 0 := by
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      have h3 : 256 ^ init.length * (last &&& 0x7f).toNat = 0 := by omega
      rcases Nat.mul_eq_zero.mp h3 with h' | h'
      · omega
      · exact h'
    · rintro ⟨h1, h2⟩; simp [h1, h2]
  rw [hz, leNat_eq_zero_iff, toNat_and_7f_eq_zero_iff]
  simp only [Bool.or_eq_false_iff, List.any_eq_false, bne_iff_ne, ne_eq, Decidable.not_not,
    Bool.and_eq_false_iff, bne_eq_false_iff_eq]

/-- For every byte string, `castToBool` is false exactly when it is zero bytes, or zero bytes and then one `0x80`. -/
theorem castToBool_eq_false_iff (bytes : List UInt8) :
    castToBool bytes = false ↔ ∃ k, bytes = List.replicate k 0 ∨ bytes = List.replicate k 0 ++ [0x80] := by
  rw [castToBool_eq_false_iff_value]
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · simp only [value_nil, true_iff]; exact ⟨0, .inl rfl⟩
  rw [List.concat_eq_append, ← castToBool_eq_false_iff_value, castToBool_concat]
  simp only [Bool.or_eq_false_iff, List.any_eq_false, bne_iff_ne, ne_eq, Decidable.not_not,
    Bool.and_eq_false_iff, bne_eq_false_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hi : init = List.replicate init.length 0 := List.eq_replicate_iff.mpr ⟨rfl, h1⟩
    rcases h2 with rfl | rfl
    · exact ⟨init.length + 1, .inl (by rw [List.replicate_succ', ← hi])⟩
    · exact ⟨init.length, .inr (by rw [← hi])⟩
  · rintro ⟨k, h | h⟩
    · cases k with
      | zero => simp at h
      | succ k =>
        rw [List.replicate_succ'] at h
        obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
        obtain rfl := List.singleton_inj.mp h2
        exact ⟨fun x hx => (List.eq_of_mem_replicate hx), .inl rfl⟩
    · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
      obtain rfl := List.singleton_inj.mp h2
      exact ⟨fun x hx => (List.eq_of_mem_replicate hx), .inr rfl⟩

/-- For every integer, the truth value of its encoding is `n ≠ 0`. -/
theorem castToBool_encode (n : Int) : castToBool (encode n) = decide (n ≠ 0) := by
  cases h : castToBool (encode n)
  · rw [castToBool_eq_false_iff_value, value_encode] at h; simp [h]
  · have : ¬value (encode n) = 0 := fun h' => by
      rw [← castToBool_eq_false_iff_value] at h'; simp [h] at h'
    rw [value_encode] at this; simp [this]

end DogeLib.Script
