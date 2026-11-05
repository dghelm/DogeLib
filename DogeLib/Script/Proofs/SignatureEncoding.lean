module

public import DogeLib.Script.Proofs.Number
public import DogeLib.Script.SignatureEncoding

/-!
# Proofs: `Script.SignatureEncoding`

Theorems about `DogeLib.Script.SignatureEncoding`. Each holds for every input in its stated domain.

- `secp256k1HalfOrder_eq`: the half order is `secp256k1Order / 2`.
- `isValidSignatureEncoding_iff`: strict DER is exactly `derBody r s` and one hash-type byte, for two DER integers `r` and `s` with at most 66 bytes in total.
- `laxStore_eq`: the lax parser stores `laxScalars` of the values of R and S.
  The scalars are both values when both are below the group order, and zero and zero otherwise.
- `parseDerLax_derBody` and `parseDerLax_dropLast_of_isValidSignatureEncoding`: the lax parser accepts every strict-DER signature without its hash type, and stores those scalars.
  `laxScalars_of_lt`: with R and S below the group order, it stores R and S themselves.
- `parseDerLaxWith_eq`: on inputs of fewer than 2^24 bytes, the parser gives the same result for every `sizeof(size_t)` of at least 4.
- `checkLowS_iff`: `checkLowS` holds exactly when the parser succeeds and stores an S of at most half the order.
  `checkLowS_derBody_iff`: on strict DER with R and S below the order, that is a bound on S itself.
- `checkLowS_derBody_of_overflow`: on strict DER with R or S at least the order, `checkLowS` holds whatever S is.
  `checkSignatureEncoding_overflowExample`: `overflowExample` has a high S and passes `checkSignatureEncoding` with `DERSIG`, `STRICTENC` and `LOW_S`.
- `checkSignatureEncoding_eq`: the check without its call to `isLowDerSignature`, which `isLowDerSignature_ne_sigDer` shows never gives `SIG_DER`.
- `checkSignatureEncoding_nil`, `checkSignatureEncoding_of_flags`, `checkSignatureEncoding_eq_sigDer_iff`, `checkSignatureEncoding_eq_sigHighS_iff`, `checkSignatureEncoding_eq_sigHashtype_iff` and `checkSignatureEncoding_error`: when each error occurs, and that no other error occurs.
- `isDefinedHashtypeSignature_iff`: the last byte without its `0x80` bit is 1, 2 or 3.
- `isCompressedOrUncompressedPubKey_iff`, `checkPubKeyEncoding_eq_error_iff` and `isValidPubKey_of_isCompressedOrUncompressedPubKey`: the accepted key shapes, the only key error, and that every accepted key gives a valid `CPubKey`.

These theorems are statements about the definitions.
They do not say that the definitions match Core, or that Core's compiled code computes them.
They say nothing about elliptic-curve points or signature validity.
-/

@[expose] public section

namespace DogeLib.Script

/-! ## The group order -/

/-- `secp256k1HalfOrder` is half of `secp256k1Order`, rounded down. -/
theorem secp256k1HalfOrder_eq : secp256k1HalfOrder = secp256k1Order / 2 := by decide

/-- The group order is below `2 ^ 256`, so every value of more than 32 significant bytes is at least the order. -/
theorem secp256k1Order_lt : secp256k1Order < 2 ^ 256 := by decide

/-! ## Big-endian values -/

/-- The fold of `beNat` from any accumulator `a`: `a` shifted past the bytes, plus their value. -/
theorem beNat_foldl (a : Nat) (xs : List UInt8) :
    xs.foldl (fun acc b => 256 * acc + b.toNat) a = a * 256 ^ xs.length + beNat xs := by
  induction xs generalizing a with
  | nil => simp [beNat]
  | cons x xs ih =>
    show xs.foldl _ (256 * a + x.toNat) = a * 256 ^ (xs.length + 1) + xs.foldl _ (256 * 0 + x.toNat)
    rw [ih, ih]
    grind

/-- The big-endian value of `x :: xs`: `x` shifted past the bytes of `xs`, plus their value. -/
theorem beNat_cons (x : UInt8) (xs : List UInt8) : beNat (x :: xs) = x.toNat * 256 ^ xs.length + beNat xs := by
  rw [beNat, List.foldl_cons, beNat_foldl]; simp

/-- The empty byte string has value zero. -/
theorem beNat_nil : beNat [] = 0 := rfl

/-- The big-endian value of `xs ++ ys`: the value of `xs` shifted past the bytes of `ys`, plus their value. -/
theorem beNat_append (xs ys : List UInt8) : beNat (xs ++ ys) = beNat xs * 256 ^ ys.length + beNat ys := by
  rw [beNat, List.foldl_append, beNat_foldl]; rfl

/-- For every byte string, the big-endian value is below `256 ^ length`. -/
theorem beNat_lt (xs : List UInt8) : beNat xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [beNat]
  | cons x xs ih =>
    rw [beNat_cons, List.length_cons, Nat.pow_succ]
    have hx := x.toNat_lt
    have : x.toNat * 256 ^ xs.length + 256 ^ xs.length ≤ 255 * 256 ^ xs.length + 256 ^ xs.length :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
    rw [Nat.mul_comm (256 ^ xs.length) 256]
    omega

/-- Leading zero bytes do not change the big-endian value. -/
theorem beNat_dropWhile_zero (xs : List UInt8) : beNat (xs.dropWhile (· == 0)) = beNat xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x = 0
    · subst hx; simp [ih, beNat_cons]
    · simp [hx]

/-- A byte string that starts with a nonzero byte has a value of at least `256 ^ (length - 1)`. -/
theorem pow_le_beNat_cons {x : UInt8} (hx : x ≠ 0) (xs : List UInt8) : 256 ^ xs.length ≤ beNat (x :: xs) := by
  rw [beNat_cons]
  have : 1 ≤ x.toNat := by
    have : x.toNat ≠ 0 := fun h => hx (UInt8.toNat_inj.mp (by simp [h]))
    omega
  have := Nat.mul_le_mul_right (256 ^ xs.length) this
  omega

/-- After its leading zeros, a byte string of `k + 1` bytes has a value of at least `256 ^ k`. -/
theorem pow_le_beNat_dropWhile {xs : List UInt8} {k : Nat} (h : (xs.dropWhile (· == 0)).length = k + 1) :
    256 ^ k ≤ beNat xs := by
  rw [← beNat_dropWhile_zero]
  match hd : xs.dropWhile (· == 0), h with
  | x :: rest, h =>
    have hx : x ≠ 0 := by
      have := List.head_dropWhile_not (· == 0) (l := xs) (by simp [hd])
      simp [hd] at this; exact this
    simp at h; subst h
    exact pow_le_beNat_cons hx rest

/-! ## The scalars that the lax parser stores -/

/-- The scalars of R and S with values `r` and `s`: both values when both are below the group order, and zero and zero otherwise. -/
def laxScalars (r s : Nat) : Nat × Nat :=
  if r < secp256k1Order ∧ s < secp256k1Order then (r, s) else (0, 0)

/-- With both values below the group order, the stored scalars are the values. -/
theorem laxScalars_of_lt {r s : Nat} (hr : r < secp256k1Order) (hs : s < secp256k1Order) :
    laxScalars r s = (r, s) := by simp [laxScalars, hr, hs]

/-- With either value at least the group order, both stored scalars are zero. -/
theorem laxScalars_of_le {r s : Nat} (h : secp256k1Order ≤ r ∨ secp256k1Order ≤ s) :
    laxScalars r s = (0, 0) := by
  simp only [laxScalars]; rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]

/-- A byte string with more than 32 bytes after its leading zeros has a value of at least the group order. -/
theorem order_le_of_length {xs : List UInt8} (h : 32 < (xs.dropWhile (· == 0)).length) :
    secp256k1Order ≤ beNat xs := by
  obtain ⟨k, hk⟩ : ∃ k, (xs.dropWhile (· == 0)).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
  have h1 := pow_le_beNat_dropWhile hk
  have h2 : 256 ^ 32 ≤ 256 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := secp256k1Order_lt
  have : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  omega

/-- For all byte strings of R and S, the lax parser stores `laxScalars` of their big-endian values.
The length test of Core's parser (D50, lines 138 and 150) never changes the result of the order test that follows. -/
theorem laxStore_eq (rBytes sBytes : List UInt8) :
    laxStore rBytes sBytes = laxScalars (beNat rBytes) (beNat sBytes) := by
  simp only [laxStore, beNat_dropWhile_zero, laxScalars]
  by_cases hr : 32 < (rBytes.dropWhile (· == 0)).length
  · have := order_le_of_length hr; simp [hr]; omega
  by_cases hs : 32 < (sBytes.dropWhile (· == 0)).length
  · have := order_le_of_length hs; simp [hs]; omega
  simp only [hr, hs, decide_false, Bool.false_or, Bool.not_and, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt]
  by_cases h1 : beNat rBytes < secp256k1Order <;> by_cases h2 : beNat sBytes < secp256k1Order <;>
    simp [h1, h2] <;> omega

/-! ## Byte positions -/

/-- For all byte strings, byte `i` of `xs ++ ys` is byte `i` of `xs`, or byte `i - xs.length` of `ys` past the end of `xs`. -/
theorem getD_append_zero (xs ys : List UInt8) (i : Nat) :
    (xs ++ ys).getD i 0 = if i < xs.length then xs.getD i 0 else ys.getD (i - xs.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split <;> rfl

/-- Byte `i` of a list laid out as a signature: four header bytes, `r`, two bytes, `s` and a last byte. Past the end it is zero. -/
theorem getD_layout (a0 a1 a2 a3 b0 b1 h : UInt8) (r s : List UInt8) (i : Nat) :
    (a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [h]))).getD i 0 =
      if i = 0 then a0 else if i = 1 then a1 else if i = 2 then a2 else if i = 3 then a3
      else if i < 4 + r.length then r.getD (i - 4) 0
      else if i = 4 + r.length then b0 else if i = 5 + r.length then b1
      else if i < 6 + r.length + s.length then s.getD (i - 6 - r.length) 0
      else if i = 6 + r.length + s.length then h else 0 := by
  match i with
  | 0 | 1 | 2 | 3 => simp
  | i + 4 =>
    simp only [List.getD_cons_succ, getD_append_zero]
    by_cases h1 : i < r.length
    · simp [h1]; omega
    have e1 : ¬ (i + 4 < 4 + r.length) := by omega
    have e2 : ¬ (i + 4 = 0) := by omega
    simp only [h1, e1, e2, ite_false]
    by_cases h2 : i = r.length
    · subst h2; simp; repeat' split
      all_goals first | rfl | omega
    by_cases h3 : i = r.length + 1
    · subst h3; simp; repeat' split
      all_goals first | rfl | omega
    obtain ⟨k, hk⟩ : ∃ k, i - r.length = k + 2 := ⟨i - r.length - 2, by omega⟩
    rw [hk]
    simp only [List.getD_cons_succ, getD_append_zero]
    have e4 : ¬ (i + 4 = 4 + r.length) := by omega
    have e5 : ¬ (i + 4 = 5 + r.length) := by omega
    simp only [e4, e5, ite_false]
    by_cases h4 : k < s.length
    · have : i + 4 < 6 + r.length + s.length := by omega
      simp only [h4, this, ite_true]; congr 1; omega
    have : ¬ (i + 4 < 6 + r.length + s.length) := by omega
    simp only [h4, this, ite_false]
    by_cases h5 : k = s.length
    · simp only [h5, Nat.sub_self]; repeat' split
      all_goals first | rfl | omega
    · have : ¬ (i + 4 = 6 + r.length + s.length) := by omega
      simp only [this, ite_false]
      obtain ⟨m, hm⟩ : ∃ m, k - s.length = m + 1 := ⟨k - s.length - 1, by omega⟩
      simp [hm]


/-! ## The strict DER shape -/

/-- The integer rule of `IsValidSignatureEncoding` for R or S (D3, lines 149 to 170).
The integer is not empty, and its first byte is below `0x80`.
A leading zero byte comes only before a byte of at least `0x80`. -/
def isDerInteger : List UInt8 → Bool
  | [] => false
  | [x] => x &&& 0x80 == 0
  | x :: y :: _ => x &&& 0x80 == 0 && !(x == 0 && y &&& 0x80 == 0)

/-- The strict DER bytes of a signature with integers `r` and `s`, without the hash type.
They are the sequence tag and length, then each integer with its tag and length. -/
def derBody (r s : List UInt8) : List UInt8 :=
  [0x30, (r.length + s.length + 4).toUInt8, 0x02, r.length.toUInt8] ++ r ++ [0x02, s.length.toUInt8] ++ s

/-- `derBody` and a hash-type byte, laid out as in `getD_layout`. -/
theorem derBody_append (r s : List UInt8) (h : UInt8) :
    derBody r s ++ [h] = 0x30 :: (r.length + s.length + 4).toUInt8 :: 0x02 :: r.length.toUInt8 ::
      (r ++ 0x02 :: s.length.toUInt8 :: (s ++ [h])) := by
  simp [derBody]

/-- Every natural number below 256 keeps its value through `toUInt8`. -/
theorem toNat_toUInt8_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

/-- Every signature built by `derBody` from two DER integers with at most 66 bytes in total, followed by any byte, passes `isValidSignatureEncoding`. -/
theorem isValidSignatureEncoding_derBody {r s : List UInt8} (h : UInt8) (hr : isDerInteger r = true)
    (hs : isDerInteger s = true) (hlen : r.length + s.length ≤ 66) :
    isValidSignatureEncoding (derBody r s ++ [h]) = true := by
  match r, s, hr, hs with
  | x :: r', y :: s', hr, hs =>
  rw [derBody_append]
  simp only [List.length_cons] at *
  have hA := toNat_toUInt8_of_lt (n := r'.length + 1 + (s'.length + 1) + 4) (by omega)
  have hB := toNat_toUInt8_of_lt (n := r'.length + 1) (by omega)
  have hC := toNat_toUInt8_of_lt (n := s'.length + 1) (by omega)
  generalize (r'.length + 1 + (s'.length + 1) + 4).toUInt8 = A at *
  generalize (r'.length + 1).toUInt8 = B at *
  generalize (s'.length + 1).toUInt8 = C at *
  unfold isValidSignatureEncoding
  simp only [getD_layout, List.length_cons, List.length_append]
  simp +arith only [hA, hB, hC, ite_true, ite_false, Nat.reduceEqDiff]
  have e1 : r'.length + 7 - 6 - (r'.length + 1) = 0 := by omega
  have e2 : r'.length + 8 - 6 - (r'.length + 1) = 1 := by omega
  have e3 : r'.length + s'.length + 6 = r'.length + s'.length + 9 - 3 := by omega
  simp only [e1, e2, e3, List.length_nil, Nat.add_zero, bne_self_eq_false, Bool.false_eq_true, ite_false,
    Nat.sub_self, Nat.reduceSub, List.getD_cons_zero, List.getD_cons_succ]
  have h65 : ¬ 65 ≤ r'.length + s'.length := by omega
  simp only [h65, ite_false]
  cases r' <;> cases s' <;> simp_all [isDerInteger] <;> grind

/-- Every list of `n1 + n2 + 7` bytes is laid out as in `getD_layout`, with `n1` bytes in `r` and `n2` in `s`. -/
theorem exists_layout {sig : List UInt8} {n1 n2 : Nat} (h : sig.length = n1 + n2 + 7) :
    ∃ a0 a1 a2 a3 b0 b1 hh r s, sig = a0 :: a1 :: a2 :: a3 :: (r ++ b0 :: b1 :: (s ++ [hh])) ∧
      r.length = n1 ∧ s.length = n2 := by
  match sig, h with
  | a0 :: a1 :: a2 :: a3 :: rest, h =>
    simp only [List.length_cons] at h
    have hd : (rest.drop n1).length = n2 + 3 := by simp; omega
    match hrest : rest.drop n1, hd with
    | b0 :: b1 :: rest3, hd =>
      simp only [List.length_cons] at hd
      have hd3 : (rest3.drop n2).length = 1 := by simp; omega
      match hr3 : rest3.drop n2, hd3 with
      | [hh], _ =>
        refine ⟨a0, a1, a2, a3, b0, b1, hh, rest.take n1, rest3.take n2, ?_, by simp; omega, by simp; omega⟩
        rw [← hr3, List.take_append_drop, ← hrest, List.take_append_drop]

/-- A byte is the conversion of its value. -/
theorem eq_toUInt8_of_toNat {b : UInt8} {n : Nat} (h : b.toNat = n) : b = n.toUInt8 := by
  subst h; simp

/-- Every signature that passes `isValidSignatureEncoding` is `derBody r s` followed by one byte, for two DER integers `r` and `s` with at most 66 bytes in total. -/
theorem shape_of_isValidSignatureEncoding {sig : List UInt8} (h : isValidSignatureEncoding sig = true) :
    ∃ r s hh, sig = derBody r s ++ [hh] ∧ isDerInteger r = true ∧ isDerInteger s = true ∧
      r.length + s.length ≤ 66 := by
  unfold isValidSignatureEncoding at h
  simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  repeat' split at h
  all_goals try simp at h
  simp only [← List.getD_eq_getElem?_getD] at h
  generalize hn1 : (sig.getD 3 0).toNat = n1 at h
  generalize hn2 : (sig.getD (5 + n1) 0).toNat = n2 at h
  obtain ⟨h9, h73, h0, h1, h5, hL, h2, hR0, hR, hRpad, hS2, hS0, hS, hSpad⟩ := h
  obtain ⟨a0, a1, a2, a3, b0, b1, hh, r, s, hsig, hr, hs⟩ := exists_layout hL.symm
  subst hsig hr hs
  simp only [getD_layout, List.length_cons, List.length_append] at *
  simp +arith only [ite_true, ite_false, Nat.reduceEqDiff] at *
  match r, s, hR0, hS0 with
  | x :: r', y :: s', _, _ =>
  simp only [List.length_cons, List.length_nil] at *
  have h1' : a1.toNat = (r'.length + 1) + (s'.length + 1) + 4 := by omega
  refine ⟨x :: r', y :: s', hh, ?_, ?_, ?_, by simp; omega⟩
  · rw [derBody_append]
    simp only [List.length_cons]
    rw [h0, h2, hS2, eq_toUInt8_of_toNat h1', eq_toUInt8_of_toNat hn1, eq_toUInt8_of_toNat hn2]
  · cases r' <;> simp_all [isDerInteger] <;> grind
  · have e0 : r'.length + 1 + 6 - 6 - (r'.length + 1) = 0 := by omega
    have e1 : r'.length + 1 + 7 - 6 - (r'.length + 1) = 1 := by omega
    simp only [e0, e1] at hS hSpad
    cases s' <;> simp_all [isDerInteger] <;> grind

/-! ## The lax parser -/

/-- For every `sizeof(size_t)`, the lax parser accepts every `derBody` with at most 66 integer bytes, and stores `laxStore` of its R and S bytes. -/
theorem parseDerLaxWith_derBody (w : Nat) {r s : List UInt8} (hlen : r.length + s.length ≤ 66) :
    parseDerLaxWith w (derBody r s) = some (laxStore r s) := by
  have hA := toNat_toUInt8_of_lt (n := r.length + s.length + 4) (by omega)
  have hB := toNat_toUInt8_of_lt (n := r.length) (by omega)
  have hC := toNat_toUInt8_of_lt (n := s.length) (by omega)
  have hbody : derBody r s = 0x30 :: (r.length + s.length + 4).toUInt8 :: 0x02 :: r.length.toUInt8 ::
      (r ++ 0x02 :: s.length.toUInt8 :: s) := by simp [derBody]
  rw [hbody]
  generalize (r.length + s.length + 4).toUInt8 = A at *
  generalize r.length.toUInt8 = B at *
  generalize s.length.toUInt8 = C at *
  have hA8 : A &&& 0x80 = 0 := (ScriptNum.and_80_eq_zero_iff A).mpr (by omega)
  have hB8 : B &&& 0x80 = 0 := (ScriptNum.and_80_eq_zero_iff B).mpr (by omega)
  have hC8 : C &&& 0x80 = 0 := (ScriptNum.and_80_eq_zero_iff C).mpr (by omega)
  generalize hX : (48 :: A :: 2 :: B :: (r ++ 2 :: C :: s) : List UInt8) = X
  have hXl : X.length = r.length + s.length + 6 := by subst hX; simp; omega
  have x0 : X.getD 0 0 = 0x30 := by subst hX; rfl
  have x1 : X.getD 1 0 = A := by subst hX; rfl
  have x2 : X.getD 2 0 = 2 := by subst hX; rfl
  have x3 : X.getD 3 0 = B := by subst hX; rfl
  have x4 : X.getD (4 + r.length) 0 = 2 := by subst hX; simp [Nat.add_comm 4]
  have x5 : X.getD (4 + r.length + 1) 0 = C := by subst hX; simp [Nat.add_comm 4]
  have hseq : laxSequenceLength X 1 = some 2 := by
    unfold laxSequenceLength
    simp only [x1, hA8, bne_self_eq_false, Bool.false_eq_true, ite_false]
    split
    · omega
    · rfl
  have hR : laxInteger w X 2 = some (4, r.length) := by
    unfold laxInteger laxIntegerLength
    simp only [x2, show (2 + 1 : Nat) = 3 from rfl, x3, hB8, hB]
    have n2 : ¬ (2 = X.length) := by omega
    have n3 : ¬ (3 = X.length) := by omega
    have n4 : ¬ (X.length - (3 + 1) < r.length) := by omega
    simp [n2, n3, n4]
  have hS : laxInteger w X (4 + r.length) = some (4 + r.length + 2, s.length) := by
    unfold laxInteger laxIntegerLength
    simp only [x4, x5, hC8, hC]
    have n2 : ¬ (4 + r.length = X.length) := by omega
    have n3 : ¬ (4 + r.length + 1 = X.length) := by omega
    have n4 : ¬ (X.length - (4 + r.length + 1 + 1) < s.length) := by omega
    simp [n2, n3, n4]
  have dR : (X.drop 4).take r.length = r := by subst hX; simp
  have dS : (X.drop (4 + r.length + 2)).take s.length = s := by
    subst hX; simp [Nat.add_comm 4, List.drop_append]
    rw [List.drop_eq_nil_of_le (by omega)]; simp
  unfold parseDerLaxWith
  simp only [x0]
  simp [hXl, hseq, hR, hS, dR, dS]

/-- On an input of fewer than 2^24 bytes, `laxInteger` gives the same result for every `sizeof(size_t)` of at least 4 as for 4.
A long-form length with 4 or more significant bytes is at least 2^24, so it fails the bounds test with any width. -/
theorem laxInteger_width {w : Nat} (hw : 4 ≤ w) {input : List UInt8} (h : input.length < 2 ^ 24) (pos : Nat) :
    laxInteger w input pos = laxInteger 4 input pos := by
  unfold laxInteger
  split
  · rfl
  unfold laxIntegerLength
  by_cases hq : pos + 1 = input.length
  · simp only [hq, ite_true]
  simp only [hq, ite_false]
  cases hb : (input.getD (pos + 1) 0 &&& 0x80 != 0)
  · simp only [Bool.false_eq_true, ite_false]
  simp only [ite_true]
  by_cases hn : input.length < pos + 1 + 1 + ((input.getD (pos + 1) 0).toNat - 128)
  · simp only [hn, ite_true]
  simp only [hn, ite_false]
  generalize List.take _ (List.drop _ input) = field
  by_cases hl : (field.dropWhile (· == 0)).length < 4
  · have h1 : ¬ (w ≤ (field.dropWhile (· == 0)).length) := by omega
    have h2 : ¬ (4 ≤ (field.dropWhile (· == 0)).length) := by omega
    simp only [h1, h2, ite_false]
  · obtain ⟨k, hk⟩ : ∃ k, (field.dropWhile (· == 0)).length = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    have hp := pow_le_beNat_dropWhile hk
    have h3 : 256 ^ 3 ≤ 256 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have big : input.length < beNat (field.dropWhile (· == 0)) := by
      rw [beNat_dropWhile_zero]; have : (2 : Nat) ^ 24 = 256 ^ 3 := by decide
      omega
    have h2 : 4 ≤ (field.dropWhile (· == 0)).length := by omega
    by_cases hw' : w ≤ (field.dropWhile (· == 0)).length
    · simp only [hw', h2, ite_true]
    · simp only [hw', h2, ite_true, ite_false]
      have : input.length - (pos + 1 + 1 + ((input.getD (pos + 1) 0).toNat - 128)) <
          beNat (field.dropWhile (· == 0)) := by omega
      simp only [this, ite_true]

/-- A signature passes `isValidSignatureEncoding` exactly when it is `derBody r s` followed by one hash-type byte.
Here `r` and `s` are DER integers with at most 66 bytes in total. -/
theorem isValidSignatureEncoding_iff (sig : List UInt8) :
    isValidSignatureEncoding sig = true ↔
      ∃ r s h, sig = derBody r s ++ [h] ∧ isDerInteger r = true ∧ isDerInteger s = true ∧
        r.length + s.length ≤ 66 :=
  ⟨shape_of_isValidSignatureEncoding, fun ⟨_, _, h, e, hr, hs, hl⟩ => e ▸ isValidSignatureEncoding_derBody h hr hs hl⟩

/-- The lax parser accepts every `derBody` with at most 66 integer bytes, and stores `laxScalars` of the values of R and S. -/
theorem parseDerLax_derBody {r s : List UInt8} (hlen : r.length + s.length ≤ 66) :
    parseDerLax (derBody r s) = some (laxScalars (beNat r) (beNat s)) := by
  rw [parseDerLax, parseDerLaxWith_derBody 8 hlen, laxStore_eq]

/-- Take any signature that passes `isValidSignatureEncoding`.
The lax parser accepts it without its last byte, and stores `laxScalars` of the values of its R and S. -/
theorem parseDerLax_dropLast_of_isValidSignatureEncoding {sig : List UInt8}
    (h : isValidSignatureEncoding sig = true) :
    ∃ r s, isDerInteger r = true ∧ isDerInteger s = true ∧ sig.dropLast = derBody r s ∧
      parseDerLax sig.dropLast = some (laxScalars (beNat r) (beNat s)) := by
  obtain ⟨r, s, hh, rfl, hr, hs, hl⟩ := shape_of_isValidSignatureEncoding h
  refine ⟨r, s, hr, hs, List.dropLast_concat .., ?_⟩
  rw [List.dropLast_concat]; exact parseDerLax_derBody hl

/-- On inputs of fewer than 2^24 bytes, the lax parser gives the same result for every `sizeof(size_t)` of at least 4.
So 32-bit and 64-bit builds agree on every Script stack item, which has at most 520 bytes. -/
theorem parseDerLaxWith_eq {w w' : Nat} (hw : 4 ≤ w) (hw' : 4 ≤ w') {input : List UInt8}
    (h : input.length < 2 ^ 24) : parseDerLaxWith w input = parseDerLaxWith w' input := by
  simp only [parseDerLaxWith, laxInteger_width hw h, laxInteger_width hw' h]

/-! ## LOW_S -/

/-- `checkLowS` holds exactly when the lax parser succeeds and stores an S of at most half the group order. -/
theorem checkLowS_iff (sig : List UInt8) :
    checkLowS sig = true ↔ ∃ r s, parseDerLax sig = some (r, s) ∧ s ≤ secp256k1HalfOrder := by
  unfold checkLowS
  split
  · simp_all
  · rename_i r s h
    simp only [h, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq]
    exact ⟨fun hs => ⟨r, s, ⟨rfl, rfl⟩, hs⟩, fun ⟨_, _, ⟨_, h⟩, hs⟩ => h ▸ hs⟩

/-- The overflow case of design record 0003, section 5.
For a strict-DER body whose R or S is at least the group order, `checkLowS` holds, whatever S is. -/
theorem checkLowS_derBody_of_overflow {r s : List UInt8} (hlen : r.length + s.length ≤ 66)
    (hov : secp256k1Order ≤ beNat r ∨ secp256k1Order ≤ beNat s) : checkLowS (derBody r s) = true := by
  rw [checkLowS_iff, parseDerLax_derBody hlen, laxScalars_of_le hov]
  exact ⟨0, 0, rfl, by decide⟩

/-- For a strict-DER body whose R and S are below the group order, `checkLowS` holds exactly when S is at most half the order. -/
theorem checkLowS_derBody_iff {r s : List UInt8} (hlen : r.length + s.length ≤ 66)
    (hr : beNat r < secp256k1Order) (hs : beNat s < secp256k1Order) :
    checkLowS (derBody r s) = true ↔ beNat s ≤ secp256k1HalfOrder := by
  rw [checkLowS_iff, parseDerLax_derBody hlen, laxScalars_of_lt hr hs]
  constructor
  · rintro ⟨_, _, h, hs⟩; cases h; exact hs
  · intro h; exact ⟨_, _, rfl, h⟩


/-! ## The signature checks -/

/-- `checkSignatureEncoding` without the call to `isLowDerSignature`: the empty signature passes, and then the DER test, the LOW_S test and the hash-type test run in order. -/
theorem checkSignatureEncoding_eq (sig : List UInt8) (flags : UInt32) :
    checkSignatureEncoding sig flags =
      if sig = [] then .ok ()
      else if (hasFlag flags ScriptFlags.derSig || hasFlag flags ScriptFlags.lowS ||
          hasFlag flags ScriptFlags.strictEnc) && !isValidSignatureEncoding sig then .error .sigDer
      else if hasFlag flags ScriptFlags.lowS && !checkLowS sig.dropLast then .error .sigHighS
      else if hasFlag flags ScriptFlags.strictEnc && !isDefinedHashtypeSignature sig then .error .sigHashtype
      else .ok () := by
  unfold checkSignatureEncoding isLowDerSignature
  by_cases h0 : sig = [] <;> simp only [h0, List.isEmpty_nil, List.isEmpty_iff, ite_true, ite_false]
  cases hd : hasFlag flags ScriptFlags.derSig <;> cases hl : hasFlag flags ScriptFlags.lowS <;>
    cases hs : hasFlag flags ScriptFlags.strictEnc <;> cases hv : isValidSignatureEncoding sig <;>
    cases hc : checkLowS sig.dropLast <;> cases hh : isDefinedHashtypeSignature sig <;> rfl

/-- The empty signature passes `checkSignatureEncoding` for every flag set. -/
theorem checkSignatureEncoding_nil (flags : UInt32) : checkSignatureEncoding [] flags = .ok () := by
  simp [checkSignatureEncoding_eq]

/-- `checkSignatureEncoding` gives `SIG_DER` exactly for a nonempty signature that fails strict DER, with `DERSIG`, `LOW_S` or `STRICTENC`. -/
theorem checkSignatureEncoding_eq_sigDer_iff (sig : List UInt8) (flags : UInt32) :
    checkSignatureEncoding sig flags = .error .sigDer ↔
      sig ≠ [] ∧ (hasFlag flags ScriptFlags.derSig || hasFlag flags ScriptFlags.lowS ||
        hasFlag flags ScriptFlags.strictEnc) = true ∧ isValidSignatureEncoding sig = false := by
  rw [checkSignatureEncoding_eq]
  by_cases h0 : sig = [] <;> simp only [h0] <;> repeat' split
  all_goals simp_all

/-- `checkSignatureEncoding` gives `SIG_HIGH_S` exactly for a strict-DER signature that fails `CheckLowS` without its last byte, with `LOW_S`. -/
theorem checkSignatureEncoding_eq_sigHighS_iff (sig : List UInt8) (flags : UInt32) :
    checkSignatureEncoding sig flags = .error .sigHighS ↔
      sig ≠ [] ∧ hasFlag flags ScriptFlags.lowS = true ∧ isValidSignatureEncoding sig = true ∧
        checkLowS sig.dropLast = false := by
  rw [checkSignatureEncoding_eq]
  by_cases h0 : sig = [] <;> simp only [h0] <;> repeat' split
  all_goals simp_all

/-- `checkSignatureEncoding` gives `SIG_HASHTYPE` exactly for a signature with an undefined hash type, with `STRICTENC`, that passes the DER test and, with `LOW_S`, the LOW_S test. -/
theorem checkSignatureEncoding_eq_sigHashtype_iff (sig : List UInt8) (flags : UInt32) :
    checkSignatureEncoding sig flags = .error .sigHashtype ↔
      sig ≠ [] ∧ hasFlag flags ScriptFlags.strictEnc = true ∧ isValidSignatureEncoding sig = true ∧
        (hasFlag flags ScriptFlags.lowS = true → checkLowS sig.dropLast = true) ∧
        isDefinedHashtypeSignature sig = false := by
  rw [checkSignatureEncoding_eq]
  by_cases h0 : sig = [] <;> simp only [h0] <;> repeat' split
  all_goals simp_all

/-- Every error of `checkSignatureEncoding` is `SIG_DER`, `SIG_HIGH_S` or `SIG_HASHTYPE`. -/
theorem checkSignatureEncoding_error {sig : List UInt8} {flags : UInt32} {e : ScriptError}
    (h : checkSignatureEncoding sig flags = .error e) : e = .sigDer ∨ e = .sigHighS ∨ e = .sigHashtype := by
  rw [checkSignatureEncoding_eq] at h
  repeat' split at h
  all_goals (first | (cases h; simp) | simp at h)

/-- Without `DERSIG`, `LOW_S` and `STRICTENC`, every signature passes `checkSignatureEncoding`. -/
theorem checkSignatureEncoding_of_flags (sig : List UInt8) {flags : UInt32}
    (hd : hasFlag flags ScriptFlags.derSig = false) (hl : hasFlag flags ScriptFlags.lowS = false)
    (hs : hasFlag flags ScriptFlags.strictEnc = false) : checkSignatureEncoding sig flags = .ok () := by
  simp [checkSignatureEncoding_eq, hd, hl, hs]

/-- In `checkSignatureEncoding`, the call to `isLowDerSignature` never gives `SIG_DER`: with `LOW_S`, a signature that reaches it passed the DER test already. -/
theorem isLowDerSignature_ne_sigDer {sig : List UInt8} {flags : UInt32}
    (hl : hasFlag flags ScriptFlags.lowS = true) (hv : checkSignatureEncoding sig flags ≠ .error .sigDer)
    (h0 : sig ≠ []) : isLowDerSignature sig ≠ .error .sigDer := by
  rw [Ne, checkSignatureEncoding_eq_sigDer_iff] at hv
  have hv' : isValidSignatureEncoding sig = true := by
    cases h : isValidSignatureEncoding sig <;> simp_all
  simp only [isLowDerSignature, hv', Bool.not_true]
  cases checkLowS sig.dropLast <;> simp

/-! ## The overflow example -/

/-- R of the overflow example: `0x00` and then 32 bytes `0xff`, the value 2^256 − 1. -/
def overflowExampleR : List UInt8 := 0x00 :: List.replicate 32 0xff

/-- S of the overflow example: `0x7f` and then 31 bytes `0xff`, the value 2^255 − 1. -/
def overflowExampleS : List UInt8 := 0x7f :: List.replicate 31 0xff

/-- The overflow example: strict DER with R = `overflowExampleR`, S = `overflowExampleS`, and hash type `SIGHASH_ALL`. -/
def overflowExample : List UInt8 := derBody overflowExampleR overflowExampleS ++ [0x01]

/-- The overflow example is strict DER. -/
theorem overflowExample_isValidSignatureEncoding : isValidSignatureEncoding overflowExample = true :=
  isValidSignatureEncoding_derBody _ (by decide) (by decide) (by decide)

/-- R of the overflow example is at least the group order. -/
theorem overflowExample_order_le : secp256k1Order ≤ beNat overflowExampleR := by decide

/-- S of the overflow example is above half the group order: it is a high S. -/
theorem overflowExample_highS : secp256k1HalfOrder < beNat overflowExampleS := by decide

/-- The LOW_S filter accepts the overflow example, which has a high S, under `DERSIG`, `STRICTENC` and `LOW_S` together. -/
theorem checkSignatureEncoding_overflowExample :
    checkSignatureEncoding overflowExample (ScriptFlags.derSig ||| ScriptFlags.strictEnc ||| ScriptFlags.lowS) = .ok () := by
  have hl : checkLowS overflowExample.dropLast = true := by
    rw [overflowExample, List.dropLast_concat]
    exact checkLowS_derBody_of_overflow (by decide) (.inl overflowExample_order_le)
  rw [checkSignatureEncoding_eq]
  have hh : isDefinedHashtypeSignature overflowExample = true := by decide
  have hs : hasFlag (ScriptFlags.derSig ||| ScriptFlags.strictEnc ||| ScriptFlags.lowS) ScriptFlags.strictEnc = true := by
    decide
  have h0 : overflowExample ≠ [] := by simp [overflowExample]
  simp [overflowExample_isValidSignatureEncoding, hl, hh, hs, h0]

/-! ## Hash types -/

/-- For every byte, clearing the top bit with `~~~0x80` and with `&&& 0x7f` agree. -/
theorem and_not_80 (b : UInt8) : b &&& ~~~0x80 = b &&& 0x7f := by
  have : (~~~0x80 : UInt8) = 0x7f := by decide
  rw [this]

/-- `isDefinedHashtypeSignature` holds exactly when the last byte, without the `0x80` bit, is 1, 2 or 3. -/
theorem isDefinedHashtypeSignature_iff (sig : List UInt8) :
    isDefinedHashtypeSignature sig = true ↔
      ∃ b, sig.getLast? = some b ∧ (b &&& 0x7f = 1 ∨ b &&& 0x7f = 2 ∨ b &&& 0x7f = 3) := by
  unfold isDefinedHashtypeSignature
  split
  · simp_all
  · rename_i b hb
    simp only [hb, Option.some.injEq, exists_eq_left', and_not_80]
    generalize b &&& 0x7f = h
    obtain ⟨n, hn, rfl⟩ : ∃ n, n < 256 ∧ h = n.toUInt8 := ⟨h.toNat, h.toNat_lt, by simp⟩
    revert n
    decide +kernel

/-! ## Public keys -/

/-- `isCompressedOrUncompressedPubKey` holds exactly for 65 bytes starting with `0x04`, and 33 bytes starting with `0x02` or `0x03`. -/
theorem isCompressedOrUncompressedPubKey_iff (pubKey : List UInt8) :
    isCompressedOrUncompressedPubKey pubKey = true ↔
      (∃ x, pubKey = 0x04 :: x ∧ x.length = 64) ∨
      (∃ p x, (p = 0x02 ∨ p = 0x03) ∧ pubKey = p :: x ∧ x.length = 32) := by
  unfold isCompressedOrUncompressedPubKey
  match pubKey with
  | [] => simp
  | p :: x =>
    simp only [List.length_cons, List.getD_cons_zero, List.cons.injEq]
    by_cases h4 : p = 0x04
    · subst h4; simp; omega
    by_cases h23 : p = 0x02 ∨ p = 0x03
    · rcases h23 with rfl | rfl <;> simp <;> omega
    · simp only [not_or] at h23
      simp_all

/-- `checkPubKeyEncoding` fails exactly with `PUBKEYTYPE`, with `STRICTENC`, for a key that fails `isCompressedOrUncompressedPubKey`. -/
theorem checkPubKeyEncoding_eq_error_iff (pubKey : List UInt8) (flags : UInt32) (e : ScriptError) :
    checkPubKeyEncoding pubKey flags = .error e ↔
      e = .pubkeyType ∧ hasFlag flags ScriptFlags.strictEnc = true ∧
        isCompressedOrUncompressedPubKey pubKey = false := by
  unfold checkPubKeyEncoding
  cases hs : hasFlag flags ScriptFlags.strictEnc <;> cases hk : isCompressedOrUncompressedPubKey pubKey <;>
    simp [eq_comm]

/-- Every key that passes `isCompressedOrUncompressedPubKey` gives a valid `CPubKey`. -/
theorem isValidPubKey_of_isCompressedOrUncompressedPubKey {pubKey : List UInt8}
    (h : isCompressedOrUncompressedPubKey pubKey = true) : isValidPubKey pubKey = true := by
  rcases (isCompressedOrUncompressedPubKey_iff pubKey).mp h with ⟨x, rfl, hx⟩ | ⟨p, x, hp, rfl, hx⟩
  · simp [isValidPubKey, pubKeyLength, hx]
  · rcases hp with rfl | rfl <;> simp [isValidPubKey, pubKeyLength, hx]

end DogeLib.Script
