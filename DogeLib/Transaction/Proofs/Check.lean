module

public import DogeLib.Transaction.Check

/-!
# Proofs: the duplicate-input test of `CheckTransaction`

`hasDuplicate` inserts the key of each outpoint into a `Std.TreeSet`, and stops at the first key that is already there.
This module proves it equal to `hasDuplicateScan`, which compares every pair, and both equal to the negation of `List.Nodup`.

- `OutPoint.key_inj`: different outpoints have different keys.
- `hasDuplicateScan_eq_not_nodup`: `hasDuplicateScan` is true exactly when the list has two equal entries.
- `hasDuplicateFrom_iff`: the loop finds a key that is already in the set, or two equal keys of the list.
- `hasDuplicate_eq_not_nodup`, `hasDuplicate_eq_hasDuplicateScan`: the set test, the test of every pair and `List.Nodup` agree on every list.
-/

@[expose] public section

namespace DogeLib.Transaction

/-- For all bytes `bs`, `bytesValue bs` is below `2 ^ (8 * bs.length)`. -/
theorem bytesValue_lt : ∀ bs : List UInt8, bytesValue bs < 2 ^ (8 * bs.length)
  | [] => by simp [bytesValue]
  | b :: bs => by
    have ih := bytesValue_lt bs
    have hb := b.toNat_lt
    have e : 2 ^ (8 * (bs.length + 1)) = 2 ^ 8 * 2 ^ (8 * bs.length) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    have : 2 ^ 8 * (bytesValue bs + 1) ≤ 2 ^ 8 * 2 ^ (8 * bs.length) := Nat.mul_le_mul_left _ ih
    rw [List.length_cons, e, bytesValue]
    rw [Nat.mul_succ] at this
    omega

/-- For all lists of bytes `a` and `b` of the same length: equal values give equal lists. -/
theorem bytesValue_inj : ∀ {a b : List UInt8}, a.length = b.length → bytesValue a = bytesValue b → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [bytesValue] at h
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : bytesValue a = bytesValue b := by omega
    rw [UInt8.toNat_inj.mp h1, bytesValue_inj (by simpa using hl) h2]

/-- For all outpoints `a` and `b`: equal keys give equal outpoints. -/
theorem OutPoint.key_inj {a b : OutPoint} (h : a.key = b.key) : a = b := by
  obtain ⟨⟨ha, hal⟩, na⟩ := a
  obtain ⟨⟨hb, hbl⟩, nb⟩ := b
  have la := bytesValue_lt ha
  have lb := bytesValue_lt hb
  rw [hal] at la; rw [hbl] at lb
  simp only [OutPoint.key] at h
  have h1 : bytesValue ha = bytesValue hb := by omega
  have h2 : na.toNat = nb.toNat := by omega
  obtain rfl := bytesValue_inj (by rw [hal, hbl]) h1
  obtain rfl := UInt32.toNat_inj.mp h2
  rfl

/--
For every set `seen` and list `l` of keys: `hasDuplicateFrom seen l` is true exactly when `seen` holds a key of `l`, or `l` has two equal entries.
-/
theorem hasDuplicateFrom_iff : ∀ (seen : Std.TreeSet Nat) (l : List Nat),
    hasDuplicateFrom seen l = true ↔ (∃ k ∈ l, seen.contains k = true) ∨ ¬ l.Nodup
  | seen, [] => by simp [hasDuplicateFrom]
  | seen, k :: ks => by
    rw [hasDuplicateFrom, Bool.or_eq_true, hasDuplicateFrom_iff (seen.insert k) ks]
    simp only [Std.TreeSet.contains_insert, Bool.or_eq_true, beq_iff_eq, Nat.compare_eq_eq,
      List.mem_cons, List.nodup_cons, exists_eq_or_imp]
    constructor
    · rintro (h | ⟨x, hx, rfl | h⟩ | h)
      · exact .inl (.inl h)
      · exact .inr fun hn => hn.1 hx
      · exact .inl (.inr ⟨x, hx, h⟩)
      · exact .inr fun hn => h hn.2
    · rintro ((h | ⟨x, hx, h⟩) | h)
      · exact .inl h
      · exact .inr (.inl ⟨x, hx, .inr h⟩)
      · by_cases hk : k ∈ ks
        · exact .inr (.inl ⟨k, hk, .inl rfl⟩)
        · exact .inr (.inr fun hn => h ⟨hk, hn⟩)

/-- For every list of outpoints, `hasDuplicateScan` is true exactly when two entries of the list are equal. -/
theorem hasDuplicateScan_eq_not_nodup : ∀ l : List OutPoint, hasDuplicateScan l = !decide l.Nodup
  | [] => by simp [hasDuplicateScan]
  | o :: rest => by
    rw [hasDuplicateScan, hasDuplicateScan_eq_not_nodup rest]
    by_cases h : o ∈ rest <;> simp [h, List.nodup_cons]

/-- For every list of outpoints, `hasDuplicate` is true exactly when two entries of the list are equal. -/
theorem hasDuplicate_eq_not_nodup (l : List OutPoint) : hasDuplicate l = !decide l.Nodup := by
  rw [Bool.eq_iff_iff, hasDuplicate, hasDuplicateFrom_iff]
  simp only [Std.TreeSet.contains_emptyc, Bool.false_eq_true, and_false, exists_false, false_or,
    Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h hnd
    exact h (List.pairwise_map.mpr (hnd.imp fun h e => h (OutPoint.key_inj e)))
  · intro h hk
    exact h ((List.pairwise_map.mp hk).imp fun h e => h (congrArg _ e))

/-- For every list of outpoints, the test `hasDuplicate` equals `hasDuplicateScan`, the test of every pair. -/
theorem hasDuplicate_eq_hasDuplicateScan (l : List OutPoint) : hasDuplicate l = hasDuplicateScan l := by
  rw [hasDuplicate_eq_not_nodup, hasDuplicateScan_eq_not_nodup]
