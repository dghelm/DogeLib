module

public import DogeLib.Work.MedianTimePast

/-! Properties of the median time past on a checked finite view. -/

@[expose] public section

namespace DogeLib.Work

/-- For every entry, Core's walk collects at least one time and at most `nMedianTimeSpan` times. -/
theorem medianTimeSpan_bounds (last : BlockIndex) :
    0 < medianTimeSpan last ∧ medianTimeSpan last ≤ nMedianTimeSpan := by
  simp only [medianTimeSpan, nMedianTimeSpan]
  omega

/-- For every view and count, `sortedTimes` is a permutation of the widened times of the first `count` entries. -/
theorem sortedTimes_perm (view : List BlockIndex) (count : Nat) :
    (sortedTimes view count).Perm ((view.take count).map BlockIndex.getBlockTime) :=
  List.mergeSort_perm _ _

/-- For every view and count, `sortedTimes` is in ascending order: each element is at most every later element. -/
theorem sortedTimes_sorted (view : List BlockIndex) (count : Nat) :
    (sortedTimes view count).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Int => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((view.take count).map BlockIndex.getBlockTime)
  exact sorted.imp (by simp)

/-- For every view and count, `sortedTimes` has one element for each of the first `count` entries. -/
theorem length_sortedTimes (view : List BlockIndex) (count : Nat) :
    (sortedTimes view count).length = min count view.length := by
  simp [sortedTimes]

/-- The empty view returns `emptyView`. -/
theorem medianTimePast_nil : medianTimePast [] = .error .emptyView := rfl

/-- Every view that `validateWorkView` rejects returns `invalidView` with the same error. -/
theorem medianTimePast_invalid (view : List BlockIndex) (error : NextWorkError)
    (invalid : validateWorkView view = .error error) :
    medianTimePast view = .error (.invalidView error) := by
  simp [medianTimePast, invalid]
  rfl

/-- A checked view with fewer than `medianTimeSpan last` entries returns `shortView`.
Here `last` is the first entry, and the view has `rest.length + 1` entries. -/
theorem medianTimePast_short (last : BlockIndex) (rest : List BlockIndex)
    (valid : validateWorkView (last :: rest) = .ok ())
    (short : rest.length + 1 < medianTimeSpan last) :
    medianTimePast (last :: rest) = .error .shortView := by
  simp only [medianTimePast, valid]
  split
  · omega
  · rfl

/-- The median characterization.
Let `h` be the height of the first entry `last`, and let `k = min 11 (h + 1)` be `medianTimeSpan last`.
For a view that passes `validateWorkView` and has at least `k` entries, the result is the element at index `k / 2` of `sortedTimes`.
`sortedTimes` is the ascending sort of the widened times of the first `k` entries (`sortedTimes_perm`, `sortedTimes_sorted`).
For an even `k`, that element is the upper median. -/
theorem medianTimePast_eq (last : BlockIndex) (rest : List BlockIndex)
    (valid : validateWorkView (last :: rest) = .ok ())
    (deep : medianTimeSpan last ≤ rest.length + 1) :
    ∃ index : medianTimeSpan last / 2 < (sortedTimes (last :: rest) (medianTimeSpan last)).length,
      medianTimePast (last :: rest) =
        .ok (sortedTimes (last :: rest) (medianTimeSpan last))[medianTimeSpan last / 2] := by
  have span := medianTimeSpan_bounds last
  refine ⟨by rw [length_sortedTimes]; simp only [List.length_cons]; omega, ?_⟩
  simp only [medianTimePast, valid]
  split
  · rfl
  · contradiction

/-- A successful result is an element of `sortedTimes` for the first `medianTimeSpan last` entries, at index `medianTimeSpan last / 2`.
This form of `medianTimePast_eq` takes the success as its hypothesis, for every view whose first entry is `last`. -/
theorem medianTimePast_ok (last : BlockIndex) (rest : List BlockIndex) (median : Int)
    (success : medianTimePast (last :: rest) = .ok median) :
    validateWorkView (last :: rest) = .ok () ∧ medianTimeSpan last ≤ rest.length + 1 ∧
      (sortedTimes (last :: rest) (medianTimeSpan last))[medianTimeSpan last / 2]? = some median := by
  cases valid : validateWorkView (last :: rest) with
  | error error =>
    rw [medianTimePast_invalid _ error valid] at success
    cases success
  | ok u =>
    cases u
    by_cases deep : medianTimeSpan last ≤ rest.length + 1
    · obtain ⟨index, eq⟩ := medianTimePast_eq last rest valid deep
      rw [eq] at success
      cases success
      exact ⟨rfl, deep, List.getElem?_eq_getElem index⟩
    · rw [medianTimePast_short last rest valid (by omega)] at success
      cases success

/-- A successful result is the time of one of the first `medianTimeSpan last` entries, for every view whose first entry is `last`. -/
theorem medianTimePast_mem (last : BlockIndex) (rest : List BlockIndex) (median : Int)
    (success : medianTimePast (last :: rest) = .ok median) :
    ∃ entry ∈ (last :: rest).take (medianTimeSpan last), entry.getBlockTime = median := by
  obtain ⟨-, -, found⟩ := medianTimePast_ok last rest median success
  have member : median ∈ sortedTimes (last :: rest) (medianTimeSpan last) :=
    List.mem_of_getElem? found
  obtain ⟨entry, entryMember, eq⟩ :=
    List.mem_map.mp ((sortedTimes_perm (last :: rest) (medianTimeSpan last)).mem_iff.mp member)
  exact ⟨entry, entryMember, eq⟩

/-- A successful result lies between the least and the greatest time of the first `medianTimeSpan last` entries.
Each bound is the time of one of those entries, for every view whose first entry is `last`. -/
theorem medianTimePast_bounds (last : BlockIndex) (rest : List BlockIndex) (median : Int)
    (success : medianTimePast (last :: rest) = .ok median) :
    (∃ least ∈ (last :: rest).take (medianTimeSpan last), least.getBlockTime ≤ median ∧
      ∀ entry ∈ (last :: rest).take (medianTimeSpan last), least.getBlockTime ≤ entry.getBlockTime) ∧
    (∃ greatest ∈ (last :: rest).take (medianTimeSpan last), median ≤ greatest.getBlockTime ∧
      ∀ entry ∈ (last :: rest).take (medianTimeSpan last), entry.getBlockTime ≤ greatest.getBlockTime) := by
  obtain ⟨-, deep, found⟩ := medianTimePast_ok last rest median success
  have span := medianTimeSpan_bounds last
  let window := (last :: rest).take (medianTimeSpan last)
  let sorted := sortedTimes (last :: rest) (medianTimeSpan last)
  have perm : sorted.Perm (window.map BlockIndex.getBlockTime) := sortedTimes_perm _ _
  have ordered : sorted.Pairwise (· ≤ ·) := sortedTimes_sorted _ _
  have length : sorted.length = medianTimeSpan last := by
    simp only [sorted, length_sortedTimes, List.length_cons]
    omega
  have middle : medianTimeSpan last / 2 < sorted.length := by omega
  have medianEq : sorted[medianTimeSpan last / 2] = median := by
    have := List.getElem?_eq_getElem middle
    simp only [sorted] at this
    rw [this] at found
    exact Option.some.inj found
  have le_of_index : ∀ (i j : Nat) (hi : i < sorted.length) (hj : j < sorted.length),
      i ≤ j → sorted[i] ≤ sorted[j] := by
    intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with lt | eq
    · exact List.pairwise_iff_getElem.mp ordered i j hi hj lt
    · subst eq
      exact Int.le_refl _
  have entry_of_sorted : ∀ (i : Nat) (hi : i < sorted.length),
      ∃ entry ∈ window, entry.getBlockTime = sorted[i] := by
    intro i hi
    obtain ⟨entry, member, eq⟩ := List.mem_map.mp (perm.mem_iff.mp (List.getElem_mem hi))
    exact ⟨entry, member, eq⟩
  have sorted_of_entry : ∀ entry ∈ window,
      ∃ (i : Nat) (hi : i < sorted.length), sorted[i] = entry.getBlockTime := by
    intro entry member
    have := perm.mem_iff.mpr (List.mem_map_of_mem member)
    obtain ⟨i, hi, eq⟩ := List.getElem_of_mem this
    exact ⟨i, hi, eq⟩
  constructor
  · obtain ⟨least, member, eq⟩ := entry_of_sorted 0 (by omega)
    refine ⟨least, member, ?_, ?_⟩
    · rw [eq, ← medianEq]
      exact le_of_index _ _ _ _ (Nat.zero_le _)
    · intro entry entryMember
      obtain ⟨i, hi, eqi⟩ := sorted_of_entry entry entryMember
      rw [eq, ← eqi]
      exact le_of_index _ _ _ _ (Nat.zero_le _)
  · obtain ⟨greatest, member, eq⟩ := entry_of_sorted (sorted.length - 1) (by omega)
    refine ⟨greatest, member, ?_, ?_⟩
    · rw [eq, ← medianEq]
      exact le_of_index _ _ _ _ (by omega)
    · intro entry entryMember
      obtain ⟨i, hi, eqi⟩ := sorted_of_entry entry entryMember
      rw [eq, ← eqi]
      exact le_of_index _ _ _ _ (by omega)

/-- The rank property of the upper median.
Let `k = medianTimeSpan last`.
For a successful result, at least `k / 2 + 1` of the first `k` entries have a time at most the result.
At least `k - k / 2` of them have a time at least the result.
The statement does not mention `sortedTimes`, so it fixes the index `k / 2` independently of the sort. -/
theorem medianTimePast_rank (last : BlockIndex) (rest : List BlockIndex) (median : Int)
    (success : medianTimePast (last :: rest) = .ok median) :
    medianTimeSpan last / 2 + 1 ≤
        (((last :: rest).take (medianTimeSpan last)).filter
          (fun entry => decide (entry.getBlockTime ≤ median))).length ∧
      medianTimeSpan last - medianTimeSpan last / 2 ≤
        (((last :: rest).take (medianTimeSpan last)).filter
          (fun entry => decide (median ≤ entry.getBlockTime))).length := by
  obtain ⟨-, deep, found⟩ := medianTimePast_ok last rest median success
  have span := medianTimeSpan_bounds last
  let window := (last :: rest).take (medianTimeSpan last)
  let sorted := sortedTimes (last :: rest) (medianTimeSpan last)
  have perm : sorted.Perm (window.map BlockIndex.getBlockTime) := sortedTimes_perm _ _
  have ordered : sorted.Pairwise (· ≤ ·) := sortedTimes_sorted _ _
  have length : sorted.length = medianTimeSpan last := by
    simp only [sorted, length_sortedTimes, List.length_cons]
    omega
  have middle : medianTimeSpan last / 2 < sorted.length := by omega
  have medianEq : sorted[medianTimeSpan last / 2] = median := by
    have := List.getElem?_eq_getElem middle
    simp only [sorted] at this
    rw [this] at found
    exact Option.some.inj found
  have le_of_index : ∀ (i j : Nat) (hi : i < sorted.length) (hj : j < sorted.length),
      i ≤ j → sorted[i] ≤ sorted[j] := by
    intro i j hi hj hij
    rcases Nat.lt_or_eq_of_le hij with lt | eq
    · exact List.pairwise_iff_getElem.mp ordered i j hi hj lt
    · subst eq
      exact Int.le_refl _
  -- Count through the permutation: a filter of the window has the length of a count in `sorted`.
  have countEq : ∀ p : Int → Bool,
      (window.filter (fun entry => p entry.getBlockTime)).length = sorted.countP p := by
    intro p
    rw [perm.countP_eq, List.countP_map, List.countP_eq_length_filter]
    rfl
  have lowCount : medianTimeSpan last / 2 + 1 ≤ sorted.countP (fun t => decide (t ≤ median)) := by
    have split := List.take_append_drop (medianTimeSpan last / 2 + 1) sorted
    rw [← split, List.countP_append]
    have all : (sorted.take (medianTimeSpan last / 2 + 1)).countP (fun t => decide (t ≤ median)) =
        (sorted.take (medianTimeSpan last / 2 + 1)).length := by
      rw [List.countP_eq_length]
      intro t member
      obtain ⟨i, hi, eq⟩ := List.getElem_of_mem member
      rw [List.length_take] at hi
      rw [← eq, List.getElem_take, ← medianEq]
      simpa using le_of_index i _ (by omega) middle (by omega)
    rw [all, List.length_take]
    omega
  have highCount : medianTimeSpan last - medianTimeSpan last / 2 ≤
      sorted.countP (fun t => decide (median ≤ t)) := by
    have split := List.take_append_drop (medianTimeSpan last / 2) sorted
    rw [← split, List.countP_append]
    have all : (sorted.drop (medianTimeSpan last / 2)).countP (fun t => decide (median ≤ t)) =
        (sorted.drop (medianTimeSpan last / 2)).length := by
      rw [List.countP_eq_length]
      intro t member
      obtain ⟨i, hi, eq⟩ := List.getElem_of_mem member
      rw [List.length_drop] at hi
      rw [← eq, List.getElem_drop, ← medianEq]
      simpa using le_of_index _ _ middle (by omega) (by omega)
    rw [all, List.length_drop]
    omega
  exact ⟨by rw [countEq (fun t => decide (t ≤ median))]; exact lowCount,
    by rw [countEq (fun t => decide (median ≤ t))]; exact highCount⟩

/-- Prefix congruence.
Let `k = medianTimeSpan last`.
Two views that pass `validateWorkView`, start with the same entry `last` and agree on their first `k` entries give the same result.
The result is the same success or the same error, so entries after the first `k` never change it. -/
theorem medianTimePast_congr_prefix (last : BlockIndex) (rest₁ rest₂ : List BlockIndex)
    (valid₁ : validateWorkView (last :: rest₁) = .ok ())
    (valid₂ : validateWorkView (last :: rest₂) = .ok ())
    (agree : (last :: rest₁).take (medianTimeSpan last) = (last :: rest₂).take (medianTimeSpan last)) :
    medianTimePast (last :: rest₁) = medianTimePast (last :: rest₂) := by
  have lengths := congrArg List.length agree
  simp only [List.length_take, List.length_cons] at lengths
  by_cases deep₁ : medianTimeSpan last ≤ rest₁.length + 1
  · have deep₂ : medianTimeSpan last ≤ rest₂.length + 1 := by omega
    obtain ⟨_, eq₁⟩ := medianTimePast_eq last rest₁ valid₁ deep₁
    obtain ⟨_, eq₂⟩ := medianTimePast_eq last rest₂ valid₂ deep₂
    rw [eq₁, eq₂]
    simp only [sortedTimes, agree]
  · have short₂ : rest₂.length + 1 < medianTimeSpan last := by omega
    rw [medianTimePast_short last rest₁ valid₁ (by omega), medianTimePast_short last rest₂ valid₂ short₂]

end DogeLib.Work
