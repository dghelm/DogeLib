module

public import DogeLib.Work.NextWork
public import DogeLib.Work.Proofs.Consensus

/-! Properties of finite-view next-work selection. -/

@[expose] public section

namespace DogeLib.Work

/-- At a previous height of at least 145000, the local retarget interval is one for every parameter record. -/
theorem retargetInterval_after (params : WorkParams) (height : Nat) (h : 145000 ≤ height) :
    retargetInterval params height = 1 := by simp [retargetInterval, h]

/-- Below previous height 145000, the local interval is the selected record's interval. -/
theorem retargetInterval_before (params : WorkParams) (height : Nat) (h : height < 145000) :
    retargetInterval params height = params.difficultyAdjustmentInterval := by
  simp [retargetInterval, show ¬ height ≥ 145000 by omega]

/-- The first retarget looks back one fewer than the interval, for every interval and previous height whose successor is the interval. -/
theorem blocksToGoBack_first (interval height : Nat) (h : height + 1 = interval) :
    blocksToGoBack interval height = interval - 1 := by simp [blocksToGoBack, h]

/-- Every later retarget looks back the full interval, when the successor height differs from the interval. -/
theorem blocksToGoBack_later (interval height : Nat) (h : height + 1 ≠ interval) :
    blocksToGoBack interval height = interval := by simp [blocksToGoBack, h]

/-- At a retarget with a positive interval, the first-height subtraction cannot underflow.
The hypotheses are exactly positivity and divisibility of the next height. -/
theorem blocksToGoBack_le (interval height : Nat) (positive : 0 < interval)
    (retarget : (height + 1) % interval = 0) : blocksToGoBack interval height ≤ height := by
  have le : interval ≤ height + 1 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero retarget)
  unfold blocksToGoBack
  split <;> omega

/-- With a null tip, every parameter record and candidate time return compact powLimit. -/
theorem getNextWorkRequired_genesis (params : WorkParams) (time : UInt32) :
    getNextWorkRequired params [] time = .ok (ArithUint256.getCompact params.powLimit) := rfl

/-- On a view that passes validation, the DigiShield minimum-difficulty condition returns compact powLimit for every candidate time satisfying it. -/
theorem getNextWorkRequired_minDifficulty (params : WorkParams) (last : BlockIndex)
    (rest : List BlockIndex) (time : UInt32)
    (valid : validateWorkView (last :: rest) = .ok ())
    (allowed : allowDigishieldMinDifficultyForBlock params last time = true) :
    getNextWorkRequired params (last :: rest) time =
      .ok (ArithUint256.getCompact params.powLimit) := by
  simp [getNextWorkRequired, valid, getNextWorkRequiredFromView, allowed]
  rfl

/-- A successful recovery returns the compact target of an entry in the supplied view, for every interval and limit.
This claim does not require target validity or coherent heights. -/
theorem recoverLastNonMinDifficulty_mem (interval : Nat) (limit : UInt32)
    (view : List BlockIndex) (bits : UInt32)
    (success : recoverLastNonMinDifficulty interval limit view = .ok bits) :
    ∃ entry ∈ view, entry.nBits = bits := by
  induction view with
  | nil => simp [recoverLastNonMinDifficulty] at success
  | cons entry rest ih =>
    simp only [recoverLastNonMinDifficulty] at success
    split at success
    · cases success
      exact ⟨entry, by simp, rfl⟩
    · cases rest with
      | nil => simp at success
      | cons prev rest =>
        obtain ⟨found, member, eq⟩ := ih success
        exact ⟨found, List.mem_cons_of_mem entry member, eq⟩

/-- From previous height 145000, the non-retarget branch cannot execute, for any parameter record.
Thus it cannot reach legacy recovery, including for selected testnet records. -/
theorem retargetInterval_no_recovery (params : WorkParams) (height : Nat)
    (h : 145000 ≤ height) : (height + 1) % retargetInterval params height = 0 := by
  rw [retargetInterval_after params height h]
  exact Nat.mod_one _

/-- Whenever the caller is off a retarget boundary, the local interval equals the record's interval, for every parameter record and previous height.
The recovery branch can therefore never observe different intervals. -/
theorem retargetInterval_eq_record_of_nonretarget (params : WorkParams) (height : Nat)
    (off : (height + 1) % retargetInterval params height ≠ 0) :
    retargetInterval params height = params.difficultyAdjustmentInterval := by
  have before : height < 145000 := by
    by_cases after : 145000 ≤ height
    · exact False.elim (off (retargetInterval_no_recovery params height after))
    · omega
  exact retargetInterval_before params height before

/-! ## Depth and completeness on checked views -/

/-- A view of two or more entries passes `validateWorkView` exactly when three conditions hold.
The first height is below 2147483647, the first entry links to the second, and the rest passes. -/
theorem validateWorkView_cons_cons (entry prev : BlockIndex) (rest : List BlockIndex) :
    validateWorkView (entry :: prev :: rest) = .ok () ↔
      entry.nHeight < 2147483647 ∧ entry.nHeight = prev.nHeight + 1 ∧
        validateWorkView (prev :: rest) = .ok () := by
  conv => lhs; rw [validateWorkView]
  by_cases range : entry.nHeight ≥ 2147483647
  · have out : ¬ entry.nHeight < 2147483647 := by omega
    simp [range, out, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · have inside : entry.nHeight < 2147483647 := by omega
    by_cases link : entry.nHeight = prev.nHeight + 1
    · have prevInside : ¬ 2147483646 ≤ prev.nHeight := by omega
      simp [link, prevInside]
      omega
    · simp [range, link, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A checked view whose last entry has height 0 has one entry more than the height of its first entry. -/
theorem length_of_validateWorkView (entry : BlockIndex) (rest : List BlockIndex)
    (valid : validateWorkView (entry :: rest) = .ok ())
    (genesis : (entry :: rest).getLast?.map BlockIndex.nHeight = some 0) :
    rest.length = entry.nHeight := by
  induction rest generalizing entry with
  | nil => simp at genesis; simp [genesis]
  | cons prev rest ih =>
    obtain ⟨-, link, valid'⟩ := (validateWorkView_cons_cons entry prev rest).mp valid
    have := ih prev valid' (by simpa [List.getLast?_cons_cons] using genesis)
    simp only [List.length_cons]
    omega

/-- For a positive interval, if `(p + 1) % i` is not zero, then it is `p % i + 1`. -/
private theorem succ_mod_of_ne_zero (p i : Nat) (positive : 0 < i) (h : (p + 1) % i ≠ 0) :
    (p + 1) % i = p % i + 1 := by
  have lt := Nat.mod_lt p positive
  by_cases one : i = 1
  · subst one; simp [Nat.mod_one] at h
  · have key : (p + 1) % i = (p % i + 1) % i := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < i by omega)]
    by_cases top : p % i + 1 < i
    · rw [key, Nat.mod_eq_of_lt top]
    · have : p % i + 1 = i := by omega
      rw [key, this, Nat.mod_self] at h
      exact absurd rfl h

/--
Prefix congruence of the recovery walk.
Let the interval be positive, and let the first view pass `validateWorkView`.
Let two views start with the same entry and agree on their first `n` entries.
If `n` is greater than the first height modulo the interval, the walk returns the same result.
The walk stops at the latest at a height divisible by the interval, so it reads no entry after the first `n`.
-/
theorem recoverLastNonMinDifficulty_congr_prefix (interval : Nat) (positive : 0 < interval)
    (limit : UInt32) (n : Nat) (entry : BlockIndex) (rest₁ rest₂ : List BlockIndex)
    (valid : validateWorkView (entry :: rest₁) = .ok ())
    (deep : entry.nHeight % interval < n)
    (agree : (entry :: rest₁).take n = (entry :: rest₂).take n) :
    recoverLastNonMinDifficulty interval limit (entry :: rest₁) =
      recoverLastNonMinDifficulty interval limit (entry :: rest₂) := by
  induction rest₁ generalizing n entry rest₂ with
  | nil =>
    simp only [recoverLastNonMinDifficulty]
    split
    · rfl
    · rename_i stop
      have nonzero : entry.nHeight % interval ≠ 0 := fun h => stop (.inl h)
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      cases rest₂ with
      | nil => rfl
      | cons _ _ => simp at agree
  | cons prev rest ih =>
    obtain ⟨-, link, valid'⟩ := (validateWorkView_cons_cons entry prev rest).mp valid
    simp only [recoverLastNonMinDifficulty]
    split
    · rfl
    · rename_i stop
      have nonzero : entry.nHeight % interval ≠ 0 := fun h => stop (.inl h)
      have step : entry.nHeight % interval = prev.nHeight % interval + 1 := by
        rw [link] at nonzero ⊢
        exact succ_mod_of_ne_zero _ _ positive nonzero
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      cases rest₂ with
      | nil => simp at agree
      | cons prev₂ rest₂ =>
        simp only [List.take_succ_cons, List.cons.injEq] at agree
        obtain ⟨rfl, agree'⟩ := agree.2
        exact ih (m + 1) prev rest₂ valid' (by omega) (by simp [agree'])

/--
Prefix congruence of `getNextWorkRequiredFromView`.
Let the first view pass `validateWorkView`, and let `d = retargetInterval params last.nHeight + 1`.
Let two views start with the same entry `last` and agree on their first `d` entries.
Then they give the same result for every record and candidate time.
A retarget reads the entry at index `blocksToGoBack`, at most the interval, and the recovery walk reads fewer than `d` entries.
-/
theorem getNextWorkRequiredFromView_congr_prefix (params : WorkParams) (last : BlockIndex)
    (rest₁ rest₂ : List BlockIndex) (time : UInt32)
    (valid : validateWorkView (last :: rest₁) = .ok ())
    (agree : (last :: rest₁).take (retargetInterval params last.nHeight + 1) =
      (last :: rest₂).take (retargetInterval params last.nHeight + 1)) :
    getNextWorkRequiredFromView params (last :: rest₁) time =
      getNextWorkRequiredFromView params (last :: rest₂) time := by
  have index : ∀ i, i ≤ retargetInterval params last.nHeight →
      (last :: rest₁)[i]? = (last :: rest₂)[i]? := by
    intro i hi
    have := congrArg (·[i]?) agree
    rwa [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)] at this
  simp only [getNextWorkRequiredFromView]
  split
  · rfl
  · split
    · rfl
    · rename_i nonzero
      split
      · rename_i off
        have off' : (last.nHeight + 1) % retargetInterval params last.nHeight ≠ 0 := by
          simpa using off
        have eq := retargetInterval_eq_record_of_nonretarget params last.nHeight off'
        have positive : 0 < params.difficultyAdjustmentInterval := by omega
        rw [recoverLastNonMinDifficulty_congr_prefix params.difficultyAdjustmentInterval positive _
          (params.difficultyAdjustmentInterval + 1) last rest₁ rest₂ valid
          (by have := Nat.mod_lt last.nHeight positive; omega) (by rw [← eq]; exact agree)]
      · rw [index (blocksToGoBack (retargetInterval params last.nHeight) last.nHeight)
          (by unfold blocksToGoBack; split <;> omega)]

/--
Prefix congruence of `nextWorkRequired`.
Let two views pass `validateWorkView` and start with the same entry `last`.
Let `d = retargetInterval params last.nHeight + 1`, where `params` is the record that `getConsensus` selects at the candidate height `last.nHeight + 1`.
If the views agree on their first `d` entries, they give the same result for every network and candidate time.
-/
theorem nextWorkRequired_congr_prefix (network : WorkNetwork) (last : BlockIndex)
    (rest₁ rest₂ : List BlockIndex) (time : UInt32)
    (valid₁ : validateWorkView (last :: rest₁) = .ok ())
    (valid₂ : validateWorkView (last :: rest₂) = .ok ())
    (agree : (last :: rest₁).take
        (retargetInterval (getConsensus network (UInt32.ofNat (last.nHeight + 1))) last.nHeight + 1) =
      (last :: rest₂).take
        (retargetInterval (getConsensus network (UInt32.ofNat (last.nHeight + 1))) last.nHeight + 1)) :
    nextWorkRequired network (last :: rest₁) time = nextWorkRequired network (last :: rest₂) time := by
  simp only [nextWorkRequired, valid₁, valid₂]
  exact congrArg (fun r => (do let _ ← (Except.ok () : Except NextWorkError Unit); r))
    (getNextWorkRequiredFromView_congr_prefix _ last rest₁ rest₂ time valid₁ agree)

/-- For every network and UInt32 height, the selected record has a positive `DifficultyAdjustmentInterval`.
The interval is 240 or 1 on mainnet and testnet, and 14400 or 1 on regtest. -/
theorem difficultyAdjustmentInterval_getConsensus_pos (network : WorkNetwork) (height : UInt32) :
    0 < (getConsensus network height).difficultyAdjustmentInterval := by
  cases network <;>
    simp only [getConsensus_mainnet, getConsensus_testnet, getConsensus_regtest] <;>
    repeat (any_goals (first | decide | (split <;> try dsimp only)))

/--
Completeness of the recovery walk.
Let the view pass `validateWorkView` with one entry more than the height of its first entry, so that it reaches height 0.
Then the walk returns a value and never `missingAncestor`, for every interval and limit.
The walk stops at the latest at height 0, because 0 modulo every interval is 0.
-/
theorem recoverLastNonMinDifficulty_ok (interval : Nat) (limit : UInt32)
    (entry : BlockIndex) (rest : List BlockIndex)
    (valid : validateWorkView (entry :: rest) = .ok ()) (length : rest.length = entry.nHeight) :
    ∃ bits, recoverLastNonMinDifficulty interval limit (entry :: rest) = .ok bits := by
  induction rest generalizing entry with
  | nil =>
    simp only [List.length_nil] at length
    refine ⟨entry.nBits, ?_⟩
    simp [recoverLastNonMinDifficulty, ← length]
  | cons prev rest ih =>
    obtain ⟨-, link, valid'⟩ := (validateWorkView_cons_cons entry prev rest).mp valid
    simp only [recoverLastNonMinDifficulty]
    split
    · exact ⟨_, rfl⟩
    · exact ih prev valid' (by simp only [List.length_cons] at length; omega)

/--
Completeness of `nextWorkRequired` on a view that reaches height 0.
Let the view pass `validateWorkView` and have one entry more than the height of its first entry.
Then `nextWorkRequired` returns a value, and no adapter error, for every network and candidate time.
-/
theorem nextWorkRequired_ok (network : WorkNetwork) (last : BlockIndex) (rest : List BlockIndex)
    (time : UInt32) (valid : validateWorkView (last :: rest) = .ok ())
    (length : rest.length = last.nHeight) :
    ∃ required, nextWorkRequired network (last :: rest) time = .ok required := by
  have positive := difficultyAdjustmentInterval_getConsensus_pos network (UInt32.ofNat (last.nHeight + 1))
  simp only [nextWorkRequired, valid]
  generalize getConsensus network (UInt32.ofNat (last.nHeight + 1)) = params at positive ⊢
  have intervalPositive : 0 < retargetInterval params last.nHeight := by
    unfold retargetInterval; split <;> omega
  simp only [getNextWorkRequiredFromView]
  split
  · exact ⟨_, rfl⟩
  · split
    · omega
    · split
      · split
        · split
          · exact ⟨_, rfl⟩
          · obtain ⟨bits, eq⟩ := recoverLastNonMinDifficulty_ok params.difficultyAdjustmentInterval
              (ArithUint256.getCompact params.powLimit) last rest valid length
            exact ⟨bits, by rw [eq]; rfl⟩
        · exact ⟨_, rfl⟩
      · rename_i retarget
        have le := blocksToGoBack_le _ _ intervalPositive (by simpa using retarget)
        have notBelow : ¬ last.nHeight < blocksToGoBack (retargetInterval params last.nHeight) last.nHeight := by
          omega
        have present : blocksToGoBack (retargetInterval params last.nHeight) last.nHeight <
            (last :: rest).length := by
          simp only [List.length_cons]; omega
        simp only [notBelow, ite_false, List.getElem?_eq_getElem present]
        exact ⟨_, rfl⟩

end DogeLib.Work
