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

end DogeLib.Work
