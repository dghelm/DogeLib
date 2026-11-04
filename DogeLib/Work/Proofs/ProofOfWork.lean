module

public import DogeLib.Work.ProofOfWork
public import DogeLib.Work.Proofs.ArithUint256Bytes
public import DogeLib.Work.Proofs.Retarget
public import DogeLib.Work.Proofs.Consensus

/-!
# Properties of the supplied-hash check

Target validity supplies the old-target bound for the retarget.
The numerical parameter bounds remain explicit in the general theorems.
-/

@[expose] public section

namespace DogeLib.Work

/-- For every supplied hash, the word conversion equals the independent radix-256 interpretation of its internal bytes. -/
theorem hashToArith256_eq (hash : Hash256) :
    hashToArith256 hash = ArithUint256.ofTargetBytes
      (fun i => hash.val[i.val]'(by have := hash.property; omega)) :=
  ArithUint256.Words.uintToArith256_toArith _

/-- For every compact and parameter record, target validity is exactly the four range conditions checked by Core. -/
theorem validProofOfWorkTarget_iff (nBits : UInt32) (params : RetargetParams) :
    validProofOfWorkTarget nBits params = true ↔
      (ArithUint256.setCompact nBits).fNegative = false ∧
      (ArithUint256.setCompact nBits).value ≠ 0 ∧
      (ArithUint256.setCompact nBits).fOverflow = false ∧
      (ArithUint256.setCompact nBits).value ≤ params.powLimit := by
  simp [validProofOfWorkTarget, and_assoc]

/-- For every supplied hash, compact and parameter record, acceptance means target validity and a hash at most the decoded target. -/
theorem checkProofOfWork_iff (hash : Hash256) (nBits : UInt32) (params : RetargetParams) :
    checkProofOfWork hash nBits params = true ↔
      validProofOfWorkTarget nBits params = true ∧
      hashToArith256 hash ≤ (ArithUint256.setCompact nBits).value := by
  simp [checkProofOfWork]

/-- The all-zero hash represents the arithmetic value zero. -/
theorem hashToArith256_zero : hashToArith256 Hash256.zero = 0 := by
  decide +kernel

/-- For every compact and parameter record, target validity is equivalent to acceptance of some supplied hash.
The all-zero hash witnesses the forward implication. -/
theorem validProofOfWorkTarget_iff_exists_hash (nBits : UInt32) (params : RetargetParams) :
    validProofOfWorkTarget nBits params = true ↔
      ∃ hash : Hash256, checkProofOfWork hash nBits params = true := by
  constructor
  · intro valid
    exact ⟨Hash256.zero, (checkProofOfWork_iff _ _ _).2 ⟨valid, by
      rw [hashToArith256_zero]; exact Fin.zero_le _⟩⟩
  · rintro ⟨hash, accepted⟩
    exact ((checkProofOfWork_iff hash nBits params).1 accepted).1

/-- For every fixed compact and parameter record, a smaller supplied hash is accepted whenever the original hash is accepted. -/
theorem checkProofOfWork_mono (hash smaller : Hash256) (nBits : UInt32) (params : RetargetParams)
    (accepted : checkProofOfWork hash nBits params = true)
    (le : hashToArith256 smaller ≤ hashToArith256 hash) :
    checkProofOfWork smaller nBits params = true := by
  obtain ⟨valid, bound⟩ := (checkProofOfWork_iff _ _ _).1 accepted
  exact (checkProofOfWork_iff _ _ _).2 ⟨valid, Fin.le_trans le bound⟩

/-- For every height and actual timespan, target validity prevents retarget multiplication wrap if `powLimit * 4T < 2^256`. -/
theorem no_wrap_of_validProofOfWorkTarget (params : RetargetParams) (nHeight : Int32)
    (nActualTimespan : Int) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits params = true)
    (limit : params.powLimit.val * (params.retargetTimespan * 4).toNat < 2 ^ 256) :
    (ArithUint256.setCompact nBits).value.val *
      (modulatedTimespan params nHeight nActualTimespan).toNat < 2 ^ 256 :=
  no_wrap_of_le_powLimit params nHeight nActualTimespan nBits
    ((validProofOfWorkTarget_iff _ _).1 valid).2.2.2 limit

/-- For all retarget inputs, a valid previous target gives the exact closed form when `T < 2^30` and `powLimit * 4T < 2^256`. -/
theorem retarget_eq_of_validProofOfWorkTarget (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits params = true)
    (timespan : params.retargetTimespan < 2 ^ 30)
    (limit : params.powLimit.val * (params.retargetTimespan * 4).toNat < 2 ^ 256) :
    calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
      ArithUint256.getCompact (ArithUint256.ofNat (min ((ArithUint256.setCompact nBits).value.val *
        (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat /
        params.retargetTimespan.toNat) params.powLimit.val)) :=
  retarget_eq_of_no_wrap params nHeight nLastBlockTime nFirstBlockTime nBits timespan
    (no_wrap_of_validProofOfWorkTarget params nHeight _ nBits valid limit)

/-- At every selection height, all mainnet records satisfy the timespan and target bounds for the exact retarget form. -/
theorem mainnet_proofOfWork_bounds (selectionHeight : UInt32) :
    let params := (getConsensus .mainnet selectionHeight).toRetargetParams
    params.retargetTimespan < 2 ^ 30 ∧
      params.powLimit.val * (params.retargetTimespan * 4).toNat < 2 ^ 256 := by
  rw [getConsensus_mainnet]
  split <;> decide

/-- At every mainnet parameter-selection height, every valid previous target prevents multiplication wrap for all retarget heights and timespans. -/
theorem mainnet_no_wrap_of_validProofOfWorkTarget (selectionHeight : UInt32)
    (nHeight : Int32) (nActualTimespan : Int) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits (getConsensus .mainnet selectionHeight).toRetargetParams = true) :
    (ArithUint256.setCompact nBits).value.val *
      (modulatedTimespan (getConsensus .mainnet selectionHeight).toRetargetParams nHeight nActualTimespan).toNat < 2 ^ 256 :=
  no_wrap_of_validProofOfWorkTarget _ _ _ _ valid (mainnet_proofOfWork_bounds selectionHeight).2

/-- At every mainnet parameter-selection height, a valid previous target gives the exact retarget form for every retarget height and pair of times. -/
theorem mainnet_retarget_eq_of_validProofOfWorkTarget (selectionHeight : UInt32)
    (nHeight : Int32) (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits (getConsensus .mainnet selectionHeight).toRetargetParams = true) :
    let params := (getConsensus .mainnet selectionHeight).toRetargetParams
    calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
      ArithUint256.getCompact (ArithUint256.ofNat (min ((ArithUint256.setCompact nBits).value.val *
        (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat /
        params.retargetTimespan.toNat) params.powLimit.val)) :=
  retarget_eq_of_validProofOfWorkTarget _ _ _ _ _ valid
    (mainnet_proofOfWork_bounds selectionHeight).1 (mainnet_proofOfWork_bounds selectionHeight).2

/-- At every selection height, all testnet records satisfy the timespan and target bounds for the exact retarget form. -/
theorem testnet_proofOfWork_bounds (selectionHeight : UInt32) :
    let params := (getConsensus .testnet selectionHeight).toRetargetParams
    params.retargetTimespan < 2 ^ 30 ∧
      params.powLimit.val * (params.retargetTimespan * 4).toNat < 2 ^ 256 := by
  rw [getConsensus_testnet]
  split <;> (try split) <;> decide

/-- At every testnet parameter-selection height, every valid previous target prevents multiplication wrap for all retarget heights and timespans. -/
theorem testnet_no_wrap_of_validProofOfWorkTarget (selectionHeight : UInt32)
    (nHeight : Int32) (nActualTimespan : Int) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits (getConsensus .testnet selectionHeight).toRetargetParams = true) :
    (ArithUint256.setCompact nBits).value.val *
      (modulatedTimespan (getConsensus .testnet selectionHeight).toRetargetParams nHeight nActualTimespan).toNat < 2 ^ 256 :=
  no_wrap_of_validProofOfWorkTarget _ _ _ _ valid (testnet_proofOfWork_bounds selectionHeight).2

/-- At every testnet parameter-selection height, a valid previous target gives the exact retarget form for every retarget height and pair of times. -/
theorem testnet_retarget_eq_of_validProofOfWorkTarget (selectionHeight : UInt32)
    (nHeight : Int32) (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32)
    (valid : validProofOfWorkTarget nBits (getConsensus .testnet selectionHeight).toRetargetParams = true) :
    let params := (getConsensus .testnet selectionHeight).toRetargetParams
    calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
      ArithUint256.getCompact (ArithUint256.ofNat (min ((ArithUint256.setCompact nBits).value.val *
        (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat /
        params.retargetTimespan.toNat) params.powLimit.val)) :=
  retarget_eq_of_validProofOfWorkTarget _ _ _ _ _ valid
    (testnet_proofOfWork_bounds selectionHeight).1 (testnet_proofOfWork_bounds selectionHeight).2

/-- For every height and actual timespan, regtest's DigiShield record clamps the multiplier to one. -/
theorem regtestDigishield_modulatedTimespan (nHeight : Int32) (nActualTimespan : Int) :
    modulatedTimespan regtestDigishieldWorkParams.toRetargetParams nHeight nActualTimespan = 1 := by
  have bounds := modulatedTimespan_mem regtestDigishieldWorkParams.toRetargetParams nHeight nActualTimespan
  have limits : timespanLimits regtestDigishieldWorkParams.toRetargetParams nHeight = (1, 1) := by rfl
  rw [limits] at bounds
  dsimp only at bounds
  omega

/-- At every regtest selection height from ten, multiplication cannot wrap for any compact, retarget height or actual timespan.
The multiplier is one, so target validity is unnecessary. -/
theorem regtest_no_wrap (selectionHeight : UInt32) (active : 10 ≤ selectionHeight)
    (nHeight : Int32) (nActualTimespan : Int) (nBits : UInt32) :
    (ArithUint256.setCompact nBits).value.val *
      (modulatedTimespan (getConsensus .regtest selectionHeight).toRetargetParams nHeight nActualTimespan).toNat < 2 ^ 256 := by
  rw [getConsensus_regtest, ite_eq_right (by simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega), regtestDigishield_modulatedTimespan]
  simpa only [Int.toNat_one, Nat.mul_one] using (ArithUint256.setCompact nBits).value.isLt

/-- At every regtest selection height from ten, the exact retarget form holds for every compact, retarget height and pair of times. -/
theorem regtest_retarget_eq (selectionHeight : UInt32) (active : 10 ≤ selectionHeight)
    (nHeight : Int32) (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) :
    let params := (getConsensus .regtest selectionHeight).toRetargetParams
    calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
      ArithUint256.getCompact (ArithUint256.ofNat (min ((ArithUint256.setCompact nBits).value.val *
        (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat /
        params.retargetTimespan.toNat) params.powLimit.val)) := by
  apply retarget_eq_of_no_wrap
  · rw [getConsensus_regtest, ite_eq_right (by simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega)]
    decide
  · exact regtest_no_wrap selectionHeight active _ _ _

/-- A valid legacy regtest target can wrap Core's multiplication modulo 2^256.
For compact `0x207fffff` and timespan 901, the retarget returns `0x1f02467a`.
The clamped timespan is 901, and its product exceeds 2^256. -/
theorem legacy_regtest_wrap_example :
    validProofOfWorkTarget 0x207fffff regtestWorkParams.toRetargetParams = true ∧
    modulatedTimespan regtestWorkParams.toRetargetParams 1 901 = 901 ∧
    2 ^ 256 ≤ (ArithUint256.setCompact 0x207fffff).value.val * 901 ∧
    calculateDogecoinNextWorkRequired regtestWorkParams.toRetargetParams 1 901 0 0x207fffff = 0x1f02467a := by
  decide +kernel

end DogeLib.Work
