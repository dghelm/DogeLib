module

public import DogeLib.Work.RetargetWords
public import DogeLib.Work.Proofs.ArithUint256Compact
public import DogeLib.Work.Proofs.ArithUint256Bytes
public import DogeLib.Work.Proofs.Consensus

/-! # Agreement of the word retarget with the arithmetic specification -/

@[expose] public section

namespace DogeLib.Work

open ArithUint256

/-- Word comparison tests the arithmetic strict upper bound, for every pair of word arrays. -/
theorem ArithUint256.Words.compareTo_gt (a b : Words) :
    (Words.compareTo a b == .gt) = decide (Words.toArith a > Words.toArith b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Words.compareTo_eq, Nat.compare_eq_gt, decide_eq_true_eq,
    Words.toArith, ArithUint256.ofNat, Nat.mod_eq_of_lt (Words.value_lt a),
    Nat.mod_eq_of_lt (Words.value_lt b), Fin.lt_def]

set_option maxHeartbeats 2000000 in
/-- For every parameter record and word limit, word retarget succeeds and equals the arithmetic retarget with that limit. -/
theorem calculateDogecoinNextWorkRequiredWithWords_eq (params : RetargetParams) (limit : Words)
    (height : Int32) (last first : Int64) (compact : UInt32) :
    calculateDogecoinNextWorkRequiredWithWords params limit height last first compact =
      some (calculateDogecoinNextWorkRequired { params with powLimit := Words.toArith limit }
        height last first compact) := by
  have hcompact : Words.toArith (Words.setCompact compact).value = (ArithUint256.setCompact compact).value :=
    by simpa only [Words.CompactResult.toArith] using
      congrArg SetCompactResult.value (Words.setCompact_toArith compact)
  let t := modulatedTimespan params height (actualTimespan last first)
  let a := ArithUint256.mulUInt32 (ArithUint256.setCompact compact).value (toUInt32 t)
  let b := ArithUint256.ofNat (toUInt64 params.retargetTimespan)
  have hb := retargetDivisor_ne_zero params
  have hu : (UInt64.ofNat (toUInt64 params.retargetTimespan)).toNat = toUInt64 params.retargetTimespan := by
    have hx : toUInt64 params.retargetTimespan < 2 ^ 64 := by
      unfold toUInt64
      have := Int.emod_lt_of_pos params.retargetTimespan (by decide : (0 : Int) < 2 ^ 64)
      have := Int.emod_nonneg params.retargetTimespan (by decide : (2 : Int) ^ 64 ≠ 0)
      omega
    exact Nat.mod_eq_of_lt hx
  have ha : Words.mulUInt32 (Words.setCompact compact).value (toUInt32 t) = Words.ofArith a := by
    rw [← Words.ofArith_toArith (Words.setCompact compact).value, hcompact, Words.mulUInt32_ofArith]
  have hbw : Words.ofUInt64 (UInt64.ofNat (toUInt64 params.retargetTimespan)) = Words.ofArith b := by
    rw [← Words.ofArith_toArith (Words.ofUInt64 _), Words.ofUInt64_toArith, hu]
  unfold calculateDogecoinNextWorkRequiredWithWords
  simp only [Words.readWords_ofFn]
  change (Words.divide (Words.mulUInt32 (Words.setCompact compact).value (toUInt32 t))
      (Words.ofUInt64 (UInt64.ofNat (toUInt64 params.retargetTimespan)))).bind
      (fun q => some (Words.getCompact (if Words.compareTo q limit == .gt then limit else q))) = _
  rw [ha, hbw, Words.divide_ofArith a b hb]
  simp only [Option.bind_some, Words.compareTo_gt, Words.toArith_ofArith, decide_eq_true_eq]
  change _ = some (ArithUint256.getCompact
    (if a.div b hb > Words.toArith limit then Words.toArith limit else a.div b hb))
  split <;> simp only [Words.getCompact_toArith, Words.toArith_ofArith]

/-- For every existing parameter record, height, block times and compact input, word retarget succeeds with exactly the specified target. -/
theorem calculateDogecoinNextWorkRequiredWords_eq (params : RetargetParams) (height : Int32)
    (last first : Int64) (compact : UInt32) :
    calculateDogecoinNextWorkRequiredWords params height last first compact =
      some (calculateDogecoinNextWorkRequired params height last first compact) := by
  have h := calculateDogecoinNextWorkRequiredWithWords_eq params (Words.ofArith params.powLimit)
    height last first compact
  simpa only [calculateDogecoinNextWorkRequiredWords, Words.toArith_ofArith] using h

/-- For every 32-byte limit and retarget input, the byte entry point equals the specification with the interpreted byte limit. -/
theorem calculateDogecoinNextWorkRequiredBytes_eq (params : RetargetParams) (limit : TargetBytes)
    (height : Int32) (last first : Int64) (compact : UInt32) :
    calculateDogecoinNextWorkRequiredBytes params limit height last first compact =
      some (calculateDogecoinNextWorkRequired { params with powLimit := ofTargetBytes limit }
        height last first compact) := by
  simpa only [calculateDogecoinNextWorkRequiredBytes, Words.readWords_ofFn, Words.uintToArith256_toArith]
    using calculateDogecoinNextWorkRequiredWithWords_eq params
      (Words.readWords (Vector.ofFn (Words.uintToArith256 limit))) height last first compact

private theorem retarget_literal (params : RetargetParams) (literal : String)
    (h : (targetBytesOfHex literal).map (Words.toArith ∘ Words.uintToArith256) = some params.powLimit) :
    ∃ bs, targetBytesOfHex literal = some bs ∧
      ∀ (height : Int32) (last first : Int64) (compact : UInt32),
        calculateDogecoinNextWorkRequiredBytes params bs height last first compact =
          some (calculateDogecoinNextWorkRequired params height last first compact) := by
  cases hp : targetBytesOfHex literal with
  | none => simp [hp] at h
  | some bs =>
    have hlimit : ofTargetBytes bs = params.powLimit := by
      simpa only [hp, Option.map_some, Option.some.injEq, Function.comp_def, Words.uintToArith256_toArith] using h
    refine ⟨bs, rfl, ?_⟩
    intro height last first compact
    rw [calculateDogecoinNextWorkRequiredBytes_eq, hlimit]

/-- At every mainnet selection height, Core's literal parses and its bytes give the specified retarget for every retarget input. -/
theorem retarget_mainnet_literal (selectionHeight : UInt32) :
    ∃ bs, targetBytesOfHex mainnetPowLimitHex = some bs ∧
      ∀ (height : Int32) (last first : Int64) (compact : UInt32),
        calculateDogecoinNextWorkRequiredBytes (getConsensus .mainnet selectionHeight).toRetargetParams
          bs height last first compact =
          some (calculateDogecoinNextWorkRequired (getConsensus .mainnet selectionHeight).toRetargetParams
            height last first compact) := by
  apply retarget_literal
  rw [getConsensus_mainnet]
  split
  · exact mainnet_powLimit_literal
  · exact mainnet_digishield_powLimit_literal

/-- At every testnet selection height, Core's literal parses and its bytes give the specified retarget for every retarget input. -/
theorem retarget_testnet_literal (selectionHeight : UInt32) :
    ∃ bs, targetBytesOfHex mainnetPowLimitHex = some bs ∧
      ∀ (height : Int32) (last first : Int64) (compact : UInt32),
        calculateDogecoinNextWorkRequiredBytes (getConsensus .testnet selectionHeight).toRetargetParams
          bs height last first compact =
          some (calculateDogecoinNextWorkRequired (getConsensus .testnet selectionHeight).toRetargetParams
            height last first compact) := by
  apply retarget_literal
  rw [getConsensus_testnet]
  split
  · exact testnet_powLimit_literal
  · split
    · exact testnet_digishield_powLimit_literal
    · exact testnet_minDifficulty_powLimit_literal

/-- At every regtest selection height, Core's literal parses and its bytes give the specified retarget for every retarget input. -/
theorem retarget_regtest_literal (selectionHeight : UInt32) :
    ∃ bs, targetBytesOfHex regtestPowLimitHex = some bs ∧
      ∀ (height : Int32) (last first : Int64) (compact : UInt32),
        calculateDogecoinNextWorkRequiredBytes (getConsensus .regtest selectionHeight).toRetargetParams
          bs height last first compact =
          some (calculateDogecoinNextWorkRequired (getConsensus .regtest selectionHeight).toRetargetParams
            height last first compact) := by
  apply retarget_literal
  rw [getConsensus_regtest]
  split
  · exact regtest_powLimit_literal
  · exact regtest_digishield_powLimit_literal

end DogeLib.Work
