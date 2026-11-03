module

public import DogeLib.Work.Retarget
public import DogeLib.Work.Proofs.ArithUint256

/-!
# Proofs: `Retarget`

Properties of `calculateDogecoinNextWorkRequired` (src/dogecoin.cpp lines 41-87).

```text
modulatedTimespan_mem           the modulated timespan lies within the bounds of its regime
retarget_decoded_le_powLimit    the new target decodes to at most powLimit, with no flags set
signedSteps_fit                 no int64_t step overflows for block times in [0, 2^32)
modulatedTimespan_eq_int64      Lean's Int64 arithmetic computes the same timespan on that domain
retarget_eq_of_no_wrap          without a wrap, the result is GetCompact(min(old * m / T, powLimit))
no_wrap_of_le_powLimit          an old target at most powLimit does not wrap on mainnet parameters
retarget_wrap_example           with a larger old target, the product wraps
```

The regime theorems state the bounds for DigiShield and for each height range before it, and for the mainnet parameters.
`retarget_decoded_le_powLimit` holds for every input, including old targets above `powLimit` and products that wrap.
A natural property fails: a longer actual timespan does not always give a larger target, because the product at line 80 can wrap.
`retarget_wrap_example` records a counterexample.
-/

@[expose] public section

namespace DogeLib.Work

/-- `Int.tdiv` in terms of `Int./`: the quotient of a nonnegative dividend rounds down, and that of a negative dividend rounds toward zero, as in C++. -/
theorem tdiv_eq (a b : Int) :
    a.tdiv b = if 0 ≤ a then a / b else -((-a) / b) := by
  split
  · exact Int.tdiv_eq_ediv_of_nonneg (by assumption)
  · rw [show a.tdiv b = (-(-a)).tdiv b by rw [Int.neg_neg], Int.neg_tdiv,
      Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-- The target timespan is positive, by the invariant of `RetargetParams`. -/
theorem retargetTimespan_pos (params : RetargetParams) : 0 < params.retargetTimespan := by
  have := Int64.lt_iff_toInt_lt.mp params.nPowTargetTimespan_pos
  simpa [RetargetParams.retargetTimespan] using this

/-- The target timespan is below 2^63, as every `int64_t` is. -/
theorem retargetTimespan_lt (params : RetargetParams) : params.retargetTimespan < 2 ^ 63 :=
  params.nPowTargetTimespan.toInt_lt

/-- For every parameter set and height, the minimum timespan does not exceed the maximum.
This needs a positive target timespan: with a negative one, the DigiShield minimum exceeds the maximum. -/
theorem timespanLimits_le (params : RetargetParams) (nHeight : Int32) :
    (timespanLimits params nHeight).1 ≤ (timespanLimits params nHeight).2 := by
  have hT := retargetTimespan_pos params
  unfold timespanLimits
  split
  · simp only [tdiv_eq _ 4, tdiv_eq _ 2, show 0 ≤ params.retargetTimespan by omega, ite_true]; omega
  · split
    · simp only [tdiv_eq _ 4, show 0 ≤ params.retargetTimespan by omega, ite_true]; omega
    · split
      · simp only [tdiv_eq _ 8, show 0 ≤ params.retargetTimespan by omega, ite_true]; omega
      · simp only [tdiv_eq _ 16, show 0 ≤ params.retargetTimespan by omega, ite_true]; omega

/-- For every parameter set, height and actual timespan, the modulated timespan lies within the bounds of its regime, `timespanLimits`. -/
theorem modulatedTimespan_mem (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int) :
    (timespanLimits params nHeight).1 ≤ modulatedTimespan params nHeight nActualTimespan ∧
    modulatedTimespan params nHeight nActualTimespan ≤ (timespanLimits params nHeight).2 := by
  have h := timespanLimits_le params nHeight
  unfold modulatedTimespan
  generalize timespanLimits params nHeight = p at h ⊢
  obtain ⟨lo, hi⟩ := p
  dsimp only at h ⊢
  split
  · omega
  · split <;> omega


/-- With DigiShield, the modulated timespan lies in `[T - T/4, T + T/2]` for target timespan `T`, at every height and for every actual timespan. -/
theorem modulatedTimespan_digishield (params : RetargetParams)
    (digishield : params.fDigishieldDifficultyCalculation = true) (nHeight : Int32) (nActualTimespan : Int) :
    params.retargetTimespan - params.retargetTimespan.tdiv 4 ≤ modulatedTimespan params nHeight nActualTimespan ∧
    modulatedTimespan params nHeight nActualTimespan ≤ params.retargetTimespan + params.retargetTimespan.tdiv 2 := by
  simpa [timespanLimits, digishield] using modulatedTimespan_mem params nHeight nActualTimespan

/-- Before DigiShield, for a next block above height 10000, the modulated timespan lies in `[T/4, 4T]`. -/
theorem modulatedTimespan_after_10000 (params : RetargetParams)
    (legacy : params.fDigishieldDifficultyCalculation = false) (nHeight : Int32) (height : nHeight > 10000)
    (nActualTimespan : Int) :
    params.retargetTimespan.tdiv 4 ≤ modulatedTimespan params nHeight nActualTimespan ∧
    modulatedTimespan params nHeight nActualTimespan ≤ params.retargetTimespan * 4 := by
  simpa [timespanLimits, legacy, height] using modulatedTimespan_mem params nHeight nActualTimespan

/-- Before DigiShield, for a next block at a height in `(5000, 10000]`, the modulated timespan lies in `[T/8, 4T]`. -/
theorem modulatedTimespan_after_5000 (params : RetargetParams)
    (legacy : params.fDigishieldDifficultyCalculation = false) (nHeight : Int32)
    (height : nHeight > 5000) (height' : ¬ nHeight > 10000) (nActualTimespan : Int) :
    params.retargetTimespan.tdiv 8 ≤ modulatedTimespan params nHeight nActualTimespan ∧
    modulatedTimespan params nHeight nActualTimespan ≤ params.retargetTimespan * 4 := by
  simpa [timespanLimits, legacy, height, height'] using modulatedTimespan_mem params nHeight nActualTimespan

/-- Before DigiShield, for a next block at height 5000 or below, the modulated timespan lies in `[T/16, 4T]`. -/
theorem modulatedTimespan_to_5000 (params : RetargetParams)
    (legacy : params.fDigishieldDifficultyCalculation = false) (nHeight : Int32)
    (height : ¬ nHeight > 5000) (nActualTimespan : Int) :
    params.retargetTimespan.tdiv 16 ≤ modulatedTimespan params nHeight nActualTimespan ∧
    modulatedTimespan params nHeight nActualTimespan ≤ params.retargetTimespan * 4 := by
  have h' : ¬ nHeight > 10000 := fun h => height (Int32.lt_trans (by decide) h)
  simpa [timespanLimits, legacy, height, h'] using modulatedTimespan_mem params nHeight nActualTimespan

/-- With the mainnet DigiShield parameters (`T = 60`), the modulated timespan lies in `[45, 90]` for every height and actual timespan. -/
theorem mainnetDigishield_modulatedTimespan (nHeight : Int32) (nActualTimespan : Int) :
    45 ≤ modulatedTimespan mainnetDigishieldParams nHeight nActualTimespan ∧
    modulatedTimespan mainnetDigishieldParams nHeight nActualTimespan ≤ 90 := by
  have := modulatedTimespan_digishield mainnetDigishieldParams rfl nHeight nActualTimespan
  have hT : mainnetDigishieldParams.retargetTimespan = 60 := by decide
  rw [hT] at this
  simpa using this

/-- With the mainnet parameters before DigiShield (`T = 14400`), the modulated timespan is at most 57600.
It is at least 3600 above height 10000, at least 1800 above height 5000, and at least 900 at every height. -/
theorem mainnet_modulatedTimespan (nHeight : Int32) (nActualTimespan : Int) :
    (nHeight > 10000 → 3600 ≤ modulatedTimespan mainnetParams nHeight nActualTimespan) ∧
    (nHeight > 5000 → 1800 ≤ modulatedTimespan mainnetParams nHeight nActualTimespan) ∧
    900 ≤ modulatedTimespan mainnetParams nHeight nActualTimespan ∧
    modulatedTimespan mainnetParams nHeight nActualTimespan ≤ 57600 := by
  have hT : mainnetParams.retargetTimespan = 14400 := by decide
  have h := modulatedTimespan_mem mainnetParams nHeight nActualTimespan
  simp only [timespanLimits, hT] at h
  have hd : mainnetParams.fDigishieldDifficultyCalculation = false := rfl
  have t4 : (14400 : Int).tdiv 4 = 3600 := by decide
  have t8 : (14400 : Int).tdiv 8 = 1800 := by decide
  have t16 : (14400 : Int).tdiv 16 = 900 := by decide
  by_cases h1 : nHeight > 10000
  · have h2 : nHeight > 5000 := Int32.lt_trans (by decide) h1
    simp only [hd, h1, t4, Bool.false_eq_true, ite_false, ite_true] at h
    refine ⟨fun _ => by omega, fun _ => by omega, by omega, by omega⟩
  · by_cases h2 : nHeight > 5000
    · simp only [hd, h1, h2, t8, Bool.false_eq_true, ite_false, ite_true] at h
      refine ⟨fun h' => absurd h' h1, fun _ => by omega, by omega, by omega⟩
    · simp only [hd, h1, h2, t16, Bool.false_eq_true, ite_false] at h
      refine ⟨fun h' => absurd h' h1, fun h' => absurd h' h2, by omega, by omega⟩


/-- `x` is in the range of `int64_t`, `[-2^63, 2^63)`. -/
def FitsInt64 (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

/-- No signed step of lines 45-66 overflows `int64_t` when both block times are in `[0, 2^32)` and the target timespan is below 2^61.
`GetBlockTime` returns a `uint32_t` time widened to `int64_t`, so every block time from Core is in that range.
On this domain the `Int` computation is the C++ computation, which has no undefined behavior. -/
theorem signedSteps_fit (params : RetargetParams) (nLastBlockTime nFirstBlockTime : Int64)
    (last : 0 ≤ nLastBlockTime.toInt ∧ nLastBlockTime.toInt < 2 ^ 32)
    (first : 0 ≤ nFirstBlockTime.toInt ∧ nFirstBlockTime.toInt < 2 ^ 32)
    (timespan : params.retargetTimespan < 2 ^ 61) :
    let T := params.retargetTimespan
    let nActualTimespan := actualTimespan nLastBlockTime nFirstBlockTime
    FitsInt64 nActualTimespan ∧ FitsInt64 (nActualTimespan - T) ∧
    FitsInt64 ((nActualTimespan - T).tdiv 8) ∧ FitsInt64 (T + (nActualTimespan - T).tdiv 8) ∧
    FitsInt64 (T.tdiv 4) ∧ FitsInt64 (T - T.tdiv 4) ∧ FitsInt64 (T.tdiv 2) ∧ FitsInt64 (T + T.tdiv 2) ∧
    FitsInt64 (T * 4) ∧ FitsInt64 (T.tdiv 8) ∧ FitsInt64 (T.tdiv 16) := by
  have hT := retargetTimespan_pos params
  simp only [FitsInt64, actualTimespan, tdiv_eq]
  split <;> split <;> omega


/-- `timespanLimits` computed with Lean's `Int64` operations: two's-complement wrapping, and `/` that rounds toward zero. -/
def timespanLimitsInt64 (params : RetargetParams) (nHeight : Int32) : Int64 × Int64 :=
  let retargetTimespan := params.nPowTargetTimespan
  if params.fDigishieldDifficultyCalculation then
    (retargetTimespan - retargetTimespan / 4, retargetTimespan + retargetTimespan / 2)
  else if nHeight > 10000 then (retargetTimespan / 4, retargetTimespan * 4)
  else if nHeight > 5000 then (retargetTimespan / 8, retargetTimespan * 4)
  else (retargetTimespan / 16, retargetTimespan * 4)

/-- `modulatedTimespan` computed with Lean's `Int64` operations, from the two block times, as lines 45-72 read. -/
def modulatedTimespanInt64 (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) : Int64 :=
  let retargetTimespan := params.nPowTargetTimespan
  let nActualTimespan := nLastBlockTime - nFirstBlockTime
  let nModulatedTimespan := if params.fDigishieldDifficultyCalculation then
    retargetTimespan + (nActualTimespan - retargetTimespan) / 8 else nActualTimespan
  let (nMinTimespan, nMaxTimespan) := timespanLimitsInt64 params nHeight
  if nModulatedTimespan < nMinTimespan then nMinTimespan
  else if nModulatedTimespan > nMaxTimespan then nMaxTimespan
  else nModulatedTimespan

/-- A value in the range of `int64_t` is its own balanced residue modulo 2^64. -/
private theorem bmod64 {x : Int} (h : FitsInt64 x) : x.bmod (2 ^ 64) = x :=
  Int.bmod_eq_of_le (by unfold FitsInt64 at h; omega) (by unfold FitsInt64 at h; omega)

/-- On the domain of `signedSteps_fit`, Lean's `Int64` machine arithmetic computes the same modulated timespan as the `Int` specification.
`Int64.toInt_div` states that `Int64` division rounds toward zero, so the theorem also checks the choice of `Int.tdiv`. -/
theorem modulatedTimespan_eq_int64 (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64)
    (last : 0 ≤ nLastBlockTime.toInt ∧ nLastBlockTime.toInt < 2 ^ 32)
    (first : 0 ≤ nFirstBlockTime.toInt ∧ nFirstBlockTime.toInt < 2 ^ 32)
    (timespan : params.retargetTimespan < 2 ^ 61) :
    (modulatedTimespanInt64 params nHeight nLastBlockTime nFirstBlockTime).toInt =
      modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime) := by
  obtain ⟨fA, fD, fQ, fM, f4, fmin, f2, fmax, fmul, f8, f16⟩ :=
    signedSteps_fit params nLastBlockTime nFirstBlockTime last first timespan
  simp only [RetargetParams.retargetTimespan, actualTimespan] at *
  have e8 : (8 : Int64).toInt = 8 := by decide
  have e4 : (4 : Int64).toInt = 4 := by decide
  have e2 : (2 : Int64).toInt = 2 := by decide
  have e16 : (16 : Int64).toInt = 16 := by decide
  have hA : (nLastBlockTime - nFirstBlockTime).toInt = nLastBlockTime.toInt - nFirstBlockTime.toInt := by
    rw [Int64.toInt_sub, bmod64 fA]
  have hD : (nLastBlockTime - nFirstBlockTime - params.nPowTargetTimespan).toInt =
      nLastBlockTime.toInt - nFirstBlockTime.toInt - params.nPowTargetTimespan.toInt := by
    rw [Int64.toInt_sub, hA, bmod64 fD]
  have hQ : ((nLastBlockTime - nFirstBlockTime - params.nPowTargetTimespan) / 8).toInt =
      (nLastBlockTime.toInt - nFirstBlockTime.toInt - params.nPowTargetTimespan.toInt).tdiv 8 := by
    rw [Int64.toInt_div, hD, e8, bmod64 fQ]
  have hM : (params.nPowTargetTimespan + (nLastBlockTime - nFirstBlockTime - params.nPowTargetTimespan) / 8).toInt =
      params.nPowTargetTimespan.toInt +
        (nLastBlockTime.toInt - nFirstBlockTime.toInt - params.nPowTargetTimespan.toInt).tdiv 8 := by
    rw [Int64.toInt_add, hQ, bmod64 fM]
  have h4 : (params.nPowTargetTimespan / 4).toInt = params.nPowTargetTimespan.toInt.tdiv 4 := by
    rw [Int64.toInt_div, e4, bmod64 f4]
  have h2 : (params.nPowTargetTimespan / 2).toInt = params.nPowTargetTimespan.toInt.tdiv 2 := by
    rw [Int64.toInt_div, e2, bmod64 f2]
  have h8 : (params.nPowTargetTimespan / 8).toInt = params.nPowTargetTimespan.toInt.tdiv 8 := by
    rw [Int64.toInt_div, e8, bmod64 f8]
  have h16 : (params.nPowTargetTimespan / 16).toInt = params.nPowTargetTimespan.toInt.tdiv 16 := by
    rw [Int64.toInt_div, e16, bmod64 f16]
  have hmin : (params.nPowTargetTimespan - params.nPowTargetTimespan / 4).toInt =
      params.nPowTargetTimespan.toInt - params.nPowTargetTimespan.toInt.tdiv 4 := by
    rw [Int64.toInt_sub, h4, bmod64 fmin]
  have hmax : (params.nPowTargetTimespan + params.nPowTargetTimespan / 2).toInt =
      params.nPowTargetTimespan.toInt + params.nPowTargetTimespan.toInt.tdiv 2 := by
    rw [Int64.toInt_add, h2, bmod64 fmax]
  have hmul : (params.nPowTargetTimespan * 4).toInt = params.nPowTargetTimespan.toInt * 4 := by
    rw [Int64.toInt_mul, e4, bmod64 fmul]
  have limits : ((timespanLimitsInt64 params nHeight).1.toInt, (timespanLimitsInt64 params nHeight).2.toInt) =
      timespanLimits params nHeight := by
    unfold timespanLimitsInt64 timespanLimits
    simp only [RetargetParams.retargetTimespan]
    split
    · simp only [hmin, hmax]
    · split
      · simp only [h4, hmul]
      · split
        · simp only [h8, hmul]
        · simp only [h16, hmul]
  have filtered : (if params.fDigishieldDifficultyCalculation then
      params.nPowTargetTimespan + (nLastBlockTime - nFirstBlockTime - params.nPowTargetTimespan) / 8
      else nLastBlockTime - nFirstBlockTime).toInt =
      filteredTimespan params (nLastBlockTime.toInt - nFirstBlockTime.toInt) := by
    unfold filteredTimespan
    simp only [RetargetParams.retargetTimespan]
    split
    · exact hM
    · exact hA
  unfold modulatedTimespanInt64 modulatedTimespan
  dsimp only
  rw [← limits, ← filtered]
  generalize timespanLimitsInt64 params nHeight = p
  generalize (if params.fDigishieldDifficultyCalculation then
      params.nPowTargetTimespan + (nLastBlockTime - nFirstBlockTime - params.nPowTargetTimespan) / 8
      else nLastBlockTime - nFirstBlockTime) = m
  obtain ⟨lo, hi⟩ := p
  dsimp only
  by_cases c1 : m < lo
  · have c1' : m.toInt < lo.toInt := Int64.lt_iff_toInt_lt.mp c1
    simp only [c1, c1', ite_true]
  · have c1' : ¬ m.toInt < lo.toInt := fun h => c1 (Int64.lt_iff_toInt_lt.mpr h)
    by_cases c2 : hi < m
    · have c2' : hi.toInt < m.toInt := Int64.lt_iff_toInt_lt.mp c2
      simp only [c1, c1', gt_iff_lt, c2, c2', ite_true, ite_false]
    · have c2' : ¬ hi.toInt < m.toInt := fun h => c2 (Int64.lt_iff_toInt_lt.mpr h)
      simp only [c1, c1', gt_iff_lt, c2, c2', ite_false]


open ArithUint256 in
/-- For all inputs, the retarget returns `GetCompact` of a value that does not exceed `powLimit`. -/
theorem retarget_eq_getCompact (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) :
    ∃ bnNew : ArithUint256, bnNew ≤ params.powLimit ∧
      calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
        getCompact bnNew := by
  unfold calculateDogecoinNextWorkRequired
  dsimp only
  split
  · exact ⟨_, Fin.le_refl _, rfl⟩
  · rename_i h
    exact ⟨_, Fin.not_lt.mp h, rfl⟩

open ArithUint256 in
/-- For all inputs, the new compact target decodes to a value that does not exceed `powLimit`.
`SetCompact` reports neither a negative number nor an overflow for it.
Both claims hold also when the 256-bit multiplication wraps. -/
theorem retarget_decoded_le_powLimit (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) :
    let nBitsNew := calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits
    (setCompact nBitsNew).value ≤ params.powLimit ∧
      (setCompact nBitsNew).fNegative = false ∧ (setCompact nBitsNew).fOverflow = false := by
  obtain ⟨bnNew, hle, heq⟩ := retarget_eq_getCompact params nHeight nLastBlockTime nFirstBlockTime nBits
  dsimp only
  rw [heq]
  exact ⟨Fin.le_trans (setCompact_getCompact_le bnNew) hle, setCompact_getCompact_flags bnNew⟩

/-- The modulated timespan is never negative, because every minimum is nonnegative for a positive target timespan. -/
theorem modulatedTimespan_nonneg (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int) :
    0 ≤ modulatedTimespan params nHeight nActualTimespan := by
  have hT := retargetTimespan_pos params
  have h := (modulatedTimespan_mem params nHeight nActualTimespan).1
  have : 0 ≤ (timespanLimits params nHeight).1 := by
    unfold timespanLimits
    split
    · simp only [tdiv_eq]; split <;> omega
    · split
      · simp only [tdiv_eq]; split <;> omega
      · split <;> (simp only [tdiv_eq]; split <;> omega)
  omega

/-- The modulated timespan never exceeds four times the target timespan. -/
theorem modulatedTimespan_le_four_mul (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int) :
    modulatedTimespan params nHeight nActualTimespan ≤ params.retargetTimespan * 4 := by
  have hT := retargetTimespan_pos params
  have h := (modulatedTimespan_mem params nHeight nActualTimespan).2
  have : (timespanLimits params nHeight).2 ≤ params.retargetTimespan * 4 := by
    unfold timespanLimits
    split
    · simp only [tdiv_eq]; split <;> omega
    · split
      · simp
      · split <;> simp
  omega

/-- If the target timespan is below 2^30, the conversion of the modulated timespan to `uint32_t` at line 80 keeps its value. -/
theorem toUInt32_modulatedTimespan (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int)
    (timespan : params.retargetTimespan < 2 ^ 30) :
    (toUInt32 (modulatedTimespan params nHeight nActualTimespan)).toNat =
      (modulatedTimespan params nHeight nActualTimespan).toNat := by
  have h0 := modulatedTimespan_nonneg params nHeight nActualTimespan
  have h1 := modulatedTimespan_le_four_mul params nHeight nActualTimespan
  simp only [toUInt32, UInt32.toNat_ofNat']
  omega

open ArithUint256 in
/-- If the target timespan is below 2^30 and the product at line 80 is below 2^256, the retarget computes `GetCompact(min(old * modulated / T, powLimit))` in exact arithmetic. -/
theorem retarget_eq_of_no_wrap (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32)
    (timespan : params.retargetTimespan < 2 ^ 30)
    (noWrap : (setCompact nBits).value.val *
      (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat < 2 ^ 256) :
    calculateDogecoinNextWorkRequired params nHeight nLastBlockTime nFirstBlockTime nBits =
      getCompact (ofNat (min ((setCompact nBits).value.val *
        (modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)).toNat /
        params.retargetTimespan.toNat) params.powLimit.val)) := by
  have hT := retargetTimespan_pos params
  have hconv := toUInt32_modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime) timespan
  have hdiv : (ofNat (toUInt64 params.retargetTimespan)).val = params.retargetTimespan.toNat := by
    simp only [ofNat, toUInt64]; omega
  unfold calculateDogecoinNextWorkRequired
  dsimp only
  congr 1
  apply Fin.ext
  simp only [ArithUint256.div, mulUInt32, hconv, hdiv]
  simp only [ofNat, Nat.mod_eq_of_lt noWrap]
  split
  · rename_i h
    simp only [Fin.lt_def] at h
    rw [Nat.min_eq_right (Nat.le_of_lt h)]
    exact (Nat.mod_eq_of_lt params.powLimit.isLt).symm
  · rename_i h
    simp only [Fin.lt_def] at h
    rw [Nat.min_eq_left (Nat.not_lt.mp h)]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) noWrap)).symm

/-- If the old target does not exceed `powLimit`, and `powLimit * 4T` is below 2^256, the product at line 80 does not wrap. -/
theorem no_wrap_of_le_powLimit (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int)
    (nBits : UInt32) (previous : (ArithUint256.setCompact nBits).value ≤ params.powLimit)
    (limit : params.powLimit.val * (params.retargetTimespan * 4).toNat < 2 ^ 256) :
    (ArithUint256.setCompact nBits).value.val * (modulatedTimespan params nHeight nActualTimespan).toNat <
      2 ^ 256 := by
  have h0 := modulatedTimespan_nonneg params nHeight nActualTimespan
  have h1 := modulatedTimespan_le_four_mul params nHeight nActualTimespan
  have hm : (modulatedTimespan params nHeight nActualTimespan).toNat ≤ (params.retargetTimespan * 4).toNat := by
    omega
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul (Fin.le_def.mp previous) hm) limit

/-- Both mainnet parameter sets satisfy the bound of `no_wrap_of_le_powLimit`. -/
theorem mainnet_limit :
    mainnetParams.powLimit.val * (mainnetParams.retargetTimespan * 4).toNat < 2 ^ 256 ∧
    mainnetDigishieldParams.powLimit.val * (mainnetDigishieldParams.retargetTimespan * 4).toNat < 2 ^ 256 := by
  decide

/-- The case of Core's `get_next_work_digishield_rounding`: an actual timespan of 48 seconds gives 59, because the quotient `-12 / 8` rounds toward zero.
Floor division would give 58. -/
theorem filteredTimespan_rounding :
    filteredTimespan mainnetDigishieldParams 48 = 59 ∧ (60 + (48 - 60) / 8 : Int) = 58 := by
  decide

/-- The 256-bit product at line 80 can wrap, so a longer actual timespan can give a smaller target.
The compact `0x21008000` encodes 2^255, above the mainnet `powLimit`, and reports no overflow.
With 3601 seconds the product keeps 2^255, and the target clamps to `powLimit`.
With 3602 seconds the product wraps to zero, and so does the target. -/
theorem retarget_wrap_example :
    calculateDogecoinNextWorkRequired mainnetParams 20000 3601 0 0x21008000 = 0x1e0fffff ∧
    calculateDogecoinNextWorkRequired mainnetParams 20000 3602 0 0x21008000 = 0 := by
  decide +kernel

end DogeLib.Work
