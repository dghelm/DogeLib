module

public import DogeLib.Block.ContextualCheck
public import DogeLib.Block.Proofs.ContextualParams
public import DogeLib.Block.Proofs.VersionGate
public import DogeLib.Work.Proofs.MedianTimePast
public import DogeLib.Work.Proofs.NextWork

/-!
# Properties of contextual header validation

The theorems characterize `contextualCheckBlockHeader` (design record 0006, stage 3, and the targets of its section 11).

Each characterization takes a view `prev :: rest`, whose first entry `prev` is the predecessor.
The candidate height is `prev.nHeight + 1`, and the record is `getContextualParams network (UInt32.ofNat (prev.nHeight + 1))`.
The seven conditions of Core's checks, stated over the inputs, are:

1. `allowLegacyBlocks = true ∨ header.isLegacy = false`.
2. `allowLegacyBlocks = false ∨ header.isAuxpow = false`.
3. `header.nBits = required`, where `nextWorkRequired network (prev :: rest) header.nTime = .ok required`.
4. Every checkpoint height `c` with `lastCheckpointHeight = some c` satisfies `c ≤ prev.nHeight + 1`.
5. `median < header.getBlockTime`, where `medianTimePast (prev :: rest) = .ok median`.
6. `header.getBlockTime ≤ adjustedTime.toInt + maxFutureBlockTime`.
7. If the base version is below 3, the candidate height is below `bip66Height`.
   If the base version is below 4, the candidate height is below `bip65Height`.

The domain is a view on which `medianTimePast` and `nextWorkRequired` succeed, with an adjusted time of at most `maxAdjustedTime`.

- `contextualCheck_eq_ok_iff`: the function accepts exactly on the domain when the seven conditions hold.
- `contextualCheck_eq_lateLegacyBlock_iff` and the six other `contextualCheck_eq_*_iff` theorems: the targets `contextualCheck_eq_error_iff`, one for each rejection.
  The function returns a rejection exactly on the domain when its condition fails and the conditions of all earlier checks hold.
- `contextualCheck_nil`, `contextualCheck_of_medianTimePast_error`, `contextualCheck_of_nextWorkRequired_error` and `contextualCheck_of_adjustedTime`: the adapter error outside the domain.
- `contextualCheck_congr_header`: the result depends on the header only through `nVersion`, `nTime` and `nBits`.
- `contextualCheck_adjustedTime_mono`: an acceptance stays an acceptance for a greater adjusted time up to `maxAdjustedTime`.
- `contextualCheck_no_checkpoint`: without a last checkpoint, check 4 never rejects.
- `contextualCheck_congr_prefix`: checked views that agree on their first `contextualViewDepth` entries give the same result.
- `contextualCheck_complete`: a checked view that reaches height 0, with an adjusted time of at most `maxAdjustedTime`, gives no adapter error.
- `badVersion_iff`: check 7 rejects exactly when the base version is below 3 from `BIP66Height` or below 4 from `BIP65Height`, with each network's heights.

The theorems establish the behaviour of DogeLib's definitions.
They say nothing about the values that a caller supplies: the adjusted time, the last checkpoint and the link from the header to the view.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Work

/-! ## Binds of checks -/

/-- For every two results of unit type, their sequence accepts exactly when both accept. -/
theorem bind_unit_eq_ok {ε : Type} (a b : Except ε Unit) :
    (a >>= fun _ => b) = .ok () ↔ a = .ok () ∧ b = .ok () := by
  cases a <;> simp [bind, Except.bind]

/-- For every two results of unit type, their sequence fails with `e` in two cases.
The first fails with `e`, or the first accepts and the second fails with `e`. -/
theorem bind_unit_eq_error {ε : Type} (a b : Except ε Unit) (e : ε) :
    (a >>= fun _ => b) = .error e ↔ a = .error e ∨ (a = .ok () ∧ b = .error e) := by
  cases a <;> simp [bind, Except.bind]

/-! ## The individual checks -/

/-- Checks 1 and 2 accept exactly when both of their conditions hold. -/
theorem checkVersion_mapError_eq_ok_iff (p : ContextualParams) (h : PureBlockHeader) :
    (checkVersion p.toVersionGateParams h).mapError ContextualHeaderError.ofVersionGate = .ok () ↔
      (p.allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        (p.allowLegacyBlocks = false ∨ h.isAuxpow = false) := by
  unfold checkVersion
  cases p.allowLegacyBlocks <;> cases h.isLegacy <;> cases h.isAuxpow <;> simp [Except.mapError]

/-- Checks 1 and 2 fail only with `late-legacy-block` or `early-auxpow-block`, each exactly under its condition. -/
theorem checkVersion_mapError_eq_error_iff (p : ContextualParams) (h : PureBlockHeader)
    (e : ContextualHeaderError) :
    (checkVersion p.toVersionGateParams h).mapError ContextualHeaderError.ofVersionGate = .error e ↔
      (e = .lateLegacyBlock ∧ p.allowLegacyBlocks = false ∧ h.isLegacy = true) ∨
        (e = .earlyAuxpowBlock ∧ (p.allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
          p.allowLegacyBlocks = true ∧ h.isAuxpow = true) := by
  unfold checkVersion
  cases p.allowLegacyBlocks <;> cases h.isLegacy <;> cases h.isAuxpow <;>
    simp [Except.mapError, ContextualHeaderError.ofVersionGate, eq_comm]

/-- Check 3 accepts exactly when `nBits` equals the required value as a raw 32-bit value. -/
theorem checkDiffbits_eq_ok_iff (h : PureBlockHeader) (required : UInt32) :
    checkDiffbits h required = .ok () ↔ h.nBits = required := by
  unfold checkDiffbits; split <;> simp_all

/-- Check 3 fails only with `bad-diffbits`, exactly when `nBits` differs from the required value. -/
theorem checkDiffbits_eq_error_iff (h : PureBlockHeader) (required : UInt32) (e : ContextualHeaderError) :
    checkDiffbits h required = .error e ↔ e = .badDiffbits ∧ h.nBits ≠ required := by
  unfold checkDiffbits; split <;> simp_all [eq_comm]

/-- Check 4 accepts exactly when every last checkpoint height is at most the candidate height. -/
theorem checkCheckpoint_eq_ok_iff (height : Nat) (c : Option Nat) :
    checkCheckpoint height c = .ok () ↔ ∀ checkpoint, c = some checkpoint → checkpoint ≤ height := by
  unfold checkCheckpoint
  cases c with
  | none => simp
  | some checkpoint =>
    by_cases below : height < checkpoint
    · simp [below]
    · simp [below]; omega

/-- Check 4 fails only with `bad-fork-prior-to-checkpoint`, exactly when a last checkpoint height is greater than the candidate height. -/
theorem checkCheckpoint_eq_error_iff (height : Nat) (c : Option Nat) (e : ContextualHeaderError) :
    checkCheckpoint height c = .error e ↔
      e = .badForkPriorToCheckpoint ∧ ∃ checkpoint, c = some checkpoint ∧ height < checkpoint := by
  unfold checkCheckpoint
  cases c with
  | none => simp
  | some checkpoint =>
    by_cases below : height < checkpoint <;> simp [below, eq_comm]

/-- Check 5 accepts exactly when the header time is greater than the median. -/
theorem checkTimeTooOld_eq_ok_iff (h : PureBlockHeader) (median : Int) :
    checkTimeTooOld h median = .ok () ↔ median < h.getBlockTime := by
  unfold checkTimeTooOld; split <;> simp <;> omega

/-- Check 5 fails only with `time-too-old`, exactly when the header time is at most the median. -/
theorem checkTimeTooOld_eq_error_iff (h : PureBlockHeader) (median : Int) (e : ContextualHeaderError) :
    checkTimeTooOld h median = .error e ↔ e = .timeTooOld ∧ h.getBlockTime ≤ median := by
  unfold checkTimeTooOld; split <;> simp_all [eq_comm]

/-- Check 6 accepts exactly when the header time is at most the adjusted time plus `maxFutureBlockTime`. -/
theorem checkTimeTooNew_eq_ok_iff (h : PureBlockHeader) (adjustedTime : Int) :
    checkTimeTooNew h adjustedTime = .ok () ↔ h.getBlockTime ≤ adjustedTime + maxFutureBlockTime := by
  unfold checkTimeTooNew; split <;> simp <;> omega

/-- Check 6 fails only with `time-too-new`, exactly when the header time is greater than the adjusted time plus `maxFutureBlockTime`. -/
theorem checkTimeTooNew_eq_error_iff (h : PureBlockHeader) (adjustedTime : Int) (e : ContextualHeaderError) :
    checkTimeTooNew h adjustedTime = .error e ↔
      e = .timeTooNew ∧ adjustedTime + maxFutureBlockTime < h.getBlockTime := by
  unfold checkTimeTooNew; split <;> simp_all [eq_comm]

/-- Check 7 accepts exactly when a base version below 3 comes before `bip66Height`, and a base version below 4 before `bip65Height`. -/
theorem checkBaseVersion_eq_ok_iff (p : ContextualParams) (height : Nat) (h : PureBlockHeader) :
    checkBaseVersion p height h = .ok () ↔
      (h.getBaseVersion < 3 → height < p.bip66Height) ∧ (h.getBaseVersion < 4 → height < p.bip65Height) := by
  unfold checkBaseVersion; split <;> simp_all <;> omega

/-- Check 7 fails only with `bad-version` and the base version, exactly when the base version is below 3 from `bip66Height`, or below 4 from `bip65Height`. -/
theorem checkBaseVersion_eq_error_iff (p : ContextualParams) (height : Nat) (h : PureBlockHeader)
    (e : ContextualHeaderError) :
    checkBaseVersion p height h = .error e ↔
      e = .badVersion h.getBaseVersion ∧
        ((h.getBaseVersion < 3 ∧ p.bip66Height ≤ height) ∨ (h.getBaseVersion < 4 ∧ p.bip65Height ≤ height)) := by
  unfold checkBaseVersion; split <;> simp_all [eq_comm]

/-! ## The seven checks on derived values -/

/-- For every record, candidate height, header, required value, median, adjusted time and last checkpoint, `contextualChecks` accepts exactly when the seven conditions hold. -/
theorem contextualChecks_eq_ok_iff (p : ContextualParams) (height : Nat) (h : PureBlockHeader)
    (required : UInt32) (median adjustedTime : Int) (c : Option Nat) :
    contextualChecks p height h required median adjustedTime c = .ok () ↔
      (p.allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
      (p.allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
      h.nBits = required ∧
      (∀ checkpoint, c = some checkpoint → checkpoint ≤ height) ∧
      median < h.getBlockTime ∧
      h.getBlockTime ≤ adjustedTime + maxFutureBlockTime ∧
      (h.getBaseVersion < 3 → height < p.bip66Height) ∧
      (h.getBaseVersion < 4 → height < p.bip65Height) := by
  simp only [contextualChecks, bind_unit_eq_ok, checkVersion_mapError_eq_ok_iff, checkDiffbits_eq_ok_iff,
    checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff, checkTimeTooNew_eq_ok_iff,
    checkBaseVersion_eq_ok_iff, and_assoc]

/-- Every error of `contextualChecks` is one of the seven Core rejections, never an adapter error. -/
theorem contextualChecks_isRejection (p : ContextualParams) (height : Nat) (h : PureBlockHeader)
    (required : UInt32) (median adjustedTime : Int) (c : Option Nat) (e : ContextualHeaderError)
    (failure : contextualChecks p height h required median adjustedTime c = .error e) :
    e.isRejection = true := by
  cases e <;> simp only [ContextualHeaderError.isRejection] <;>
    simp [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
      checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
      checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff] at failure

/-! ## The domain and the adapter errors -/

/-- For every network, header, adjusted time and last checkpoint, the empty view returns the adapter error `emptyView`. -/
theorem contextualCheck_nil (network : WorkNetwork) (h : PureBlockHeader) (adjustedTime : Int64)
    (c : Option Nat) : contextualCheckBlockHeader network h [] adjustedTime c = .error .emptyView := rfl

/-- If `medianTimePast` fails on a nonempty view, the function returns its adapter error: `invalidView`, `emptyView` or `shortView`. -/
theorem contextualCheck_of_medianTimePast_error (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (e : MedianTimeError) (failure : medianTimePast (prev :: rest) = .error e) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error (.ofMedianTime e) := by
  simp [contextualCheckBlockHeader, failure, Except.mapError, bind, Except.bind]

/-- If `medianTimePast` succeeds and `nextWorkRequired` fails on a nonempty view, the function returns the adapter error `nextWork` with that error. -/
theorem contextualCheck_of_nextWorkRequired_error (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (median : Int) (medianOk : medianTimePast (prev :: rest) = .ok median)
    (e : NextWorkError) (failure : nextWorkRequired network (prev :: rest) h.nTime = .error e) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error (.nextWork e) := by
  simp [contextualCheckBlockHeader, medianOk, failure, Except.mapError, bind, Except.bind]

/-- If both walks succeed on a nonempty view and the adjusted time is above `maxAdjustedTime`, the function returns the adapter error `adjustedTimeOutOfRange`. -/
theorem contextualCheck_of_adjustedTime (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (median : Int) (medianOk : medianTimePast (prev :: rest) = .ok median)
    (required : UInt32) (requiredOk : nextWorkRequired network (prev :: rest) h.nTime = .ok required)
    (above : maxAdjustedTime < adjustedTime.toInt) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .adjustedTimeOutOfRange := by
  simp [contextualCheckBlockHeader, medianOk, requiredOk, above, Except.mapError, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw]

/--
On the domain, the function is `contextualChecks` on the derived values.
The domain is a nonempty view on which `medianTimePast` and `nextWorkRequired` succeed, with an adjusted time of at most `maxAdjustedTime`.
The derived values are the record at the candidate height, the candidate height, the required value, the median and the widened adjusted time.
-/
theorem contextualCheck_eq_contextualChecks (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (median : Int) (medianOk : medianTimePast (prev :: rest) = .ok median)
    (required : UInt32) (requiredOk : nextWorkRequired network (prev :: rest) h.nTime = .ok required)
    (bounded : adjustedTime.toInt ≤ maxAdjustedTime) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c =
      contextualChecks (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))) (prev.nHeight + 1)
        h required median adjustedTime.toInt c := by
  have notAbove : ¬ maxAdjustedTime < adjustedTime.toInt := by omega
  simp [contextualCheckBlockHeader, medianOk, requiredOk, notAbove, Except.mapError, bind, Except.bind]

/--
Let `r` be a result whose errors are all Core rejections.
The function returns `r` exactly on the domain when `contextualChecks` returns `r` on the derived values.
The domain is: `medianTimePast` succeeds with `median`, `nextWorkRequired` succeeds with `required`, and the adjusted time is at most `maxAdjustedTime`.
-/
theorem contextualCheck_eq_iff_contextualChecks (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (r : Except ContextualHeaderError Unit) (rejection : ∀ e, r = .error e → e.isRejection = true) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = r ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        contextualChecks (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))) (prev.nHeight + 1)
          h required median adjustedTime.toInt c = r := by
  cases medianResult : medianTimePast (prev :: rest) with
  | error e =>
    rw [contextualCheck_of_medianTimePast_error network h prev rest adjustedTime c e medianResult]
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    intro eq
    have := rejection _ eq.symm
    cases e <;> simp [ContextualHeaderError.ofMedianTime, ContextualHeaderError.isRejection] at this
  | ok median =>
    cases requiredResult : nextWorkRequired network (prev :: rest) h.nTime with
    | error e =>
      rw [contextualCheck_of_nextWorkRequired_error network h prev rest adjustedTime c median medianResult e
        requiredResult]
      simp only [reduceCtorEq, false_and, and_false, exists_false, iff_false]
      intro eq
      have := rejection _ eq.symm
      simp [ContextualHeaderError.isRejection] at this
    | ok required =>
      by_cases bounded : adjustedTime.toInt ≤ maxAdjustedTime
      · rw [contextualCheck_eq_contextualChecks network h prev rest adjustedTime c median medianResult
          required requiredResult bounded]
        simp [bounded]
      · rw [contextualCheck_of_adjustedTime network h prev rest adjustedTime c median medianResult
          required requiredResult (by omega)]
        simp only [bounded, false_and, and_false, exists_false, iff_false, Except.ok.injEq]
        intro eq
        have := rejection _ eq.symm
        simp [ContextualHeaderError.isRejection] at this

/-! ## Characterization -/

/--
The acceptance characterization, the target `contextualCheck_eq_ok_iff` of design record 0006.
Fix a network, a header, a nonempty view `prev :: rest`, an adjusted time and a last checkpoint.
The function accepts exactly when the input is in the domain and the seven conditions hold.
The domain: `medianTimePast` succeeds with `median`, `nextWorkRequired` succeeds with `required`, and the adjusted time is at most `maxAdjustedTime`.
The conditions use the record that `getContextualParams` selects at the candidate height `prev.nHeight + 1`.
-/
theorem contextualCheck_eq_ok_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .ok () ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits = required ∧
        (∀ checkpoint, c = some checkpoint → checkpoint ≤ prev.nHeight + 1) ∧
        median < h.getBlockTime ∧
        h.getBlockTime ≤ adjustedTime.toInt + maxFutureBlockTime ∧
        (h.getBaseVersion < 3 → prev.nHeight + 1 < (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).bip66Height) ∧
        (h.getBaseVersion < 4 → prev.nHeight + 1 < (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).bip65Height) := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq)]
  simp only [contextualChecks_eq_ok_iff]

/--
Check 1 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `late-legacy-block` exactly when the input is in the domain and the condition of check 1 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_lateLegacyBlock_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .lateLegacyBlock ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∧ h.isLegacy = true := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp

/--
Check 2 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `early-auxpow-block` exactly when three conditions hold.
The input is in the domain, the condition of check 1 holds, and the condition of check 2 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_earlyAuxpowBlock_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .earlyAuxpowBlock ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∧ h.isAuxpow = true := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp

/--
Check 3 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `bad-diffbits` exactly when three conditions hold.
The input is in the domain, the conditions of checks 1 and 2 hold, and the condition of check 3 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_badDiffbits_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .badDiffbits ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits ≠ required := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp [and_assoc]

/--
Check 4 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `bad-fork-prior-to-checkpoint` exactly when three conditions hold.
The input is in the domain, the conditions of checks 1 to 3 hold, and the condition of check 4 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_badForkPriorToCheckpoint_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .badForkPriorToCheckpoint ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits = required ∧
        (∃ checkpoint, c = some checkpoint ∧ prev.nHeight + 1 < checkpoint) := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp [and_assoc]

/--
Check 5 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `time-too-old` exactly when three conditions hold.
The input is in the domain, the conditions of checks 1 to 4 hold, and the condition of check 5 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_timeTooOld_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .timeTooOld ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits = required ∧
        (∀ checkpoint, c = some checkpoint → checkpoint ≤ prev.nHeight + 1) ∧
        h.getBlockTime ≤ median := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp [and_assoc]

/--
Check 6 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `time-too-new` exactly when three conditions hold.
The input is in the domain, the conditions of checks 1 to 5 hold, and the condition of check 6 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_timeTooNew_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error .timeTooNew ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits = required ∧
        (∀ checkpoint, c = some checkpoint → checkpoint ≤ prev.nHeight + 1) ∧
        median < h.getBlockTime ∧
        adjustedTime.toInt + maxFutureBlockTime < h.getBlockTime := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp [and_assoc]

/--
Check 7 of the characterization, one of the targets `contextualCheck_eq_error_iff` of design record 0006.
Fix a network, a header, a nonempty view, an adjusted time and a last checkpoint.
The function rejects with `bad-version` and the base version `b` exactly when four conditions hold.
The input is in the domain, the conditions of checks 1 to 6 hold, `b` is `h.getBaseVersion`, and the condition of check 7 fails.
The domain and the conditions are those of `contextualCheck_eq_ok_iff`.
-/
theorem contextualCheck_eq_badVersion_iff (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat) (b : Int) :
    contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error (.badVersion b) ↔
      ∃ median required, medianTimePast (prev :: rest) = .ok median ∧
        nextWorkRequired network (prev :: rest) h.nTime = .ok required ∧
        adjustedTime.toInt ≤ maxAdjustedTime ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = true ∨ h.isLegacy = false) ∧
        ((getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).allowLegacyBlocks = false ∨ h.isAuxpow = false) ∧
        h.nBits = required ∧
        (∀ checkpoint, c = some checkpoint → checkpoint ≤ prev.nHeight + 1) ∧
        median < h.getBlockTime ∧
        h.getBlockTime ≤ adjustedTime.toInt + maxFutureBlockTime ∧
        b = h.getBaseVersion ∧
        ((h.getBaseVersion < 3 ∧ (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).bip66Height ≤ prev.nHeight + 1) ∨
          (h.getBaseVersion < 4 ∧ (getContextualParams network (UInt32.ofNat (prev.nHeight + 1))).bip65Height ≤ prev.nHeight + 1)) := by
  rw [contextualCheck_eq_iff_contextualChecks _ _ _ _ _ _ _ (by intro e eq; cases eq; rfl)]
  simp only [contextualChecks, bind_unit_eq_error, checkVersion_mapError_eq_error_iff,
    checkDiffbits_eq_error_iff, checkCheckpoint_eq_error_iff, checkTimeTooOld_eq_error_iff,
    checkTimeTooNew_eq_error_iff, checkBaseVersion_eq_error_iff, checkVersion_mapError_eq_ok_iff,
    checkDiffbits_eq_ok_iff, checkCheckpoint_eq_ok_iff, checkTimeTooOld_eq_ok_iff,
    checkTimeTooNew_eq_ok_iff]
  simp [and_assoc]

/-! ## Dependence on the inputs -/

/--
The target `contextualCheck_congr_header`.
For every network, view, adjusted time and last checkpoint, two headers with the same `nVersion`, `nTime` and `nBits` give the same result.
So the previous hash, the Merkle root and the nonce never change the result.
-/
theorem contextualCheck_congr_header (network : WorkNetwork) (h h' : PureBlockHeader)
    (view : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (version : h.nVersion = h'.nVersion) (time : h.nTime = h'.nTime) (bits : h.nBits = h'.nBits) :
    contextualCheckBlockHeader network h view adjustedTime c =
      contextualCheckBlockHeader network h' view adjustedTime c := by
  obtain ⟨v, _, _, t, b, _⟩ := h
  obtain ⟨v', _, _, t', b', _⟩ := h'
  simp only at version time bits
  subst version time bits
  rfl

/--
The target `contextualCheck_adjustedTime_mono`.
Fix a network, a header, a view and a last checkpoint, and let the function accept with the adjusted time `t₁`.
Then it accepts with every adjusted time `t₂` from `t₁` up to `maxAdjustedTime`.
-/
theorem contextualCheck_adjustedTime_mono (network : WorkNetwork) (h : PureBlockHeader)
    (view : List BlockIndex) (t₁ t₂ : Int64) (c : Option Nat)
    (accepted : contextualCheckBlockHeader network h view t₁ c = .ok ())
    (later : t₁.toInt ≤ t₂.toInt) (bounded : t₂.toInt ≤ maxAdjustedTime) :
    contextualCheckBlockHeader network h view t₂ c = .ok () := by
  cases view with
  | nil => simp [contextualCheck_nil] at accepted
  | cons prev rest =>
    rw [contextualCheck_eq_ok_iff] at accepted ⊢
    obtain ⟨median, required, m, r, -, c1, c2, c3, c4, c5, c6, c7⟩ := accepted
    exact ⟨median, required, m, r, bounded, c1, c2, c3, c4, c5, by omega, c7⟩

/--
The target `contextualCheck_no_checkpoint`.
For every network, header, view and adjusted time, with no last checkpoint the function never rejects with `bad-fork-prior-to-checkpoint`.
-/
theorem contextualCheck_no_checkpoint (network : WorkNetwork) (h : PureBlockHeader)
    (view : List BlockIndex) (adjustedTime : Int64) :
    contextualCheckBlockHeader network h view adjustedTime none ≠ .error .badForkPriorToCheckpoint := by
  cases view with
  | nil => simp [contextualCheck_nil]
  | cons prev rest =>
    rw [ne_eq, contextualCheck_eq_badForkPriorToCheckpoint_iff]
    simp

/--
The number of leading view entries that `contextualCheck_congr_prefix` requires to agree, for the predecessor `prev`.
It is the greater of `nMedianTimeSpan` and `retargetInterval params prev.nHeight + 1`, where `params` is the record of `getConsensus` at the candidate height.
`nextWorkRequired` reads fewer than `retargetInterval params prev.nHeight + 1` entries (`nextWorkRequired_congr_prefix`).
`contextualViewDepth_eq` gives its values: 241 on mainnet and testnet below candidate height 145000, and 11 from that height.
On regtest it is 14401 below candidate height 10, and 11 from that height.
-/
def contextualViewDepth (network : WorkNetwork) (prev : BlockIndex) : Nat :=
  max nMedianTimeSpan
    (retargetInterval (getConsensus network (UInt32.ofNat (prev.nHeight + 1))) prev.nHeight + 1)

/--
The values of `contextualViewDepth` for a predecessor height below 2147483647, as `validateWorkView` requires.
On mainnet and testnet, the depth is 241 below candidate height 145000 and 11 from it.
On regtest, the depth is 14401 below candidate height 10 and 11 from it.
-/
theorem contextualViewDepth_eq (network : WorkNetwork) (prev : BlockIndex)
    (range : prev.nHeight < 2147483647) :
    contextualViewDepth network prev =
      match network with
      | .mainnet | .testnet => if prev.nHeight + 1 < 145000 then 241 else 11
      | .regtest => if prev.nHeight + 1 < 10 then 14401 else 11 := by
  have exact : (UInt32.ofNat (prev.nHeight + 1)).toNat = prev.nHeight + 1 := by
    simp only [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have m₁ : mainnetWorkParams.difficultyAdjustmentInterval = 240 := by decide
  have m₂ : mainnetDigishieldWorkParams.difficultyAdjustmentInterval = 1 := by decide
  have t₁ : testnetWorkParams.difficultyAdjustmentInterval = 240 := by decide
  have t₂ : testnetDigishieldWorkParams.difficultyAdjustmentInterval = 1 := by decide
  have t₃ : testnetMinDifficultyWorkParams.difficultyAdjustmentInterval = 1 := by decide
  have r₁ : regtestWorkParams.difficultyAdjustmentInterval = 14400 := by decide
  have r₂ : regtestDigishieldWorkParams.difficultyAdjustmentInterval = 1 := by decide
  cases network <;>
    simp only [contextualViewDepth, getConsensus_mainnet, getConsensus_testnet, getConsensus_regtest,
      UInt32.lt_iff_toNat_lt, exact, UInt32.reduceToNat] <;>
    repeat' split
  all_goals simp only [retargetInterval, nMedianTimeSpan, m₁, m₂, t₁, t₂, t₃, r₁, r₂] at *
  all_goals (repeat' split) <;> omega

/--
The target `contextualCheck_congr_prefix`, with the depth `d` settled as `retargetInterval params prev.nHeight + 1`.
Let two views `prev :: rest₁` and `prev :: rest₂` pass `validateWorkView`.
If they agree on their first `contextualViewDepth network prev` entries, they give the same result for every network, header, adjusted time and last checkpoint.
The result is the same acceptance, the same rejection or the same adapter error.
-/
theorem contextualCheck_congr_prefix (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest₁ rest₂ : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (valid₁ : validateWorkView (prev :: rest₁) = .ok ())
    (valid₂ : validateWorkView (prev :: rest₂) = .ok ())
    (agree : (prev :: rest₁).take (contextualViewDepth network prev) =
      (prev :: rest₂).take (contextualViewDepth network prev)) :
    contextualCheckBlockHeader network h (prev :: rest₁) adjustedTime c =
      contextualCheckBlockHeader network h (prev :: rest₂) adjustedTime c := by
  have shorter : ∀ n, n ≤ contextualViewDepth network prev →
      (prev :: rest₁).take n = (prev :: rest₂).take n := by
    intro n le
    have := congrArg (List.take n) agree
    simpa [List.take_take, Nat.min_eq_left le] using this
  have median := medianTimePast_congr_prefix prev rest₁ rest₂ valid₁ valid₂
    (shorter _ (by
      have := (medianTimeSpan_bounds prev).2
      simp only [contextualViewDepth]
      omega))
  have required := nextWorkRequired_congr_prefix network prev rest₁ rest₂ h.nTime valid₁ valid₂
    (shorter _ (by simp only [contextualViewDepth]; omega))
  simp only [contextualCheckBlockHeader, median, required]

/--
The target `contextualCheck_complete`.
Let the view `prev :: rest` pass `validateWorkView` and reach height 0: its last entry has height 0.
With an adjusted time of at most `maxAdjustedTime`, every error of the function is a Core rejection, for every network, header and last checkpoint.
So the function returns no adapter error.
-/
theorem contextualCheck_complete (network : WorkNetwork) (h : PureBlockHeader)
    (prev : BlockIndex) (rest : List BlockIndex) (adjustedTime : Int64) (c : Option Nat)
    (valid : validateWorkView (prev :: rest) = .ok ())
    (genesis : (prev :: rest).getLast?.map BlockIndex.nHeight = some 0)
    (bounded : adjustedTime.toInt ≤ maxAdjustedTime) (e : ContextualHeaderError)
    (failure : contextualCheckBlockHeader network h (prev :: rest) adjustedTime c = .error e) :
    e.isRejection = true := by
  have length := length_of_validateWorkView prev rest valid genesis
  have deep : medianTimeSpan prev ≤ rest.length + 1 := by
    simp only [medianTimeSpan, nMedianTimeSpan]; omega
  obtain ⟨_, medianOk⟩ := medianTimePast_eq prev rest valid deep
  obtain ⟨required, requiredOk⟩ := nextWorkRequired_ok network prev rest h.nTime valid length
  rw [contextualCheck_eq_contextualChecks network h prev rest adjustedTime c _ medianOk required
    requiredOk bounded] at failure
  exact contextualChecks_isRejection _ _ _ _ _ _ _ _ failure

/--
The target `badVersion_iff`.
Let `b = h.signedVersion.toInt.tmod 256`, the signed remainder of `nVersion` by 256, which is `h.getBaseVersion`.

For every network, candidate height and header, check 7 with the record of `getContextualParams` at that height rejects exactly in two cases.
The base version is below 3 from `BIP66Height`, or below 4 from `BIP65Height`.
`BIP66Height` is 1034383 on mainnet, 708658 on testnet and 1251 on regtest.
`BIP65Height` is 3464751 on mainnet, 1854705 on testnet and 1351 on regtest.
The rejection carries `b`.
-/
theorem badVersion_iff (network : WorkNetwork) (height : Nat) (h : PureBlockHeader) :
    checkBaseVersion (getContextualParams network (UInt32.ofNat height)) height h =
        .error (.badVersion (h.signedVersion.toInt.tmod 256)) ↔
      (h.signedVersion.toInt.tmod 256 < 3 ∧
          (match network with | .mainnet => 1034383 | .testnet => 708658 | .regtest => 1251) ≤ height) ∨
        (h.signedVersion.toInt.tmod 256 < 4 ∧
          (match network with | .mainnet => 3464751 | .testnet => 1854705 | .regtest => 1351) ≤ height) := by
  rw [checkBaseVersion_eq_error_iff, bip66Height_getConsensus, bip65Height_getConsensus]
  cases network <;> simp [PureBlockHeader.getBaseVersion]

end DogeLib.Block
