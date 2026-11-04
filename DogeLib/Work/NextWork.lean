module

public import DogeLib.Work.Consensus

/-!
# Next-work selection

`GetNextWorkRequired` in `src/pow.cpp` lines 32-88 at Core `e0a1c15` (D17).
A view lists block-index entries from newest to oldest.
Each next element represents `pprev`. Adjacent heights must differ by one.
Every height must be below 2147483647, so the next height fits a signed 32-bit integer.
A view may stop above genesis, but a walk that needs the missing history returns an error.

The view does not assert header validity or a bound on decoded targets.

The candidate time is separate from the view, as `pblock` is separate from `pindexLast`.
Both times are UInt32 values widened to Int, following `GetBlockTime` (`src/chain.h`, D18, lines 274-277, and D10, lines 73-76).
The network spacings are 60 or 1, so the delay comparison cannot overflow int64_t.

The wrapper selects parameters for the candidate height, as `src/validation.cpp` lines 3068-3070 and 3089 do.
Mining uses the same height (miner.cpp lines 151-153 and 209).
The two hard-coded height checks instead use the previous height.
`fPowNoRetargeting` and `fPowAllowDigishieldMinDifficultyBlocks` do not control this caller.
-/

@[expose] public section

namespace DogeLib.Work

/-- Fields read from `CBlockIndex` (`src/chain.h`, D18, lines 164-171 and 200-201 at `e0a1c15`).
The following element of a view represents this entry's predecessor. -/
structure BlockIndex where
  /-- Nonnegative `nHeight`, checked before a caller uses signed height arithmetic. -/
  nHeight : Nat
  /-- `nTime`, widened by `GetBlockTime`. -/
  nTime : UInt32
  /-- Compact target, preserved without a validity check. -/
  nBits : UInt32
  deriving DecidableEq, Repr

/-- Errors of the finite-view adapter to D17, lines 32-88 at `e0a1c15`.
These errors describe the adapter, not Core consensus rejection codes. -/
inductive NextWorkError where
  /-- A height cannot be incremented within Core's signed 32-bit domain. -/
  | heightOutOfRange
  /-- Adjacent entries do not represent consecutive predecessors. -/
  | inconsistentHeights
  /-- The first-height assertion at pow.cpp line 84 would fail. -/
  | firstHeightUnderflow
  /-- Required history is absent. Core asserts an ancestor at pow.cpp line 86. -/
  | missingAncestor
  /-- A custom parameter record supplies an interval of zero. -/
  | zeroInterval
  deriving DecidableEq, Repr

/-- Checks a finite view's height domain and predecessor links (`src/chain.h`, D18, lines 164-171 at `e0a1c15`).
The final entry may be above genesis, so success does not promise enough history for a walk. -/
def validateWorkView : List BlockIndex → Except NextWorkError Unit
  | [] => .ok ()
  | entry :: rest => do
    if entry.nHeight ≥ 2147483647 then throw .heightOutOfRange
    match rest with
    | [] => pure ()
    | prev :: _ =>
      if entry.nHeight != prev.nHeight + 1 then throw .inconsistentHeights
      validateWorkView rest

/-- Local retarget interval (`src/pow.cpp`, D17, lines 50-53 at `e0a1c15`).
The 145000 threshold uses the previous height, independent of parameter selection. -/
def retargetInterval (params : WorkParams) (previousHeight : Nat) : Nat :=
  if previousHeight ≥ 145000 then 1 else params.difficultyAdjustmentInterval

/-- Lookback for a retarget (`src/pow.cpp`, D17, lines 77-81 at `e0a1c15`).
The first retarget uses interval minus one, and every later retarget uses the full interval. -/
def blocksToGoBack (interval previousHeight : Nat) : Nat :=
  if previousHeight + 1 = interval then interval - 1 else interval

/-- Strict timestamp delay comparison (`src/pow.cpp`, D17, line 59 at `e0a1c15`).
Times are widened UInt32 values, and spacing is measured in seconds. -/
def delayedBlock (params : WorkParams) (lastTime candidateTime : UInt32) : Bool :=
  (candidateTime.toNat : Int) > (lastTime.toNat : Int) + (params.nPowTargetSpacing : Int) * 2

/-- `AllowDigishieldMinDifficultyForBlock` (`src/dogecoin.cpp`, D6, lines 26-39 at `e0a1c15`).
The source checks previous height 157500, not the unused DigiShield permission field. -/
def allowDigishieldMinDifficultyForBlock (params : WorkParams) (last : BlockIndex)
    (candidateTime : UInt32) : Bool :=
  params.fPowAllowMinDifficultyBlocks && last.nHeight ≥ 157500 &&
    delayedBlock params last.nTime candidateTime

/-- The recovery walk (`src/pow.cpp`, D17, lines 65-69 at `e0a1c15`).
It uses the record's interval, not `retargetInterval`.
At a truncated suffix it fails only if the loop still needs a predecessor.
Height zero represents a null predecessor. -/
def recoverLastNonMinDifficulty (interval : Nat) (limit : UInt32) :
    List BlockIndex → Except NextWorkError UInt32
  | [] => .error .missingAncestor
  | entry :: rest =>
    if entry.nHeight % interval = 0 ∨ entry.nBits ≠ limit then .ok entry.nBits
    else match rest with
      | [] => .error .missingAncestor
      | _ :: _ => recoverLastNonMinDifficulty interval limit rest

/-- The caller after view validation (`src/pow.cpp`, D17, lines 32-88 at `e0a1c15`).
A missing retarget ancestor maps Core's assertion to `missingAncestor`.
`firstHeightUnderflow` maps the nonnegative-first-height assertion separately.
For custom records, `zeroInterval` prevents division or remainder by zero. -/
def getNextWorkRequiredFromView (params : WorkParams) (view : List BlockIndex)
    (candidateTime : UInt32) : Except NextWorkError UInt32 := do
  let limit := ArithUint256.getCompact params.powLimit
  match view with
  | [] => return limit
  | last :: _ =>
    if allowDigishieldMinDifficultyForBlock params last candidateTime then return limit
    let interval := retargetInterval params last.nHeight
    if interval = 0 then throw .zeroInterval
    if (last.nHeight + 1) % interval != 0 then
      if params.fPowAllowMinDifficultyBlocks then
        if delayedBlock params last.nTime candidateTime then return limit
        return ← recoverLastNonMinDifficulty params.difficultyAdjustmentInterval limit view
      return last.nBits
    let back := blocksToGoBack interval last.nHeight
    if last.nHeight < back then throw .firstHeightUnderflow
    let first ← match view[back]? with
      | none => throw .missingAncestor
      | some first => pure first
    return calculateDogecoinNextWorkRequired params.toRetargetParams
      (Int32.ofNat (last.nHeight + 1))
      (Int64.ofNat last.nTime.toNat) (Int64.ofNat first.nTime.toNat) last.nBits

/-- `GetNextWorkRequired` on a checked finite view (`src/pow.cpp`, D17, lines 32-88 at `e0a1c15`).
Checks all supplied links before the source branches run.
An empty view represents the null tip, for which the result is compact `powLimit`.
A successful result makes no claim that the supplied headers satisfy proof of work. -/
def getNextWorkRequired (params : WorkParams) (view : List BlockIndex)
    (candidateTime : UInt32) : Except NextWorkError UInt32 := do
  validateWorkView view
  getNextWorkRequiredFromView params view candidateTime

/-- Selects the candidate height's work parameters and calls `GetNextWorkRequired`.
Follows `src/validation.cpp` lines 3068-3070 and 3089 at `e0a1c15` (D33).
The checked view bounds the height before the UInt32 conversion is used. -/
def nextWorkRequired (network : WorkNetwork) (view : List BlockIndex)
    (candidateTime : UInt32) : Except NextWorkError UInt32 := do
  validateWorkView view
  let height := match view with | [] => 0 | last :: _ => last.nHeight + 1
  getNextWorkRequiredFromView (getConsensus network (UInt32.ofNat height)) view candidateTime

end DogeLib.Work
