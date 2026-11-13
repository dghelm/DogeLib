module

public import DogeLib.Block.Header

/-!
# Version bits

Core's `VersionBitsState` for a deployment, as `AbstractThresholdConditionChecker::GetStateFor` computes it (SOURCES.md, D102, lines 24 to 106).
The mainnet deployment parameters of CSV and SegWit come from the mainnet activation parameters (D100).

A deployment has a start time, a timeout, a signalling bit, a confirmation window `nMinerConfirmationWindow` and an activation threshold `nRuleChangeActivationThreshold`.
On mainnet the window is 10,080 blocks and the threshold is 9,576.
A block signals a deployment when its version has the top three bits `001` and the deployment's bit set (`VersionBitsConditionChecker::Condition`, D102, lines 153 to 156).

## The full walk and the shortcut

`versionBitsWalk` is the fold that `GetStateFor` computes.
Core aligns the predecessor to a period boundary, walks back one period at a time to a boundary whose state is known, and walks forward with `thresholdStep` (D102, lines 58 to 103).
The backward walk stops at a boundary whose median time past is below the start time, which Core treats as `DEFINED` (lines 44 to 47).
`thresholdStep` folds this reset into one function: a boundary below the start time gives `DEFINED` whatever the state before it.
So `versionBitsWalk` over every period boundary from the genesis period, with the state `DEFINED` before the first, gives the state that `GetStateFor` returns at the last boundary.

The full walk needs the version and time of every block, so a request through the full walk is large.
Design record 0010, section 4, gives a shortcut for the two cases that a request in continuous integration uses:

1. The last boundary's median time is below the start time: the state is `DEFINED`.
2. The last boundary's median time is at or after the timeout: the state is `FAILED`, given `csv_never_lockedIn`.

`versionBitsShortcut` returns the state in those two cases and `none` in the gap between them.
`versionBits_shortcut` (in `DogeLib.Block.Proofs.VersionBits`) proves that the shortcut equals the full walk in both cases, under the hypothesis of `csv_never_lockedIn` that every period signals no block.

## Source

The definitions follow Core's statements, with the reset of the backward walk folded into `thresholdStep`.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/versionbits.cpp`:

Copyright (c) 2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block

/-- The five states of `ThresholdState` (D102, `src/versionbits.h`, lines 20 to 27). -/
inductive ThresholdState where
  /-- `THRESHOLD_DEFINED`: the first state of every deployment. -/
  | defined
  /-- `THRESHOLD_STARTED`: the start time has passed, and the window counts signals. -/
  | started
  /-- `THRESHOLD_LOCKED_IN`: a window reached the threshold. -/
  | lockedIn
  /-- `THRESHOLD_ACTIVE`: the deployment is active. -/
  | active
  /-- `THRESHOLD_FAILED`: the timeout passed before lock-in. -/
  | failed
  deriving DecidableEq, Repr

/-- `VERSIONBITS_TOP_MASK` (D102, `src/versionbits.h`, line 16): the mask of the top three version bits. -/
def versionBitsTopMask : UInt32 := 0xE0000000

/-- `VERSIONBITS_TOP_BITS` (D102, `src/versionbits.h`, line 14): the required value of the top three version bits, `001`. -/
def versionBitsTopBits : UInt32 := 0x20000000

/-- The lowercase name of a `ThresholdState`, as the oracle reports it. -/
def ThresholdState.name : ThresholdState → String
  | .defined => "defined"
  | .started => "started"
  | .lockedIn => "locked_in"
  | .active => "active"
  | .failed => "failed"

/-- A versionbits deployment: its signalling bit, start time and timeout (D100). -/
structure Deployment where
  /-- The signalling bit, from 0 to 28. -/
  bit : Nat
  /-- `nStartTime`, the first median time at which the window counts signals. -/
  startTime : Int
  /-- `nTimeout`, the median time at or after which the deployment fails without lock-in. A timeout of 0 disables the deployment. -/
  timeout : Int
  deriving DecidableEq, Repr

/-- The mainnet CSV deployment (D100): bit 0, start 2016-05-01, timeout 2017-05-01. -/
def csvDeployment : Deployment := ⟨0, 1462060800, 1493596800⟩

/-- The mainnet SegWit deployment (D100): bit 1, start 2016-11-15, timeout 0 (disabled). -/
def segwitDeployment : Deployment := ⟨1, 1479168000, 0⟩

/-- `nMinerConfirmationWindow` on mainnet (D100): the length of a retarget-independent signalling window. -/
def minerConfirmationWindow : Nat := 10080

/-- `nRuleChangeActivationThreshold` on mainnet (D100): the number of signalling blocks in a window that locks a deployment in. -/
def ruleChangeActivationThreshold : Nat := 9576

/--
`VersionBitsConditionChecker::Condition` (D102, lines 153 to 156): a block signals the deployment when its version has the top three bits `001` and the deployment's bit set.
Core reads `pindex->nVersion` as the signed `int32_t` field, and the bitwise operations use its bit pattern, which is `nVersion`.
-/
def versionBitsCondition (dep : Deployment) (nVersion : UInt32) : Bool :=
  (nVersion &&& versionBitsTopMask == versionBitsTopBits) &&
    (nVersion &&& ((1 : UInt32) <<< dep.bit.toUInt32) != 0)

/--
One period boundary of the walk: its median time past and the number of blocks in its period that signal the deployment.
`GetStateFor` reads the median time at the boundary (D102, lines 44 and 65) and counts the signals of the period (lines 78 to 85).
-/
structure PeriodBoundary where
  /-- The median time past at the boundary, widened to `Int` as `GetMedianTimePast` widens it. -/
  mtp : Int
  /-- The number of blocks in the period that `versionBitsCondition` accepts. -/
  conditionCount : Nat
  deriving DecidableEq, Repr

/--
One step of the forward walk of `GetStateFor` (D102, lines 58 to 103), with the backward-walk reset folded in.

A boundary whose median time is below the start time gives `DEFINED`, as the backward walk stops there (lines 44 to 47).
Otherwise the step follows Core's switch:

- From `DEFINED`: the timeout gives `FAILED`, and otherwise the start time (reached here) gives `STARTED` (lines 64 to 69).
- From `STARTED`: the timeout gives `FAILED`, and otherwise a count at or above the threshold gives `LOCKED_IN` (lines 72 to 89).
- `LOCKED_IN` goes to `ACTIVE`, and `ACTIVE` and `FAILED` are terminal (lines 91 to 100).
-/
def thresholdStep (dep : Deployment) (threshold : Nat) (s : ThresholdState) (b : PeriodBoundary) :
    ThresholdState :=
  if b.mtp < dep.startTime then .defined
  else
    match s with
    | .defined => if dep.timeout ≤ b.mtp then .failed else .started
    | .started =>
      if dep.timeout ≤ b.mtp then .failed
      else if threshold ≤ b.conditionCount then .lockedIn else .started
    | .lockedIn => .active
    | .active => .active
    | .failed => .failed

/--
The state that `GetStateFor` returns at the last boundary of `boundaries` (D102, lines 24 to 106).
`boundaries` holds every period boundary from the genesis period up to the aligned boundary, oldest first.
The fold starts at `DEFINED`, the state of the genesis period.
-/
def versionBitsWalk (dep : Deployment) (threshold : Nat) (boundaries : List PeriodBoundary) :
    ThresholdState :=
  boundaries.foldl (thresholdStep dep threshold) .defined

/--
The shortcut of design record 0010, section 4, for the aligned boundary's median time `mtp`.
It returns `DEFINED` below the start time, `FAILED` at or after the timeout, and `none` in the gap between them.
For a deployment with a timeout of 0, such as SegWit, the gap is empty.
-/
def versionBitsShortcut (dep : Deployment) (mtp : Int) : Option ThresholdState :=
  if mtp < dep.startTime then some .defined
  else if dep.timeout ≤ mtp then some .failed
  else none

/--
The deployment's state at an aligned boundary, by the shortcut.
A null boundary, below the first period, gives `DEFINED` (D102, lines 39 to 47).
Otherwise the result is `versionBitsShortcut` of the boundary's median time, which is `none` in the case-3 gap.
-/
def versionBitsStateFromBoundary (dep : Deployment) : Option Int → Option ThresholdState
  | none => some .defined
  | some mtp => versionBitsShortcut dep mtp

/-! ## The full walk from a header chain

`versionBitsStateFull` computes the state from the version and time of every block, for the outside-CI comparison with Core.
It splits the chain into periods, counts the signalling blocks of each period and takes the median time at each boundary, then folds with `versionBitsWalk`.
-/

/-- `nMedianTimeSpan` (D18): the number of blocks in a median time past. -/
def versionBitsMedianSpan : Nat := 11

/-- The version and time of a block, which `GetStateFor` reads (D102). -/
structure VbEntry where
  /-- The block's `nVersion`. -/
  nVersion : UInt32
  /-- The block's `nTime`. -/
  nTime : UInt32
  deriving DecidableEq, Repr

/-- The number of blocks in `entries` whose version signals `dep` (D102, `Condition`). -/
def signalCount (dep : Deployment) (entries : List VbEntry) : Nat :=
  entries.countP (fun e => versionBitsCondition dep e.nVersion)

/-- The median of the times of `entries`, widened to `Int`, as `GetMedianTimePast` sorts and takes the middle (D18). -/
def medianTime (entries : List VbEntry) : Int :=
  let ts := (entries.map (fun e => (e.nTime.toNat : Int))).mergeSort
  ts.getD (ts.length / 2) 0

/--
The period boundaries of a chain, oldest first, one for each complete period of `period` blocks.
`chain` is the blocks from the genesis block, oldest first.
Each boundary's signal count is over its period, and its median time is over the last `nMedianTimeSpan` blocks of the period, which are the boundary and its predecessors.
This median takes its samples from the period alone, so it matches Core only when the period is at least `nMedianTimeSpan`, as the mainnet window of 10,080 is.
-/
def chainBoundaries (dep : Deployment) (period : Nat) (chain : List VbEntry) : List PeriodBoundary :=
  (List.range (chain.length / period)).map fun i =>
    let p := (chain.drop (i * period)).take period
    ⟨medianTime (p.drop (period - versionBitsMedianSpan)), signalCount dep p⟩

/--
The state that `GetStateFor` returns at the last complete period boundary of `chain` (D102, lines 24 to 106).
`chain` holds the blocks from the genesis block to the aligned boundary, oldest first, so its length is a multiple of the period.
-/
def versionBitsStateFull (dep : Deployment) (threshold : Nat) (chain : List VbEntry) : ThresholdState :=
  versionBitsWalk dep threshold (chainBoundaries dep minerConfirmationWindow chain)

end DogeLib.Block
