module

public import DogeLib.Work.Retarget

/-!
# Work parameters by height

The module defines the work-field projection of Core's consensus trees at `e0a1c15` (SOURCES.md, D14, D15).
It omits rewards, version rules and AuxPoW validity.
The AuxPoW records remain in the trees because the search compares their effective heights.
-/

@[expose] public section

namespace DogeLib.Work

/-- Networks of `src/chainparams.cpp` at `e0a1c15`, lines 70, 223 and 377. -/
inductive WorkNetwork where
  | mainnet | testnet | regtest
  deriving DecidableEq, Repr

/-- Fields read by `GetNextWorkRequired`, `src/pow.cpp` lines 32-88 at `e0a1c15`.
The fixed network records supply positive spacing and intervals. -/
structure WorkParams extends RetargetParams where
  /-- `nPowTargetSpacing`, in seconds (`src/consensus/params.h`, D15, line 67). -/
  nPowTargetSpacing : Nat
  /-- Permission read by both minimum-difficulty branches (D17, D6). -/
  fPowAllowMinDifficultyBlocks : Bool

/-- `DifficultyAdjustmentInterval`, `src/consensus/params.h` line 69 (D15) at `e0a1c15`.
For the network records both operands are positive, so natural division agrees with C++ division. -/
def WorkParams.difficultyAdjustmentInterval (params : WorkParams) : Nat :=
  params.nPowTargetTimespan.toInt.toNat / params.nPowTargetSpacing

/-- A consensus record and its search links (`src/consensus/params.h`, D15, lines 84-88 at `e0a1c15`). -/
inductive ConsensusTree where
  | node (nHeightEffective : UInt32) (params : WorkParams)
      (pLeft pRight : Option ConsensusTree)

/-- The record selected by a tree search, including the effective height (`src/chainparams.cpp`, D14, lines 494-506 at `e0a1c15`).
The right candidate is used only if its effective height does not exceed the target. -/
def ConsensusTree.getConsensus : ConsensusTree → UInt32 → UInt32 × WorkParams
  | .node effective params left right, height =>
    if height < effective then
      match left with
      | some tree => tree.getConsensus height
      | none => (effective, params)
    else if height > effective then
      match right with
      | some tree =>
        let candidate := tree.getConsensus height
        if candidate.1 ≤ height then candidate else (effective, params)
      | none => (effective, params)
    else (effective, params)

/-- Mainnet before height 145000 (`src/chainparams.cpp`, D14, lines 88-95 at `e0a1c15`). -/
def mainnetWorkParams : WorkParams := ⟨mainnetParams, 60, false⟩

/-- Mainnet from height 145000, unchanged at 371337 (`src/chainparams.cpp`, D14, lines 126-136 at `e0a1c15`). -/
def mainnetDigishieldWorkParams : WorkParams := ⟨mainnetDigishieldParams, 60, false⟩

/-- Testnet before height 145000 (`src/chainparams.cpp`, D14, lines 233-251 at `e0a1c15`). -/
def testnetWorkParams : WorkParams := ⟨mainnetParams, 60, true⟩

/-- Testnet heights 145000-157499 (`src/chainparams.cpp`, D14, lines 282-288 at `e0a1c15`). -/
def testnetDigishieldWorkParams : WorkParams := ⟨mainnetDigishieldParams, 60, false⟩

/-- Testnet from height 157500, unchanged at 158100 (`src/chainparams.cpp`, D14, lines 291-300 at `e0a1c15`). -/
def testnetMinDifficultyWorkParams : WorkParams := ⟨mainnetDigishieldParams, 60, true⟩

/-- Regtest before height 10 (`src/chainparams.cpp`, D14, lines 392-397 at `e0a1c15`).
`fPowNoRetargeting` is absent because this caller does not read it. -/
def regtestWorkParams : WorkParams :=
  ⟨⟨⟨2 ^ 255 - 1, by decide⟩, 14400, false, by decide⟩, 1, true⟩

/-- Regtest from height 10, unchanged at 20 (`src/chainparams.cpp`, D14, lines 425-432 at `e0a1c15`). -/
def regtestDigishieldWorkParams : WorkParams :=
  ⟨⟨⟨2 ^ 255 - 1, by decide⟩, 1, true, by decide⟩, 1, true⟩

/-- Network trees with Core's links (`src/chainparams.cpp`, D14, lines 138-141, 302-306 and 434-437 at `e0a1c15`).
Core never assigns the base regtest record's effective height.
Its zero value comes from static initialization of `regTestParams` (line 485).
That height does not affect the search result, because the left branch returns without checking the effective height (lines 495-496). -/
def consensusTree : WorkNetwork → ConsensusTree
  | .mainnet => .node 145000 mainnetDigishieldWorkParams
      (some (.node 0 mainnetWorkParams none none))
      (some (.node 371337 mainnetDigishieldWorkParams none none))
  | .testnet => .node 145000 testnetDigishieldWorkParams
      (some (.node 0 testnetWorkParams none none))
      (some (.node 157500 testnetMinDifficultyWorkParams none
        (some (.node 158100 testnetMinDifficultyWorkParams none none))))
  | .regtest => .node 10 regtestDigishieldWorkParams
      (some (.node 0 regtestWorkParams none none))
      (some (.node 20 regtestDigishieldWorkParams none none))

/-- Work fields selected for a target height by Core's tree search (`src/chainparams.cpp`, D14, lines 494-506 at `e0a1c15`).
This projection applies to all UInt32 heights, including the AuxPoW eras. -/
def getConsensus (network : WorkNetwork) (height : UInt32) : WorkParams :=
  ((consensusTree network).getConsensus height).2

end DogeLib.Work
