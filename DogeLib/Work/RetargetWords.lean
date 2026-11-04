module

public import DogeLib.Work.Retarget
public import DogeLib.Work.ArithUint256Compact
public import DogeLib.Work.ArithUint256Bytes

/-!
# Retarget arithmetic over Core's words

This model follows Dogecoin Core `e0a1c15`, `src/dogecoin.cpp` lines 75-86 (SOURCES.md, D6).
Core's lines 41-74 come through the timespan specification and its signed-arithmetic domain in `Work.Retarget`.
All target operations use word models, including the divisor constructor and the limit comparison.
The byte entry point includes Core's `UintToArith256` conversion of `powLimit`.
The arithmetic entry point accepts the existing `RetargetParams` representation.
Division keeps its `Option`, so an exception cannot silently become a target.

The adapted code is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notices:

Copyright (c) 2015-2022 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work

open ArithUint256

/-- The retarget's target operations with an explicit word limit (D6 lines 75-86).
The timespan parameters keep the existing positive-target-timespan domain. -/
def calculateDogecoinNextWorkRequiredWithWords (params : RetargetParams) (powLimit : Words)
    (nHeight : Int32) (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) : Option UInt32 := do
  let nModulatedTimespan :=
    modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)
  let bnNew := Words.readWords (Vector.ofFn (Words.setCompact nBits).value)
  let bnNew := Words.readWords (Vector.ofFn (Words.mulUInt32 bnNew (toUInt32 nModulatedTimespan)))
  let divisor := Words.ofUInt64 (UInt64.ofNat (toUInt64 params.retargetTimespan))
  let bnNew ← Words.divide bnNew divisor
  let bnNew := Words.readWords (Vector.ofFn bnNew)
  let bnNew := if Words.compareTo bnNew powLimit == .gt then powLimit else bnNew
  return Words.getCompact bnNew

/-- Word retarget for every existing arithmetic parameter record (D6 lines 75-86).
`ofArith` supplies the limit's words at this API boundary. -/
def calculateDogecoinNextWorkRequiredWords (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) : Option UInt32 :=
  calculateDogecoinNextWorkRequiredWithWords params (Words.ofArith params.powLimit)
    nHeight nLastBlockTime nFirstBlockTime nBits

/-- Word retarget from Core's 32-byte powLimit representation (D6 line 75 and D13 lines 254-260).
The explicit bytes supply the limit instead of the arithmetic field in `params`. -/
def calculateDogecoinNextWorkRequiredBytes (params : RetargetParams) (powLimit : TargetBytes)
    (nHeight : Int32) (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) : Option UInt32 :=
  calculateDogecoinNextWorkRequiredWithWords params
    (Words.readWords (Vector.ofFn (Words.uintToArith256 powLimit)))
    nHeight nLastBlockTime nFirstBlockTime nBits

end DogeLib.Work
