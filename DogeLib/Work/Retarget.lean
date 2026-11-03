module

public import DogeLib.Work.ArithUint256

/-!
# `Retarget`

Dogecoin's difficulty retarget arithmetic: `CalculateDogecoinNextWorkRequired` in `src/dogecoin.cpp` lines 41-87, at Dogecoin Core `e0a1c15` (SOURCES.md, D6).

The function computes the compact target of the next block from explicit inputs:

```text
nBits             pindexLast->nBits            compact target of the last block
nLastBlockTime    pindexLast->GetBlockTime()   time of the last block, (int64_t)nTime (D18)
nFirstBlockTime   nFirstBlockTime              time of the first block of the interval
nHeight           pindexLast->nHeight + 1      height of the next block (line 43)
params            the consensus parameters     nPowTargetTimespan, powLimit,
                                               fDigishieldDifficultyCalculation
```

The steps follow the source:

```text
45      nActualTimespan = nLastBlockTime - nFirstBlockTime                   int64_t
50-66   DigiShield: nModulatedTimespan = T + (nActualTimespan - T) / 8       int64_t, / truncates
        bounds [T - T/4, T + T/2], or [T/4, 4T], [T/8, 4T], [T/16, 4T] by height
68-72   clamp nModulatedTimespan to the bounds
78      bnNew.SetCompact(nBits)                                              flags ignored
80      bnNew *= nModulatedTimespan    operator*=(uint32_t): converts to uint32_t, mod 2^256
81      bnNew /= retargetTimespan      operator/=(const base_uint&): converts to uint64_t
83-84   bnNew = min(bnNew, powLimit)
86      return bnNew.GetCompact()                                            fNegative = false
```

`T` is `params.nPowTargetTimespan`.

## Signed arithmetic

The source computes the timespans in `int64_t`.
This module computes them in `Int`, with `Int.tdiv` for the C++ `/` operator.
Core builds as C++11 by default (configure.ac line 81, SOURCES.md D19), and C++14 and C++17 keep the rules below.
C++11 discards the fractional part of a quotient ([expr.mul] paragraph 4, SOURCES.md S1), so the quotient rounds toward zero.
`Int.tdiv` also rounds toward zero, and `Int./` rounds down, so the two differ when the dividend is negative.
Core's test `get_next_work_digishield_rounding` depends on that difference (D7).

`Int` agrees with `int64_t` while no step overflows, and a signed overflow is undefined behavior in C++.
`signedSteps_fit` in `DogeLib.Work.Proofs.Retarget` proves that no step overflows when both block times are in `[0, 2^32)` and `nPowTargetTimespan < 2^61`.
The only caller, `GetNextWorkRequired` (D17), passes two values of `GetBlockTime`, which widens a `uint32_t` time (D18), so both are in that range.
`modulatedTimespan_eq_int64` proves that Lean's `Int64` operations compute the same value on that domain.

## Overload selection

`bnNew` is an `arith_uint256` and `nModulatedTimespan` is an `int64_t`.
`base_uint` declares `operator*=(uint32_t)` and `operator*=(const base_uint&)` (arith_uint256.h lines 169 and 170).
The first needs only the integral conversion from `int64_t` to `uint32_t`.
The second needs a user-defined conversion through the constructor `base_uint(uint64_t)` (line 51).
A standard conversion sequence is better than a user-defined one ([over.ics.rank] paragraph 2), so line 80 calls `operator*=(uint32_t)`.
The conversion to `uint32_t` keeps the value modulo 2^32 ([conv.integral] paragraph 2).

`base_uint` declares only `operator/=(const base_uint&)` (line 171).
So line 81 converts `retargetTimespan` to `uint64_t` modulo 2^64, then builds a `base_uint` from it through `base_uint(uint64_t)`.

## Parameters

`RetargetParams` holds the three fields of `Consensus::Params` that the function reads.
It requires `nPowTargetTimespan > 0`: every network of the pinned Core sets 14400, 60 or 1 (D14).
With a zero timespan, Core throws `uint_error` at line 81.

Which parameters apply at which height is not part of this module.
Core selects them with `Consensus::Params::GetConsensus` (D14), and `GetNextWorkRequired` in `src/pow.cpp` (D17) chooses when to call this function and with which first block.
-/

@[expose] public section

namespace DogeLib.Work

/-- The fields of `Consensus::Params` (src/consensus/params.h, D15) that the retarget reads. -/
structure RetargetParams where
  /-- `powLimit`: the largest target, the lowest difficulty. -/
  powLimit : ArithUint256
  /-- `nPowTargetTimespan`: the target time of one retarget interval, in seconds. -/
  nPowTargetTimespan : Int64
  /-- `fDigishieldDifficultyCalculation`: the DigiShield amplitude filter and bounds apply. -/
  fDigishieldDifficultyCalculation : Bool
  /-- The target timespan is positive, so that the division at line 81 never divides by zero. -/
  nPowTargetTimespan_pos : 0 < nPowTargetTimespan

namespace RetargetParams

/-- `nPowTargetTimespan` as a mathematical integer, the `retargetTimespan` of line 44. -/
def retargetTimespan (params : RetargetParams) : Int := params.nPowTargetTimespan.toInt

end RetargetParams

/-! ## Timespans -/

/-- `nActualTimespan` (line 45): the last block time minus the first block time. -/
def actualTimespan (nLastBlockTime nFirstBlockTime : Int64) : Int :=
  nLastBlockTime.toInt - nFirstBlockTime.toInt

/-- The pair `(nMinTimespan, nMaxTimespan)` of lines 50-66.

DigiShield allows a quarter less and a half more than the target timespan.
Before DigiShield, the maximum is four times the target, and the minimum depends on the height of the next block. -/
def timespanLimits (params : RetargetParams) (nHeight : Int32) : Int × Int :=
  let retargetTimespan := params.retargetTimespan
  if params.fDigishieldDifficultyCalculation then
    (retargetTimespan - retargetTimespan.tdiv 4, retargetTimespan + retargetTimespan.tdiv 2)
  else if nHeight > 10000 then
    (retargetTimespan.tdiv 4, retargetTimespan * 4)
  else if nHeight > 5000 then
    (retargetTimespan.tdiv 8, retargetTimespan * 4)
  else
    (retargetTimespan.tdiv 16, retargetTimespan * 4)

/-- The timespan before the clamp.
DigiShield's amplitude filter (line 53) moves the actual timespan an eighth of the way from the target, with a quotient that rounds toward zero.
Without DigiShield, it is the actual timespan. -/
def filteredTimespan (params : RetargetParams) (nActualTimespan : Int) : Int :=
  let retargetTimespan := params.retargetTimespan
  if params.fDigishieldDifficultyCalculation then
    retargetTimespan + (nActualTimespan - retargetTimespan).tdiv 8
  else
    nActualTimespan

/-- `nModulatedTimespan` after the clamp of lines 68-72. -/
def modulatedTimespan (params : RetargetParams) (nHeight : Int32) (nActualTimespan : Int) : Int :=
  let (nMinTimespan, nMaxTimespan) := timespanLimits params nHeight
  let nModulatedTimespan := filteredTimespan params nActualTimespan
  if nModulatedTimespan < nMinTimespan then nMinTimespan
  else if nModulatedTimespan > nMaxTimespan then nMaxTimespan
  else nModulatedTimespan

/-! ## Integral conversions -/

/-- The conversion of an `int64_t` value to `uint32_t`: the value modulo 2^32 ([conv.integral] paragraph 2). -/
def toUInt32 (x : Int) : UInt32 := UInt32.ofNat (x % 2 ^ 32).toNat

/-- The conversion of an `int64_t` value to `uint64_t`: the value modulo 2^64 ([conv.integral] paragraph 2). -/
def toUInt64 (x : Int) : Nat := (x % 2 ^ 64).toNat

/-- The divisor of line 81, `base_uint(uint64_t(retargetTimespan))`, is not zero. -/
theorem retargetDivisor_ne_zero (params : RetargetParams) :
    (ArithUint256.ofNat (toUInt64 params.retargetTimespan)).val ≠ 0 := by
  have pos := Int64.lt_iff_toInt_lt.mp params.nPowTargetTimespan_pos
  have lt := params.nPowTargetTimespan.toInt_lt
  simp only [ArithUint256.ofNat, toUInt64, RetargetParams.retargetTimespan, Int64.toInt_zero] at *
  omega

/-! ## The retarget -/

/--
`CalculateDogecoinNextWorkRequired(pindexLast, nFirstBlockTime, params)` (src/dogecoin.cpp lines 41-87).

The arguments are the values that Core reads from `pindexLast`, as the module docstring lists them.
`nHeight` is the height of the next block, `pindexLast->nHeight + 1`.
The result is the compact target that the next block must carry.

`SetCompact` ignores the sign and overflow flags here (line 78).
The multiplication and the division follow the overloads that the module docstring explains.
-/
def calculateDogecoinNextWorkRequired (params : RetargetParams) (nHeight : Int32)
    (nLastBlockTime nFirstBlockTime : Int64) (nBits : UInt32) : UInt32 :=
  let nModulatedTimespan :=
    modulatedTimespan params nHeight (actualTimespan nLastBlockTime nFirstBlockTime)
  let bnNew := (ArithUint256.setCompact nBits).value
  let bnNew := bnNew.mulUInt32 (toUInt32 nModulatedTimespan)
  let bnNew := bnNew.div (ArithUint256.ofNat (toUInt64 params.retargetTimespan))
    (retargetDivisor_ne_zero params)
  let bnNew := if bnNew > params.powLimit then params.powLimit else bnNew
  ArithUint256.getCompact bnNew

/-! ## Dogecoin mainnet parameters -/

/-- Mainnet `powLimit` (src/chainparams.cpp line 88): 2^236 - 1. -/
def mainnetPowLimit : ArithUint256 :=
  ⟨0x00000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, by decide⟩

/-- Mainnet parameters before DigiShield, `Params().GetConsensus(0)` (src/chainparams.cpp lines 88-91). -/
def mainnetParams : RetargetParams where
  powLimit := mainnetPowLimit
  nPowTargetTimespan := 4 * 60 * 60
  fDigishieldDifficultyCalculation := false
  nPowTargetTimespan_pos := by decide

/-- Mainnet parameters from height 145000, `digishieldConsensus` (src/chainparams.cpp lines 126-130).
The AuxPoW parameters from height 371337 keep these three fields (lines 134-136). -/
def mainnetDigishieldParams : RetargetParams where
  powLimit := mainnetPowLimit
  nPowTargetTimespan := 60
  fDigishieldDifficultyCalculation := true
  nPowTargetTimespan_pos := by decide

end DogeLib.Work
