module

public import DogeLib.Block.ContextualParams
public import DogeLib.Work.MedianTimePast

/-!
# Contextual header validation

Core's `ContextualCheckBlockHeader` (SOURCES.md, D33, lines 3066 to 3119), design record 0006, stage 3.
The function checks a header against the chain that it extends, the node's adjusted time and the last checkpoint that the node knows.
It runs seven checks in Core's order and returns the first failure:

1. Without `fAllowLegacyBlocks`, the header must not be legacy: `late-legacy-block` (lines 3073 to 3077).
2. With `fAllowLegacyBlocks`, the AuxPoW flag must be clear: `early-auxpow-block` (lines 3082 to 3086).
3. `nBits` must equal `GetNextWorkRequired` as raw 32-bit values: `bad-diffbits` (lines 3089 and 3090).
4. The candidate height must not be below the last known checkpoint: `bad-fork-prior-to-checkpoint` (lines 3093 to 3100).
5. The header time must be greater than the median time past of the predecessor: `time-too-old` (lines 3103 and 3104).
6. The header time must be at most the adjusted time plus two hours: `time-too-new` (lines 3107 and 3108).
7. The base version must be at least 3 from `BIP66Height`, and at least 4 from `BIP65Height`: `bad-version(0x…)` (lines 3113 to 3116).

The parameter record comes from `GetConsensus` at the candidate height, the predecessor's height plus one (lines 3068 to 3070).
Checks 1 and 2 are `checkVersion`, check 3 uses `Work.nextWorkRequired`, and check 5 uses `Work.medianTimePast`.

## Inputs and domain

The chain enters as the checked finite view of `Work.NextWork`: block-index entries from the predecessor down, newest first.
Core's callers always pass a predecessor (D33, lines 3205 to 3267 and 3412 to 3423).
So the view must not be empty, and the domain excludes the genesis header.
The function cannot check that the view is the chain of the header's `hashPrevBlock`, because no check reads a hash.
The caller asserts that link, as Core's lookup of `pindexPrev` does.

The adjusted time is an `Int64` input, as `nAdjustedTime` is in Core.
Core's callers pass `GetAdjustedTime()`, the system time plus a peer offset (`src/timedata.cpp`, D72, lines 34 to 37), and this module does not model that source.
Core computes `nAdjustedTime + 7200` in signed 64-bit arithmetic, which overflows above `INT64_MAX - 7200`.
That overflow is undefined behaviour in C++, so the domain excludes those adjusted times (design record 0006, decision 9).

Check 4 takes the height of the last known checkpoint as an input.
`contextualCheckBlockHeaderWithCheckpoints` derives that height with `lastCheckpoint` from the enabled flag and the known checkpoint heights (decision 2).

## Adapter errors

An input outside the domain returns an adapter error, never a Core rejection:

- An empty view.
- A view that `validateWorkView` rejects.
- A view with fewer entries than Core's median walk reads (`Work.medianTimePast`).
- A view that lacks an ancestor that `GetNextWorkRequired` reads, or another `NextWorkError`.
- An adjusted time above `INT64_MAX - 7200`.

The function checks the domain before check 1.
So an input outside the domain returns an adapter error even when Core would reject it at an earlier check.
On the domain, the function runs Core's checks in Core's order, and source review connects each check to Core.
No theorem or comparison establishes agreement with compiled Core.

Every time comparison widens `nTime` to `Int`, as `GetBlockTime` widens it to `int64_t` (D10, lines 73 to 76).
On the domain, the `Int` comparisons equal Core's signed 64-bit comparisons, because no value overflows.
The theorems are in `DogeLib.Block.Proofs.ContextualCheck`.

## Source

The definitions follow Core's statements in order, with a named error for each rejection.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/validation.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Work

/-- Core's `CBlockHeader::GetBlockTime` (`src/primitives/pureheader.h`, D10, lines 73 to 76): the UInt32 time widened exactly to Int. -/
def PureBlockHeader.getBlockTime (h : PureBlockHeader) : Int := h.nTime.toNat

/--
Core's `GetBaseVersion` (D10, lines 88 to 95): `nVersion % VERSION_AUXPOW`, with `VERSION_AUXPOW = 256`.
The C++ remainder of a signed `int32_t` truncates toward zero, as `Int.tmod` does.
So a negative version has a base version from −255 to 0.
For example, `0x80000003` has the base version −253.
-/
def PureBlockHeader.getBaseVersion (h : PureBlockHeader) : Int := h.signedVersion.toInt.tmod 256

/-- The bound of check 6 above the adjusted time, `2 * 60 * 60` seconds (D33, line 3107). -/
def maxFutureBlockTime : Int := 2 * 60 * 60

/--
The greatest adjusted time for which Core's sum `nAdjustedTime + 2 * 60 * 60` does not overflow `int64_t`: `INT64_MAX - 7200`.
A greater adjusted time is outside the domain (design record 0006, decision 9).
-/
def maxAdjustedTime : Int := 9223372036854775807 - maxFutureBlockTime

/--
The result of `contextualCheckBlockHeader` when it does not accept.
The first seven constructors are Core's rejections, one for each check of D33, lines 3066 to 3119, in source order.
The other constructors are adapter errors for an input outside the domain. They are not Core verdicts.
-/
inductive ContextualHeaderError where
  /-- Check 1: legacy blocks are not allowed, and the version is legacy: `late-legacy-block` (lines 3073 to 3077). -/
  | lateLegacyBlock
  /-- Check 2: legacy blocks are allowed, and the AuxPoW flag is set: `early-auxpow-block` (lines 3082 to 3086). -/
  | earlyAuxpowBlock
  /-- Check 3: `nBits` differs from the required compact value: `bad-diffbits` (lines 3089 and 3090). -/
  | badDiffbits
  /-- Check 4: the candidate height is below the last known checkpoint: `bad-fork-prior-to-checkpoint` (lines 3093 to 3100). -/
  | badForkPriorToCheckpoint
  /-- Check 5: the header time is at most the median time past: `time-too-old` (lines 3103 and 3104). -/
  | timeTooOld
  /-- Check 6: the header time is greater than the adjusted time plus two hours: `time-too-new` (lines 3107 and 3108). -/
  | timeTooNew
  /-- Check 7: the base version is below the threshold for the candidate height: `bad-version(0x…)` (lines 3113 to 3116).
  The field is the base version. -/
  | badVersion (baseVersion : Int)
  /-- Adapter error: the view is empty, so there is no predecessor. -/
  | emptyView
  /-- Adapter error: `validateWorkView` rejects the view, with its error. -/
  | invalidView (error : NextWorkError)
  /-- Adapter error: the view has fewer entries than Core's median walk reads. -/
  | shortView
  /-- Adapter error: `Work.nextWorkRequired` returns this error, for example `missingAncestor`. -/
  | nextWork (error : NextWorkError)
  /-- Adapter error: the adjusted time is above `maxAdjustedTime`, where Core's sum overflows. -/
  | adjustedTimeOutOfRange
  deriving DecidableEq, Repr

/-- True for the seven Core rejections, and false for the adapter errors. -/
def ContextualHeaderError.isRejection : ContextualHeaderError → Bool
  | .lateLegacyBlock | .earlyAuxpowBlock | .badDiffbits | .badForkPriorToCheckpoint | .timeTooOld
  | .timeTooNew | .badVersion _ => true
  | .emptyView | .invalidView _ | .shortView | .nextWork _ | .adjustedTimeOutOfRange => false

/--
Eight lowercase hexadecimal digits of the 32-bit two's-complement pattern of `n`, as Core's `%08x` prints an `int32_t`.
Core's `strprintf` sets hexadecimal output and zero fill for `%08x`, and writes the value to a C++ stream (`src/tinyformat.h`, D71, lines 308 to 338, 612 to 620 and 709 to 712).
In hexadecimal, the stream prints a signed `int` as its unsigned 32-bit pattern, so −253 prints as `ffffff03`.
For an `n` from −2147483648 to 2147483647, the result has exactly eight digits.
-/
def hex8 (n : Int) : String :=
  let digits := Nat.toDigits 16 (n % 4294967296).toNat
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/--
Core's reject reason for each rejection (D33, lines 3077, 3086, 3090, 3099, 3104, 3108 and 3115), and `none` for an adapter error.
The reason of check 7 is `bad-version(0x%08x)` with the base version.
-/
def ContextualHeaderError.rejectReason : ContextualHeaderError → Option String
  | .lateLegacyBlock => some "late-legacy-block"
  | .earlyAuxpowBlock => some "early-auxpow-block"
  | .badDiffbits => some "bad-diffbits"
  | .badForkPriorToCheckpoint => some "bad-fork-prior-to-checkpoint"
  | .timeTooOld => some "time-too-old"
  | .timeTooNew => some "time-too-new"
  | .badVersion baseVersion => some s!"bad-version(0x{hex8 baseVersion})"
  | .emptyView | .invalidView _ | .shortView | .nextWork _ | .adjustedTimeOutOfRange => none

/-- The rejection of `checkVersion` as a rejection of the contextual check. -/
def ContextualHeaderError.ofVersionGate : VersionGateError → ContextualHeaderError
  | .lateLegacyBlock => .lateLegacyBlock
  | .earlyAuxpowBlock => .earlyAuxpowBlock

/-- The adapter error of `Work.medianTimePast` as an adapter error of the contextual check. -/
def ContextualHeaderError.ofMedianTime : MedianTimeError → ContextualHeaderError
  | .invalidView error => .invalidView error
  | .emptyView => .emptyView
  | .shortView => .shortView

/-- Check 3 (D33, lines 3089 and 3090): `nBits` must equal the required value.
The comparison is of the raw 32-bit values, so another compact encoding of the same target fails. -/
def checkDiffbits (header : PureBlockHeader) (required : UInt32) : Except ContextualHeaderError Unit :=
  if header.nBits = required then .ok () else .error .badDiffbits

/-- Check 4 (D33, lines 3093 to 3100): the candidate height must not be below the height of the last known checkpoint.
`none` means that checkpoints are disabled or that the node knows no checkpoint, and then the check passes. -/
def checkCheckpoint (height : Nat) (lastCheckpointHeight : Option Nat) : Except ContextualHeaderError Unit :=
  match lastCheckpointHeight with
  | some checkpoint => if height < checkpoint then .error .badForkPriorToCheckpoint else .ok ()
  | none => .ok ()

/-- Check 5 (D33, lines 3103 and 3104): the header time must be greater than the median time past.
A header time equal to the median fails. -/
def checkTimeTooOld (header : PureBlockHeader) (median : Int) : Except ContextualHeaderError Unit :=
  if header.getBlockTime ≤ median then .error .timeTooOld else .ok ()

/-- Check 6 (D33, lines 3107 and 3108): the header time must be at most the adjusted time plus `maxFutureBlockTime`.
A header time equal to that bound passes. -/
def checkTimeTooNew (header : PureBlockHeader) (adjustedTime : Int) : Except ContextualHeaderError Unit :=
  if adjustedTime + maxFutureBlockTime < header.getBlockTime then .error .timeTooNew else .ok ()

/-- Check 7 (D33, lines 3113 to 3116): from `BIP66Height` the base version must be at least 3, and from `BIP65Height` at least 4.
Both thresholds compare the candidate height with `≥`. -/
def checkBaseVersion (params : ContextualParams) (height : Nat) (header : PureBlockHeader) :
    Except ContextualHeaderError Unit :=
  if (header.getBaseVersion < 3 ∧ params.bip66Height ≤ height) ∨
      (header.getBaseVersion < 4 ∧ params.bip65Height ≤ height) then
    .error (.badVersion header.getBaseVersion)
  else .ok ()

/--
The seven checks of `ContextualCheckBlockHeader` (D33, lines 3072 to 3116) on derived values, in Core's order.
`params` is the selected record, `height` the candidate height, `required` the result of `GetNextWorkRequired`, and `median` the median time past of the predecessor.
`adjustedTime` is the widened adjusted time.
The function returns the first failing check.
-/
def contextualChecks (params : ContextualParams) (height : Nat) (header : PureBlockHeader)
    (required : UInt32) (median adjustedTime : Int) (lastCheckpointHeight : Option Nat) :
    Except ContextualHeaderError Unit := do
  (checkVersion params.toVersionGateParams header).mapError .ofVersionGate
  checkDiffbits header required
  checkCheckpoint height lastCheckpointHeight
  checkTimeTooOld header median
  checkTimeTooNew header adjustedTime
  checkBaseVersion params height header

/--
Core's `ContextualCheckBlockHeader` (D33, lines 3066 to 3119) on a checked finite view.

`view` holds the predecessor and its ancestors, newest first, as `Work.BlockIndex` entries.
`adjustedTime` is `nAdjustedTime`.
`lastCheckpointHeight` is the height of the checkpoint that `GetLastCheckpoint` returns, or `none` when checkpoints are disabled or no checkpoint is known.

The function first checks the domain and returns an adapter error outside it.
Then it computes the candidate height, the record of `getContextualParams` at that height, the median time past and the required work.
It returns `contextualChecks` on those values: `.ok ()` when every check passes, and otherwise the first failing check.
-/
def contextualCheckBlockHeader (network : WorkNetwork) (header : PureBlockHeader)
    (view : List BlockIndex) (adjustedTime : Int64) (lastCheckpointHeight : Option Nat) :
    Except ContextualHeaderError Unit :=
  match view with
  | [] => .error .emptyView
  | prev :: rest => do
    let median ← (medianTimePast (prev :: rest)).mapError .ofMedianTime
    let required ← (nextWorkRequired network (prev :: rest) header.nTime).mapError .nextWork
    if maxAdjustedTime < adjustedTime.toInt then throw .adjustedTimeOutOfRange
    let height := prev.nHeight + 1
    contextualChecks (getContextualParams network (UInt32.ofNat height)) height header required median
      adjustedTime.toInt lastCheckpointHeight

/--
`contextualCheckBlockHeader` with the checkpoint state of design record 0006, decision 2.
`checkpointsEnabled` is `fCheckpointsEnabled`, and `knownCheckpoints` holds the table heights whose hashes the node's block index contains.
`lastCheckpoint` derives the height that check 4 compares.
-/
def contextualCheckBlockHeaderWithCheckpoints (network : WorkNetwork) (header : PureBlockHeader)
    (view : List BlockIndex) (adjustedTime : Int64) (checkpointsEnabled : Bool)
    (knownCheckpoints : List Nat) : Except ContextualHeaderError Unit :=
  contextualCheckBlockHeader network header view adjustedTime
    (lastCheckpoint network checkpointsEnabled knownCheckpoints)

end DogeLib.Block
