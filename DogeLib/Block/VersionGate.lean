module

public import DogeLib.Block.AuxPowCheck

/-!
# Version gating

The two version checks at the start of Core's `ContextualCheckBlockHeader` (SOURCES.md, D33, lines 3072 to 3086).
They reject a legacy version once merged mining is active, and an AuxPoW flag before it is active.
Design record 0004 adds them as stage 4b, under decision 1 of its section 9.

`checkVersion` reads only the version of the header and the `fAllowLegacyBlocks` field of a parameter record.
The caller selects the record.
Core selects it with `GetConsensus` at the height of the new header (D14).
This module does not select a record from a height, and it does not model the record tree of `chainparams.cpp`.
It also omits every other check of `ContextualCheckBlockHeader`: `nBits` against `GetNextWorkRequired`, the checkpoints, the time checks and the rejection of outdated versions.
The theorems are in `DogeLib.Block.Proofs.VersionGate`.

## Source

The adaptation follows Core's two statements in order, with a named error for each rejection.
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

/--
Core's `IsLegacy` (D10, lines 150 to 155): the signed version is 1, or it is 2 with chain ID zero.
The chain ID of version 2 is always zero, so a version is legacy exactly when it is 1 or 2 (`PureBlockHeader.isLegacy_iff`).
-/
def PureBlockHeader.isLegacy (h : PureBlockHeader) : Bool :=
  h.signedVersion == 1 || (h.signedVersion == 2 && h.chainId == 0)

/--
The fields of Core's `Consensus::Params` (D15) that `checkVersion` reads.
The caller selects the record, as `GetConsensus` does for a height in Core (D14).
-/
structure VersionGateParams where
  /-- `fAllowLegacyBlocks`: true before merged mining is active, and false from its activation height on (D14). -/
  allowLegacyBlocks : Bool
  deriving DecidableEq, Repr

/-- The reason that `checkVersion` rejects a header: one constructor for each `return state.DoS(...)` of D33, in source order. -/
inductive VersionGateError where
  /-- Legacy blocks are not allowed, and the version is legacy: `late-legacy-block` (lines 3073 to 3077). -/
  | lateLegacyBlock
  /-- Legacy blocks are allowed, and the AuxPoW flag is set: `early-auxpow-block` (lines 3079 to 3086). -/
  | earlyAuxpowBlock
  deriving DecidableEq, Repr

/-- The reject reason that Core reports for each error (D33, lines 3077 and 3086). -/
def VersionGateError.rejectReason : VersionGateError → String
  | .lateLegacyBlock => "late-legacy-block"
  | .earlyAuxpowBlock => "early-auxpow-block"

/--
The version checks of Core's `ContextualCheckBlockHeader` (D33, lines 3072 to 3086), with the first failing check as its error.

1. If the record does not allow legacy blocks, the version must not be legacy.
2. If the record allows legacy blocks, the AuxPoW flag must be clear.

The function reads only `nVersion` of the header and `allowLegacyBlocks` of the record.
It does not select the record from a height, and it omits the other checks of `ContextualCheckBlockHeader`.
-/
def checkVersion (p : VersionGateParams) (h : PureBlockHeader) : Except VersionGateError Unit :=
  if !p.allowLegacyBlocks && h.isLegacy then .error .lateLegacyBlock
  else if p.allowLegacyBlocks && h.isAuxpow then .error .earlyAuxpowBlock
  else .ok ()

end DogeLib.Block
