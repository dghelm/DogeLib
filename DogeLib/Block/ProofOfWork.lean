module

public import DogeLib.Block.AuxPowCheck
public import DogeLib.Block.VersionGate
public import DogeLib.Cryptography.Hash.Scrypt
public import DogeLib.Work.Consensus
public import DogeLib.Work.ProofOfWork

/-!
# Header proof of work

Core's `CheckAuxPowProofOfWork` and the proof-of-work check of `CheckBlockHeader`, design record 0004, stage 4a.
The sources are at the Core pin (SOURCES.md):

- `CheckAuxPowProofOfWork`, `src/dogecoin.cpp` lines 89 to 125 (D6).
- `CheckBlockHeader`, `src/validation.cpp` lines 2927 to 2937 (D33).
- `CPureBlockHeader::GetPoWHash`, `src/primitives/pureheader.cpp` lines 25 to 30 (D40).
- The AuxPoW fields of `Consensus::Params`, `src/consensus/params.h` lines 79 to 88 (D15), and the network records in `src/chainparams.cpp` (D14).

`checkAuxPowProofOfWork` takes its parameter record explicitly, so it claims nothing about which record a caller supplies.
`checkBlockHeader` supplies the height-zero record of a network, as Core does.
The theorems, including the agreement of every selected record with the height-zero record, are in `DogeLib.Block.Proofs.ProofOfWork`.

The module does not cover the contextual checks of `ContextualCheckBlockHeader`, except through the separate `checkVersion`.
It makes no cryptographic claim.

## Source

The adaptation follows Core's statements in order, with a named error for each `return error(...)`.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notices from `src/dogecoin.cpp` and `src/validation.cpp`:

Copyright (c) 2015-2022 The Dogecoin Core developers
Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/--
Core's `GetPoWHash` (D40, lines 25 to 30): the scrypt digest of the 80 encoded header bytes, in the internal order of `uint256`.
The encoding always has 80 bytes, so the zero hash of the second branch is never returned (`PureBlockHeader.powHash_eq`).
-/
def PureBlockHeader.powHash (h : PureBlockHeader) : Hash256 :=
  match Bytes.ofListExact? (n := 80) (Codec.encode h) with
  | some b => Cryptography.Hash.Scrypt.scrypt_1024_1_1_256 b
  | none => Hash256.zero

/--
The fields of Core's `Consensus::Params` (D15) that `CheckAuxPowProofOfWork` reads (D6, lines 89 to 125).
`Work.checkProofOfWork` reads only `powLimit` of the `RetargetParams` part.
The other `RetargetParams` fields come from the same Core record and do not affect the check.
-/
structure AuxPowParams extends Work.RetargetParams where
  /-- `nAuxpowChainId`: the chain ID that a header must carry (D15, line 80). -/
  auxpowChainId : Int32
  /-- `fStrictChainId`: whether the chain ID tests of `CheckAuxPowProofOfWork` and `CAuxPow::check` apply (D15, line 81). -/
  strictChainId : Bool

/-- Mainnet before height 145000, `consensus` (D14, lines 88 to 123). -/
def mainnetAuxPowParams : AuxPowParams := ⟨Work.mainnetParams, 0x62, true⟩

/-- Mainnet from height 145000, `digishieldConsensus` and `auxpowConsensus` (D14, lines 125 to 136).
Both are copies of `consensus` with changes to fields that this record omits, apart from the retarget fields. -/
def mainnetDigishieldAuxPowParams : AuxPowParams := ⟨Work.mainnetDigishieldParams, 0x62, true⟩

/-- Testnet before height 145000, `consensus` (D14, lines 233 to 279). -/
def testnetAuxPowParams : AuxPowParams := ⟨Work.mainnetParams, 0x62, false⟩

/-- Testnet from height 145000: `digishieldConsensus`, `minDifficultyConsensus` and `auxpowConsensus` (D14, lines 282 to 300).
Each is a copy of the previous record with changes to fields that this record omits, apart from the retarget fields. -/
def testnetDigishieldAuxPowParams : AuxPowParams := ⟨Work.mainnetDigishieldParams, 0x62, false⟩

/-- Regtest before height 10, `consensus` (D14, lines 392 to 419). -/
def regtestAuxPowParams : AuxPowParams := ⟨Work.regtestWorkParams.toRetargetParams, 0x62, true⟩

/-- Regtest from height 10, `digishieldConsensus` and `auxpowConsensus` (D14, lines 425 to 432). -/
def regtestDigishieldAuxPowParams : AuxPowParams := ⟨Work.regtestDigishieldWorkParams.toRetargetParams, 0x62, true⟩

/-- A consensus record and its search links (D15, lines 84 to 88), for any projection `α` of the record. -/
inductive ParamsTree (α : Type) where
  | node (nHeightEffective : UInt32) (params : α) (pLeft pRight : Option (ParamsTree α))

/-- The record selected by Core's `GetConsensus` (D14, lines 494 to 506), with its effective height.
The search is the one of `Work.ConsensusTree.getConsensus`, and `getAuxPowParams_eq_work` proves that the two agree. -/
def ParamsTree.getConsensus {α : Type} : ParamsTree α → UInt32 → UInt32 × α
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

/-- The AuxPoW projection of each network's tree, with Core's links (D14, lines 138 to 141, 302 to 306 and 434 to 437).
The effective heights and links are those of `Work.consensusTree`. -/
def auxPowTree : Work.WorkNetwork → ParamsTree AuxPowParams
  | .mainnet => .node 145000 mainnetDigishieldAuxPowParams
      (some (.node 0 mainnetAuxPowParams none none))
      (some (.node 371337 mainnetDigishieldAuxPowParams none none))
  | .testnet => .node 145000 testnetDigishieldAuxPowParams
      (some (.node 0 testnetAuxPowParams none none))
      (some (.node 157500 testnetDigishieldAuxPowParams none
        (some (.node 158100 testnetDigishieldAuxPowParams none none))))
  | .regtest => .node 10 regtestDigishieldAuxPowParams
      (some (.node 0 regtestAuxPowParams none none))
      (some (.node 20 regtestDigishieldAuxPowParams none none))

/-- The AuxPoW fields of the record that `GetConsensus` selects for a height (D14, lines 494 to 506). -/
def getAuxPowParams (network : Work.WorkNetwork) (height : UInt32) : AuxPowParams :=
  ((auxPowTree network).getConsensus height).2

/-- The reason that `checkAuxPowProofOfWork` rejects a header: one constructor for each `return error(...)` of D6, in source order. -/
inductive CheckPowError where
  /-- The header is not legacy, `fStrictChainId` is set, and the chain ID is not `nAuxpowChainId` (line 96). -/
  | wrongChainId
  /-- No payload, but the AuxPoW flag is set (line 104). -/
  | auxpowFlagWithoutPayload
  /-- No payload, and the header's own scrypt digest does not satisfy its `nBits` (line 108). -/
  | proofOfWorkFailed
  /-- A payload, but the AuxPoW flag is clear (line 116). -/
  | payloadWithoutFlag
  /-- The parent's scrypt digest does not satisfy the `nBits` of this header (line 119). -/
  | auxProofOfWorkFailed
  /-- `CAuxPow::check` rejects the payload (line 122), for the reason in `e`. -/
  | auxPow (e : AuxPowCheckError)
  deriving DecidableEq, Repr

/--
Core's `CheckAuxPowProofOfWork` (D6, lines 89 to 125), with the first failing check as its error.
Core returns `true` exactly when the result is `.ok ()`.

1. Unless the header is legacy, with `fStrictChainId` its chain ID must equal `nAuxpowChainId`.
2. Without a payload, the AuxPoW flag must be clear, and the header's own scrypt digest must satisfy its `nBits`.
3. With a payload, the AuxPoW flag must be set.
4. The scrypt digest of the 80 parent bytes must satisfy the `nBits` of this header, not the parent's `nBits`.
5. `AuxPow.check` must accept, with this header's double SHA-256 hash and this header's own chain ID.
-/
def checkAuxPowProofOfWork (p : AuxPowParams) (h : BlockHeader) : Except CheckPowError Unit :=
  if !h.pure.isLegacy && p.strictChainId && h.pure.chainId != p.auxpowChainId then .error .wrongChainId
  else
    match h.auxpow with
    | none =>
      if h.pure.isAuxpow then .error .auxpowFlagWithoutPayload
      else if !Work.checkProofOfWork h.pure.powHash h.pure.nBits p.toRetargetParams then
        .error .proofOfWorkFailed
      else .ok ()
    | some a =>
      if !h.pure.isAuxpow then .error .payloadWithoutFlag
      else if !Work.checkProofOfWork a.parentBlock.powHash h.pure.nBits p.toRetargetParams then
        .error .auxProofOfWorkFailed
      else
        match a.check h.pure.getHash h.pure.chainId p.strictChainId with
        | .error e => .error (.auxPow e)
        | .ok () => .ok ()

/-- The reject reason that `CheckBlockHeader` reports for every proof-of-work failure (D33, line 2934). -/
def CheckPowError.rejectReason (_ : CheckPowError) : String := "high-hash"

/--
Core's `CheckBlockHeader` with `fCheckPOW` true (D33, lines 2927 to 2937): `checkAuxPowProofOfWork` on the height-zero record of the network.
Every selected record of a network gives the same result (`checkAuxPowProofOfWork_getAuxPowParams`).
-/
def checkBlockHeader (network : Work.WorkNetwork) (h : BlockHeader) : Except CheckPowError Unit :=
  checkAuxPowProofOfWork (getAuxPowParams network 0) h

end DogeLib.Block
