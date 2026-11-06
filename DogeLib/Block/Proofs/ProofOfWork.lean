module

public import DogeLib.Block.ProofOfWork
public import DogeLib.Block.Proofs.AuxPow
public import DogeLib.Block.Proofs.Header
public import DogeLib.Cryptography.Proofs.Hash.ScryptPow
public import DogeLib.Work.Proofs.Consensus

/-!
# Header proof-of-work properties

The theorems characterize `PureBlockHeader.powHash`, `checkAuxPowProofOfWork` and `checkBlockHeader` (design record 0004, stage 4a).
They state what the definitions compute, for every header and every parameter record.
They make no claim about Core beyond the source review of SOUNDNESS.md, and no cryptographic claim.
No theorem evaluates scrypt.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/-! ## The scrypt digest -/

/-- For every pure header, `powHash` is `scrypt_1024_1_1_256` of its 80 encoded bytes. -/
theorem PureBlockHeader.powHash_eq (h : PureBlockHeader) :
    h.powHash = Cryptography.Hash.Scrypt.scrypt_1024_1_1_256 ⟨Codec.encode h, h.encode_length⟩ := by
  simp [PureBlockHeader.powHash, Bytes.ofListExact?, h.encode_length]

/--
For every pure header, `powHash` equals the RFC 7914 scrypt model on the 80 encoded bytes.
The bytes are both password and salt, with N = 1024, r = 1, p = 1 and a 32-byte output.
-/
theorem PureBlockHeader.powHash_eq_spec (h : PureBlockHeader) :
    Cryptography.Hash.Scrypt.Spec.scrypt ((Codec.encode h).map UInt8.toBitVec)
        ((Codec.encode h).map UInt8.toBitVec) 1024 1 1 32 =
      some (h.powHash.val.map UInt8.toBitVec) := by
  rw [h.powHash_eq]
  exact Cryptography.Hash.Scrypt.powHash_eq_spec ⟨Codec.encode h, h.encode_length⟩

/-! ## The composition theorem -/

set_option linter.unusedSimpArgs false in
/--
For every parameter record and full header, `checkAuxPowProofOfWork` accepts exactly when two conditions hold.

- The chain ID condition: the header is legacy, or `strictChainId` is false, or its chain ID is `auxpowChainId`.
- One of two branches:
  - There is no payload, the AuxPoW flag is clear, and the header's own scrypt digest satisfies `Work.checkProofOfWork` with the header's `nBits`.
  - There is a payload, and the AuxPoW flag is set.
    The scrypt digest of the 80 parent bytes satisfies `Work.checkProofOfWork` with the `nBits` of this header, not of the parent.
    `AuxPow.check` also accepts the payload with this header's hash, its chain ID and `strictChainId`.

`Work.checkProofOfWork_iff` turns each proof-of-work condition into target validity and a digest at most the target.
-/
theorem checkAuxPowProofOfWork_iff (p : AuxPowParams) (h : BlockHeader) :
    (checkAuxPowProofOfWork p h).isOk = true ↔
      (h.pure.isLegacy = true ∨ p.strictChainId = false ∨ h.pure.chainId = p.auxpowChainId) ∧
      ((h.auxpow = none ∧ h.pure.isAuxpow = false ∧
          Work.checkProofOfWork h.pure.powHash h.pure.nBits p.toRetargetParams = true) ∨
        (∃ a, h.auxpow = some a ∧ h.pure.isAuxpow = true ∧
          Work.checkProofOfWork a.parentBlock.powHash h.pure.nBits p.toRetargetParams = true ∧
          a.check h.pure.getHash h.pure.chainId p.strictChainId = .ok ())) := by
  rcases h with ⟨pure, _ | a⟩
  · cases hl : pure.isLegacy <;> cases hs : p.strictChainId <;>
      by_cases hid : pure.chainId = p.auxpowChainId <;> cases hf : pure.isAuxpow <;>
      cases hw : Work.checkProofOfWork pure.powHash pure.nBits p.toRetargetParams <;>
      simp [checkAuxPowProofOfWork, hl, hs, hid, hf, hw, Except.isOk, Except.toBool]
  · simp only [checkAuxPowProofOfWork, Option.some.injEq, exists_eq_left', reduceCtorEq, false_and,
      false_or]
    generalize a.check pure.getHash pure.chainId p.strictChainId = r
    cases hl : pure.isLegacy <;> cases hs : p.strictChainId <;>
      by_cases hid : pure.chainId = p.auxpowChainId <;> cases hf : pure.isAuxpow <;>
      cases hw : Work.checkProofOfWork a.parentBlock.powHash pure.nBits p.toRetargetParams <;>
      rcases r with e | ⟨⟩ <;>
      simp [hl, hs, hid, hf, hw, Except.isOk, Except.toBool]

/--
For every parameter record, read mode and input, a header that `BlockHeader.read` returns never reaches the two mismatch rejections (design record 0004, item 12).
The result is neither `auxpowFlagWithoutPayload` nor `payloadWithoutFlag`.
-/
theorem checkAuxPowProofOfWork_read (p : AuxPowParams) (mode : TxReadMode) (bs : List UInt8)
    (h : BlockHeader) (rest : List UInt8) (hr : BlockHeader.read mode bs = .ok (h, rest)) :
    checkAuxPowProofOfWork p h ≠ .error .auxpowFlagWithoutPayload ∧
      checkAuxPowProofOfWork p h ≠ .error .payloadWithoutFlag := by
  have hs := BlockHeader.read_auxpow_isSome mode bs h rest hr
  rcases h with ⟨pure, _ | a⟩ <;> simp only [Option.isSome_none, Option.isSome_some] at hs <;>
    simp only [checkAuxPowProofOfWork, ← hs] <;> constructor <;> intro he <;>
    (repeat' split at he) <;> simp_all

/-! ## Record independence -/

/--
For every two parameter records with the same `auxpowChainId`, `strictChainId` and `powLimit`, and every full header, `checkAuxPowProofOfWork` gives the same result.
The other retarget fields are never read.
-/
theorem checkAuxPowProofOfWork_congr (p q : AuxPowParams) (h : BlockHeader)
    (hid : p.auxpowChainId = q.auxpowChainId) (hs : p.strictChainId = q.strictChainId)
    (hl : p.powLimit = q.powLimit) :
    checkAuxPowProofOfWork p h = checkAuxPowProofOfWork q h := by
  have hw : ∀ hash nBits, Work.checkProofOfWork hash nBits p.toRetargetParams =
      Work.checkProofOfWork hash nBits q.toRetargetParams := by
    intro hash nBits
    simp [Work.checkProofOfWork, Work.validProofOfWorkTarget, hl]
  simp only [checkAuxPowProofOfWork, hid, hs, hw]

/-- At every UInt32 height, the mainnet search selects the pre-DigiShield record below 145000 and the DigiShield record from 145000. -/
theorem getAuxPowParams_mainnet (height : UInt32) :
    getAuxPowParams .mainnet height =
      if height < 145000 then mainnetAuxPowParams else mainnetDigishieldAuxPowParams := by
  simp only [getAuxPowParams, auxPowTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-- At every UInt32 height, the testnet search selects the pre-DigiShield record below 145000 and the DigiShield record from 145000. -/
theorem getAuxPowParams_testnet (height : UInt32) :
    getAuxPowParams .testnet height =
      if height < 145000 then testnetAuxPowParams else testnetDigishieldAuxPowParams := by
  simp only [getAuxPowParams, auxPowTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-- At every UInt32 height, the regtest search selects the pre-DigiShield record below 10 and the DigiShield record from 10. -/
theorem getAuxPowParams_regtest (height : UInt32) :
    getAuxPowParams .regtest height =
      if height < 10 then regtestAuxPowParams else regtestDigishieldAuxPowParams := by
  simp only [getAuxPowParams, auxPowTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/--
For every network, height and full header, `checkAuxPowProofOfWork` on the record that `GetConsensus` selects for the height equals the result on the height-zero record.
So `CheckBlockHeader` and the disk reads, which select different records, agree on every header.
-/
theorem checkAuxPowProofOfWork_getAuxPowParams (network : Work.WorkNetwork) (height : UInt32)
    (h : BlockHeader) :
    checkAuxPowProofOfWork (getAuxPowParams network height) h =
      checkAuxPowProofOfWork (getAuxPowParams network 0) h := by
  apply checkAuxPowProofOfWork_congr
  all_goals
    cases network <;>
    simp only [getAuxPowParams_mainnet, getAuxPowParams_testnet, getAuxPowParams_regtest] <;>
    split <;> rfl

/-- For every network, height and full header, `checkBlockHeader` equals `checkAuxPowProofOfWork` on the record selected for the height. -/
theorem checkBlockHeader_eq (network : Work.WorkNetwork) (height : UInt32) (h : BlockHeader) :
    checkBlockHeader network h = checkAuxPowProofOfWork (getAuxPowParams network height) h :=
  (checkAuxPowProofOfWork_getAuxPowParams network height h).symm

/-! ## Agreement with the work projection -/

/--
For every network and height, the AuxPoW search and `Work.ConsensusTree.getConsensus` select a record with the same effective height.
The two records also have the same retarget fields.
So the AuxPoW projection selects the same Core record as the work projection.
-/
theorem getAuxPowParams_eq_work (network : Work.WorkNetwork) (height : UInt32) :
    ((auxPowTree network).getConsensus height).1 = ((Work.consensusTree network).getConsensus height).1 ∧
      (getAuxPowParams network height).toRetargetParams = (Work.getConsensus network height).toRetargetParams := by
  cases network <;>
    simp only [getAuxPowParams, Work.getConsensus, auxPowTree, Work.consensusTree, ParamsTree.getConsensus,
      Work.ConsensusTree.getConsensus] <;>
    repeat (any_goals (first | exact ⟨rfl, rfl⟩ | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

end DogeLib.Block
