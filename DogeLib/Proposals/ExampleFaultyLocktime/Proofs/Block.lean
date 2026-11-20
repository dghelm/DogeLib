module

public import DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Compatibility
public import DogeLib.Proposals.Framework.Proofs.Block

/-!
# Proofs: `Proposals.ExampleFaultyLocktime`, block level

The example is an invented, deliberately faulty proposal, not a proposal for Dogecoin (`DogeLib.Proposals.ExampleFaultyLocktime`).
Every theorem here is block-level: it is about one block on a supplied coin set and chain view.
None is a claim about a chain or about the network.

The theorems are the targets of design record 0011, section 10.1, for `blockRevision`:

- `lockStep_eq_of_not_nop4`: on an instruction other than `OP_NOP4`, the step of each variant is the baseline step.
- `block_inactive`: for each variant, where the activation is inactive, `validateBlockWith` equals the embedded result of `validateBlock`.
- `corrected_block_restricts`: a block that `validateBlockWith` accepts with the corrected variant, `validateBlock` accepts, with the same coin set and the same changes. For every activation.
- `block_congr`: for each variant, on a block in which no spend holds `OP_NOP4` as an instruction, `validateBlockWith` equals the embedded result of `validateBlock`. For every activation.

The faulty variant has no restriction theorem. Its spend check accepts a spend that `verifyLegacySpend` rejects (`Proofs.Witnesses`).
Each theorem holds for every pair of embeddings, verifier, pair of flags, context and coin set.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleFaultyLocktime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

variable {ρ μ ρ' μ' : Type}

/-- For every variant, `active`, checker and flag set: on an instruction whose opcode is not `OP_NOP4`, `lockStep` is the baseline step. -/
theorem lockStep_eq_of_not_nop4 (v : Variant) (active : Bool) (checker : Option SignatureChecker) (flags : UInt32)
    (script : List UInt8) (s : ExecState) (i : Instruction) (hi : isNop4 i.opcode = false) :
    lockStep v active checker flags script s i = baselineStep id id checker flags script s i := by
  simp only [lockStep, baselineStep, hi, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases evalInstruction checker script flags s i <;> rfl

/-- For each variant: where the activation is inactive on mainnet at the height of the block, `validateBlockWith` equals the embedded result of `validateBlock`. -/
theorem block_inactive (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ρ μ)
    (v : Variant) (verify : SignatureVerifier) {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool)
    {ctx : ValidateContext} (hact : a.isActive .mainnet ctx.height = false) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision v verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E (rev := blockRevision v verify)
    ⟨fun ictx spk f => revisedSpend_inactive_eq v ⟨ictx, spk, f, verify⟩, fun _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => rfl⟩
    fCheckPOW fCheckMerkleRoot hact s b

/-- If `validateBlockWith` with the corrected variant accepts a block, `validateBlock` accepts it, with the same coin set and the same changes. For every activation. -/
theorem corrected_block_restricts {V : ValidateEmbedding ρ μ ρ' μ'} {E : ConnectEmbedding ScriptError Unsupported ρ μ}
    {verify : SignatureVerifier} {a : Activation} {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext}
    {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockWith V E (blockRevision .corrected verify) a fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r :=
  validateBlockWith_restricts (rev := blockRevision .corrected verify)
    (fun active height ictx spk hacc =>
      corrected_soft_fork_local (active := active) (a := ⟨ictx, spk, connectScriptFlags height, verify⟩) hacc)
    (fun _ _ => rfl) (fun _ _ _ _ => Int.le_refl _) h

/-- For each variant: on a block in which no spend holds `OP_NOP4` as an instruction (`BlockUntouched isNop4`), `validateBlockWith` equals the embedded result of `validateBlock`. For every activation. -/
theorem block_congr (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ρ μ)
    (v : Variant) {verify : SignatureVerifier} (a : Activation) (fCheckPOW fCheckMerkleRoot : Bool)
    {ctx : ValidateContext} {s : CoinSet} {b : Block} (hfree : BlockUntouched isNop4 verify ctx.height s b) :
    validateBlockWith V E (blockRevision v verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_congr V E (rev := blockRevision v verify) (O := isNop4)
    (step := fun ictx f => lockStep v (a.isActive .mainnet ctx.height)
      (some (transactionChecker ictx.tx ictx.index verify)) f)
    (fun _ _ _ => rfl)
    (fun _ f script st i hi => lockStep_eq_of_not_nop4 v _ _ f script st i hi)
    rfl (fun _ _ _ => rfl) fCheckPOW fCheckMerkleRoot rfl hfree

end DogeLib.Proposals.ExampleFaultyLocktime
