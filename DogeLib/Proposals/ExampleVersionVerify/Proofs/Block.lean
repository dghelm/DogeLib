module

public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Compatibility
public import DogeLib.Proposals.Framework.Proofs.Block

/-!
# Proofs: `Proposals.ExampleVersionVerify`, block level

The example is not a proposal for Dogecoin (`DogeLib.Proposals.ExampleVersionVerify`).
Every theorem here is block-level: it is about one block on a supplied coin set and chain view.
None is a claim about a chain or about the network.

The theorems are the targets of design record 0011, section 10.1, for `blockRevision`:

- `example_block_inactive`: where the activation is inactive, `validateBlockWith` equals the embedded result of `validateBlock`.
- `example_block_restricts`: a block that `validateBlockWith` accepts, `validateBlock` accepts, with the same coin set and the same changes. For every activation.
- `example_block_congr`: on a block in which no spend holds `OP_NOP10` as an instruction, `validateBlockWith` equals the embedded result of `validateBlock`. For every activation.

Each holds for every pair of embeddings, verifier, pair of flags, context and coin set.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleVersionVerify

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

variable {ρ μ ρ' μ' : Type}

/-- Where the activation is inactive on mainnet at the height of the block, `validateBlockWith` with the example equals the embedded result of `validateBlock`. -/
theorem example_block_inactive (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ExampleScriptError ExampleScriptUnsupported ρ μ) (verify : SignatureVerifier)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext}
    (hact : a.isActive .mainnet ctx.height = false) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E Sum.inl Sum.inl (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E (rev := blockRevision verify)
    ⟨fun ictx spk f => example_spend_inactive_eq ictx spk f verify, fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    fCheckPOW fCheckMerkleRoot hact s b

/-- If `validateBlockWith` with the example accepts a block, `validateBlock` accepts it, with the same coin set and the same changes. For every activation. -/
theorem example_block_restricts {V : ValidateEmbedding ρ μ ρ' μ'}
    {E : ConnectEmbedding ExampleScriptError ExampleScriptUnsupported ρ μ} {verify : SignatureVerifier}
    {a : Activation} {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block}
    {r : ConnectResult}
    (h : validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r :=
  validateBlockWith_restricts (rev := blockRevision verify) (fun _ _ _ _ hacc => example_soft_fork_local hacc)
    (fun _ _ => rfl) (fun _ _ _ _ => Int.le_refl _) h

/-- On a block in which no spend holds `OP_NOP10` as an instruction (`BlockUntouched isNop10`), `validateBlockWith` with the example equals the embedded result of `validateBlock`. For every activation. -/
theorem example_block_congr (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ExampleScriptError ExampleScriptUnsupported ρ μ) {verify : SignatureVerifier}
    (a : Activation) (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} {s : CoinSet} {b : Block}
    (hfree : BlockUntouched isNop10 verify ctx.height s b) :
    validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E Sum.inl Sum.inl (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_congr V E (rev := blockRevision verify) (O := isNop10)
    (step := fun ictx f => exampleStep (a.isActive .mainnet ctx.height) (some (.ofInput ictx))
      (some (transactionChecker ictx.tx ictx.index verify)) f)
    (fun _ _ _ => rfl)
    (fun _ f script st i hi => exampleStep_eq_of_not_nop10 _ _ _ f script st i hi)
    rfl (fun _ _ _ => rfl) fCheckPOW fCheckMerkleRoot rfl hfree

end DogeLib.Proposals.ExampleVersionVerify
