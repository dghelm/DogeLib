module

public import DogeLib.Block.Proofs.ContextualCheck
public import DogeLib.Proposals.Framework.Proofs.Block
public import DogeLib.Proposals.Framework.Proofs.Compatibility
public import DogeLib.Proposals.RelativeLockTime

/-!
# Proofs: `Proposals.RelativeLockTime`, the lock-time cutoff

The theorems of design record 0012 for the rule of BIP 113, the one rule that `blockRevision` has.
The revision is partial: it has no rule of BIP 112 or BIP 68 (`DogeLib.Proposals.RelativeLockTime`).
No theorem here is a claim about the three rules together.

Each block-level theorem is about `validateBlock` for one block on a supplied coin set and view.
None is a claim about a chain or about the network.
Every theorem holds for every signature verifier, and none assumes a property of the verifier.

## Rule level

`DogeLib.Proposals.Framework.Proofs.LockTime` has `isFinalTx_mono` and `contextualCheckBlockBody_csv_restricts`, the two rule-level targets of design record 0012, section 9.2, for this rule.

- `medianTimePast_of_headerPassed`: on an applicable block whose contextual header check passes, the view has a median time past, and it is below the time of the block.
- `lockTimeArgs_of_headerPassed`: the revision then passes `csvActive` true and that median.
- `lockTimeCutoff_le`: the cutoff of the revision is then at most the time of the block.

## Block level

- `relativeLockTime_inactive_eq`: with `active` false, the revision equals the embedded result of `validateBlock`, for every context.
- `relativeLockTime_activation`, `_of_lt`, `_of_none`: where an activation is inactive at the height of the block, `validateBlockWith` with the revision equals the embedded result of `validateBlock`.
- `relativeLockTime_restricts`: a block that the revision accepts, `validateBlock` accepts, with the same coin set and the same changes. For every `active` and every context.
- `relativeLockTime_eq_of_cutoff_untouched`: on a block without a cutoff transaction, the revision equals the embedded result of `validateBlock`.

`DogeLib.Proposals.RelativeLockTime.Proofs.Witnesses` has the two witnesses and the `SoftFork` statement for this rule.

## Hypotheses and where Core enforces them

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The median time past of the predecessor is below the time of the block. | `lockTimeCutoff_le` | `ContextualCheckBlockHeader`, with the reason `time-too-old` (SOURCES.md, D33, line 3104). `validateBlock` runs it first, so `relativeLockTime_restricts` does not assume it. |
| The block is applicable. | The revised rule | It is part of the definition, and no theorem assumes it. Core reads the median only with a predecessor (D110, line 3135). |
| `csvActive` of the context is false. | `relativeLockTime_eq_of_cutoff_untouched` | The field is the version-bits state of the pin, which is never active on a mainnet chain whose headers passed the header checks (`csv_never_lockedIn`). |

`relativeLockTime_restricts` needs no hypothesis on `csvActive`.
With that field true, `connectBlockWith` returns the result `csvActive` for every block but one with the genesis hash, and such a block is not applicable.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

variable {ρ μ ρ' μ' : Type}

/-! ## The lock-time arguments -/

/-- With `active` false, the lock-time arguments of the revision are those of the baseline. -/
theorem lockTimeArgs_inactive (ctx : ValidateContext) (b : Block) :
    lockTimeArgs false ctx b = baselineLockTimeArgs ctx := by
  simp [lockTimeArgs]

/-- On a block that is not applicable, the lock-time arguments of the revision are those of the baseline, for every `active`. -/
theorem lockTimeArgs_of_not_applicable {active : Bool} {ctx : ValidateContext} {b : Block}
    (h : applicable ctx b = false) : lockTimeArgs active ctx b = baselineLockTimeArgs ctx := by
  simp [lockTimeArgs, h]

/-- A block whose header has the hash of the mainnet genesis block is not applicable. -/
theorem not_applicable_of_genesis {ctx : ValidateContext} {b : Block}
    (h : (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true) : applicable ctx b = false := by
  unfold applicable
  rw [h]
  simp

/--
On an applicable block whose contextual header check passes (`contextualHeaderPassed`):
`Work.medianTimePast` of the view succeeds, and the median is below the time of the block.
The second part is check 5 of `contextualCheckBlockHeader`, Core's `time-too-old`.
-/
theorem medianTimePast_of_headerPassed {ctx : ValidateContext} {b : Block} (happ : applicable ctx b = true)
    (hpass : contextualHeaderPassed ctx b) :
    ∃ median, medianTimePast ctx.view = .ok median ∧ median < (b.header.pure.nTime.toNat : Int) := by
  unfold applicable at happ
  unfold contextualHeaderPassed at hpass
  generalize (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = g at happ hpass
  cases g with
  | true => simp at happ
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hpass
    rcases hview : ctx.view with _ | ⟨prev, rest⟩
    · simp [hview] at happ
    · rw [hview] at hpass
      obtain ⟨median, _, hmed, _, _, _, _, _, _, hlt, _⟩ := (contextualCheck_eq_ok_iff _ _ _ _ _ _).mp hpass
      exact ⟨median, hmed, hlt⟩

/--
Take an applicable block whose contextual header check passes.
The active revision passes `csvActive` true and the median time past of the view, which is below the time of the block.
-/
theorem lockTimeArgs_of_headerPassed {ctx : ValidateContext} {b : Block} (happ : applicable ctx b = true)
    (hpass : contextualHeaderPassed ctx b) :
    ∃ median, medianTimePast ctx.view = .ok median ∧ lockTimeArgs true ctx b = (true, median) ∧
      median < (b.header.pure.nTime.toNat : Int) := by
  obtain ⟨median, hmed, hlt⟩ := medianTimePast_of_headerPassed happ hpass
  exact ⟨median, hmed, by simp [lockTimeArgs, happ, hmed], hlt⟩

/--
Condition 4 of design record 0012, section 6.4, for this revision.
Take a context with `csvActive` false, and a block whose contextual header check passes.
Then the lock-time cutoff of the revision is at most the cutoff of the baseline, which is the time of the block.
For every `active`, on an applicable block or not.
-/
theorem lockTimeCutoff_le {active : Bool} {ctx : ValidateContext} {b : Block} (hcsv : ctx.csvActive = false)
    (hpass : contextualHeaderPassed ctx b) :
    lockTimeCutoff (lockTimeArgs active ctx b) b ≤ lockTimeCutoff (baselineLockTimeArgs ctx) b := by
  cases active with
  | false => rw [lockTimeArgs_inactive]; exact Int.le_refl _
  | true =>
    cases happ : applicable ctx b with
    | false => rw [lockTimeArgs_of_not_applicable happ]; exact Int.le_refl _
    | true =>
      obtain ⟨median, _, hargs, hlt⟩ := lockTimeArgs_of_headerPassed happ hpass
      rw [hargs]
      simp only [lockTimeCutoff, baselineLockTimeArgs, hcsv, ↓reduceIte, Bool.false_eq_true]
      omega

/-! ## Inactive equality -/

/-- The revision has the inactive equality of the block layer: with `active` false, each of its parts has its baseline value. -/
theorem blockRevision_inactiveBaseline (verify : SignatureVerifier) :
    (blockRevision verify : BlockRevision ScriptError Unsupported ρ μ).InactiveBaseline id id verify :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, lockTimeArgs_inactive⟩

/--
The target `relativeLockTime_inactive_eq` of design record 0012, section 9.3, for the revision with the rule of BIP 113.
With `active` false, `validateBlockWithActive` with the revision equals the embedded result of `validateBlock`.
The equality covers every acceptance, each rejection and each result outside the model.
For every pair of embeddings, verifier, pair of flags, context, coin set and block.
-/
theorem relativeLockTime_inactive_eq (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ρ μ)
    (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (s : CoinSet)
    (b : Block) :
    validateBlockWithActive V E (blockRevision verify) false fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWithActive_inactive V E (blockRevision_inactiveBaseline verify) fCheckPOW fCheckMerkleRoot ctx s b

/--
The target `relativeLockTime_activation` of design record 0012, section 9.3, for the revision with the rule of BIP 113.
Where the activation is inactive on mainnet at the height of the block, `validateBlockWith` with the revision equals the embedded result of `validateBlock`.
For every activation, pair of embeddings, verifier, pair of flags, context, coin set and block.
-/
theorem relativeLockTime_activation (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ρ μ)
    (verify : SignatureVerifier) {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext}
    (hact : a.isActive .mainnet ctx.height = false) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E (blockRevision_inactiveBaseline verify) fCheckPOW fCheckMerkleRoot hact s b

/-- `relativeLockTime_activation` for a block below the activation height `h₀` of mainnet. -/
theorem relativeLockTime_activation_of_lt (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ρ μ) (verify : SignatureVerifier) {a : Activation}
    (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} {h₀ : Nat} (hheight : a.height .mainnet = some h₀)
    (hlt : ctx.height < h₀) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  relativeLockTime_activation V E verify fCheckPOW fCheckMerkleRoot (Activation.isActive_lt hheight hlt) s b

/-- `relativeLockTime_activation` for an activation with no activation height on mainnet, at every height. -/
theorem relativeLockTime_activation_of_none (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ρ μ) (verify : SignatureVerifier) {a : Activation}
    (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (hnone : a.height .mainnet = none) (s : CoinSet)
    (b : Block) :
    validateBlockWith V E (blockRevision verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  relativeLockTime_activation V E verify fCheckPOW fCheckMerkleRoot (Activation.none_inactive hnone ctx.height) s b

/-! ## Restriction -/

/-- If the embedded result of `verifyLegacySpend` is an acceptance, `verifyLegacySpend` accepts. -/
theorem accepted_of_ofBaseline_accepted {r : VerifyResult}
    (h : VerifyOutcome.ofBaseline (ε := ScriptError) (υ := Unsupported) id id r = .accepted) : r = .accepted := by
  cases r <;> simp_all [VerifyOutcome.ofBaseline]

/--
The target `relativeLockTime_restricts` of design record 0012, section 9.3, for the revision with the rule of BIP 113.
If `validateBlockWithActive` with the revision accepts a block, `validateBlock` accepts it, with the same coin set and the same changes.
For every `active`, pair of embeddings, verifier, pair of flags, context and coin set, on an applicable block or not.
The statement has no hypothesis on the times: `validateBlockWithActive` runs the contextual header check before the body check.
-/
theorem relativeLockTime_restricts {V : ValidateEmbedding ρ μ ρ' μ'} {E : ConnectEmbedding ScriptError Unsupported ρ μ}
    {verify : SignatureVerifier} {active fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet}
    {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E (blockRevision verify) active fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r := by
  refine validateBlockWithActive_restricts (rev := blockRevision verify)
    (fun ictx spk hacc => accepted_of_ofBaseline_accepted hacc) rfl (fun hpass => ?_) h
  cases hcsv : ctx.csvActive with
  | false => exact lockTimeCutoff_le hcsv hpass
  | true =>
    have hg := connectBlockWith_ok_genesis_of_csvActive (validateBlockWithActive_ok_connect h) hcsv
    have hargs : (blockRevision (ρ := ρ) (μ := μ) verify).lockTimeArgs active ctx b = baselineLockTimeArgs ctx :=
      lockTimeArgs_of_not_applicable (not_applicable_of_genesis hg)
    rw [hargs]
    exact Int.le_refl _

/-! ## Blocks that the rule does not touch -/

/--
The part of `relativeLockTime_eq_of_untouched` of design record 0012, section 9.3, for the rule of BIP 113.
Take a context with `csvActive` false.
Let the block have no cutoff transaction (`CutoffUntouched`), when the view has a median time past `median`.
A cutoff transaction has a time lock time from `median` to below the time of the block, and an input whose sequence is not `SEQUENCE_FINAL`.
Then `validateBlockWithActive` with the revision equals the embedded result of `validateBlock`, for every `active`.
So a block whose two verdicts differ has a cutoff transaction.
For every pair of embeddings, verifier, pair of flags and coin set.
-/
theorem relativeLockTime_eq_of_cutoff_untouched (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ρ μ) (verify : SignatureVerifier)
    (active fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} (s : CoinSet) {b : Block}
    (hcsv : ctx.csvActive = false)
    (hfree : ∀ median, medianTimePast ctx.view = .ok median →
      CutoffUntouched median (b.header.pure.nTime.toNat : Int) b.transactions) :
    validateBlockWithActive V E (blockRevision verify) active fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  rw [← validateBlockWithActive_ofBaseline V E id id verify active]
  apply validateBlockWithActive_congr
  · intro hpass
    simp only [contextualBodyWith, blockRevision, BlockRevision.baseline]
    cases active with
    | false => rw [lockTimeArgs_inactive]
    | true =>
      cases happ : applicable ctx b with
      | false => rw [lockTimeArgs_of_not_applicable happ]
      | true =>
        obtain ⟨median, hmed, hargs, hlt⟩ := lockTimeArgs_of_headerPassed happ hpass
        rw [hargs]
        apply contextualCheckBlockBody_eq_of_untouched (args := (true, median)) (args' := baselineLockTimeArgs ctx)
        · simp only [lockTimeCutoff, baselineLockTimeArgs, hcsv, ↓reduceIte, Bool.false_eq_true]
          omega
        · simpa only [lockTimeCutoff, baselineLockTimeArgs, hcsv, ↓reduceIte, Bool.false_eq_true] using
            hfree median hmed
  · exact connectBlockWith_congr_revision E true (fun _ _ _ _ _ _ _ _ _ => rfl) rfl (fun _ _ _ _ _ _ => rfl)

end DogeLib.Proposals.RelativeLockTime
