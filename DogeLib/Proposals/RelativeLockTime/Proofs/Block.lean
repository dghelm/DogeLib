module

public import DogeLib.Block.Proofs.ContextualCheck
public import DogeLib.Proposals.Framework.Proofs.Block
public import DogeLib.Proposals.Framework.Proofs.Compatibility
public import DogeLib.Proposals.RelativeLockTime.Proofs.CheckSequence
public import DogeLib.Proposals.RelativeLockTime.Proofs.SequenceLocks

/-!
# Proofs: `Proposals.RelativeLockTime` at the block level

Block-level theorems of design record 0012 for the three rules of `blockRevision`: the lock-time cutoff of BIP 113, the script flag of BIP 112 and the sequence locks of BIP 68.
`DogeLib.Proposals.RelativeLockTime.Proofs.SoftFork` has the theorems that join the rules: the soft fork, the list of blocks and the enforced lock.

Each block-level theorem here is about `validateBlock` for one block on a supplied coin set and view.
None is a claim about the network.
Every theorem holds for every signature verifier, and none assumes a property of the verifier.

## Rule level

`DogeLib.Proposals.Framework.Proofs.LockTime` has `isFinalTx_mono` and `contextualCheckBlockBody_csv_restricts`, the two rule-level targets of design record 0012, section 9.2, for the cutoff.
`DogeLib.Proposals.RelativeLockTime.Proofs.CheckSequence` has the Script-local targets for the flag.

- `medianTimePast_of_headerPassed`: on an applicable block whose contextual header check passes, the view has a median time past, and it is below the time of the block.
- `lockTimeArgs_of_headerPassed`: the revision then passes `csvActive` true and that median.
- `lockTimeCutoff_le`: the cutoff of the revision is then at most the time of the block.
- `scriptFlags_inactive`, `scriptFlags_p2sh`: the script flags of the revision are `connectScriptFlags` with `active` false, and agree with them on `SCRIPT_VERIFY_P2SH` for every `active`.
- `spend_restricts`: an input that `verifyLegacySpend` accepts under the script flags of the revision, it accepts under `connectScriptFlags`.
- `checkInputScriptWith_withCsvFlag`: on an input whose spend check does not read the CSV flag, both runs of the script check give one outcome with the flag and without it.
- `txTest_inactive`, `txTest_eq_ok_iff`, `txTest_of_sequence_untouched`: the transaction test of the revision accepts with `active` false or a version below 2, accepts exactly when `sequenceLocks` accepts, and accepts a transaction that is not an object of the rule of BIP 68.

## Block level

- `relativeLockTime_inactive_eq`: with `active` false, the revision equals the embedded result of `validateBlock`, for every context.
- `relativeLockTime_activation`, `_of_lt`, `_of_none`: where an activation is inactive at the height of the block, `validateBlockWith` with the revision equals the embedded result of `validateBlock`.
- `relativeLockTime_restricts`: a block that the revision accepts, `validateBlock` accepts, with the same coin set and the same changes. For every `active` and every context. The statement covers the three rules.
- `relativeLockTime_eq_of_not_applicable`: on a block that is not applicable, the revision equals the embedded result of `validateBlock`, for every `active`.
- `contextualBody_eq_of_cutoff_untouched`: on a block with no cutoff transaction, the body check of the revision equals that of the baseline.
- `relativeLockTime_eq_of_untouched`: on a block with no cutoff transaction, no transaction that is an object of the rule of BIP 68 (`SequenceUntouched`) and no instruction `0xb2` in a script of a spend, the revision equals the embedded result of `validateBlock`.

## Hypotheses and where Core enforces them

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The median time past of the predecessor is below the time of the block. | `lockTimeCutoff_le` | `ContextualCheckBlockHeader`, with the reason `time-too-old` (SOURCES.md, D33, line 3104). `validateBlock` runs it first, so `relativeLockTime_restricts` does not assume it. |
| The block is applicable. | The revised cutoff | It is part of the definition, and no theorem of this module assumes it. Core reads the median only with a predecessor (D110, line 3135). |
| `csvActive` of the context is false. | `relativeLockTime_eq_of_untouched` | The field is the version-bits state of the pin, which is never active on a mainnet chain whose headers passed the header checks (`csv_never_lockedIn`). |

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

/-! ## The script flags -/

/-- With `active` false, the script flags of the revision are `connectScriptFlags`, at every height. -/
theorem scriptFlags_inactive (height : Nat) : scriptFlags false height = connectScriptFlags height := rfl

/-- With `active` true, the script flags of the revision are `connectScriptFlags` with the CSV flag, at every height. -/
theorem scriptFlags_active (height : Nat) : scriptFlags true height = withCsvFlag (connectScriptFlags height) := rfl

/--
Condition 2 of design record 0012, section 6.4, for this revision.
The script flags of the revision and `connectScriptFlags` agree on `SCRIPT_VERIFY_P2SH`, for every `active` and height.
-/
theorem scriptFlags_p2sh (active : Bool) (height : Nat) :
    hasFlag (scriptFlags active height) ScriptFlags.p2sh = hasFlag (connectScriptFlags height) ScriptFlags.p2sh := by
  cases active with
  | false => rfl
  | true => exact hasFlag_withCsvFlag _ (by decide)

/-- If the embedded result of `verifyLegacySpend` is an acceptance, `verifyLegacySpend` accepts. -/
theorem accepted_of_ofBaseline_accepted {r : VerifyResult}
    (h : VerifyOutcome.ofBaseline (ε := ScriptError) (υ := Unsupported) id id r = .accepted) : r = .accepted := by
  cases r <;> simp_all [VerifyOutcome.ofBaseline]

/--
Condition 1 of design record 0012, section 6.4, for this revision.
If the spend check of the revision accepts an input under the script flags of the revision, `verifyLegacySpend` accepts it under `connectScriptFlags`.
For every verifier, `active`, height, input and previous `scriptPubKey`. With `active` true it is `csvFlag_soft_fork_local`.
-/
theorem spend_restricts {verify : SignatureVerifier} {active : Bool} {height : Nat} {ictx : InputContext}
    {spk : Transaction.Script}
    (h : baselineSpendCheck (ε := ScriptError) (υ := Unsupported) id id verify ictx spk (scriptFlags active height) =
      .accepted) :
    verifyLegacySpend ictx spk (connectScriptFlags height) verify = .accepted := by
  have h' := accepted_of_ofBaseline_accepted h
  cases active with
  | false => exact h'
  | true => exact csvFlag_soft_fork_local h'

/-! ## The transaction test -/

/-- With `active` false, or with a version below 2 as an unsigned value, the transaction test of the revision accepts. For every view, height, index and list of coins. -/
theorem txTest_inactive {active : Bool} {tx : Transaction} (h : active = false ∨ tx.version.toNat < 2)
    (view : List BlockIndex) (height index : Nat) (coins : List Coin) :
    txTest active view height index tx coins = .ok () := by
  simp only [txTest, sequenceLocks_inactive h, BlockOutcome.map]

/-- The transaction test of the revision accepts exactly when `sequenceLocks` accepts. -/
theorem txTest_eq_ok_iff {active : Bool} {view : List BlockIndex} {height index : Nat} {tx : Transaction}
    {coins : List Coin} :
    txTest active view height index tx coins = .ok () ↔ sequenceLocks active view height index tx coins = .ok () := by
  unfold txTest
  cases sequenceLocks active view height index tx coins <;> simp [BlockOutcome.map]

/-! ## Inactive equality -/

/-- The revision has the inactive equality of the block layer: with `active` false, each of its parts has its baseline value. -/
theorem blockRevision_inactiveBaseline (verify : SignatureVerifier) (view : List BlockIndex) :
    (blockRevision verify view).InactiveBaseline id id verify :=
  ⟨fun _ _ _ => rfl, scriptFlags_inactive, fun height index tx coins => txTest_inactive (tx := tx) (.inl rfl) view height index coins,
    lockTimeArgs_inactive⟩

/--
The target `relativeLockTime_inactive_eq` of design record 0012, section 9.3, for the revision with the rules of BIP 113 and BIP 112.
With `active` false, `validateBlockWithActive` with the revision equals the embedded result of `validateBlock`.
The equality covers every acceptance, each rejection and each result outside the model.
For every pair of embeddings, verifier, pair of flags, context, coin set and block.
-/
theorem relativeLockTime_inactive_eq (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason)
    (verify : SignatureVerifier) (view : List BlockIndex) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) :
    validateBlockWithActive V E (blockRevision verify view) false fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWithActive_inactive V E (blockRevision_inactiveBaseline verify view) fCheckPOW fCheckMerkleRoot ctx s b

/--
The target `relativeLockTime_activation` of design record 0012, section 9.3, for the revision with the rules of BIP 113 and BIP 112.
Where the activation is inactive on mainnet at the height of the block, `validateBlockWith` with the revision equals the embedded result of `validateBlock`.
For every activation, pair of embeddings, verifier, pair of flags, context, coin set and block.
-/
theorem relativeLockTime_activation (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ') (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason)
    (verify : SignatureVerifier) (view : List BlockIndex) {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool)
    {ctx : ValidateContext} (hact : a.isActive .mainnet ctx.height = false) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify view) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E (blockRevision_inactiveBaseline verify view) fCheckPOW fCheckMerkleRoot hact s b

/-- `relativeLockTime_activation` for a block below the activation height `h₀` of mainnet. -/
theorem relativeLockTime_activation_of_lt (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason) (verify : SignatureVerifier) (view : List BlockIndex)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} {h₀ : Nat}
    (hheight : a.height .mainnet = some h₀) (hlt : ctx.height < h₀) (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify view) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  relativeLockTime_activation V E verify view fCheckPOW fCheckMerkleRoot (Activation.isActive_lt hheight hlt) s b

/-- `relativeLockTime_activation` for an activation with no activation height on mainnet, at every height. -/
theorem relativeLockTime_activation_of_none (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason) (verify : SignatureVerifier) (view : List BlockIndex)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (hnone : a.height .mainnet = none)
    (s : CoinSet) (b : Block) :
    validateBlockWith V E (blockRevision verify view) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  relativeLockTime_activation V E verify view fCheckPOW fCheckMerkleRoot (Activation.none_inactive hnone ctx.height) s b

/-! ## Restriction -/

/--
The target `relativeLockTime_restricts` of design record 0012, section 9.3, for the revision with the rules of BIP 113 and BIP 112.
If `validateBlockWithActive` with the revision accepts a block, `validateBlock` accepts it, with the same coin set and the same changes.
For every `active`, pair of embeddings, verifier, pair of flags, context and coin set, on an applicable block or not.
The statement has no hypothesis on the times: `validateBlockWithActive` runs the contextual header check before the body check.
The proof uses conditions 1, 2 and 4 of design record 0012, section 6.4: `spend_restricts` for the flag, `scriptFlags_p2sh`, and `lockTimeCutoff_le` for the cutoff.
-/
theorem relativeLockTime_restricts {V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ'} {E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason}
    {verify : SignatureVerifier} {view : List BlockIndex} {active fCheckPOW fCheckMerkleRoot : Bool}
    {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E (blockRevision verify view) active fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r := by
  refine validateBlockWithActive_restricts (rev := blockRevision verify view)
    (fun ictx spk hacc => spend_restricts hacc) (scriptFlags_p2sh _ _) (fun hpass => ?_) h
  cases hcsv : ctx.csvActive with
  | false => exact lockTimeCutoff_le hcsv hpass
  | true =>
    have hg := connectBlockWith_ok_genesis_of_csvActive (validateBlockWithActive_ok_connect h) hcsv
    have hargs : (blockRevision verify view).lockTimeArgs active ctx b = baselineLockTimeArgs ctx :=
      lockTimeArgs_of_not_applicable (not_applicable_of_genesis hg)
    rw [hargs]
    exact Int.le_refl _

/-! ## A block that is not applicable -/

/--
Take a block that is not applicable, whose contextual header check passes (`contextualHeaderPassed`).
Then its header has the hash of the mainnet genesis block.
The other case of a block that is not applicable is an empty view, on which `contextualCheckBlockHeader` returns an adapter error.
-/
theorem genesis_of_not_applicable {ctx : ValidateContext} {b : Block} (happ : applicable ctx b = false)
    (hpass : contextualHeaderPassed ctx b) :
    (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true := by
  unfold applicable at happ
  unfold contextualHeaderPassed at hpass
  generalize (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = g at happ hpass
  cases g with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hpass
    rcases hview : ctx.view with _ | ⟨prev, rest⟩
    · rw [hview, contextualCheck_nil] at hpass
      cases hpass
    · simp [hview] at happ

/--
The revision is inactive on a block that is not applicable (design record 0012, section 5).
On such a block, `validateBlockWithActive` with the revision equals the embedded result of `validateBlock`, for every `active`.
The equality covers every acceptance, each rejection and each result outside the model.
For every pair of embeddings, verifier, pair of flags, context and coin set.

`scriptFlags` does not read the block.
A block that is not applicable and passes the contextual header check has the genesis hash, and `connectBlockWith` connects no transaction of it.
-/
theorem relativeLockTime_eq_of_not_applicable (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason) (verify : SignatureVerifier) (view : List BlockIndex)
    (active fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} (s : CoinSet) {b : Block}
    (happ : applicable ctx b = false) :
    validateBlockWithActive V E (blockRevision verify view) active fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  rw [← validateBlockWithActive_ofBaseline V E id id verify active]
  apply validateBlockWithActive_congr_of_passed
  · intro _
    simp only [contextualBodyWith, blockRevision, BlockRevision.baseline, lockTimeArgs_of_not_applicable happ]
  · intro hpass
    exact connectBlockWith_genesis E _ _ _ _ true _ s (genesis_of_not_applicable happ hpass)

/-! ## Blocks that the rules do not touch -/

/--
One script check with the CSV flag added, on an input whose spend check does not read that flag.
Let the spend check give one result with `withCsvFlag g` and with `g`, for the input and every flag set `g`.
Then `checkInputScriptWith` gives one outcome with `withCsvFlag f` and with `f`.
The equality covers the second run: the CSV flag is not mandatory, so both second runs have the flags of `f` that are mandatory.
For every embedding and spend check.
-/
theorem checkInputScriptWith_withCsvFlag {ε υ : Type} {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ}
    {f : UInt32} {txIndex : Nat} {tx : Transaction} {input : Nat} {coin : Coin}
    (h : ∀ ictx, inputContext? tx input = some ictx → ∀ g,
      spend ictx coin.out.scriptPubKey (withCsvFlag g) = spend ictx coin.out.scriptPubKey g) :
    checkInputScriptWith E spend (withCsvFlag f) txIndex tx input coin =
      checkInputScriptWith E spend f txIndex tx input coin := by
  unfold checkInputScriptWith
  cases hic : inputContext? tx input with
  | none => rfl
  | some ctx =>
    simp only [h ctx hic f, withCsvFlag_and_notMandatory, withCsvFlag_and_not_notMandatory, ↓reduceIte]
    cases hs : spend ctx coin.out.scriptPubKey f with
    | accepted => rfl
    | unsupported u => rfl
    | rejected e =>
      simp only
      cases hnm : (f &&& standardNotMandatoryVerifyFlags != 0) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [and_not_notMandatory_of_none hnm, hs]

/-- `checkInputScriptWith_withCsvFlag` for the script loop: each input of the list, with its coin, has a spend check that does not read the CSV flag. -/
theorem checkInputScriptsWith_withCsvFlag {ε υ : Type} {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ}
    {f : UInt32} {txIndex : Nat} {tx : Transaction} :
    ∀ {coins : List Coin} {input : Nat},
      (∀ j coin, coins[j]? = some coin → ∀ ictx, inputContext? tx (input + j) = some ictx → ∀ g,
        spend ictx coin.out.scriptPubKey (withCsvFlag g) = spend ictx coin.out.scriptPubKey g) →
      checkInputScriptsWith E spend (withCsvFlag f) txIndex tx input coins =
        checkInputScriptsWith E spend f txIndex tx input coins
  | [], _, _ => rfl
  | coin :: rest, input, h => by
    unfold checkInputScriptsWith
    rw [checkInputScriptWith_withCsvFlag (E := E) (fun ictx hic g => h 0 coin rfl ictx (by simpa using hic) g)]
    rw [checkInputScriptsWith_withCsvFlag (coins := rest) (input := input + 1)
      (fun j c hj ictx hic g => h (j + 1) c (by simpa using hj) ictx (by rw [← hic]; congr 1; omega) g)]

/--
On a spend with no instruction `0xb2` (`SpendUntouched isCsvOpcode`), the baseline spend check gives one result with `withCsvFlag g` and with `g`, for every flag set `g`.
The scripts of the spend are the `scriptSig`, the spent `scriptPubKey` and a P2SH redeem script.
-/
theorem baselineSpendCheck_withCsvFlag_of_untouched {verify : SignatureVerifier} {ictx : InputContext}
    {spk : Transaction.Script} (hu : SpendUntouched isCsvOpcode verify ictx spk) (g : UInt32) :
    baselineSpendCheck (ε := ScriptError) (υ := Unsupported) id id verify ictx spk (withCsvFlag g) =
      baselineSpendCheck id id verify ictx spk g := by
  rw [← spend_eq_baseline_of_untouched (O := isCsvOpcode)
    (step := fun ictx f => baselineStep id id (some (transactionChecker ictx.tx ictx.index verify)) (withCsvFlag f))
    (fun ictx f script st i hi => baselineStep_withCsvFlag_of_ne id id _ f script st i hi) hu g]
  unfold baselineSpendCheck verifyLegacySpend
  rw [← verifyScriptWith_baseline id id,
    verifyScriptWith_flags_congr _ (unsupportedFlagBits_withCsvFlag g) (hasFlag_withCsvFlag g (by decide))]

/--
Take a block on a coin set with two properties.
No script of a spend of the block holds an instruction `0xb2` (`BlockUntouched isCsvOpcode`).
The transaction test of the revision accepts every transaction of the block that is not a coinbase, with the coins of its inputs.
Then `connectBlockWith` with the revision equals `connectBlockWith` with the baseline revision, for every `active`.
The equality covers both runs of each script check.
-/
theorem connectBlockWith_eq_of_untouched (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason)
    (verify : SignatureVerifier) (view : List BlockIndex) (active fJustCheck : Bool) {ctx : ConnectContext}
    {s : CoinSet} {b : Block} (hfree : BlockUntouched isCsvOpcode verify ctx.height s b)
    (htest : ∀ i tx, b.transactions[i]? = some tx → tx.isCoinBase = false → ∀ coins,
      txTest active view ctx.height i tx coins = .ok ()) :
    connectBlockWith E (blockRevision verify view) active fJustCheck ctx s b =
      connectBlockWith E (.baseline id id verify) active fJustCheck ctx s b := by
  cases active with
  | false =>
    exact connectBlockWith_congr_revision E fJustCheck (fun _ _ _ _ _ _ _ _ _ => rfl) rfl
      (fun i tx hi hcb coins _ => htest i tx hi hcb coins)
  | true =>
    refine connectBlockWith_congr_scripts E fJustCheck (fun i tx hi hcb coins hl => ?_) (scriptFlags_p2sh true _)
      (fun i tx hi hcb coins _ => htest i tx hi hcb coins)
    show checkInputScriptsWith E (baselineSpendCheck id id verify) (withCsvFlag (connectScriptFlags ctx.height)) i tx 0
      coins = checkInputScriptsWith E (baselineSpendCheck id id verify) (connectScriptFlags ctx.height) i tx 0 coins
    apply checkInputScriptsWith_withCsvFlag
    intro j coin hj ictx hic g
    obtain ⟨input, hin, hcoin⟩ := lookupInputs_getElem? hl j coin hj
    obtain ⟨htx, hinp⟩ := inputContext?_some (by simpa using hic)
    have hinput : input = ictx.input := by
      rw [hin] at hinp
      exact Option.some.inj hinp
    exact baselineSpendCheck_withCsvFlag_of_untouched
      (hfree i tx hi hcb ictx htx coin (by rw [← hinput]; exact hcoin)) g

/--
The body check on a block without a cutoff transaction.
Take a context with `csvActive` false, and a block whose contextual header check passes (`contextualHeaderPassed`).
Let the block have no cutoff transaction (`CutoffUntouched`), when the view has a median time past `median`.
Then `contextualBodyWith` gives one result for the revision and for the baseline revision, for every `active` and every view argument of the revision.
The body check runs no script and no transaction test, so the statement has no condition on opcode `0xb2` or on a sequence.
The cutoff count of `block.contextual_check_body` rests on this theorem.
-/
theorem contextualBody_eq_of_cutoff_untouched (verify : SignatureVerifier) (view : List BlockIndex) (active : Bool)
    {ctx : ValidateContext} {b : Block} (hcsv : ctx.csvActive = false)
    (hfree : ∀ median, medianTimePast ctx.view = .ok median →
      CutoffUntouched median (b.header.pure.nTime.toNat : Int) b.transactions)
    (hpass : contextualHeaderPassed ctx b) :
    contextualBodyWith (blockRevision verify view) active ctx b =
      contextualBodyWith (BlockRevision.baseline (ρ := ConnectRejection) (μ := ConnectReason) id id verify) active
        ctx b := by
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

/--
No transaction of the list is an object of the rule of BIP 68.
Each transaction that is not a coinbase has a version below 2 as an unsigned value, or every one of its inputs has a sequence with bit 31 set.
-/
def SequenceUntouched (txs : List Transaction) : Prop :=
  ∀ tx ∈ txs, tx.isCoinBase = false →
    tx.version.toNat < 2 ∨ ∀ input ∈ tx.inputs.val, input.sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0

/--
On an applicable block whose contextual header check passes, the transaction test of the revision on the view of the context accepts every transaction that is not an object of the rule of BIP 68.
-/
theorem txTest_of_sequence_untouched {ctx : ValidateContext} {b : Block} (happ : applicable ctx b = true)
    (hpass : contextualHeaderPassed ctx b) {tx : Transaction}
    (h : tx.version.toNat < 2 ∨ ∀ input ∈ tx.inputs.val, input.sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0)
    (active : Bool) (index : Nat) (coins : List Coin) :
    txTest active ctx.view ctx.height index tx coins = .ok () := by
  rcases h with h | h
  · exact txTest_inactive (.inr h) _ _ _ _
  · obtain ⟨median, hmed, -⟩ := medianTimePast_of_headerPassed happ hpass
    rw [txTest_eq_ok_iff]
    rcases hview : ctx.view with _ | ⟨prev, rest⟩
    · exact sequenceLocks_empty_view _ _ _ _ _
    · rw [hview] at hmed
      exact sequenceLocks_of_disabled (by simp [ValidateContext.height, hview]) hmed h active index coins

/--
The target `relativeLockTime_eq_of_untouched` of design record 0012, section 9.3.
Take a context with `csvActive` false, and a block on a coin set in which no rule has an object:

1. The block has no cutoff transaction (`CutoffUntouched`), when the view has a median time past `median`.
   A cutoff transaction has a time lock time from `median` to below the time of the block, and an input whose sequence is not `SEQUENCE_FINAL`.
2. No transaction that is not a coinbase has both a version of at least 2 and an input whose sequence has bit 31 clear (`SequenceUntouched`).
3. No script of a spend of the block holds an instruction `0xb2` (`BlockUntouched isCsvOpcode`).
   The scripts are each `scriptSig`, each spent `scriptPubKey` and each P2SH redeem script.

Then `validateBlockWithActive` with the revision on the view of the context equals the embedded result of `validateBlock`, for every `active`.
So a block whose two verdicts differ has an object of one of the three rules.
A block that is not applicable needs none of the three conditions (`relativeLockTime_eq_of_not_applicable`).
For every pair of embeddings, verifier and pair of flags.
-/
theorem relativeLockTime_eq_of_untouched (V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ')
    (E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason) (verify : SignatureVerifier)
    (active fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} {s : CoinSet} {b : Block}
    (hcsv : ctx.csvActive = false)
    (hfree : ∀ median, medianTimePast ctx.view = .ok median →
      CutoffUntouched median (b.header.pure.nTime.toNat : Int) b.transactions)
    (hseq : SequenceUntouched b.transactions)
    (hop : BlockUntouched isCsvOpcode verify ctx.height s b) :
    validateBlockWithActive V E (blockRevision verify ctx.view) active fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E id id (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  cases happ : applicable ctx b with
  | false => exact relativeLockTime_eq_of_not_applicable V E verify _ active fCheckPOW fCheckMerkleRoot s happ
  | true =>
    rw [← validateBlockWithActive_ofBaseline V E id id verify active]
    apply validateBlockWithActive_congr_of_passed
    · exact contextualBody_eq_of_cutoff_untouched verify _ active hcsv hfree
    · intro hpass
      exact connectBlockWith_eq_of_untouched E verify _ active true (ctx := connectContextOf ctx b) hop
        (fun i tx hi hcb coins =>
          txTest_of_sequence_untouched happ hpass (hseq tx (List.mem_of_getElem? hi) hcb) active i coins)

end DogeLib.Proposals.RelativeLockTime
