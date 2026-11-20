module

public import DogeLib.Block.Proofs.ConnectProperties
public import DogeLib.Proposals.Framework.Block
public import DogeLib.Proposals.Framework.Proofs.Activation
public import DogeLib.Proposals.Framework.Proofs.LockTime
public import DogeLib.Proposals.Framework.Proofs.Script
public meta import Lean.Elab.Term
import Lean.Elab.Term

/-!
# Proofs: `Proposals.Framework.Block`

The theorems of the block-level layer of a proposed revision (design record 0011, section 10.1), with the extensions E1 to E4 of design record 0012, section 6.3.
Each is block-level: it is about one block on a supplied coin set and chain view.
None is a claim about a chain or about the network.

Every theorem holds for every signature verifier, and none assumes a property of the verifier.
`E` and `V` are the embeddings of `ConnectBlock` and `validateBlock` results, and every theorem holds for every embedding.

A revision has four parts: its spend check, its script flags (E1), its transaction test (E2) and its lock-time arguments (E3).
`validateBlockWith` is `validateBlockWithActive` at the value of `active` that an activation gives, and most theorems have both forms.

## Agreement with the baseline

- `connectBlockWith_ofBaseline`: `connectBlockWith` with the baseline revision equals the embedded result of `connectBlock`, for every embedding, error map and map of unsupported reasons.
- `connectBlockWith_baseline`: with the baseline error type, `connectBlockWith` with the baseline revision equals `connectBlock`. The design records name this theorem as a target.
- `validateBlockWithActive_ofBaseline`, `validateBlockWith_ofBaseline` and `validateBlockWith_baseline`: the same for `validateBlock`.

So a change to `connectBlock` or `validateBlock` that the copies do not follow fails the build.
These theorems hold for every context. With `csvActive` true in the context, both sides give the result `csvActive` when they reach the test of that field.

## Inactive equality

- `BlockRevision.InactiveBaseline`: with `active` false, each of the four parts of a revision has its baseline value.
- `connectBlockWith_inactive`: for such a revision, `connectBlockWith` with `active` false equals the embedded result of `connectBlock`.
- `validateBlockWithActive_inactive`, `validateBlockWith_inactive`: for such a revision, and an activation that is inactive at the height of the block, the revised validation equals the embedded result of `validateBlock`.
- `validateBlockWith_inactive_of_lt` and `validateBlockWith_inactive_of_none`: the cases of a block below the activation height, and of no activation height.

## Restriction

A revision restricts the baseline under the four conditions of design record 0012, section 6.4.

- `connectBlockWith_restricts`: conditions 1 to 3. A block that `connectBlockWith` accepts on a coin set is accepted by `connectBlock` on that set, with the same coin set and the same changes.
- `validateBlockWithActive_restricts`, `validateBlockWith_restricts`: the same for `validateBlock`, with condition 4 on the lock-time cutoff.
- `connectBlockWith_ok_of` and `validateBlockWithActive_ok_of`: the general form, between two revisions.
- `checksBeforeConnect_ok_of_cutoff`: the four checks before `ConnectBlock` accept at every later cutoff.

Condition 1 is about acceptance by the spend check, which is the first run of each script check.
The theorems say nothing about the error of a rejection.
Condition 4 can use the result of the contextual header check (`contextualHeaderPassed`), which runs before the body check.

## Congruence

- `connectBlockWith_congr_revision`: two revisions whose spend checks, script flags and transaction tests agree on a block give one `connectBlockWith` outcome.
- `validateBlockWithActive_congr`: `validateBlockWithActive` reads a revision through `contextualBodyWith` and `connectBlockWith` alone.
- `SpendUntouched O` and `BlockUntouched O`: no `scriptSig`, no spent `scriptPubKey` and no P2SH redeem script of the block holds an instruction with an opcode in `O`.
- `verifyScriptWith_congr_p2sh`: `verifyScriptWith_congr` with the redeem-script hypothesis only for a pay-to-script-hash `scriptPubKey` and a push-only `scriptSig`.
- `connectBlockWith_congr` and `validateBlockWith_congr`: take a revision whose spend check is `verifyScriptWith` with a step that equals the baseline step outside `O`, and whose other parts agree with the baseline on the block. On a block with `BlockUntouched O`, the outcome equals the embedded result of the baseline. The equality holds for both runs of each script check.

A spend of a block is an input of a transaction that is not a coinbase, with the coin of its outpoint.
The coin is that of `coinsBefore`: the coin set just before the transaction.
So the spent `scriptPubKey` of an input can come from an earlier transaction of the same block.

## The unfolding of `validateBlock`

`validateBlock_eq_checks` states `validateBlock` as `checksBeforeConnect` and then `connectBlock`.
Its proof does not use `unfold validateBlock`.
The kernel compares a definition with its unfolded body by reduction.
Here it reduces the test of the genesis hash, which does not end in practical time.
`validateBlock_value` states the unfolding with the stored value of the definition, which `definition_value%` reads from the environment.
The kernel checks that theorem as it checks every other: the two sides are one term.
The elaborator `definition_value%` is not trusted. A wrong value would fail the kernel check of `validateBlock_value`.

`checksBeforeConnect_eq_body` evaluates the first three checks from their results.
A proof about a concrete block uses it, so that the kernel evaluates each check alone.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Block DogeLib.Transaction DogeLib.Script DogeLib.Work

variable {ε υ ρ μ ρ' μ' : Type}

/-! ## Outcomes -/

/-- An outcome whose `rejection?` is `some e` is the rejection `e`. -/
theorem BlockOutcome.eq_rejected_of_rejection? {α : Type} {o : BlockOutcome ρ μ α} {e : ρ}
    (h : o.rejection? = some e) : o = .rejected e := by
  cases o <;> simp_all [BlockOutcome.rejection?]

/-- An outcome with `isOk` true is an acceptance with some result. -/
theorem BlockOutcome.exists_ok_of_isOk {α : Type} {o : BlockOutcome ρ μ α} (h : o.isOk = true) : ∃ a, o = .ok a := by
  cases o <;> simp_all [BlockOutcome.isOk]

/-- An outcome has the verdict `accepted` exactly when it is an acceptance with some result. -/
theorem BlockOutcome.verdict_eq_accepted_iff {α : Type} {o : BlockOutcome ρ μ α} :
    o.verdict = .accepted ↔ ∃ a, o = .ok a := by
  cases o <;> simp [BlockOutcome.verdict]

/-- `ConnectEmbedding.ofError` never accepts. -/
theorem ConnectEmbedding.ofError_ne_ok {α : Type} (E : ConnectEmbedding ε υ ρ μ) (e : ConnectBlockError) (a : α) :
    (E.ofError e : BlockOutcome ρ μ α) ≠ .ok a := by
  unfold ConnectEmbedding.ofError
  split <;> simp

/-- With the baseline embedding, `toExcept` of the embedded result of a `ConnectBlock` call is that result. -/
theorem ConnectEmbedding.toExcept_ofBaseline {α : Type} (r : Except ConnectBlockError α) :
    (ConnectEmbedding.baseline.ofBaseline id id r).toExcept = r := by
  rcases r with e | a
  · cases e <;>
      simp only [ConnectEmbedding.ofBaseline, ConnectEmbedding.ofBaselineError, ConnectEmbedding.ofError,
        ConnectEmbedding.baseline, id] <;>
      first | rfl | (split <;> rfl)
  · rfl

/-- A baseline error has one embedded form at every result type: a rejection or an unsupported reason. -/
theorem ConnectEmbedding.ofError_cases (E : ConnectEmbedding ε υ ρ μ) (e : ConnectBlockError) :
    (∃ r, ∀ α : Type, (E.ofError e : BlockOutcome ρ μ α) = .rejected r) ∨
      (∃ u, ∀ α : Type, (E.ofError e : BlockOutcome ρ μ α) = .unsupported u) := by
  unfold ConnectEmbedding.ofError
  by_cases h : e.isRejection
  · exact .inl ⟨E.rejected e, fun _ => by simp [h]⟩
  · exact .inr ⟨E.unsupported e, fun _ => by simp [h]⟩

/-- The embedded form of a baseline error is one rejection or one unsupported reason at every result type. -/
theorem ConnectEmbedding.ofBaselineError_cases (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (e : ConnectBlockError) :
    (∃ r, ∀ α : Type, (E.ofBaselineError embed embedU e : BlockOutcome ρ μ α) = .rejected r) ∨
      (∃ u, ∀ α : Type, (E.ofBaselineError embed embedU e : BlockOutcome ρ μ α) = .unsupported u) := by
  cases e
  case script tx input mandatory e => exact .inl ⟨_, fun _ => rfl⟩
  case scriptUnsupported u => exact .inr ⟨_, fun _ => rfl⟩
  all_goals exact E.ofError_cases _

/-- An `if` with a false condition is its second branch. -/
private theorem ite_neg' {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : (if c then a else b) = b := by
  simp [h]

/-- If a guarded baseline error accepts, the guard is false and the other branch accepts. -/
theorem ConnectEmbedding.ite_ofError_ok {α : Type} {E : ConnectEmbedding ε υ ρ μ} {c : Prop} [Decidable c]
    {e : ConnectBlockError} {t : BlockOutcome ρ μ α} {y : α}
    (h : (if c then (E.ofError e : BlockOutcome ρ μ α) else t) = .ok y) : ¬c ∧ t = .ok y := by
  split at h
  · exact absurd h (E.ofError_ne_ok _ _)
  · exact ⟨‹_›, h⟩

/-! ## Agreement with the baseline -/

/-- With the baseline spend check, `checkInputScriptWith` equals the embedded result of `checkInputScript`, for every embedding, flag set, transaction, input and coin. -/
theorem checkInputScriptWith_baseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat) (tx : Transaction)
    (input : Nat) (coin : Coin) :
    checkInputScriptWith E (baselineSpendCheck embed embedU verify) flags txIndex tx input coin =
      E.ofBaseline embed embedU (checkInputScript verify flags txIndex tx input coin) := by
  unfold checkInputScriptWith checkInputScript baselineSpendCheck
  cases inputContext? tx input with
  | none => rfl
  | some ctx =>
    simp only
    cases verifyLegacySpend ctx coin.out.scriptPubKey flags verify with
    | accepted => rfl
    | unsupported u => rfl
    | rejected e =>
      simp only [VerifyOutcome.ofBaseline]
      split
      · cases verifyLegacySpend ctx coin.out.scriptPubKey (flags &&& ~~~standardNotMandatoryVerifyFlags) verify <;> rfl
      · rfl

/-- With the baseline spend check, `checkInputScriptsWith` equals the embedded result of `checkInputScripts`, for every list of coins and first input. -/
theorem checkInputScriptsWith_baseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat) (tx : Transaction) :
    ∀ (coins : List Coin) (input : Nat),
      checkInputScriptsWith E (baselineSpendCheck embed embedU verify) flags txIndex tx input coins =
        E.ofBaseline embed embedU (checkInputScripts verify flags txIndex tx input coins)
  | [], _ => rfl
  | coin :: rest, input => by
    unfold checkInputScriptsWith checkInputScripts
    rw [checkInputScriptWith_baseline]
    cases h : checkInputScript verify flags txIndex tx input coin with
    | ok u =>
      cases u
      simpa [ConnectEmbedding.ofBaseline] using
        checkInputScriptsWith_baseline E embed embedU verify flags txIndex tx rest (input + 1)
    | error e =>
      simp only [ConnectEmbedding.ofBaseline]
      rcases E.ofBaselineError_cases embed embedU e with ⟨r, hr⟩ | ⟨u, hu⟩
      · simp [hr]
      · simp [hu]

/-- With the baseline spend check, `checkInputsWith` equals the embedded result of `checkInputs`. -/
theorem checkInputsWith_baseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (height : Nat) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (coins : List Coin) :
    checkInputsWith E (baselineSpendCheck embed embedU verify) height flags txIndex tx coins =
      E.ofBaseline embed embedU (checkInputs verify height flags txIndex tx coins) := by
  unfold checkInputsWith checkInputs
  rw [checkInputScriptsWith_baseline]
  split <;> simp_all [ConnectEmbedding.ofBaseline, ConnectEmbedding.ofBaselineError]

/-- With the baseline spend check and the test that accepts everything, `connectTransactionWith` equals the embedded result of `connectTransaction`, for every context, flag set, state and transaction. -/
theorem connectTransactionWith_baseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) (index : Nat)
    (st : ConnectState) (tx : Transaction) :
    connectTransactionWith E (baselineSpendCheck embed embedU verify) TxTest.accept ctx flags index st tx =
      E.ofBaseline embed embedU (connectTransaction verify ctx flags index st tx) := by
  unfold connectTransactionWith connectFoundWith connectTransaction TxTest.accept
  simp only [checkInputsWith_baseline, ite_self]
  generalize (if tx.isCoinBase = true then some [] else lookupInputs st.coins tx.inputs.val) = lk
  cases lk with
  | none => rfl
  | some coins =>
    simp only
    by_cases hcost : st.sigOpsCost + getTransactionSigOpCost tx coins (hasFlag flags ScriptFlags.p2sh) >
        maxBlockSigOpsCost
    · simp only [hcost, ↓reduceIte]; rfl
    · simp only [hcost, ↓reduceIte]
      generalize (if tx.isCoinBase = true then some st.fees else addFee st.fees coins tx.valueOut) = fs
      cases fs with
      | none => rfl
      | some fees =>
        simp only
        cases hcb : tx.isCoinBase with
        | true => simp only [↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]; rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
          cases h : checkInputs verify ctx.height flags index tx coins with
          | ok u =>
            cases u
            simp only [ConnectEmbedding.ofBaseline]
            split <;> rfl
          | error e =>
            simp only [ConnectEmbedding.ofBaseline]
            rcases E.ofBaselineError_cases embed embedU e with ⟨r, hr⟩ | ⟨u, hu⟩
            · simp [hr]
            · simp [hu]

/-- With the baseline spend check and the test that accepts everything, `connectTransactionsWith` equals the embedded result of `connectTransactions`, for every list of transactions, index and state. -/
theorem connectTransactionsWith_baseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) :
    ∀ (txs : List Transaction) (index : Nat) (st : ConnectState),
      connectTransactionsWith E (baselineSpendCheck embed embedU verify) TxTest.accept ctx flags index st txs =
        E.ofBaseline embed embedU (connectTransactions verify ctx flags index st txs)
  | [], _, _ => rfl
  | tx :: rest, index, st => by
    unfold connectTransactionsWith connectTransactions
    rw [connectTransactionWith_baseline]
    cases h : connectTransaction verify ctx flags index st tx with
    | ok st' =>
      simpa [ConnectEmbedding.ofBaseline] using
        connectTransactionsWith_baseline E embed embedU verify ctx flags rest (index + 1) st'
    | error e =>
      simp only [ConnectEmbedding.ofBaseline]
      rcases E.ofBaselineError_cases embed embedU e with ⟨r, hr⟩ | ⟨u, hu⟩
      · simp [hr]
      · simp [hu]

/--
For every embedding `E`, error map `embed`, map of unsupported reasons `embedU`, verifier, value of `active`, flag `fJustCheck`, context, coin set and block:
`connectBlockWith` with the baseline revision equals the embedded result of `connectBlock`.
The baseline revision has the baseline spend check and the baseline values of the script flags and of the transaction test.
-/
theorem connectBlockWith_ofBaseline (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) (active fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) :
    connectBlockWith E (.baseline embed embedU verify) active fJustCheck ctx s b =
      E.ofBaseline embed embedU (connectBlock verify fJustCheck ctx s b) := by
  unfold connectBlockWith connectBlock BlockRevision.baseline
  simp only [connectTransactionsWith_baseline]
  cases checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | error e => rfl
  | ok u =>
    simp only
    cases hg : (some b.header.pure.getHash == genesisHash? .mainnet) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases h30 : (enforceBip30 ctx.bip34Ancestor && b.transactions.any (fun tx => s.haveUnspent tx.txid)) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hcsv : ctx.csvActive with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases h : connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions with
          | error e =>
            simp only [ConnectEmbedding.ofBaseline]
            rcases E.ofBaselineError_cases embed embedU e with ⟨r, hr⟩ | ⟨u, hu⟩
            · simp [hr]
            · simp [hu]
          | ok st =>
            have hok : (E.ofBaseline embed embedU (.ok st) : BlockOutcome ρ μ ConnectState) = .ok st := rfl
            simp only [hok]
            cases getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash with
            | error e => rfl
            | ok subsidy =>
              simp only
              cases hr : (!inInt64Range (st.fees + (subsidy : Int))) with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [apply_ite (E.ofBaseline embed embedU)]
                rfl

/-! ## Restriction -/

section Restriction

variable {ε₁ υ₁ ρ₁ μ₁ ε₂ υ₂ ρ₂ μ₂ : Type} {E₁ : ConnectEmbedding ε₁ υ₁ ρ₁ μ₁} {E₂ : ConnectEmbedding ε₂ υ₂ ρ₂ μ₂}
  {spend₁ : SpendCheck ε₁ υ₁} {spend₂ : SpendCheck ε₂ υ₂} {test₁ : TxTest ρ₁ μ₁} {test₂ : TxTest ρ₂ μ₂}
  {flags₁ flags₂ : UInt32}

/-- Let every input that `spend₁` accepts under `flags₁` be accepted by `spend₂` under `flags₂`. If `checkInputScriptWith` accepts an input with `spend₁` and `flags₁`, it accepts the input with `spend₂` and `flags₂`. -/
theorem checkInputScriptWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted)
    {txIndex : Nat} {tx : Transaction} {input : Nat} {coin : Coin}
    (h : checkInputScriptWith E₁ spend₁ flags₁ txIndex tx input coin = .ok ()) :
    checkInputScriptWith E₂ spend₂ flags₂ txIndex tx input coin = .ok () := by
  unfold checkInputScriptWith at h ⊢
  cases hic : inputContext? tx input with
  | none => simp [hic, ConnectEmbedding.ofError_ne_ok] at h
  | some ctx =>
    simp only [hic] at h ⊢
    cases hs : spend₁ ctx coin.out.scriptPubKey flags₁ with
    | accepted => simp [hacc _ _ hs]
    | unsupported u => simp [hs] at h
    | rejected e =>
      simp only [hs] at h
      split at h
      · split at h <;> cases h
      · cases h

/-- Let every input that `spend₁` accepts under `flags₁` be accepted by `spend₂` under `flags₂`. If `checkInputScriptsWith` accepts with `spend₁` and `flags₁`, it accepts with `spend₂` and `flags₂`. -/
theorem checkInputScriptsWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted)
    {txIndex : Nat} {tx : Transaction} :
    ∀ {coins : List Coin} {input : Nat}, checkInputScriptsWith E₁ spend₁ flags₁ txIndex tx input coins = .ok () →
      checkInputScriptsWith E₂ spend₂ flags₂ txIndex tx input coins = .ok ()
  | [], _, _ => rfl
  | coin :: rest, input, h => by
    unfold checkInputScriptsWith at h ⊢
    cases h1 : checkInputScriptWith E₁ spend₁ flags₁ txIndex tx input coin with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok u =>
      simp only [h1] at h
      simp only [checkInputScriptWith_ok_of hacc h1]
      exact checkInputScriptsWith_ok_of hacc h

/-- Let every input that `spend₁` accepts under `flags₁` be accepted by `spend₂` under `flags₂`. If `checkInputsWith` accepts with `spend₁` and `flags₁`, it accepts with `spend₂` and `flags₂`. -/
theorem checkInputsWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted) {height : Nat}
    {txIndex : Nat} {tx : Transaction} {coins : List Coin}
    (h : checkInputsWith E₁ spend₁ height flags₁ txIndex tx coins = .ok ()) :
    checkInputsWith E₂ spend₂ height flags₂ txIndex tx coins = .ok () := by
  unfold checkInputsWith at h ⊢
  cases hc : checkTxInputs height coins tx.valueOut with
  | error e =>
    simp only [hc] at h
    split at h <;> first | exact absurd h (E₁.ofError_ne_ok _ _) | simp_all
  | ok u =>
    simp only [hc] at h ⊢
    exact checkInputScriptsWith_ok_of hacc h

/--
Let every input that `spend₁` accepts under `flags₁` be accepted by `spend₂` under `flags₂`, and let the two flag sets agree on `SCRIPT_VERIFY_P2SH`.
If `connectFoundWith` accepts a transaction with `spend₁` and `flags₁`, it accepts the transaction with `spend₂` and `flags₂`, with the same state.
-/
theorem connectFoundWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted)
    (hp2sh : hasFlag flags₁ ScriptFlags.p2sh = hasFlag flags₂ ScriptFlags.p2sh) {ctx : ConnectContext}
    {index : Nat} {st st' : ConnectState} {tx : Transaction} {coins : List Coin}
    (h : connectFoundWith E₁ spend₁ ctx flags₁ index st tx coins = .ok st') :
    connectFoundWith E₂ spend₂ ctx flags₂ index st tx coins = .ok st' := by
  unfold connectFoundWith at h ⊢
  rw [hp2sh] at h
  simp only at h ⊢
  obtain ⟨hcost, h⟩ := ConnectEmbedding.ite_ofError_ok h
  rw [ite_neg' hcost]
  generalize (if tx.isCoinBase = true then some st.fees else addFee st.fees coins tx.valueOut) = fs at h ⊢
  cases fs with
  | none => exact absurd h (E₁.ofError_ne_ok _ _)
  | some fees =>
    simp only at h ⊢
    have hci : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ₂ μ₂ Unit)
        else checkInputsWith E₂ spend₂ ctx.height flags₂ index tx coins) = .ok () := by
      cases hcb : tx.isCoinBase with
      | true => rfl
      | false =>
        simp only [hcb, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases h1 : checkInputsWith E₁ spend₁ ctx.height flags₁ index tx coins with
        | rejected e => simp [h1] at h
        | unsupported u => simp [h1] at h
        | ok u => exact checkInputsWith_ok_of hacc h1
    rw [hci]
    cases h1 : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ₁ μ₁ Unit)
        else checkInputsWith E₁ spend₁ ctx.height flags₁ index tx coins) with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok u =>
      simp only [h1] at h ⊢
      obtain ⟨hn, h⟩ := ConnectEmbedding.ite_ofError_ok h
      rw [ite_neg' hn]
      cases h
      rfl

/--
Take the hypotheses of `connectFoundWith_ok_of`, and let `test₂` accept every transaction that `test₁` accepts.
If `connectTransactionWith` accepts a transaction with `spend₁`, `test₁` and `flags₁`, it accepts the transaction with `spend₂`, `test₂` and `flags₂`, with the same state.
-/
theorem connectTransactionWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted)
    (hp2sh : hasFlag flags₁ ScriptFlags.p2sh = hasFlag flags₂ ScriptFlags.p2sh)
    (htest : ∀ index tx coins, test₁ index tx coins = .ok () → test₂ index tx coins = .ok ())
    {ctx : ConnectContext} {index : Nat} {st st' : ConnectState} {tx : Transaction}
    (h : connectTransactionWith E₁ spend₁ test₁ ctx flags₁ index st tx = .ok st') :
    connectTransactionWith E₂ spend₂ test₂ ctx flags₂ index st tx = .ok st' := by
  unfold connectTransactionWith at h ⊢
  generalize (if tx.isCoinBase = true then some [] else lookupInputs st.coins tx.inputs.val) = lk at h ⊢
  cases lk with
  | none => exact absurd h (E₁.ofError_ne_ok _ _)
  | some coins =>
    simp only at h ⊢
    cases h1 : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ₁ μ₁ Unit)
        else test₁ index tx coins) with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok u =>
      simp only [h1] at h
      have h2 : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ₂ μ₂ Unit)
          else test₂ index tx coins) = .ok () := by
        cases hcb : tx.isCoinBase with
        | true => rfl
        | false =>
          simp only [hcb, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          exact htest _ _ _ h1
      simp only [h2]
      exact connectFoundWith_ok_of hacc hp2sh h

/-- Under the hypotheses of `connectTransactionWith_ok_of`: if `connectTransactionsWith` accepts with `spend₁`, `test₁` and `flags₁`, it accepts with `spend₂`, `test₂` and `flags₂`, with the same state. -/
theorem connectTransactionsWith_ok_of
    (hacc : ∀ ictx spk, spend₁ ictx spk flags₁ = .accepted → spend₂ ictx spk flags₂ = .accepted)
    (hp2sh : hasFlag flags₁ ScriptFlags.p2sh = hasFlag flags₂ ScriptFlags.p2sh)
    (htest : ∀ index tx coins, test₁ index tx coins = .ok () → test₂ index tx coins = .ok ())
    {ctx : ConnectContext} :
    ∀ {txs : List Transaction} {index : Nat} {st st' : ConnectState},
      connectTransactionsWith E₁ spend₁ test₁ ctx flags₁ index st txs = .ok st' →
        connectTransactionsWith E₂ spend₂ test₂ ctx flags₂ index st txs = .ok st'
  | [], _, _, _, h => by
    unfold connectTransactionsWith at h ⊢
    cases h
    rfl
  | tx :: rest, index, st, st', h => by
    unfold connectTransactionsWith at h ⊢
    cases h1 : connectTransactionWith E₁ spend₁ test₁ ctx flags₁ index st tx with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok st1 =>
      simp only [h1] at h
      simp only [connectTransactionWith_ok_of hacc hp2sh htest h1]
      exact connectTransactionsWith_ok_of hacc hp2sh htest h

/--
Acceptance moves from one revision to another.
Take two revisions, a value of `active` and a context, with the script flags `f₁` and `f₂` of the two revisions at the height of the context.
Let three conditions hold:

1. Every input that the spend check of `rev₁` accepts under `f₁`, the spend check of `rev₂` accepts under `f₂`.
2. `f₁` and `f₂` agree on `SCRIPT_VERIFY_P2SH`, which the count of signature operations reads.
3. Every transaction that the test of `rev₁` accepts, the test of `rev₂` accepts.

If `connectBlockWith` accepts a block with `rev₁`, it accepts the block with `rev₂`, with the same coin set and the same changes.
The two revisions can have different error types and embeddings.
-/
theorem connectBlockWith_ok_of {rev₁ : BlockRevision ε₁ υ₁ ρ₁ μ₁} {rev₂ : BlockRevision ε₂ υ₂ ρ₂ μ₂} {active : Bool}
    {ctx : ConnectContext}
    (hacc : ∀ ictx spk, rev₁.spend active ictx spk (rev₁.scriptFlags active ctx.height) = .accepted →
      rev₂.spend active ictx spk (rev₂.scriptFlags active ctx.height) = .accepted)
    (hp2sh : hasFlag (rev₁.scriptFlags active ctx.height) ScriptFlags.p2sh =
      hasFlag (rev₂.scriptFlags active ctx.height) ScriptFlags.p2sh)
    (htest : ∀ index tx coins, rev₁.txTest active ctx.height index tx coins = .ok () →
      rev₂.txTest active ctx.height index tx coins = .ok ())
    {fJustCheck : Bool} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : connectBlockWith E₁ rev₁ active fJustCheck ctx s b = .ok r) :
    connectBlockWith E₂ rev₂ active fJustCheck ctx s b = .ok r := by
  unfold connectBlockWith at h ⊢
  cases hcb : checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | error e =>
    simp only [hcb] at h
    exact absurd h (E₁.ofError_ne_ok _ _)
  | ok u =>
    simp only [hcb] at h ⊢
    cases hg : (some b.header.pure.getHash == genesisHash? .mainnet) with
    | true =>
      simp only [hg, ↓reduceIte] at h ⊢
      cases h
      rfl
    | false =>
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h30 : (enforceBip30 ctx.bip34Ancestor && b.transactions.any (fun tx => s.haveUnspent tx.txid)) with
      | true =>
        simp only [h30, ↓reduceIte] at h
        exact absurd h (E₁.ofError_ne_ok _ _)
      | false =>
        simp only [h30, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hcsv : ctx.csvActive with
        | true =>
          simp only [hcsv, ↓reduceIte] at h
          exact absurd h (E₁.ofError_ne_ok _ _)
        | false =>
          simp only [hcsv, Bool.false_eq_true, ↓reduceIte] at h ⊢
          cases h1 : connectTransactionsWith E₁ (rev₁.spend active) (rev₁.txTest active ctx.height) ctx
              (rev₁.scriptFlags active ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions with
          | rejected e => simp [h1] at h
          | unsupported u => simp [h1] at h
          | ok st =>
            simp only [h1] at h
            simp only [connectTransactionsWith_ok_of hacc hp2sh htest h1]
            cases hsub : getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash with
            | error e =>
              simp only [hsub] at h
              exact absurd h (E₁.ofError_ne_ok _ _)
            | ok subsidy =>
              simp only [hsub] at h ⊢
              obtain ⟨hr, h⟩ := ConnectEmbedding.ite_ofError_ok h
              rw [ite_neg' hr]
              obtain ⟨hc, h⟩ := ConnectEmbedding.ite_ofError_ok h
              rw [ite_neg' hc]
              cases h
              rfl

end Restriction

/-! ## Congruence -/

/-- The context that `inputContext?` builds has the transaction, and its input is the input at the index. -/
theorem inputContext?_some {tx : Transaction} {input : Nat} {ictx : InputContext}
    (h : inputContext? tx input = some ictx) : ictx.tx = tx ∧ tx.inputs.val[input]? = some ictx.input := by
  unfold inputContext? at h
  split at h
  · rename_i hb
    cases h
    have hlt : input < 2 ^ 32 := by omega
    refine ⟨rfl, ?_⟩
    simp [InputContext.input, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, List.getElem?_eq_getElem hb.1]
  · cases h

/-- When `lookupInputs` succeeds, the coin at each position is the coin of the input at that position. -/
theorem lookupInputs_getElem? {s : CoinSet} : ∀ {inputs : List TxIn} {coins : List Coin},
    lookupInputs s inputs = some coins → ∀ (j : Nat) (c : Coin), coins[j]? = some c →
      ∃ input, inputs[j]? = some input ∧ s.coin input.prevout = some c
  | [], coins, h, j, c, hc => by
    simp only [lookupInputs, Option.some.injEq] at h
    subst h
    simp at hc
  | i :: rest, coins, h, j, c, hc => by
    unfold lookupInputs at h
    split at h
    · cases h
    · rename_i c0 hc0
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, rfl⟩ := h
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        exact ⟨i, rfl, hc0⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hc ⊢
        exact lookupInputs_getElem? htail k c hc

section Congruence

variable {E : ConnectEmbedding ε υ ρ μ} {spend₁ spend₂ : SpendCheck ε υ}

/-- If two spend checks agree on the input, for every flag set, `checkInputScriptWith` gives the same outcome for both. -/
theorem checkInputScriptWith_congr {flags : UInt32} {txIndex : Nat} {tx : Transaction} {input : Nat} {coin : Coin}
    (h : ∀ ictx, inputContext? tx input = some ictx → ∀ f,
      spend₁ ictx coin.out.scriptPubKey f = spend₂ ictx coin.out.scriptPubKey f) :
    checkInputScriptWith E spend₁ flags txIndex tx input coin =
      checkInputScriptWith E spend₂ flags txIndex tx input coin := by
  unfold checkInputScriptWith
  cases hic : inputContext? tx input with
  | none => rfl
  | some ctx => simp only [h ctx hic]

/-- If two spend checks agree on each input of the list with its coin, for every flag set, `checkInputScriptsWith` gives the same outcome for both. -/
theorem checkInputScriptsWith_congr {flags : UInt32} {txIndex : Nat} {tx : Transaction} :
    ∀ {coins : List Coin} {input : Nat},
      (∀ j coin, coins[j]? = some coin → ∀ ictx, inputContext? tx (input + j) = some ictx → ∀ f,
        spend₁ ictx coin.out.scriptPubKey f = spend₂ ictx coin.out.scriptPubKey f) →
      checkInputScriptsWith E spend₁ flags txIndex tx input coins =
        checkInputScriptsWith E spend₂ flags txIndex tx input coins
  | [], _, _ => rfl
  | coin :: rest, input, h => by
    unfold checkInputScriptsWith
    rw [checkInputScriptWith_congr (E := E) (fun ictx hic f => h 0 coin rfl ictx (by simpa using hic) f)]
    rw [checkInputScriptsWith_congr (coins := rest) (input := input + 1)
      (fun j c hj ictx hic f => h (j + 1) c (by simpa using hj) ictx (by rw [← hic]; congr 1; omega) f)]

/--
Let the script loops of two spend checks, and two transaction tests, agree on the coins that `lookupInputs` finds for the transaction.
Then `connectTransactionWith` gives the same outcome for both.
-/
theorem connectTransactionWith_congr {test₁ test₂ : TxTest ρ μ} {ctx : ConnectContext} {flags : UInt32} {index : Nat}
    {st : ConnectState} {tx : Transaction}
    (h : tx.isCoinBase = false → ∀ coins, lookupInputs st.coins tx.inputs.val = some coins →
      checkInputScriptsWith E spend₁ flags index tx 0 coins = checkInputScriptsWith E spend₂ flags index tx 0 coins)
    (htest : tx.isCoinBase = false → ∀ coins, lookupInputs st.coins tx.inputs.val = some coins →
      test₁ index tx coins = test₂ index tx coins) :
    connectTransactionWith E spend₁ test₁ ctx flags index st tx =
      connectTransactionWith E spend₂ test₂ ctx flags index st tx := by
  unfold connectTransactionWith connectFoundWith
  cases hcb : tx.isCoinBase with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases hl : lookupInputs st.coins tx.inputs.val with
    | none => rfl
    | some coins =>
      simp only [checkInputsWith, h hcb coins hl, htest hcb coins hl]

/-- A transaction that the loop accepts leaves the set `applyTransaction` of the set before it. -/
theorem connectTransactionWith_ok_coins {spend : SpendCheck ε υ} {test : TxTest ρ μ} {ctx : ConnectContext}
    {flags : UInt32} {index : Nat} {st st' : ConnectState} {tx : Transaction}
    (h : connectTransactionWith E spend test ctx flags index st tx = .ok st') :
    st'.coins = applyTransaction st.coins ctx.height tx := by
  unfold connectTransactionWith connectFoundWith at h
  generalize (if tx.isCoinBase = true then some [] else lookupInputs st.coins tx.inputs.val) = lk at h
  cases lk with
  | none => exact absurd h (E.ofError_ne_ok _ _)
  | some coins =>
    simp only at h
    cases h0 : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ μ Unit)
        else test index tx coins) with
    | rejected e => simp [h0] at h
    | unsupported u => simp [h0] at h
    | ok u0 =>
      simp only [h0] at h
      obtain ⟨_, h⟩ := ConnectEmbedding.ite_ofError_ok h
      generalize (if tx.isCoinBase = true then some st.fees else addFee st.fees coins tx.valueOut) = fs at h
      cases fs with
      | none => exact absurd h (E.ofError_ne_ok _ _)
      | some fees =>
        simp only at h
        cases h1 : (if tx.isCoinBase = true then (BlockOutcome.ok () : BlockOutcome ρ μ Unit)
            else checkInputsWith E spend ctx.height flags index tx coins) with
        | rejected e => simp [h1] at h
        | unsupported u => simp [h1] at h
        | ok u =>
          simp only [h1] at h
          obtain ⟨_, h⟩ := ConnectEmbedding.ite_ofError_ok h
          cases h
          rfl

/--
Let the script loops of two spend checks, and two transaction tests, agree on each transaction of the list with the coins of its inputs in `coinsBefore` at its index.
Then `connectTransactionsWith` gives the same outcome for both.
-/
theorem connectTransactionsWith_congr {test₁ test₂ : TxTest ρ μ} {ctx : ConnectContext} {flags : UInt32} :
    ∀ {txs : List Transaction} {index : Nat} {st : ConnectState},
      (∀ i tx, txs[i]? = some tx → tx.isCoinBase = false → ∀ coins,
        lookupInputs (coinsBefore st.coins ctx.height txs i) tx.inputs.val = some coins →
          checkInputScriptsWith E spend₁ flags (index + i) tx 0 coins =
            checkInputScriptsWith E spend₂ flags (index + i) tx 0 coins) →
      (∀ i tx, txs[i]? = some tx → tx.isCoinBase = false → ∀ coins,
        lookupInputs (coinsBefore st.coins ctx.height txs i) tx.inputs.val = some coins →
          test₁ (index + i) tx coins = test₂ (index + i) tx coins) →
      connectTransactionsWith E spend₁ test₁ ctx flags index st txs =
        connectTransactionsWith E spend₂ test₂ ctx flags index st txs
  | [], _, _, _, _ => rfl
  | tx :: rest, index, st, h, htest => by
    unfold connectTransactionsWith
    rw [← connectTransactionWith_congr (E := E) (spend₁ := spend₁) (spend₂ := spend₂) (test₁ := test₁)
      (test₂ := test₂)
      (fun hcb coins hl => by simpa using h 0 tx rfl hcb coins (by simpa [coinsBefore] using hl))
      (fun hcb coins hl => by simpa using htest 0 tx rfl hcb coins (by simpa [coinsBefore] using hl))]
    cases h1 : connectTransactionWith E spend₁ test₁ ctx flags index st tx with
    | rejected e => rfl
    | unsupported u => rfl
    | ok st1 =>
      simp only
      have hidx : ∀ i, index + 1 + i = index + (i + 1) := fun i => by omega
      apply connectTransactionsWith_congr
      · intro i t hi hcb coins hl
        rw [hidx]
        exact h (i + 1) t (by simpa using hi) hcb coins
          (by simpa [coinsBefore, connectTransactionWith_ok_coins h1] using hl)
      · intro i t hi hcb coins hl
        rw [hidx]
        exact htest (i + 1) t (by simpa using hi) hcb coins
          (by simpa [coinsBefore, connectTransactionWith_ok_coins h1] using hl)

end Congruence

/--
Congruence in the revision.
Take two revisions with one error type, a value of `active`, and a block on a coin set.
Let three conditions hold:

1. The two spend checks agree on every spend of the block, for every flag set.
2. The two revisions give one flag set at the height of the block.
3. The two transaction tests agree on every transaction of the block that is not a coinbase, with the coins of its inputs.

A spend of the block is an input of a transaction that is not a coinbase, with the coin of its outpoint in the set just before its transaction (`coinsBefore`).
Then `connectBlockWith` gives the same outcome for both revisions.
-/
theorem connectBlockWith_congr_revision (E : ConnectEmbedding ε υ ρ μ) {rev₁ rev₂ : BlockRevision ε υ ρ μ}
    {active : Bool} (fJustCheck : Bool) {ctx : ConnectContext} {s : CoinSet} {b : Block}
    (hspend : ∀ i tx, b.transactions[i]? = some tx → tx.isCoinBase = false → ∀ ictx : InputContext, ictx.tx = tx →
      ∀ c, (coinsBefore s ctx.height b.transactions i).coin ictx.input.prevout = some c → ∀ f,
        rev₁.spend active ictx c.out.scriptPubKey f = rev₂.spend active ictx c.out.scriptPubKey f)
    (hflags : rev₁.scriptFlags active ctx.height = rev₂.scriptFlags active ctx.height)
    (htest : ∀ i tx, b.transactions[i]? = some tx → tx.isCoinBase = false → ∀ coins,
      lookupInputs (coinsBefore s ctx.height b.transactions i) tx.inputs.val = some coins →
        rev₁.txTest active ctx.height i tx coins = rev₂.txTest active ctx.height i tx coins) :
    connectBlockWith E rev₁ active fJustCheck ctx s b = connectBlockWith E rev₂ active fJustCheck ctx s b := by
  have key : connectTransactionsWith E (rev₁.spend active) (rev₁.txTest active ctx.height) ctx
      (rev₁.scriptFlags active ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions =
        connectTransactionsWith E (rev₂.spend active) (rev₂.txTest active ctx.height) ctx
          (rev₂.scriptFlags active ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions := by
    rw [← hflags]
    apply connectTransactionsWith_congr
    · intro i tx hi hcb coins hl
      apply checkInputScriptsWith_congr
      intro j coin hj ictx hic f
      obtain ⟨input, hin, hcoin⟩ := lookupInputs_getElem? hl j coin hj
      obtain ⟨htx, hinp⟩ := inputContext?_some (by simpa using hic)
      have hinput : input = ictx.input := by
        rw [hin] at hinp
        exact Option.some.inj hinp
      exact hspend i tx hi hcb ictx htx coin (by rw [← hinput]; exact hcoin) f
    · intro i tx hi hcb coins hl
      simpa using htest i tx hi hcb coins hl
  simp only [connectBlockWith, key]

/-! ## `validateBlockWith` -/

/-- `ValidateEmbedding.ofError` never accepts. -/
theorem ValidateEmbedding.ofError_ne_ok {α : Type} (V : ValidateEmbedding ρ μ ρ' μ') (e : ValidateError) (a : α) :
    (V.ofError e : BlockOutcome ρ' μ' α) ≠ .ok a := by
  unfold ValidateEmbedding.ofError
  split <;> simp

/-- A mapped outcome accepts exactly when the outcome accepts, with the same result. -/
theorem BlockOutcome.map_eq_ok {α : Type} {f : ρ → ρ'} {g : μ → μ'} {o : BlockOutcome ρ μ α} {a : α} :
    o.map f g = .ok a ↔ o = .ok a := by
  cases o <;> simp [BlockOutcome.map]

/-- With the baseline embeddings, `toExcept` of the embedded result of a `validateBlock` call is that result. -/
theorem ValidateEmbedding.toExcept_ofBaseline {α : Type} (r : Except ValidateError α) :
    (ValidateEmbedding.baseline.ofBaseline ConnectEmbedding.baseline id id r).toExcept = r := by
  rcases r with e | a
  · cases e
    case connect e =>
      have h := ConnectEmbedding.toExcept_ofBaseline (α := α) (.error e)
      simp only [ConnectEmbedding.ofBaseline] at h
      simp only [ValidateEmbedding.ofBaseline, ValidateEmbedding.baseline]
      cases h' : (ConnectEmbedding.baseline.ofBaselineError id id e : BlockOutcome _ _ α) with
      | ok a => simp [h', BlockOutcome.toExcept] at h
      | rejected e' =>
        simp only [h', BlockOutcome.toExcept, Except.error.injEq] at h
        simp [BlockOutcome.map, BlockOutcome.toExcept, h]
      | unsupported e' =>
        simp only [h', BlockOutcome.toExcept, Except.error.injEq] at h
        simp [BlockOutcome.map, BlockOutcome.toExcept, h]
    all_goals
      simp only [ValidateEmbedding.ofBaseline, ValidateEmbedding.ofError, ValidateEmbedding.baseline, id]
      split <;> rfl
  · rfl

open Lean Elab Term in
/--
`definition_value% c` is the stored value of the definition `c`, which must have no universe parameters.
`validateBlock_value` uses it to state the unfolding of `validateBlock` with the terms of the definition itself.
-/
elab "definition_value% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let .defnInfo d ← Lean.getConstInfo n | throwError "{n} is not a definition"
  unless d.levelParams.isEmpty do throwError "{n} has universe parameters"
  return d.value

/--
`validateBlock` equals its stored value, as a function.
A proof rewrites with this theorem in place of `unfold validateBlock`.
The kernel compares the two sides of an unfolding. With `unfold`, it reduces the genesis test of the body, which does not end in practical time.
Here the two sides are one term, so the kernel reduces nothing.
-/
theorem validateBlock_value : validateBlock = definition_value% validateBlock := Eq.refl _

/-- `validateBlock` is `checksBeforeConnect` with the lock-time arguments of the context, and then `connectBlock`, with its error under `ValidateError.connect`. -/
theorem validateBlock_eq_checks (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool)
    (ctx : ValidateContext) (s : CoinSet) (b : Block) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b =
      match checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (baselineLockTimeArgs ctx) b with
      | .error e => .error e
      | .ok () =>
        match connectBlock verify true (connectContextOf ctx b) s b with
        | .error e => .error (.connect e)
        | .ok result => .ok result := by
  generalize hr : validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = r
  generalize hc : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (baselineLockTimeArgs ctx) b = c
  rw [validateBlock_value] at hr
  unfold checksBeforeConnect baselineLockTimeArgs at hc
  simp only at hr hc
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !fCheckPOW) = true
    then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = x1 at hr hc
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = x2 at hr hc
  generalize checkBlock WorkNetwork.mainnet fCheckPOW fCheckMerkleRoot b = x3 at hr hc
  generalize contextualCheckBlockBody ctx.height ctx.prevMedianTimePast ctx.csvActive ctx.segwitActive b = x4
    at hr hc
  subst hr hc
  rcases x1 with e | ⟨⟩
  · rfl
  rcases x2 with e | ⟨⟩
  · rfl
  rcases x3 with e | ⟨⟩
  · rfl
  rcases x4 with e | ⟨⟩
  · rfl
  rfl

/-- `checksBeforeConnect` never returns an error of `ConnectBlock`, for any lock-time arguments. -/
theorem checksBeforeConnect_ne_connect {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext}
    {args : Bool × Int} {b : Block} {e : ConnectBlockError} :
    checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx args b ≠ .error (.connect e) := by
  intro hc
  unfold checksBeforeConnect at hc
  simp only at hc
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !fCheckPOW) = true
    then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = x1 at hc
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = x2 at hc
  generalize checkBlock WorkNetwork.mainnet fCheckPOW fCheckMerkleRoot b = x3 at hc
  generalize contextualCheckBlockBody ctx.height args.2 args.1 ctx.segwitActive b = x4 at hc
  rcases x1 with e | ⟨⟩
  · cases hc
  rcases x2 with e | ⟨⟩
  · cases hc
  rcases x3 with e | ⟨⟩
  · cases hc
  rcases x4 with e | ⟨⟩
  · cases hc
  cases hc

/--
The contextual header check of `checksBeforeConnect`, with its genesis case.
`validateBlock` skips `ContextualCheckBlockHeader` for a header with the hash of the mainnet genesis block.
-/
def contextualHeaderPassed (ctx : ValidateContext) (b : Block) : Prop :=
  (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = .ok ()

/--
`checksBeforeConnect` reads its lock-time arguments through `contextualCheckBlockBody` alone, and only after the contextual header check passes.
Take two pairs of arguments that give one body result whenever that check passes (`contextualHeaderPassed`).
Then they give one result of `checksBeforeConnect`.
-/
theorem checksBeforeConnect_congr_body {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext}
    {args args' : Bool × Int} {b : Block}
    (h : contextualHeaderPassed ctx b → contextualCheckBlockBody ctx.height args.2 args.1 ctx.segwitActive b =
      contextualCheckBlockBody ctx.height args'.2 args'.1 ctx.segwitActive b) :
    checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx args b =
      checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx args' b := by
  unfold contextualHeaderPassed at h
  unfold checksBeforeConnect
  simp only
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !fCheckPOW) = true
    then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = x1
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = x2 at h ⊢
  rcases x1 with e | ⟨⟩
  · simp only [checkStep]
  rcases x2 with e | ⟨⟩
  · simp only [checkStep]
  simp only [checkStep, h rfl]

/--
`checksBeforeConnect` after its first three checks, without the proof-of-work check.
Take a block whose header does not have the genesis hash, whose contextual header check passes and whose `CheckBlock` passes without `fCheckPOW`.
Then `checksBeforeConnect` is the result of `contextualCheckBlockBody` with the lock-time arguments, under `ValidateError.contextualBody`.
A proof of a concrete block uses this theorem to evaluate each check alone.
-/
theorem checksBeforeConnect_eq_body {fCheckMerkleRoot : Bool} {ctx : ValidateContext} {args : Bool × Int} {b : Block}
    (hg : (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = false)
    (hh : contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight = .ok ())
    (hcb : checkBlock WorkNetwork.mainnet false fCheckMerkleRoot b = .ok ()) :
    checksBeforeConnect false fCheckMerkleRoot ctx args b =
      checkStep .contextualBody (contextualCheckBlockBody ctx.height args.2 args.1 ctx.segwitActive b)
        fun _ => .ok () := by
  have h1 : (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !false) = true
      then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = .ok () := by
    simp only [Bool.not_false, Bool.or_true, ↓reduceIte]
  have h2 : (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
      else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
        ctx.lastCheckpointHeight) = .ok () := by
    rw [hg]
    exact hh
  unfold checksBeforeConnect
  simp only
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !false) = true
    then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = x1 at h1 ⊢
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = x2 at h2 ⊢
  generalize checkBlock WorkNetwork.mainnet false fCheckMerkleRoot b = x3 at hcb ⊢
  subst h1 h2 hcb
  simp only [checkStep]

/--
Acceptance of the four checks moves to a later lock-time cutoff.
Suppose that, whenever the contextual header check passes, the cutoff of `args` is at most the cutoff of `args'`.
If `checksBeforeConnect` accepts the block with `args`, it accepts the block with `args'`.
The header check runs before the body check, so the hypothesis can use its result.
-/
theorem checksBeforeConnect_ok_of_cutoff {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext}
    {args args' : Bool × Int} {b : Block}
    (hcut : contextualHeaderPassed ctx b → lockTimeCutoff args b ≤ lockTimeCutoff args' b)
    (h : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx args b = .ok ()) :
    checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx args' b = .ok () := by
  unfold contextualHeaderPassed at hcut
  unfold checksBeforeConnect at h ⊢
  simp only at h ⊢
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet || !fCheckPOW) = true
    then Except.ok () else checkBlockHeader WorkNetwork.mainnet b.header) = x1 at h ⊢
  generalize (if (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true then Except.ok ()
    else contextualCheckBlockHeader WorkNetwork.mainnet b.header.pure ctx.view ctx.adjustedTime
      ctx.lastCheckpointHeight) = x2 at h hcut ⊢
  generalize checkBlock WorkNetwork.mainnet fCheckPOW fCheckMerkleRoot b = x3 at h ⊢
  rcases x1 with e | ⟨⟩
  · cases h
  rcases x2 with e | ⟨⟩
  · cases h
  rcases x3 with e | ⟨⟩
  · cases h
  simp only [checkStep] at h ⊢
  cases hb : contextualCheckBlockBody ctx.height args.2 args.1 ctx.segwitActive b with
  | error e => simp [hb] at h
  | ok u =>
    cases u
    rw [contextualCheckBlockBody_cutoff_mono (hcut rfl) hb]

/--
`validateBlockWithActive` reads the revision through `contextualBodyWith` and `connectBlockWith` alone.
Take two revisions and two values of `active`.
Let `contextualBodyWith` give one result for both whenever the contextual header check passes, and let `connectBlockWith` give one result for both.
Then `validateBlockWithActive` gives one result for both.
-/
theorem validateBlockWithActive_congr (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    {rev₁ rev₂ : BlockRevision ε υ ρ μ} {act₁ act₂ : Bool} (fCheckPOW fCheckMerkleRoot : Bool)
    {ctx : ValidateContext} {s : CoinSet} {b : Block}
    (hbody : contextualHeaderPassed ctx b → contextualBodyWith rev₁ act₁ ctx b = contextualBodyWith rev₂ act₂ ctx b)
    (h : connectBlockWith E rev₁ act₁ true (connectContextOf ctx b) s b =
      connectBlockWith E rev₂ act₂ true (connectContextOf ctx b) s b) :
    validateBlockWithActive V E rev₁ act₁ fCheckPOW fCheckMerkleRoot ctx s b =
      validateBlockWithActive V E rev₂ act₂ fCheckPOW fCheckMerkleRoot ctx s b := by
  unfold validateBlockWithActive
  rw [h, checksBeforeConnect_congr_body hbody]

/--
For every pair of embeddings, error map, map of unsupported reasons, verifier, value of `active`, pair of flags, context, coin set and block:
`validateBlockWithActive` with the baseline revision equals the embedded result of `validateBlock`.
-/
theorem validateBlockWithActive_ofBaseline (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    (embed : ScriptError → ε) (embedU : Unsupported → υ) (verify : SignatureVerifier) (active : Bool)
    (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (s : CoinSet) (b : Block) :
    validateBlockWithActive V E (.baseline embed embedU verify) active fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  rw [validateBlock_eq_checks]
  unfold validateBlockWithActive
  rw [connectBlockWith_ofBaseline]
  simp only [BlockRevision.baseline]
  cases hc : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (baselineLockTimeArgs ctx) b with
  | error e =>
    cases e
    case connect e => exact absurd hc checksBeforeConnect_ne_connect
    all_goals rfl
  | ok u =>
    cases connectBlock verify true (connectContextOf ctx b) s b <;> rfl

/--
For every pair of embeddings, error map, map of unsupported reasons, verifier, activation, pair of flags, context, coin set and block:
`validateBlockWith` with the baseline revision equals the embedded result of `validateBlock`.
-/
theorem validateBlockWith_ofBaseline (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    (embed : ScriptError → ε) (embedU : Unsupported → υ) (verify : SignatureVerifier) (a : Activation)
    (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (s : CoinSet) (b : Block) :
    validateBlockWith V E (.baseline embed embedU verify) a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWithActive_ofBaseline V E embed embedU verify _ fCheckPOW fCheckMerkleRoot ctx s b

/--
Acceptance moves from one revision to another, for `validateBlockWithActive`.
Take the three conditions of `connectBlockWith_ok_of` at the height of the block.
Let the four checks before `ConnectBlock` accept with the lock-time arguments of `rev₂` whenever they accept with those of `rev₁`.
If `validateBlockWithActive` accepts a block with `rev₁`, it accepts the block with `rev₂`, with the same coin set and the same changes.
-/
theorem validateBlockWithActive_ok_of {ε₁ υ₁ ρ₁ μ₁ ρ₁' μ₁' ε₂ υ₂ ρ₂ μ₂ ρ₂' μ₂' : Type}
    {V₁ : ValidateEmbedding ρ₁ μ₁ ρ₁' μ₁'} {E₁ : ConnectEmbedding ε₁ υ₁ ρ₁ μ₁}
    {V₂ : ValidateEmbedding ρ₂ μ₂ ρ₂' μ₂'} {E₂ : ConnectEmbedding ε₂ υ₂ ρ₂ μ₂}
    {rev₁ : BlockRevision ε₁ υ₁ ρ₁ μ₁} {rev₂ : BlockRevision ε₂ υ₂ ρ₂ μ₂} {active : Bool}
    {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (hacc : ∀ ictx spk, rev₁.spend active ictx spk (rev₁.scriptFlags active ctx.height) = .accepted →
      rev₂.spend active ictx spk (rev₂.scriptFlags active ctx.height) = .accepted)
    (hp2sh : hasFlag (rev₁.scriptFlags active ctx.height) ScriptFlags.p2sh =
      hasFlag (rev₂.scriptFlags active ctx.height) ScriptFlags.p2sh)
    (htest : ∀ index tx coins, rev₁.txTest active ctx.height index tx coins = .ok () →
      rev₂.txTest active ctx.height index tx coins = .ok ())
    (hchecks : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (rev₁.lockTimeArgs active ctx b) b = .ok () →
      checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (rev₂.lockTimeArgs active ctx b) b = .ok ())
    (h : validateBlockWithActive V₁ E₁ rev₁ active fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlockWithActive V₂ E₂ rev₂ active fCheckPOW fCheckMerkleRoot ctx s b = .ok r := by
  unfold validateBlockWithActive at h ⊢
  cases hc : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (rev₁.lockTimeArgs active ctx b) b with
  | error e =>
    rw [hc] at h
    exact absurd h (V₁.ofError_ne_ok _ _)
  | ok u =>
    cases u
    rw [hc] at h
    rw [hchecks hc]
    simp only [ValidateEmbedding.afterChecks, BlockOutcome.map_eq_ok] at h ⊢
    exact connectBlockWith_ok_of (ctx := connectContextOf ctx b) hacc hp2sh htest h

/--
`connectBlockWith` keeps the result `csvActive` of `connectBlock`.
Suppose that it accepts a block in a context with `csvActive` true.
Then the header of the block has the hash of the mainnet genesis block, for which `ConnectBlock` connects no transaction.
-/
theorem connectBlockWith_ok_genesis_of_csvActive {E : ConnectEmbedding ε υ ρ μ} {rev : BlockRevision ε υ ρ μ}
    {active fJustCheck : Bool} {ctx : ConnectContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : connectBlockWith E rev active fJustCheck ctx s b = .ok r) (hcsv : ctx.csvActive = true) :
    (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = true := by
  unfold connectBlockWith at h
  cases hcb : checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | error e =>
    simp only [hcb] at h
    exact absurd h (E.ofError_ne_ok _ _)
  | ok u =>
    simp only [hcb] at h
    cases hg : (some b.header.pure.getHash == genesisHash? .mainnet) with
    | true => rfl
    | false =>
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
      cases h30 : (enforceBip30 ctx.bip34Ancestor && b.transactions.any (fun tx => s.haveUnspent tx.txid)) with
      | true =>
        simp only [h30, ↓reduceIte] at h
        exact absurd h (E.ofError_ne_ok _ _)
      | false =>
        simp only [h30, Bool.false_eq_true, ↓reduceIte, hcsv] at h
        exact absurd h (E.ofError_ne_ok _ _)

/-- If `validateBlockWithActive` accepts a block, its `connectBlockWith` call accepts the block with the same result. -/
theorem validateBlockWithActive_ok_connect {V : ValidateEmbedding ρ μ ρ' μ'} {E : ConnectEmbedding ε υ ρ μ}
    {rev : BlockRevision ε υ ρ μ} {active fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet}
    {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E rev active fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    connectBlockWith E rev active true (connectContextOf ctx b) s b = .ok r := by
  unfold validateBlockWithActive at h
  cases hc : checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (rev.lockTimeArgs active ctx b) b with
  | error e =>
    rw [hc] at h
    exact absurd h (V.ofError_ne_ok _ _)
  | ok u =>
    cases u
    rw [hc] at h
    simpa only [ValidateEmbedding.afterChecks, BlockOutcome.map_eq_ok] using h

/-! ## The targets of design record 0011, section 10.1, with the extensions of design record 0012 -/

/--
The target `connectBlockWith_baseline` of design record 0011, section 10.1, and of design record 0012, section 9.1.
For every verifier, value of `active`, flag `fJustCheck`, context, coin set and block:
`connectBlockWith` with the baseline revision and the baseline error type equals `connectBlock`.
The baseline revision has the baseline spend check, the baseline script flags and the transaction test that accepts everything.
The baseline error type is `ConnectEmbedding.baseline`, and `toExcept` only changes the name of the result type.
`connectBlockWith_ofBaseline` is the same agreement for every embedding.
The statement holds for a context with `csvActive` true too. Both sides then give the result `csvActive` when they reach the test of that field.
-/
theorem connectBlockWith_baseline (verify : SignatureVerifier) (active fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) :
    (connectBlockWith ConnectEmbedding.baseline (.baseline id id verify) active fJustCheck ctx s b).toExcept =
      connectBlock verify fJustCheck ctx s b := by
  rw [connectBlockWith_ofBaseline, ConnectEmbedding.toExcept_ofBaseline]

/--
For every verifier, activation, pair of flags, context, coin set and block:
`validateBlockWith` with the baseline revision and the baseline error types equals `validateBlock`.
`validateBlockWith_ofBaseline` is the same agreement for every pair of embeddings.
-/
theorem validateBlockWith_baseline (verify : SignatureVerifier) (a : Activation) (fCheckPOW fCheckMerkleRoot : Bool)
    (ctx : ValidateContext) (s : CoinSet) (b : Block) :
    (validateBlockWith ValidateEmbedding.baseline ConnectEmbedding.baseline (.baseline id id verify) a fCheckPOW
      fCheckMerkleRoot ctx s b).toExcept = validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b := by
  rw [validateBlockWith_ofBaseline, ValidateEmbedding.toExcept_ofBaseline]

/--
The inactive equality of a revision: with `active` false, each part has its baseline value.
The spend check equals the embedded result of `verifyLegacySpend`, for every input, script and flag set.
The script flags, the transaction test and the lock-time arguments are those of the baseline (extensions E1 to E3 of design record 0012).
-/
structure BlockRevision.InactiveBaseline (rev : BlockRevision ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) (verify : SignatureVerifier) : Prop where
  /-- The spend check with `active` false is the embedded `verifyLegacySpend`. -/
  spend : ∀ ictx spk f, rev.spend false ictx spk f = .ofBaseline embed embedU (verifyLegacySpend ictx spk f verify)
  /-- The script flags with `active` false are `connectScriptFlags`. -/
  scriptFlags : ∀ height, rev.scriptFlags false height = connectScriptFlags height
  /-- The transaction test with `active` false accepts every transaction. -/
  txTest : ∀ height index tx coins, rev.txTest false height index tx coins = .ok ()
  /-- The lock-time arguments with `active` false are those of the context. -/
  lockTimeArgs : ∀ ctx b, rev.lockTimeArgs false ctx b = baselineLockTimeArgs ctx

/-- The baseline revision has the inactive equality. -/
theorem BlockRevision.baseline_inactiveBaseline (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (verify : SignatureVerifier) :
    (BlockRevision.baseline embed embedU verify : BlockRevision ε υ ρ μ).InactiveBaseline embed embedU verify :=
  ⟨fun _ _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩

/--
Take a revision with the inactive equality (`BlockRevision.InactiveBaseline`).
Then `connectBlockWith` with `active` false equals the embedded result of `connectBlock`.
For every embedding, flag `fJustCheck`, context, coin set and block.
-/
theorem connectBlockWith_inactive (E : ConnectEmbedding ε υ ρ μ) {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ} (hin : rev.InactiveBaseline embed embedU verify)
    (fJustCheck : Bool) (ctx : ConnectContext) (s : CoinSet) (b : Block) :
    connectBlockWith E rev false fJustCheck ctx s b =
      E.ofBaseline embed embedU (connectBlock verify fJustCheck ctx s b) := by
  rw [← connectBlockWith_ofBaseline E embed embedU verify false]
  exact connectBlockWith_congr_revision E fJustCheck
    (fun _ _ _ _ ictx _ c _ f => hin.spend ictx c.out.scriptPubKey f) (hin.scriptFlags _)
    (fun _ _ _ _ _ _ => hin.txTest _ _ _ _)

/--
Take a revision with the inactive equality.
Then `validateBlockWithActive` with `active` false equals the embedded result of `validateBlock`: every acceptance, each rejection and each result outside the model agrees.
For every pair of embeddings, pair of flags, context, coin set and block.
-/
theorem validateBlockWithActive_inactive (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    {embed : ScriptError → ε} {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    (hin : rev.InactiveBaseline embed embedU verify) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) :
    validateBlockWithActive V E rev false fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  rw [← validateBlockWithActive_ofBaseline V E embed embedU verify false]
  apply validateBlockWithActive_congr
  · intro _
    simp only [contextualBodyWith, hin.lockTimeArgs, BlockRevision.baseline]
  · rw [connectBlockWith_inactive E hin, connectBlockWith_ofBaseline]

/--
The target `validateBlockWith_inactive` of design record 0011, section 10.1, and of design record 0012, section 9.1.
Take a revision with the inactive equality: with `active` false, its spend check and its values of E1 to E3 are those of the baseline.
Let the activation be inactive on mainnet at the height of the block.
Then `validateBlockWith` equals the embedded result of `validateBlock`: every acceptance, each rejection and each result outside the model agrees.
For every pair of embeddings, pair of flags, context, coin set and block.
`validateBlockWith_inactive_of_lt` and `validateBlockWith_inactive_of_none` give the two cases of an inactive height.
-/
theorem validateBlockWith_inactive (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    {embed : ScriptError → ε} {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    (hin : rev.InactiveBaseline embed embedU verify)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext}
    (hact : a.isActive .mainnet ctx.height = false) (s : CoinSet) (b : Block) :
    validateBlockWith V E rev a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  unfold validateBlockWith
  rw [hact]
  exact validateBlockWithActive_inactive V E hin fCheckPOW fCheckMerkleRoot ctx s b

/-- `validateBlockWith_inactive` for a block below the activation height `h₀` of mainnet. -/
theorem validateBlockWith_inactive_of_lt (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    {embed : ScriptError → ε} {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    (hin : rev.InactiveBaseline embed embedU verify)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) {ctx : ValidateContext} {h₀ : Nat}
    (hheight : a.height .mainnet = some h₀) (hlt : ctx.height < h₀) (s : CoinSet) (b : Block) :
    validateBlockWith V E rev a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E hin fCheckPOW fCheckMerkleRoot (Activation.isActive_lt hheight hlt) s b

/-- `validateBlockWith_inactive` for an activation with no activation height on mainnet, at every height. -/
theorem validateBlockWith_inactive_of_none (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    {embed : ScriptError → ε} {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    (hin : rev.InactiveBaseline embed embedU verify)
    {a : Activation} (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (hnone : a.height .mainnet = none) (s : CoinSet) (b : Block) :
    validateBlockWith V E rev a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) :=
  validateBlockWith_inactive V E hin fCheckPOW fCheckMerkleRoot (Activation.none_inactive hnone ctx.height) s b

/--
The target `connectBlockWith_restricts` of design record 0011, section 10.1, with conditions 1 to 3 of design record 0012, section 6.4.
Take a revision, a value of `active` and a context, with the script flags `f` of the revision at the height of the context.

1. If the spend check of the revision accepts an input under `f`, `verifyLegacySpend` accepts it under `connectScriptFlags`.
2. `f` and `connectScriptFlags` agree on `SCRIPT_VERIFY_P2SH`.
3. The baseline has no transaction test, so every transaction test meets the third condition.

If `connectBlockWith` accepts a block on a coin set, `connectBlock` accepts it on that set, with the same coin set and the same changes.
For every embedding, flag `fJustCheck`, coin set and block.
The hypothesis reads the first run of each script check alone.
The statement needs no hypothesis on `csvActive` of the context: with `csvActive` true, `connectBlockWith` accepts no block that reaches the test of that field.
-/
theorem connectBlockWith_restricts {E : ConnectEmbedding ε υ ρ μ} {verify : SignatureVerifier}
    {rev : BlockRevision ε υ ρ μ} {active : Bool} {ctx : ConnectContext}
    (hspend : ∀ ictx spk, rev.spend active ictx spk (rev.scriptFlags active ctx.height) = .accepted →
      verifyLegacySpend ictx spk (connectScriptFlags ctx.height) verify = .accepted)
    (hp2sh : hasFlag (rev.scriptFlags active ctx.height) ScriptFlags.p2sh =
      hasFlag (connectScriptFlags ctx.height) ScriptFlags.p2sh)
    {fJustCheck : Bool} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : connectBlockWith E rev active fJustCheck ctx s b = .ok r) : connectBlock verify fJustCheck ctx s b = .ok r := by
  have h2 : connectBlockWith ConnectEmbedding.baseline (.baseline id id verify) active fJustCheck ctx s b = .ok r :=
    connectBlockWith_ok_of (rev₂ := .baseline id id verify)
      (fun ictx spk hacc => by
        simp [BlockRevision.baseline, baselineSpendCheck, hspend ictx spk hacc, VerifyOutcome.ofBaseline])
      hp2sh (fun _ _ _ _ => rfl) h
  have h3 := connectBlockWith_baseline verify active fJustCheck ctx s b
  rw [h2] at h3
  exact h3.symm

/--
The target `validateBlockWith_restricts` of design record 0012, section 9.1, for one value of `active`.
Take conditions 1 and 2 of `connectBlockWith_restricts` at the height of the block.
Take condition 4 of design record 0012, section 6.4, for the block.
When the contextual header check passes (`contextualHeaderPassed`), the lock-time cutoff of the revision is at most the cutoff of the baseline.
If `validateBlockWithActive` accepts a block, `validateBlock` accepts it, with the same coin set and the same changes.
For every pair of embeddings, pair of flags, context and coin set.
-/
theorem validateBlockWithActive_restricts {V : ValidateEmbedding ρ μ ρ' μ'} {E : ConnectEmbedding ε υ ρ μ}
    {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ} {active : Bool} {ctx : ValidateContext} {b : Block}
    (hspend : ∀ ictx spk, rev.spend active ictx spk (rev.scriptFlags active ctx.height) = .accepted →
      verifyLegacySpend ictx spk (connectScriptFlags ctx.height) verify = .accepted)
    (hp2sh : hasFlag (rev.scriptFlags active ctx.height) ScriptFlags.p2sh =
      hasFlag (connectScriptFlags ctx.height) ScriptFlags.p2sh)
    (hcut : contextualHeaderPassed ctx b →
      lockTimeCutoff (rev.lockTimeArgs active ctx b) b ≤ lockTimeCutoff (baselineLockTimeArgs ctx) b)
    {fCheckPOW fCheckMerkleRoot : Bool} {s : CoinSet} {r : ConnectResult}
    (h : validateBlockWithActive V E rev active fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r := by
  have h2 : validateBlockWithActive ValidateEmbedding.baseline ConnectEmbedding.baseline (.baseline id id verify)
      active fCheckPOW fCheckMerkleRoot ctx s b = .ok r :=
    validateBlockWithActive_ok_of (rev₂ := .baseline id id verify)
      (fun ictx spk hacc => by
        simp [BlockRevision.baseline, baselineSpendCheck, hspend ictx spk hacc, VerifyOutcome.ofBaseline])
      hp2sh (fun _ _ _ _ => rfl) (checksBeforeConnect_ok_of_cutoff hcut) h
  have h3 := validateBlockWithActive_ofBaseline ValidateEmbedding.baseline ConnectEmbedding.baseline id id verify
    active fCheckPOW fCheckMerkleRoot ctx s b
  rw [h2] at h3
  have h4 := ValidateEmbedding.toExcept_ofBaseline (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b)
  rw [← h3] at h4
  exact h4.symm

/--
The target `validateBlockWith_restricts` of design record 0012, section 9.1.
Take a revision that restricts the baseline at every height (design record 0012, section 6.4):

1. If its spend check accepts an input under its script flags, `verifyLegacySpend` accepts the input under `connectScriptFlags`.
2. Its script flags and `connectScriptFlags` agree on `SCRIPT_VERIFY_P2SH`.
3. The baseline has no transaction test, so every transaction test meets the third condition.
4. When the contextual header check of a block passes, the lock-time cutoff of the revision is at most the cutoff of the baseline.

If `validateBlockWith` accepts a block, `validateBlock` accepts it, with the same coin set and the same changes.
For every pair of embeddings, activation, pair of flags, context and coin set.
A revision of Script alone has the baseline flags and the baseline lock-time arguments, so it meets conditions 2 and 4 by reflexivity.
-/
theorem validateBlockWith_restricts {V : ValidateEmbedding ρ μ ρ' μ'} {E : ConnectEmbedding ε υ ρ μ}
    {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    (hspend : ∀ active height ictx spk, rev.spend active ictx spk (rev.scriptFlags active height) = .accepted →
      verifyLegacySpend ictx spk (connectScriptFlags height) verify = .accepted)
    (hp2sh : ∀ active height, hasFlag (rev.scriptFlags active height) ScriptFlags.p2sh =
      hasFlag (connectScriptFlags height) ScriptFlags.p2sh)
    (hcut : ∀ active ctx b, contextualHeaderPassed ctx b →
      lockTimeCutoff (rev.lockTimeArgs active ctx b) b ≤ lockTimeCutoff (baselineLockTimeArgs ctx) b)
    {a : Activation} {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block}
    {r : ConnectResult} (h : validateBlockWith V E rev a fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r :=
  validateBlockWithActive_restricts (hspend _ _) (hp2sh _ _) (hcut _ _ _) h

/-! ## Congruence for a revision of Script instructions -/

/--
`verifyScriptWith_congr` with the redeem-script hypothesis only where the P2SH evaluation can run.
Take two steps that agree on every instruction whose opcode is not in `O`.
Let `scriptSig` and `scriptPubKey` have no instruction in `O`.
Let `scriptPubKey` be pay-to-script-hash and `scriptSig` push-only. Then let each top item of a final stack of `scriptSig` with `step₁`, read as a script, have no instruction in `O`.
Then the two `verifyScriptWith` calls give the same result, for every error map, map of unsupported reasons and flag set.
-/
theorem verifyScriptWith_congr_p2sh {O : UInt8 → Bool} {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {step₁ step₂ : Step ε υ}
    (hstep : ∀ script s i, O i.opcode = false → step₁ script s i = step₂ script s i) (flags : UInt32)
    {scriptSig scriptPubKey : List UInt8} (hsig : opcodeFree O scriptSig = true)
    (hpub : opcodeFree O scriptPubKey = true)
    (hredeem : isPayToScriptHash scriptPubKey = true → isPushOnly scriptSig = true → ∀ s redeem rest,
      evalScriptWith embed embedU step₁ flags scriptSig [] = .ok s →
        s.stack.reverse = redeem :: rest → opcodeFree O redeem = true) :
    verifyScriptWith embed embedU step₁ flags scriptSig scriptPubKey =
      verifyScriptWith embed embedU step₂ flags scriptSig scriptPubKey := by
  unfold verifyScriptWith
  rw [← evalScriptWith_congr (hstep scriptSig) flags [] hsig]
  cases hs : evalScriptWith embed embedU step₁ flags scriptSig [] with
  | rejected e => rfl
  | unsupported u => rfl
  | ok s =>
    simp only
    rw [← evalScriptWith_congr (hstep scriptPubKey) flags s.stack hpub]
    cases hp : isPayToScriptHash scriptPubKey with
    | false => simp
    | true =>
      cases hpo : isPushOnly scriptSig with
      | false => simp
      | true =>
        rcases hsr : s.stack.reverse with _ | ⟨redeem, rest⟩
        · rfl
        · simp only [evalScriptWith_congr (hstep redeem) flags rest.reverse (hredeem hp hpo s redeem rest hs hsr)]

/--
No script of one spend holds an instruction in `O`.
The `scriptSig` and the spent `scriptPubKey` have no instruction with an opcode in `O`.
For a pay-to-script-hash `scriptPubKey` and a push-only `scriptSig`, the redeem script has none either.
The redeem script is the top item of the stack that the baseline evaluation of `scriptSig` leaves, under any flag set.
For a push-only `scriptSig`, that item is its last push.
-/
def SpendUntouched (O : UInt8 → Bool) (verify : SignatureVerifier) (ictx : InputContext)
    (prevScriptPubKey : Transaction.Script) : Prop :=
  opcodeFree O ictx.input.scriptSig.bytes.val = true ∧ opcodeFree O prevScriptPubKey.bytes.val = true ∧
    (isPayToScriptHash prevScriptPubKey.bytes.val = true → isPushOnly ictx.input.scriptSig.bytes.val = true →
      ∀ f s redeem rest,
        evalScript (some (transactionChecker ictx.tx ictx.index verify)) f ictx.input.scriptSig.bytes.val [] = .ok s →
          s.stack.reverse = redeem :: rest → opcodeFree O redeem = true)

/--
No spend of the block `b` on the coin set `s` holds an instruction in `O`.
A spend is an input of a transaction of `b` that is not a coinbase, with the coin of its outpoint in the set just before its transaction (`coinsBefore`, at the height `height`).
That coin is in `s`, or an earlier transaction of the block created it.
-/
def BlockUntouched (O : UInt8 → Bool) (verify : SignatureVerifier) (height : Nat) (s : CoinSet) (b : Block) : Prop :=
  ∀ i tx, b.transactions[i]? = some tx → tx.isCoinBase = false → ∀ ictx : InputContext, ictx.tx = tx →
    ∀ c, (coinsBefore s height b.transactions i).coin ictx.input.prevout = some c →
      SpendUntouched O verify ictx c.out.scriptPubKey

/--
A spend check that is `verifyScriptWith` with a revised step agrees with the baseline on an untouched spend.
Let the revised step agree with the baseline step on every instruction whose opcode is not in `O`.
Then on a spend with `SpendUntouched O`, the check equals the embedded result of `verifyLegacySpend`, for every flag set.
-/
theorem spend_eq_baseline_of_untouched {O : UInt8 → Bool} {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {verify : SignatureVerifier} {step : InputContext → UInt32 → Step ε υ}
    (hstep : ∀ ictx f script st i, O i.opcode = false → step ictx f script st i =
      baselineStep embed embedU (some (transactionChecker ictx.tx ictx.index verify)) f script st i)
    {ictx : InputContext} {spk : Transaction.Script} (hu : SpendUntouched O verify ictx spk) (f : UInt32) :
    verifyScriptWith embed embedU (step ictx f) f ictx.input.scriptSig.bytes.val spk.bytes.val =
      baselineSpendCheck embed embedU verify ictx spk f := by
  unfold baselineSpendCheck verifyLegacySpend
  rw [← verifyScriptWith_baseline embed embedU]
  refine verifyScriptWith_congr_p2sh (O := O) (hstep ictx f) f hu.1 hu.2.1 ?_
  intro hp hpo s redeem rest hs hsr
  rw [evalScriptWith_congr (hstep ictx f _) f [] hu.1, evalScriptWith_baseline] at hs
  refine hu.2.2 hp hpo f s redeem rest ?_ hsr
  cases he : evalScript (some (transactionChecker ictx.tx ictx.index verify)) f ictx.input.scriptSig.bytes.val [] with
  | ok s' =>
    rw [he] at hs
    simp only [EvalOutcome.ofBaseline, EvalOutcome.ok.injEq] at hs
    rw [hs]
  | rejected e => simp [he, EvalOutcome.ofBaseline] at hs
  | unsupported u => simp [he, EvalOutcome.ofBaseline] at hs

/--
Congruence for `connectBlockWith`, for a revision that redefines the instructions with an opcode in `O`.
Let the spend check of the revision, for the value `active`, be `verifyScriptWith` with a step that agrees with the baseline step on every instruction whose opcode is not in `O`.
Let the script flags of the revision at the height of the block be `connectScriptFlags`, and let its transaction test accept every transaction.
Take a block with `BlockUntouched O` on the coin set: no `scriptSig`, no spent `scriptPubKey` and no P2SH redeem script holds an instruction in `O`.
Then `connectBlockWith` equals the embedded result of `connectBlock`.
The equality covers both runs of each script check, because it holds for every flag set.
-/
theorem connectBlockWith_congr (E : ConnectEmbedding ε υ ρ μ) {O : UInt8 → Bool} {embed : ScriptError → ε}
    {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ} {active : Bool}
    {step : InputContext → UInt32 → Step ε υ} {ctx : ConnectContext}
    (hspend : ∀ ictx spk f, rev.spend active ictx spk f =
      verifyScriptWith embed embedU (step ictx f) f ictx.input.scriptSig.bytes.val spk.bytes.val)
    (hstep : ∀ ictx f script st i, O i.opcode = false → step ictx f script st i =
      baselineStep embed embedU (some (transactionChecker ictx.tx ictx.index verify)) f script st i)
    (hflags : rev.scriptFlags active ctx.height = connectScriptFlags ctx.height)
    (htest : ∀ index tx coins, rev.txTest active ctx.height index tx coins = .ok ())
    (fJustCheck : Bool) {s : CoinSet} {b : Block}
    (hfree : BlockUntouched O verify ctx.height s b) :
    connectBlockWith E rev active fJustCheck ctx s b =
      E.ofBaseline embed embedU (connectBlock verify fJustCheck ctx s b) := by
  rw [← connectBlockWith_ofBaseline E embed embedU verify active]
  refine connectBlockWith_congr_revision E fJustCheck (fun i tx hi hcb ictx htx c hc f => ?_) hflags
    (fun _ _ _ _ _ _ => htest _ _ _)
  rw [hspend]
  exact spend_eq_baseline_of_untouched hstep (hfree i tx hi hcb ictx htx c hc) f

/--
The target `validateBlockWith_congr` of design record 0011, section 10.1, and of design record 0012, section 9.1.
Take a revision that redefines the instructions with an opcode in `O`, as in `connectBlockWith_congr`, for the value of `active` at the height of the block.
Let its values of E1 to E3 agree with the baseline on the block.
Its script flags at the height are `connectScriptFlags`, its transaction test accepts, and its lock-time arguments are those of the context.

Take a block with `BlockUntouched O` on the coin set, at the height of the block.
Then `validateBlockWith` equals the embedded result of `validateBlock`.
It lifts `verifyScriptWith_congr` for both runs of each script check.
For every pair of embeddings, activation, pair of flags and context.
-/
theorem validateBlockWith_congr (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ) {O : UInt8 → Bool}
    {embed : ScriptError → ε} {embedU : Unsupported → υ} {verify : SignatureVerifier} {rev : BlockRevision ε υ ρ μ}
    {a : Activation} {ctx : ValidateContext} {step : InputContext → UInt32 → Step ε υ}
    (hspend : ∀ ictx spk f, rev.spend (a.isActive .mainnet ctx.height) ictx spk f =
      verifyScriptWith embed embedU (step ictx f) f ictx.input.scriptSig.bytes.val spk.bytes.val)
    (hstep : ∀ ictx f script st i, O i.opcode = false → step ictx f script st i =
      baselineStep embed embedU (some (transactionChecker ictx.tx ictx.index verify)) f script st i)
    (hflags : rev.scriptFlags (a.isActive .mainnet ctx.height) ctx.height = connectScriptFlags ctx.height)
    (htest : ∀ index tx coins, rev.txTest (a.isActive .mainnet ctx.height) ctx.height index tx coins = .ok ())
    (fCheckPOW fCheckMerkleRoot : Bool) {s : CoinSet} {b : Block}
    (hargs : rev.lockTimeArgs (a.isActive .mainnet ctx.height) ctx b = baselineLockTimeArgs ctx)
    (hfree : BlockUntouched O verify ctx.height s b) :
    validateBlockWith V E rev a fCheckPOW fCheckMerkleRoot ctx s b =
      V.ofBaseline E embed embedU (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b) := by
  rw [← validateBlockWithActive_ofBaseline V E embed embedU verify (a.isActive .mainnet ctx.height)]
  unfold validateBlockWith
  apply validateBlockWithActive_congr
  · intro _
    simp only [contextualBodyWith, hargs, BlockRevision.baseline]
  · rw [connectBlockWith_congr E hspend hstep hflags htest true (ctx := connectContextOf ctx b) hfree,
      connectBlockWith_ofBaseline]

end DogeLib.Proposals.Framework
