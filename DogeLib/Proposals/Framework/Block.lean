module

public import DogeLib.Block.Validate
public import DogeLib.Proposals.Framework.Activation
public import DogeLib.Proposals.Framework.Compatibility

/-!
# `Proposals.Framework.Block`

The block level of a proposed revision of Script: `connectBlock` and `validateBlock` with the spend check as a parameter.
Design record 0011, section 10.1 and decision 11, sets the contract.

`connectBlock` takes Core's signature verifier, and runs `verifyLegacySpend` on each input.
A proposed revision of Script has its own spend check, with an argument `active`.
This module copies the chain of definitions from `checkInputScript` to `connectBlock`, and `validateBlock`, and replaces the call of `verifyLegacySpend` with a call of a spend check.
It follows option M2 of design record 0007: no baseline file changes.

| Framework | Baseline |
| --- | --- |
| `checkInputScriptWith` | `DogeLib.Block.checkInputScript` |
| `checkInputScriptsWith` | `DogeLib.Block.checkInputScripts` |
| `checkInputsWith` | `DogeLib.Block.checkInputs` |
| `connectTransactionWith` | `DogeLib.Block.connectTransaction` |
| `connectTransactionsWith` | `DogeLib.Block.connectTransactions` |
| `connectBlockWith` | `DogeLib.Block.connectBlock` |
| `checksBeforeConnect`, `validateBlockWith` | `DogeLib.Block.validateBlock` |

`DogeLib.Proposals.Framework.Proofs.Block` proves that each definition, with the baseline spend check, equals the embedded result of its baseline definition.
So a change to the baseline chain that this copy does not follow fails the build.

## The revision

`BlockRevision ε υ` holds what a revision changes at the block level.
It has one field, the spend check `spend : Bool → SpendCheck ε υ`, where the `Bool` is `active`.
The spend check captures its signature verifier.
`BlockRevision.baseline` is `verifyLegacySpend` for both values of `active`.

Everything else is the baseline: the flags of a height, the count of signature operations, the amounts, the coin set and the four checks before `ConnectBlock`.
A revision that changes one of them is outside this module (design record 0011, sections 10.1 and 12).

## Results

The baseline results are `Except ConnectBlockError` and `Except ValidateError`.
`ConnectBlockError.script` holds a baseline `ScriptError`, and a revision can have another error type.
A baseline error is also one of two kinds: a rejection of Core, or a result outside the model, which says nothing about Core's verdict.
`ConnectBlockError.isRejection` separates the two kinds.

So the definitions return a `BlockOutcome ρ μ α`, with the constructors `ok`, `rejected` and `unsupported`.
The form is that of the Script framework: `ρ` is the type of rejections, and `μ` is the type of unsupported reasons.
A `ConnectEmbedding ε υ ρ μ` gives the four maps into those types:

| Map | Source |
| --- | --- |
| `rejected` | A baseline `ConnectBlockError` that is a rejection, other than a script failure. |
| `unsupported` | A baseline `ConnectBlockError` that is a result outside the model, other than an unsupported script result. |
| `script` | A failure of the spend check, with its error of type `ε`, and the transaction, the input and the class of the failure. |
| `scriptUnsupported` | An unsupported result of the spend check, with its reason of type `υ`. |

A `ValidateEmbedding` does the same for `ValidateError` and for the results of `connectBlockWith`.
`ConnectEmbedding.baseline` and `ValidateEmbedding.baseline` use the baseline error types for both `ρ` and `μ`.
With them, `BlockOutcome.toExcept` gives back the baseline result exactly.

*The embedded result* of a baseline call is `ConnectEmbedding.ofBaseline` or `ValidateEmbedding.ofBaseline` of its result.
An unsupported result is never a rejection.

## The second script check

`checkInputScript` runs a failed script again without the flags that are not mandatory, and takes the class of the failure from the second run.
`checkInputScriptWith` keeps that contract.
It runs the same spend check, with the same `active`, on the reduced flags.
It classifies by the second run and keeps the error of the first.
Acceptance depends on the first run alone.

## Activation

`connectBlockWith` takes `active` as an argument.
`validateBlockWith` takes an `Activation`, and computes `active` from the height of the block on mainnet (design record 0007, section 7.2).

## Labels

A theorem about these definitions is *block-level*: it is about one block on a supplied coin set and chain view.
It is not a claim about a chain or about the network.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Block DogeLib.Transaction DogeLib.Script DogeLib.Work

/-- The outcome of a block-level check, with the type of rejections `ρ`, the type of unsupported reasons `μ` and the type of results `α`. -/
inductive BlockOutcome (ρ μ α : Type) where
  /-- The check accepts, with this result. -/
  | ok (a : α)
  /-- The check rejects, with this error. -/
  | rejected (error : ρ)
  /-- The check needs a capability that the specification lacks, or its input is outside the model. The result says nothing about Core's verdict. -/
  | unsupported (reason : μ)

/-- The verdict of a block-level outcome. -/
def BlockOutcome.verdict {ρ μ α : Type} : BlockOutcome ρ μ α → Verdict
  | .ok _ => .accepted
  | .rejected _ => .rejected
  | .unsupported _ => .unsupported

/-- An outcome with its rejection mapped by `f` and its unsupported reason mapped by `g`. -/
def BlockOutcome.map {ρ μ ρ' μ' α : Type} (f : ρ → ρ') (g : μ → μ') : BlockOutcome ρ μ α → BlockOutcome ρ' μ' α
  | .ok a => .ok a
  | .rejected e => .rejected (f e)
  | .unsupported u => .unsupported (g u)

/-- An outcome whose rejections and unsupported reasons have one type, as an `Except` value. Both kinds become `Except.error`. -/
def BlockOutcome.toExcept {ε α : Type} : BlockOutcome ε ε α → Except ε α
  | .ok a => .ok a
  | .rejected e => .error e
  | .unsupported e => .error e

/-- The verdict of a baseline `connectBlock` or `validateBlock` result, where `isRejection` separates Core's rejections from the results outside the model. -/
def verdictOfBlockResult {ε α : Type} (isRejection : ε → Bool) : Except ε α → Verdict
  | .ok _ => .accepted
  | .error e => if isRejection e then .rejected else .unsupported

/--
The spend check of one legacy input, for one value of `active`: the input, the `scriptPubKey` of the spent output and Core's flag set.
The check captures its signature verifier.
-/
abbrev SpendCheck (ε υ : Type) : Type := InputContext → Transaction.Script → UInt32 → VerifyOutcome ε υ

/--
What a proposed revision changes at the block level, with the script error type `ε` and the type of unsupported script reasons `υ`.
The revision changes the spend check and nothing else.
-/
structure BlockRevision (ε υ : Type) where
  /-- The spend check for each value of `active`. -/
  spend : Bool → SpendCheck ε υ

/-- The baseline spend check: `verifyLegacySpend` with the verifier `verify`, with its result mapped by `embed` and `embedU`. -/
def baselineSpendCheck {ε υ : Type} (embed : ScriptError → ε) (embedU : Unsupported → υ) (verify : SignatureVerifier) :
    SpendCheck ε υ :=
  fun ctx prevScriptPubKey flags => .ofBaseline embed embedU (verifyLegacySpend ctx prevScriptPubKey flags verify)

/-- The revision that changes nothing: the baseline spend check for both values of `active`. -/
def BlockRevision.baseline {ε υ : Type} (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (verify : SignatureVerifier) : BlockRevision ε υ :=
  ⟨fun _ => baselineSpendCheck embed embedU verify⟩

/--
The maps from the results of `ConnectBlock` into the rejections `ρ` and the unsupported reasons `μ` of a block-level outcome.
`ε` and `υ` are the error type and the type of unsupported reasons of the spend check.
-/
structure ConnectEmbedding (ε υ ρ μ : Type) where
  /-- A baseline error that is a rejection of Core. `ConnectEmbedding.ofError` applies it only when `isRejection` is true. -/
  rejected : ConnectBlockError → ρ
  /-- A baseline error that is a result outside the model. `ConnectEmbedding.ofError` applies it only when `isRejection` is false. -/
  unsupported : ConnectBlockError → μ
  /-- A failure of the spend check of input `input` of the transaction at `tx`, with its error. `mandatory` is false when the check passes without the flags that are not mandatory. -/
  script : (tx input : Nat) → (mandatory : Bool) → ε → ρ
  /-- An unsupported result of the spend check, with its reason. -/
  scriptUnsupported : υ → μ

/-- A baseline error as an outcome: `rejected` for a rejection of Core, and `unsupported` for a result outside the model. -/
def ConnectEmbedding.ofError {ε υ ρ μ α : Type} (E : ConnectEmbedding ε υ ρ μ) (e : ConnectBlockError) :
    BlockOutcome ρ μ α :=
  if e.isRejection then .rejected (E.rejected e) else .unsupported (E.unsupported e)

/--
The embedded form of a baseline error.
A script failure goes through `script` with its error mapped by `embed`.
An unsupported script result goes through `scriptUnsupported` with its reason mapped by `embedU`.
Every other error goes through `ofError`.
-/
def ConnectEmbedding.ofBaselineError {ε υ ρ μ α : Type} (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) : ConnectBlockError → BlockOutcome ρ μ α
  | .script tx input mandatory e => .rejected (E.script tx input mandatory (embed e))
  | .scriptUnsupported u => .unsupported (E.scriptUnsupported (embedU u))
  | e => E.ofError e

/-- The embedded result of a baseline `ConnectBlock` call: its value, or `ofBaselineError` of its error. -/
def ConnectEmbedding.ofBaseline {ε υ ρ μ α : Type} (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε)
    (embedU : Unsupported → υ) : Except ConnectBlockError α → BlockOutcome ρ μ α
  | .ok a => .ok a
  | .error e => E.ofBaselineError embed embedU e

/-- The embedding into the baseline error type: `ConnectBlockError` for rejections and for unsupported reasons, with the baseline constructors. -/
def ConnectEmbedding.baseline : ConnectEmbedding ScriptError Unsupported ConnectBlockError ConnectBlockError :=
  ⟨id, id, .script, .scriptUnsupported⟩

/--
The script check of one input, as `checkInputScript`, with the spend check `spend` in place of `verifyLegacySpend`.
A failed check runs again on the flags without `standardNotMandatoryVerifyFlags`, and the second run gives `mandatory`.
The error is that of the first run.
-/
def checkInputScriptWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ) (flags : UInt32)
    (txIndex : Nat) (tx : Transaction) (input : Nat) (coin : Coin) : BlockOutcome ρ μ Unit :=
  match inputContext? tx input with
  | none => E.ofError (.contextBounds txIndex)
  | some ctx =>
    match spend ctx coin.out.scriptPubKey flags with
    | .accepted => .ok ()
    | .unsupported u => .unsupported (E.scriptUnsupported u)
    | .rejected e =>
      if flags &&& standardNotMandatoryVerifyFlags != 0 then
        match spend ctx coin.out.scriptPubKey (flags &&& ~~~standardNotMandatoryVerifyFlags) with
        | .accepted => .rejected (E.script txIndex input false e)
        | .rejected _ => .rejected (E.script txIndex input true e)
        | .unsupported u => .unsupported (E.scriptUnsupported u)
      else .rejected (E.script txIndex input true e)

/-- The script loop from input `input`, as `checkInputScripts`: the first failure, in input order. -/
def checkInputScriptsWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ) (flags : UInt32)
    (txIndex : Nat) (tx : Transaction) (input : Nat) : List Coin → BlockOutcome ρ μ Unit
  | [] => .ok ()
  | coin :: rest =>
    match checkInputScriptWith E spend flags txIndex tx input coin with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok () => checkInputScriptsWith E spend flags txIndex tx (input + 1) rest

/-- `CheckInputs` for a transaction that is not a coinbase, as `checkInputs`: `checkTxInputs`, then the script of each input. -/
def checkInputsWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ) (height : Nat)
    (flags : UInt32) (txIndex : Nat) (tx : Transaction) (coins : List Coin) : BlockOutcome ρ μ Unit :=
  match checkTxInputs height coins tx.valueOut with
  | .error .outOfDomain => E.ofError .outOfDomain
  | .error e => E.ofError (.txInputs txIndex e)
  | .ok () => checkInputScriptsWith E spend flags txIndex tx 0 coins

/-- One pass of the transaction loop, as `connectTransaction`, for the transaction at `index`. -/
def connectTransactionWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ)
    (ctx : ConnectContext) (flags : UInt32) (index : Nat) (st : ConnectState) (tx : Transaction) :
    BlockOutcome ρ μ ConnectState :=
  match (if tx.isCoinBase then some [] else lookupInputs st.coins tx.inputs.val) with
  | none => E.ofError (.inputsMissingOrSpent index)
  | some coins =>
    let cost := st.sigOpsCost + getTransactionSigOpCost tx coins (hasFlag flags ScriptFlags.p2sh)
    if cost > maxBlockSigOpsCost then E.ofError .sigOps
    else
      match (if tx.isCoinBase then some st.fees else addFee st.fees coins tx.valueOut) with
      | none => E.ofError .outOfDomain
      | some fees =>
        match (if tx.isCoinBase then .ok () else checkInputsWith E spend ctx.height flags index tx coins) with
        | .rejected e => .rejected e
        | .unsupported u => .unsupported u
        | .ok () =>
          let spentSet := if tx.isCoinBase then st.coins else spendInputs st.coins tx.inputs.val
          if !tx.isCoinBase && spentSet.haveUnspent tx.txid then E.ofError (.newCoinsExist index)
          else
            let spent := (tx.inputs.val.zip coins).map fun (input, coin) => CoinChange.spent input.prevout coin
            let created := (TxCoins.ofTx tx ctx.height).coins.map fun (o, c) => CoinChange.created o c
            .ok ⟨spentSet.addTx tx ctx.height, fees, cost, created.reverse ++ spent.reverse ++ st.changes⟩

/-- The transaction loop from the transaction at `index`, as `connectTransactions`. -/
def connectTransactionsWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ)
    (ctx : ConnectContext) (flags : UInt32) (index : Nat) (st : ConnectState) :
    List Transaction → BlockOutcome ρ μ ConnectState
  | [] => .ok st
  | tx :: rest =>
    match connectTransactionWith E spend ctx flags index st tx with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok st' => connectTransactionsWith E spend ctx flags (index + 1) st' rest

/--
`connectBlock` with the spend check of the revision `rev` for the value `active`, in place of `verifyLegacySpend`.
The checks, their order, the flags of the height and the count of signature operations are those of `connectBlock`.
`E` maps each failure into the outcome.
-/
def connectBlockWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (rev : BlockRevision ε υ) (active : Bool)
    (fJustCheck : Bool) (ctx : ConnectContext) (s : CoinSet) (b : Block) : BlockOutcome ρ μ ConnectResult :=
  match checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | .error e => E.ofError (.checkBlock e)
  | .ok () =>
    if some b.header.pure.getHash == genesisHash? .mainnet then .ok ⟨s, []⟩
    else
      let txs := b.transactions
      if enforceBip30 ctx.bip34Ancestor && txs.any (fun tx => s.haveUnspent tx.txid) then E.ofError .bip30
      else if ctx.csvActive then E.ofError .csvActive
      else
        match connectTransactionsWith E (rev.spend active) ctx (connectScriptFlags ctx.height) 0 ⟨s, 0, 0, []⟩ txs with
        | .rejected e => .rejected e
        | .unsupported u => .unsupported u
        | .ok st =>
          match getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash with
          | .error e => E.ofError (.subsidy e)
          | .ok subsidy =>
            if !inInt64Range (st.fees + (subsidy : Int)) then E.ofError .outOfDomain
            else if (match txs with | [] => 0 | coinbase :: _ => coinbase.valueOut) > st.fees + (subsidy : Int) then
              E.ofError .coinbaseAmount
            else .ok ⟨st.coins, st.changes.reverse⟩

/--
The maps from the results of `validateBlock` into the rejections `ρ'` and the unsupported reasons `μ'` of a block-level outcome.
`ρ` and `μ` are the types of the `connectBlockWith` outcome.
-/
structure ValidateEmbedding (ρ μ ρ' μ' : Type) where
  /-- A baseline error of the first four checks that is a rejection of Core. `ValidateEmbedding.ofError` applies it only when the error has a reject reason. -/
  rejected : ValidateError → ρ'
  /-- A baseline error of the first four checks that is an adapter error. `ValidateEmbedding.ofError` applies it only when the error has no reject reason. -/
  unsupported : ValidateError → μ'
  /-- A rejection of `connectBlockWith`. -/
  connect : ρ → ρ'
  /-- An unsupported result of `connectBlockWith`. -/
  connectUnsupported : μ → μ'

/-- A baseline error as an outcome: `rejected` when it has a reject reason of Core, and `unsupported` otherwise. -/
def ValidateEmbedding.ofError {ρ μ ρ' μ' α : Type} (V : ValidateEmbedding ρ μ ρ' μ') (e : ValidateError) :
    BlockOutcome ρ' μ' α :=
  if e.rejectReason.isSome then .rejected (V.rejected e) else .unsupported (V.unsupported e)

/--
The embedded result of a baseline `validateBlock` call.
An error of `ConnectBlock` goes through `E.ofBaselineError` and then through `connect` or `connectUnsupported`.
Every other error goes through `ofError`.
-/
def ValidateEmbedding.ofBaseline {ε υ ρ μ ρ' μ' α : Type} (V : ValidateEmbedding ρ μ ρ' μ')
    (E : ConnectEmbedding ε υ ρ μ) (embed : ScriptError → ε) (embedU : Unsupported → υ) :
    Except ValidateError α → BlockOutcome ρ' μ' α
  | .ok a => .ok a
  | .error (.connect e) => (E.ofBaselineError embed embedU e).map V.connect V.connectUnsupported
  | .error e => V.ofError e

/-- The embedding into the baseline error type: `ValidateError` for rejections and for unsupported reasons, with `ValidateError.connect` for the results of `ConnectBlock`. -/
def ValidateEmbedding.baseline : ValidateEmbedding ConnectBlockError ConnectBlockError ValidateError ValidateError :=
  ⟨id, id, .connect, .connect⟩

/--
One of the checks of `validateBlock` before `ConnectBlock`: the error of `check` under `wrap`, or the result of `next`.
`next` is a function, so that it runs only when `check` passes.
-/
def checkStep {ε : Type} (wrap : ε → ValidateError) (check : Except ε Unit)
    (next : Unit → Except ValidateError Unit) : Except ValidateError Unit :=
  match check with
  | .error e => .error (wrap e)
  | .ok () => next ()

/--
The four checks of `validateBlock` before `ConnectBlock`, in its order and with its genesis case: `CheckBlockHeader`, `ContextualCheckBlockHeader`, `CheckBlock` and `ContextualCheckBlock`.
The result is the failure of the first check that fails. It is never `ValidateError.connect`.
-/
def checksBeforeConnect (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (b : Block) :
    Except ValidateError Unit :=
  let genesis := some b.header.pure.getHash == genesisHash? .mainnet
  checkStep .header (if genesis || !fCheckPOW then .ok () else checkBlockHeader .mainnet b.header) fun _ =>
    checkStep .contextualHeader (if genesis then .ok () else
        contextualCheckBlockHeader .mainnet b.header.pure ctx.view ctx.adjustedTime ctx.lastCheckpointHeight) fun _ =>
      checkStep .checkBlock (checkBlock .mainnet fCheckPOW fCheckMerkleRoot b) fun _ =>
        checkStep .contextualBody
          (contextualCheckBlockBody ctx.height ctx.prevMedianTimePast ctx.csvActive ctx.segwitActive b) fun _ => .ok ()

/-- The context of `ConnectBlock` that `validateBlock` builds for the block `b`. -/
def connectContextOf (ctx : ValidateContext) (b : Block) : ConnectContext :=
  ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩

/--
The outcome of `validateBlockWith` from the result of `checksBeforeConnect` and the outcome of `connectBlockWith`.
An error of the checks goes through `ofError`, and `connect` runs only when the checks pass.
-/
def ValidateEmbedding.afterChecks {ρ μ ρ' μ' α : Type} (V : ValidateEmbedding ρ μ ρ' μ')
    (checks : Except ValidateError Unit) (connect : Unit → BlockOutcome ρ μ α) : BlockOutcome ρ' μ' α :=
  match checks with
  | .error e => V.ofError e
  | .ok () => (connect ()).map V.connect V.connectUnsupported

/--
`validateBlock` with `connectBlockWith` in place of `connectBlock`.
The first four checks are `checksBeforeConnect`: those of `validateBlock`, in the same order and with the same genesis case.
The revision is active when `activation` is active on mainnet at the height of the block.
`V` maps each failure into the outcome.
-/
def validateBlockWith {ε υ ρ μ ρ' μ' : Type} (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    (rev : BlockRevision ε υ) (activation : Activation) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) : BlockOutcome ρ' μ' ConnectResult :=
  V.afterChecks (checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx b) fun _ =>
    connectBlockWith E rev (activation.isActive .mainnet ctx.height) true (connectContextOf ctx b) s b

end DogeLib.Proposals.Framework
