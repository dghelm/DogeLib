module

public import DogeLib.Block.Validate
public import DogeLib.Proposals.Framework.Activation
public import DogeLib.Proposals.Framework.Compatibility

/-!
# `Proposals.Framework.Block`

The block level of a proposed revision: `connectBlock` and `validateBlock` with the parts that a revision changes as parameters.
Design record 0011, section 10.1 and decision 11, sets the contract for a revision of Script.
Design record 0012, section 6.3, adds the extensions E1 to E4 for a revision of a rule outside Script.

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

`BlockRevision ε υ ρ μ` holds what a revision changes at the block level.
Each field takes `active : Bool` first.

| Field | Extension | Meaning | Baseline value |
| --- | --- | --- | --- |
| `spend` | | The spend check of one input. It captures its signature verifier. | `verifyLegacySpend` |
| `scriptFlags` | E1 | The script flags of a block at a height. | `connectScriptFlags` |
| `txTest` | E2 | A test of one transaction that is not a coinbase, with the height, the index and the spent coins. | Accepts every transaction. |
| `lockTimeArgs` | E3 | The two lock-time arguments of `contextualCheckBlockBody`: `csvActive` and the median time past. | Those of the context. |

The last three fields have their baseline values as defaults, so a revision of Script sets `spend` alone.
`BlockRevision.baseline` has the baseline value in every field, for both values of `active`.
The types `ρ` and `μ` are the rejections and the unsupported reasons of `txTest`, which are those of the `ConnectBlock` outcome (extension E4).

Everything else is the baseline: the count of signature operations, the amounts, the coin set and the other checks before `ConnectBlock`.

`txTest` runs after the lookup of the inputs and before the count of signature operations, as `SequenceLocks` does in Core (SOURCES.md, D114, lines 1948 to 1959).
The second script check removes the flags that are not mandatory from the value of `scriptFlags`, as the baseline does.
The count of signature operations reads `SCRIPT_VERIFY_P2SH` from the value of `scriptFlags`.

`connectBlockWith` keeps the result `csvActive` of `connectBlock` for a context whose `csvActive` is true.
That field of the context is the version-bits state of the pin, which is never active on mainnet (`csv_never_lockedIn`).
A revision sets the lock-time rules through its own fields, and no revision reads that state as its activation.
So every theorem about the baseline revision holds for every context, as before the extensions.

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

`connectBlockWith` and `validateBlockWithActive` take `active` as an argument.
`validateBlockWith` takes an `Activation`, and computes `active` from the height of the block on mainnet (design record 0007, section 7.2).
It is `validateBlockWithActive` with that value.

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

/-- The rejection of an outcome, or `none` for an acceptance or an unsupported result. -/
def BlockOutcome.rejection? {ρ μ α : Type} : BlockOutcome ρ μ α → Option ρ
  | .rejected e => some e
  | _ => none

/-- Whether an outcome is an acceptance. -/
def BlockOutcome.isOk {ρ μ α : Type} : BlockOutcome ρ μ α → Bool
  | .ok _ => true
  | _ => false

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

/-- The test of one transaction: its index, the transaction and the coins that its inputs spend. `BlockRevision.txTest` gives it for a value of `active` and a height. -/
abbrev TxTest (ρ μ : Type) : Type := Nat → Transaction → List Coin → BlockOutcome ρ μ Unit

/-- The transaction test that accepts every transaction: the baseline value. -/
def TxTest.accept {ρ μ : Type} : TxTest ρ μ := fun _ _ _ => .ok ()

/-- The lock-time arguments of the baseline: `csvActive` and the median time past of the context. -/
def baselineLockTimeArgs (ctx : ValidateContext) : Bool × Int := (ctx.csvActive, ctx.prevMedianTimePast)

/--
What a proposed revision changes at the block level.
`ε` and `υ` are the script error type and the type of unsupported script reasons of the spend check.
`ρ` and `μ` are the types of rejections and of unsupported reasons of the transaction test, which are those of the `ConnectBlock` outcome.
Each field takes `active` first. A field without a value here has its baseline value.
-/
structure BlockRevision (ε υ ρ μ : Type) where
  /-- The spend check for each value of `active`. -/
  spend : Bool → SpendCheck ε υ
  /-- The script flags of a block at a height (extension E1). The baseline value is `connectScriptFlags`. -/
  scriptFlags : Bool → Nat → UInt32 := fun _ => connectScriptFlags
  /--
  A test of one transaction that is not a coinbase (extension E2): the height of the block, the index of the transaction, the transaction and the coins that its inputs spend, in input order.
  The baseline value accepts every transaction.
  -/
  txTest : Bool → Nat → TxTest ρ μ := fun _ _ => TxTest.accept
  /--
  The lock-time arguments of `contextualCheckBlockBody` for a block in a context (extension E3): `csvActive`, and the median time past that the body reads when `csvActive` is true.
  The baseline value is the pair of the context.
  -/
  lockTimeArgs : Bool → ValidateContext → Block → Bool × Int := fun _ ctx _ => baselineLockTimeArgs ctx

/-- The baseline spend check: `verifyLegacySpend` with the verifier `verify`, with its result mapped by `embed` and `embedU`. -/
def baselineSpendCheck {ε υ : Type} (embed : ScriptError → ε) (embedU : Unsupported → υ) (verify : SignatureVerifier) :
    SpendCheck ε υ :=
  fun ctx prevScriptPubKey flags => .ofBaseline embed embedU (verifyLegacySpend ctx prevScriptPubKey flags verify)

/-- The revision that changes nothing: the baseline spend check for both values of `active`, and the baseline value of every other field. -/
def BlockRevision.baseline {ε υ ρ μ : Type} (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (verify : SignatureVerifier) : BlockRevision ε υ ρ μ where
  spend := fun _ => baselineSpendCheck embed embedU verify

/--
The lock-time cutoff of `contextualCheckBlockBody` for the arguments `args`: the median time past when `csvActive` is true, and the time of the block otherwise (SOURCES.md, D110, lines 3128 to 3136).
-/
def lockTimeCutoff (args : Bool × Int) (b : Block) : Int :=
  if args.1 then args.2 else (b.header.pure.nTime.toNat : Int)

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

/--
The part of `connectTransactionWith` after the lookup of the inputs and the transaction test, as the same part of `connectTransaction`:
the count of signature operations, the fee, `CheckInputs` and the update of the coin set.
-/
def connectFoundWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ)
    (ctx : ConnectContext) (flags : UInt32) (index : Nat) (st : ConnectState) (tx : Transaction) (coins : List Coin) :
    BlockOutcome ρ μ ConnectState :=
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

/--
One pass of the transaction loop, as `connectTransaction`, for the transaction at `index`.
After the lookup of the inputs, the test `test` runs on a transaction that is not a coinbase.
A transaction that passes it continues with `connectFoundWith`.
-/
def connectTransactionWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ) (test : TxTest ρ μ)
    (ctx : ConnectContext) (flags : UInt32) (index : Nat) (st : ConnectState) (tx : Transaction) :
    BlockOutcome ρ μ ConnectState :=
  match (if tx.isCoinBase then some [] else lookupInputs st.coins tx.inputs.val) with
  | none => E.ofError (.inputsMissingOrSpent index)
  | some coins =>
    match (if tx.isCoinBase then .ok () else test index tx coins) with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok () => connectFoundWith E spend ctx flags index st tx coins

/-- The transaction loop from the transaction at `index`, as `connectTransactions`. -/
def connectTransactionsWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (spend : SpendCheck ε υ)
    (test : TxTest ρ μ) (ctx : ConnectContext) (flags : UInt32) (index : Nat) (st : ConnectState) :
    List Transaction → BlockOutcome ρ μ ConnectState
  | [] => .ok st
  | tx :: rest =>
    match connectTransactionWith E spend test ctx flags index st tx with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok st' => connectTransactionsWith E spend test ctx flags (index + 1) st' rest

/--
`connectBlock` with the parts of the revision `rev` for the value `active`:
its spend check in place of `verifyLegacySpend`, its script flags in place of `connectScriptFlags`, and its transaction test.
The other checks, their order and the count of signature operations are those of `connectBlock`.
`E` maps each failure into the outcome.
-/
def connectBlockWith {ε υ ρ μ : Type} (E : ConnectEmbedding ε υ ρ μ) (rev : BlockRevision ε υ ρ μ) (active : Bool)
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
        match connectTransactionsWith E (rev.spend active) (rev.txTest active ctx.height) ctx
            (rev.scriptFlags active ctx.height) 0 ⟨s, 0, 0, []⟩ txs with
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
`args` holds the lock-time arguments of the last check: `csvActive` and the median time past.
`validateBlock` passes those of the context.
The result is the failure of the first check that fails. It is never `ValidateError.connect`.
-/
def checksBeforeConnect (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext) (args : Bool × Int) (b : Block) :
    Except ValidateError Unit :=
  let genesis := some b.header.pure.getHash == genesisHash? .mainnet
  checkStep .header (if genesis || !fCheckPOW then .ok () else checkBlockHeader .mainnet b.header) fun _ =>
    checkStep .contextualHeader (if genesis then .ok () else
        contextualCheckBlockHeader .mainnet b.header.pure ctx.view ctx.adjustedTime ctx.lastCheckpointHeight) fun _ =>
      checkStep .checkBlock (checkBlock .mainnet fCheckPOW fCheckMerkleRoot b) fun _ =>
        checkStep .contextualBody
          (contextualCheckBlockBody ctx.height args.2 args.1 ctx.segwitActive b) fun _ => .ok ()

/--
`ContextualCheckBlock` with the lock-time arguments of the revision `rev` for the value `active`.
`validateBlockWithActive` runs this check as the last of `checksBeforeConnect`.
-/
def contextualBodyWith {ε υ ρ μ : Type} (rev : BlockRevision ε υ ρ μ) (active : Bool) (ctx : ValidateContext)
    (b : Block) : Except ContextualBodyError Unit :=
  contextualCheckBlockBody ctx.height (rev.lockTimeArgs active ctx b).2 (rev.lockTimeArgs active ctx b).1
    ctx.segwitActive b

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
`validateBlock` with the revision `rev` for the value `active`.
The first four checks are `checksBeforeConnect` with the lock-time arguments of the revision: those of `validateBlock`, in the same order and with the same genesis case.
Then `connectBlockWith` runs in place of `connectBlock`.
`V` maps each failure into the outcome.
-/
def validateBlockWithActive {ε υ ρ μ ρ' μ' : Type} (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    (rev : BlockRevision ε υ ρ μ) (active : Bool) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) : BlockOutcome ρ' μ' ConnectResult :=
  V.afterChecks (checksBeforeConnect fCheckPOW fCheckMerkleRoot ctx (rev.lockTimeArgs active ctx b) b) fun _ =>
    connectBlockWith E rev active true (connectContextOf ctx b) s b

/--
`validateBlockWithActive` for an activation.
The revision is active when `activation` is active on mainnet at the height of the block.
-/
def validateBlockWith {ε υ ρ μ ρ' μ' : Type} (V : ValidateEmbedding ρ μ ρ' μ') (E : ConnectEmbedding ε υ ρ μ)
    (rev : BlockRevision ε υ ρ μ) (activation : Activation) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) : BlockOutcome ρ' μ' ConnectResult :=
  validateBlockWithActive V E rev (activation.isActive .mainnet ctx.height) fCheckPOW fCheckMerkleRoot ctx s b

end DogeLib.Proposals.Framework
