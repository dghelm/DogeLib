module

public import DogeLib.Block.Exports.Validate
public import DogeLib.Exports.Oracle
public import DogeLib.Proposals.ExampleFaultyLocktime
public import DogeLib.Proposals.ExampleVersionVerify
public import DogeLib.Proposals.Framework.Block
public import DogeLib.Proposals.RelativeLockTime

/-!
# The operations of the proposal executable

The operations `block.validate` and `block.contextual_check_body` of the proposal executable, `dogelib-proposal-oracle`.
Design record 0011, section 10.2 and decision 10, sets the contract of the first.
Design record 0012, section 10.2 and decision 13, sets the contract of the second.

## `block.validate`

The operation is `block.validate` of `dogelib-oracle` with one more argument:

```text
"revision": {"name": "ExampleVersionVerify", "variant": null, "activation_height": 0}
```

`name` and `variant` select an entry of `revisions`. `activation_height` is a mainnet height, or null for no activation.
Without the argument, the operation is `Block.Exports.blockValidateWith` with no hook: the code of `dogelib-oracle`, and the same response.

With the argument, the baseline carries the state through the request, as before.
For each block, `validateBlockWith` also runs the revision on the state before the block.
The block record gains the object `revised`:

| Field | Value |
| --- | --- |
| `active` | Whether the revision is active at the height of the block. |
| `verdict` | `accepted`, `rejected` or `unsupported`. |
| `step` | For a rejection or an unsupported result, the name of the check: one of the five steps of `validateBlock`. A result of the transaction test of a revision has the step `ConnectBlock`. |
| `reject_reason` | For a rejection, Core's reject reason. For a script failure, the bracket holds the text of the revision's error. A transaction that fails the sequence locks of `RelativeLockTime` has `bad-txns-nonfinal`. |
| `dos`, `reject_code` | For a rejection, the denial-of-service score and the reject code. A script failure that is not mandatory has the score 0 and the code `0x40`, as in the baseline. |
| `tx`, `input` | For a rejection that names them, the position of the transaction in the block and of the input in the transaction. A failure of the sequence locks names the transaction. |
| `script_error` | For a script failure, the text of the error of the first script run. |
| `mandatory` | For a script failure, false when the second run, without the flags that are not mandatory, accepts. |
| `reason` | For an unsupported result, a text for the missing capability or the result outside the model. The three reasons of the sequence locks of `RelativeLockTime` are `RelativeLockTime: ancestorOutsideView`, `RelativeLockTime: coinAboveBlock` and `RelativeLockTime: heightOutOfDomain`. |
| `changes_digest_hex` | For an acceptance, the digest of the coin changes of the revision's result. |

A field that does not apply is null.
An unsupported result is never a rejection. It says nothing about any verdict.

The revision never changes the state that the request carries.
So `revised` answers one question for each block: what does the revision say about this block on the baseline chain below it?
No Core behaviour exists for a revision, and no comparison supports a `revised` object (design record 0007, section 9).

## `block.contextual_check_body`

The operation is `block.contextual_check_body` of `dogelib-oracle` with the same argument `revision`.
Without the argument, it is the baseline operation, with the same response.
With the argument, the response gains the object `revised`: `contextualBodyWith` of the revision on the block, in the context that the request gives.

| Field | Value |
| --- | --- |
| `active` | Whether the revision is active at the height of the block. |
| `verdict` | `accepted`, `rejected` or `unsupported`. |
| `reject_reason`, `dos`, `reject_code` | For a rejection, Core's reject reason, score and code. Null otherwise. |
| `reason` | For an unsupported result, a text for the input outside the model. Null otherwise. |
| `lock_time_cutoff` | The lock-time cutoff that the revision gives the check. |

The context of the request has the view `chain`, and the two version-bits states and the median time that the baseline operation computes.
The operation runs `ContextualCheckBlock` alone, with no header check before it.
So a revision that reads the median time past of the view needs a view with that median, and the operation gives `unsupported` without one.

## The revisions

`ExampleFaultyLocktime` and `ExampleVersionVerify` are the two examples of the `Proposals` library. Neither is a proposal for Dogecoin.
`RelativeLockTime` is the revision of design record 0012, with its three rules: BIP 113, BIP 112 and BIP 68.
For `block.validate`, the transaction test of the revision reads the view `chain` of the block.
A `revised` object names the rule of a rejection through its step and its reason.
The cutoff of BIP 113 has the step `ContextualCheckBlock` and the reason `bad-txns-nonfinal`.
A sequence lock of BIP 68 has the step `ConnectBlock`, the reason `bad-txns-nonfinal` and the transaction.
The opcode of BIP 112 has a script failure with its `script_error`.
For `block.contextual_check_body`, the `revised` object holds the result of the lock-time cutoff alone, because that operation runs no script and connects no transaction.
-/

@[expose] public section

namespace DogeLib.Proposals.Exports

open Lean (Json)
open DogeLib.Exports DogeLib.Block DogeLib.Block.Exports DogeLib.Script DogeLib.Work
open DogeLib.Proposals.Framework

/--
The fields of a `revised` object that describe a failure, with nulls where a field does not apply.
`score` holds the denial-of-service score and the reject code of a rejection.
-/
def failureFields (step : Option String) (rejectReason : Option String) (score : Option (Nat × Nat))
    (tx input : Option Nat) (scriptError : Option String) (mandatory : Option Bool) (reason : Option String) :
    List (String × Json) :=
  [("step", (step.map Json.str).getD .null), ("reject_reason", (rejectReason.map Json.str).getD .null),
    ("dos", (score.map (natJson ·.1)).getD .null), ("reject_code", (score.map (natJson ·.2)).getD .null),
    ("tx", (tx.map natJson).getD .null), ("input", (input.map natJson).getD .null),
    ("script_error", (scriptError.map Json.str).getD .null), ("mandatory", (mandatory.map Json.bool).getD .null),
    ("reason", (reason.map Json.str).getD .null)]

/-- The transaction that a `CheckBlock` rejection names: the position of the transaction that `CheckTransaction` rejects. -/
def checkBlockTx : CheckBlockError → Option Nat
  | .transaction index _ => some index
  | _ => none

/-- The transaction that a baseline `ConnectBlock` rejection names, when it names one. -/
def rejectionTx : ConnectBlockError → Option Nat
  | .inputsMissingOrSpent tx | .txInputs tx _ | .script tx _ _ _ => some tx
  | .checkBlock e => checkBlockTx e
  | _ => none

/-- The transaction that a rejection of one of the four checks before `ConnectBlock` names, when it names one. -/
def validateRejectionTx : ValidateError → Option Nat
  | .checkBlock e => checkBlockTx e
  | _ => none

/--
The embedding of `ConnectBlock` results into the failure fields of a `revised` object.
`describe` gives the text of a script error of the revision, and `describeU` the text of an unsupported script reason.
-/
def connectFields {ε υ : Type} (describe : ε → String) (describeU : υ → String) :
    ConnectEmbedding ε υ (List (String × Json)) (List (String × Json)) where
  rejected e :=
    failureFields (some "ConnectBlock") e.rejectReason (some (e.dosScore, e.rejectCode)) (rejectionTx e) none none
      none none
  unsupported e := failureFields (some "ConnectBlock") none none none none none none (some (reprStr e))
  script tx input mandatory e :=
    let kind := if mandatory then "mandatory-script-verify-flag-failed" else "non-mandatory-script-verify-flag"
    -- The score and the code of `ConnectBlockError.script`, which do not depend on the script error.
    let score := if mandatory then (100, 0x10) else (0, 0x40)
    failureFields (some "ConnectBlock") (some s!"{kind} ({describe e})") (some score) (some tx) (some input)
      (some (describe e)) (some mandatory) none
  scriptUnsupported u := failureFields (some "ConnectBlock") none none none none none none (some (describeU u))

/-- The embedding of `validateBlock` results into the failure fields of a `revised` object. The fields of a `ConnectBlock` result pass unchanged. -/
def validateFields :
    ValidateEmbedding (List (String × Json)) (List (String × Json)) (List (String × Json)) (List (String × Json)) where
  rejected e :=
    failureFields (some e.step) e.rejectReason (some (e.dosScore, e.rejectCode)) (validateRejectionTx e) none none none
      none
  unsupported e := failureFields (some e.step) none none none none none none (some (reprStr e))
  connect := id
  connectUnsupported := id

/--
The hook of a revision that can read the context of the block: `validateBlockWith` on the block, as a `revised` object.
`rev` gives the revision for the context, `E` maps the results of `ConnectBlock` into the outcome types of the revision, and `V` maps every result into failure fields.
-/
def revisedHookWith {ε υ ρ μ : Type} (rev : ValidateContext → BlockRevision ε υ ρ μ)
    (V : ValidateEmbedding ρ μ (List (String × Json)) (List (String × Json))) (E : ConnectEmbedding ε υ ρ μ)
    (activation : Activation) : BlockHook :=
  fun options ctx s b =>
    let active := Json.bool (activation.isActive .mainnet ctx.height)
    match validateBlockWith V E (rev ctx) activation options.checkPow options.checkMerkle ctx s b with
    | .ok result =>
      Json.mkObj ([("active", active), ("verdict", "accepted"),
        ("changes_digest_hex", .str (hexOf (changesDigest result.changes).toList))] ++
        failureFields none none none none none none none none)
    | .rejected fields =>
      Json.mkObj ([("active", active), ("verdict", "rejected"), ("changes_digest_hex", .null)] ++ fields)
    | .unsupported fields =>
      Json.mkObj ([("active", active), ("verdict", "unsupported"), ("changes_digest_hex", .null)] ++ fields)

/--
The hook of a revision that does not read the context: `revisedHookWith` with the failure fields as the outcome types.
`describe` and `describeU` give the texts of the revision's script errors and unsupported script reasons.
-/
def revisedHook {ε υ : Type} (rev : BlockRevision ε υ (List (String × Json)) (List (String × Json)))
    (describe : ε → String) (describeU : υ → String) (activation : Activation) : BlockHook :=
  revisedHookWith (fun _ => rev) validateFields (connectFields describe describeU) activation

/-- The `revised` object of `block.contextual_check_body`, from the context of the request and the block. -/
abbrev BodyHook : Type := ValidateContext → Block → Json

/--
The body hook of a revision: `contextualBodyWith` on the block, as a `revised` object.
`guard` names an input on which the lock-time arguments of the revision are outside its model, for a value of `active`. The result is then `unsupported` with that text.
-/
def revisedBody {ε υ ρ μ : Type} (rev : BlockRevision ε υ ρ μ)
    (guard : Bool → ValidateContext → Block → Option String) (activation : Activation) : BodyHook :=
  fun ctx b =>
    let active := activation.isActive .mainnet ctx.height
    let cutoff := Json.num (Lean.JsonNumber.fromInt (lockTimeCutoff (rev.lockTimeArgs active ctx b) b))
    let object (verdict : String) (rejectReason dos code reason : Json) : Json :=
      Json.mkObj [("active", .bool active), ("verdict", .str verdict), ("reject_reason", rejectReason), ("dos", dos),
        ("reject_code", code), ("reason", reason), ("lock_time_cutoff", cutoff)]
    match guard active ctx b with
    | some reason => object "unsupported" .null .null .null (.str reason)
    | none =>
      match contextualBodyWith rev active ctx b with
      | .ok () => object "accepted" .null .null .null .null
      | .error e =>
        if e.isRejection then
          object "rejected" (e.rejectReason.map Json.str |>.getD .null) (natJson e.dosScore) (natJson e.rejectCode)
            .null
        else object "unsupported" .null .null .null (.str (reprStr e))

/-- No input is outside the model of the lock-time arguments: the guard of a revision with the baseline arguments. -/
def noGuard : Bool → ValidateContext → Block → Option String := fun _ _ _ => none

/--
The guard of `RelativeLockTime`: with `active` true on an applicable block, the view must have a median time past.
`validateBlockWithActive` needs no guard, because the contextual header check computes the same median first.
`block.contextual_check_body` runs no header check.
-/
def relativeLockTimeGuard (active : Bool) (ctx : ValidateContext) (b : Block) : Option String :=
  if active && RelativeLockTime.applicable ctx b then
    match medianTimePast ctx.view with
    | .ok _ => none
    | .error e => some s!"RelativeLockTime: the chain has no median time past of the predecessor ({reprStr e})"
  else none

/-- A revision that a request can name. -/
structure NamedRevision where
  /-- The value of `name` in the `revision` argument. -/
  name : String
  /-- The value of `variant`, or `none` for a revision without variants, which a request writes as null. -/
  variant : Option String
  /-- The hook of the revision for an activation, for `block.validate`. -/
  hook : Activation → BlockHook
  /-- The body hook of the revision for an activation, for `block.contextual_check_body`. -/
  body : Activation → BodyHook

/-- The text of a script error of `ExampleVersionVerify`: Core's text for a baseline error, and a name for an error of the example. -/
def describeExampleError : ExampleVersionVerify.ExampleScriptError → String
  | .inl e => e.description
  | .inr .negativeOperand => "ExampleVersionVerify: negative operand"
  | .inr .versionTooLow => "ExampleVersionVerify: version too low"

/-- The text of an unsupported script reason of `ExampleVersionVerify`. -/
def describeExampleUnsupported : ExampleVersionVerify.ExampleScriptUnsupported → String
  | .inl u => reprStr u
  | .inr .missingContext => "ExampleVersionVerify: missing context"

/-- The type of failure fields, which is the type of rejections and of unsupported reasons of a `revised` object. -/
abbrev Fields : Type := List (String × Json)

/-- `ExampleFaultyLocktime` with a variant, as a revision of the executable. -/
def faultyLocktimeRevision (v : ExampleFaultyLocktime.Variant) :
    BlockRevision ScriptError Unsupported Fields Fields :=
  ExampleFaultyLocktime.blockRevision v coreVerifier

/-- `ExampleVersionVerify` as a revision of the executable. -/
def versionVerifyRevision :
    BlockRevision ExampleVersionVerify.ExampleScriptError ExampleVersionVerify.ExampleScriptUnsupported Fields Fields :=
  ExampleVersionVerify.blockRevision coreVerifier

/--
`RelativeLockTime` as a revision of the executable, for the context of a block.
Its transaction test reads the view of the context.
-/
def relativeLockTimeRevision (ctx : ValidateContext) :
    BlockRevision ScriptError Unsupported RelativeLockTime.ConnectRejection RelativeLockTime.ConnectReason :=
  RelativeLockTime.blockRevision coreVerifier ctx.view

/-- The text of a result outside the model of the sequence locks of `RelativeLockTime`. -/
def describeRelativeLockTimeReason : RelativeLockTime.Reason → String
  | .ancestorOutsideView => "RelativeLockTime: ancestorOutsideView"
  | .coinAboveBlock => "RelativeLockTime: coinAboveBlock"
  | .heightOutOfDomain => "RelativeLockTime: heightOutOfDomain"

/--
The embedding of the results of `RelativeLockTime` into the failure fields of a `revised` object.
A baseline result has the fields of `validateFields` and `connectFields`.
A transaction that fails the sequence locks has Core's `bad-txns-nonfinal` of `ConnectBlock`, with the score 100 and the code `REJECT_INVALID` (SOURCES.md, D114, lines 1955 to 1958).
A reason of the sequence locks is an unsupported result of `ConnectBlock`.
-/
def relativeLockTimeFields :
    ValidateEmbedding RelativeLockTime.ConnectRejection RelativeLockTime.ConnectReason Fields Fields where
  rejected := validateFields.rejected
  unsupported := validateFields.unsupported
  connect
    | .inl (.script tx input mandatory e) =>
      (connectFields ScriptError.description (reprStr : Unsupported → String)).script tx input mandatory e
    | .inl e => (connectFields ScriptError.description (reprStr : Unsupported → String)).rejected e
    | .inr (.sequenceLocks index) =>
      failureFields (some "ConnectBlock") (some "bad-txns-nonfinal") (some (100, 0x10)) (some index) none none none
        none
  connectUnsupported
    | .inl (.scriptUnsupported u) =>
      (connectFields ScriptError.description (reprStr : Unsupported → String)).scriptUnsupported u
    | .inl e => (connectFields ScriptError.description (reprStr : Unsupported → String)).unsupported e
    | .inr reason =>
      failureFields (some "ConnectBlock") none none none none none none (some (describeRelativeLockTimeReason reason))

/--
The revisions that a request can name, with `coreVerifier`.
`ExampleFaultyLocktime` has the variants `corrected` and `faulty`. `ExampleVersionVerify` has no variant.
Neither example is a proposal for Dogecoin.
`RelativeLockTime` is the revision of design record 0012, with the rules of BIP 113, BIP 112 and BIP 68. It has no variant.
-/
def revisions : List NamedRevision :=
  [⟨"ExampleFaultyLocktime", some "corrected",
      revisedHook (faultyLocktimeRevision .corrected) ScriptError.description reprStr,
      revisedBody (faultyLocktimeRevision .corrected) noGuard⟩,
    ⟨"ExampleFaultyLocktime", some "faulty",
      revisedHook (faultyLocktimeRevision .faulty) ScriptError.description reprStr,
      revisedBody (faultyLocktimeRevision .faulty) noGuard⟩,
    ⟨"ExampleVersionVerify", none,
      revisedHook versionVerifyRevision describeExampleError describeExampleUnsupported,
      revisedBody versionVerifyRevision noGuard⟩,
    ⟨"RelativeLockTime", none,
      revisedHookWith relativeLockTimeRevision relativeLockTimeFields RelativeLockTime.connectEmbedding,
      fun activation ctx b => revisedBody (relativeLockTimeRevision ctx) relativeLockTimeGuard activation ctx b⟩]

/-- The activation with the height `height` on mainnet, and no activation on any other network. -/
def mainnetActivation (height : Option Nat) : Activation :=
  ⟨fun
    | .mainnet => height
    | _ => none⟩

/--
The revision of a request: none without the argument `revision`, and the named revision with its activation otherwise.
The argument is an object with exactly the fields `name`, `variant` and `activation_height`.
-/
def requestRevision (fields : Args) : Except Failure (Option (NamedRevision × Activation)) := do
  let some value := fields.get? "revision" | return none
  let .obj revision := value | throw (.request "revision must be an object")
  for (key, _) in revision do
    unless ["name", "variant", "activation_height"].contains key do
      throw (.request s!"unknown revision field {key}")
  let .str name ← arg revision "name" | throw (.request "revision name must be a string")
  let variant ← match ← arg revision "variant" with
    | .null => pure none
    | .str v => pure (some v)
    | _ => throw (.request "revision variant must be a string or null")
  let height ← match ← arg revision "activation_height" with
    | .null => pure none
    | _ => (fun h => some h.toNat) <$> argInt revision "activation_height" 0 2147483646
  let some named := revisions.find? fun r => r.name == name && r.variant == variant
    | throw (.request s!"unknown revision {name} with variant {variant.getD "null"}")
  return some (named, mainnetActivation height)

/-- The hook of a request: none without the argument `revision`, and the hook of the named revision with it. -/
def revisionHook : HookReader := fun fields => do
  return (← requestRevision fields).map fun (named, activation) => named.hook activation

/-- The arguments that the proposal executable adds to `block.validate`. -/
def revisionArgs : List String := ["revision"]

/-- `block.validate` of the proposal executable: the baseline operation with the argument `revision`. -/
def blockValidate : Operation := blockValidateWith revisionArgs revisionHook

/-- `block.validate` with `blocks_file` of the proposal executable. A request that also has `coins_file` goes to `Block.Exports.blockValidateSnapshotWith` with the same argument and hook. -/
def blockValidateFile (fields : Args) : IO (Except Failure Json) :=
  blockValidateFileWith revisionArgs revisionHook fields

/--
`block.contextual_check_body` of the proposal executable: the baseline operation with the argument `revision`.
Without the argument it runs the baseline operation.
With it, the response of the baseline operation gains the object `revised`, which the body hook of the revision gives.
A request on which the baseline operation returns an error returns that error.
-/
def contextualCheckBody : Operation where
  name := Block.Exports.contextualCheckBody.name
  args := Block.Exports.contextualCheckBody.args ++ revisionArgs
  run fields := do
    match ← requestRevision fields with
    | none => Block.Exports.contextualCheckBody.run fields
    | some (named, activation) =>
      let base ← Block.Exports.contextualCheckBody.run (fields.erase "revision")
      let mode ← argMode fields
      let bs ← argHex fields "block_hex"
      let chain ← Work.Exports.argView fields
      match Block.decodeComplete mode bs with
      | .error _ => throw (.request "the block does not decode")
      | .ok b =>
        let (_, csvActive, segwitActive, prevMtp) ← bodyStates chain
        let ctx : ValidateContext :=
          { view := chain, adjustedTime := 0, lastCheckpointHeight := none, csvActive, segwitActive,
            prevMedianTimePast := prevMtp, bip34Ancestor := none }
        return base.setObjVal! "revised" (named.body activation ctx b)

/-- Every operation of the proposal executable: those of `dogelib-oracle`, with `blockValidate` and `contextualCheckBody` of this module in the place of the baseline ones. -/
def operations : List Operation :=
  DogeLib.Exports.operations.map fun op =>
    if op.name == blockValidate.name then blockValidate
    else if op.name == contextualCheckBody.name then contextualCheckBody
    else op

/-- Answer a line in `IO`, as the `dogelib-proposal-oracle` executable does. -/
def respondIO (line : String) : IO (Option Json) :=
  respondM (runRequestIOWith operations (fun fields =>
    if fields.contains "coins_file" then Block.Exports.blockValidateSnapshotWith revisionArgs revisionHook fields
    else blockValidateFile fields)) line

/-- The name of the executable. -/
def programName : String := "dogelib-proposal-oracle"

/-- The object that `dogelib-proposal-oracle --version` prints: the record format of the oracle, and the name of this program, so that a saved run does not mistake it for `dogelib-oracle`. -/
def versionJson : Json := Json.mkObj [("format", .str formatName), ("program", .str programName)]

/-- The entry point of `dogelib-proposal-oracle`: answer each line of standard input, or print the version object with `--version`. -/
def run (argv : List String) : IO UInt32 := do
  match argv with
  | ["--version"] =>
    IO.println versionJson.compress
    return 0
  | [] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      if let some response ← respondIO line then
        stdout.putStrLn response.compress
        stdout.flush
    return 0
  | _ =>
    IO.eprintln s!"usage: {programName} [--version]"
    return 2

end DogeLib.Proposals.Exports
