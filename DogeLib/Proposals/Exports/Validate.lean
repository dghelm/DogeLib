module

public import DogeLib.Block.Exports.Validate
public import DogeLib.Exports.Oracle
public import DogeLib.Proposals.ExampleFaultyLocktime
public import DogeLib.Proposals.ExampleVersionVerify
public import DogeLib.Proposals.Framework.Block

/-!
# `block.validate` with a proposed revision

The operation `block.validate` of the proposal executable, `dogelib-proposal-oracle`.
Design record 0011, section 10.2 and decision 10, sets the contract.

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
| `step` | For a rejection or an unsupported result, the name of the check: one of the five steps of `validateBlock`. |
| `reject_reason` | For a rejection, Core's reject reason. For a script failure, the bracket holds the text of the revision's error. |
| `tx`, `input` | For a rejection that names them, the position of the transaction in the block and of the input in the transaction. |
| `script_error` | For a script failure, the text of the error of the first script run. |
| `mandatory` | For a script failure, false when the second run, without the flags that are not mandatory, accepts. |
| `reason` | For an unsupported result, a text for the missing capability or the result outside the model. |
| `changes_digest_hex` | For an acceptance, the digest of the coin changes of the revision's result. |

A field that does not apply is null.
An unsupported result is never a rejection. It says nothing about any verdict.

The revision never changes the state that the request carries.
So `revised` answers one question for each block: what does the revision say about this block on the baseline chain below it?
No Core behaviour exists for a revision, and no comparison supports a `revised` object (design record 0007, section 9).

The revisions are the two examples of the `Proposals` library. Neither is a proposal for Dogecoin.
-/

@[expose] public section

namespace DogeLib.Proposals.Exports

open Lean (Json)
open DogeLib.Exports DogeLib.Block DogeLib.Block.Exports DogeLib.Script DogeLib.Work
open DogeLib.Proposals.Framework

/-- The fields of a `revised` object that describe a failure, with nulls where a field does not apply. -/
def failureFields (step : Option String) (rejectReason : Option String) (tx input : Option Nat)
    (scriptError : Option String) (mandatory : Option Bool) (reason : Option String) : List (String × Json) :=
  [("step", (step.map Json.str).getD .null), ("reject_reason", (rejectReason.map Json.str).getD .null),
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
  rejected e := failureFields (some "ConnectBlock") e.rejectReason (rejectionTx e) none none none none
  unsupported e := failureFields (some "ConnectBlock") none none none none none (some (reprStr e))
  script tx input mandatory e :=
    let kind := if mandatory then "mandatory-script-verify-flag-failed" else "non-mandatory-script-verify-flag"
    failureFields (some "ConnectBlock") (some s!"{kind} ({describe e})") (some tx) (some input) (some (describe e))
      (some mandatory) none
  scriptUnsupported u := failureFields (some "ConnectBlock") none none none none none (some (describeU u))

/-- The embedding of `validateBlock` results into the failure fields of a `revised` object. The fields of a `ConnectBlock` result pass unchanged. -/
def validateFields :
    ValidateEmbedding (List (String × Json)) (List (String × Json)) (List (String × Json)) (List (String × Json)) where
  rejected e := failureFields (some e.step) e.rejectReason (validateRejectionTx e) none none none none
  unsupported e := failureFields (some e.step) none none none none none (some (reprStr e))
  connect := id
  connectUnsupported := id

/--
The hook of a revision: `validateBlockWith` on the block, as a `revised` object.
`describe` and `describeU` give the texts of the revision's script errors and unsupported script reasons.
-/
def revisedHook {ε υ : Type} (rev : BlockRevision ε υ) (describe : ε → String) (describeU : υ → String)
    (activation : Activation) : BlockHook :=
  fun options ctx s b =>
    let active := Json.bool (activation.isActive .mainnet ctx.height)
    match validateBlockWith validateFields (connectFields describe describeU) rev activation options.checkPow
        options.checkMerkle ctx s b with
    | .ok result =>
      Json.mkObj ([("active", active), ("verdict", "accepted"),
        ("changes_digest_hex", .str (hexOf (changesDigest result.changes).toList))] ++
        failureFields none none none none none none none)
    | .rejected fields =>
      Json.mkObj ([("active", active), ("verdict", "rejected"), ("changes_digest_hex", .null)] ++ fields)
    | .unsupported fields =>
      Json.mkObj ([("active", active), ("verdict", "unsupported"), ("changes_digest_hex", .null)] ++ fields)

/-- A revision that a request can name. -/
structure NamedRevision where
  /-- The value of `name` in the `revision` argument. -/
  name : String
  /-- The value of `variant`, or `none` for a revision without variants, which a request writes as null. -/
  variant : Option String
  /-- The hook of the revision for an activation. -/
  hook : Activation → BlockHook

/-- The text of a script error of `ExampleVersionVerify`: Core's text for a baseline error, and a name for an error of the example. -/
def describeExampleError : ExampleVersionVerify.ExampleScriptError → String
  | .inl e => e.description
  | .inr .negativeOperand => "ExampleVersionVerify: negative operand"
  | .inr .versionTooLow => "ExampleVersionVerify: version too low"

/-- The text of an unsupported script reason of `ExampleVersionVerify`. -/
def describeExampleUnsupported : ExampleVersionVerify.ExampleScriptUnsupported → String
  | .inl u => reprStr u
  | .inr .missingContext => "ExampleVersionVerify: missing context"

/--
The revisions that a request can name: the two examples of the `Proposals` library, with `coreVerifier`.
`ExampleFaultyLocktime` has the variants `corrected` and `faulty`. `ExampleVersionVerify` has no variant.
Neither is a proposal for Dogecoin.
-/
def revisions : List NamedRevision :=
  [⟨"ExampleFaultyLocktime", some "corrected",
      revisedHook (ExampleFaultyLocktime.blockRevision .corrected coreVerifier) ScriptError.description reprStr⟩,
    ⟨"ExampleFaultyLocktime", some "faulty",
      revisedHook (ExampleFaultyLocktime.blockRevision .faulty coreVerifier) ScriptError.description reprStr⟩,
    ⟨"ExampleVersionVerify", none,
      revisedHook (ExampleVersionVerify.blockRevision coreVerifier) describeExampleError describeExampleUnsupported⟩]

/-- The activation with the height `height` on mainnet, and no activation on any other network. -/
def mainnetActivation (height : Option Nat) : Activation :=
  ⟨fun
    | .mainnet => height
    | _ => none⟩

/--
The hook of a request: none without the argument `revision`, and the hook of the named revision with it.
The argument is an object with exactly the fields `name`, `variant` and `activation_height`.
-/
def revisionHook : HookReader := fun fields => do
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
  return some (named.hook (mainnetActivation height))

/-- The arguments that the proposal executable adds to `block.validate`. -/
def revisionArgs : List String := ["revision"]

/-- `block.validate` of the proposal executable: the baseline operation with the argument `revision`. -/
def blockValidate : Operation := blockValidateWith revisionArgs revisionHook

/-- `block.validate` with `blocks_file` of the proposal executable. -/
def blockValidateFile (fields : Args) : IO (Except Failure Json) :=
  blockValidateFileWith revisionArgs revisionHook fields

/-- Every operation of the proposal executable: those of `dogelib-oracle`, with `blockValidate` of this module in the place of the baseline one. -/
def operations : List Operation :=
  DogeLib.Exports.operations.map fun op => if op.name == blockValidate.name then blockValidate else op

/-- Answer a line in `IO`, as the `dogelib-proposal-oracle` executable does. -/
def respondIO (line : String) : IO (Option Json) :=
  respondM (runRequestIOWith operations blockValidateFile) line

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
