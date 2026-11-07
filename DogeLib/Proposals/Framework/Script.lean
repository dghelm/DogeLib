module

public import DogeLib.Script.Verify

/-!
# `Proposals.Framework.Script`

The Script loop with the instruction step as a parameter, for proposed revisions of Script.
Design record 0007, section 6 and decisions 3 and 10, sets the contract.

A proposed revision of Script changes the step of one instruction.
It does not change `evalLoop`, `evalScript` or `verifyScript` in the baseline.
This module copies those three definitions, and replaces the call of `evalInstruction` with a call of a step parameter:

| Framework | Baseline |
| --- | --- |
| `evalLoopWith` | `DogeLib.Script.evalLoop` |
| `evalScriptWith` | `DogeLib.Script.evalScript` |
| `verifyScriptWith` | `DogeLib.Script.verifyScript` |

`baselineStep` is the baseline step, `evalInstruction`, with its results mapped into the framework's result types.
`DogeLib.Proposals.Framework.Proofs.Script` proves that each framework definition, with `baselineStep`, equals its baseline definition.
So a change to the baseline loop that this copy does not follow fails the build.

## Errors

The baseline result types carry a `ScriptError`, and a proposal cannot add a constructor to that type.
So the framework result types `StepOutcome`, `EvalOutcome` and `VerifyOutcome` take the error type `ε` as a parameter.
The loop and `VerifyScript` produce baseline errors of their own, such as `BAD_OPCODE` and `EVAL_FALSE`.
Each framework definition takes a map `embed : ScriptError → ε` for those errors.
A proposal with its own errors `E` uses `ε = ScriptError ⊕ E` and `embed = Sum.inl`.

## Restriction

`Restricts step₁ step₀` says that every successful step of `step₁` is a successful step of `step₀` with the same state.
It reads only the successful results, so the two steps can have different error types.
`DogeLib.Proposals.Framework.Proofs.Script` proves that restriction lifts through the loop and through `VerifyScript`, including the P2SH evaluation.

## Opcode sets

`opcodeFreeFrom O script pc` says that no instruction that the reader reads from `pc` to the end has an opcode in `O`.
It counts every instruction, also an instruction in a branch that does not execute.
A short push at the end is not an instruction, and the loop rejects it before any step.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Script

/-- The outcome of one instruction, with the error type `ε`. The constructors are those of `DogeLib.Script.StepResult`. -/
inductive StepOutcome (ε : Type) where
  /-- The instruction succeeded, with this state. The cursor stays at the start of the instruction. -/
  | next (s : ExecState)
  /-- The instruction failed with this error. -/
  | rejected (error : ε)
  /-- The instruction needs a capability that the specification lacks. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- The outcome of one evaluation, with the error type `ε`. The constructors are those of `DogeLib.Script.EvalResult`. -/
inductive EvalOutcome (ε : Type) where
  /-- The evaluation succeeded. The state is its final state. -/
  | ok (s : ExecState)
  /-- The evaluation failed with this error. -/
  | rejected (error : ε)
  /-- The evaluation needs a capability that the specification lacks. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- The outcome of one `VerifyScript` call, with the error type `ε`. The constructors are those of `DogeLib.Script.VerifyResult`. -/
inductive VerifyOutcome (ε : Type) where
  /-- The call accepted. -/
  | accepted
  /-- The call failed with this error. -/
  | rejected (error : ε)
  /-- The call needs a capability that the specification lacks. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- A baseline step result, with its error mapped by `embed`. -/
def StepOutcome.ofBaseline {ε : Type} (embed : ScriptError → ε) : StepResult → StepOutcome ε
  | .next s => .next s
  | .rejected e => .rejected (embed e)
  | .unsupported u => .unsupported u

/-- A baseline evaluation result, with its error mapped by `embed`. -/
def EvalOutcome.ofBaseline {ε : Type} (embed : ScriptError → ε) : EvalResult → EvalOutcome ε
  | .ok s => .ok s
  | .rejected e => .rejected (embed e)
  | .unsupported u => .unsupported u

/-- A baseline `VerifyScript` result, with its error mapped by `embed`. -/
def VerifyOutcome.ofBaseline {ε : Type} (embed : ScriptError → ε) : VerifyResult → VerifyOutcome ε
  | .accepted => .accepted
  | .rejected e => .rejected (embed e)
  | .unsupported u => .unsupported u

/--
An instruction step: the script, the state before the instruction, and the instruction that `readInstruction` read at the cursor of the state.
The step takes the script because the signature opcodes read it.
A step captures its checker, its flags and any context of a proposal.
-/
abbrev Step (ε : Type) : Type := List UInt8 → ExecState → Instruction → StepOutcome ε

/-- The baseline step: `evalInstruction` with the checker `checker` and the flags `flags`, with its errors mapped by `embed`. -/
def baselineStep {ε : Type} (embed : ScriptError → ε) (checker : Option SignatureChecker) (flags : UInt32) : Step ε :=
  fun script s i => StepOutcome.ofBaseline embed (evalInstruction checker script flags s i)

/--
`step₁` restricts `step₀` when every successful step of `step₁` is a successful step of `step₀` with the same state.
Design record 0007, section 6.1.
A restricting step can reject, or report an unsupported capability, where `step₀` succeeds.
It cannot succeed where `step₀` does not succeed, and it cannot change the state of a success.
-/
def Restricts {ε₁ ε₀ : Type} (step₁ : Step ε₁) (step₀ : Step ε₀) : Prop :=
  ∀ script s i t, step₁ script s i = .next t → step₀ script s i = .next t

/--
The loop of `evalLoop`, with the instruction step `step` in place of `evalInstruction`.
At the end of the script, a nonempty `vfExec` gives `embed UNBALANCED_CONDITIONAL`.
A short push gives `embed BAD_OPCODE`.
-/
def evalLoopWith {ε : Type} (embed : ScriptError → ε) (step : Step ε) (script : List UInt8) (s : ExecState) :
    EvalOutcome ε :=
  match hr : readInstruction script s.pc with
  | .atEnd => if s.vfExec.isEmpty then .ok s else .rejected (embed .unbalancedConditional)
  | .truncated .. => .rejected (embed .badOpcode)
  | .instruction i =>
    have := readInstruction_progress hr
    match step script s i with
    | .next t => evalLoopWith embed step script { t with pc := i.next }
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
termination_by script.length - s.pc
decreasing_by omega

/--
`evalScript` with the instruction step `step`, on the caller's main stack `stack`.
A flag outside `supportedFlags` is unsupported, before any other check.
A script above 10,000 bytes gives `embed SCRIPT_SIZE`.
-/
def evalScriptWith {ε : Type} (embed : ScriptError → ε) (step : Step ε) (flags : UInt32) (script : List UInt8)
    (stack : List (List UInt8)) : EvalOutcome ε :=
  if unsupportedFlagBits flags ≠ 0 then .unsupported (.flags (unsupportedFlagBits flags))
  else if maxScriptSize < script.length then .rejected (embed .scriptSize)
  else evalLoopWith embed step script (ExecState.init stack)

/-- `finishEval` for the framework: `embed EVAL_FALSE` unless the top item of the final stack is true. -/
def finishEvalWith {ε : Type} (embed : ScriptError → ε) : EvalOutcome ε → VerifyOutcome ε
  | .ok s => if trueTop s.stack then .accepted else .rejected (embed .evalFalse)
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u

/--
`verifyScript` with the instruction step `step`, for `scriptSig` and `scriptPubKey`.
`flags` selects the P2SH evaluation, and its unsupported bits give `unsupported` before any evaluation.
The step uses its own flags. `baselineStep` with the same `flags` gives `verifyScript`.
-/
def verifyScriptWith {ε : Type} (embed : ScriptError → ε) (step : Step ε) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) : VerifyOutcome ε :=
  if unsupportedFlagBits flags ≠ 0 then .unsupported (.flags (unsupportedFlagBits flags))
  else match evalScriptWith embed step flags scriptSig [] with
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u
  | .ok s =>
    match evalScriptWith embed step flags scriptPubKey s.stack with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok t =>
      if !trueTop t.stack then .rejected (embed .evalFalse)
      else if hasFlag flags ScriptFlags.p2sh && isPayToScriptHash scriptPubKey then
        if !isPushOnly scriptSig then .rejected (embed .sigPushOnly)
        else match s.stack.reverse with
          -- `verifyScript` has the same unreachable value. `verifyScript_p2sh_saved_ne_nil` proves that the case is unreachable there.
          | [] => .rejected (embed .unknownError)
          | redeem :: rest => finishEvalWith embed (evalScriptWith embed step flags redeem rest.reverse)
      else .accepted

/--
No instruction that `readInstruction` reads from `pc` to the end of `script` has an opcode in `O`.
Every instruction counts, also one in a branch that does not execute.
A short push stops the reader. It is not an instruction, and it gives `true`.
-/
def opcodeFreeFrom (O : UInt8 → Bool) (script : List UInt8) (pc : Nat) : Bool :=
  match hr : readInstruction script pc with
  | .atEnd => true
  | .truncated .. => true
  | .instruction i =>
    have := readInstruction_progress hr
    !O i.opcode && opcodeFreeFrom O script i.next
termination_by script.length - pc
decreasing_by omega

/-- No instruction of `script`, read from its start, has an opcode in `O`. -/
def opcodeFree (O : UInt8 → Bool) (script : List UInt8) : Bool := opcodeFreeFrom O script 0

end DogeLib.Proposals.Framework
