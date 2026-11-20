module

public import DogeLib.Proposals.Framework.Block

/-!
# `Proposals.ExampleVersionVerify`

**This module is not a proposal for Dogecoin.**
No one proposes this rule for any network, and no network activates it.
It is the worked example of design record 0007, section 10.
Decision 9 keeps it in the `Proposals` library as a permanent test of the framework.
Its theorems show that the framework states and proves a Script-local soft fork from end to end.
They say nothing about the merits of any rule.

## The rule

The example redefines `OP_NOP10` (`0xb9`) in the shape of `OP_CHECKLOCKTIMEVERIFY`.
With `active` true and the opcode in an executing branch, it checks in this order (design record 0007, section 10.1):

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item is a five-byte `CScriptNum` without the minimal requirement, as for `OP_CHECKLOCKTIMEVERIFY`. A failed decode gives `UNKNOWN_ERROR`.
3. A negative operand gives the example error `negativeOperand`.
4. Without a transaction context, the result is unsupported, as for the lock-time opcodes without a checker.
5. The version of the transaction, read as an unsigned 32-bit value, must be at least the operand. Otherwise the example error is `versionTooLow`.

The record lists the missing context as its fifth item.
The context check must come before the comparison that reads the context, so the definition puts it fourth.
The order matches `DogeLib.Script.checkLockTimeStep` with a checker whose `checkLockTime` returns `none`: that result comes only after the negative check.
It differs from the baseline `OP_CHECKLOCKTIMEVERIFY` without a checker (`checker = none`), which reports unsupported before it reads the stack.
The example has no such case, because it reads the context, not the checker.

The opcode never pops its operand.
With `active` false, or in a branch that does not execute, `OP_NOP10` stays a NOP.

## The step

`exampleStep` runs the baseline `evalInstruction` first.
When the result is `next t`, the opcode is `0xb9`, the branch executes and `active` is true, it applies `versionCheck` to `t`.
Every other result passes unchanged, with a baseline error and a baseline unsupported reason mapped by `Sum.inl`.
`versionCheck` returns `next t` or fails, so the step restricts the baseline step.

The baseline step checks the stack size after the opcode.
A caller's initial stack of more than 1,000 items can therefore give `STACK_SIZE` before the example's own error (design record 0007, section 10.2).
The difference changes an error, never acceptance.

## Errors and the unsupported reason

The errors are `ScriptError ⊕ ExampleError`, with the baseline errors under `Sum.inl` (decision 10).

The unsupported reasons are `Unsupported ⊕ ExampleUnsupported`, with the baseline reasons under `Sum.inl` (issue #122).
A missing transaction context reports `Sum.inr ExampleUnsupported.missingContext`.
No baseline result maps to a reason under `Sum.inr`, so the reason identifies the example's own case.
The reason is a label for a missing capability. It is not a rejection, and it makes no claim about any verdict.

## Context

The rule reads the transaction through `ExampleContext`, not through `SignatureChecker`, so the baseline checker type does not change.
`exampleVerifyLegacySpend` builds the context from the transaction of its `InputContext`.
`exampleVerifyScript` and `exampleEvalScript` take an optional context.

## Activation

Each revised definition takes `active : Bool` (decision 4).
No network has an activation height for the example, and the module defines no `Activation` value.

## Block level

`blockRevision verify` is the example as a `BlockRevision` of `DogeLib.Proposals.Framework.Block`: its spend check is `exampleVerifyLegacySpend` with the verifier `verify`.
`connectBlockWith` and `validateBlockWith` run it on a block (design record 0011, section 10.1).

## Labels

Every compatibility theorem in `DogeLib.Proposals.ExampleVersionVerify.Proofs` is Script-local, except those of `Proofs.Block`, which are block-level.
A Script-local theorem is about one call of `evalScript`, `verifyScript` or `verifyLegacySpend`.
No theorem of the example is a soft-fork claim about the network, which also needs the statement for chains (design record 0007, section 8.3).
The legacy projection of the example is the identity, because the rule changes no encoding and a successful step leaves the baseline state.

There is no external document, so the example has no identifier in SOURCES.md.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleVersionVerify

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

/-- `OP_NOP10`, the opcode that the example redefines. -/
def nop10 : UInt8 := 0xb9

/-- The opcode set of the example: `OP_NOP10` alone. -/
def isNop10 (op : UInt8) : Bool := op == nop10

/-- The errors of the example. -/
inductive ExampleError where
  /-- The operand is negative. -/
  | negativeOperand
  /-- The version of the transaction, read as an unsigned 32-bit value, is below the operand. -/
  | versionTooLow
  deriving DecidableEq, Repr

/-- The error type of the revised definitions: a baseline error under `Sum.inl`, or an example error under `Sum.inr`. -/
abbrev ExampleScriptError : Type := ScriptError ⊕ ExampleError

/--
The unsupported reasons of the example.
A missing context stays an unsupported result. It is never a rejection.
-/
inductive ExampleUnsupported where
  /-- An executed `OP_NOP10`, with `active` true, has no transaction context to read. -/
  | missingContext
  deriving DecidableEq, Repr

/-- The type of unsupported reasons of the revised definitions: a baseline reason under `Sum.inl`, or an example reason under `Sum.inr`. -/
abbrev ExampleScriptUnsupported : Type := Unsupported ⊕ ExampleUnsupported

/-- The transaction context that the rule reads. -/
structure ExampleContext where
  /-- The spending transaction. -/
  tx : Transaction

/-- The context of one legacy input: its transaction. -/
def ExampleContext.ofInput (ctx : InputContext) : ExampleContext := ⟨ctx.tx⟩

/--
The checks of the example on the state `t` after the baseline NOP, in the order of the module documentation.
The operand is the top item of `t`, and the check never pops it.
It returns `next t` or fails.
-/
def versionCheck (ctx : Option ExampleContext) (t : ExecState) :
    StepOutcome ExampleScriptError ExampleScriptUnsupported :=
  match t.stack.reverse with
  | [] => .rejected (.inl .invalidStackOperation)
  | top :: _ =>
    match ScriptNum.decode top false lockTimeNumSize with
    | .error _ => .rejected (.inl .unknownError)
    | .ok n =>
      if n < 0 then .rejected (.inr .negativeOperand)
      else match ctx with
        | none => .unsupported (.inr .missingContext)
        | some c => if n ≤ (c.tx.version.toNat : Int) then .next t else .rejected (.inr .versionTooLow)

/--
The revised step.
It runs `evalInstruction checker script flags s i`.
A successful `OP_NOP10` in an executing branch, with `active` true, then goes through `versionCheck`.
Every other result passes unchanged, with a baseline error and a baseline unsupported reason under `Sum.inl`.
-/
def exampleStep (active : Bool) (ctx : Option ExampleContext) (checker : Option SignatureChecker) (flags : UInt32) :
    Step ExampleScriptError ExampleScriptUnsupported :=
  fun script s i =>
    match evalInstruction checker script flags s i with
    | .next t => if active && isNop10 i.opcode && s.fExec then versionCheck ctx t else .next t
    | .rejected e => .rejected (.inl e)
    | .unsupported u => .unsupported (.inl u)

/-- The revised `evalScript`: `evalScriptWith` with the example step. -/
def exampleEvalScript (active : Bool) (ctx : Option ExampleContext) (checker : Option SignatureChecker)
    (flags : UInt32) (script : List UInt8) (stack : List (List UInt8)) :
    EvalOutcome ExampleScriptError ExampleScriptUnsupported :=
  evalScriptWith Sum.inl Sum.inl (exampleStep active ctx checker flags) flags script stack

/-- The revised `verifyScript`: `verifyScriptWith` with the example step, for the checker `c`. -/
def exampleVerifyScript (active : Bool) (ctx : Option ExampleContext) (c : SignatureChecker) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) : VerifyOutcome ExampleScriptError ExampleScriptUnsupported :=
  verifyScriptWith Sum.inl Sum.inl (exampleStep active ctx (some c) flags) flags scriptSig scriptPubKey

/--
The revised spend predicate of one legacy input.
It runs `exampleVerifyScript` with the transaction of `ctx` as the example context and with the checker of `verifyLegacySpend`.
-/
def exampleVerifyLegacySpend (active : Bool) (ctx : InputContext) (prevScriptPubKey : Transaction.Script)
    (flags : UInt32) (verify : SignatureVerifier) : VerifyOutcome ExampleScriptError ExampleScriptUnsupported :=
  exampleVerifyScript active (some (.ofInput ctx)) (transactionChecker ctx.tx ctx.index verify) flags
    ctx.input.scriptSig.bytes.val prevScriptPubKey.bytes.val

/-- The example at the block level: the spend check `exampleVerifyLegacySpend` with the verifier `verify`. -/
def blockRevision {ρ μ : Type} (verify : SignatureVerifier) :
    BlockRevision ExampleScriptError ExampleScriptUnsupported ρ μ where
  spend := fun active ctx prevScriptPubKey flags => exampleVerifyLegacySpend active ctx prevScriptPubKey flags verify

/-- The arguments of one spend check, other than `active`: the input, the previous `scriptPubKey`, the flags and the verifier. -/
structure SpendArgs where
  /-- The input and its transaction. -/
  ctx : InputContext
  /-- The `scriptPubKey` of the spent output. -/
  prevScriptPubKey : Transaction.Script
  /-- Core's flag set. -/
  flags : UInt32
  /-- The elliptic-curve check. -/
  verify : SignatureVerifier

/-- `verifyLegacySpend` on spend arguments. -/
def baselineSpend (a : SpendArgs) : VerifyResult :=
  verifyLegacySpend a.ctx a.prevScriptPubKey a.flags a.verify

/-- `exampleVerifyLegacySpend` on spend arguments. -/
def revisedSpend (active : Bool) (a : SpendArgs) : VerifyOutcome ExampleScriptError ExampleScriptUnsupported :=
  exampleVerifyLegacySpend active a.ctx a.prevScriptPubKey a.flags a.verify

/--
The scripts of the characterization: a push of the bytes `b`, then `OP_NOP10`, then the script `S`.
The push opcode is the length of `b`: `OP_0` for the empty list, and a direct push for 1 to 75 bytes.
-/
def operandScript (b S : List UInt8) : List UInt8 := (b.length.toUInt8 :: b) ++ nop10 :: S

/--
The redefined rule runs in a spend: its previous `scriptPubKey` is `operandScript b S` for an operand `b` of at most 5 bytes.
The second instruction of that script is `OP_NOP10` at the top level, so it executes whenever the push before it succeeds.
-/
def RunsRule (a : SpendArgs) : Prop :=
  ∃ b S, b.length ≤ 5 ∧ a.prevScriptPubKey.bytes.val = operandScript b S

/--
The legacy projection of the example: the identity on input contexts and on Script states.
The rule changes no encoding, and a successful revised step leaves the baseline state (design record 0007, section 8.4).
-/
def projection : LegacyProjection InputContext InputContext ExecState ExecState :=
  LegacyProjection.identity InputContext ExecState

end DogeLib.Proposals.ExampleVersionVerify
