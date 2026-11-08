module

public import DogeLib.Proposals.Framework.Compatibility

/-!
# `Proposals.ExampleFaultyLocktime`

**This module is not a proposal for Dogecoin.**
It is an invented proposal with a deliberate fault, kept as a teaching example and as a test of the framework.
No one proposes this rule for any network, and no network activates it.
Its theorems show that the framework of design record 0007 catches one class of error.
In that class, a small change of stack effect makes a soft-fork claim false.

The theorems say nothing about the merits of any rule.
`docs/in-practice.md` uses the module as its worked example.

## The rule

The example redefines `OP_NOP4` (`0xb3`) as a lock-time check in the shape of `OP_CHECKLOCKTIMEVERIFY` (D3, lines 350 to 390).
At the pin, `OP_NOP4` is a NOP: Core's `EvalScript` gives `DISCOURAGE_UPGRADABLE_NOPS` only with that flag, and otherwise does nothing (D3, lines 429 to 435).
`OP_CHECKLOCKTIMEVERIFY` is `OP_NOP2` (`0xb1`), and `OP_CHECKSEQUENCEVERIFY` is `OP_NOP3` (`0xb2`).
The flag `DISCOURAGE_UPGRADABLE_NOPS` lies outside `supportedFlags`, so every call with that flag is unsupported before any evaluation.

With `active` true and the opcode in an executing branch, the rule runs `DogeLib.Script.checkLockTimeStep` on the state after the baseline NOP.
That step has the checks and errors of `OP_CHECKLOCKTIMEVERIFY` with its flag set (D3, lines 360 to 390):

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item is a five-byte `CScriptNum` without the minimal requirement. A failed decode gives `UNKNOWN_ERROR`.
3. A negative operand gives `NEGATIVE_LOCKTIME`.
4. The checker's `checkLockTime` decides the rest: `false` gives `UNSATISFIED_LOCKTIME`, and `none` gives an unsupported result.

The two variants differ only after a successful check:

| Variant | After a successful check |
| --- | --- |
| `Variant.faulty` | The step pops the operand. The pop is the deliberate fault. |
| `Variant.corrected` | The step keeps the operand, as `OP_CHECKLOCKTIMEVERIFY` does. |

With `active` false, or in a branch that does not execute, `OP_NOP4` stays a NOP in both variants.
Without a checker, an executed `OP_NOP4` with `active` true reports the baseline reason `Unsupported.checkLockTimeVerify`.
That constructor's documentation describes `OP_CHECKLOCKTIMEVERIFY`, so the label is a stand-in, as in `ExampleVersionVerify`.
A spend always has a checker, so no spend reaches that case.

## Errors

Every error of the rule is a baseline `ScriptError`, so the revised definitions use `ScriptError` with the error map `id`.

## Results

`DogeLib.Proposals.ExampleFaultyLocktime.Proofs` proves these Script-local results:

- Both variants have the inactive equality.
- The faulty step does not restrict the baseline step.
  The faulty spend predicate accepts the counterexample `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL`, and `verifyLegacySpend` rejects it.
  So the faulty variant is not a `SoftFork`. It is `Incompatible`.
- The corrected step restricts the baseline step, and the corrected spend predicate is a `SoftFork` with a strictness witness and a use witness.

## Labels

Every theorem about the example is Script-local, as design record 0007, section 8.3, defines the label.
None of them is a soft-fork claim about the network.
The legacy projection is the identity, because the rule changes no encoding.

There is no external document, so the example has no identifier in SOURCES.md.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleFaultyLocktime

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

/-- `OP_NOP4`, the opcode that the example redefines. -/
def nop4 : UInt8 := 0xb3

/-- The opcode set of the example: `OP_NOP4` alone. -/
def isNop4 (op : UInt8) : Bool := op == nop4

/-- The two variants of the rule. -/
inductive Variant where
  /-- The deliberately faulty rule: it pops the operand after a successful check. -/
  | faulty
  /-- The corrected rule: it keeps the operand, as `OP_CHECKLOCKTIMEVERIFY` does. -/
  | corrected
  deriving DecidableEq, Repr

/--
The lock-time check of variant `v` with the checker `c`, on the state `t` after the baseline NOP.
It runs `checkLockTimeStep c t`.
On success, `Variant.faulty` removes the top item of the stack, and `Variant.corrected` keeps the state.
-/
def lockCheck (v : Variant) (c : SignatureChecker) (t : ExecState) : StepOutcome ScriptError :=
  match checkLockTimeStep c t with
  | .next t' =>
    match v with
    | .faulty => .next { t' with stack := t'.stack.dropLast }
    | .corrected => .next t'
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u

/--
The revised step of variant `v`.
It runs `evalInstruction checker script flags s i`.
A successful `OP_NOP4` in an executing branch, with `active` true, then goes through `lockCheck v`.
Without a checker, that case is unsupported with the stand-in reason `checkLockTimeVerify`.
Every other result passes unchanged.
-/
def lockStep (v : Variant) (active : Bool) (checker : Option SignatureChecker) (flags : UInt32) :
    Step ScriptError :=
  fun script s i =>
    match evalInstruction checker script flags s i with
    | .next t =>
      if active && isNop4 i.opcode && s.fExec then
        match checker with
        | none => .unsupported .checkLockTimeVerify
        | some c => lockCheck v c t
      else .next t
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u

/-- The revised `evalScript` of variant `v`: `evalScriptWith` with `lockStep v`. -/
def revisedEvalScript (v : Variant) (active : Bool) (checker : Option SignatureChecker) (flags : UInt32)
    (script : List UInt8) (stack : List (List UInt8)) : EvalOutcome ScriptError :=
  evalScriptWith id (lockStep v active checker flags) flags script stack

/-- The revised `verifyScript` of variant `v`: `verifyScriptWith` with `lockStep v`, for the checker `c`. -/
def revisedVerifyScript (v : Variant) (active : Bool) (c : SignatureChecker) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) : VerifyOutcome ScriptError :=
  verifyScriptWith id (lockStep v active (some c) flags) flags scriptSig scriptPubKey

/-- The revised spend predicate of one legacy input: `revisedVerifyScript` with the checker of `verifyLegacySpend`. -/
def revisedVerifyLegacySpend (v : Variant) (active : Bool) (ctx : InputContext)
    (prevScriptPubKey : Transaction.Script) (flags : UInt32) (verify : SignatureVerifier) :
    VerifyOutcome ScriptError :=
  revisedVerifyScript v active (transactionChecker ctx.tx ctx.index verify) flags ctx.input.scriptSig.bytes.val
    prevScriptPubKey.bytes.val

/-- The arguments of one spend check, other than the variant and `active`: the input, the previous `scriptPubKey`, the flags and the verifier. -/
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

/-- `revisedVerifyLegacySpend v` on spend arguments. -/
def revisedSpend (v : Variant) (active : Bool) (a : SpendArgs) : VerifyOutcome ScriptError :=
  revisedVerifyLegacySpend v active a.ctx a.prevScriptPubKey a.flags a.verify

/--
The scripts of the use predicate: a push of the bytes `b`, then `OP_NOP4`, then the script `S`.
The push opcode is the length of `b`: `OP_0` for the empty list, and a direct push for 1 to 75 bytes.
-/
def operandScript (b S : List UInt8) : List UInt8 := (b.length.toUInt8 :: b) ++ nop4 :: S

/--
The redefined rule runs in a spend: its previous `scriptPubKey` is `operandScript b S` for an operand `b` of at most 5 bytes.
The second instruction of that script is `OP_NOP4` at the top level, so it executes whenever the push before it succeeds.
-/
def RunsRule (a : SpendArgs) : Prop :=
  ∃ b S, b.length ≤ 5 ∧ a.prevScriptPubKey.bytes.val = operandScript b S

end DogeLib.Proposals.ExampleFaultyLocktime
