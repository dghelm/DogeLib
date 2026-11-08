import DogeLib.Proposals
import KnownAnswers.Script

/-!
## Proposals: the worked example `ExampleVersionVerify`

`ExampleVersionVerify` is the worked example of design record 0007, section 10. It is not a proposal for Dogecoin.
These cases run the revised `verifyScript`, `evalScript` and spend predicate through the compiled code.

Each expected result is derived by hand from the rule of section 10.1, never computed by DogeLib:

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The operand is the top item as a five-byte `CScriptNum` without the minimal requirement. A longer item gives `UNKNOWN_ERROR`.
3. A negative operand gives `negativeOperand`.
4. Without a transaction context the result is unsupported, with the reason `noContext`.
5. The version, read as an unsigned 32-bit value, below the operand gives `versionTooLow`.

The inactive result of each case is also derived by hand: `OP_NOP10` is a NOP, and Core's `EvalScript` and `VerifyScript` (D3) give the rest.
Every case also checks that the revision with `active` false gives the baseline `verifyScript` result, with the error under `Sum.inl`.

The cases cover each step of the rule and both sides of the version comparison.
They also cover a negative operand, negative zero, a six-byte operand and an unsigned version above 2^31.
Other cases put the operand in a branch that does not execute or in a P2SH redeem script.
Each of the 20 `verifyScript` cases runs with `active` true and with `active` false.
The 6 other cases run with `active` true, and the spend cases also run the baseline.
One case shows the error order of design record 0007, section 10.2: a caller's stack of 1,001 items gives `STACK_SIZE` before the example's own error.
-/

namespace KnownAnswers.Proposals.ExampleVersionVerify

open DogeLib.Script DogeLib.Proposals.Framework DogeLib.Proposals.ExampleVersionVerify
open KnownAnswers.ScriptVerify (mkTx p2shOf)

/-- The context of `mkTx version 0 0`. -/
def ctxOf (version : UInt32) : ExampleContext := ⟨mkTx version 0 0⟩

/-- `transactionChecker` for input 0 of `mkTx version 0 0`, with a verifier that is always unavailable. -/
def checkerOf (version : UInt32) : SignatureChecker := transactionChecker (mkTx version 0 0) 0 fun _ _ _ => none

/-- A `verifyScript` case: a label, the version, whether the context is present, flags, `scriptSig`, `scriptPubKey`, the active result and the inactive result. -/
structure Case where
  label : String
  version : UInt32
  context : Bool := true
  flags : UInt32 := 0
  scriptSig : List UInt8 := []
  scriptPubKey : List UInt8
  active : VerifyOutcome ExampleScriptError
  inactive : VerifyOutcome ExampleScriptError

/-- The redeem script of the P2SH cases: a push of the operand 3, then `OP_NOP10`. -/
def redeem : List UInt8 := [0x01, 0x03, 0xb9]

/-- The `verifyScript` cases. -/
def cases : List Case := [
  -- Step 1: `OP_NOP10` alone. Inactive: the stack stays empty, so `VerifyScript` gives `EVAL_FALSE`.
  { label := "empty stack", version := 2, scriptPubKey := [0xb9],
    active := .rejected (.inl .invalidStackOperation), inactive := .rejected (.inl .evalFalse) },
  -- Step 2: a push of six bytes `01 00 00 00 00 00` exceeds five bytes. Inactive: the top item is true.
  { label := "six-byte operand", version := 2, scriptPubKey := [0x06, 0x01, 0, 0, 0, 0, 0, 0xb9],
    active := .rejected (.inl .unknownError), inactive := .accepted },
  -- Step 3: `81` is -1. Inactive: `81` is true.
  { label := "negative operand", version := 2, scriptPubKey := [0x01, 0x81, 0xb9],
    active := .rejected (.inr .negativeOperand), inactive := .accepted },
  -- `OP_1NEGATE` pushes -1.
  { label := "OP_1NEGATE operand", version := 2, scriptPubKey := [0x4f, 0xb9],
    active := .rejected (.inr .negativeOperand), inactive := .accepted },
  -- `80` is negative zero, which is 0 and not negative, and is not minimal. `OP_DROP OP_1` leaves a true top.
  { label := "negative zero operand", version := 0, scriptPubKey := [0x01, 0x80, 0xb9, 0x75, 0x51],
    active := .accepted, inactive := .accepted },
  -- `OP_0` pushes the empty operand 0, which every version meets. `OP_1` leaves a true top.
  { label := "empty operand", version := 0, scriptPubKey := [0x00, 0xb9, 0x51],
    active := .accepted, inactive := .accepted },
  -- Step 5, both sides of the comparison with version 2.
  { label := "operand 1, version 2", version := 2, scriptPubKey := [0x01, 0x01, 0xb9],
    active := .accepted, inactive := .accepted },
  { label := "operand 2, version 2", version := 2, scriptPubKey := [0x01, 0x02, 0xb9],
    active := .accepted, inactive := .accepted },
  { label := "operand 3, version 2", version := 2, scriptPubKey := [0x01, 0x03, 0xb9],
    active := .rejected (.inr .versionTooLow), inactive := .accepted },
  -- `OP_16` pushes 16.
  { label := "OP_16 operand, version 2", version := 2, scriptPubKey := [0x60, 0xb9],
    active := .rejected (.inr .versionTooLow), inactive := .accepted },
  -- `ff ff ff ff 00` is 4294967295. The version bits `ffffffff` are -1 as Core's `int32_t`, and 4294967295 unsigned.
  { label := "five-byte operand 2^32 - 1, version ffffffff", version := 0xffffffff,
    scriptPubKey := [0x05, 0xff, 0xff, 0xff, 0xff, 0x00, 0xb9], active := .accepted, inactive := .accepted },
  { label := "five-byte operand 2^32 - 1, version fffffffe", version := 0xfffffffe,
    scriptPubKey := [0x05, 0xff, 0xff, 0xff, 0xff, 0x00, 0xb9],
    active := .rejected (.inr .versionTooLow), inactive := .accepted },
  -- `OP_0 OP_IF 05 OP_NOP10 OP_ENDIF OP_1`: the branch does not execute, so `OP_NOP10` stays a NOP.
  { label := "operand in a skipped branch", version := 2, scriptPubKey := [0x00, 0x63, 0x01, 0x05, 0xb9, 0x68, 0x51],
    active := .accepted, inactive := .accepted },
  -- The same script with `OP_1 OP_IF`: the branch executes, and 5 is above the version.
  { label := "operand in an executed branch", version := 2, scriptPubKey := [0x51, 0x63, 0x01, 0x05, 0xb9, 0x68, 0x51],
    active := .rejected (.inr .versionTooLow), inactive := .accepted },
  -- Step 4: no context. The rule reaches the context only after a decoded, nonnegative operand.
  { label := "no context", version := 2, context := false, scriptPubKey := [0x01, 0x02, 0xb9],
    active := .unsupported noContext, inactive := .accepted },
  { label := "no context, negative operand", version := 2, context := false, scriptPubKey := [0x01, 0x81, 0xb9],
    active := .rejected (.inr .negativeOperand), inactive := .accepted },
  { label := "no context, empty stack", version := 2, context := false, scriptPubKey := [0xb9],
    active := .rejected (.inl .invalidStackOperation), inactive := .rejected (.inl .evalFalse) },
  -- The operand comes from `scriptSig`, and `OP_NOP10` runs in `scriptPubKey`.
  { label := "operand from scriptSig", version := 2, scriptSig := [0x01, 0x03], scriptPubKey := [0xb9],
    active := .rejected (.inr .versionTooLow), inactive := .accepted },
  -- P2SH: the redeem script pushes 3 and runs `OP_NOP10`. Its top item 3 is true.
  { label := "P2SH redeem, version 2", version := 2, flags := ScriptFlags.p2sh, scriptSig := [0x03] ++ redeem,
    scriptPubKey := p2shOf redeem, active := .rejected (.inr .versionTooLow), inactive := .accepted },
  { label := "P2SH redeem, version 3", version := 3, flags := ScriptFlags.p2sh, scriptSig := [0x03] ++ redeem,
    scriptPubKey := p2shOf redeem, active := .accepted, inactive := .accepted }
]

/-- Check a condition and report its label on failure. Returns the number of failures. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL ExampleVersionVerify: {label}"
  return 1

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let ctx := if c.context then some (ctxOf c.version) else none
    let checker := checkerOf c.version
    let active := exampleVerifyScript true ctx checker c.flags c.scriptSig c.scriptPubKey
    let inactive := exampleVerifyScript false ctx checker c.flags c.scriptSig c.scriptPubKey
    let baseline := VerifyOutcome.ofBaseline Sum.inl (verifyScript checker c.flags c.scriptSig c.scriptPubKey)
    failures := failures + (← require s!"{c.label}, active: got {repr active}" (decide (active = c.active)))
    failures := failures + (← require s!"{c.label}, inactive: got {repr inactive}" (decide (inactive = c.inactive)))
    failures := failures + (← require s!"{c.label}, inactive against the baseline: got {repr baseline}"
      (decide (inactive = baseline)))
  -- Design record 0007, section 10.2: 1,001 copies of the operand 5 on the caller's stack.
  -- The baseline step rejects the stack size after the NOP, before the example compares 5 with the version 2.
  let big : List (List UInt8) := List.replicate 1001 [0x05]
  let r := exampleEvalScript true (some (ctxOf 2)) none 0 [0xb9] big
  failures := failures + (← require s!"stack of 1,001 items: got {repr r}" (decide (r = .rejected (.inl .stackSize))))
  -- `evalScript` without a checker: the rule reads only the context. The stack keeps the operand.
  let r := exampleEvalScript true (some (ctxOf 2)) none 0 [0x01, 0x02, 0xb9] []
  let okStack := match r with
    | .ok s => s.stack == [[0x02]]
    | _ => false
  failures := failures + (← require s!"evalScript without a checker: got {repr r}" okStack)
  -- The spend predicate on the witnesses of `example_strict` and `example_use`.
  let spend (version : UInt32) : InputContext := ⟨mkTx version 0 0, 0, by simp [mkTx], by simp [mkTx], by simp [mkTx]⟩
  let prev : DogeLib.Transaction.Script := ⟨⟨[0x01, 0x02, 0xb9], by decide⟩⟩
  for (version, expected) in [((1 : UInt32), (VerifyOutcome.rejected (.inr .versionTooLow) :
      VerifyOutcome ExampleScriptError)), (2, .accepted)] do
    let got := exampleVerifyLegacySpend true (spend version) prev 0 fun _ _ _ => none
    failures := failures + (← require s!"spend, version {version}: got {repr got}" (decide (got = expected)))
    let base := verifyLegacySpend (spend version) prev 0 fun _ _ _ => none
    failures := failures + (← require s!"spend, version {version}, baseline: got {repr base}"
      (decide (base = .accepted)))
  IO.println s!"ExampleVersionVerify: {cases.length} verifyScript cases and 6 other cases, {failures} failures"
  return failures

end KnownAnswers.Proposals.ExampleVersionVerify
