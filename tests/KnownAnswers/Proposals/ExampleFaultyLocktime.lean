import DogeLib.Proposals
import KnownAnswers.Script

/-!
## Proposals: the deliberately faulty example `ExampleFaultyLocktime`

`ExampleFaultyLocktime` is an invented proposal with a deliberate fault, kept as a teaching example and as a test of the framework.
It is not a proposal for Dogecoin.
These cases run the revised `verifyScript` and spend predicate of both variants through the compiled code.

Each expected result is derived by hand, never computed by DogeLib.
With `active` true, an executed `OP_NOP4` checks as `OP_CHECKLOCKTIMEVERIFY` with its flag set (D3, lines 360 to 390):

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The operand is the top item as a five-byte `CScriptNum` without the minimal requirement.
3. A negative operand gives `NEGATIVE_LOCKTIME`.
4. `CheckLockTime` (D3, lines 1274 to 1308) gives `UNSATISFIED_LOCKTIME` unless three conditions hold.
   The operand and `nLockTime` lie on the same side of 500,000,000, and the operand is at most `nLockTime`.
   The input's sequence is not `0xffffffff`.

After a successful check, the faulty variant pops the operand, and the corrected variant keeps it.
The inactive result of each case is also derived by hand: `OP_NOP4` is a NOP (D3, lines 429 to 435), and Core's `EvalScript` and `VerifyScript` (D3) give the rest.
Every case also checks that both variants with `active` false give the baseline `verifyScript` result.

Each transaction is `mkTx 1 lockTime sequence`: version 1, one input with an empty `scriptSig`, no outputs.
The cases cover the counterexample of `faulty_counterexample` and the spend of `corrected_use`.
They also cover each failed check, a skipped branch, a P2SH redeem script and an operand from `scriptSig`.
`DISCOURAGE_UPGRADABLE_NOPS` lies outside the supported flags, so that case is unsupported.
The 12 `verifyScript` cases run both variants with `active` true and with `active` false.
The 4 spend cases run `revisedVerifyLegacySpend` for both variants and the baseline `verifyLegacySpend`.
-/

namespace KnownAnswers.Proposals.ExampleFaultyLocktime

open DogeLib.Script DogeLib.Proposals.Framework DogeLib.Proposals.ExampleFaultyLocktime
open KnownAnswers.ScriptVerify (mkTx p2shOf)

/-- `transactionChecker` for input 0 of `mkTx 1 lockTime sequence`, with a verifier that is always unavailable. -/
def checkerOf (lockTime sequence : UInt32) : SignatureChecker :=
  transactionChecker (mkTx 1 lockTime sequence) 0 fun _ _ _ => none

/-- A `verifyScript` case: a label, the lock time, the sequence, flags, `scriptSig`, `scriptPubKey`, and the three expected results. -/
structure Case where
  label : String
  lockTime : UInt32 := 2
  sequence : UInt32 := 0xfffffffe
  flags : UInt32 := 0
  scriptSig : List UInt8 := []
  scriptPubKey : List UInt8
  faulty : VerifyOutcome ScriptError
  corrected : VerifyOutcome ScriptError
  inactive : VerifyOutcome ScriptError

/-- `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL`. -/
def counterexample : List UInt8 := [0x51, 0x52, 0xb3, 0x51, 0x87]

/-- A push of the operand 2, then `OP_NOP4 OP_DROP OP_1`: the usual shape of a lock-time spend. -/
def lockSpend : List UInt8 := [0x01, 0x02, 0xb3, 0x75, 0x51]

/-- The `verifyScript` cases. -/
def cases : List Case := [
  -- The counterexample. Baseline: `[1, 2, 1]` before `OP_EQUAL`, so `[1, false]` and `EVAL_FALSE`.
  -- Faulty: the check passes and pops 2, so `[1, 1]` before `OP_EQUAL` and `[true]`.
  { label := "counterexample", scriptPubKey := counterexample,
    faulty := .accepted, corrected := .rejected .evalFalse, inactive := .rejected .evalFalse },
  -- The same stack effect with the pushes in `scriptSig`: the relaxation does not depend on where the operand comes from.
  { label := "counterexample, operands from scriptSig", scriptSig := [0x51, 0x52], scriptPubKey := [0xb3, 0x51, 0x87],
    faulty := .accepted, corrected := .rejected .evalFalse, inactive := .rejected .evalFalse },
  -- A lock-time spend that meets the lock time. Faulty: the pop leaves an empty stack, so `OP_DROP` fails.
  { label := "lock-time spend, lock time 2", scriptPubKey := lockSpend,
    faulty := .rejected .invalidStackOperation, corrected := .accepted, inactive := .accepted },
  -- The operand 2 is above the lock time 1.
  { label := "lock-time spend, lock time 1", lockTime := 1, scriptPubKey := lockSpend,
    faulty := .rejected .unsatisfiedLocktime, corrected := .rejected .unsatisfiedLocktime, inactive := .accepted },
  -- A final sequence disables the lock time.
  { label := "lock-time spend, final sequence", sequence := 0xffffffff, scriptPubKey := lockSpend,
    faulty := .rejected .unsatisfiedLocktime, corrected := .rejected .unsatisfiedLocktime, inactive := .accepted },
  -- The operand 500,000,000 (`00 65 cd 1d`) is a time, and the lock time 2 is a height.
  { label := "operand and lock time of different types", scriptPubKey := [0x04, 0x00, 0x65, 0xcd, 0x1d, 0xb3],
    faulty := .rejected .unsatisfiedLocktime, corrected := .rejected .unsatisfiedLocktime, inactive := .accepted },
  -- `OP_NOP4` alone. Inactive: the stack stays empty, so `EVAL_FALSE`.
  { label := "empty stack", scriptPubKey := [0xb3],
    faulty := .rejected .invalidStackOperation, corrected := .rejected .invalidStackOperation,
    inactive := .rejected .evalFalse },
  -- `81` is -1.
  { label := "negative operand", scriptPubKey := [0x01, 0x81, 0xb3],
    faulty := .rejected .negativeLocktime, corrected := .rejected .negativeLocktime, inactive := .accepted },
  -- The operand alone. Faulty: the pop leaves an empty stack, so `EVAL_FALSE`.
  { label := "operand left on the stack", scriptPubKey := [0x01, 0x02, 0xb3],
    faulty := .rejected .evalFalse, corrected := .accepted, inactive := .accepted },
  -- `OP_0 OP_IF 05 OP_NOP4 OP_ENDIF OP_1`: the branch does not execute, so `OP_NOP4` stays a NOP.
  { label := "operand in a skipped branch", scriptPubKey := [0x00, 0x63, 0x01, 0x05, 0xb3, 0x68, 0x51],
    faulty := .accepted, corrected := .accepted, inactive := .accepted },
  -- `DISCOURAGE_UPGRADABLE_NOPS` (bit 7) is outside the supported flags.
  { label := "DISCOURAGE_UPGRADABLE_NOPS", flags := ScriptFlags.discourageUpgradableNops, scriptPubKey := counterexample,
    faulty := .unsupported (.flags 0x80), corrected := .unsupported (.flags 0x80), inactive := .unsupported (.flags 0x80) },
  -- P2SH: the redeem script is the lock-time spend, pushed by `scriptSig`.
  { label := "P2SH redeem lock-time spend", flags := ScriptFlags.p2sh, scriptSig := [0x05] ++ lockSpend,
    scriptPubKey := p2shOf lockSpend,
    faulty := .rejected .invalidStackOperation, corrected := .accepted, inactive := .accepted }
]

/-- Check a condition and report its label on failure. Returns the number of failures. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL ExampleFaultyLocktime: {label}"
  return 1

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let checker := checkerOf c.lockTime c.sequence
    let baseline := VerifyOutcome.ofBaseline id (verifyScript checker c.flags c.scriptSig c.scriptPubKey)
    for (v, expected) in [(Variant.faulty, c.faulty), (.corrected, c.corrected)] do
      let active := revisedVerifyScript v true checker c.flags c.scriptSig c.scriptPubKey
      let inactive := revisedVerifyScript v false checker c.flags c.scriptSig c.scriptPubKey
      failures := failures + (← require s!"{c.label}, {repr v}, active: got {repr active}" (decide (active = expected)))
      failures := failures + (← require s!"{c.label}, {repr v}, inactive: got {repr inactive}"
        (decide (inactive = c.inactive)))
      failures := failures + (← require s!"{c.label}, {repr v}, inactive against the baseline: got {repr baseline}"
        (decide (inactive = baseline)))
  -- The spend predicate on the witnesses of `faulty_counterexample`, `faulty_strict`, `corrected_strict` and `corrected_use`.
  let spend (lockTime : UInt32) : InputContext :=
    ⟨mkTx 1 lockTime 0xfffffffe, 0, by simp [mkTx], by simp [mkTx], by simp [mkTx]⟩
  let script (bytes : List UInt8) (h : bytes.length < 2 ^ 64) : DogeLib.Transaction.Script := ⟨⟨bytes, h⟩⟩
  let spendCases : List (String × UInt32 × DogeLib.Transaction.Script × VerifyResult × VerifyOutcome ScriptError ×
      VerifyOutcome ScriptError) := [
    ("counterexample, lock time 2", 2, script counterexample (by decide), .rejected .evalFalse, .accepted,
      .rejected .evalFalse),
    ("counterexample, lock time 1", 1, script counterexample (by decide), .rejected .evalFalse,
      .rejected .unsatisfiedLocktime, .rejected .unsatisfiedLocktime),
    ("lock-time spend, lock time 2", 2, script lockSpend (by decide), .accepted, .rejected .invalidStackOperation,
      .accepted),
    ("lock-time spend, lock time 1", 1, script lockSpend (by decide), .accepted, .rejected .unsatisfiedLocktime,
      .rejected .unsatisfiedLocktime)
  ]
  for (label, lockTime, prev, base, faulty, corrected) in spendCases do
    let got := verifyLegacySpend (spend lockTime) prev 0 fun _ _ _ => none
    failures := failures + (← require s!"spend {label}, baseline: got {repr got}" (decide (got = base)))
    for (v, expected) in [(Variant.faulty, faulty), (.corrected, corrected)] do
      let got := revisedVerifyLegacySpend v true (spend lockTime) prev 0 fun _ _ _ => none
      failures := failures + (← require s!"spend {label}, {repr v}: got {repr got}" (decide (got = expected)))
  IO.println s!"ExampleFaultyLocktime: {cases.length} verifyScript cases and {spendCases.length} spend cases, {failures} failures"
  return failures

end KnownAnswers.Proposals.ExampleFaultyLocktime
