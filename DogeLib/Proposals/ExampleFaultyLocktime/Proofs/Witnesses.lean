module

public import DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Compatibility

/-!
# Proofs: `Proposals.ExampleFaultyLocktime`, witnesses

The example is an invented, deliberately faulty proposal, not a proposal for Dogecoin (`DogeLib.Proposals.ExampleFaultyLocktime`).
Every witness is one concrete spend of input 0 of `spendTx lockTime`:

- `spendTx lockTime`: version 1, one input with an empty `scriptSig` and sequence `0xfffffffe`, no outputs, and the lock time `lockTime`.
- No flags, and a verifier that is always unavailable. The scripts have no signature opcode, so no verifier call happens.

The previous `scriptPubKey` is one of two scripts:

| Script | Bytes | Instructions |
| --- | --- | --- |
| `counterexampleScript` | `51 52 b3 51 87` | `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL` |
| `useScript` | `01 02 b3 75 51` | a push of 2, `OP_NOP4 OP_DROP OP_1` |

The lock time 2 meets the operand 2: both lie below `LOCKTIME_THRESHOLD`, 2 ≤ 2, and the sequence is not `SEQUENCE_FINAL`.
The lock time 1 does not meet it.

## The faulty variant

- `faultyStep_pops`, `faultyStep_not_restricts`: at `OP_NOP4` of the counterexample, the faulty step succeeds with a state that the baseline step does not give.
- `faulty_counterexample`: with lock time 2, `verifyLegacySpend` rejects the counterexample with `EVAL_FALSE`, and the active faulty revision accepts it.
- `faulty_not_restrictsAcceptance`, `faulty_not_softFork`: the faulty spend predicate does not restrict acceptance, so it is not a `SoftFork`.
- `faulty_strict`, `faulty_incompatible`: the faulty spend predicate also rejects a spend that the baseline accepts, so it is `Incompatible`.

## The corrected variant

- `corrected_counterexample`: the corrected revision rejects the counterexample with `EVAL_FALSE`, as the baseline does.
- `corrected_strict`: with lock time 1, the baseline accepts `useScript`, and the corrected revision rejects it with `UNSATISFIED_LOCKTIME`.
- `corrected_use`: with lock time 2, the corrected revision accepts `useScript`, and the scripts are in the domain of `RunsRule`.
- `corrected_softFork`: the corrected spend predicate is a `SoftFork` of `verifyLegacySpend` in the sense of the framework.

The kernel computes every witness with `decide +kernel`. No digest is computed on these paths.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleFaultyLocktime

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

/-- The empty script. -/
def emptyScript : Transaction.Script := ⟨⟨[], by decide⟩⟩

/-- `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL`: `51 52 b3 51 87`. -/
def counterexampleBytes : List UInt8 := [0x51, 0x52, nop4, 0x51, 0x87]

/-- The counterexample script, `counterexampleBytes`. -/
def counterexampleScript : Transaction.Script := ⟨⟨counterexampleBytes, by decide⟩⟩

/-- A push of the operand 2, then `OP_NOP4 OP_DROP OP_1`: `01 02 b3 75 51`. -/
def useScript : Transaction.Script := ⟨⟨operandScript [2] [0x75, 0x51], by decide⟩⟩

/-- A transaction with version 1, one input with an empty `scriptSig` and sequence `0xfffffffe`, no outputs and the lock time `lockTime`. -/
def spendTx (lockTime : UInt32) : Transaction :=
  { version := 1
    inputs := ⟨[{ prevout := OutPoint.null, scriptSig := emptyScript, sequence := 0xfffffffe }], by decide⟩
    outputs := ⟨[], by decide⟩
    lockTime }

/-- Input 0 of `spendTx lockTime`, the previous `scriptPubKey` `prev`, no flags and an unavailable verifier. -/
def spendArgs (lockTime : UInt32) (prev : Transaction.Script) : SpendArgs :=
  { ctx := ⟨spendTx lockTime, 0, by simp [spendTx], by simp [spendTx], by simp [spendTx]⟩
    prevScriptPubKey := prev
    flags := 0
    verify := fun _ _ _ => none }

/-- The checker of `spendArgs 2 prev`: `transactionChecker` for input 0 of `spendTx 2`. -/
def counterexampleChecker : SignatureChecker := transactionChecker (spendTx 2) 0 fun _ _ _ => none

/-- The state of the counterexample before `OP_NOP4`: the stack `[1, 2]`, from the bottom to the top, and the cursor 2. -/
def beforeNop4 : ExecState :=
  { stack := [[1], [2]], altstack := [], pc := 2, beginCodeHash := 0, vfExec := [], opCount := 0 }

/-- The instruction `OP_NOP4` at offset 2 of the counterexample. -/
def nop4Instruction : Instruction := { opcode := nop4, bytes := [nop4], pushed := [], next := 3 }

/-! ## The faulty variant -/

/--
At `OP_NOP4` of the counterexample, with the checker of lock time 2: the active faulty step succeeds with the stack `[1]`.
The baseline step succeeds with the stack `[1, 2]`. Both steps count the opcode.
-/
theorem faultyStep_pops :
    lockStep .faulty true (some counterexampleChecker) 0 counterexampleBytes beforeNop4 nop4Instruction =
        .next { beforeNop4 with stack := [[1]], opCount := 1 } ∧
      baselineStep id (some counterexampleChecker) 0 counterexampleBytes beforeNop4 nop4Instruction =
        .next { beforeNop4 with opCount := 1 } := by
  decide +kernel

/--
The active faulty step does not restrict the baseline step, for the checker of lock time 2 and no flags.
`faultyStep_pops` gives the instruction: the faulty step succeeds with a state that the baseline step does not give.
-/
theorem faultyStep_not_restricts :
    ¬ Restricts (lockStep .faulty true (some counterexampleChecker) 0) (baselineStep id (some counterexampleChecker) 0) := by
  intro h
  have := h counterexampleBytes beforeNop4 nop4Instruction _ faultyStep_pops.1
  rw [faultyStep_pops.2] at this
  revert this
  decide

/--
With lock time 2, `verifyLegacySpend` rejects the counterexample with `EVAL_FALSE`, and the active faulty revision accepts it.
The baseline stack before `OP_EQUAL` is `[1, 2, 1]`, so the final stack is `[1, false]`.
The faulty stack before `OP_EQUAL` is `[1, 1]`, so the final stack is `[true]`.
Script-local.
-/
theorem faulty_counterexample :
    baselineSpend (spendArgs 2 counterexampleScript) = .rejected .evalFalse ∧
      revisedSpend .faulty true (spendArgs 2 counterexampleScript) = .accepted := by
  decide +kernel

/--
The faulty spend predicate does not restrict acceptance: it accepts a spend that `verifyLegacySpend` rejects.
So the faulty rule cannot be deployed as a soft fork. Script-local.
-/
theorem faulty_not_restrictsAcceptance :
    ¬ RestrictsAcceptance baselineVerdict VerifyOutcome.verdict baselineSpend (revisedSpend .faulty) := by
  intro h
  have := h true (spendArgs 2 counterexampleScript) (by rw [faulty_counterexample.2]; rfl)
  rw [faulty_counterexample.1] at this
  cases this

/-- The faulty spend predicate is not a `SoftFork` of `verifyLegacySpend`, for any use predicate. Script-local. -/
theorem faulty_not_softFork (runs : SpendArgs → Prop) :
    ¬ SoftFork (VerifyOutcome.ofBaseline id) baselineVerdict VerifyOutcome.verdict runs baselineSpend
      (revisedSpend .faulty) :=
  fun h => faulty_not_restrictsAcceptance h.restricts

/--
With lock time 1, `verifyLegacySpend` accepts `useScript`, and the active faulty revision rejects it with `UNSATISFIED_LOCKTIME`.
Script-local.
-/
theorem faulty_strict :
    baselineSpend (spendArgs 1 useScript) = .accepted ∧
      revisedSpend .faulty true (spendArgs 1 useScript) = .rejected .unsatisfiedLocktime := by
  decide +kernel

/--
The faulty spend predicate is an `Incompatible` change of `verifyLegacySpend`: the inactive equality, a strictness witness and a relaxation witness.
Script-local.
-/
theorem faulty_incompatible :
    Incompatible (VerifyOutcome.ofBaseline id) baselineVerdict VerifyOutcome.verdict baselineSpend
      (revisedSpend .faulty) where
  inactive_eq := inactiveEq .faulty
  strict := ⟨spendArgs 1 useScript, by rw [faulty_strict.1]; rfl, by rw [faulty_strict.2]; rfl⟩
  relaxed := ⟨spendArgs 2 counterexampleScript, by rw [faulty_counterexample.2]; rfl,
    by rw [faulty_counterexample.1]; rfl⟩

/-! ## The corrected variant -/

/-- With lock time 2, the active corrected revision rejects the counterexample with `EVAL_FALSE`, as `verifyLegacySpend` does. Script-local. -/
theorem corrected_counterexample :
    revisedSpend .corrected true (spendArgs 2 counterexampleScript) = .rejected .evalFalse := by
  decide +kernel

/--
With lock time 1, `verifyLegacySpend` accepts `useScript`, and the active corrected revision rejects it with `UNSATISFIED_LOCKTIME`.
Script-local.
-/
theorem corrected_strict :
    baselineSpend (spendArgs 1 useScript) = .accepted ∧
      revisedSpend .corrected true (spendArgs 1 useScript) = .rejected .unsatisfiedLocktime := by
  decide +kernel

/--
With lock time 2, the active corrected revision accepts `useScript`.
Its previous `scriptPubKey` is `operandScript [2] [0x75, 0x51]`, so `OP_NOP4` executes at the top level with the operand 2.
Script-local.
-/
theorem corrected_use :
    revisedSpend .corrected true (spendArgs 2 useScript) = .accepted ∧ RunsRule (spendArgs 2 useScript) :=
  ⟨by decide +kernel, ⟨[2], [0x75, 0x51], by decide, rfl⟩⟩

/--
The corrected spend predicate is a soft fork of `verifyLegacySpend` at the level of one input, in the sense of the framework's `SoftFork`.
The embedding is `VerifyOutcome.ofBaseline id`, and the use predicate is `RunsRule`.
Script-local: it is not a soft-fork claim about the network, which also needs block validity (design record 0007, section 8.3).
-/
theorem corrected_softFork :
    SoftFork (VerifyOutcome.ofBaseline id) baselineVerdict VerifyOutcome.verdict RunsRule baselineSpend
      (revisedSpend .corrected) where
  inactive_eq := inactiveEq .corrected
  restricts := corrected_restrictsAcceptance
  strict := ⟨spendArgs 1 useScript, by rw [corrected_strict.1]; rfl, by rw [corrected_strict.2]; rfl⟩
  use := ⟨spendArgs 2 useScript, by rw [corrected_use.1]; rfl, corrected_use.2⟩

end DogeLib.Proposals.ExampleFaultyLocktime
