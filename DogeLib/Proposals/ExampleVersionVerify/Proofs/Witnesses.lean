module

public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Compatibility

/-!
# Proofs: `Proposals.ExampleVersionVerify`, witnesses

The example is not a proposal for Dogecoin (`DogeLib.Proposals.ExampleVersionVerify`).
A revision that rejects every input restricts acceptance, so a soft fork also needs two witnesses (design record 0007, section 8.1).
Both witnesses are one concrete spend, with the version of its transaction as the only difference:

- `witnessTx v`: version `v`, one input with an empty `scriptSig` and sequence 0, no outputs and lock time 0.
- The previous `scriptPubKey` is `01 02 b9`: a push of the operand 2, then `OP_NOP10`.
- No flags, and a verifier that is always unavailable. The scripts have no signature opcode, so no verifier call happens.

The theorems:

- `example_strict`: with version 1, the baseline accepts and the active revision rejects with `versionTooLow`.
- `example_use`: with version 2, the active revision accepts, and the scripts are in the domain of `RunsRule`.
- `example_softFork`: the spend predicate is a `SoftFork` of `verifyLegacySpend` in the sense of the framework.

The witnesses are computed by the kernel with `decide +kernel`. No digest is computed on these paths.
Every theorem is Script-local.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleVersionVerify

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

/-- The empty script. -/
def emptyScript : Transaction.Script := ⟨⟨[], by decide⟩⟩

/-- The previous `scriptPubKey` of the witnesses: `01 02 b9`, a push of the operand 2 and then `OP_NOP10`. -/
def witnessScriptPubKey : Transaction.Script := ⟨⟨operandScript [2] [], by decide⟩⟩

/-- A transaction with version `v`, one input with an empty `scriptSig` and sequence 0, no outputs and lock time 0. -/
def witnessTx (v : UInt32) : Transaction :=
  { version := v
    inputs := ⟨[{ prevout := OutPoint.null, scriptSig := emptyScript, sequence := 0 }], by decide⟩
    outputs := ⟨[], by decide⟩
    lockTime := 0 }

/-- The spend of the witnesses: input 0 of `witnessTx v`, the script `witnessScriptPubKey`, no flags and an unavailable verifier. -/
def witnessArgs (v : UInt32) : SpendArgs :=
  { ctx := ⟨witnessTx v, 0, by simp [witnessTx], by simp [witnessTx], by simp [witnessTx]⟩
    prevScriptPubKey := witnessScriptPubKey
    flags := 0
    verify := fun _ _ _ => none }

/--
`example_strict`, design record 0007, section 10.3.
With version 1, `verifyLegacySpend` accepts the witness spend, and the active revision rejects it with `versionTooLow`: the operand 2 is above the version.
Script-local.
-/
theorem example_strict :
    baselineSpend (witnessArgs 1) = .accepted ∧ revisedSpend true (witnessArgs 1) = .rejected (.inr .versionTooLow) := by
  decide +kernel

/--
`example_use`, design record 0007, section 10.3.
With version 2, the active revision accepts the witness spend.
Its previous `scriptPubKey` is `operandScript [2] []`, so the second instruction, `OP_NOP10`, executes at the top level with the operand 2.
Script-local.
-/
theorem example_use : revisedSpend true (witnessArgs 2) = .accepted ∧ RunsRule (witnessArgs 2) :=
  ⟨by decide +kernel, ⟨[2], [], by decide, rfl⟩⟩

/--
The spend predicate of the example is a soft fork of `verifyLegacySpend` at the level of one input, in the sense of the framework's `SoftFork`.
The embedding maps a baseline error under `Sum.inl`, and the use predicate is `RunsRule`.
Script-local: it is not a soft-fork claim about the network, which also needs block validity (design record 0007, section 8.3).
-/
theorem example_softFork :
    SoftFork (VerifyOutcome.ofBaseline Sum.inl) baselineVerdict VerifyOutcome.verdict RunsRule baselineSpend
      revisedSpend where
  inactive_eq := example_inactiveEq
  restricts := example_restrictsAcceptance
  strict := ⟨witnessArgs 1, by rw [example_strict.1]; rfl, by rw [example_strict.2]; rfl⟩
  use := ⟨witnessArgs 2, by rw [example_use.1]; rfl, example_use.2⟩

end DogeLib.Proposals.ExampleVersionVerify
