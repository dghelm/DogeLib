module

public import DogeLib.Proposals.ExampleFaultyLocktime
public import DogeLib.Proposals.Framework.Proofs.Compatibility
public import DogeLib.Script.Proofs.Eval
public import DogeLib.Script.Proofs.Verify

/-!
# Proofs: `Proposals.ExampleFaultyLocktime`, compatibility

The example is an invented, deliberately faulty proposal, not a proposal for Dogecoin (`DogeLib.Proposals.ExampleFaultyLocktime`).
Every theorem here is Script-local: it is about one call of `evalScript`, `verifyScript` or `verifyLegacySpend`, not about a block or a chain.

## The step

- `lockStep_false`: with `active` false, the step of each variant is the baseline step.
- `lockCheck_corrected_next`: a successful corrected check leaves the state unchanged.
- `correctedStep_restricts`: the corrected step restricts the baseline step, for every `active`, checker and flag set.

`DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Witnesses` proves that the faulty step does not restrict the baseline step.

## Inactive equality

- `revisedVerifyScript_inactive_eq`, `revisedSpend_inactive_eq`, `inactiveEq`: with `active` false, the revised `verifyScript` and spend predicate of each variant equal the baseline results.
  The equality covers every result: acceptance, each rejection and each unsupported capability.

## Restriction of acceptance

- `corrected_verifyScript_soft_fork_local`: if the corrected `verifyScript` accepts, `verifyScript` accepts with the same checker, flags and scripts.
- `corrected_soft_fork_local`: if the corrected spend predicate accepts an input, `verifyLegacySpend` accepts it with the same flags and verifier.
- `corrected_restrictsAcceptance`: the corrected spend predicate has the framework's restriction of acceptance.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleFaultyLocktime

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

variable {ε₀ : Type}

/-! ## The step -/

/-- For every variant, checker and flag set: the step with `active` false is the baseline step, with the error map `id`. -/
theorem lockStep_false (v : Variant) (checker : Option SignatureChecker) (flags : UInt32) :
    lockStep v false checker flags = baselineStep id checker flags := by
  funext script s i
  simp only [lockStep, baselineStep, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases evalInstruction checker script flags s i <;> rfl

/-- For every checker and states `t` and `t'`: if the corrected check of `t` succeeds with `t'`, then `t'` is `t`. -/
theorem lockCheck_corrected_next {c : SignatureChecker} {t t' : ExecState}
    (h : lockCheck .corrected c t = .next t') : t' = t := by
  unfold lockCheck at h
  cases hc : checkLockTimeStep c t with
  | next u =>
    rw [hc] at h
    cases h
    exact checkLockTimeStep_next hc
  | rejected e => rw [hc] at h; cases h
  | unsupported u => rw [hc] at h; cases h

/--
For every `active`, checker, flag set and error map `embed₀`: the corrected step restricts the baseline step.
Every successful corrected step is a successful baseline step with the same state.
-/
theorem correctedStep_restricts (embed₀ : ScriptError → ε₀) (active : Bool) (checker : Option SignatureChecker)
    (flags : UInt32) : Restricts (lockStep .corrected active checker flags) (baselineStep embed₀ checker flags) := by
  intro script s i t h
  simp only [lockStep] at h
  simp only [baselineStep]
  cases he : evalInstruction checker script flags s i with
  | next t₀ =>
    rw [he] at h
    simp only at h
    split at h
    · split at h
      · cases h
      · rw [lockCheck_corrected_next h]; rfl
    · cases h; rfl
  | rejected e => rw [he] at h; cases h
  | unsupported u => rw [he] at h; cases h

/-! ## Inactive equality -/

/--
For every variant, checker `c`, flag set, `scriptSig` and `scriptPubKey`: with `active` false, the revised `verifyScript` equals `verifyScript`.
The P2SH evaluation is included. Script-local.
-/
theorem revisedVerifyScript_inactive_eq (v : Variant) (c : SignatureChecker) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) :
    revisedVerifyScript v false c flags scriptSig scriptPubKey =
      .ofBaseline id (verifyScript c flags scriptSig scriptPubKey) := by
  simp only [revisedVerifyScript, lockStep_false]
  exact verifyScriptWith_baseline id c flags scriptSig scriptPubKey

/-- For every variant and spend arguments: with `active` false, the revised spend predicate equals `verifyLegacySpend`. Script-local. -/
theorem revisedSpend_inactive_eq (v : Variant) (a : SpendArgs) :
    revisedSpend v false a = .ofBaseline id (baselineSpend a) :=
  revisedVerifyScript_inactive_eq v _ _ _ _

/-- For every variant, the spend predicate has the framework's inactive equality, over `SpendArgs`. Script-local. -/
theorem inactiveEq (v : Variant) : InactiveEq (VerifyOutcome.ofBaseline id) baselineSpend (revisedSpend v) :=
  revisedSpend_inactive_eq v

/-! ## Restriction of acceptance -/

/--
For every `active`, checker `c`, flag set, `scriptSig` and `scriptPubKey`:
if the corrected `verifyScript` accepts, `verifyScript c flags` accepts the same scripts.
The P2SH evaluation is included. Script-local.
-/
theorem corrected_verifyScript_soft_fork_local {active : Bool} {c : SignatureChecker} {flags : UInt32}
    {scriptSig scriptPubKey : List UInt8}
    (h : revisedVerifyScript .corrected active c flags scriptSig scriptPubKey = .accepted) :
    verifyScript c flags scriptSig scriptPubKey = .accepted :=
  verifyScript_of_restricts id (correctedStep_restricts id active (some c) flags) scriptSig scriptPubKey h

/--
For every `active` and spend arguments: if the corrected spend predicate accepts the input, `verifyLegacySpend` accepts it with the same flags and verifier.
Script-local: the theorem is about one input, not about a block or the network.
-/
theorem corrected_soft_fork_local {active : Bool} {a : SpendArgs} (h : revisedSpend .corrected active a = .accepted) :
    baselineSpend a = .accepted :=
  corrected_verifyScript_soft_fork_local h

/-- The corrected spend predicate has the framework's restriction of acceptance, over `SpendArgs`. Script-local. -/
theorem corrected_restrictsAcceptance :
    RestrictsAcceptance baselineVerdict VerifyOutcome.verdict baselineSpend (revisedSpend .corrected) := by
  intro active a h
  rw [VerifyOutcome.verdict_eq_accepted] at h
  rw [baselineVerdict_eq_accepted]
  exact corrected_soft_fork_local h

end DogeLib.Proposals.ExampleFaultyLocktime
