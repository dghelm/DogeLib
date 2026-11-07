module

public import DogeLib.Proposals.Framework.Compatibility
public import DogeLib.Proposals.Framework.Proofs.Script

/-!
# Proofs: `Proposals.Framework.Compatibility`

## Verdicts

- `baselineVerdict_eq_accepted`, `VerifyOutcome.verdict_eq_accepted`: a result has the verdict `accepted` exactly when it is `accepted`.
- `VerifyOutcome.verdict_ofBaseline`: mapping the error of a baseline result does not change its verdict.

## Shapes from the step

A revision of `VerifyScript` at the level of one check has a context type `κ`.
Functions map a context to the checker, the flags, `scriptSig` and `scriptPubKey`.
The revised step can depend on `active` and on the context.

- `inactiveEq_verifyScriptWith`: if the revised step with `active` false is the baseline step, the revision has the inactive equality.
- `restrictsAcceptance_verifyScriptWith`: if the revised step restricts the baseline step for every `active` and context, the revision restricts acceptance.

These two theorems reduce the inactive equality and restriction of acceptance of a Script revision to properties of its step.
Both are Script-local. They say nothing about block validity or the network.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Script

variable {ε ε₀ κ : Type}

/-- For every baseline `VerifyScript` result `r`: its verdict is `accepted` exactly when `r` is `accepted`. -/
theorem baselineVerdict_eq_accepted {r : VerifyResult} : baselineVerdict r = .accepted ↔ r = .accepted := by
  cases r <;> simp [baselineVerdict]

/-- For every framework `VerifyScript` result `r`: its verdict is `accepted` exactly when `r` is `accepted`. -/
theorem VerifyOutcome.verdict_eq_accepted {r : VerifyOutcome ε} : r.verdict = .accepted ↔ r = .accepted := by
  cases r <;> simp [VerifyOutcome.verdict]

/-- For every error map `embed` and baseline `VerifyScript` result `r`: the mapped result has the verdict of `r`. -/
theorem VerifyOutcome.verdict_ofBaseline (embed : ScriptError → ε) (r : VerifyResult) :
    (VerifyOutcome.ofBaseline embed r).verdict = baselineVerdict r := by
  cases r <;> rfl

/--
This holds for every context type `κ`, every map from a context to a checker, flags, `scriptSig` and `scriptPubKey`, and every error map `embed`.
Let the revised step `step false ctx` be the baseline step for the context's checker and flags.
Then the revision `verifyScriptWith embed (step active ctx)` has the inactive equality with `verifyScript`.
The embedding is `VerifyOutcome.ofBaseline embed`.
-/
theorem inactiveEq_verifyScriptWith (checker : κ → SignatureChecker) (flags : κ → UInt32)
    (scriptSig scriptPubKey : κ → List UInt8) (embed : ScriptError → ε) (step : Bool → κ → Step ε)
    (hstep : ∀ ctx, step false ctx = baselineStep embed (some (checker ctx)) (flags ctx)) :
    InactiveEq (VerifyOutcome.ofBaseline embed)
      (fun ctx => verifyScript (checker ctx) (flags ctx) (scriptSig ctx) (scriptPubKey ctx))
      (fun active ctx => verifyScriptWith embed (step active ctx) (flags ctx) (scriptSig ctx) (scriptPubKey ctx)) := by
  intro ctx
  simp only [hstep]
  exact verifyScriptWith_baseline embed (checker ctx) (flags ctx) (scriptSig ctx) (scriptPubKey ctx)

/--
This holds for every context type `κ`, every map from a context to a checker, flags and scripts, and all error maps `embed` and `embed₀`.
Let the revised step `step active ctx` restrict the baseline step for the context's checker and flags, for every `active` and context.
Then the revision `verifyScriptWith embed (step active ctx)` restricts the acceptance of `verifyScript`.
-/
theorem restrictsAcceptance_verifyScriptWith (checker : κ → SignatureChecker) (flags : κ → UInt32)
    (scriptSig scriptPubKey : κ → List UInt8) (embed : ScriptError → ε) (embed₀ : ScriptError → ε₀)
    (step : Bool → κ → Step ε)
    (hres : ∀ active ctx, Restricts (step active ctx) (baselineStep embed₀ (some (checker ctx)) (flags ctx))) :
    RestrictsAcceptance baselineVerdict VerifyOutcome.verdict
      (fun ctx => verifyScript (checker ctx) (flags ctx) (scriptSig ctx) (scriptPubKey ctx))
      (fun active ctx => verifyScriptWith embed (step active ctx) (flags ctx) (scriptSig ctx) (scriptPubKey ctx)) := by
  intro active ctx hacc
  rw [VerifyOutcome.verdict_eq_accepted] at hacc
  rw [baselineVerdict_eq_accepted]
  exact verifyScript_of_restricts embed₀ (hres active ctx) (scriptSig ctx) (scriptPubKey ctx) hacc

end DogeLib.Proposals.Framework
