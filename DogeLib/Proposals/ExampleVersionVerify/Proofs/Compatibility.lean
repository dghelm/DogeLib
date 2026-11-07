module

public import DogeLib.Proposals.ExampleVersionVerify
public import DogeLib.Proposals.Framework.Proofs.Compatibility
public import DogeLib.Script.Proofs.Verify

/-!
# Proofs: `Proposals.ExampleVersionVerify`, compatibility

The example is not a proposal for Dogecoin (`DogeLib.Proposals.ExampleVersionVerify`).
Every theorem here is Script-local: it is about one call of `evalScript`, `verifyScript` or `verifyLegacySpend`, not about a block or a chain.

## The step

- `versionCheck_next`: a successful `versionCheck` leaves the state unchanged.
- `exampleStep_false`: with `active` false, the example step is the baseline step.
- `exampleStep_restricts`: the example step restricts the baseline step, for every `active`, context, checker and flag set.
- `exampleStep_eq_of_not_nop10`: at an instruction other than `OP_NOP10`, the example step is the baseline step.

## Inactive equality

- `example_evalScript_inactive_eq`, `example_inactive_eq`, `example_spend_inactive_eq`: with `active` false, the revised `evalScript`, `verifyScript` and spend predicate equal the baseline results, with the errors under `Sum.inl`.
  The equality covers every result: acceptance, each rejection and each unsupported capability.

## Restriction of acceptance

- `example_verifyScript_soft_fork_local`: if the revised `verifyScript` accepts, `verifyScript` accepts with the same checker, flags and scripts.
- `example_soft_fork_local`: if the revised spend predicate accepts an input, `verifyLegacySpend` accepts it with the same flags and verifier.

## Agreement outside the redefined rule

- `example_evalScript_eq_of_no_nop10`, `example_eq_of_no_nop10`: on scripts with no instruction `0xb9`, the revised result equals the baseline result for every `active` and context.
  A Core comparison of the baseline then applies to those scripts too (design record 0007, section 9).

## Legacy projection

- `projection_eq_identity`: the projection of the example is the identity.
- `example_step_state`, `example_evalScript_state`: a successful revised step, or evaluation, gives the baseline success with the projected state.
- `example_soft_fork_projected`: if the revised spend predicate accepts an input, `verifyLegacySpend` accepts its projection.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleVersionVerify

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

variable {ε₀ : Type}

/-! ## The step -/

/-- For every context and states `t` and `t'`: if `versionCheck ctx t` succeeds with `t'`, then `t'` is `t`. -/
theorem versionCheck_next {ctx : Option ExampleContext} {t t' : ExecState}
    (h : versionCheck ctx t = .next t') : t' = t := by
  unfold versionCheck at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h; rfl
          · cases h

/-- For every context, checker and flag set: the example step with `active` false is the baseline step, with the errors under `Sum.inl`. -/
theorem exampleStep_false (ctx : Option ExampleContext) (checker : Option SignatureChecker) (flags : UInt32) :
    exampleStep false ctx checker flags = baselineStep Sum.inl checker flags := by
  funext script s i
  simp only [exampleStep, baselineStep]
  cases evalInstruction checker script flags s i <;> rfl

/--
For every `active`, context, checker, flag set and error map `embed₀`: the example step restricts the baseline step.
Every successful example step is a successful baseline step with the same state.
-/
theorem exampleStep_restricts (embed₀ : ScriptError → ε₀) (active : Bool) (ctx : Option ExampleContext)
    (checker : Option SignatureChecker) (flags : UInt32) :
    Restricts (exampleStep active ctx checker flags) (baselineStep embed₀ checker flags) := by
  intro script s i t h
  simp only [exampleStep] at h
  simp only [baselineStep]
  cases he : evalInstruction checker script flags s i with
  | next t₀ =>
    rw [he] at h
    simp only at h
    split at h
    · rw [versionCheck_next h]; rfl
    · cases h; rfl
  | rejected e => rw [he] at h; cases h
  | unsupported u => rw [he] at h; cases h

/-- For every `active`, context, checker, flag set, script and state: at an instruction whose opcode is not `0xb9`, the example step is the baseline step. -/
theorem exampleStep_eq_of_not_nop10 (active : Bool) (ctx : Option ExampleContext) (checker : Option SignatureChecker)
    (flags : UInt32) (script : List UInt8) (s : ExecState) (i : Instruction) (hi : isNop10 i.opcode = false) :
    exampleStep active ctx checker flags script s i = baselineStep Sum.inl checker flags script s i := by
  simp only [exampleStep, baselineStep, hi, Bool.and_false, Bool.false_and]
  cases evalInstruction checker script flags s i <;> rfl

/-! ## Inactive equality -/

/--
For every context, checker, flag set, script and stack: with `active` false, the revised `evalScript` equals `evalScript`, with the error under `Sum.inl`.
Script-local.
-/
theorem example_evalScript_inactive_eq (ctx : Option ExampleContext) (checker : Option SignatureChecker)
    (flags : UInt32) (script : List UInt8) (stack : List (List UInt8)) :
    exampleEvalScript false ctx checker flags script stack =
      .ofBaseline Sum.inl (evalScript checker flags script stack) := by
  simp only [exampleEvalScript, exampleStep_false]
  exact evalScriptWith_baseline Sum.inl checker flags script stack

/--
`example_inactive_eq`, design record 0007, section 10.3.
For every context, checker `c`, flag set, `scriptSig` and `scriptPubKey`: with `active` false, the revised `verifyScript` equals `verifyScript`, with the error under `Sum.inl`.
The P2SH evaluation is included. Script-local.
-/
theorem example_inactive_eq (ctx : Option ExampleContext) (c : SignatureChecker) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) :
    exampleVerifyScript false ctx c flags scriptSig scriptPubKey =
      .ofBaseline Sum.inl (verifyScript c flags scriptSig scriptPubKey) := by
  simp only [exampleVerifyScript, exampleStep_false]
  exact verifyScriptWith_baseline Sum.inl c flags scriptSig scriptPubKey

/--
For every input, previous `scriptPubKey`, flag set and verifier: with `active` false, the revised spend predicate equals `verifyLegacySpend`, with the error under `Sum.inl`.
Script-local.
-/
theorem example_spend_inactive_eq (ctx : InputContext) (prevScriptPubKey : Transaction.Script) (flags : UInt32)
    (verify : SignatureVerifier) :
    exampleVerifyLegacySpend false ctx prevScriptPubKey flags verify =
      .ofBaseline Sum.inl (verifyLegacySpend ctx prevScriptPubKey flags verify) :=
  example_inactive_eq _ _ _ _ _

/-- The spend predicate has the framework's inactive equality, over `SpendArgs`. Script-local. -/
theorem example_inactiveEq : InactiveEq (VerifyOutcome.ofBaseline Sum.inl) baselineSpend revisedSpend :=
  fun a => example_spend_inactive_eq a.ctx a.prevScriptPubKey a.flags a.verify

/-! ## Restriction of acceptance -/

/--
For every `active`, context, checker `c`, flag set, `scriptSig` and `scriptPubKey`:
if the revised `verifyScript` accepts, `verifyScript c flags` accepts the same scripts.
The P2SH evaluation is included. Script-local.
-/
theorem example_verifyScript_soft_fork_local {active : Bool} {ctx : Option ExampleContext} {c : SignatureChecker}
    {flags : UInt32} {scriptSig scriptPubKey : List UInt8}
    (h : exampleVerifyScript active ctx c flags scriptSig scriptPubKey = .accepted) :
    verifyScript c flags scriptSig scriptPubKey = .accepted :=
  verifyScript_of_restricts id (exampleStep_restricts id active ctx (some c) flags) scriptSig scriptPubKey h

/--
`example_soft_fork_local`, design record 0007, section 10.3.
This holds for every `active`, input, previous `scriptPubKey`, flag set and verifier.
If the revised spend predicate accepts the input, `verifyLegacySpend` accepts it with the same flags and verifier.
Script-local: the theorem is about one input, not about a block or the network.
-/
theorem example_soft_fork_local {active : Bool} {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier}
    (h : exampleVerifyLegacySpend active ctx prevScriptPubKey flags verify = .accepted) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted :=
  example_verifyScript_soft_fork_local h

/-- The spend predicate has the framework's restriction of acceptance, over `SpendArgs`. Script-local. -/
theorem example_restrictsAcceptance :
    RestrictsAcceptance baselineVerdict VerifyOutcome.verdict baselineSpend revisedSpend := by
  intro active a h
  rw [VerifyOutcome.verdict_eq_accepted] at h
  rw [baselineVerdict_eq_accepted]
  exact example_soft_fork_local h

/-! ## Agreement outside the redefined rule -/

/--
This holds for every `active`, context, checker, flag set and stack.
On a script with no instruction `0xb9`, the revised `evalScript` equals `evalScript`, with the error under `Sum.inl`.
Every instruction counts, also one in a branch that does not execute. Script-local.
-/
theorem example_evalScript_eq_of_no_nop10 (active : Bool) (ctx : Option ExampleContext)
    (checker : Option SignatureChecker) (flags : UInt32) {script : List UInt8} (stack : List (List UInt8))
    (hfree : opcodeFree isNop10 script = true) :
    exampleEvalScript active ctx checker flags script stack =
      .ofBaseline Sum.inl (evalScript checker flags script stack) := by
  unfold exampleEvalScript
  rw [evalScriptWith_congr (step₂ := baselineStep Sum.inl checker flags)
    (fun s i hi => exampleStep_eq_of_not_nop10 active ctx checker flags script s i hi) flags stack hfree]
  exact evalScriptWith_baseline Sum.inl checker flags script stack

/--
`example_eq_of_no_nop10`, design record 0007, section 10.3. Script-local.
This holds for every `active`, context, checker `c` and flag set.
Let `scriptSig` and `scriptPubKey` have no instruction `0xb9`, also in a branch that does not execute.
Let every redeem script that the P2SH evaluation can take have none either: the top item of each final stack of `scriptSig` under `evalScript`.
Then the revised `verifyScript` equals `verifyScript`, with the error under `Sum.inl`.
-/
theorem example_eq_of_no_nop10 (active : Bool) (ctx : Option ExampleContext) (c : SignatureChecker) (flags : UInt32)
    {scriptSig scriptPubKey : List UInt8} (hsig : opcodeFree isNop10 scriptSig = true)
    (hpub : opcodeFree isNop10 scriptPubKey = true)
    (hredeem : ∀ s redeem rest, evalScript (some c) flags scriptSig [] = .ok s →
      s.stack.reverse = redeem :: rest → opcodeFree isNop10 redeem = true) :
    exampleVerifyScript active ctx c flags scriptSig scriptPubKey =
      .ofBaseline Sum.inl (verifyScript c flags scriptSig scriptPubKey) := by
  unfold exampleVerifyScript
  have hstep : ∀ script s i, isNop10 i.opcode = false →
      exampleStep active ctx (some c) flags script s i = baselineStep Sum.inl (some c) flags script s i :=
    fun script s i hi => exampleStep_eq_of_not_nop10 active ctx (some c) flags script s i hi
  rw [verifyScriptWith_congr (step₂ := baselineStep Sum.inl (some c) flags) hstep flags hsig hpub ?_]
  · exact verifyScriptWith_baseline Sum.inl c flags scriptSig scriptPubKey
  · intro s redeem rest hs hsr
    have h := example_evalScript_eq_of_no_nop10 active ctx (some c) flags [] hsig
    unfold exampleEvalScript at h
    rw [h] at hs
    apply hredeem s redeem rest _ hsr
    cases he : evalScript (some c) flags scriptSig [] <;> rw [he] at hs <;> cases hs
    rfl

/-! ## Legacy projection -/

/-- The projection of the example is the identity on input contexts and on Script states. -/
theorem projection_eq_identity : projection = LegacyProjection.identity InputContext ExecState := rfl

/--
This holds for every `active`, context, checker, flag set, script, state `s` and instruction `i`.
If the example step succeeds with `t`, then `evalInstruction` succeeds with the projected state of `t`, which is `t`.
-/
theorem example_step_state {active : Bool} {ctx : Option ExampleContext} {checker : Option SignatureChecker}
    {flags : UInt32} {script : List UInt8} {s t : ExecState} {i : Instruction}
    (h : exampleStep active ctx checker flags script s i = .next t) :
    evalInstruction checker script flags s i = .next (projection.state t) := by
  have := exampleStep_restricts id active ctx checker flags script s i t h
  simp only [baselineStep] at this
  cases he : evalInstruction checker script flags s i <;> rw [he] at this <;> cases this
  rfl

/--
This holds for every `active`, context, checker, flag set, script and stack.
If the revised `evalScript` succeeds with the final state `t`, then `evalScript` succeeds with the projected state of `t`, which is `t`.
Script-local.
-/
theorem example_evalScript_state {active : Bool} {ctx : Option ExampleContext} {checker : Option SignatureChecker}
    {flags : UInt32} {script : List UInt8} {stack : List (List UInt8)} {t : ExecState}
    (h : exampleEvalScript active ctx checker flags script stack = .ok t) :
    evalScript checker flags script stack = .ok (projection.state t) := by
  have := evalScriptWith_restricts (embed₀ := id) (exampleStep_restricts id active ctx checker flags) flags script
    stack t h
  rw [evalScriptWith_baseline] at this
  cases he : evalScript checker flags script stack <;> rw [he] at this <;> cases this
  rfl

/--
This holds for every `active`, input, previous `scriptPubKey`, flag set and verifier.
If the revised spend predicate accepts the input, `verifyLegacySpend` accepts its projection, which is the same input.
Script-local.
-/
theorem example_soft_fork_projected {active : Bool} {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier}
    (h : exampleVerifyLegacySpend active ctx prevScriptPubKey flags verify = .accepted) :
    verifyLegacySpend (projection.message ctx) prevScriptPubKey flags verify = .accepted :=
  example_soft_fork_local h

end DogeLib.Proposals.ExampleVersionVerify
