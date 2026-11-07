module

public import DogeLib.Proposals.Framework.Script
public import DogeLib.Script.Proofs.Eval

/-!
# Proofs: `Proposals.Framework.Script`

## Agreement with the baseline

For every error map `embed`, the framework definitions with `baselineStep embed` equal the baseline definitions, with the errors mapped by `embed`:

- `evalLoopWith_baseline`: `evalLoopWith` equals `evalLoop`, for every checker, flag set, script and state.
- `evalScriptWith_baseline`: `evalScriptWith` equals `evalScript`, for every checker, flag set, script and stack.
- `verifyScriptWith_baseline`: `verifyScriptWith` equals `verifyScript`, for every checker, flag set, `scriptSig` and `scriptPubKey`.

With `embed = id`, `ofBaseline id` changes only the name of the result type.

## Restriction

For all steps `step₁` and `step₀` such that `step₁` restricts `step₀`, and all error maps:

- `evalLoopWith_restricts`: if the loop with `step₁` succeeds with the final state `t`, the loop with `step₀` from the same state succeeds with `t`.
- `evalScriptWith_restricts`: the same for one evaluation from a stack.
- `verifyScriptWith_restricts`: if `verifyScriptWith` with `step₁` accepts, `verifyScriptWith` with `step₀` accepts. The P2SH evaluation is included.
- `verifyScript_of_restricts`: if `step₁` restricts the baseline step with checker `c` and flags `flags`, and `verifyScriptWith` with `step₁` and `flags` accepts, then `verifyScript c flags` accepts.

## Congruence

Let `O` be a set of opcodes, and let two steps agree on every instruction whose opcode is outside `O`:

- `evalLoopWith_congr`: the two loops give the same result from every state whose cursor starts a part of the script with no instruction in `O`.
- `evalScriptWith_congr`: the same for one evaluation of a script with no instruction in `O`.
- `verifyScriptWith_congr`: the same for `VerifyScript`, when `scriptSig`, `scriptPubKey` and the P2SH redeem script have no instruction in `O`.

These theorems are statements about the definitions. They do not say that a proposal is a soft fork of the network.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Script

variable {ε ε₀ ε₁ : Type}

/-! ## Unfolding the loop -/

/-- At the end of the script, the loop succeeds with the state when `vfExec` is empty, and gives `embed UNBALANCED_CONDITIONAL` otherwise. -/
theorem evalLoopWith_atEnd {embed : ScriptError → ε} {step : Step ε} {script : List UInt8} {s : ExecState}
    (hr : readInstruction script s.pc = .atEnd) :
    evalLoopWith embed step script s =
      if s.vfExec.isEmpty then .ok s else .rejected (embed .unbalancedConditional) := by
  rw [evalLoopWith]
  split <;> simp_all

/-- At a short push, the loop gives `embed BAD_OPCODE`. -/
theorem evalLoopWith_truncated {embed : ScriptError → ε} {step : Step ε} {script : List UInt8} {s : ExecState}
    {o : UInt8} {p : ShortPart} {c : Nat} (hr : readInstruction script s.pc = .truncated o p c) :
    evalLoopWith embed step script s = .rejected (embed .badOpcode) := by
  rw [evalLoopWith]
  split <;> simp_all

/--
Let `readInstruction` read the instruction `i` at the cursor.
Then the loop continues from the step's state with the cursor at `i.next`.
Or it stops with the step's error or unsupported result.
-/
theorem evalLoopWith_instruction {embed : ScriptError → ε} {step : Step ε} {script : List UInt8}
    {s : ExecState} {i : Instruction} (hr : readInstruction script s.pc = .instruction i) :
    evalLoopWith embed step script s =
      match step script s i with
      | .next t => evalLoopWith embed step script { t with pc := i.next }
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u := by
  rw [evalLoopWith]
  split <;> (try simp_all) <;> rfl

/-! ## Agreement with the baseline -/

/--
This holds for every error map `embed`, checker, flag set, script and state `s`.
The loop with the baseline step equals `evalLoop` from `s`, with its error mapped by `embed`.
-/
theorem evalLoopWith_baseline (embed : ScriptError → ε) (checker : Option SignatureChecker) (flags : UInt32)
    (script : List UInt8) (s : ExecState) :
    evalLoopWith embed (baselineStep embed checker flags) script s =
      .ofBaseline embed (evalLoop checker flags script s) := by
  induction s using evalLoop.induct (checker := checker) (flags := flags) (script := script) with
  | case1 s hr _ | case2 s hr _ =>
    rw [evalLoopWith_atEnd hr, evalLoop_atEnd (readInstruction_atEnd_iff.mp hr)]
    by_cases hv : s.vfExec = [] <;> simp [hv, EvalOutcome.ofBaseline]
  | case3 s o p c hr =>
    rw [evalLoopWith_truncated hr, evalLoop_truncated hr]
    rfl
  | case4 s i hr _ t ht ih =>
    rw [evalLoopWith_instruction hr, evalLoop_instruction hr]
    simp only [baselineStep, ht, StepOutcome.ofBaseline]
    exact ih
  | case5 s i hr _ e he =>
    rw [evalLoopWith_instruction hr, evalLoop_instruction hr]
    simp only [baselineStep, he, StepOutcome.ofBaseline, EvalOutcome.ofBaseline]
  | case6 s i hr _ u hu =>
    rw [evalLoopWith_instruction hr, evalLoop_instruction hr]
    simp only [baselineStep, hu, StepOutcome.ofBaseline, EvalOutcome.ofBaseline]

/--
This holds for every error map `embed`, checker, flag set, script and stack.
One evaluation with the baseline step equals `evalScript`, with its error mapped by `embed`.
-/
theorem evalScriptWith_baseline (embed : ScriptError → ε) (checker : Option SignatureChecker) (flags : UInt32)
    (script : List UInt8) (stack : List (List UInt8)) :
    evalScriptWith embed (baselineStep embed checker flags) flags script stack =
      .ofBaseline embed (evalScript checker flags script stack) := by
  unfold evalScriptWith evalScript
  split
  · rfl
  · split
    · rfl
    · exact evalLoopWith_baseline embed checker flags script _

-- Each branch of the case split uses a different part of the simp set.
set_option linter.unusedSimpArgs false in
/--
This holds for every error map `embed`, checker `c`, flag set `flags`, `scriptSig` and `scriptPubKey`.
`verifyScriptWith` with the baseline step for `c` and `flags` equals `verifyScript`, with its error mapped by `embed`.
The P2SH evaluation is included.
-/
theorem verifyScriptWith_baseline (embed : ScriptError → ε) (c : SignatureChecker) (flags : UInt32)
    (scriptSig scriptPubKey : List UInt8) :
    verifyScriptWith embed (baselineStep embed (some c) flags) flags scriptSig scriptPubKey =
      .ofBaseline embed (verifyScript c flags scriptSig scriptPubKey) := by
  unfold verifyScriptWith verifyScript
  simp only [evalScriptWith_baseline]
  by_cases hf : unsupportedFlagBits flags = 0
  case neg => simp only [hf, ne_eq, not_false_eq_true, ↓reduceIte, VerifyOutcome.ofBaseline]
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases evalScript (some c) flags scriptSig [] with s | e | u <;>
    simp only [EvalOutcome.ofBaseline, VerifyOutcome.ofBaseline]
  rcases evalScript (some c) flags scriptPubKey s.stack with t | e | u <;>
    simp only [EvalOutcome.ofBaseline, VerifyOutcome.ofBaseline]
  by_cases h1 : trueTop t.stack <;> simp only [h1, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, VerifyOutcome.ofBaseline]
  by_cases h2 : (hasFlag flags ScriptFlags.p2sh && isPayToScriptHash scriptPubKey) = true <;>
    simp only [h2, Bool.false_eq_true, ↓reduceIte, VerifyOutcome.ofBaseline]
  by_cases h3 : isPushOnly scriptSig <;> simp only [h3, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, VerifyOutcome.ofBaseline]
  rcases s.stack.reverse with _ | ⟨redeem, rest⟩
  · rfl
  · simp only [evalScriptWith_baseline]
    rcases evalScript (some c) flags redeem rest.reverse with u | e | u <;>
      simp only [EvalOutcome.ofBaseline, finishEvalWith, finishEval, VerifyOutcome.ofBaseline]
    by_cases h4 : trueTop u.stack <;> simp [h4, VerifyOutcome.ofBaseline]

/-! ## Restriction -/

/--
Let `step₁` restrict `step₀`. This holds for all error maps, every script and every state `s`.
If the loop with `step₁` from `s` succeeds with the final state `t`, then the loop with `step₀` from `s` succeeds with `t`.
-/
theorem evalLoopWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀} {step₁ : Step ε₁}
    {step₀ : Step ε₀} (hres : Restricts step₁ step₀) (script : List UInt8) (s t : ExecState)
    (hok : evalLoopWith embed₁ step₁ script s = .ok t) : evalLoopWith embed₀ step₀ script s = .ok t := by
  induction s using evalLoopWith.induct (step := step₁) (script := script) with
  | case1 s hr he =>
    rw [evalLoopWith_atEnd hr] at hok
    rw [evalLoopWith_atEnd hr]
    simp only [he, ↓reduceIte, EvalOutcome.ok.injEq] at hok ⊢
    exact hok
  | case2 s hr he =>
    rw [evalLoopWith_atEnd hr] at hok
    simp [he] at hok
  | case3 s o p c hr =>
    rw [evalLoopWith_truncated hr] at hok
    cases hok
  | case4 s i hr _ u hu ih =>
    rw [evalLoopWith_instruction hr, hu] at hok
    rw [evalLoopWith_instruction hr, hres script s i u hu]
    exact ih hok
  | case5 s i hr _ e he =>
    rw [evalLoopWith_instruction hr, he] at hok
    cases hok
  | case6 s i hr _ u hu =>
    rw [evalLoopWith_instruction hr, hu] at hok
    cases hok

/--
Let `step₁` restrict `step₀`. This holds for all error maps, every flag set, script and stack.
If one evaluation with `step₁` succeeds with the final state `t`, then the evaluation with `step₀` succeeds with `t`.
-/
theorem evalScriptWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀} {step₁ : Step ε₁}
    {step₀ : Step ε₀} (hres : Restricts step₁ step₀) (flags : UInt32) (script : List UInt8)
    (stack : List (List UInt8)) (t : ExecState) (hok : evalScriptWith embed₁ step₁ flags script stack = .ok t) :
    evalScriptWith embed₀ step₀ flags script stack = .ok t := by
  unfold evalScriptWith at hok ⊢
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · simp only [*, ↓reduceIte]
      exact evalLoopWith_restricts hres script _ t hok

/--
Let `step₁` restrict `step₀`. This holds for all error maps, every flag set, `scriptSig` and `scriptPubKey`.
If `verifyScriptWith` with `step₁` accepts, then `verifyScriptWith` with `step₀` accepts.
The proof runs through each evaluation: `scriptSig`, `scriptPubKey` and the P2SH redeem script.
A successful evaluation with `step₁` is a successful evaluation with `step₀`, with the same final state.
So each later evaluation starts from the same stack.
-/
theorem verifyScriptWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀} {step₁ : Step ε₁}
    {step₀ : Step ε₀} (hres : Restricts step₁ step₀) (flags : UInt32) (scriptSig scriptPubKey : List UInt8)
    (hacc : verifyScriptWith embed₁ step₁ flags scriptSig scriptPubKey = .accepted) :
    verifyScriptWith embed₀ step₀ flags scriptSig scriptPubKey = .accepted := by
  unfold verifyScriptWith at hacc ⊢
  by_cases hf : unsupportedFlagBits flags = 0
  case neg => simp [hf] at hacc
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte] at hacc ⊢
  cases hs : evalScriptWith embed₁ step₁ flags scriptSig [] with
  | rejected e => simp [hs] at hacc
  | unsupported u => simp [hs] at hacc
  | ok s =>
    rw [hs] at hacc
    rw [evalScriptWith_restricts hres flags scriptSig [] s hs]
    simp only at hacc ⊢
    cases ht : evalScriptWith embed₁ step₁ flags scriptPubKey s.stack with
    | rejected e => simp [ht] at hacc
    | unsupported u => simp [ht] at hacc
    | ok t =>
      rw [ht] at hacc
      rw [evalScriptWith_restricts hres flags scriptPubKey s.stack t ht]
      simp only at hacc ⊢
      by_cases h1 : trueTop t.stack
      case neg => simp [h1] at hacc
      by_cases h2 : (hasFlag flags ScriptFlags.p2sh && isPayToScriptHash scriptPubKey) = true
      case neg => simp [h1, h2]
      by_cases h3 : isPushOnly scriptSig
      case neg => simp [h1, h2, h3] at hacc
      simp only [h1, h2, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hacc ⊢
      rcases hsr : s.stack.reverse with _ | ⟨redeem, rest⟩
      · simp [hsr] at hacc
      · simp only [hsr] at hacc ⊢
        unfold finishEvalWith at hacc ⊢
        cases hr : evalScriptWith embed₁ step₁ flags redeem rest.reverse with
        | ok u =>
          rw [hr] at hacc
          rw [evalScriptWith_restricts hres flags redeem rest.reverse u hr]
          simp only at hacc ⊢
          by_cases h4 : trueTop u.stack <;> simp [h4] at hacc ⊢
        | rejected e => simp [hr] at hacc
        | unsupported u => simp [hr] at hacc

/--
Let `step` restrict the baseline step for the checker `c` and the flag set `flags`, with any error maps `embed` and `embed₀`.
This holds for every `scriptSig` and `scriptPubKey`.
If `verifyScriptWith` with `step` and `flags` accepts, then `verifyScript c flags` accepts.
The theorem is Script-local.
-/
theorem verifyScript_of_restricts {embed : ScriptError → ε} (embed₀ : ScriptError → ε₀) {step : Step ε}
    {c : SignatureChecker} {flags : UInt32} (hres : Restricts step (baselineStep embed₀ (some c) flags))
    (scriptSig scriptPubKey : List UInt8)
    (hacc : verifyScriptWith embed step flags scriptSig scriptPubKey = .accepted) :
    verifyScript c flags scriptSig scriptPubKey = .accepted := by
  have h := verifyScriptWith_restricts (embed₀ := embed₀) hres flags scriptSig scriptPubKey hacc
  rw [verifyScriptWith_baseline] at h
  cases hv : verifyScript c flags scriptSig scriptPubKey <;> simp_all [VerifyOutcome.ofBaseline]

/-! ## Congruence -/

/-- At the instruction `i` that `readInstruction` reads at `pc`, the opcode test continues at `i.next` when the opcode of `i` is outside `O`. -/
theorem opcodeFreeFrom_instruction {O : UInt8 → Bool} {script : List UInt8} {pc : Nat} {i : Instruction}
    (hr : readInstruction script pc = .instruction i) :
    opcodeFreeFrom O script pc = (!O i.opcode && opcodeFreeFrom O script i.next) := by
  rw [opcodeFreeFrom]
  split <;> (try simp_all) <;> rfl

/--
Let `O` be an opcode set, and let `step₁` and `step₂` agree on `script` at every state and every instruction with an opcode outside `O`.
This holds for every error map and every state `s`.
Let no instruction from `s.pc` to the end of the script have an opcode in `O`.
Then the two loops give the same result from `s`.
-/
theorem evalLoopWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {step₁ step₂ : Step ε}
    {script : List UInt8} (hstep : ∀ s i, O i.opcode = false → step₁ script s i = step₂ script s i)
    (s : ExecState) (hfree : opcodeFreeFrom O script s.pc = true) :
    evalLoopWith embed step₁ script s = evalLoopWith embed step₂ script s := by
  induction s using evalLoopWith.induct (step := step₁) (script := script) with
  | case1 s hr _ | case2 s hr _ => rw [evalLoopWith_atEnd hr, evalLoopWith_atEnd hr]
  | case3 s o p c hr => rw [evalLoopWith_truncated hr, evalLoopWith_truncated hr]
  | case4 s i hr _ u hu ih =>
    rw [opcodeFreeFrom_instruction hr, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    rw [evalLoopWith_instruction hr, evalLoopWith_instruction hr, ← hstep s i hfree.1, hu]
    exact ih hfree.2
  | case5 s i hr _ e he =>
    rw [opcodeFreeFrom_instruction hr, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    rw [evalLoopWith_instruction hr, evalLoopWith_instruction hr, ← hstep s i hfree.1, he]
  | case6 s i hr _ u hu =>
    rw [opcodeFreeFrom_instruction hr, Bool.and_eq_true, Bool.not_eq_true'] at hfree
    rw [evalLoopWith_instruction hr, evalLoopWith_instruction hr, ← hstep s i hfree.1, hu]

/--
Let `O` be an opcode set, and let `step₁` and `step₂` agree on `script` at every instruction with an opcode outside `O`.
This holds for every error map, flag set and stack.
If `script` has no instruction in `O`, the two evaluations give the same result.
-/
theorem evalScriptWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {step₁ step₂ : Step ε}
    {script : List UInt8} (hstep : ∀ s i, O i.opcode = false → step₁ script s i = step₂ script s i)
    (flags : UInt32) (stack : List (List UInt8)) (hfree : opcodeFree O script = true) :
    evalScriptWith embed step₁ flags script stack = evalScriptWith embed step₂ flags script stack := by
  unfold evalScriptWith
  split
  · rfl
  · split
    · rfl
    · exact evalLoopWith_congr hstep _ hfree

/--
Let `O` be an opcode set, and let `step₁` and `step₂` agree on every script at every instruction with an opcode outside `O`.
This holds for every error map and flag set.
Let `scriptSig` and `scriptPubKey` have no instruction in `O`.
Let each redeem script that the P2SH evaluation can take also have no instruction in `O`.
Then the two `verifyScriptWith` calls give the same result.
The redeem-script hypothesis covers each top item of a final stack of `scriptSig` with `step₁`.
-/
theorem verifyScriptWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {step₁ step₂ : Step ε}
    (hstep : ∀ script s i, O i.opcode = false → step₁ script s i = step₂ script s i) (flags : UInt32)
    {scriptSig scriptPubKey : List UInt8} (hsig : opcodeFree O scriptSig = true)
    (hpub : opcodeFree O scriptPubKey = true)
    (hredeem : ∀ s redeem rest, evalScriptWith embed step₁ flags scriptSig [] = .ok s →
      s.stack.reverse = redeem :: rest → opcodeFree O redeem = true) :
    verifyScriptWith embed step₁ flags scriptSig scriptPubKey =
      verifyScriptWith embed step₂ flags scriptSig scriptPubKey := by
  unfold verifyScriptWith
  rw [← evalScriptWith_congr (hstep scriptSig) flags [] hsig]
  cases hs : evalScriptWith embed step₁ flags scriptSig [] with
  | rejected e => rfl
  | unsupported u => rfl
  | ok s =>
    simp only
    rw [← evalScriptWith_congr (hstep scriptPubKey) flags s.stack hpub]
    rcases hsr : s.stack.reverse with _ | ⟨redeem, rest⟩
    · rfl
    · simp only [evalScriptWith_congr (hstep redeem) flags rest.reverse (hredeem s redeem rest hs hsr)]

end DogeLib.Proposals.Framework
