module

public import DogeLib.Proposals.Framework.Script
public import DogeLib.Script.Proofs.Eval

/-!
# Proofs: `Proposals.Framework.Script`

## Agreement with the baseline

Let `embed` be an error map and `embedU` a map of unsupported reasons.
The framework definitions with `baselineStep embed embedU` equal the baseline definitions, with the errors and the unsupported reasons mapped:

- `evalLoopWith_baseline`: `evalLoopWith` equals `evalLoop`, for every checker, flag set, script and state.
- `evalScriptWith_baseline`: `evalScriptWith` equals `evalScript`, for every checker, flag set, script and stack.
- `verifyScriptWith_baseline`: `verifyScriptWith` equals `verifyScript`, for every checker, flag set, `scriptSig` and `scriptPubKey`.

With `embed = id` and `embedU = id`, `ofBaseline id id` changes only the name of the result type.

## Restriction

For all steps `step₁` and `step₀` such that `step₁` restricts `step₀`, and all error maps and maps of unsupported reasons:

- `evalLoopWith_restricts`: if the loop with `step₁` succeeds with the final state `t`, the loop with `step₀` from the same state succeeds with `t`.
- `evalScriptWith_restricts`: the same for one evaluation from a stack.
- `verifyScriptWith_restricts`: if `verifyScriptWith` with `step₁` accepts, `verifyScriptWith` with `step₀` accepts. The P2SH evaluation is included.
- `verifyScript_of_restricts`: if `step₁` restricts the baseline step with checker `c` and flags `flags`, and `verifyScriptWith` with `step₁` and `flags` accepts, then `verifyScript c flags` accepts.

## Congruence

Let `O` be a set of opcodes, and let two steps agree on every instruction whose opcode is outside `O`:

- `evalLoopWith_congr`: the two loops give the same result from every state whose cursor starts a part of the script with no instruction in `O`.
- `evalScriptWith_congr`: the same for one evaluation of a script with no instruction in `O`.
- `verifyScriptWith_congr`: the same for `VerifyScript`, when `scriptSig`, `scriptPubKey` and the P2SH redeem script have no instruction in `O`.

## Scripts after a prefix, and acceptance

- `readInstruction_append`, `opcodeFreeFrom_append`: the reader and the opcode test of a script after a prefix are those of the script alone, with every cursor moved by the length of the prefix.
- `VerifyOutcome.ofBaseline_eq_accepted`, `EvalOutcome.ofBaseline_eq_ok`: a mapped baseline result is a success exactly when the baseline result is.
- `verifyScriptWith_accepted_iff`: outside the P2SH template, `verifyScriptWith` accepts exactly when the flags are supported, both evaluations succeed and the final top item is true.
- `verifyScriptWith_flags_congr`: `verifyScriptWith` reads its flag argument through the unsupported bits and `SCRIPT_VERIFY_P2SH` alone.

These theorems are statements about the definitions. They do not say that a proposal is a soft fork of the network.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Script

variable {ε ε₀ ε₁ υ υ₀ υ₁ : Type}

/-! ## Unfolding the loop -/

/-- At the end of the script, the loop succeeds with the state when `vfExec` is empty, and gives `embed UNBALANCED_CONDITIONAL` otherwise. -/
theorem evalLoopWith_atEnd {embed : ScriptError → ε} {step : Step ε υ} {script : List UInt8} {s : ExecState}
    (hr : readInstruction script s.pc = .atEnd) :
    evalLoopWith embed step script s =
      if s.vfExec.isEmpty then .ok s else .rejected (embed .unbalancedConditional) := by
  rw [evalLoopWith]
  split <;> simp_all

/-- At a short push, the loop gives `embed BAD_OPCODE`. -/
theorem evalLoopWith_truncated {embed : ScriptError → ε} {step : Step ε υ} {script : List UInt8} {s : ExecState}
    {o : UInt8} {p : ShortPart} {c : Nat} (hr : readInstruction script s.pc = .truncated o p c) :
    evalLoopWith embed step script s = .rejected (embed .badOpcode) := by
  rw [evalLoopWith]
  split <;> simp_all

/--
Let `readInstruction` read the instruction `i` at the cursor.
Then the loop continues from the step's state with the cursor at `i.next`.
Or it stops with the step's error or unsupported result.
-/
theorem evalLoopWith_instruction {embed : ScriptError → ε} {step : Step ε υ} {script : List UInt8}
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
This holds for every error map `embed`, map of unsupported reasons `embedU`, checker, flag set, script and state `s`.
The loop with the baseline step equals `evalLoop` from `s`, with its error mapped by `embed` and its unsupported reason mapped by `embedU`.
-/
theorem evalLoopWith_baseline (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (checker : Option SignatureChecker) (flags : UInt32) (script : List UInt8) (s : ExecState) :
    evalLoopWith embed (baselineStep embed embedU checker flags) script s =
      .ofBaseline embed embedU (evalLoop checker flags script s) := by
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
This holds for every error map `embed`, map of unsupported reasons `embedU`, checker, flag set, script and stack.
One evaluation with the baseline step equals `evalScript`, with its error mapped by `embed` and its unsupported reason mapped by `embedU`.
-/
theorem evalScriptWith_baseline (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (checker : Option SignatureChecker) (flags : UInt32) (script : List UInt8) (stack : List (List UInt8)) :
    evalScriptWith embed embedU (baselineStep embed embedU checker flags) flags script stack =
      .ofBaseline embed embedU (evalScript checker flags script stack) := by
  unfold evalScriptWith evalScript
  split
  · rfl
  · split
    · rfl
    · exact evalLoopWith_baseline embed embedU checker flags script _

-- Each branch of the case split uses a different part of the simp set.
set_option linter.unusedSimpArgs false in
/--
This holds for every error map `embed`, map of unsupported reasons `embedU`, checker `c`, flag set `flags`, `scriptSig` and `scriptPubKey`.
`verifyScriptWith` with the baseline step for `c` and `flags` equals `verifyScript`, with its error mapped by `embed` and its unsupported reason mapped by `embedU`.
The P2SH evaluation is included.
-/
theorem verifyScriptWith_baseline (embed : ScriptError → ε) (embedU : Unsupported → υ) (c : SignatureChecker)
    (flags : UInt32) (scriptSig scriptPubKey : List UInt8) :
    verifyScriptWith embed embedU (baselineStep embed embedU (some c) flags) flags scriptSig scriptPubKey =
      .ofBaseline embed embedU (verifyScript c flags scriptSig scriptPubKey) := by
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
theorem evalLoopWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀} {step₁ : Step ε₁ υ₁}
    {step₀ : Step ε₀ υ₀} (hres : Restricts step₁ step₀) (script : List UInt8) (s t : ExecState)
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
Let `step₁` restrict `step₀`. This holds for all error maps and maps of unsupported reasons, every flag set, script and stack.
If one evaluation with `step₁` succeeds with the final state `t`, then the evaluation with `step₀` succeeds with `t`.
-/
theorem evalScriptWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀}
    {embedU₁ : Unsupported → υ₁} {embedU₀ : Unsupported → υ₀} {step₁ : Step ε₁ υ₁}
    {step₀ : Step ε₀ υ₀} (hres : Restricts step₁ step₀) (flags : UInt32) (script : List UInt8)
    (stack : List (List UInt8)) (t : ExecState) (hok : evalScriptWith embed₁ embedU₁ step₁ flags script stack = .ok t) :
    evalScriptWith embed₀ embedU₀ step₀ flags script stack = .ok t := by
  unfold evalScriptWith at hok ⊢
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · simp only [*, ↓reduceIte]
      exact evalLoopWith_restricts hres script _ t hok

/--
Let `step₁` restrict `step₀`. This holds for all error maps and maps of unsupported reasons, every flag set, `scriptSig` and `scriptPubKey`.
If `verifyScriptWith` with `step₁` accepts, then `verifyScriptWith` with `step₀` accepts.
The proof runs through each evaluation: `scriptSig`, `scriptPubKey` and the P2SH redeem script.
A successful evaluation with `step₁` is a successful evaluation with `step₀`, with the same final state.
So each later evaluation starts from the same stack.
-/
theorem verifyScriptWith_restricts {embed₁ : ScriptError → ε₁} {embed₀ : ScriptError → ε₀}
    {embedU₁ : Unsupported → υ₁} {embedU₀ : Unsupported → υ₀} {step₁ : Step ε₁ υ₁}
    {step₀ : Step ε₀ υ₀} (hres : Restricts step₁ step₀) (flags : UInt32) (scriptSig scriptPubKey : List UInt8)
    (hacc : verifyScriptWith embed₁ embedU₁ step₁ flags scriptSig scriptPubKey = .accepted) :
    verifyScriptWith embed₀ embedU₀ step₀ flags scriptSig scriptPubKey = .accepted := by
  unfold verifyScriptWith at hacc ⊢
  by_cases hf : unsupportedFlagBits flags = 0
  case neg => simp [hf] at hacc
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte] at hacc ⊢
  cases hs : evalScriptWith embed₁ embedU₁ step₁ flags scriptSig [] with
  | rejected e => simp [hs] at hacc
  | unsupported u => simp [hs] at hacc
  | ok s =>
    rw [hs] at hacc
    rw [evalScriptWith_restricts hres flags scriptSig [] s hs]
    simp only at hacc ⊢
    cases ht : evalScriptWith embed₁ embedU₁ step₁ flags scriptPubKey s.stack with
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
        cases hr : evalScriptWith embed₁ embedU₁ step₁ flags redeem rest.reverse with
        | ok u =>
          rw [hr] at hacc
          rw [evalScriptWith_restricts hres flags redeem rest.reverse u hr]
          simp only at hacc ⊢
          by_cases h4 : trueTop u.stack <;> simp [h4] at hacc ⊢
        | rejected e => simp [hr] at hacc
        | unsupported u => simp [hr] at hacc

/--
Let `step` restrict the baseline step for the checker `c` and the flag set `flags`.
This holds for all error maps `embed` and `embed₀`, and all maps of unsupported reasons `embedU` and `embedU₀`.
This holds for every `scriptSig` and `scriptPubKey`.
If `verifyScriptWith` with `step` and `flags` accepts, then `verifyScript c flags` accepts.
The theorem is Script-local.
-/
theorem verifyScript_of_restricts {embed : ScriptError → ε} {embedU : Unsupported → υ} (embed₀ : ScriptError → ε₀)
    (embedU₀ : Unsupported → υ₀) {step : Step ε υ} {c : SignatureChecker} {flags : UInt32}
    (hres : Restricts step (baselineStep embed₀ embedU₀ (some c) flags)) (scriptSig scriptPubKey : List UInt8)
    (hacc : verifyScriptWith embed embedU step flags scriptSig scriptPubKey = .accepted) :
    verifyScript c flags scriptSig scriptPubKey = .accepted := by
  have h := verifyScriptWith_restricts (embed₀ := embed₀) (embedU₀ := embedU₀) hres flags scriptSig scriptPubKey hacc
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
theorem evalLoopWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {step₁ step₂ : Step ε υ}
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
This holds for every error map, map of unsupported reasons, flag set and stack.
If `script` has no instruction in `O`, the two evaluations give the same result.
-/
theorem evalScriptWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {embedU : Unsupported → υ} {step₁ step₂ : Step ε υ}
    {script : List UInt8} (hstep : ∀ s i, O i.opcode = false → step₁ script s i = step₂ script s i)
    (flags : UInt32) (stack : List (List UInt8)) (hfree : opcodeFree O script = true) :
    evalScriptWith embed embedU step₁ flags script stack = evalScriptWith embed embedU step₂ flags script stack := by
  unfold evalScriptWith
  split
  · rfl
  · split
    · rfl
    · exact evalLoopWith_congr hstep _ hfree

/--
Let `O` be an opcode set, and let `step₁` and `step₂` agree on every script at every instruction with an opcode outside `O`.
This holds for every error map, map of unsupported reasons and flag set.
Let `scriptSig` and `scriptPubKey` have no instruction in `O`.
Let each redeem script that the P2SH evaluation can take also have no instruction in `O`.
Then the two `verifyScriptWith` calls give the same result.
The redeem-script hypothesis covers each top item of a final stack of `scriptSig` with `step₁`.
-/
theorem verifyScriptWith_congr {O : UInt8 → Bool} {embed : ScriptError → ε} {embedU : Unsupported → υ} {step₁ step₂ : Step ε υ}
    (hstep : ∀ script s i, O i.opcode = false → step₁ script s i = step₂ script s i) (flags : UInt32)
    {scriptSig scriptPubKey : List UInt8} (hsig : opcodeFree O scriptSig = true)
    (hpub : opcodeFree O scriptPubKey = true)
    (hredeem : ∀ s redeem rest, evalScriptWith embed embedU step₁ flags scriptSig [] = .ok s →
      s.stack.reverse = redeem :: rest → opcodeFree O redeem = true) :
    verifyScriptWith embed embedU step₁ flags scriptSig scriptPubKey =
      verifyScriptWith embed embedU step₂ flags scriptSig scriptPubKey := by
  unfold verifyScriptWith
  rw [← evalScriptWith_congr (hstep scriptSig) flags [] hsig]
  cases hs : evalScriptWith embed embedU step₁ flags scriptSig [] with
  | rejected e => rfl
  | unsupported u => rfl
  | ok s =>
    simp only
    rw [← evalScriptWith_congr (hstep scriptPubKey) flags s.stack hpub]
    rcases hsr : s.stack.reverse with _ | ⟨redeem, rest⟩
    · rfl
    · simp only [evalScriptWith_congr (hstep redeem) flags rest.reverse (hredeem s redeem rest hs hsr)]

/-! ## Scripts after a prefix -/

/-- At the end of the script, the opcode test gives `true`. -/
theorem opcodeFreeFrom_atEnd {O : UInt8 → Bool} {script : List UInt8} {pc : Nat}
    (hr : readInstruction script pc = .atEnd) : opcodeFreeFrom O script pc = true := by
  rw [opcodeFreeFrom]
  split <;> simp_all

/-- At a short push, the opcode test gives `true`. -/
theorem opcodeFreeFrom_truncated {O : UInt8 → Bool} {script : List UInt8} {pc : Nat} {o : UInt8}
    {p : ShortPart} {c : Nat} (hr : readInstruction script pc = .truncated o p c) :
    opcodeFreeFrom O script pc = true := by
  rw [opcodeFreeFrom]
  split <;> simp_all

/-- For every prefix `p`, script `S` and cursor `k`: the reader at `p.length + k` of `p ++ S` reads what it reads at `k` of `S`. Every cursor moves by `p.length`. -/
theorem readInstruction_append (p S : List UInt8) (k : Nat) :
    readInstruction (p ++ S) (p.length + k) =
      match readInstruction S k with
      | .instruction i => .instruction { i with next := p.length + i.next }
      | .atEnd => .atEnd
      | .truncated o part c => .truncated o part (p.length + c) := by
  have h : (p ++ S).drop (p.length + k) = S.drop k := by
    rw [← List.drop_drop, List.drop_left]
  simp only [readInstruction, h]
  split <;> simp <;> omega

/-- For every opcode set `O`, prefix `p`, script `S` and cursor `k`: the test of `p ++ S` from `p.length + k` is the test of `S` from `k`. -/
theorem opcodeFreeFrom_append (O : UInt8 → Bool) (p S : List UInt8) (k : Nat) :
    opcodeFreeFrom O (p ++ S) (p.length + k) = opcodeFreeFrom O S k := by
  induction k using opcodeFreeFrom.induct S with
  | case1 k hr =>
    rw [opcodeFreeFrom_atEnd hr]
    apply opcodeFreeFrom_atEnd
    rw [readInstruction_append, hr]
  | case2 k o part c hr =>
    rw [opcodeFreeFrom_truncated hr]
    apply opcodeFreeFrom_truncated (o := o) (p := part) (c := p.length + c)
    rw [readInstruction_append, hr]
  | case3 k i hr _ ih =>
    rw [opcodeFreeFrom_instruction hr, ← ih]
    have h' := readInstruction_append p S k
    rw [hr] at h'
    rw [opcodeFreeFrom_instruction h']

/-! ## Acceptance -/

/-- For every error map, map of unsupported reasons and baseline result: the mapped result is accepted exactly when the baseline result is. -/
theorem VerifyOutcome.ofBaseline_eq_accepted {ε υ : Type} {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {r : VerifyResult} :
    VerifyOutcome.ofBaseline embed embedU r = .accepted ↔ r = .accepted := by
  cases r <;> simp [VerifyOutcome.ofBaseline]

/-- For every error map, map of unsupported reasons and success state: a mapped baseline evaluation succeeds with `t` exactly when the baseline evaluation does. -/
theorem EvalOutcome.ofBaseline_eq_ok {ε υ : Type} {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {r : EvalResult} {t : ExecState} :
    EvalOutcome.ofBaseline embed embedU r = .ok t ↔ r = .ok t := by
  cases r <;> simp [EvalOutcome.ofBaseline]

/--
Let `scriptPubKey` lie outside the P2SH template. This holds for every step, error map, map of unsupported reasons, flag set and `scriptSig`.
`verifyScriptWith` accepts exactly when the flags are supported, both evaluations succeed, and the final top item is true.
-/
theorem verifyScriptWith_accepted_iff {ε υ : Type} {embed : ScriptError → ε} {embedU : Unsupported → υ}
    {step : Step ε υ} {flags : UInt32}
    {scriptSig scriptPubKey : List UInt8} (hp : isPayToScriptHash scriptPubKey = false) :
    verifyScriptWith embed embedU step flags scriptSig scriptPubKey = .accepted ↔
      unsupportedFlagBits flags = 0 ∧ ∃ s t, evalScriptWith embed embedU step flags scriptSig [] = .ok s ∧
        evalScriptWith embed embedU step flags scriptPubKey s.stack = .ok t ∧ trueTop t.stack = true := by
  unfold verifyScriptWith
  by_cases hf : unsupportedFlagBits flags = 0
  case neg => simp [hf]
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
  cases hs : evalScriptWith embed embedU step flags scriptSig [] with
  | rejected e => simp
  | unsupported u => simp
  | ok s =>
    simp only
    cases ht : evalScriptWith embed embedU step flags scriptPubKey s.stack with
    | rejected e => simp [ht]
    | unsupported u => simp [ht]
    | ok t =>
      by_cases h1 : trueTop t.stack = true
      · simp [h1, hp, ht]
      · simp [h1, ht]

/--
`verifyScriptWith` reads its flag argument through `unsupportedFlagBits` and `SCRIPT_VERIFY_P2SH` alone.
For two flag sets with the same unsupported bits and the same `SCRIPT_VERIFY_P2SH`, it gives one result, for every step, error map, map of unsupported reasons, `scriptSig` and `scriptPubKey`.
The step keeps its own flags.
-/
theorem verifyScriptWith_flags_congr {embed : ScriptError → ε} {embedU : Unsupported → υ} (step : Step ε υ)
    {f g : UInt32} (hu : unsupportedFlagBits f = unsupportedFlagBits g)
    (hp : hasFlag f ScriptFlags.p2sh = hasFlag g ScriptFlags.p2sh) (scriptSig scriptPubKey : List UInt8) :
    verifyScriptWith embed embedU step f scriptSig scriptPubKey =
      verifyScriptWith embed embedU step g scriptSig scriptPubKey := by
  simp only [verifyScriptWith, evalScriptWith, hu, hp]

end DogeLib.Proposals.Framework
