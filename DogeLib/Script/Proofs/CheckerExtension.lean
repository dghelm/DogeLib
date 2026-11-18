module

public import DogeLib.Script.Proofs.Verify

/-!
# Proofs: checker extension

A congruence of `evalScript` and `verifyScript` over the signature checker.

`d.Extends c` says that the checker `d` gives the answer of the checker `c` on every request that `c` answers.
`d` can also answer a request on which `c` is unavailable.

- `evalScript_checker_extends`, `verifyScript_checker_extends`: if `d` extends `c`, then the call with `c` is unsupported, or the call with `d` gives the same result.
- `verifyScript_checker_congr`: two checkers that extend one checker `c` give the same result, when the call with `c` is decided.
- `EvalResult.Decided`, `VerifyResult.Decided`: a result is decided when it is not unsupported.
  `verifyScript_decided`: `verifyScript` is decided when each of its evaluations is decided.
- `checkSigStep_checker_extends`, `checkMultisigStep_checker_extends`, `checkLockTimeStep_checker_extends`, `checkSequenceStep_checker_extends`, `execOpcode_checker_extends`, `evalInstruction_checker_extends`: the same statement for each step.

An unavailable answer gives an unsupported result at the opcode that asked (`DogeLib.Script.Eval`).
So a call with `c` that is not unsupported asked `c` only the requests that `c` answers.
The theorems use that fact in place of a list of the requests of a run.

These theorems are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/--
The checker `d` extends the checker `c`: on every request that `c` answers, `d` gives the same answer.
The three fields are the three kinds of request.
-/
structure SignatureChecker.Extends (d c : SignatureChecker) : Prop where
  /-- Every answered signature check of `c` has the same answer in `d`. -/
  checkSig : ∀ sig key code b, c.checkSig sig key code = some b → d.checkSig sig key code = some b
  /-- Every answered lock-time check of `c` has the same answer in `d`. -/
  checkLockTime : ∀ n b, c.checkLockTime n = some b → d.checkLockTime n = some b
  /-- Every answered sequence check of `c` has the same answer in `d`. -/
  checkSequence : ∀ n b, c.checkSequence n = some b → d.checkSequence n = some b

/-- Every checker extends itself. -/
theorem SignatureChecker.Extends.refl (c : SignatureChecker) : c.Extends c :=
  ⟨fun _ _ _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

/-- The result of one `EvalScript` call is decided: it is not unsupported. -/
def EvalResult.Decided : EvalResult → Prop
  | .unsupported _ => False
  | _ => True

/-- The result of one `VerifyScript` call is decided: it is not unsupported. -/
def VerifyResult.Decided : VerifyResult → Prop
  | .unsupported _ => False
  | _ => True

/-- A decided result of `EvalScript` is not unsupported. -/
theorem EvalResult.Decided.ne_unsupported {r : EvalResult} (h : r.Decided) (u : Unsupported) : r ≠ .unsupported u := by
  rintro rfl; exact h

/-- A decided result of `VerifyScript` is not unsupported. -/
theorem VerifyResult.Decided.ne_unsupported {r : VerifyResult} (h : r.Decided) (u : Unsupported) :
    r ≠ .unsupported u := by
  rintro rfl; exact h

variable {c d : SignatureChecker} {script : List UInt8} {flags : UInt32}

/-! ## The steps that read the checker -/

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every script, flag set, state and opcode:
`checkSigStep` with `c` is unsupported, or `checkSigStep` with `d` gives the same result.
-/
theorem checkSigStep_checker_extends (h : d.Extends c) (s : ExecState) (op : UInt8) :
    (∃ u, checkSigStep c script flags s op = .unsupported u) ∨
      checkSigStep d script flags s op = checkSigStep c script flags s op := by
  unfold checkSigStep
  split
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · rename_i key sig rest _ _ _ _ _
        cases hc : c.checkSig sig key (effectiveScriptCode script s.beginCodeHash [sig]) with
        | none => exact .inl ⟨_, rfl⟩
        | some b => rw [h.checkSig _ _ _ _ hc]; exact .inr rfl
  · exact .inr rfl

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every pair of one signature and one key:
`multisigCheck` with `c` gives an unsupported error, or `multisigCheck` with `d` gives the same result.
-/
theorem multisigCheck_checker_extends (h : d.Extends c) (code : List UInt8) (op : UInt8) (sig key : List UInt8) :
    (∃ u, multisigCheck c flags code op sig key = .error (.unsupported u)) ∨
      multisigCheck d flags code op sig key = multisigCheck c flags code op sig key := by
  unfold multisigCheck
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · cases hc : c.checkSig sig key code with
      | none => exact .inl ⟨_, rfl⟩
      | some b => rw [h.checkSig _ _ _ _ hc]; exact .inr rfl

/--
Take check functions `check₁` and `check₂` of the matching loop of `OP_CHECKMULTISIG`.
Assume that on every pair, `check₁` gives an unsupported error or `check₂` gives the result of `check₁`.
Then on all signatures and keys, the loop with `check₁` gives an unsupported error, or the loop with `check₂` gives the same result.
-/
theorem multisigLoop_extends {α β : Type} {check₁ check₂ : α → β → Except StepResult Bool}
    (h : ∀ sig key, (∃ u, check₁ sig key = .error (.unsupported u)) ∨ check₂ sig key = check₁ sig key) :
    ∀ (sigs : List α) (keys : List β),
      (∃ u, multisigLoop check₁ sigs keys = .error (.unsupported u)) ∨
        multisigLoop check₂ sigs keys = multisigLoop check₁ sigs keys
  | [], _ => .inr (by simp [multisigLoop])
  | _ :: _, [] => .inr rfl
  | sig :: sigs, key :: keys => by
    rcases h sig key with ⟨u, hu⟩ | he
    · exact .inl ⟨u, by simp [multisigLoop, hu]⟩
    · simp only [multisigLoop, he]
      cases check₁ sig key with
      | error e => exact .inr rfl
      | ok ok =>
        cases ok
        · simp only [Bool.false_eq_true, ite_false]
          split
          · exact .inr rfl
          · exact multisigLoop_extends h _ keys
        · simp only [ite_true]
          split
          · exact .inr rfl
          · exact multisigLoop_extends h _ keys

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every script, flag set, state and opcode:
`checkMultisigStep` with `c` is unsupported, or `checkMultisigStep` with `d` gives the same result.
-/
theorem checkMultisigStep_checker_extends (h : d.Extends c) (s : ExecState) (op : UInt8) :
    (∃ u, checkMultisigStep c script flags s op = .unsupported u) ∨
      checkMultisigStep d script flags s op = checkMultisigStep c script flags s op := by
  unfold checkMultisigStep
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · dsimp only
      iterate 8 (split; exact .inr rfl)
      rename_i _ _ keysRest _ _ nv _ _ _ _ _ _ sigsRest _ _ mv _ _ _ _ _ _ _
      rcases multisigLoop_extends (fun sig key => multisigCheck_checker_extends (flags := flags) h
          (effectiveScriptCode script s.beginCodeHash (List.take (ScriptNum.getint mv).toNat sigsRest)) op sig key)
          (List.take (ScriptNum.getint mv).toNat sigsRest) (List.take (ScriptNum.getint nv).toNat keysRest) with
        ⟨u, hu⟩ | he
      · exact .inl ⟨u, by rw [hu]⟩
      · rw [he]; exact .inr rfl

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every state:
`checkLockTimeStep` with `c` is unsupported, or `checkLockTimeStep` with `d` gives the same result.
-/
theorem checkLockTimeStep_checker_extends (h : d.Extends c) (s : ExecState) :
    (∃ u, checkLockTimeStep c s = .unsupported u) ∨ checkLockTimeStep d s = checkLockTimeStep c s := by
  unfold checkLockTimeStep
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · rename_i n _ _
        cases hc : c.checkLockTime n with
        | none => exact .inl ⟨_, rfl⟩
        | some b => rw [h.checkLockTime _ _ hc]; exact .inr rfl

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every state:
`checkSequenceStep` with `c` is unsupported, or `checkSequenceStep` with `d` gives the same result.
-/
theorem checkSequenceStep_checker_extends (h : d.Extends c) (s : ExecState) :
    (∃ u, checkSequenceStep c s = .unsupported u) ∨ checkSequenceStep d s = checkSequenceStep c s := by
  unfold checkSequenceStep
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · split
        · exact .inr rfl
        · rename_i n _ _ _
          cases hc : c.checkSequence n with
          | none => exact .inl ⟨_, rfl⟩
          | some b => rw [h.checkSequence _ _ hc]; exact .inr rfl

/-! ## One instruction -/

/-- A property holds for every byte when it holds for each value below 256, which `decide` can check. -/
theorem forall_byte_of_forall_lt (P : UInt8 → Prop) (h : ∀ n, n < 256 → P n.toUInt8) (b : UInt8) : P b := by
  simpa using h b.toNat b.toNat_lt

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every script, flag set, branch flag, state, opcode, pushed bytes and next cursor:
`execOpcode` with `c` is unsupported, or `execOpcode` with `d` gives the same result.
-/
theorem execOpcode_checker_extends (h : d.Extends c) (fExec : Bool) (s : ExecState) (op : UInt8)
    (pushed : List UInt8) (next : Nat) :
    (∃ u, execOpcode (some c) script flags fExec s op pushed next = .unsupported u) ∨
      execOpcode (some d) script flags fExec s op pushed next =
        execOpcode (some c) script flags fExec s op pushed next := by
  cases hr : readsChecker op
  · exact .inr (execOpcode_checker_congr hr)
  · have hop : op ∈ [0xac, 0xad, 0xae, 0xaf, 0xb1, 0xb2] :=
      forall_byte_of_forall_lt (fun op => readsChecker op = true → op ∈ [0xac, 0xad, 0xae, 0xaf, 0xb1, 0xb2])
        (by decide +kernel) op hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [execOpcode_checkSig (.inl rfl), execOpcode_checkSig (.inl rfl)]
      exact checkSigStep_checker_extends h s _
    · rw [execOpcode_checkSig (.inr rfl), execOpcode_checkSig (.inr rfl)]
      exact checkSigStep_checker_extends h s _
    · rw [execOpcode_checkMultisig (.inl rfl), execOpcode_checkMultisig (.inl rfl)]
      exact checkMultisigStep_checker_extends h s _
    · rw [execOpcode_checkMultisig (.inr rfl), execOpcode_checkMultisig (.inr rfl)]
      exact checkMultisigStep_checker_extends h s _
    · have e : ∀ x : SignatureChecker, execOpcode (some x) script flags fExec s 0xb1 pushed next =
          if hasFlag flags ScriptFlags.checkLockTimeVerify then checkLockTimeStep x s else .next s := fun _ => rfl
      rw [e, e]
      split
      · exact checkLockTimeStep_checker_extends h s
      · exact .inr rfl
    · have e : ∀ x : SignatureChecker, execOpcode (some x) script flags fExec s 0xb2 pushed next =
          if hasFlag flags ScriptFlags.checkSequenceVerify then checkSequenceStep x s else .next s := fun _ => rfl
      rw [e, e]
      split
      · exact checkSequenceStep_checker_extends h s
      · exact .inr rfl

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every script, flag set, state and instruction:
`evalInstruction` with `c` is unsupported, or `evalInstruction` with `d` gives the same result.
-/
theorem evalInstruction_checker_extends (h : d.Extends c) (s : ExecState) (i : Instruction) :
    (∃ u, evalInstruction (some c) script flags s i = .unsupported u) ∨
      evalInstruction (some d) script flags s i = evalInstruction (some c) script flags s i := by
  unfold evalInstruction
  split
  · exact .inr rfl
  · dsimp only
    split
    · exact .inr rfl
    · split
      · exact .inr rfl
      · by_cases hx : (({ s with opCount := countOp i.opcode s.opCount } : ExecState).fExec ||
            (0x63 ≤ i.opcode && i.opcode ≤ 0x68)) = true
        · simp only [hx, ↓reduceIte]
          rcases execOpcode_checker_extends (script := script) (flags := flags) h
              ({ s with opCount := countOp i.opcode s.opCount } : ExecState).fExec
              { s with opCount := countOp i.opcode s.opCount } i.opcode i.pushed i.next with ⟨u, hu⟩ | he
          · exact .inl ⟨u, by rw [hu]⟩
          · rw [he]; exact .inr rfl
        · simp only [hx]
          exact .inr rfl

/-! ## The call -/

private theorem evalLoop_checker_extends (h : d.Extends c) (s : ExecState) :
    (∃ u, evalLoop (some c) flags script s = .unsupported u) ∨
      evalLoop (some d) flags script s = evalLoop (some c) flags script s := by
  induction s using evalLoop.induct (checker := some c) (flags := flags) (script := script) with
  | case1 s hr _ | case2 s hr _ =>
    rw [evalLoop_atEnd (readInstruction_atEnd_iff.mp hr), evalLoop_atEnd (readInstruction_atEnd_iff.mp hr)]
    exact .inr rfl
  | case3 s o p q hr => rw [evalLoop_truncated hr, evalLoop_truncated hr]; exact .inr rfl
  | case4 s i hr _ t ht ih =>
    rw [evalLoop_instruction hr, evalLoop_instruction hr]
    rcases evalInstruction_checker_extends (script := script) (flags := flags) h s i with ⟨u, hu⟩ | he
    · rw [ht] at hu; cases hu
    · rw [he, ht]; exact ih
  | case5 s i hr _ e he' =>
    rw [evalLoop_instruction hr, evalLoop_instruction hr]
    rcases evalInstruction_checker_extends (script := script) (flags := flags) h s i with ⟨u, hu⟩ | he
    · rw [he'] at hu; cases hu
    · rw [he, he']; exact .inr rfl
  | case6 s i hr _ u hu =>
    rw [evalLoop_instruction hr, hu]
    exact .inl ⟨u, rfl⟩

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every flag set, script and stack:
the call with `c` is unsupported, or the call with `d` gives the same result.
So a call that `c` decides does not depend on the answers of `d` to the requests on which `c` is unavailable.
-/
theorem evalScript_checker_extends (h : d.Extends c) (flags : UInt32) (script : List UInt8)
    (stack : List (List UInt8)) :
    (∃ u, evalScript (some c) flags script stack = .unsupported u) ∨
      evalScript (some d) flags script stack = evalScript (some c) flags script stack := by
  unfold evalScript
  split
  · exact .inr rfl
  · split
    · exact .inr rfl
    · exact evalLoop_checker_extends h _

/--
Take checkers `c` and `d` such that `d` extends `c`.
For every flag set, `scriptSig` and `scriptPubKey`:
`verifyScript` with `c` is unsupported, or `verifyScript` with `d` gives the same result.
The statement covers the evaluation of the redeem script under `P2SH`.
-/
theorem verifyScript_checker_extends (h : d.Extends c) (flags : UInt32) (scriptSig scriptPubKey : List UInt8) :
    (∃ u, verifyScript c flags scriptSig scriptPubKey = .unsupported u) ∨
      verifyScript d flags scriptSig scriptPubKey = verifyScript c flags scriptSig scriptPubKey := by
  unfold verifyScript
  split
  · exact .inr rfl
  · rcases evalScript_checker_extends h flags scriptSig [] with ⟨u, hu⟩ | he
    · exact .inl ⟨u, by rw [hu]⟩
    · rw [he]
      cases evalScript (some c) flags scriptSig [] with
      | rejected e => exact .inr rfl
      | unsupported u => exact .inr rfl
      | ok s =>
        dsimp only
        rcases evalScript_checker_extends h flags scriptPubKey s.stack with ⟨u, hu⟩ | he2
        · exact .inl ⟨u, by rw [hu]⟩
        · rw [he2]
          cases evalScript (some c) flags scriptPubKey s.stack with
          | rejected e => exact .inr rfl
          | unsupported u => exact .inr rfl
          | ok t =>
            dsimp only
            split
            · exact .inr rfl
            · split
              · split
                · exact .inr rfl
                · split
                  · exact .inr rfl
                  · rename_i redeem rest _
                    rcases evalScript_checker_extends h flags redeem rest.reverse with ⟨u, hu⟩ | he3
                    · exact .inl ⟨u, by rw [hu]; rfl⟩
                    · rw [he3]; exact .inr rfl
              · exact .inr rfl

/--
Take checkers `c`, `d₁` and `d₂` such that `d₁` and `d₂` both extend `c`, and any flag set, `scriptSig` and `scriptPubKey`.
If `verifyScript` with `c` is decided, then `verifyScript` gives the same result with `d₁` and with `d₂`.
-/
theorem verifyScript_checker_congr {d₁ d₂ : SignatureChecker} (h₁ : d₁.Extends c) (h₂ : d₂.Extends c)
    {flags : UInt32} {scriptSig scriptPubKey : List UInt8}
    (hc : (verifyScript c flags scriptSig scriptPubKey).Decided) :
    verifyScript d₁ flags scriptSig scriptPubKey = verifyScript d₂ flags scriptSig scriptPubKey := by
  rcases verifyScript_checker_extends h₁ flags scriptSig scriptPubKey with ⟨u, hu⟩ | e₁
  · exact absurd hu (hc.ne_unsupported u)
  · rcases verifyScript_checker_extends h₂ flags scriptSig scriptPubKey with ⟨u, hu⟩ | e₂
    · exact absurd hu (hc.ne_unsupported u)
    · rw [e₁, e₂]

/--
For every checker, supported flag set, `scriptSig` and `scriptPubKey`: `verifyScript` is decided when each of its evaluations is decided.
The evaluations are `scriptSig` on the empty stack, `scriptPubKey` on the final stack of `scriptSig`, and the redeem script.
The redeem script runs only with `P2SH` and the template, on the final stack of `scriptSig` without its top item.
-/
theorem verifyScript_decided {flags : UInt32} {scriptSig scriptPubKey : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (h₁ : (evalScript (some c) flags scriptSig []).Decided)
    (h₂ : ∀ s, evalScript (some c) flags scriptSig [] = .ok s →
      (evalScript (some c) flags scriptPubKey s.stack).Decided)
    (h₃ : ∀ s redeem rest, evalScript (some c) flags scriptSig [] = .ok s →
      hasFlag flags ScriptFlags.p2sh = true → isPayToScriptHash scriptPubKey = true →
      s.stack.reverse = redeem :: rest → (evalScript (some c) flags redeem rest.reverse).Decided) :
    (verifyScript c flags scriptSig scriptPubKey).Decided := by
  unfold verifyScript
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte]
  cases e₁ : evalScript (some c) flags scriptSig [] with
  | rejected e => trivial
  | unsupported u => rw [e₁] at h₁; exact h₁.elim
  | ok s =>
    dsimp only
    have h₂' := h₂ s e₁
    cases e₂ : evalScript (some c) flags scriptPubKey s.stack with
    | rejected e => trivial
    | unsupported u => rw [e₂] at h₂'; exact h₂'.elim
    | ok t =>
      dsimp only
      split
      · trivial
      · split
        · rename_i hp
          simp only [Bool.and_eq_true] at hp
          split
          · trivial
          · split
            · trivial
            · rename_i redeem rest hr
              have h₃' := h₃ s redeem rest e₁ hp.1 hp.2 hr
              cases e₃ : evalScript (some c) flags redeem rest.reverse with
              | rejected e => trivial
              | unsupported u => rw [e₃] at h₃'; exact h₃'.elim
              | ok w => simp only [finishEval]; split <;> trivial
        · trivial

end DogeLib.Script
