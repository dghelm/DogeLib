module

public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Compatibility

/-!
# Proofs: `Proposals.ExampleVersionVerify`, characterization

The example is not a proposal for Dogecoin (`DogeLib.Proposals.ExampleVersionVerify`).

## Domain

Design record 0007, section 10.3, leaves the exact domain of `example_accepted_iff` to this stage. The domain is:

- `scriptPubKey` is `operandScript b S`: the push `L b₁ … b_L` of the operand bytes `b`, then `OP_NOP10`, then the script `S`.
  The push byte `L` is the length of `b`: `OP_0` for the empty operand, and a direct push otherwise.
- The operand has at most 5 bytes. It decodes as Core's `CScriptNum(…, false, 5)` does: `n = ScriptNum.value b`, without the minimal requirement.
  The domain excludes `OP_1NEGATE`, `OP_1` to `OP_16` and the `OP_PUSHDATA` forms as the operand push.
  It also excludes an operand of more than five bytes, whose decode fails with `UNKNOWN_ERROR`.
- `S` has no instruction `0xb9`, read from its start, and neither has `scriptSig`.
  So the only `OP_NOP10` that the evaluation reads is the second instruction of `scriptPubKey`.
- The context is present. The checker and the flag set are arbitrary.

`scriptPubKey` starts with a byte from 0 to 5, so it is never the P2SH template, and no redeem script runs.

## Results

- `readInstruction_operandScript_zero`, `readInstruction_operandScript_nop10`: the first two instructions of `operandScript b S`.
- `opcodeFreeFrom_append`: the opcode test of a script after a prefix is the test of the script alone.
- `example_accepted_iff`: in that domain, the active revision accepts exactly when `verifyScript` accepts and `0 ≤ n ≤ version`.
- `example_spend_accepted_iff`: the same statement for the spend predicate.

Every theorem is Script-local.
-/

@[expose] public section

namespace DogeLib.Proposals.ExampleVersionVerify

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

/-! ## Reading the script -/

/-- For every byte list `b` of at most 75 bytes, the length as a byte keeps its value. -/
theorem toNat_lengthByte {b : List UInt8} (hb : b.length < 0x4c) : b.length.toUInt8.toNat = b.length :=
  ScriptNum.toUInt8_toNat_of_lt (by omega)

/-- Let `b` have at most 75 bytes. For every `S`, the first instruction of `operandScript b S` pushes `b`, and the next cursor is `b.length + 1`. -/
theorem readInstruction_operandScript_zero {b S : List UInt8} (hb : b.length < 0x4c) :
    readInstruction (operandScript b S) 0 =
      .instruction ⟨b.length.toUInt8, b.length.toUInt8 :: b, b, b.length + 1⟩ := by
  have hop : b.length.toUInt8 < 0x4c := by
    rw [UInt8.lt_iff_toNat_lt, toNat_lengthByte hb]; exact hb
  have hw : lengthFieldWidth b.length.toUInt8 = 0 := by
    have h1 : b.length.toUInt8 ≠ 0x4c := fun h => by rw [h] at hop; exact absurd hop (by decide)
    have h2 : b.length.toUInt8 ≠ 0x4d := fun h => by rw [h] at hop; exact absurd hop (by decide)
    have h3 : b.length.toUInt8 ≠ 0x4e := fun h => by rw [h] at hop; exact absurd hop (by decide)
    simp [lengthFieldWidth, h1, h2, h3]
  simp only [readInstruction, operandScript, List.drop_zero, List.cons_append, readOp, hop, ↓reduceIte,
    readPush, toNat_lengthByte hb, List.length_append, List.length_cons]
  have hlt : ¬(b.length + (S.length + 1) < b.length) := by omega
  simp only [hlt, ↓reduceIte]
  simp only [Nat.toUInt8] at hw
  simp [hw]

/-- For every `b` and `S`, the instruction at `b.length + 1` of `operandScript b S` is `OP_NOP10`, and the next cursor is `b.length + 2`. -/
theorem readInstruction_operandScript_nop10 (b S : List UInt8) :
    readInstruction (operandScript b S) (b.length + 1) = .instruction ⟨nop10, [nop10], [], b.length + 2⟩ := by
  have h : (operandScript b S).drop (b.length + 1) = nop10 :: S := by
    simp [operandScript]
  simp only [readInstruction, h, readOp, nop10]
  simp [lengthFieldWidth]

/-- At the end of the script, the opcode test gives `true`. -/
private theorem opcodeFreeFrom_atEnd {O : UInt8 → Bool} {script : List UInt8} {pc : Nat}
    (hr : readInstruction script pc = .atEnd) : opcodeFreeFrom O script pc = true := by
  rw [opcodeFreeFrom]
  split <;> simp_all

/-- At a short push, the opcode test gives `true`. -/
private theorem opcodeFreeFrom_truncated {O : UInt8 → Bool} {script : List UInt8} {pc : Nat} {o : UInt8}
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

/-! ## The two instructions -/

/-- Facts about the push opcode of an operand of at most five bytes. -/
private theorem lengthByte_facts {n : Nat} (hn : n ≤ 5) :
    n.toUInt8 ≤ 0x4e ∧ (∀ k, countOp n.toUInt8 k = k) ∧ isDisabled n.toUInt8 = false ∧
      isNop10 n.toUInt8 = false ∧ n.toUInt8 ≠ 0xa9 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with h | h | h | h | h | h <;>
    subst h <;> refine ⟨by decide, fun k => by simp [countOp], by decide, by decide, by decide⟩

/--
Let `b` have at most five bytes. This holds for every checker, flag set and stack `stk`.
The push of `b` at the start of `operandScript b S` gives `STACK_SIZE` above 1,000 items, and otherwise pushes `b`.
-/
private theorem evalInstruction_operand {checker : Option SignatureChecker} {flags : UInt32} {b S : List UInt8}
    (hb : b.length ≤ 5) (stk : List (List UInt8)) :
    evalInstruction checker (operandScript b S) flags (ExecState.init stk)
        ⟨b.length.toUInt8, b.length.toUInt8 :: b, b, b.length + 1⟩ =
      if maxStackItems < stk.length + 1 then .rejected .stackSize
      else .next { ExecState.init stk with stack := stk ++ [b] } := by
  obtain ⟨hpush, hcount, hdis, -, -⟩ := lengthByte_facts hb
  rw [evalInstruction_exec (by rfl) (by simp [maxScriptElementSize]; omega)
    (by simp [hcount, ExecState.init, maxOpsPerScript]) hdis]
  simp only [hcount, execOpcode_push hpush]
  simp [ExecState.init]

/--
Let the branch of the state `s` execute, with opcode count 0 and at most 1,000 stack items.
Then the baseline step of `OP_NOP10` only counts the opcode, for every checker, flag set, script and cursor `n`.
-/
private theorem evalInstruction_nop10 {checker : Option SignatureChecker} {flags : UInt32} {script : List UInt8}
    {s : ExecState} (n : Nat) (hx : s.fExec = true) (hc : s.opCount = 0)
    (hl : s.stack.length + s.altstack.length ≤ maxStackItems) :
    evalInstruction checker script flags s ⟨nop10, [nop10], [], n⟩ = .next { s with opCount := 1 } := by
  have hcount : countOp nop10 s.opCount = 1 := by simp [countOp, hc, nop10]
  rw [evalInstruction_exec hx (by simp [maxScriptElementSize]) (by simp [hcount, maxOpsPerScript])
    (show isDisabled nop10 = false by decide)]
  simp only [hcount, execOpcode_nop (op := nop10) (by decide)]
  simp [Nat.not_lt.mpr hl]

/-! ## One evaluation of the operand script -/

/-- For every flag set and the two scripts: the verdict of the baseline and that of the error-mapped baseline agree on acceptance. -/
private theorem ofBaseline_eq_accepted {ε : Type} {embed : ScriptError → ε} {r : VerifyResult} :
    VerifyOutcome.ofBaseline embed r = .accepted ↔ r = .accepted := by
  cases r <;> simp [VerifyOutcome.ofBaseline]

/-- For every error map and success state: an error-mapped baseline evaluation succeeds with `t` exactly when the baseline evaluation does. -/
private theorem evalOfBaseline_eq_ok {ε : Type} {embed : ScriptError → ε} {r : EvalResult} {t : ExecState} :
    EvalOutcome.ofBaseline embed r = .ok t ↔ r = .ok t := by
  cases r <;> simp [EvalOutcome.ofBaseline]

/--
Let `scriptPubKey` lie outside the P2SH template. This holds for every step, error map, flag set and `scriptSig`.
`verifyScriptWith` accepts exactly when the flags are supported, both evaluations succeed, and the final top item is true.
-/
private theorem verifyScriptWith_accepted_iff {ε : Type} {embed : ScriptError → ε} {step : Step ε} {flags : UInt32}
    {scriptSig scriptPubKey : List UInt8} (hp : isPayToScriptHash scriptPubKey = false) :
    verifyScriptWith embed step flags scriptSig scriptPubKey = .accepted ↔
      unsupportedFlagBits flags = 0 ∧ ∃ s t, evalScriptWith embed step flags scriptSig [] = .ok s ∧
        evalScriptWith embed step flags scriptPubKey s.stack = .ok t ∧ trueTop t.stack = true := by
  unfold verifyScriptWith
  by_cases hf : unsupportedFlagBits flags = 0
  case neg => simp [hf]
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
  cases hs : evalScriptWith embed step flags scriptSig [] with
  | rejected e => simp
  | unsupported u => simp
  | ok s =>
    simp only
    cases ht : evalScriptWith embed step flags scriptPubKey s.stack with
    | rejected e => simp [ht]
    | unsupported u => simp [ht]
    | ok t =>
      by_cases h1 : trueTop t.stack = true
      · simp [h1, hp, ht]
      · simp [h1, ht]

/--
The evaluation of `operandScript b S`, for an operand of at most 5 bytes and an `S` without `0xb9`.
The active example loop succeeds with `t` exactly when the baseline loop succeeds with `t` and `0 ≤ n ≤ version`.
-/
private theorem evalScriptWith_operand_iff {ctx : ExampleContext} {checker : Option SignatureChecker}
    {flags : UInt32} {b S : List UInt8} (hb₅ : b.length ≤ 5) (hS : opcodeFree isNop10 S = true)
    (stk : List (List UInt8)) (t : ExecState) :
    evalScriptWith Sum.inl (exampleStep true (some ctx) checker flags) flags (operandScript b S) stk = .ok t ↔
      evalScriptWith (ε := ExampleScriptError) Sum.inl (baselineStep Sum.inl checker flags) flags
          (operandScript b S) stk = .ok t ∧
        0 ≤ ScriptNum.value b ∧ ScriptNum.value b ≤ (ctx.tx.version.toNat : Int) := by
  obtain ⟨-, -, -, hnop, -⟩ := lengthByte_facts hb₅
  have hb : b.length < 0x4c := by omega
  unfold evalScriptWith
  by_cases hf : unsupportedFlagBits flags ≠ 0
  · simp [hf]
  simp only [hf, ↓reduceIte]
  by_cases hz : maxScriptSize < (operandScript b S).length
  · simp [hz]
  simp only [hz, ↓reduceIte]
  have h0 : readInstruction (operandScript b S) (ExecState.init stk).pc = _ :=
    readInstruction_operandScript_zero (S := S) hb
  rw [evalLoopWith_instruction h0, evalLoopWith_instruction h0]
  rw [exampleStep_eq_of_not_nop10 _ _ _ _ _ _ _ hnop]
  simp only [baselineStep, evalInstruction_operand hb₅]
  by_cases hl : maxStackItems < stk.length + 1
  · simp [hl, StepOutcome.ofBaseline]
  simp only [hl, ↓reduceIte, StepOutcome.ofBaseline]
  -- The state before `OP_NOP10`.
  have h1 : readInstruction (operandScript b S)
      ({ ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 } : ExecState).pc = _ :=
    readInstruction_operandScript_nop10 b S
  rw [evalLoopWith_instruction h1, evalLoopWith_instruction h1]
  have hn := evalInstruction_nop10 (checker := checker) (flags := flags) (script := operandScript b S)
    (s := { ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 }) (b.length + 2) rfl rfl
    (by simp [ExecState.init]; omega)
  simp only [exampleStep, baselineStep, hn, StepOutcome.ofBaseline]
  have hx : ({ ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 } : ExecState).fExec = true := rfl
  simp only [hx, isNop10, nop10, beq_self_eq_true, Bool.and_self, ↓reduceIte, versionCheck]
  have hdec : ScriptNum.decode b false lockTimeNumSize = .ok (ScriptNum.value b) := by
    simp [ScriptNum.decode, lockTimeNumSize, Nat.not_lt.mpr hb₅]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    hdec]
  -- The rest of the script has no `OP_NOP10`.
  have hfree : opcodeFreeFrom isNop10 (operandScript b S) (b.length + 2) = true := by
    have he : operandScript b S = (b.length.toUInt8 :: b ++ [nop10]) ++ S := by simp [operandScript]
    have hlen : (b.length.toUInt8 :: b ++ [nop10]).length + 0 = b.length + 2 := by simp
    rw [he, ← hlen, opcodeFreeFrom_append]
    exact hS
  have hcongr := evalLoopWith_congr (embed := Sum.inl) (step₁ := exampleStep true (some ctx) checker flags)
    (step₂ := baselineStep Sum.inl checker flags)
    (fun s i hi => exampleStep_eq_of_not_nop10 true (some ctx) checker flags (operandScript b S) s i hi)
    { ExecState.init stk with stack := stk ++ [b], opCount := 1, pc := b.length + 2 } hfree
  by_cases hneg : ScriptNum.value b < 0
  · simp [hneg]; omega
  · by_cases hle : ScriptNum.value b ≤ (ctx.tx.version.toNat : Int)
    · simp only [hneg, hle, ↓reduceIte]
      rw [hcongr]
      constructor
      · intro h; exact ⟨h, by omega, trivial⟩
      · intro h; exact h.1
    · simp [hneg, hle]

/-! ## The characterization -/

/--
`example_accepted_iff`, design record 0007, section 10.3.
This holds for every context, checker `c` and flag set.
Let the operand `b` have at most 5 bytes, and let `n = ScriptNum.value b`, its decode without the minimal requirement.
Let `scriptSig` and `S` have no instruction `0xb9`, and let `scriptPubKey` be `operandScript b S`: the push of `b`, `OP_NOP10`, then `S`.
Then the active revision accepts exactly when `verifyScript c flags` accepts and `0 ≤ n ≤ version`, with the version of the context's transaction read as an unsigned 32-bit value.
Script-local.
-/
theorem example_accepted_iff (ctx : ExampleContext) (c : SignatureChecker) (flags : UInt32)
    {scriptSig b S : List UInt8} (hb₅ : b.length ≤ 5)
    (hsig : opcodeFree isNop10 scriptSig = true) (hS : opcodeFree isNop10 S = true) :
    exampleVerifyScript true (some ctx) c flags scriptSig (operandScript b S) = .accepted ↔
      verifyScript c flags scriptSig (operandScript b S) = .accepted ∧
        0 ≤ ScriptNum.value b ∧ ScriptNum.value b ≤ (ctx.tx.version.toNat : Int) := by
  obtain ⟨-, -, -, -, ha9⟩ := lengthByte_facts hb₅
  have hp : isPayToScriptHash (operandScript b S) = false := by
    simp [isPayToScriptHash, operandScript, ha9]
  unfold exampleVerifyScript
  rw [← ofBaseline_eq_accepted (embed := (Sum.inl : ScriptError → ExampleScriptError)),
    ← verifyScriptWith_baseline, verifyScriptWith_accepted_iff hp, verifyScriptWith_accepted_iff hp]
  rw [evalScriptWith_congr (step₂ := baselineStep Sum.inl (some c) flags)
    (fun s i hi => exampleStep_eq_of_not_nop10 true (some ctx) (some c) flags scriptSig s i hi) flags [] hsig]
  constructor
  · rintro ⟨hf, s, t, hs, ht, htop⟩
    obtain ⟨ht', hr⟩ := (evalScriptWith_operand_iff hb₅ hS s.stack t).mp ht
    exact ⟨⟨hf, s, t, hs, ht', htop⟩, hr⟩
  · rintro ⟨⟨hf, s, t, hs, ht, htop⟩, hr⟩
    exact ⟨hf, s, t, hs, (evalScriptWith_operand_iff hb₅ hS s.stack t).mpr ⟨ht, hr⟩, htop⟩

/--
This holds for every input, previous `scriptPubKey`, flag set and verifier.
Let the operand `b` have at most 5 bytes, and let the input's `scriptSig` and `S` have no instruction `0xb9`.
Let the previous `scriptPubKey` be `operandScript b S`.
Then the active spend predicate accepts exactly when `verifyLegacySpend` accepts and `0 ≤ ScriptNum.value b ≤ version`, with the version of the input's transaction read as an unsigned 32-bit value.
Script-local.
-/
theorem example_spend_accepted_iff (ctx : InputContext) (prevScriptPubKey : Transaction.Script) (flags : UInt32)
    (verify : SignatureVerifier) {b S : List UInt8} (hb₅ : b.length ≤ 5)
    (hsig : opcodeFree isNop10 ctx.input.scriptSig.bytes.val = true) (hS : opcodeFree isNop10 S = true)
    (hprev : prevScriptPubKey.bytes.val = operandScript b S) :
    exampleVerifyLegacySpend true ctx prevScriptPubKey flags verify = .accepted ↔
      verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted ∧
        0 ≤ ScriptNum.value b ∧ ScriptNum.value b ≤ (ctx.tx.version.toNat : Int) := by
  unfold exampleVerifyLegacySpend verifyLegacySpend
  rw [hprev]
  exact example_accepted_iff (.ofInput ctx) _ flags hb₅ hsig hS

end DogeLib.Proposals.ExampleVersionVerify
