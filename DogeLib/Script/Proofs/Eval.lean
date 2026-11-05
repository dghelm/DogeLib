module

public import DogeLib.Script.Eval
public import DogeLib.Script.Proofs.Instruction
public import DogeLib.Script.Proofs.Number
public import DogeLib.Script.Proofs.State

/-!
# Proofs: `Script.Eval`

## The call

- `evalScript_unsupportedFlags`: a flag outside `supportedFlags` gives `unsupported`, before any other check.
- `evalScript_scriptSize`: with supported flags, a script above 10,000 bytes gives `SCRIPT_SIZE`.
- `evalScript_flags_congr`: in this stage, two supported flag sets that agree on the CLTV and CSV bits give the same result.
- `evalScript_ok`: a successful call ends at the end of the script with an empty conditional stack, in a state that satisfies `ExecState.WellFormed`, and within the stack limit unless the script is empty.

## The loop

- `evalLoop_atEnd`: at the end of the script, the call succeeds exactly when the conditional stack is empty, and otherwise gives `UNBALANCED_CONDITIONAL`.
- `evalLoop_truncated`: a short push gives `BAD_OPCODE`.
- `evalLoop_instruction`: after an instruction, the loop continues with the cursor after it, or stops with the instruction's rejection or unsupported result.
- `evalLoop_ok`: the loop form of `evalScript_ok`, from any state that satisfies `ExecState.WellFormed`.

## One instruction

- `evalInstruction_pushSize`, `evalInstruction_opCount`, `evalInstruction_disabled`: Core's checks, in Core's order, whether or not the branch executes.
- `evalInstruction_verif`: `OP_VERIF` and `OP_VERNOTIF` give `BAD_OPCODE`, also in a skipped branch.
- `evalInstruction_skipped`: in a skipped branch, an opcode outside `OP_IF` to `OP_ENDIF` that passes the checks only counts. Both stacks and `vfExec` stay unchanged.
- `evalInstruction_exec`: in an executing branch, an instruction that passes the checks runs `execOpcode`, followed by the stack check.
- `evalInstruction_stackSize`: a successful step leaves at most 1,000 items on the two stacks.
- `evalInstruction_wellFormed`: a successful step and the cursor move keep `ExecState.WellFormed`.
- `execOpcode_frame`: an opcode never changes the cursor or the opcode count, sets the separator cursor only to the cursor after the instruction, and adds at most one entry to `vfExec`, only for `OP_IF` and `OP_NOTIF`.

## Opcode effects

The `execOpcode_*` theorems give the stack effect of each implemented opcode.
Stacks are written bottom first and top last, as in `ExecState`.
`execOpcode_underflow` gives `INVALID_STACK_OPERATION` for each stack opcode on a stack with too few items.
`execOpcode_signature`, `execOpcode_cltv` and `execOpcode_csv` give the unsupported results.

## Numeric and hash opcodes

- `execOpcode_1add` to `execOpcode_within`, and `execOpcode_ripemd160` to `execOpcode_hash256`: the stack effect of each opcode, from the decoded operands.
- `execOpcode_numeric_underflow`, `execOpcode_hash_underflow`: too few items give `INVALID_STACK_OPERATION`.
- `execOpcode_numeric_decode`: an operand that fails a four-byte decode gives `UNKNOWN_ERROR`.
- `execOpcode_addSub_length`: `OP_1ADD`, `OP_1SUB`, `OP_ADD` and `OP_SUB` push at most five bytes. `execOpcode_numeric_length_le_four`: the other numeric opcodes that push a result push at most four bytes.
- `numericOperand_ne_int64Min`, `numericOperand_add_one_le`, `numericOperand_sub_one_ge`, `numericOperand_addSub_mem`: on four-byte operands the asserts of Core's `CScriptNum` operators hold, and no `int64_t` operation overflows.

These theorems are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

/-- A property holds for every byte when it holds for each value below 256, which `decide` can check. -/
private theorem allBytes (P : UInt8 → Prop) (h : ∀ n, n < 256 → P n.toUInt8) (b : UInt8) : P b := by
  simpa using h b.toNat b.toNat_lt

/-! ## Opcode frame -/

/--
For every flag set, branch flag, state, opcode, pushed bytes and next cursor: if `execOpcode` succeeds, the result has the same cursor and opcode count.
Its separator cursor is unchanged or equals `next`.
Its conditional stack has at most one more entry, and only for `OP_IF` (`0x63`) and `OP_NOTIF` (`0x64`).
-/
theorem execOpcode_frame {flags : UInt32} {fExec : Bool} {s t : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (h : execOpcode flags fExec s op pushed next = .next t) :
    t.pc = s.pc ∧ t.opCount = s.opCount ∧
      (t.beginCodeHash = s.beginCodeHash ∨ t.beginCodeHash = next) ∧
      t.vfExec.length ≤ s.vfExec.length + (if op = 0x63 ∨ op = 0x64 then 1 else 0) := by
  unfold execOpcode numUnary numBinary hashTop at h
  repeat' ((try dsimp only at h); split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp_all; try omega)
    | skip

/--
For all flag sets `f` and `g` that agree on the bits of `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY` and `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`, `execOpcode` gives the same result for every other argument.
-/
theorem execOpcode_flags_congr {f g : UInt32}
    (hl : hasFlag f ScriptFlags.checkLockTimeVerify = hasFlag g ScriptFlags.checkLockTimeVerify)
    (hs : hasFlag f ScriptFlags.checkSequenceVerify = hasFlag g ScriptFlags.checkSequenceVerify)
    (fExec : Bool) (s : ExecState) (op : UInt8) (pushed : List UInt8) (next : Nat) :
    execOpcode f fExec s op pushed next = execOpcode g fExec s op pushed next := by
  simp only [execOpcode, hl, hs]

/-! ## One instruction -/

/-- For every flag set, state and instruction that pushes more than 520 bytes: the step gives `PUSH_SIZE`, whether or not the branch executes. -/
theorem evalInstruction_pushSize {flags : UInt32} {s : ExecState} {i : Instruction}
    (h : maxScriptElementSize < i.pushed.length) : evalInstruction flags s i = .rejected .pushSize := by
  simp [evalInstruction, h]

/--
For every flag set, state and instruction that pushes at most 520 bytes: if the opcode count after the instruction exceeds 201, the step gives `OP_COUNT`, whether or not the branch executes.
-/
theorem evalInstruction_opCount {flags : UInt32} {s : ExecState} {i : Instruction}
    (hp : i.pushed.length ≤ maxScriptElementSize) (hc : maxOpsPerScript < countOp i.opcode s.opCount) :
    evalInstruction flags s i = .rejected .opCount := by
  simp [evalInstruction, Nat.not_lt.mpr hp, hc]

/--
For every flag set, state and instruction that pushes at most 520 bytes and keeps the opcode count at most 201: a disabled opcode gives `DISABLED_OPCODE`, whether or not the branch executes.
-/
theorem evalInstruction_disabled {flags : UInt32} {s : ExecState} {i : Instruction}
    (hp : i.pushed.length ≤ maxScriptElementSize) (hc : countOp i.opcode s.opCount ≤ maxOpsPerScript)
    (hd : isDisabled i.opcode = true) : evalInstruction flags s i = .rejected .disabledOpcode := by
  simp [evalInstruction, Nat.not_lt.mpr hp, Nat.not_lt.mpr hc, hd]

/--
For every flag set and state: `OP_VERIF` (`0x65`) and `OP_VERNOTIF` (`0x66`) give `BAD_OPCODE` when the opcode count stays at most 201, whether or not the branch executes.
-/
theorem evalInstruction_verif {flags : UInt32} {s : ExecState} {i : Instruction}
    (hp : i.pushed.length ≤ maxScriptElementSize) (hc : countOp i.opcode s.opCount ≤ maxOpsPerScript)
    (hop : i.opcode = 0x65 ∨ i.opcode = 0x66) : evalInstruction flags s i = .rejected .badOpcode := by
  rcases hop with hop | hop <;> rw [hop] at hc <;>
    simp [evalInstruction, Nat.not_lt.mpr hp, Nat.not_lt.mpr hc, hop, isDisabled, execOpcode,
      isSignatureOpcode]

/--
For every flag set, state `s` in a skipped branch (`s.fExec = false`) within the stack limit, and instruction whose opcode lies outside `OP_IF` to `OP_ENDIF` (`0x63` to `0x68`):
if the push size, the opcode count and the disabled check pass, the step only counts the opcode.
Both stacks, `vfExec` and the separator cursor stay unchanged.
-/
theorem evalInstruction_skipped {flags : UInt32} {s : ExecState} {i : Instruction}
    (hx : s.fExec = false) (hop : i.opcode < 0x63 ∨ 0x68 < i.opcode)
    (hp : i.pushed.length ≤ maxScriptElementSize) (hc : countOp i.opcode s.opCount ≤ maxOpsPerScript)
    (hd : isDisabled i.opcode = false) (hl : s.WithinStackLimit) :
    evalInstruction flags s i = .next { s with opCount := countOp i.opcode s.opCount } := by
  have hr : ¬(0x63 ≤ i.opcode ∧ i.opcode ≤ 0x68) := by
    rcases hop with hop | hop
    · exact fun h => absurd (UInt8.lt_of_lt_of_le hop h.1) (UInt8.lt_irrefl _)
    · exact fun h => absurd (UInt8.lt_of_lt_of_le hop h.2) (UInt8.lt_irrefl _)
  have hx' : ({ s with opCount := countOp i.opcode s.opCount } : ExecState).fExec = false := hx
  simp only [evalInstruction, Nat.not_lt.mpr hp, Nat.not_lt.mpr hc, hd, hx', Bool.false_or, ite_false]
  simp only [decide_eq_true_eq, Bool.and_eq_true, hr, ite_false]
  simp only [ExecState.WithinStackLimit] at hl
  simp [Nat.not_lt.mpr hl]

/--
For every flag set, state `s` whose branch executes (`s.fExec = true`), and instruction `i` that passes the push size, opcode count and disabled checks:
the step runs `execOpcode` on `s` with the new opcode count, and then rejects a result with more than 1,000 items on the two stacks.
-/
theorem evalInstruction_exec {flags : UInt32} {s : ExecState} {i : Instruction}
    (hx : s.fExec = true) (hp : i.pushed.length ≤ maxScriptElementSize)
    (hc : countOp i.opcode s.opCount ≤ maxOpsPerScript) (hd : isDisabled i.opcode = false) :
    evalInstruction flags s i =
      match execOpcode flags true { s with opCount := countOp i.opcode s.opCount } i.opcode i.pushed i.next with
      | .next t => if maxStackItems < t.stack.length + t.altstack.length then .rejected .stackSize else .next t
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u := by
  have hx' : ({ s with opCount := countOp i.opcode s.opCount } : ExecState).fExec = true := hx
  simp only [evalInstruction, Nat.not_lt.mpr hp, Nat.not_lt.mpr hc, hd, hx', Bool.true_or, ite_true,
    ite_false, Bool.false_eq_true]
  rfl

/-- For every flag set, state and instruction: a successful step leaves at most 1,000 items on the main stack and the altstack together. -/
theorem evalInstruction_stackSize {flags : UInt32} {s t : ExecState} {i : Instruction}
    (h : evalInstruction flags s i = .next t) : t.WithinStackLimit := by
  unfold evalInstruction at h
  repeat' ((try dsimp only at h); split at h)
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; simp only [ExecState.WithinStackLimit]; omega)
    | skip

/--
For every flag set, state `s` whose conditional stack is at most its opcode count, and instruction `i`: a successful step keeps the cursor of `s`.
Its separator cursor is that of `s` or `i.next`.
Its opcode count is at most 201, and its conditional stack is at most that count.
-/
private theorem evalInstruction_frame {flags : UInt32} {s t : ExecState} {i : Instruction}
    (h : evalInstruction flags s i = .next t) (hv : s.vfExec.length ≤ s.opCount) :
    t.pc = s.pc ∧ (t.beginCodeHash = s.beginCodeHash ∨ t.beginCodeHash = i.next) ∧
      t.opCount ≤ maxOpsPerScript ∧ t.vfExec.length ≤ t.opCount := by
  unfold evalInstruction at h
  by_cases hA : maxScriptElementSize < i.pushed.length
  · simp [hA] at h
  by_cases hB : maxOpsPerScript < countOp i.opcode s.opCount
  · simp [hA, hB] at h
  by_cases hC : isDisabled i.opcode = true
  · simp [hA, hB, hC] at h
  simp only [hA, hB, hC, ite_false, Bool.false_eq_true] at h
  split at h
  · rename_i u heq
    split at h
    · cases h
    · cases h
      split at heq
      · obtain ⟨h1, h2, h3, h4⟩ := execOpcode_frame heq
        simp only at h1 h2 h3 h4
        refine ⟨h1, h3, by omega, ?_⟩
        rw [h2]
        simp only [countOp] at hB ⊢
        split at h4 <;> rename_i hif
        · rcases hif with hif | hif <;> simp [hif] at h4 ⊢ <;> omega
        · split <;> omega
      · cases heq
        exact ⟨rfl, .inl rfl, by dsimp only; omega, by simp only [countOp] at hB ⊢; split <;> omega⟩
  · cases h
  · cases h

/--
For every script, flag set, state `s` that satisfies `ExecState.WellFormed`, and instruction `i` that `readInstruction` reads at `s.pc`:
if the step succeeds with `t`, then `t` with the cursor moved to `i.next` satisfies `ExecState.WellFormed`, and `t` is within the stack limit.
-/
theorem evalInstruction_wellFormed {script : List UInt8} {flags : UInt32} {s t : ExecState} {i : Instruction}
    (hs : s.WellFormed script) (hr : readInstruction script s.pc = .instruction i)
    (h : evalInstruction flags s i = .next t) :
    ({ t with pc := i.next } : ExecState).WellFormed script ∧ t.WithinStackLimit := by
  obtain ⟨hpc, hb, hc, hv⟩ := evalInstruction_frame h hs.vfExec_length_le
  have hnext : IsBoundary script i.next := .step hs.pc_boundary hr
  have hlt := (readInstruction_consumes hr).1
  refine ⟨⟨hnext, ?_, ?_, hc, hv⟩, evalInstruction_stackSize h⟩
  · rcases hb with hb | hb
    · exact hb ▸ hs.beginCodeHash_boundary
    · exact hb ▸ hnext
  · rcases hb with hb | hb
    · exact hb ▸ Nat.le_trans hs.beginCodeHash_le_pc (Nat.le_of_lt hlt)
    · exact hb ▸ Nat.le_refl _

/-! ## The loop -/

/-- For every flag set, script and state whose cursor is at or after the end: the loop succeeds with the state when `vfExec` is empty, and gives `UNBALANCED_CONDITIONAL` otherwise. -/
theorem evalLoop_atEnd {flags : UInt32} {script : List UInt8} {s : ExecState} (h : script.length ≤ s.pc) :
    evalLoop flags script s = if s.vfExec = [] then .ok s else .rejected .unbalancedConditional := by
  have hr := readInstruction_atEnd_iff.mpr h
  rw [evalLoop]
  split <;> simp_all [List.isEmpty_iff]

/-- For every flag set, script and state at which `readInstruction` finds a short push: the loop gives `BAD_OPCODE`. -/
theorem evalLoop_truncated {flags : UInt32} {script : List UInt8} {s : ExecState} {o : UInt8} {p : ShortPart}
    {c : Nat} (h : readInstruction script s.pc = .truncated o p c) :
    evalLoop flags script s = .rejected .badOpcode := by
  rw [evalLoop]
  split <;> simp_all

/--
For every flag set, script, state `s` and instruction `i` that `readInstruction` reads at `s.pc`: the loop continues from the step's state with the cursor at `i.next`, or stops with the step's rejection or unsupported result.
-/
theorem evalLoop_instruction {flags : UInt32} {script : List UInt8} {s : ExecState} {i : Instruction}
    (h : readInstruction script s.pc = .instruction i) :
    evalLoop flags script s =
      match evalInstruction flags s i with
      | .next t => evalLoop flags script { t with pc := i.next }
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u := by
  rw [evalLoop]
  split <;> (try simp_all) <;> rfl

/--
For every flag set, script and state `s` that satisfies `ExecState.WellFormed`: if the loop succeeds with `t`, then `t` satisfies `ExecState.WellFormed`, its cursor is the end of the script and its conditional stack is empty.
Either `t` is `s`, or `t` is within the stack limit.
-/
theorem evalLoop_ok {flags : UInt32} {script : List UInt8} {s t : ExecState} (hs : s.WellFormed script)
    (h : evalLoop flags script s = .ok t) :
    t.WellFormed script ∧ t.pc = script.length ∧ t.vfExec = [] ∧ (t = s ∨ t.WithinStackLimit) := by
  induction s using evalLoop.induct (flags := flags) (script := script) with
  | case1 s hr he =>
    have hle := readInstruction_atEnd_iff.mp hr
    rw [evalLoop_atEnd hle] at h
    simp only [List.isEmpty_iff.mp he, ite_true, EvalResult.ok.injEq] at h
    subst h
    exact ⟨hs, Nat.le_antisymm hs.pc_le_length hle, List.isEmpty_iff.mp he, .inl rfl⟩
  | case2 s hr he =>
    have hne : s.vfExec ≠ [] := fun h' => he (List.isEmpty_iff.mpr h')
    rw [evalLoop_atEnd (readInstruction_atEnd_iff.mp hr)] at h
    simp [hne] at h
  | case3 s o p c hr =>
    rw [evalLoop_truncated hr] at h
    cases h
  | case4 s i hr _ u hu ih =>
    rw [evalLoop_instruction hr, hu] at h
    obtain ⟨hw, hl⟩ := evalInstruction_wellFormed hs hr hu
    obtain ⟨h1, h2, h3, h4⟩ := ih hw h
    refine ⟨h1, h2, h3, .inr ?_⟩
    rcases h4 with h4 | h4
    · exact h4 ▸ hl
    · exact h4
  | case5 s i hr _ e he =>
    rw [evalLoop_instruction hr, he] at h
    cases h
  | case6 s i hr _ u hu =>
    rw [evalLoop_instruction hr, hu] at h
    cases h

/-! ## The call -/

/-- For every flag set with a bit outside `supportedFlags`, every script and every stack: the call is unsupported, and the reason holds exactly those bits. -/
theorem evalScript_unsupportedFlags {flags : UInt32} {script : List UInt8} {stack : List (List UInt8)}
    (h : unsupportedFlagBits flags ≠ 0) :
    evalScript flags script stack = .unsupported (.flags (unsupportedFlagBits flags)) := by
  simp [evalScript, h]

/-- For every supported flag set, every script above 10,000 bytes and every stack: the call gives `SCRIPT_SIZE`. -/
theorem evalScript_scriptSize {flags : UInt32} {script : List UInt8} {stack : List (List UInt8)}
    (hf : unsupportedFlagBits flags = 0) (h : maxScriptSize < script.length) :
    evalScript flags script stack = .rejected .scriptSize := by
  simp [evalScript, hf, h]

/--
For every flag set, script and stack: if the call succeeds with `t`, then `t` satisfies `ExecState.WellFormed`, its cursor is the end of the script, and its conditional stack is empty.
If the script is not empty, `t` is within the stack limit.
-/
theorem evalScript_ok {flags : UInt32} {script : List UInt8} {stack : List (List UInt8)} {t : ExecState}
    (h : evalScript flags script stack = .ok t) :
    t.WellFormed script ∧ t.pc = script.length ∧ t.vfExec = [] ∧ (script ≠ [] → t.WithinStackLimit) := by
  unfold evalScript at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨h1, h2, h3, h4⟩ := evalLoop_ok (init_wellFormed script stack) h
      refine ⟨h1, h2, h3, fun hne => ?_⟩
      rcases h4 with h4 | h4
      · have : t.pc = 0 := h4 ▸ rfl
        exact absurd (List.length_eq_zero_iff.mp (h2 ▸ this)) hne
      · exact h4

private theorem evalInstruction_flags_congr {f g : UInt32}
    (hl : hasFlag f ScriptFlags.checkLockTimeVerify = hasFlag g ScriptFlags.checkLockTimeVerify)
    (hs : hasFlag f ScriptFlags.checkSequenceVerify = hasFlag g ScriptFlags.checkSequenceVerify)
    (s : ExecState) (i : Instruction) : evalInstruction f s i = evalInstruction g s i := by
  simp only [evalInstruction, execOpcode_flags_congr hl hs]

private theorem evalLoop_flags_congr {f g : UInt32}
    (hl : hasFlag f ScriptFlags.checkLockTimeVerify = hasFlag g ScriptFlags.checkLockTimeVerify)
    (hs : hasFlag f ScriptFlags.checkSequenceVerify = hasFlag g ScriptFlags.checkSequenceVerify)
    (script : List UInt8) (s : ExecState) : evalLoop f script s = evalLoop g script s := by
  induction s using evalLoop.induct (flags := f) (script := script) with
  | case1 s hr _ | case2 s hr _ =>
    rw [evalLoop_atEnd (readInstruction_atEnd_iff.mp hr), evalLoop_atEnd (readInstruction_atEnd_iff.mp hr)]
  | case3 s o p c hr => rw [evalLoop_truncated hr, evalLoop_truncated hr]
  | case4 s i hr _ u hu ih =>
    rw [evalLoop_instruction hr, evalLoop_instruction hr, ← evalInstruction_flags_congr hl hs, hu]
    exact ih
  | case5 s i hr _ e he =>
    rw [evalLoop_instruction hr, evalLoop_instruction hr, ← evalInstruction_flags_congr hl hs, he]
  | case6 s i hr _ u hu =>
    rw [evalLoop_instruction hr, evalLoop_instruction hr, ← evalInstruction_flags_congr hl hs, hu]

/--
For all supported flag sets `f` and `g` that agree on the bits of `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY` and `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`: the call gives the same result on every script and stack.
So `P2SH`, `STRICTENC`, `DERSIG`, `LOW_S` and `NULLDUMMY` do not change one call in this stage.
This holds for this stage's capabilities only: the signature opcodes of stage 3 read `STRICTENC`, `DERSIG`, `LOW_S` and `NULLDUMMY`.
-/
theorem evalScript_flags_congr {f g : UInt32} (hf : unsupportedFlagBits f = 0) (hg : unsupportedFlagBits g = 0)
    (hl : hasFlag f ScriptFlags.checkLockTimeVerify = hasFlag g ScriptFlags.checkLockTimeVerify)
    (hs : hasFlag f ScriptFlags.checkSequenceVerify = hasFlag g ScriptFlags.checkSequenceVerify)
    (script : List UInt8) (stack : List (List UInt8)) : evalScript f script stack = evalScript g script stack := by
  simp only [evalScript, hf, hg, evalLoop_flags_congr hl hs]

/-! ## Opcode effects: pushes and conditionals -/

/-- A push opcode (`0x00` to `0x4e`) pushes its bytes. -/
theorem execOpcode_push {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8} {pushed : List UInt8}
    {next : Nat} (hop : op ≤ 0x4e) :
    execOpcode flags fExec s op pushed next = .next { s with stack := s.stack ++ [pushed] } := by
  simp [execOpcode, hop]

/-- `OP_1NEGATE` (`0x4f`) and `OP_1` to `OP_16` (`0x51` to `0x60`) push the Script number `op - 0x50`. -/
theorem execOpcode_smallInteger {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (hop : op = 0x4f ∨ (0x51 ≤ op ∧ op ≤ 0x60)) :
    execOpcode flags fExec s op pushed next =
      .next { s with stack := s.stack ++ [ScriptNum.encode ((op.toNat : Int) - 0x50)] } := by
  have hle : ¬op ≤ 0x4e := by
    rcases hop with hop | ⟨hop, -⟩
    · subst hop; decide
    · intro h; exact absurd (UInt8.le_trans hop h) (by decide)
  simp [execOpcode, hle, hop]

/-- In an executing branch, `OP_IF` (`0x63`) pops the top item `x` and adds `CastToBool x` to `vfExec`. -/
theorem execOpcode_if {flags : UInt32} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags true s 0x63 pushed next =
      .next { s with stack := rest, vfExec := s.vfExec ++ [castToBool x] } := by
  simp [execOpcode, h]

/-- In an executing branch, `OP_NOTIF` (`0x64`) pops the top item `x` and adds the negation of `CastToBool x` to `vfExec`. -/
theorem execOpcode_notif {flags : UInt32} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags true s 0x64 pushed next =
      .next { s with stack := rest, vfExec := s.vfExec ++ [!castToBool x] } := by
  simp [execOpcode, h]

/-- In an executing branch, `OP_IF` and `OP_NOTIF` on an empty stack give `UNBALANCED_CONDITIONAL`. -/
theorem execOpcode_if_empty {flags : UInt32} {s : ExecState} {op : UInt8} {pushed : List UInt8} {next : Nat}
    (hop : op = 0x63 ∨ op = 0x64) (h : s.stack = []) :
    execOpcode flags true s op pushed next = .rejected .unbalancedConditional := by
  rcases hop with hop | hop <;> simp [execOpcode, hop, h]

/-- In a skipped branch, `OP_IF` and `OP_NOTIF` leave the stack unchanged and add `false` to `vfExec`. -/
theorem execOpcode_if_skipped {flags : UInt32} {s : ExecState} {op : UInt8} {pushed : List UInt8} {next : Nat}
    (hop : op = 0x63 ∨ op = 0x64) :
    execOpcode flags false s op pushed next = .next { s with vfExec := s.vfExec ++ [false] } := by
  rcases hop with hop | hop <;> simp [execOpcode, hop]

/-- `OP_ELSE` (`0x67`) negates the last entry of `vfExec`. -/
theorem execOpcode_else {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {v : List Bool} {b : Bool} (h : s.vfExec = v ++ [b]) :
    execOpcode flags fExec s 0x67 pushed next = .next { s with vfExec := v ++ [!b] } := by
  simp [execOpcode, h]

/-- `OP_ENDIF` (`0x68`) removes the last entry of `vfExec`. -/
theorem execOpcode_endif {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {v : List Bool} {b : Bool} (h : s.vfExec = v ++ [b]) :
    execOpcode flags fExec s 0x68 pushed next = .next { s with vfExec := v } := by
  simp [execOpcode, h]

/-- `OP_ELSE` and `OP_ENDIF` with an empty `vfExec` give `UNBALANCED_CONDITIONAL`. -/
theorem execOpcode_else_endif_empty {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (hop : op = 0x67 ∨ op = 0x68) (h : s.vfExec = []) :
    execOpcode flags fExec s op pushed next = .rejected .unbalancedConditional := by
  rcases hop with hop | hop <;> simp [execOpcode, hop, h]

/-- `OP_VERIFY` (`0x69`) pops a top item that `CastToBool` makes true. -/
theorem execOpcode_verify_true {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x])
    (hx : castToBool x = true) :
    execOpcode flags fExec s 0x69 pushed next = .next { s with stack := rest } := by
  simp [execOpcode, h, hx]

/-- `OP_VERIFY` gives `VERIFY` on a top item that `CastToBool` makes false, such as negative zero. -/
theorem execOpcode_verify_false {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x])
    (hx : castToBool x = false) :
    execOpcode flags fExec s 0x69 pushed next = .rejected .verify := by
  simp [execOpcode, h, hx]

/-- `OP_RETURN` (`0x6a`) gives `OP_RETURN`. -/
theorem execOpcode_return {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat} :
    execOpcode flags fExec s 0x6a pushed next = .rejected .opReturn := by
  simp [execOpcode]

/-- The NOPs: `OP_NOP` (`0x61`), `OP_NOP1` (`0xb0`) and `OP_NOP4` to `OP_NOP10` (`0xb3` to `0xb9`) leave the state unchanged. -/
theorem execOpcode_nop {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8} {pushed : List UInt8}
    {next : Nat} (hop : op = 0x61 ∨ op = 0xb0 ∨ (0xb3 ≤ op ∧ op ≤ 0xb9)) :
    execOpcode flags fExec s op pushed next = .next s := by
  rcases hop with hop | hop | ⟨h1, h2⟩
  · simp [execOpcode, hop]
  · simp [execOpcode, hop]
  · have : op ∈ [0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9] :=
      allBytes (fun op => 0xb3 ≤ op → op ≤ 0xb9 → op ∈ [0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9])
        (by decide +kernel) op h1 h2
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at this
    rcases this with h | h | h | h | h | h | h <;> simp [execOpcode, h]

/-- Without `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY`, `OP_CHECKLOCKTIMEVERIFY` (`0xb1`) is `OP_NOP2`. -/
theorem execOpcode_nop2 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    (h : hasFlag flags ScriptFlags.checkLockTimeVerify = false) :
    execOpcode flags fExec s 0xb1 pushed next = .next s := by
  simp [execOpcode, h]

/-- Without `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`, `OP_CHECKSEQUENCEVERIFY` (`0xb2`) is `OP_NOP3`. -/
theorem execOpcode_nop3 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    (h : hasFlag flags ScriptFlags.checkSequenceVerify = false) :
    execOpcode flags fExec s 0xb2 pushed next = .next s := by
  simp [execOpcode, h]

/-- With `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY`, `OP_CHECKLOCKTIMEVERIFY` is unsupported. -/
theorem execOpcode_cltv {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    (h : hasFlag flags ScriptFlags.checkLockTimeVerify = true) :
    execOpcode flags fExec s 0xb1 pushed next = .unsupported .checkLockTimeVerify := by
  simp [execOpcode, h]

/-- With `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`, `OP_CHECKSEQUENCEVERIFY` is unsupported. -/
theorem execOpcode_csv {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    (h : hasFlag flags ScriptFlags.checkSequenceVerify = true) :
    execOpcode flags fExec s 0xb2 pushed next = .unsupported .checkSequenceVerify := by
  simp [execOpcode, h]

/-! ## Opcode effects: stack operations -/

/-- `OP_TOALTSTACK` (`0x6b`) moves the top item to the altstack. -/
theorem execOpcode_toAltStack {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0x6b pushed next = .next { s with stack := rest, altstack := s.altstack ++ [x] } := by
  simp [execOpcode, h]

/-- `OP_FROMALTSTACK` (`0x6c`) moves the top item of the altstack to the main stack. -/
theorem execOpcode_fromAltStack {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.altstack = rest ++ [x]) :
    execOpcode flags fExec s 0x6c pushed next = .next { s with stack := s.stack ++ [x], altstack := rest } := by
  simp [execOpcode, h]

/-- `OP_FROMALTSTACK` with an empty altstack gives `INVALID_ALTSTACK_OPERATION`. -/
theorem execOpcode_fromAltStack_empty {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} (h : s.altstack = []) :
    execOpcode flags fExec s 0x6c pushed next = .rejected .invalidAltstackOperation := by
  simp [execOpcode, h]

/-- `OP_2DROP` (`0x6d`): `x1 x2 → `. -/
theorem execOpcode_2drop {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x6d pushed next = .next { s with stack := rest } := by
  simp [execOpcode, h]

/-- `OP_2DUP` (`0x6e`): `x1 x2 → x1 x2 x1 x2`. -/
theorem execOpcode_2dup {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x6e pushed next = .next { s with stack := rest ++ [x1, x2, x1, x2] } := by
  simp [execOpcode, h]

/-- `OP_3DUP` (`0x6f`): `x1 x2 x3 → x1 x2 x3 x1 x2 x3`. -/
theorem execOpcode_3dup {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 x3 : List UInt8} (h : s.stack = rest ++ [x1, x2, x3]) :
    execOpcode flags fExec s 0x6f pushed next = .next { s with stack := rest ++ [x1, x2, x3, x1, x2, x3] } := by
  simp [execOpcode, h]

/-- `OP_2OVER` (`0x70`): `x1 x2 x3 x4 → x1 x2 x3 x4 x1 x2`. -/
theorem execOpcode_2over {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 x3 x4 : List UInt8} (h : s.stack = rest ++ [x1, x2, x3, x4]) :
    execOpcode flags fExec s 0x70 pushed next = .next { s with stack := rest ++ [x1, x2, x3, x4, x1, x2] } := by
  simp [execOpcode, h]

/-- `OP_2ROT` (`0x71`): `x1 x2 x3 x4 x5 x6 → x3 x4 x5 x6 x1 x2`. -/
theorem execOpcode_2rot {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 x3 x4 x5 x6 : List UInt8} (h : s.stack = rest ++ [x1, x2, x3, x4, x5, x6]) :
    execOpcode flags fExec s 0x71 pushed next = .next { s with stack := rest ++ [x3, x4, x5, x6, x1, x2] } := by
  simp [execOpcode, h]

/-- `OP_2SWAP` (`0x72`): `x1 x2 x3 x4 → x3 x4 x1 x2`. -/
theorem execOpcode_2swap {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 x3 x4 : List UInt8} (h : s.stack = rest ++ [x1, x2, x3, x4]) :
    execOpcode flags fExec s 0x72 pushed next = .next { s with stack := rest ++ [x3, x4, x1, x2] } := by
  simp [execOpcode, h]

/-- `OP_IFDUP` (`0x73`) duplicates a top item that `CastToBool` makes true. -/
theorem execOpcode_ifdup_true {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x])
    (hx : castToBool x = true) :
    execOpcode flags fExec s 0x73 pushed next = .next { s with stack := rest ++ [x, x] } := by
  simp [execOpcode, h, hx]

/-- `OP_IFDUP` leaves the state unchanged when `CastToBool` makes the top item false, such as negative zero. -/
theorem execOpcode_ifdup_false {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x])
    (hx : castToBool x = false) :
    execOpcode flags fExec s 0x73 pushed next = .next s := by
  simp [execOpcode, h, hx]

/-- `OP_DEPTH` (`0x74`) pushes the number of items on the main stack. -/
theorem execOpcode_depth {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat} :
    execOpcode flags fExec s 0x74 pushed next =
      .next { s with stack := s.stack ++ [ScriptNum.encode s.stack.length] } := by
  simp [execOpcode]

/-- `OP_DROP` (`0x75`): `x → `. -/
theorem execOpcode_drop {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0x75 pushed next = .next { s with stack := rest } := by
  simp [execOpcode, h]

/-- `OP_DUP` (`0x76`): `x → x x`. -/
theorem execOpcode_dup {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0x76 pushed next = .next { s with stack := rest ++ [x, x] } := by
  simp [execOpcode, h]

/-- `OP_NIP` (`0x77`): `x1 x2 → x2`. -/
theorem execOpcode_nip {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x77 pushed next = .next { s with stack := rest ++ [x2] } := by
  simp [execOpcode, h]

/-- `OP_OVER` (`0x78`): `x1 x2 → x1 x2 x1`. -/
theorem execOpcode_over {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x78 pushed next = .next { s with stack := rest ++ [x1, x2, x1] } := by
  simp [execOpcode, h]

/-- `OP_ROT` (`0x7b`): `x1 x2 x3 → x2 x3 x1`. -/
theorem execOpcode_rot {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 x3 : List UInt8} (h : s.stack = rest ++ [x1, x2, x3]) :
    execOpcode flags fExec s 0x7b pushed next = .next { s with stack := rest ++ [x2, x3, x1] } := by
  simp [execOpcode, h]

/-- `OP_SWAP` (`0x7c`): `x1 x2 → x2 x1`. -/
theorem execOpcode_swap {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x7c pushed next = .next { s with stack := rest ++ [x2, x1] } := by
  simp [execOpcode, h]

/-- `OP_TUCK` (`0x7d`): `x1 x2 → x2 x1 x2`. -/
theorem execOpcode_tuck {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x7d pushed next = .next { s with stack := rest ++ [x2, x1, x2] } := by
  simp [execOpcode, h]

/-- `OP_SIZE` (`0x82`): `x → x n`, where `n` is the Script number of the length of `x`. -/
theorem execOpcode_size {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0x82 pushed next =
      .next { s with stack := rest ++ [x, ScriptNum.encode x.length] } := by
  simp [execOpcode, h]

/--
`OP_PICK` (`0x79`): `below x above n → below x above x`, where `n` decodes as a four-byte Script number whose `getint` is the number of items in `above`.
-/
theorem execOpcode_pick {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {below above : List (List UInt8)} {x n : List UInt8} {v : Int}
    (h : s.stack = below ++ [x] ++ above ++ [n]) (hn : ScriptNum.decode n false = .ok v)
    (hv : ScriptNum.getint v = above.length) :
    execOpcode flags fExec s 0x79 pushed next = .next { s with stack := below ++ [x] ++ above ++ [x] } := by
  have hlen : (above.reverse ++ x :: below.reverse)[above.length]? = some x := by
    rw [List.getElem?_append_right (by simp)]; simp
  cases hr : above.reverse ++ x :: below.reverse with
  | nil => simp at hr
  | cons a t =>
    rw [hr] at hlen
    have hrev : t.reverse ++ [a] = below ++ x :: above := by
      have := congrArg List.reverse hr
      simpa using this.symm
    simp [execOpcode, h, hn, hv, List.reverse_append, hr, hlen]
    have hpos : ¬((above.length : Int) < 0) := by omega
    simp only [hpos, ite_false]
    rw [show t.reverse ++ [a, x] = (t.reverse ++ [a]) ++ [x] by simp, hrev]
    simp

/--
`OP_ROLL` (`0x7a`): `below x above n → below above x`, where `n` decodes as a four-byte Script number whose `getint` is the number of items in `above`.
-/
theorem execOpcode_roll {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {below above : List (List UInt8)} {x n : List UInt8} {v : Int}
    (h : s.stack = below ++ [x] ++ above ++ [n]) (hn : ScriptNum.decode n false = .ok v)
    (hv : ScriptNum.getint v = above.length) :
    execOpcode flags fExec s 0x7a pushed next = .next { s with stack := below ++ above ++ [x] } := by
  have hlen : (above.reverse ++ x :: below.reverse)[above.length]? = some x := by
    rw [List.getElem?_append_right (by simp)]; simp
  have hera : (above.reverse ++ x :: below.reverse).eraseIdx above.length = above.reverse ++ below.reverse := by
    rw [List.eraseIdx_append_of_length_le (by simp)]; simp
  cases hr : above.reverse ++ x :: below.reverse with
  | nil => simp at hr
  | cons a t =>
    rw [hr] at hlen hera
    simp [execOpcode, h, hn, hv, List.reverse_append, hr, hlen, hera]

/-- `OP_PICK` and `OP_ROLL` give `UNKNOWN_ERROR` when the top item fails to decode as a four-byte Script number, on a stack of at least two items. -/
theorem execOpcode_pickRoll_decode {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} {rest : List (List UInt8)} {y n : List UInt8} {e : ScriptNum.DecodeError}
    (hop : op = 0x79 ∨ op = 0x7a) (h : s.stack = rest ++ [y, n]) (hn : ScriptNum.decode n false = .error e) :
    execOpcode flags fExec s op pushed next = .rejected .unknownError := by
  rcases hop with hop | hop <;> simp [execOpcode, hop, h, hn]

/--
`OP_PICK` and `OP_ROLL` give `INVALID_STACK_OPERATION` when the `getint` of the decoded operand is negative or at least the number of items below it.
-/
theorem execOpcode_pickRoll_range {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} {rest : List (List UInt8)} {n : List UInt8} {v : Int}
    (hop : op = 0x79 ∨ op = 0x7a) (h : s.stack = rest ++ [n]) (hne : rest ≠ [])
    (hn : ScriptNum.decode n false = .ok v)
    (hv : ScriptNum.getint v < 0 ∨ rest.length ≤ ScriptNum.getint v) :
    execOpcode flags fExec s op pushed next = .rejected .invalidStackOperation := by
  cases hr : rest.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp hr) hne
  | cons a t =>
    have hl : t.length + 1 = rest.length := by
      have := congrArg List.length hr
      simp only [List.length_reverse, List.length_cons] at this
      omega
    by_cases hneg : ScriptNum.getint v < 0
    · rcases hop with rfl | rfl <;> simp [execOpcode, h, hr, hn, hneg]
    · have hnone : (a :: t)[(ScriptNum.getint v).toNat]? = none :=
        List.getElem?_eq_none (by simp; omega)
      rcases hop with rfl | rfl <;> simp [execOpcode, h, hr, hn, hneg, hnone]

/-! ## Opcode effects: equality -/

/-- `OP_EQUAL` (`0x87`): `x1 x2 → b`, where `b` is `0x01` when the items are equal and the empty string otherwise. -/
theorem execOpcode_equal {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2]) :
    execOpcode flags fExec s 0x87 pushed next = .next { s with stack := rest ++ [boolBytes (x1 == x2)] } := by
  simp [execOpcode, h]

/-- `OP_EQUALVERIFY` (`0x88`) pops two equal items. -/
theorem execOpcode_equalVerify_eq {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x, x]) :
    execOpcode flags fExec s 0x88 pushed next = .next { s with stack := rest } := by
  simp [execOpcode, h]

/-- `OP_EQUALVERIFY` gives `EQUALVERIFY` on two different items. -/
theorem execOpcode_equalVerify_ne {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x1 x2 : List UInt8} (h : s.stack = rest ++ [x1, x2])
    (hne : x1 ≠ x2) :
    execOpcode flags fExec s 0x88 pushed next = .rejected .equalVerify := by
  simp [execOpcode, h, hne]

/-- `OP_CODESEPARATOR` (`0xab`) sets the separator cursor to the cursor after the instruction. -/
theorem execOpcode_codeSeparator {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} : execOpcode flags fExec s 0xab pushed next = .next { s with beginCodeHash := next } := by
  simp [execOpcode]

/-! ## Opcode effects: numbers -/

/-- A truth value as a script number encodes as the bytes of `OP_EQUAL`: `[1]` for true and `[]` for false. -/
theorem encode_ofBool (b : Bool) : ScriptNum.encode (ofBool b) = boolBytes b := by
  cases b
  · simp [ofBool, boolBytes, ScriptNum.encode_zero]
  · simp [ofBool, boolBytes, ScriptNum.encode, ScriptNum.leBytes_of_lt (c := 1) (by decide) (by decide)]
    decide

/-- `OP_1ADD` (`0x8b`): `x → encode (a + 1)`, where `x` decodes as the four-byte script number `a`. -/
theorem execOpcode_1add {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x8b pushed next = .next { s with stack := rest ++ [ScriptNum.encode (a + 1)] } := by
  simp [execOpcode, numUnary, h, hx]

/-- `OP_1SUB` (`0x8c`): `x → encode (a - 1)`, where `x` decodes as the four-byte script number `a`. -/
theorem execOpcode_1sub {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x8c pushed next = .next { s with stack := rest ++ [ScriptNum.encode (a - 1)] } := by
  simp [execOpcode, numUnary, h, hx]

/-- `OP_NEGATE` (`0x8f`): `x → encode (-a)`, where `x` decodes as the four-byte script number `a`. -/
theorem execOpcode_negate {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x8f pushed next = .next { s with stack := rest ++ [ScriptNum.encode (-a)] } := by
  simp [execOpcode, numUnary, h, hx]

/-- `OP_ABS` (`0x90`): `x → encode |a|`, where `x` decodes as the four-byte script number `a`. -/
theorem execOpcode_abs {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x90 pushed next =
      .next { s with stack := rest ++ [ScriptNum.encode (a.natAbs : Int)] } := by
  have : (if a < 0 then -a else a) = (a.natAbs : Int) := by split <;> omega
  simp [execOpcode, numUnary, h, hx, this]

/-- `OP_NOT` (`0x91`): `x → b`, where `b` is `[1]` when `x` decodes as zero and `[]` otherwise. -/
theorem execOpcode_not {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x91 pushed next = .next { s with stack := rest ++ [boolBytes (decide (a = 0))] } := by
  simp [execOpcode, numUnary, h, hx, ← encode_ofBool]

/-- `OP_0NOTEQUAL` (`0x92`): `x → b`, where `b` is `[1]` when `x` decodes as a nonzero number and `[]` otherwise. -/
theorem execOpcode_0notequal {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} {a : Int} (h : s.stack = rest ++ [x])
    (hx : ScriptNum.decode x false = .ok a) :
    execOpcode flags fExec s 0x92 pushed next = .next { s with stack := rest ++ [boolBytes (decide (a ≠ 0))] } := by
  simp [execOpcode, numUnary, h, hx, ← encode_ofBool]

/-- `OP_ADD` (`0x93`): `x1 x2 → encode (a + b)`, where `x1` and `x2` decode as the four-byte script numbers `a` and `b`. -/
theorem execOpcode_add {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x93 pushed next = .next { s with stack := rest ++ [ScriptNum.encode (a + b)] } := by
  simp [execOpcode, numBinary, h, h1, h2]

/-- `OP_SUB` (`0x94`): `x1 x2 → encode (a - b)`, where `x1` and `x2` decode as `a` and `b`. The top item is subtracted. -/
theorem execOpcode_sub {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x94 pushed next = .next { s with stack := rest ++ [ScriptNum.encode (a - b)] } := by
  simp [execOpcode, numBinary, h, h1, h2]

/-- `OP_BOOLAND` (`0x9a`): `x1 x2 → [1]` when both decode as nonzero numbers, and `[]` otherwise. -/
theorem execOpcode_boolAnd {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x9a pushed next =
      .next { s with stack := rest ++ [boolBytes (decide (a ≠ 0 ∧ b ≠ 0))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_BOOLOR` (`0x9b`): `x1 x2 → [1]` when either decodes as a nonzero number, and `[]` otherwise. -/
theorem execOpcode_boolOr {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x9b pushed next =
      .next { s with stack := rest ++ [boolBytes (decide (a ≠ 0 ∨ b ≠ 0))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_NUMEQUAL` (`0x9c`): `x1 x2 → [1]` when they decode as equal numbers, and `[]` otherwise. -/
theorem execOpcode_numEqual {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x9c pushed next = .next { s with stack := rest ++ [boolBytes (decide (a = b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_NUMEQUALVERIFY` (`0x9d`) pops two items that decode as equal numbers. -/
theorem execOpcode_numEqualVerify_eq {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x1 x2 : List UInt8} {a : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok a) :
    execOpcode flags fExec s 0x9d pushed next = .next { s with stack := rest } := by
  simp [execOpcode, h, h1, h2]

/-- `OP_NUMEQUALVERIFY` gives `NUMEQUALVERIFY` on two items that decode as different numbers. -/
theorem execOpcode_numEqualVerify_ne {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) (hne : a ≠ b) :
    execOpcode flags fExec s 0x9d pushed next = .rejected .numEqualVerify := by
  simp [execOpcode, h, h1, h2, hne]

/-- `OP_NUMNOTEQUAL` (`0x9e`): `x1 x2 → [1]` when they decode as different numbers, and `[]` otherwise. -/
theorem execOpcode_numNotEqual {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x9e pushed next = .next { s with stack := rest ++ [boolBytes (decide (a ≠ b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_LESSTHAN` (`0x9f`): `x1 x2 → [1]` when `a < b`, and `[]` otherwise, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_lessThan {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0x9f pushed next = .next { s with stack := rest ++ [boolBytes (decide (a < b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_GREATERTHAN` (`0xa0`): `x1 x2 → [1]` when `a > b`, and `[]` otherwise, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_greaterThan {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0xa0 pushed next = .next { s with stack := rest ++ [boolBytes (decide (a > b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_LESSTHANOREQUAL` (`0xa1`): `x1 x2 → [1]` when `a ≤ b`, and `[]` otherwise, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_lessThanOrEqual {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0xa1 pushed next = .next { s with stack := rest ++ [boolBytes (decide (a ≤ b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_GREATERTHANOREQUAL` (`0xa2`): `x1 x2 → [1]` when `a ≥ b`, and `[]` otherwise, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_greaterThanOrEqual {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8}
    {next : Nat} {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0xa2 pushed next = .next { s with stack := rest ++ [boolBytes (decide (a ≥ b))] } := by
  simp [execOpcode, numBinary, h, h1, h2, ← encode_ofBool]

/-- `OP_MIN` (`0xa3`): `x1 x2 → encode (min a b)`, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_min {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0xa3 pushed next = .next { s with stack := rest ++ [ScriptNum.encode (min a b)] } := by
  have : (if a < b then a else b) = min a b := by simp only [Int.min_def]; split <;> split <;> omega
  simp [execOpcode, numBinary, h, h1, h2, this]

/-- `OP_MAX` (`0xa4`): `x1 x2 → encode (max a b)`, where `x1` and `x2` decode as `a` and `b`. -/
theorem execOpcode_max {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x1 x2 : List UInt8} {a b : Int} (h : s.stack = rest ++ [x1, x2])
    (h1 : ScriptNum.decode x1 false = .ok a) (h2 : ScriptNum.decode x2 false = .ok b) :
    execOpcode flags fExec s 0xa4 pushed next = .next { s with stack := rest ++ [ScriptNum.encode (max a b)] } := by
  have : (if a > b then a else b) = max a b := by simp only [Int.max_def]; split <;> split <;> omega
  simp [execOpcode, numBinary, h, h1, h2, this]

/--
`OP_WITHIN` (`0xa5`): `x xlo xhi → [1]` when `lo ≤ a < hi`, and `[]` otherwise.
Here `x`, `xlo` and `xhi` decode as the four-byte script numbers `a`, `lo` and `hi`.
-/
theorem execOpcode_within {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x xlo xhi : List UInt8} {a lo hi : Int} (h : s.stack = rest ++ [x, xlo, xhi])
    (hx : ScriptNum.decode x false = .ok a) (hlo : ScriptNum.decode xlo false = .ok lo)
    (hhi : ScriptNum.decode xhi false = .ok hi) :
    execOpcode flags fExec s 0xa5 pushed next =
      .next { s with stack := rest ++ [boolBytes (decide (lo ≤ a ∧ a < hi))] } := by
  simp [execOpcode, h, hx, hlo, hhi]

/-! ## Opcode effects: hashes -/

/-- `OP_RIPEMD160` (`0xa6`): `x → RIPEMD-160 (x)`. -/
theorem execOpcode_ripemd160 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0xa6 pushed next =
      .next { s with stack := rest ++ [(Cryptography.Hash.ripemd160 ⟨x.toArray⟩).toList] } := by
  simp [execOpcode, hashTop, h]

/-- `OP_SHA1` (`0xa7`): `x → SHA-1 (x)`. -/
theorem execOpcode_sha1 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0xa7 pushed next =
      .next { s with stack := rest ++ [(Cryptography.Hash.sha1 ⟨x.toArray⟩).toList] } := by
  simp [execOpcode, hashTop, h]

/-- `OP_SHA256` (`0xa8`): `x → SHA-256 (x)`. -/
theorem execOpcode_sha256 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0xa8 pushed next =
      .next { s with stack := rest ++ [(Cryptography.Hash.sha256 ⟨x.toArray⟩).toList] } := by
  simp [execOpcode, hashTop, h]

/-- `OP_HASH160` (`0xa9`): `x → Hash160 (x)`, RIPEMD-160 of SHA-256. -/
theorem execOpcode_hash160 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0xa9 pushed next =
      .next { s with stack := rest ++ [(Cryptography.Hash.hash160 ⟨x.toArray⟩).toList] } := by
  simp [execOpcode, hashTop, h]

/-- `OP_HASH256` (`0xaa`): `x → SHA-256 (SHA-256 (x))`. -/
theorem execOpcode_hash256 {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {x : List UInt8} (h : s.stack = rest ++ [x]) :
    execOpcode flags fExec s 0xaa pushed next =
      .next { s with stack := rest ++ [(Cryptography.Hash.Sha256d.hash ⟨x.toArray⟩).toList] } := by
  simp [execOpcode, hashTop, h]

/-! ## Underflow -/

/-- The stack opcodes and the number of main-stack items each needs (D3, lines 478 to 738). -/
def stackArity : List (UInt8 × Nat) :=
  [(0x69, 1), (0x6b, 1), (0x6d, 2), (0x6e, 2), (0x6f, 3), (0x70, 4), (0x71, 6), (0x72, 4), (0x73, 1),
    (0x75, 1), (0x76, 1), (0x77, 2), (0x78, 2), (0x79, 2), (0x7a, 2), (0x7b, 3), (0x7c, 2), (0x7d, 2),
    (0x82, 1), (0x87, 2), (0x88, 2)]

/--
For each pair `(op, k)` of `stackArity`: `op` on a main stack of fewer than `k` items gives `INVALID_STACK_OPERATION`.
The pairs are `OP_VERIFY`, `OP_TOALTSTACK` to `OP_IFDUP`, `OP_DROP` to `OP_TUCK`, `OP_SIZE`, `OP_EQUAL` and `OP_EQUALVERIFY`.
-/
theorem execOpcode_underflow {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8} {k : Nat}
    {pushed : List UInt8} {next : Nat} (hop : (op, k) ∈ stackArity) (h : s.stack.length < k) :
    execOpcode flags fExec s op pushed next = .rejected .invalidStackOperation := by
  have hr : s.stack.reverse.length < k := by simpa using h
  simp only [stackArity, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hop
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [execOpcode]
    generalize s.stack.reverse = r at hr ⊢
    rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;> simp_all <;> omega

/-! ## Numeric and hash failures -/

/-- The numeric opcodes and the number of operands each pops (D3, lines 744 to 841). -/
def numericArity : List (UInt8 × Nat) :=
  [(0x8b, 1), (0x8c, 1), (0x8f, 1), (0x90, 1), (0x91, 1), (0x92, 1), (0x93, 2), (0x94, 2), (0x9a, 2), (0x9b, 2),
    (0x9c, 2), (0x9d, 2), (0x9e, 2), (0x9f, 2), (0xa0, 2), (0xa1, 2), (0xa2, 2), (0xa3, 2), (0xa4, 2), (0xa5, 3)]

/-- For each pair `(op, k)` of `numericArity`: `op` on a main stack of fewer than `k` items gives `INVALID_STACK_OPERATION`. -/
theorem execOpcode_numeric_underflow {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8} {k : Nat}
    {pushed : List UInt8} {next : Nat} (hop : (op, k) ∈ numericArity) (h : s.stack.length < k) :
    execOpcode flags fExec s op pushed next = .rejected .invalidStackOperation := by
  have hr : s.stack.reverse.length < k := by simpa using h
  simp only [numericArity, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hop
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · simp only [execOpcode, numUnary, numBinary]
    generalize s.stack.reverse = r at hr ⊢
    rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> simp_all <;> omega

/--
For each pair `(op, k)` of `numericArity`, let `args` be the top `k` items of the main stack.
If one of them fails a four-byte decode, `op` gives `UNKNOWN_ERROR`.
-/
theorem execOpcode_numeric_decode {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8} {k : Nat}
    {pushed : List UInt8} {next : Nat} {rest args : List (List UInt8)} {x : List UInt8}
    {e : ScriptNum.DecodeError} (hop : (op, k) ∈ numericArity) (h : s.stack = rest ++ args)
    (hk : args.length = k) (hx : x ∈ args) (he : ScriptNum.decode x false = .error e) :
    execOpcode flags fExec s op pushed next = .rejected .unknownError := by
  simp only [numericArity, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hop
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rcases args with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨_, _⟩⟩⟩⟩ <;> simp only [List.length_cons, List.length_nil] at hk <;>
      (try omega) <;>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx <;>
      rcases hx with rfl | rfl | rfl <;>
      simp only [execOpcode, numUnary, numBinary, h, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, he] <;>
      (repeat' split) <;> simp_all

/-- Each hash opcode, `0xa6` to `0xaa`, on an empty main stack gives `INVALID_STACK_OPERATION`. -/
theorem execOpcode_hash_underflow {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (hop : op ∈ [0xa6, 0xa7, 0xa8, 0xa9, 0xaa]) (h : s.stack = []) :
    execOpcode flags fExec s op pushed next = .rejected .invalidStackOperation := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl <;> simp [execOpcode, hashTop, h]

/-! ## Numeric results -/

/-- A successful unary numeric step pops one item that decodes as `a` and pushes `encode (f a)`. -/
private theorem numUnary_next {s t : ExecState} {f : Int → Int} (h : numUnary s f = .next t) :
    ∃ rest x a, s.stack = rest ++ [x] ∧ ScriptNum.decode x false = .ok a ∧
      t.stack = rest ++ [ScriptNum.encode (f a)] := by
  unfold numUnary at h
  split at h
  · cases h
  · rename_i x rest hr
    split at h
    · cases h
    · rename_i a ha
      cases h
      exact ⟨rest.reverse, x, a, by simpa using congrArg List.reverse hr, ha, rfl⟩

/-- A successful binary numeric step pops two items that decode as `a` and `b` and pushes `encode (f a b)`. -/
private theorem numBinary_next {s t : ExecState} {f : Int → Int → Int} (h : numBinary s f = .next t) :
    ∃ rest x1 x2 a b, s.stack = rest ++ [x1, x2] ∧ ScriptNum.decode x1 false = .ok a ∧
      ScriptNum.decode x2 false = .ok b ∧ t.stack = rest ++ [ScriptNum.encode (f a b)] := by
  unfold numBinary at h
  split at h
  · rename_i x2 x1 rest hr
    split at h
    · rename_i a b ha hb
      cases h
      exact ⟨rest.reverse, x1, x2, a, b, by simpa using congrArg List.reverse hr, ha, hb, rfl⟩
    · cases h
  · cases h

/-- A unary numeric step whose function keeps four-byte magnitudes pushes at most four bytes. -/
private theorem numUnary_length_le_four {s t : ExecState} {f : Int → Int}
    (hf : ∀ a : Int, a.natAbs ≤ 2 ^ 31 - 1 → (f a).natAbs ≤ 2 ^ 31 - 1) (h : numUnary s f = .next t) :
    ∃ rest y, t.stack = rest ++ [y] ∧ y.length ≤ 4 := by
  obtain ⟨rest, _, a, -, ha, ht⟩ := numUnary_next h
  exact ⟨rest, _, ht, ScriptNum.encode_length_le_four (hf a (ScriptNum.decode_default_natAbs_le ha))⟩

/-- A binary numeric step whose function keeps four-byte magnitudes pushes at most four bytes. -/
private theorem numBinary_length_le_four {s t : ExecState} {f : Int → Int → Int}
    (hf : ∀ a b : Int, a.natAbs ≤ 2 ^ 31 - 1 → b.natAbs ≤ 2 ^ 31 - 1 → (f a b).natAbs ≤ 2 ^ 31 - 1)
    (h : numBinary s f = .next t) : ∃ rest y, t.stack = rest ++ [y] ∧ y.length ≤ 4 := by
  obtain ⟨rest, _, _, a, b, -, ha, hb, ht⟩ := numBinary_next h
  exact ⟨rest, _, ht, ScriptNum.encode_length_le_four
    (hf a b (ScriptNum.decode_default_natAbs_le ha) (ScriptNum.decode_default_natAbs_le hb))⟩

/--
`OP_1ADD`, `OP_1SUB`, `OP_ADD` and `OP_SUB` succeed only by pushing one item of at most five bytes onto the remaining stack.
The bound follows from the four-byte operands: each lies within ±(2^31 − 1).
-/
theorem execOpcode_addSub_length {flags : UInt32} {fExec : Bool} {s t : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (hop : op = 0x8b ∨ op = 0x8c ∨ op = 0x93 ∨ op = 0x94)
    (h : execOpcode flags fExec s op pushed next = .next t) :
    ∃ rest y, t.stack = rest ++ [y] ∧ y.length ≤ 5 := by
  rcases hop with rfl | rfl | rfl | rfl <;> simp (config := { decide := true }) only [execOpcode, ↓reduceIte] at h
  · obtain ⟨rest, _, a, -, ha, ht⟩ := numUnary_next h
    exact ⟨rest, _, ht, ScriptNum.encode_add_length_le_five (ScriptNum.decode_default_natAbs_le ha) (by decide)⟩
  · obtain ⟨rest, _, a, -, ha, ht⟩ := numUnary_next h
    exact ⟨rest, _, ht, ScriptNum.encode_sub_length_le_five (ScriptNum.decode_default_natAbs_le ha) (by decide)⟩
  · obtain ⟨rest, _, _, a, b, -, ha, hb, ht⟩ := numBinary_next h
    exact ⟨rest, _, ht, ScriptNum.encode_add_length_le_five (ScriptNum.decode_default_natAbs_le ha)
      (ScriptNum.decode_default_natAbs_le hb)⟩
  · obtain ⟨rest, _, _, a, b, -, ha, hb, ht⟩ := numBinary_next h
    exact ⟨rest, _, ht, ScriptNum.encode_sub_length_le_five (ScriptNum.decode_default_natAbs_le ha)
      (ScriptNum.decode_default_natAbs_le hb)⟩

/--
The other numeric opcodes, except `OP_NUMEQUALVERIFY`, succeed only by pushing one item of at most four bytes onto the remaining stack.
`OP_NEGATE`, `OP_ABS`, `OP_MIN` and `OP_MAX` keep the magnitude of an operand, and the others push `[1]` or `[]`.
-/
theorem execOpcode_numeric_length_le_four {flags : UInt32} {fExec : Bool} {s t : ExecState} {op : UInt8} {k : Nat}
    {pushed : List UInt8} {next : Nat} (hop : (op, k) ∈ numericArity) (hne : op ∉ [0x8b, 0x8c, 0x93, 0x94, 0x9d])
    (h : execOpcode flags fExec s op pushed next = .next t) :
    ∃ rest y, t.stack = rest ++ [y] ∧ y.length ≤ 4 := by
  simp only [numericArity, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at hop
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (try (exfalso; exact hne (by decide))) <;> simp (config := { decide := true }) only [execOpcode, ↓reduceIte] at h
  all_goals first
    | exact numUnary_length_le_four
        (fun a ha => by (try simp only [ofBool]); (try dsimp only); (repeat' split) <;> omega) h
    | exact numBinary_length_le_four
        (fun a b ha hb => by (try simp only [ofBool]); (try dsimp only); (repeat' split) <;> omega) h
    | skip
  -- `OP_WITHIN`.
  split at h
  · split at h
    · cases h
      exact ⟨_, _, rfl, by simp only [boolBytes]; split <;> simp⟩
    · cases h
  · cases h

/-! ## Core's operator asserts -/

/--
`OP_NEGATE` and `OP_ABS` apply `CScriptNum::operator-()`, which asserts that the value is not `INT64_MIN` (D24, line 273).
A four-byte operand is never `-2^63`.
-/
theorem numericOperand_ne_int64Min {x : List UInt8} {req : Bool} {a : Int} (ha : ScriptNum.decode x req = .ok a) :
    a ≠ -2 ^ 63 := by
  have := ScriptNum.decode_default_natAbs_le ha
  omega

/--
`OP_1ADD` applies `CScriptNum::operator+=` with 1, which asserts `m_value <= INT64_MAX - 1` (D24, lines 285 and 286).
A four-byte operand satisfies it.
-/
theorem numericOperand_add_one_le {x : List UInt8} {req : Bool} {a : Int} (ha : ScriptNum.decode x req = .ok a) :
    a ≤ (2 ^ 63 - 1) - 1 := by
  have := ScriptNum.decode_default_natAbs_le ha
  omega

/--
`OP_1SUB` applies `CScriptNum::operator-=` with 1, which asserts `m_value >= INT64_MIN + 1` (D24, lines 293 and 294).
A four-byte operand satisfies it.
-/
theorem numericOperand_sub_one_ge {x : List UInt8} {req : Bool} {a : Int} (ha : ScriptNum.decode x req = .ok a) :
    -2 ^ 63 + 1 ≤ a := by
  have := ScriptNum.decode_default_natAbs_le ha
  omega

/--
`OP_ADD` and `OP_SUB` compute `m_value + rhs` and `m_value - rhs` in `int64_t` (D24, lines 258 and 259), without an assert.
For four-byte operands both results lie within `[-2^63, 2^63 - 1]`, so neither overflows.
-/
theorem numericOperand_addSub_mem {x y : List UInt8} {req : Bool} {a b : Int}
    (ha : ScriptNum.decode x req = .ok a) (hb : ScriptNum.decode y req = .ok b) :
    (-2 ^ 63 ≤ a + b ∧ a + b ≤ 2 ^ 63 - 1) ∧ (-2 ^ 63 ≤ a - b ∧ a - b ≤ 2 ^ 63 - 1) := by
  have := ScriptNum.decode_default_natAbs_le ha
  have := ScriptNum.decode_default_natAbs_le hb
  omega

/-! ## Unsupported opcodes -/

/-- An executed signature opcode, `0xac` to `0xaf`, is unsupported. -/
theorem execOpcode_signature {flags : UInt32} {fExec : Bool} {s : ExecState} {op : UInt8}
    {pushed : List UInt8} {next : Nat} (hop : isSignatureOpcode op = true) :
    execOpcode flags fExec s op pushed next = .unsupported (.signatureOpcode op) := by
  have h : op ∈ [0xac, 0xad, 0xae, 0xaf] :=
    allBytes (fun op => isSignatureOpcode op = true → op ∈ [0xac, 0xad, 0xae, 0xaf]) (by decide +kernel) op hop
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h <;> subst h <;>
    simp [execOpcode, isSignatureOpcode]

end DogeLib.Script
