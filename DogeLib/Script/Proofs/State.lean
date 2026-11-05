module

public import DogeLib.Script.Proofs.Instruction
public import DogeLib.Script.State

/-!
# Proofs: `Script.State`

- `init_wellFormed`: the state at the start of an `EvalScript` call satisfies the invariants for every script and every caller stack.
- `init_fExec`: the branch at the start of a call executes.
- `handOff_stack`, `handOff_altstack`, `handOff_pc`, `handOff_beginCodeHash`, `handOff_vfExec`, `handOff_opCount`: the next call receives the main stack, and every other part is reset.
- `handOff_eq_iff`: two states hand off the same start state if and only if their main stacks are equal.
- `handOff_wellFormed` and `WithinStackLimit.handOff`: the hand-off satisfies the invariants for every next script, and keeps the combined stack limit.
- `WellFormed.advance` and `WellFormed.markSeparator`: moving the cursor past an instruction that the reader reads, and setting the separator cursor to the cursor, keep the invariants.
- `WellFormed.pc_le_length` and `WellFormed.beginCodeHash_le_length`: both cursors stay within the script.

These theorems are statements about the definitions. They do not say that the definitions match Core.
`DogeLib.Script.Proofs.Eval` shows that each successful step of the evaluator keeps the invariants.
-/

@[expose] public section

namespace DogeLib.Script

/-! ## The start of a call -/

/-- For every script and every caller stack, the state at the start of `EvalScript` satisfies `ExecState.WellFormed`. -/
theorem init_wellFormed (script : List UInt8) (stack : List (List UInt8)) :
    (ExecState.init stack).WellFormed script where
  pc_boundary := .start
  beginCodeHash_boundary := .start
  beginCodeHash_le_pc := Nat.le_refl _
  opCount_le := by simp [ExecState.init, maxOpsPerScript]
  vfExec_length_le := Nat.le_refl _

/-- For every caller stack, the branch at the start of `EvalScript` executes: `vfExec` is empty. -/
theorem init_fExec (stack : List (List UInt8)) : (ExecState.init stack).fExec = true := rfl

/-! ## The hand-off of `VerifyScript` -/

/-- For every state, the next call starts with its main stack. -/
@[simp] theorem handOff_stack (s : ExecState) : s.handOff.stack = s.stack := rfl

/-- For every state, the next call starts with an empty altstack. -/
@[simp] theorem handOff_altstack (s : ExecState) : s.handOff.altstack = [] := rfl

/-- For every state, the next call starts at cursor 0. -/
@[simp] theorem handOff_pc (s : ExecState) : s.handOff.pc = 0 := rfl

/-- For every state, the next call starts with the separator cursor at 0. -/
@[simp] theorem handOff_beginCodeHash (s : ExecState) : s.handOff.beginCodeHash = 0 := rfl

/-- For every state, the next call starts with an empty conditional stack. -/
@[simp] theorem handOff_vfExec (s : ExecState) : s.handOff.vfExec = [] := rfl

/-- For every state, the next call starts with an opcode count of 0. -/
@[simp] theorem handOff_opCount (s : ExecState) : s.handOff.opCount = 0 := rfl

/--
For all states `s` and `t`: they hand off the same start state if and only if their main stacks are equal.
So the altstack, cursors, conditional stack and opcode count of one call have no effect on the next call.
-/
theorem handOff_eq_iff (s t : ExecState) : s.handOff = t.handOff ↔ s.stack = t.stack := by
  constructor
  · intro h
    simpa using congrArg ExecState.stack h
  · intro h
    simp [ExecState.handOff, h]

/-- For every state and every next script, the hand-off satisfies `ExecState.WellFormed`. -/
theorem handOff_wellFormed (s : ExecState) (script : List UInt8) : s.handOff.WellFormed script :=
  init_wellFormed script s.stack

/-- For every state within the combined stack limit, the hand-off is within it: the next call drops the altstack and keeps the main stack. -/
theorem ExecState.WithinStackLimit.handOff {s : ExecState} (h : s.WithinStackLimit) :
    s.handOff.WithinStackLimit := by
  unfold ExecState.WithinStackLimit at *
  simp only [handOff_stack, handOff_altstack, List.length_nil]
  omega

/-! ## Cursor and separator updates -/

/--
For every script `script`, state `s` that satisfies `ExecState.WellFormed`, and instruction `i` that `readInstruction` reads at `s.pc`: moving the cursor to `i.next` keeps the invariants.
The move is the cursor update of `GetOp` in the loop of `EvalScript`, with no stack effect.
-/
theorem ExecState.WellFormed.advance {script : List UInt8} {s : ExecState} {i : Instruction}
    (hs : s.WellFormed script) (h : readInstruction script s.pc = .instruction i) :
    ({ s with pc := i.next } : ExecState).WellFormed script where
  pc_boundary := .step hs.pc_boundary h
  beginCodeHash_boundary := hs.beginCodeHash_boundary
  beginCodeHash_le_pc := Nat.le_trans hs.beginCodeHash_le_pc
    (Nat.le_of_lt (readInstruction_consumes h).1)
  opCount_le := hs.opCount_le
  vfExec_length_le := hs.vfExec_length_le

/--
For every script `script` and state `s` that satisfies `ExecState.WellFormed`: setting the separator cursor to the cursor keeps the invariants.
The change is the update `pbegincodehash = pc` of an executed `OP_CODESEPARATOR` (D3, line 876).
-/
theorem ExecState.WellFormed.markSeparator {script : List UInt8} {s : ExecState}
    (hs : s.WellFormed script) :
    ({ s with beginCodeHash := s.pc } : ExecState).WellFormed script where
  pc_boundary := hs.pc_boundary
  beginCodeHash_boundary := hs.pc_boundary
  beginCodeHash_le_pc := Nat.le_refl _
  opCount_le := hs.opCount_le
  vfExec_length_le := hs.vfExec_length_le

/-- For every script and state that satisfies `ExecState.WellFormed`, the cursor is at most the length of the script. -/
theorem ExecState.WellFormed.pc_le_length {script : List UInt8} {s : ExecState}
    (hs : s.WellFormed script) : s.pc ≤ script.length :=
  hs.pc_boundary.le_length

/-- For every script and state that satisfies `ExecState.WellFormed`, the separator cursor is at most the length of the script. -/
theorem ExecState.WellFormed.beginCodeHash_le_length {script : List UInt8} {s : ExecState}
    (hs : s.WellFormed script) : s.beginCodeHash ≤ script.length :=
  hs.beginCodeHash_boundary.le_length

end DogeLib.Script
