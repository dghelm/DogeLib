module

public import DogeLib.Script.Instruction

/-!
# Per-call Script state

The fields and reset follow Core's `EvalScript` and `VerifyScript` (SOURCES.md, D3).
These definitions expose state, without executing an opcode or deciding a spend.
-/

@[expose] public section

namespace DogeLib.Script

/-- A stack of raw byte strings, with its top at the end, as in Core's vectors. -/
abbrev Stack := List (List UInt8)

/-- The per-call fields of `EvalScript`.
The caller supplies the script separately. -/
structure ExecutionState where
  /-- The main stack shared between successive evaluations. -/
  stack : Stack
  /-- The alternate stack local to one evaluation. -/
  altstack : Stack
  /-- The next byte offset to read. -/
  pc : Nat
  /-- The byte offset after the last executed separator, or zero before any separator. -/
  codeSeparator : Nat
  /-- Conditional execution entries, with the innermost entry at the end. -/
  vfExec : List Bool
  /-- The operation count local to one evaluation. -/
  nOpCount : Nat
  deriving BEq, Repr

/-- Begin an evaluation with the supplied main stack and reset every local field. -/
def initialState (stack : Stack) : ExecutionState :=
  ⟨stack, [], 0, 0, [], 0⟩

/-- Transfer only the main stack to another evaluation, as between `scriptSig` and `scriptPubKey`.
This operation assumes no evaluation result and makes no spend claim. -/
def handoff (state : ExecutionState) : ExecutionState := initialState state.stack

/-- Cursor bounds for a state relative to its supplied script. -/
def CursorInvariant (script : List UInt8) (state : ExecutionState) : Prop :=
  state.codeSeparator ≤ state.pc ∧ state.pc ≤ script.length

/-- Core's maximum script length in bytes (D24, `script.h` lines 32 to 33). -/
def maxScriptSize : Nat := 10000

/-- Core's maximum pushed element length (D24, `script.h` lines 23 to 24). -/
def maxScriptElementSize : Nat := 520

/-- Core's maximum operation count per evaluation (D24, `script.h` lines 26 to 27). -/
def maxOpsPerScript : Nat := 201

/-- Core's combined stack-item bound (D3, `EvalScript`, lines 1033 to 1035). -/
def maxStackSize : Nat := 1000

/-- Resource bounds for a state reachable from bounded pushes.
This predicate is not a precondition of `initialState` or a claim about arbitrary caller-supplied stacks.
Stage 1 proves no preservation under opcode execution. -/
def ResourceInvariant (script : List UInt8) (state : ExecutionState) : Prop :=
  script.length ≤ maxScriptSize ∧
  state.nOpCount ≤ maxOpsPerScript ∧
  state.stack.length + state.altstack.length ≤ maxStackSize ∧
  ∀ item ∈ state.stack ++ state.altstack, item.length ≤ maxScriptElementSize

/-- Execution capabilities absent from this stage. -/
inductive UnsupportedFeature where
  /-- Opcode execution has no implementation. -/
  | execution
  deriving BEq, Repr

end DogeLib.Script
