module

public import DogeLib.Script.State

/-! Reset and bounds for per-call Script state. -/

public section

namespace DogeLib.Script

/-- Initialization keeps every supplied main stack and resets all local fields. -/
theorem initialState_fields (stack : Stack) :
    (initialState stack).stack = stack ∧ (initialState stack).altstack = [] ∧
    (initialState stack).pc = 0 ∧ (initialState stack).codeSeparator = 0 ∧
    (initialState stack).vfExec = [] ∧ (initialState stack).nOpCount = 0 := by
  simp [initialState]

/-- Handoff keeps only the main stack, for every prior state. -/
theorem handoff_fields (state : ExecutionState) :
    (handoff state).stack = state.stack ∧ (handoff state).altstack = [] ∧
    (handoff state).pc = 0 ∧ (handoff state).codeSeparator = 0 ∧
    (handoff state).vfExec = [] ∧ (handoff state).nOpCount = 0 :=
  initialState_fields state.stack

/-- Every initial state satisfies the cursor invariant for every script. -/
theorem initialState_cursor (script : List UInt8) (stack : Stack) :
    CursorInvariant script (initialState stack) := by
  simp [CursorInvariant, initialState]

/-- Initial resources are bounded when the script and supplied stack meet their stated bounds. -/
theorem initialState_resources (script : List UInt8) (stack : Stack)
    (hs : script.length ≤ maxScriptSize) (hc : stack.length ≤ maxStackSize)
    (hi : ∀ item ∈ stack, item.length ≤ maxScriptElementSize) :
    ResourceInvariant script (initialState stack) := by
  simpa [ResourceInvariant, initialState, maxOpsPerScript] using And.intro hs (And.intro hc hi)

/-- Handoff satisfies the cursor invariant relative to every next script. -/
theorem handoff_cursor (script : List UInt8) (state : ExecutionState) :
    CursorInvariant script (handoff state) := initialState_cursor script state.stack

end DogeLib.Script
