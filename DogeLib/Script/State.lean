module

public import DogeLib.Script.Instruction

/-!
# `Script.State`

The state of one `EvalScript` call, and the part of it that `VerifyScript` passes from one call to the next.

`EvalScript` is in `src/script/interpreter.cpp` lines 248 to 1046 of Dogecoin Core `v1.14.9` (SOURCES.md, D3).
Its state has six parts:

| DogeLib | Core | Start of a call |
| --- | --- | --- |
| `ExecState.stack` | `stack`, the caller's vector | The caller's stack |
| `ExecState.altstack` | `altstack`, a local | Empty |
| `ExecState.pc` | `pc`, a local iterator | `begin()`, cursor 0 |
| `ExecState.beginCodeHash` | `pbegincodehash`, a local iterator | `begin()`, cursor 0 |
| `ExecState.vfExec` | `vfExec`, a local `vector<bool>` | Empty |
| `ExecState.opCount` | `nOpCount`, a local `int` | 0 |

Core declares the locals at lines 258 to 264, and `nOpCount` at line 268.
The stacks hold raw byte strings, Core's `valtype`, not decoded numbers.
Each list is in the order of Core's vector: the first element is the bottom, and the last element is the top.
A cursor is an offset from `begin()`, as in `DogeLib.Script.Instruction`.

## Reset and hand-off

Every local of `EvalScript` starts again in each call, and only `stack` comes from the caller.
`ExecState.init` is the state at the start of a call.
`VerifyScript` (lines 1409 to 1526) passes one `stack` vector to the call for `scriptSig` and then to the call for `scriptPubKey`, at lines 1424 and 1429.
`ExecState.handOff` is the state at the start of the second call: the main stack of the first call, with every other part reset.
The copy and restore of the stack for Pay to Script Hash (P2SH) are not specified here.

## Invariants

`ExecState.WellFormed` collects the invariants that hold between the instructions of a run of `EvalScript`, until the run fails:

- `pc` is an instruction boundary, because only `GetOp` moves it.
- `beginCodeHash` is an instruction boundary at or before `pc`, because `OP_CODESEPARATOR` sets it to the value of `pc` (line 876).
- `opCount` is at most `MAX_OPS_PER_SCRIPT`, because `EvalScript` fails when `++nOpCount` exceeds it (lines 286 and 287).
- `vfExec` has at most `opCount` entries, because only `OP_IF` and `OP_NOTIF` add an entry, and both opcodes are above `OP_16`, so both count.

`ExecState.WithinStackLimit` is Core's combined stack limit.
`EvalScript` checks it after each instruction (line 1033), not on the stack that the caller passes, so it is separate from `WellFormed`.

The opcode semantics are in `DogeLib.Script.Eval`.
`DogeLib.Script.Proofs.State` proves the invariants for the start of a call and for the hand-off.
It also proves them for the move of the cursor past one instruction and for the mark of a code separator.
`DogeLib.Script.Proofs.Eval` proves that each successful step of the evaluator preserves them (`evalInstruction_wellFormed`).
-/

@[expose] public section

namespace DogeLib.Script

/-- `MAX_OPS_PER_SCRIPT`, the largest number of counted opcodes in one `EvalScript` call (D24, `src/script/script.h` line 25). -/
def maxOpsPerScript : Nat := 201

/--
The largest number of items on the main stack and the altstack together.
Core has no named constant for it at the reference software revision: the value is the literal of `stack.size() + altstack.size() > 1000` (D3, line 1033).
-/
def maxStackItems : Nat := 1000

/-- The state of one `EvalScript` call (D3, lines 258 to 268). Stacks list their items from the bottom to the top. -/
structure ExecState where
  /-- The main stack, `stack`: the caller's vector. -/
  stack : List (List UInt8)
  /-- The alternative stack, `altstack`. -/
  altstack : List (List UInt8)
  /-- The program cursor `pc`, as an offset from `begin()`. -/
  pc : Nat
  /-- The cursor after the last executed `OP_CODESEPARATOR`, `pbegincodehash`, as an offset from `begin()`. -/
  beginCodeHash : Nat
  /-- The conditional stack `vfExec`, from the outermost `OP_IF` or `OP_NOTIF` to the innermost. -/
  vfExec : List Bool
  /-- The number of counted opcodes, `nOpCount`. -/
  opCount : Nat
  deriving DecidableEq, Repr

/-- `fExec` (D3, line 275): whether the current branch executes, that is, no entry of `vfExec` is false. -/
def ExecState.fExec (s : ExecState) : Bool := !s.vfExec.contains false

/-- The state at the start of `EvalScript` (D3, lines 258 to 268): the caller's main stack, and every local reset. -/
def ExecState.init (stack : List (List UInt8)) : ExecState :=
  { stack, altstack := [], pc := 0, beginCodeHash := 0, vfExec := [], opCount := 0 }

/-- The state at the start of the next `EvalScript` call of `VerifyScript` (D3, lines 1424 to 1429): only the main stack passes. -/
def ExecState.handOff (s : ExecState) : ExecState := ExecState.init s.stack

/--
The invariants between the instructions of a run of `EvalScript` on `script`, until the run fails.
`DogeLib.Script.Proofs.State` proves them for the start of a call and for the cursor and separator updates.
`evalInstruction_wellFormed` in `DogeLib.Script.Proofs.Eval` shows that each successful step of the evaluator preserves them.
-/
structure ExecState.WellFormed (script : List UInt8) (s : ExecState) : Prop where
  /-- The cursor is an instruction boundary. -/
  pc_boundary : IsBoundary script s.pc
  /-- The cursor after the last executed code separator is an instruction boundary. -/
  beginCodeHash_boundary : IsBoundary script s.beginCodeHash
  /-- The cursor after the last executed code separator is at or before the cursor. -/
  beginCodeHash_le_pc : s.beginCodeHash ≤ s.pc
  /-- The opcode count is at most `MAX_OPS_PER_SCRIPT`. -/
  opCount_le : s.opCount ≤ maxOpsPerScript
  /-- The conditional-stack length is at most the opcode count. -/
  vfExec_length_le : s.vfExec.length ≤ s.opCount

/-- Core's combined stack limit (D3, line 1033): at most 1,000 items on the main stack and the altstack together. -/
def ExecState.WithinStackLimit (s : ExecState) : Prop :=
  s.stack.length + s.altstack.length ≤ maxStackItems

end DogeLib.Script
