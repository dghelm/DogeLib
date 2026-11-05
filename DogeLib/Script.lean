module

public import DogeLib.Script.Instruction
public import DogeLib.Script.State

/-!
# `DogeLib.Script`

Script: the instruction reader of the interpreter, and the state of one `EvalScript` call.
Opcode semantics are not specified yet, so no definition here executes an opcode or returns a verdict on a spend.
-/
