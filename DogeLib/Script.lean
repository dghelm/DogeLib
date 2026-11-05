module

public import DogeLib.Script.Instruction
public import DogeLib.Script.Number
public import DogeLib.Script.State

/-!
# `DogeLib.Script`

Script: the instruction reader of the interpreter, the state of one `EvalScript` call, Script numbers and the truth value of a stack item.
Opcode semantics are not specified yet, so no definition here executes an opcode or returns a verdict on a spend.
-/
