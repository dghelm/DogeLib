module

public import DogeLib.Script.Error
public import DogeLib.Script.Eval
public import DogeLib.Script.Flags
public import DogeLib.Script.Instruction
public import DogeLib.Script.Number
public import DogeLib.Script.State

/-!
# `DogeLib.Script`

Script: the instruction reader of the interpreter, the state of one `EvalScript` call, Script numbers and the truth value of a stack item.
It also holds the interpreter's errors and flags, and one `EvalScript` call for the opcodes of stage 2 that do not compute numbers or hashes.
No definition here returns a verdict on a spend: `VerifyScript` is not specified yet.
-/
