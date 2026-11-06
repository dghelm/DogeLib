module

public import DogeLib.Script.Error
public import DogeLib.Script.Eval
public import DogeLib.Script.Flags
public import DogeLib.Script.Instruction
public import DogeLib.Script.Number
public import DogeLib.Script.Signature
public import DogeLib.Script.SignatureCode
public import DogeLib.Script.SignatureEncoding
public import DogeLib.Script.State

/-!
# `DogeLib.Script`

Script: the instruction reader of the interpreter, the state of one `EvalScript` call, Script numbers and the truth value of a stack item.
It also holds the interpreter's errors and flags, and one `EvalScript` call for the opcodes of stages 2 and 3, including the numeric, hash and signature opcodes.
`SignatureCode` prepares legacy script code with exact vector pushes and signature deletion.
`SignatureEncoding` holds the encoding checks of signatures and public keys, which the signature opcodes run.
`Signature` holds the signature checker that the evaluator takes as a parameter, with Core's two checkers, and the matching loop of `OP_CHECKMULTISIG`.
No definition here returns a verdict on a spend: `VerifyScript` is not specified yet.
-/
