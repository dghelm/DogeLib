module

public import DogeLib.Script.CoreVerifier
public import DogeLib.Script.Error
public import DogeLib.Script.Eval
public import DogeLib.Script.Flags
public import DogeLib.Script.Instruction
public import DogeLib.Script.MultisigRecovery
public import DogeLib.Script.Number
public import DogeLib.Script.Signature
public import DogeLib.Script.SignatureCode
public import DogeLib.Script.SignatureEncoding
public import DogeLib.Script.State
public import DogeLib.Script.Verify

/-!
# `DogeLib.Script`

Script: the instruction reader of the interpreter, the state of one `EvalScript` call, Script numbers and the truth value of a stack item.
It also holds the interpreter's errors and flags, and one `EvalScript` call for the opcodes of stages 2 to 4, including the numeric, hash, signature and lock-time opcodes.
`SignatureCode` prepares legacy script code with exact vector pushes and signature deletion.
`SignatureEncoding` holds the encoding checks of signatures and public keys, which the signature opcodes run.
`Signature` holds the signature checker that the evaluator takes as a parameter, with Core's two checkers, and the matching loop of `OP_CHECKMULTISIG`.
`Verify` holds `VerifyScript` without a witness, with the P2SH branch, and the spend predicate of one legacy input.
-/
