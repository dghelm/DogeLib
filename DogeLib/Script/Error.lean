module

/-!
# `Script.Error`

The errors of the Script interpreter: Core's `ScriptError_t`.

The enum is in `src/script/script_error.h` lines 9 to 68 of Dogecoin Core `v1.14.9` (SOURCES.md, D49).
`ScriptError` has one constructor for each enumerator, in Core's order, with two exceptions:

- `SCRIPT_ERR_OK` is not an error. A successful call is a separate result, so no rejection can carry it.
- `SCRIPT_ERR_ERROR_COUNT` is the number of enumerators, not an error.

`ScriptError.code` gives Core's enumerator value, from 1 to 40.
No error has the code 0, which is `SCRIPT_ERR_OK`.
`ScriptError.name` gives the name that Core's script tests use for the error (D46, lines 60 to 100).
That name is the enumerator without its `SCRIPT_ERR_` prefix, except for `SCRIPT_ERR_SIG_NULLFAIL`, whose name is `NULLFAIL`.
-/

@[expose] public section

namespace DogeLib.Script

/-- Core's `ScriptError_t` (D49, lines 9 to 68), without `SCRIPT_ERR_OK` and the count `SCRIPT_ERR_ERROR_COUNT`. -/
inductive ScriptError where
  /-- `SCRIPT_ERR_UNKNOWN_ERROR`. -/
  | unknownError
  /-- `SCRIPT_ERR_EVAL_FALSE`. -/
  | evalFalse
  /-- `SCRIPT_ERR_OP_RETURN`. -/
  | opReturn
  /-- `SCRIPT_ERR_SCRIPT_SIZE`. -/
  | scriptSize
  /-- `SCRIPT_ERR_PUSH_SIZE`. -/
  | pushSize
  /-- `SCRIPT_ERR_OP_COUNT`. -/
  | opCount
  /-- `SCRIPT_ERR_STACK_SIZE`. -/
  | stackSize
  /-- `SCRIPT_ERR_SIG_COUNT`. -/
  | sigCount
  /-- `SCRIPT_ERR_PUBKEY_COUNT`. -/
  | pubkeyCount
  /-- `SCRIPT_ERR_VERIFY`. -/
  | verify
  /-- `SCRIPT_ERR_EQUALVERIFY`. -/
  | equalVerify
  /-- `SCRIPT_ERR_CHECKMULTISIGVERIFY`. -/
  | checkMultisigVerify
  /-- `SCRIPT_ERR_CHECKSIGVERIFY`. -/
  | checkSigVerify
  /-- `SCRIPT_ERR_NUMEQUALVERIFY`. -/
  | numEqualVerify
  /-- `SCRIPT_ERR_BAD_OPCODE`. -/
  | badOpcode
  /-- `SCRIPT_ERR_DISABLED_OPCODE`. -/
  | disabledOpcode
  /-- `SCRIPT_ERR_INVALID_STACK_OPERATION`. -/
  | invalidStackOperation
  /-- `SCRIPT_ERR_INVALID_ALTSTACK_OPERATION`. -/
  | invalidAltstackOperation
  /-- `SCRIPT_ERR_UNBALANCED_CONDITIONAL`. -/
  | unbalancedConditional
  /-- `SCRIPT_ERR_NEGATIVE_LOCKTIME`. -/
  | negativeLocktime
  /-- `SCRIPT_ERR_UNSATISFIED_LOCKTIME`. -/
  | unsatisfiedLocktime
  /-- `SCRIPT_ERR_SIG_HASHTYPE`. -/
  | sigHashtype
  /-- `SCRIPT_ERR_SIG_DER`. -/
  | sigDer
  /-- `SCRIPT_ERR_MINIMALDATA`. -/
  | minimalData
  /-- `SCRIPT_ERR_SIG_PUSHONLY`. -/
  | sigPushOnly
  /-- `SCRIPT_ERR_SIG_HIGH_S`. -/
  | sigHighS
  /-- `SCRIPT_ERR_SIG_NULLDUMMY`. -/
  | sigNullDummy
  /-- `SCRIPT_ERR_PUBKEYTYPE`. -/
  | pubkeyType
  /-- `SCRIPT_ERR_CLEANSTACK`. -/
  | cleanStack
  /-- `SCRIPT_ERR_MINIMALIF`. -/
  | minimalIf
  /-- `SCRIPT_ERR_SIG_NULLFAIL`. -/
  | sigNullFail
  /-- `SCRIPT_ERR_DISCOURAGE_UPGRADABLE_NOPS`. -/
  | discourageUpgradableNops
  /-- `SCRIPT_ERR_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM`. -/
  | discourageUpgradableWitnessProgram
  /-- `SCRIPT_ERR_WITNESS_PROGRAM_WRONG_LENGTH`. -/
  | witnessProgramWrongLength
  /-- `SCRIPT_ERR_WITNESS_PROGRAM_WITNESS_EMPTY`. -/
  | witnessProgramWitnessEmpty
  /-- `SCRIPT_ERR_WITNESS_PROGRAM_MISMATCH`. -/
  | witnessProgramMismatch
  /-- `SCRIPT_ERR_WITNESS_MALLEATED`. -/
  | witnessMalleated
  /-- `SCRIPT_ERR_WITNESS_MALLEATED_P2SH`. -/
  | witnessMalleatedP2SH
  /-- `SCRIPT_ERR_WITNESS_UNEXPECTED`. -/
  | witnessUnexpected
  /-- `SCRIPT_ERR_WITNESS_PUBKEYTYPE`. -/
  | witnessPubkeyType
  deriving DecidableEq, Repr

namespace ScriptError

/-- Every error, in Core's order. -/
def all : List ScriptError :=
  [unknownError, evalFalse, opReturn, scriptSize, pushSize, opCount, stackSize, sigCount, pubkeyCount,
    verify, equalVerify, checkMultisigVerify, checkSigVerify, numEqualVerify,
    badOpcode, disabledOpcode, invalidStackOperation, invalidAltstackOperation, unbalancedConditional,
    negativeLocktime, unsatisfiedLocktime,
    sigHashtype, sigDer, minimalData, sigPushOnly, sigHighS, sigNullDummy, pubkeyType, cleanStack, minimalIf,
    sigNullFail,
    discourageUpgradableNops, discourageUpgradableWitnessProgram,
    witnessProgramWrongLength, witnessProgramWitnessEmpty, witnessProgramMismatch, witnessMalleated,
    witnessMalleatedP2SH, witnessUnexpected, witnessPubkeyType]

/-- Core's enumerator value (D49): `SCRIPT_ERR_UNKNOWN_ERROR` is 1, and each later enumerator is one more. -/
def code (e : ScriptError) : Nat := e.ctorIdx + 1

/-- The name that Core's script tests use for the error (D46, lines 60 to 100). -/
def name : ScriptError → String
  | unknownError => "UNKNOWN_ERROR"
  | evalFalse => "EVAL_FALSE"
  | opReturn => "OP_RETURN"
  | scriptSize => "SCRIPT_SIZE"
  | pushSize => "PUSH_SIZE"
  | opCount => "OP_COUNT"
  | stackSize => "STACK_SIZE"
  | sigCount => "SIG_COUNT"
  | pubkeyCount => "PUBKEY_COUNT"
  | verify => "VERIFY"
  | equalVerify => "EQUALVERIFY"
  | checkMultisigVerify => "CHECKMULTISIGVERIFY"
  | checkSigVerify => "CHECKSIGVERIFY"
  | numEqualVerify => "NUMEQUALVERIFY"
  | badOpcode => "BAD_OPCODE"
  | disabledOpcode => "DISABLED_OPCODE"
  | invalidStackOperation => "INVALID_STACK_OPERATION"
  | invalidAltstackOperation => "INVALID_ALTSTACK_OPERATION"
  | unbalancedConditional => "UNBALANCED_CONDITIONAL"
  | negativeLocktime => "NEGATIVE_LOCKTIME"
  | unsatisfiedLocktime => "UNSATISFIED_LOCKTIME"
  | sigHashtype => "SIG_HASHTYPE"
  | sigDer => "SIG_DER"
  | minimalData => "MINIMALDATA"
  | sigPushOnly => "SIG_PUSHONLY"
  | sigHighS => "SIG_HIGH_S"
  | sigNullDummy => "SIG_NULLDUMMY"
  | pubkeyType => "PUBKEYTYPE"
  | cleanStack => "CLEANSTACK"
  | minimalIf => "MINIMALIF"
  | sigNullFail => "NULLFAIL"
  | discourageUpgradableNops => "DISCOURAGE_UPGRADABLE_NOPS"
  | discourageUpgradableWitnessProgram => "DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM"
  | witnessProgramWrongLength => "WITNESS_PROGRAM_WRONG_LENGTH"
  | witnessProgramWitnessEmpty => "WITNESS_PROGRAM_WITNESS_EMPTY"
  | witnessProgramMismatch => "WITNESS_PROGRAM_MISMATCH"
  | witnessMalleated => "WITNESS_MALLEATED"
  | witnessMalleatedP2SH => "WITNESS_MALLEATED_P2SH"
  | witnessUnexpected => "WITNESS_UNEXPECTED"
  | witnessPubkeyType => "WITNESS_PUBKEYTYPE"

end ScriptError

end DogeLib.Script
