module

/-!
# `Script.Flags`

The verification flags of the Script interpreter, and the flags that DogeLib supports.

Core passes the flags to `EvalScript` and `VerifyScript` as an `unsigned int` bit set.
The bits are in `src/script/interpreter.h` lines 30 to 108 of Dogecoin Core `v1.14.9` (SOURCES.md, D25).
Here a flag set is a `UInt32`, and each constant has one bit set.

Design record 0003 (section 3) selects seven flags for the legacy spend milestone:
`P2SH`, `STRICTENC`, `DERSIG`, `LOW_S`, `NULLDUMMY`, `CHECKLOCKTIMEVERIFY` and `CHECKSEQUENCEVERIFY`.
`supportedFlags` holds exactly those bits.
A flag set with any other bit is unsupported, and the evaluator reports that before it runs.
-/

@[expose] public section

namespace DogeLib.Script

namespace ScriptFlags

/-- `SCRIPT_VERIFY_P2SH`, bit 0. -/
def p2sh : UInt32 := 0x0001
/-- `SCRIPT_VERIFY_STRICTENC`, bit 1. -/
def strictEnc : UInt32 := 0x0002
/-- `SCRIPT_VERIFY_DERSIG`, bit 2. -/
def derSig : UInt32 := 0x0004
/-- `SCRIPT_VERIFY_LOW_S`, bit 3. -/
def lowS : UInt32 := 0x0008
/-- `SCRIPT_VERIFY_NULLDUMMY`, bit 4. -/
def nullDummy : UInt32 := 0x0010
/-- `SCRIPT_VERIFY_SIGPUSHONLY`, bit 5. -/
def sigPushOnly : UInt32 := 0x0020
/-- `SCRIPT_VERIFY_MINIMALDATA`, bit 6. -/
def minimalData : UInt32 := 0x0040
/-- `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS`, bit 7. -/
def discourageUpgradableNops : UInt32 := 0x0080
/-- `SCRIPT_VERIFY_CLEANSTACK`, bit 8. -/
def cleanStack : UInt32 := 0x0100
/-- `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY`, bit 9. -/
def checkLockTimeVerify : UInt32 := 0x0200
/-- `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`, bit 10. -/
def checkSequenceVerify : UInt32 := 0x0400
/-- `SCRIPT_VERIFY_WITNESS`, bit 11. -/
def witness : UInt32 := 0x0800
/-- `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_WITNESS_PROGRAM`, bit 12. -/
def discourageUpgradableWitnessProgram : UInt32 := 0x1000
/-- `SCRIPT_VERIFY_MINIMALIF`, bit 13. -/
def minimalIf : UInt32 := 0x2000
/-- `SCRIPT_VERIFY_NULLFAIL`, bit 14. -/
def nullFail : UInt32 := 0x4000
/-- `SCRIPT_VERIFY_WITNESS_PUBKEYTYPE`, bit 15. -/
def witnessPubkeyType : UInt32 := 0x8000

end ScriptFlags

/-- The seven flags of design record 0003: bits 0 to 4, 9 and 10. -/
def supportedFlags : UInt32 :=
  ScriptFlags.p2sh ||| ScriptFlags.strictEnc ||| ScriptFlags.derSig ||| ScriptFlags.lowS |||
    ScriptFlags.nullDummy ||| ScriptFlags.checkLockTimeVerify ||| ScriptFlags.checkSequenceVerify

/-- The bits of `flags` outside `supportedFlags`. -/
def unsupportedFlagBits (flags : UInt32) : UInt32 := flags &&& ~~~supportedFlags

/-- Whether `flags` has the bit of `flag`. -/
def hasFlag (flags flag : UInt32) : Bool := flags &&& flag != 0

end DogeLib.Script
