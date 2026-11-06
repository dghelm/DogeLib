module

public import DogeLib.Cryptography.Hash.Hash160
public import DogeLib.Cryptography.Hash.Ripemd160
public import DogeLib.Cryptography.Hash.Sha1
public import DogeLib.Cryptography.Hash.Sha256
public import DogeLib.Cryptography.Hash.Sha256d
public import DogeLib.Script.Error
public import DogeLib.Script.Flags
public import DogeLib.Script.Number
public import DogeLib.Script.Signature
public import DogeLib.Script.SignatureCode
public import DogeLib.Script.State

/-!
# `Script.Eval`

One call of Core's `EvalScript` in `SIGVERSION_BASE`, for the opcodes of stages 2 to 4: control flow, stack operations, numbers, hashes, signatures and lock times.

`EvalScript` is in `src/script/interpreter.cpp` lines 248 to 1046 of Dogecoin Core `v1.14.9` (SOURCES.md, D3).
Design record 0003, sections 3 and 4, sets the scope of these stages.

## Results

`evalScript checker flags script stack` returns an `EvalResult`, one of three cases:

- `ok s`: Core returns `true` with `SCRIPT_ERR_OK`. `s` is the final state.
- `rejected e`: Core returns `false` with the error `e`.
- `unsupported r`: this stage lacks a capability that the call needs. The reason `r` names it.

An unsupported result says nothing about Core's verdict.
It is never a rejection, and an opcode that this stage lacks never becomes `BAD_OPCODE`.

## Supported flags and capabilities

The evaluator first checks the flags.
A flag set with a bit outside `supportedFlags` is `unsupported (.flags bits)`, before any other check.

Within the supported flags, this stage implements these opcodes:

| Opcodes | Bytes |
| --- | --- |
| Every push, `OP_1NEGATE`, and `OP_1` to `OP_16` | `0x00` to `0x4f`, `0x51` to `0x60` |
| `OP_NOP`, `OP_NOP1`, and `OP_NOP4` to `OP_NOP10` | `0x61`, `0xb0`, `0xb3` to `0xb9` |
| `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` when their flags are clear, or when the call has a checker | `0xb1`, `0xb2` |
| `OP_IF`, `OP_NOTIF`, `OP_ELSE`, `OP_ENDIF`, `OP_VERIFY` and `OP_RETURN` | `0x63`, `0x64`, `0x67` to `0x6a` |
| Every stack operation, from `OP_TOALTSTACK` to `OP_TUCK`, and `OP_SIZE` | `0x6b` to `0x7d`, `0x82` |
| `OP_EQUAL`, `OP_EQUALVERIFY` and `OP_CODESEPARATOR` | `0x87`, `0x88`, `0xab` |
| The numeric opcodes: `OP_1ADD`, `OP_1SUB`, `OP_NEGATE` to `OP_SUB`, and `OP_BOOLAND` to `OP_WITHIN` | `0x8b`, `0x8c`, `0x8f` to `0x94`, `0x9a` to `0xa5` |
| The hash opcodes, `OP_RIPEMD160` to `OP_HASH256` | `0xa6` to `0xaa` |
| `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY`, when the call has a checker | `0xac` to `0xaf` |
| The reserved and invalid opcodes, which give Core's `BAD_OPCODE` when they execute | `0x50`, `0x62`, `0x65`, `0x66`, `0x89`, `0x8a`, `0xba` to `0xff` |

Every opcode has a row in this table, except the disabled opcodes.
Without a checker, an executed signature opcode is unsupported, and so is `OP_CHECKLOCKTIMEVERIFY` or `OP_CHECKSEQUENCEVERIFY` with its flag set.
The disabled opcodes give Core's `DISABLED_OPCODE`, executed or not.

Three flag effects are absent here, because the flags that cause them are unsupported:

- `MINIMALDATA`: `CheckMinimalPush` (lines 307 to 309) and the minimal requirement of `CScriptNum`.
- `DISCOURAGE_UPGRADABLE_NOPS`: the errors of the NOPs (lines 354, 396 and 432).
- `MINIMALIF`: the operand check of `OP_IF` (line 447). It applies only to `SIGVERSION_WITNESS_V0`.
- `NULLFAIL`: the errors of the signature opcodes at lines 904 and 905 and 996 to 998.
  `evalScript` reports a flag set with this bit as unsupported before it runs anything, so these branches are unreachable and absent.

## The checker

The parameter `checker : Option SignatureChecker` is Core's `checker` argument (D3, line 248).

- `some c`: the signature opcodes follow Core, and call `c.checkSig` for each signature check.
  When `c.checkSig` returns `none`, the opcode is `unsupported (.signatureOpcode op)`.
- `none`: the call has no checker. Every executed signature opcode is `unsupported (.signatureOpcode op)` before it reads the stack, as in stage 2.
  Such a result makes no claim about Core's verdict, even for an opcode that Core rejects for stack underflow.

`baseChecker` is Core's `BaseSignatureChecker`, and `transactionChecker` is `TransactionSignatureChecker` (`DogeLib.Script.Signature`).
Every opcode outside `0xac` to `0xaf`, `0xb1` and `0xb2` ignores the checker, and every opcode outside `0xac` to `0xaf` ignores the script (`execOpcode_checker_congr` and `execOpcode_script_congr` in `DogeLib.Script.Proofs.Eval`).

## Lock-time opcodes

With its flag clear, `OP_CHECKLOCKTIMEVERIFY` is `OP_NOP2` and `OP_CHECKSEQUENCEVERIFY` is `OP_NOP3` (lines 352 to 358 and 394 to 400).
With its flag set and a checker `c`, each checks in this order (lines 360 to 427):

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item is a five-byte `CScriptNum` without the minimal requirement, because `MINIMALDATA` is unsupported. A failed decode gives `UNKNOWN_ERROR` through the `catch`.
3. A negative operand gives `NEGATIVE_LOCKTIME`.
4. `OP_CHECKSEQUENCEVERIFY` only: an operand with `SEQUENCE_LOCKTIME_DISABLE_FLAG` set acts as a NOP.
5. `c.checkLockTime` or `c.checkSequence` receives the operand. `false` gives `UNSATISFIED_LOCKTIME`, and `none` gives `unsupported`.

Neither opcode pops its operand.

## Signature opcodes

`OP_CHECKSIG` and `OP_CHECKSIGVERIFY` (lines 880 to 918) check in this order:

1. Fewer than two items give `INVALID_STACK_OPERATION`.
2. The script code is `effectiveScriptCode` from `beginCodeHash` with the signature push removed (lines 891 to 896).
3. `checkSignatureEncoding` and then `checkPubKeyEncoding` (line 898). Their errors come before any checker call.
4. The checker receives the signature, the public key and the script code (line 902).
5. Both items are popped and the result is pushed. `OP_CHECKSIGVERIFY` pops it again, or gives `CHECKSIGVERIFY` (lines 907 to 916).

`OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` (lines 920 to 1026) check in this order:

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item is the key count `n`, a four-byte `CScriptNum` without the minimal requirement. A failed decode gives `UNKNOWN_ERROR` through the `catch`. `n` outside 0 to 20 gives `PUBKEY_COUNT`.
3. The opcode count grows by `n`. Above 201 it gives `OP_COUNT` (lines 932 to 934).
4. Fewer than `n + 2` items give `INVALID_STACK_OPERATION`.
5. The next item is the signature count `m`, decoded the same way. `m` outside 0 to `n` gives `SIG_COUNT`.
6. Fewer than `n + m + 3` items give `INVALID_STACK_OPERATION`. This check already requires the dummy item.
7. The script code is `effectiveScriptCode` with every signature push removed, before the loop (lines 952 to 961).
8. `multisigLoop` matches signatures to keys, with the encoding checks of each visited pair before its checker call (lines 963 to 992).
9. With `NULLDUMMY`, a nonempty dummy gives `SIG_NULLDUMMY`. The dummy is popped in any case (lines 1010 to 1014).
10. The result is pushed. `OP_CHECKMULTISIGVERIFY` pops it again, or gives `CHECKMULTISIGVERIFY`.

Core's second dummy check, `stack.size() < 1` at line 1010, is unreachable after step 6.
The definition keeps it as a labelled branch.

## Numeric opcodes

Each operand is a four-byte `CScriptNum` decode without the minimal requirement, because `MINIMALDATA` is unsupported.
A failed decode throws in Core, and the `catch` at lines 1037 to 1040 gives `UNKNOWN_ERROR`.
Each result is an integer, encoded with `ScriptNum.encode`.
So `OP_ADD`, `OP_SUB`, `OP_1ADD` and `OP_1SUB` can push a five-byte result, which only a later numeric use rejects.
A comparison pushes 1 or 0 as a number, which encodes as `[1]` or `[]`.

Core computes in `int64_t` with the operators of `CScriptNum` (D24, lines 244 to 297).
`OP_1ADD` and `OP_1SUB` use `operator+=` and `operator-=`, whose asserts (lines 285 and 293) require the result to fit `int64_t`.
`OP_NEGATE` and `OP_ABS` use the unary `operator-`, which asserts that the value is not `INT64_MIN` (line 273).
`OP_ADD` and `OP_SUB` use `operator+` and `operator-` (lines 258 and 259), which have no assert, but overflow there would be undefined.
A four-byte operand lies within ±(2^31 − 1), so every result lies within ±2^32.
No assert fires and no operation overflows, and the integer results here equal Core's (`numericOperand_*` in `DogeLib.Script.Proofs.Eval`).

`OP_NUMEQUALVERIFY` pushes the comparison and pops it again when it is true (lines 817 to 823).
The stack check runs only after the instruction, so here the opcode pops both operands when they are equal and gives `NUMEQUALVERIFY` otherwise.

## One instruction

The loop body of lines 273 to 1035 checks one instruction in this order:

1. `GetOp` reads it. A short push is `BAD_OPCODE` (lines 280 and 281).
2. Pushed bytes above 520 give `PUSH_SIZE` (lines 282 and 283).
3. An opcode above `OP_16` counts. A count above 201 gives `OP_COUNT` (lines 286 and 287).
4. A disabled opcode gives `DISABLED_OPCODE` (lines 289 to 304).
5. The opcode runs when `fExec` holds, or when it lies from `OP_IF` to `OP_ENDIF` (lines 306 to 1030).
   In that range, a skipped `OP_IF` or `OP_NOTIF` adds `false` to `vfExec`.
   A skipped `OP_VERIF` or `OP_VERNOTIF` reaches `default`, which gives `BAD_OPCODE`.
6. More than 1,000 items on the two stacks together give `STACK_SIZE` (lines 1033 and 1034).
   This check runs after every instruction, executed or skipped.

Steps 2 to 4 run in a skipped branch too.
A failed numeric decode in `OP_PICK` or `OP_ROLL` throws in Core, and the `catch` at lines 1037 to 1040 gives `UNKNOWN_ERROR`.

`evalInstruction` is steps 2 to 6.
It never reads the cursor `s.pc`.
`OP_CODESEPARATOR` receives the cursor after the instruction, which is Core's `pc` at line 876.
`evalLoop` reads with `readInstruction` and then moves the cursor, as `GetOp` does.
At the end of the script it checks the conditional stack (lines 1042 and 1043).

## Termination

The evaluator takes no fuel.
`evalLoop` recurses on the distance from the cursor to the end of the script, and each instruction moves the cursor forward (`readInstruction_progress`).

## Domain

Core compares the operand of `OP_PICK` and `OP_ROLL` with `(int)stack.size()` (line 657).
Here every size is a `Nat`.
The two agree when the main stack has fewer than 2^31 items.
After the first instruction the two stacks hold at most 1,000 items.
The signature opcodes compare the counts with `(int)stack.size()` (lines 926, 940 and 948), within the same domain.
So only a caller's stack of 2^31 items or more lies outside that domain.

`OP_IF`, `OP_NOTIF`, `OP_VERIFY` and `OP_IFDUP` use `castToBool`, which inherits the boundary of Core's `CastToBool` (D3, line 40).
Core's loop counts with an `unsigned int`, so on an item of more than `UINT_MAX` bytes the counter wraps and the loop can repeat without end.
`castToBool` returns a result for every item, so the evaluator extends Core beyond that domain.
A push holds at most 520 bytes, so such an item can come only from the caller's stack.
Core checks no size of a caller's item, and neither does `evalScript`.

So the correspondence with Core covers a caller's stack of fewer than 2^31 items, each of at most `UINT_MAX` bytes.

`DogeLib.Script.Proofs.Eval` proves the properties of these definitions.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-- `MAX_SCRIPT_SIZE`, the largest script that `EvalScript` runs (D24, `src/script/script.h` line 31). -/
def maxScriptSize : Nat := 10000

/-- `MAX_SCRIPT_ELEMENT_SIZE`, the largest number of bytes that one instruction pushes (D24, line 22). -/
def maxScriptElementSize : Nat := 520

/-- A capability that this stage lacks. An unsupported result is never a Script rejection. -/
inductive Unsupported where
  /-- The flag set has these bits outside `supportedFlags`. The evaluator checks them before anything else. -/
  | flags (bits : UInt32)
  /--
  An executed `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` or `OP_CHECKMULTISIGVERIFY` needed a signature check that is unavailable.
  Either the call has no checker, or the checker returned `none`.
  -/
  | signatureOpcode (opcode : UInt8)
  /--
  An executed `OP_CHECKLOCKTIMEVERIFY` with `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY` set needed a lock-time check that is unavailable.
  Either the call has no checker, or the checker returned `none`.
  -/
  | checkLockTimeVerify
  /--
  An executed `OP_CHECKSEQUENCEVERIFY` with `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` set needed a sequence check that is unavailable.
  Either the call has no checker, or the checker returned `none`.
  -/
  | checkSequenceVerify
  deriving DecidableEq, Repr

/-- The outcome of one instruction. -/
inductive StepResult where
  /-- The instruction succeeded, with this state. The cursor stays at the start of the instruction. -/
  | next (s : ExecState)
  /-- Core returns `false` with this error. -/
  | rejected (error : ScriptError)
  /-- The instruction needs a capability that this stage lacks. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- The outcome of one `EvalScript` call. -/
inductive EvalResult where
  /-- Core returns `true` with `SCRIPT_ERR_OK`. The state is the final state of the call. -/
  | ok (s : ExecState)
  /-- Core returns `false` with this error. -/
  | rejected (error : ScriptError)
  /-- The call needs a capability that this stage lacks. Core's verdict is not determined. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- The disabled opcodes (D3, lines 289 to 304): `OP_CAT` to `OP_RIGHT` (`0x7e` to `0x81`), `OP_INVERT` to `OP_XOR` (`0x83` to `0x86`), `OP_2MUL`, `OP_2DIV` (`0x8d`, `0x8e`) and `OP_MUL` to `OP_RSHIFT` (`0x95` to `0x99`). -/
def isDisabled (op : UInt8) : Bool :=
  (0x7e ≤ op && op ≤ 0x81) || (0x83 ≤ op && op ≤ 0x86) || op == 0x8d || op == 0x8e || (0x95 ≤ op && op ≤ 0x99)

/-- The signature opcodes, `OP_CHECKSIG` to `OP_CHECKMULTISIGVERIFY` (`0xac` to `0xaf`). -/
def isSignatureOpcode (op : UInt8) : Bool := 0xac ≤ op && op ≤ 0xaf

/-- The opcodes that read the checker: the signature opcodes and `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` (`0xb1`, `0xb2`). -/
def readsChecker (op : UInt8) : Bool := isSignatureOpcode op || op == 0xb1 || op == 0xb2

/-- The opcode count after an instruction (D3, line 286): opcodes above `OP_16` (`0x60`) count. -/
def countOp (op : UInt8) (opCount : Nat) : Nat := if 0x60 < op then opCount + 1 else opCount

/-- The bytes that `OP_EQUAL` pushes (D3, lines 254 to 256): `vchTrue`, one byte `0x01`, or `vchFalse`, no bytes. -/
def boolBytes (b : Bool) : List UInt8 := if b then [1] else []

/-- A truth value as a script number, as Core assigns a `bool` to a `CScriptNum` (D3, lines 761, 762 and 800 to 808): 1 or 0. -/
def ofBool (b : Bool) : Int := if b then 1 else 0

/--
The unary numeric opcodes (D3, lines 744 to 768): pop the top item, decode it as a four-byte script number `a`, and push `encode (f a)`.
An empty stack gives `INVALID_STACK_OPERATION`.
A failed decode throws in Core, and the `catch` (lines 1037 to 1040) gives `UNKNOWN_ERROR`.
-/
def numUnary (s : ExecState) (f : Int → Int) : StepResult :=
  match s.stack.reverse with
  | [] => .rejected .invalidStackOperation
  | x :: rest =>
    match ScriptNum.decode x false with
    | .error _ => .rejected .unknownError
    | .ok a => .next { s with stack := rest.reverse ++ [ScriptNum.encode (f a)] }

/--
The binary numeric opcodes other than `OP_NUMEQUALVERIFY` (D3, lines 770 to 825): `x1 x2 → encode (f a b)`, where `x1` decodes as `a` and `x2` as `b`.
Fewer than two items give `INVALID_STACK_OPERATION`, and a failed decode gives `UNKNOWN_ERROR`.
Core decodes `x1` first. Both failures give the same error, so the order is not observable.
-/
def numBinary (s : ExecState) (f : Int → Int → Int) : StepResult :=
  match s.stack.reverse with
  | x2 :: x1 :: rest =>
    match ScriptNum.decode x1 false, ScriptNum.decode x2 false with
    | .ok a, .ok b => .next { s with stack := rest.reverse ++ [ScriptNum.encode (f a b)] }
    | _, _ => .rejected .unknownError
  | _ => .rejected .invalidStackOperation

/-- The hash opcodes (D3, lines 847 to 871): replace the top item `x` by the digest `h x`. An empty stack gives `INVALID_STACK_OPERATION`. -/
def hashTop (s : ExecState) (h : ByteArray → ByteArray) : StepResult :=
  match s.stack.reverse with
  | [] => .rejected .invalidStackOperation
  | x :: rest => .next { s with stack := rest.reverse ++ [(h ⟨x.toArray⟩).toList] }

/-- `MAX_PUBKEYS_PER_MULTISIG`, the largest key count of `OP_CHECKMULTISIG` (D24, `src/script/script.h` line 28). -/
def maxPubKeysPerMultisig : Nat := 20

/--
`OP_CHECKSIG` (`0xac`) and `OP_CHECKSIGVERIFY` (`0xad`) with the checker `c` (D3, lines 880 to 918), on the reversed stack `key :: sig :: rest`.
The encoding checks run in Core's order, signature first, before the checker call (line 898).
The checker receives the script code from `s.beginCodeHash` with the push of `sig` removed (lines 891 to 896).
A checker result of `none` gives `unsupported (.signatureOpcode op)`.
-/
def checkSigStep (c : SignatureChecker) (script : List UInt8) (flags : UInt32) (s : ExecState) (op : UInt8) :
    StepResult :=
  match s.stack.reverse with
  | key :: sig :: rest =>
    match checkSignatureEncoding sig flags with
    | .error e => .rejected e
    | .ok () =>
      match checkPubKeyEncoding key flags with
      | .error e => .rejected e
      | .ok () =>
        match c.checkSig sig key (effectiveScriptCode script s.beginCodeHash [sig]) with
        | none => .unsupported (.signatureOpcode op)
        | some ok =>
          if op = 0xad then
            if ok then .next { s with stack := rest.reverse } else .rejected .checkSigVerify
          else .next { s with stack := rest.reverse ++ [boolBytes ok] }
  | _ => .rejected .invalidStackOperation

/--
One visited pair of the `OP_CHECKMULTISIG` loop (D3, lines 966 to 978): the encoding checks, signature first, and then the checker on the script code `code`.
An encoding error gives `.error (.rejected e)`, and a checker result of `none` gives `.error (.unsupported (.signatureOpcode op))`.
-/
def multisigCheck (c : SignatureChecker) (flags : UInt32) (code : List UInt8) (op : UInt8)
    (sig key : List UInt8) : Except StepResult Bool :=
  match checkSignatureEncoding sig flags with
  | .error e => .error (.rejected e)
  | .ok () =>
    match checkPubKeyEncoding key flags with
    | .error e => .error (.rejected e)
    | .ok () =>
      match c.checkSig sig key code with
      | none => .error (.unsupported (.signatureOpcode op))
      | some ok => .ok ok

/--
`OP_CHECKMULTISIG` (`0xae`) and `OP_CHECKMULTISIGVERIFY` (`0xaf`) with the checker `c` (D3, lines 920 to 1026).
The reversed stack is `nTop :: keys ++ mTop :: sigs ++ dummy :: below`, where `keys` has `n` items and `sigs` has `m`.
Both lists are top first, the order of Core's `stacktop(-ikey)` and `stacktop(-isig)`.
The counts decode without the minimal requirement, because `MINIMALDATA` is unsupported, and a failed decode gives `UNKNOWN_ERROR`.
The result carries the opcode count after Core's `nOpCount += nKeysCount` (line 932).
The module documentation lists the checks in Core's order.
-/
def checkMultisigStep (c : SignatureChecker) (script : List UInt8) (flags : UInt32) (s : ExecState) (op : UInt8) :
    StepResult :=
  match s.stack.reverse with
  | [] => .rejected .invalidStackOperation
  | nTop :: rest =>
    match ScriptNum.decode nTop false with
    | .error _ => .rejected .unknownError
    | .ok nValue =>
      let n := ScriptNum.getint nValue
      if n < 0 ∨ (maxPubKeysPerMultisig : Int) < n then .rejected .pubkeyCount
      else
        let opCount := s.opCount + n.toNat
        if maxOpsPerScript < opCount then .rejected .opCount
        else if rest.length < n.toNat + 1 then .rejected .invalidStackOperation
        else
          let keys := rest.take n.toNat
          match rest.drop n.toNat with
          -- Unreachable after the depth check above.
          | [] => .rejected .invalidStackOperation
          | mTop :: rest' =>
            match ScriptNum.decode mTop false with
            | .error _ => .rejected .unknownError
            | .ok mValue =>
              let m := ScriptNum.getint mValue
              if m < 0 ∨ n < m then .rejected .sigCount
              else if rest'.length < m.toNat + 1 then .rejected .invalidStackOperation
              else
                let sigs := rest'.take m.toNat
                match rest'.drop m.toNat with
                -- Core's `stack.size() < 1` (line 1010), unreachable after the depth check above.
                | [] => .rejected .invalidStackOperation
                | dummy :: below =>
                  let code := effectiveScriptCode script s.beginCodeHash sigs
                  match multisigLoop (multisigCheck c flags code op) sigs keys with
                  | .error r => r
                  | .ok ok =>
                    if hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty then .rejected .sigNullDummy
                    else if op = 0xaf then
                      if ok then .next { s with stack := below.reverse, opCount }
                      else .rejected .checkMultisigVerify
                    else .next { s with stack := below.reverse ++ [boolBytes ok], opCount }

/-- The largest number of bytes in the operand of `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` (D3, lines 377 and 408). -/
def lockTimeNumSize : Nat := 5

/--
`OP_CHECKLOCKTIMEVERIFY` (`0xb1`) with its flag set and the checker `c` (D3, lines 360 to 390).
The operand is the top item, a five-byte script number. The opcode never pops it.
-/
def checkLockTimeStep (c : SignatureChecker) (s : ExecState) : StepResult :=
  match s.stack.reverse with
  | [] => .rejected .invalidStackOperation
  | top :: _ =>
    match ScriptNum.decode top false lockTimeNumSize with
    | .error _ => .rejected .unknownError
    | .ok n =>
      if n < 0 then .rejected .negativeLocktime
      else match c.checkLockTime n with
        | none => .unsupported .checkLockTimeVerify
        | some true => .next s
        | some false => .rejected .unsatisfiedLocktime

/--
`OP_CHECKSEQUENCEVERIFY` (`0xb2`) with its flag set and the checker `c` (D3, lines 402 to 427).
The operand is the top item, a five-byte script number. The opcode never pops it.
An operand with `SEQUENCE_LOCKTIME_DISABLE_FLAG` set acts as a NOP, before any checker call (lines 418 and 419).
-/
def checkSequenceStep (c : SignatureChecker) (s : ExecState) : StepResult :=
  match s.stack.reverse with
  | [] => .rejected .invalidStackOperation
  | top :: _ =>
    match ScriptNum.decode top false lockTimeNumSize with
    | .error _ => .rejected .unknownError
    | .ok n =>
      if n < 0 then .rejected .negativeLocktime
      else if n.toNat &&& sequenceLockTimeDisableFlag ≠ 0 then .next s
      else match c.checkSequence n with
        | none => .unsupported .checkSequenceVerify
        | some true => .next s
        | some false => .rejected .unsatisfiedLocktime

/--
The `switch` of `EvalScript` (D3, lines 311 to 1030) for opcode `op` with pushed bytes `pushed`.
`fExec` is whether the current branch executes. Core reaches this code with `fExec` false only for `OP_IF` to `OP_ENDIF`.
`next` is the cursor after the instruction, which `OP_CODESEPARATOR` stores.
`checker` is read only by the signature and lock-time opcodes, and `script` only by the signature opcodes.
The stacks list their items from the bottom to the top, so each operation reads the reversed stack, top first.
-/
def execOpcode (checker : Option SignatureChecker) (script : List UInt8) (flags : UInt32) (fExec : Bool)
    (s : ExecState) (op : UInt8) (pushed : List UInt8) (next : Nat) : StepResult :=
  if op ≤ 0x4e then
    -- A push (lines 306 to 310).
    .next { s with stack := s.stack ++ [pushed] }
  else if op = 0x4f ∨ (0x51 ≤ op ∧ op ≤ 0x60) then
    -- `OP_1NEGATE` and `OP_1` to `OP_16` (lines 317 to 341).
    .next { s with stack := s.stack ++ [ScriptNum.encode ((op.toNat : Int) - 0x50)] }
  else match op with
  -- `OP_NOP` (line 347).
  | 0x61 => .next s
  -- `OP_CHECKLOCKTIMEVERIFY` (lines 350 to 390). Without its flag it is `OP_NOP2`.
  | 0xb1 =>
    if hasFlag flags ScriptFlags.checkLockTimeVerify then
      match checker with
      | none => .unsupported .checkLockTimeVerify
      | some c => checkLockTimeStep c s
    else .next s
  -- `OP_CHECKSEQUENCEVERIFY` (lines 392 to 427). Without its flag it is `OP_NOP3`.
  | 0xb2 =>
    if hasFlag flags ScriptFlags.checkSequenceVerify then
      match checker with
      | none => .unsupported .checkSequenceVerify
      | some c => checkSequenceStep c s
    else .next s
  -- `OP_NOP1` and `OP_NOP4` to `OP_NOP10` (lines 429 to 435).
  | 0xb0 | 0xb3 | 0xb4 | 0xb5 | 0xb6 | 0xb7 | 0xb8 | 0xb9 => .next s
  -- `OP_IF` and `OP_NOTIF` (lines 437 to 460).
  | 0x63 | 0x64 =>
    if fExec then
      match s.stack.reverse with
      | [] => .rejected .unbalancedConditional
      | top :: rest =>
        let value := if op = 0x64 then !castToBool top else castToBool top
        .next { s with stack := rest.reverse, vfExec := s.vfExec ++ [value] }
    else .next { s with vfExec := s.vfExec ++ [false] }
  -- `OP_ELSE` (lines 462 to 468).
  | 0x67 =>
    match s.vfExec.reverse with
    | [] => .rejected .unbalancedConditional
    | last :: rest => .next { s with vfExec := rest.reverse ++ [!last] }
  -- `OP_ENDIF` (lines 470 to 476).
  | 0x68 =>
    match s.vfExec.reverse with
    | [] => .rejected .unbalancedConditional
    | _ :: rest => .next { s with vfExec := rest.reverse }
  -- `OP_VERIFY` (lines 478 to 490).
  | 0x69 =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | top :: rest => if castToBool top then .next { s with stack := rest.reverse } else .rejected .verify
  -- `OP_RETURN` (lines 492 to 496).
  | 0x6a => .rejected .opReturn
  -- `OP_TOALTSTACK` (lines 502 to 509).
  | 0x6b =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | top :: rest => .next { s with stack := rest.reverse, altstack := s.altstack ++ [top] }
  -- `OP_FROMALTSTACK` (lines 511 to 518).
  | 0x6c =>
    match s.altstack.reverse with
    | [] => .rejected .invalidAltstackOperation
    | top :: rest => .next { s with stack := s.stack ++ [top], altstack := rest.reverse }
  -- `OP_2DROP` (lines 520 to 528).
  | 0x6d =>
    match s.stack.reverse with
    | _ :: _ :: rest => .next { s with stack := rest.reverse }
    | _ => .rejected .invalidStackOperation
  -- `OP_2DUP` (lines 530 to 540).
  | 0x6e =>
    match s.stack.reverse with
    | x2 :: x1 :: _ => .next { s with stack := s.stack ++ [x1, x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_3DUP` (lines 542 to 554).
  | 0x6f =>
    match s.stack.reverse with
    | x3 :: x2 :: x1 :: _ => .next { s with stack := s.stack ++ [x1, x2, x3] }
    | _ => .rejected .invalidStackOperation
  -- `OP_2OVER` (lines 556 to 566).
  | 0x70 =>
    match s.stack.reverse with
    | _ :: _ :: x2 :: x1 :: _ => .next { s with stack := s.stack ++ [x1, x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_2ROT` (lines 568 to 579).
  | 0x71 =>
    match s.stack.reverse with
    | x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: rest =>
      .next { s with stack := rest.reverse ++ [x3, x4, x5, x6, x1, x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_2SWAP` (lines 581 to 589).
  | 0x72 =>
    match s.stack.reverse with
    | x4 :: x3 :: x2 :: x1 :: rest => .next { s with stack := rest.reverse ++ [x3, x4, x1, x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_IFDUP` (lines 591 to 600).
  | 0x73 =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | top :: _ => if castToBool top then .next { s with stack := s.stack ++ [top] } else .next s
  -- `OP_DEPTH` (lines 602 to 608).
  | 0x74 => .next { s with stack := s.stack ++ [ScriptNum.encode s.stack.length] }
  -- `OP_DROP` (lines 610 to 617).
  | 0x75 =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | _ :: rest => .next { s with stack := rest.reverse }
  -- `OP_DUP` (lines 619 to 627).
  | 0x76 =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | top :: _ => .next { s with stack := s.stack ++ [top] }
  -- `OP_NIP` (lines 629 to 636).
  | 0x77 =>
    match s.stack.reverse with
    | x2 :: _ :: rest => .next { s with stack := rest.reverse ++ [x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_OVER` (lines 638 to 646).
  | 0x78 =>
    match s.stack.reverse with
    | _ :: x1 :: _ => .next { s with stack := s.stack ++ [x1] }
    | _ => .rejected .invalidStackOperation
  -- `OP_PICK` and `OP_ROLL` (lines 648 to 664). `rest` is the stack after the pop, top first.
  | 0x79 | 0x7a =>
    match s.stack.reverse with
    | top :: rest@(_ :: _) =>
      match ScriptNum.decode top false with
      | .error _ => .rejected .unknownError
      | .ok value =>
        let n := ScriptNum.getint value
        if n < 0 then .rejected .invalidStackOperation
        else match rest[n.toNat]? with
          | none => .rejected .invalidStackOperation
          | some x =>
            let kept := if op = 0x7a then rest.eraseIdx n.toNat else rest
            .next { s with stack := kept.reverse ++ [x] }
    | _ => .rejected .invalidStackOperation
  -- `OP_ROT` (lines 666 to 676).
  | 0x7b =>
    match s.stack.reverse with
    | x3 :: x2 :: x1 :: rest => .next { s with stack := rest.reverse ++ [x2, x3, x1] }
    | _ => .rejected .invalidStackOperation
  -- `OP_SWAP` (lines 678 to 685).
  | 0x7c =>
    match s.stack.reverse with
    | x2 :: x1 :: rest => .next { s with stack := rest.reverse ++ [x2, x1] }
    | _ => .rejected .invalidStackOperation
  -- `OP_TUCK` (lines 687 to 695).
  | 0x7d =>
    match s.stack.reverse with
    | x2 :: x1 :: rest => .next { s with stack := rest.reverse ++ [x2, x1, x2] }
    | _ => .rejected .invalidStackOperation
  -- `OP_SIZE` (lines 698 to 706).
  | 0x82 =>
    match s.stack.reverse with
    | [] => .rejected .invalidStackOperation
    | top :: _ => .next { s with stack := s.stack ++ [ScriptNum.encode top.length] }
  -- `OP_EQUAL` and `OP_EQUALVERIFY` (lines 712 to 738).
  | 0x87 | 0x88 =>
    match s.stack.reverse with
    | x2 :: x1 :: rest =>
      if op = 0x88 then
        if x1 = x2 then .next { s with stack := rest.reverse } else .rejected .equalVerify
      else .next { s with stack := rest.reverse ++ [boolBytes (x1 == x2)] }
    | _ => .rejected .invalidStackOperation
  -- `OP_1ADD` to `OP_0NOTEQUAL` (lines 744 to 768).
  | 0x8b => numUnary s (· + 1)
  | 0x8c => numUnary s (· - 1)
  | 0x8f => numUnary s (- ·)
  | 0x90 => numUnary s fun a => if a < 0 then -a else a
  | 0x91 => numUnary s fun a => ofBool (a = 0)
  | 0x92 => numUnary s fun a => ofBool (a ≠ 0)
  -- `OP_ADD` to `OP_MAX` (lines 770 to 825).
  | 0x93 => numBinary s (· + ·)
  | 0x94 => numBinary s (· - ·)
  | 0x9a => numBinary s fun a b => ofBool (a ≠ 0 ∧ b ≠ 0)
  | 0x9b => numBinary s fun a b => ofBool (a ≠ 0 ∨ b ≠ 0)
  | 0x9c => numBinary s fun a b => ofBool (a = b)
  -- `OP_NUMEQUALVERIFY` (lines 803 and 817 to 823). Core pushes `a = b` as a number and pops it when it is true.
  -- The stack check runs only after the instruction, so the push is not observable.
  | 0x9d =>
    match s.stack.reverse with
    | x2 :: x1 :: rest =>
      match ScriptNum.decode x1 false, ScriptNum.decode x2 false with
      | .ok a, .ok b => if a = b then .next { s with stack := rest.reverse } else .rejected .numEqualVerify
      | _, _ => .rejected .unknownError
    | _ => .rejected .invalidStackOperation
  | 0x9e => numBinary s fun a b => ofBool (a ≠ b)
  | 0x9f => numBinary s fun a b => ofBool (a < b)
  | 0xa0 => numBinary s fun a b => ofBool (a > b)
  | 0xa1 => numBinary s fun a b => ofBool (a ≤ b)
  | 0xa2 => numBinary s fun a b => ofBool (a ≥ b)
  | 0xa3 => numBinary s fun a b => if a < b then a else b
  | 0xa4 => numBinary s fun a b => if a > b then a else b
  -- `OP_WITHIN` (lines 827 to 841): `x lo hi → lo ≤ x < hi`, pushed as `vchTrue` or `vchFalse`.
  | 0xa5 =>
    match s.stack.reverse with
    | x3 :: x2 :: x1 :: rest =>
      match ScriptNum.decode x1 false, ScriptNum.decode x2 false, ScriptNum.decode x3 false with
      | .ok a, .ok lo, .ok hi => .next { s with stack := rest.reverse ++ [boolBytes (decide (lo ≤ a ∧ a < hi))] }
      | _, _, _ => .rejected .unknownError
    | _ => .rejected .invalidStackOperation
  -- `OP_RIPEMD160`, `OP_SHA1`, `OP_SHA256`, `OP_HASH160` and `OP_HASH256` (lines 847 to 871).
  | 0xa6 => hashTop s Cryptography.Hash.ripemd160
  | 0xa7 => hashTop s Cryptography.Hash.sha1
  | 0xa8 => hashTop s Cryptography.Hash.sha256
  | 0xa9 => hashTop s Cryptography.Hash.hash160
  | 0xaa => hashTop s Cryptography.Hash.Sha256d.hash
  -- `OP_CODESEPARATOR` (lines 873 to 878).
  | 0xab => .next { s with beginCodeHash := next }
  -- `OP_CHECKSIG` and `OP_CHECKSIGVERIFY` (lines 880 to 918).
  | 0xac | 0xad =>
    match checker with
    | none => .unsupported (.signatureOpcode op)
    | some c => checkSigStep c script flags s op
  -- `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` (lines 920 to 1026).
  | 0xae | 0xaf =>
    match checker with
    | none => .unsupported (.signatureOpcode op)
    | some c => checkMultisigStep c script flags s op
  | _ =>
    -- `default` (lines 1028 and 1029): `OP_RESERVED`, `OP_VER`, `OP_VERIF`, `OP_VERNOTIF`, `OP_RESERVED1`, `OP_RESERVED2` and `0xba` to `0xff`.
    .rejected .badOpcode

/--
One iteration of the loop of `EvalScript` (D3, lines 282 to 1034), after `GetOp` read the instruction `i` at the cursor of `s`.
It checks the push size, the opcode count and the disabled opcodes, in that order.
It then runs `execOpcode` when `fExec` holds or the opcode lies from `OP_IF` to `OP_ENDIF`, and checks the combined stack size.
The cursor of the result is that of `s`. `evalLoop` moves it.
-/
def evalInstruction (checker : Option SignatureChecker) (script : List UInt8) (flags : UInt32) (s : ExecState)
    (i : Instruction) : StepResult :=
  if maxScriptElementSize < i.pushed.length then .rejected .pushSize
  else
    let opCount := countOp i.opcode s.opCount
    if maxOpsPerScript < opCount then .rejected .opCount
    else if isDisabled i.opcode then .rejected .disabledOpcode
    else
      let s := { s with opCount }
      let r :=
        if s.fExec || (0x63 ≤ i.opcode && i.opcode ≤ 0x68) then
          execOpcode checker script flags s.fExec s i.opcode i.pushed i.next
        else .next s
      match r with
      | .next t =>
        if maxStackItems < t.stack.length + t.altstack.length then .rejected .stackSize else .next t
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u

/-- Each instruction that `readInstruction` reads moves the cursor forward, and not past the end of the script. -/
theorem readInstruction_progress {script : List UInt8} {pc : Nat} {i : Instruction}
    (h : readInstruction script pc = .instruction i) : pc < i.next ∧ i.next ≤ script.length := by
  unfold readInstruction at h
  split at h
  · rename_i o b r hr
    cases h
    have h1 := congrArg List.length (readOp_op_append hr)
    have h2 := readOp_rest_length hr
    simp only [List.length_append, List.length_drop] at h1 h2
    constructor <;> simp only <;> omega
  · cases h
  · cases h

/--
The loop of `EvalScript` (D3, lines 273 to 1035) from state `s`, and the final check of the conditional stack (lines 1042 and 1043).
At the end of the script, a nonempty `vfExec` gives `UNBALANCED_CONDITIONAL`.
A short push gives `BAD_OPCODE` (lines 280 and 281).
-/
def evalLoop (checker : Option SignatureChecker) (flags : UInt32) (script : List UInt8) (s : ExecState) :
    EvalResult :=
  match hr : readInstruction script s.pc with
  | .atEnd => if s.vfExec.isEmpty then .ok s else .rejected .unbalancedConditional
  | .truncated .. => .rejected .badOpcode
  | .instruction i =>
    have := readInstruction_progress hr
    match evalInstruction checker script flags s i with
    | .next t => evalLoop checker flags script { t with pc := i.next }
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
termination_by script.length - s.pc
decreasing_by omega

/--
`EvalScript` (D3, lines 248 to 1046) in `SIGVERSION_BASE`, on the caller's main stack `stack`.
`checker` is Core's signature checker, or `none` for a call without one.
A flag outside `supportedFlags` is unsupported, before any other check.
A script above 10,000 bytes gives `SCRIPT_SIZE` (lines 266 and 267).
-/
def evalScript (checker : Option SignatureChecker) (flags : UInt32) (script : List UInt8)
    (stack : List (List UInt8)) : EvalResult :=
  if unsupportedFlagBits flags ≠ 0 then .unsupported (.flags (unsupportedFlagBits flags))
  else if maxScriptSize < script.length then .rejected .scriptSize
  else evalLoop checker flags script (ExecState.init stack)

end DogeLib.Script
