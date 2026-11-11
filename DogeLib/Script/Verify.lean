module

public import DogeLib.Script.Eval

/-!
# `Script.Verify`

Core's `VerifyScript` without a witness, for the supported flags, and the spend predicate of one legacy input.

`VerifyScript` is in `src/script/interpreter.cpp` lines 1409 to 1526 of Dogecoin Core `v1.14.9` (SOURCES.md, D3).
`CScript::IsPushOnly` and `CScript::IsPayToScriptHash` are in `src/script/script.cpp` lines 204 to 259 (D48).
Design record 0003, section 3 and stage 4, sets the contract.

| DogeLib | Core | Source |
| --- | --- | --- |
| `isPushOnly` | `CScript::IsPushOnly` | D48, lines 239 to 259 |
| `isPayToScriptHash` | `CScript::IsPayToScriptHash` | D48, lines 204 to 211 |
| `trueTop` | The checks `stack.empty()` and `CastToBool(stack.back())` | D3, lines 1432 to 1435 and 1478 to 1481 |
| `verifyScript` | `VerifyScript` with an empty witness | D3, lines 1409 to 1526 |
| `verifyLegacySpend` | `VerifyScript` with `TransactionSignatureChecker` for one input | D3, lines 1253 to 1526 |

## Results

`verifyScript` returns a `VerifyResult`:

- `accepted`: Core returns `true` with `SCRIPT_ERR_OK`.
- `rejected e`: Core returns `false` with the error `e`.
- `unsupported r`: a capability is missing, as in `DogeLib.Script.Eval`. The result says nothing about Core's verdict.

## The order of the checks

1. A flag set with a bit outside `supportedFlags` is unsupported, before any other check.
   So Core's `SIGPUSHONLY` check (lines 1419 to 1421), its `WITNESS` branches and its `CLEANSTACK` check (lines 1505 to 1513) are unreachable, and absent.
2. `scriptSig` runs on an empty stack (line 1424).
3. `scriptPubKey` runs on the final stack of `scriptSig` (line 1429). A false or missing top item gives `EVAL_FALSE`.
4. With `P2SH` and the exact template of `isPayToScriptHash` (lines 1457 to 1481):
   1. A `scriptSig` that fails `isPushOnly` gives `SIG_PUSHONLY`.
   2. The stack is again the final stack of `scriptSig`. Its top item is the redeem script, which is popped.
   3. The redeem script runs on the rest. A false or missing top item gives `EVAL_FALSE`.

Core's copy of the stack at lines 1427 and 1428 is the final state of `scriptSig`, which the definition keeps.
Core asserts that this stack is not empty (line 1469).
`verifyScript_p2sh_saved_ne_nil` in `DogeLib.Script.Proofs.Verify` proves that the assert holds: the template begins with `OP_HASH160`, which fails on an empty stack.
The definition still needs a value for that case, and the value is arbitrary.

Without `CLEANSTACK`, which is unsupported, no check limits the number of items left on the stack.

## `IsPushOnly`

`isPushOnly` reads the script from its start with `readInstruction`, as Core's loop calls `GetOp`.
A short push gives false, and so does any opcode above `OP_16` (`0x60`).
Core's test treats `OP_RESERVED` (`0x50`) as push-only, and so does this one.
An executed `OP_RESERVED` in `scriptSig` fails with `BAD_OPCODE` first, so the treatment affects no result of `verifyScript`.

## The spend predicate

`InputContext` is the transaction context of design record 0003, section 3: a transaction, an input index below the number of inputs, and fewer than 2^32 inputs and outputs.
`verifyLegacySpend` runs `verifyScript` with `transactionChecker` on that input's exact `scriptSig` and the caller's previous-output `scriptPubKey`.
The caller establishes that the script belongs to the referenced outpoint. No UTXO set is read.

`DogeLib.Script.Proofs.Verify` proves the properties of these definitions.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/--
The loop of `CScript::IsPushOnly` (D48, lines 239 to 254) from cursor `pc`.
It is true at the end of the script, false on a short push, and false at an opcode above `OP_16`.
-/
def isPushOnlyFrom (script : List UInt8) (pc : Nat) : Bool :=
  match hr : readInstruction script pc with
  | .atEnd => true
  | .truncated .. => false
  | .instruction i =>
    have := readInstruction_progress hr
    decide (i.opcode ≤ 0x60) && isPushOnlyFrom script i.next
termination_by script.length - pc
decreasing_by omega

/--
`CScript::IsPushOnly` (D48, lines 256 to 259): every instruction reads, and no opcode is above `OP_16`.
It has the domain of `readInstruction`, a script of fewer than 2^31 bytes.
`verifyScript` calls it only on a `scriptSig` that `evalScript` accepted, which has at most 10,000 bytes.
-/
def isPushOnly (script : List UInt8) : Bool := isPushOnlyFrom script 0

/--
`CScript::IsPayToScriptHash` (D48, lines 204 to 211): 23 bytes, with `OP_HASH160` first, `0x14` second and `OP_EQUAL` last.
That is `OP_HASH160`, a push of 20 bytes, and `OP_EQUAL`.
-/
def isPayToScriptHash (script : List UInt8) : Bool :=
  script.length == 23 && script[0]? == some 0xa9 && script[1]? == some 0x14 && script[22]? == some 0x87

/-- Core's check after an evaluation (D3, lines 1432 to 1435 and 1478 to 1481): the stack is not empty, and its top item is true. -/
def trueTop (stack : List (List UInt8)) : Bool :=
  match stack.getLast? with
  | none => false
  | some top => castToBool top

/-- The outcome of one `VerifyScript` call. -/
inductive VerifyResult where
  /-- Core returns `true` with `SCRIPT_ERR_OK`. -/
  | accepted
  /-- Core returns `false` with this error. -/
  | rejected (error : ScriptError)
  /-- The call needs a capability that is missing. Core's verdict is not determined. -/
  | unsupported (reason : Unsupported)
  deriving DecidableEq, Repr

/-- One evaluation followed by Core's check of its final stack: `EVAL_FALSE` unless the top item is true. -/
def finishEval : EvalResult → VerifyResult
  | .ok s => if trueTop s.stack then .accepted else .rejected .evalFalse
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u

/--
`VerifyScript` (D3, lines 1409 to 1526) with an empty witness and the checker `c`, for `scriptSig` and `scriptPubKey`.
The module documentation lists the checks in Core's order.
-/
def verifyScript (c : SignatureChecker) (flags : UInt32) (scriptSig scriptPubKey : List UInt8) : VerifyResult :=
  if unsupportedFlagBits flags ≠ 0 then .unsupported (.flags (unsupportedFlagBits flags))
  else match evalScript (some c) flags scriptSig [] with
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u
  | .ok s =>
    match evalScript (some c) flags scriptPubKey s.stack with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok t =>
      if !trueTop t.stack then .rejected .evalFalse
      else if hasFlag flags ScriptFlags.p2sh && isPayToScriptHash scriptPubKey then
        if !isPushOnly scriptSig then .rejected .sigPushOnly
        else match s.stack.reverse with
          -- Core asserts that the stack is not empty (line 1469), and `verifyScript_p2sh_saved_ne_nil` proves it.
          -- This value is arbitrary and unreachable. It is not Core's behavior.
          | [] => .rejected .unknownError
          | redeem :: rest => finishEval (evalScript (some c) flags redeem rest.reverse)
      else .accepted

/--
The transaction context of design record 0003, section 3: a transaction and the index of one of its inputs.
The bounds on the numbers of inputs and outputs are those of the design record. Core's transaction reader gives both.
-/
structure InputContext where
  /-- The spending transaction. -/
  tx : Transaction
  /-- The index of the input, Core's `nIn`. -/
  index : UInt32
  /-- The index selects an input. -/
  index_lt : index.toNat < tx.inputs.val.length
  /-- Fewer than 2^32 inputs. -/
  inputs_lt : tx.inputs.val.length < 2 ^ 32
  /-- Fewer than 2^32 outputs. -/
  outputs_lt : tx.outputs.val.length < 2 ^ 32

/-- The input that the index selects, `txTo->vin[nIn]`. -/
def InputContext.input (ctx : InputContext) : TxIn := ctx.tx.inputs.val[ctx.index.toNat]'ctx.index_lt

/--
One legacy input against the script of the output that it spends.
It runs `verifyScript` with `transactionChecker` for the input, on the input's exact `scriptSig` and on `prevScriptPubKey`.
`verify` is the elliptic-curve check that `transactionChecker` takes. SOUNDNESS.md records its hypothesis.
-/
def verifyLegacySpend (ctx : InputContext) (prevScriptPubKey : Transaction.Script) (flags : UInt32)
    (verify : SignatureVerifier) : VerifyResult :=
  verifyScript (transactionChecker ctx.tx ctx.index verify) flags ctx.input.scriptSig.bytes.val
    prevScriptPubKey.bytes.val

end DogeLib.Script
