module

public import DogeLib.Exports.Json
public import DogeLib.Script.Verify
public import DogeLib.Script.CoreVerifier
public import DogeLib.Block.Exports.Oracle
public import DogeLib.Transaction.Exports.Oracle

/-!
# `Script.Exports.Oracle`

Script and signature adapters for `dogelib-oracle/1` (docs/oracle.md).
The specification supplies instruction results, Script errors and unsupported reasons.
Adapter resource limits precede execution and do not describe consensus rules.
The transaction decoder and error conversion come from `Transaction.Exports.Oracle`.
Core sources are SOURCES.md D24 (`GetOp2`), D3 (`EvalScript` and `VerifyScript`), D25 (`BaseSignatureChecker`) and D50 (`CPubKey::Verify`).
-/

@[expose] public section

namespace DogeLib.Script.Exports

open Lean (Json)
open DogeLib.Exports

/-- Adapter resource failure, separate from Script rejection. -/
def resourceLimit : Failure := .spec (Json.mkObj [("kind", "adapter"), ("reason", "resource_limit")])

/-- Script bytes, at most 1 MiB, before the specification checks its 10,000-byte limit. -/
def argScript (args : Args) (key : String := "bytes_hex") : Except Failure (List UInt8) := do
  let value ← arg args key
  if let .str text := value then
    if text.utf8ByteSize > 2097152 then throw resourceLimit
  let bytes ← argHex args key
  return bytes

/-- Caller stack, bottom first, bounded by 4,096 items, 1 MiB per item and 4 MiB in total. -/
def argStack (args : Args) : Except Failure (List (List UInt8)) := do
  let .arr items ← arg args "stack_hex" | throw (.request "stack_hex must be an array")
  if items.size > 4096 then throw resourceLimit
  let mut stack := []
  let mut total := 0
  for item in items do
    let .str value := item | throw (.request "stack_hex items must be hexadecimal strings")
    if value.utf8ByteSize > 2097152 then throw resourceLimit
    total := total + value.utf8ByteSize / 2
    if total > 4194304 then throw resourceLimit
    let some bytes := bytesOfHexChars value.toList | throw (.request "invalid stack_hex item")
    stack := bytes :: stack
  return stack.reverse

/-- A main stack in Core vector order, from bottom to top. -/
def stackJson (stack : List (List UInt8)) : Json := .arr (stack.map (fun b => Json.str (hexOf b))).toArray

/-- The reason execution needs an unsupported capability. -/
def unsupportedFields : Unsupported → List (String × Json)
  | .flags bits => [("reason", .str "flags"), ("bits", natJson bits.toNat)]
  | .signatureOpcode op => [("reason", .str "signature_opcode"), ("opcode", natJson op.toNat)]
  | .checkLockTimeVerify => [("reason", .str "check_lock_time_verify")]
  | .checkSequenceVerify => [("reason", .str "check_sequence_verify")]

/-- One `EvalScript` result, with a stack only after success. -/
def evalJson : EvalResult → Json
  | .ok s => Json.mkObj [("result", .str "accepted"), ("script_error", .str "OK"), ("stack_hex", stackJson s.stack)]
  | .rejected e => Json.mkObj [("result", .str "rejected"), ("script_error", .str e.name)]
  | .unsupported reason => Json.mkObj (("result", .str "unsupported") :: unsupportedFields reason)

/-- One instruction read, with the cursor after success or failure. -/
def readJson (pc : Nat) : ReadResult → Json
  | .instruction i => Json.mkObj [("result", .str "instruction"), ("opcode", natJson i.opcode.toNat),
      ("bytes_hex", .str (hexOf i.bytes)), ("pushed_hex", .str (hexOf i.pushed)), ("cursor", natJson i.next)]
  | .atEnd => Json.mkObj [("result", .str "at_end"), ("cursor", natJson pc)]
  | .truncated opcode part cursor => Json.mkObj [("result", .str "truncated"), ("opcode", natJson opcode.toNat),
      ("part", .str (match part with | .lengthField => "length_field" | .payload => "payload")),
      ("cursor", natJson cursor)]

/-- A named adapter failure before Script execution. -/
def adapterFailure (reason : String) : Failure :=
  .spec (Json.mkObj [("kind", "adapter"), ("reason", .str reason)])

/-- The selected checker, with `none` as the default only for evaluation requests. -/
def argChecker (args : Args) (evaluation : Bool) : Except Failure String := do
  let value ← match args.get? "checker" with
    | some v => pure v
    | none => if evaluation then pure (.str "none") else arg args "checker"
  let .str name := value | throw (.request "checker must be a string")
  unless name == "base" || (if evaluation then name == "none" else name == "transaction") do
    throw (.request "unknown checker")
  return name

/-- One spend verdict, without an intermediate stack. -/
def verifyJson : VerifyResult → Json
  | .accepted => Json.mkObj [("result", .str "accepted"), ("script_error", .str "OK")]
  | .rejected e => Json.mkObj [("result", .str "rejected"), ("script_error", .str e.name)]
  | .unsupported u => Json.mkObj (("result", .str "unsupported") :: unsupportedFields u)

/-- One legacy input, after complete base decoding and explicit context and script bounds. -/
def verifyLegacy : Operation where
  name := "script.verify_legacy"
  args := ["tx_hex", "input_index", "prevout_script_hex", "flags", "checker"]
  run args := do
    let txBytes := ByteSlice.ofByteArray (ByteArray.mk (← argHex args "tx_hex").toArray)
    let index ← argU32 args "input_index"
    let script ← argScript args "prevout_script_hex"
    let flags ← argU32 args "flags"
    let checker ← argChecker args false
    let tx ← match Transaction.Transaction.decodeBaseCompleteSlice txBytes with
      | .ok tx => pure tx
      | .error e => throw (.spec ((Transaction.Exports.completeReadErrorJson e).setObjVal! "argument" "tx_hex"))
    if hi : index.toNat < tx.inputs.val.length then
      if hn : tx.inputs.val.length < 2 ^ 32 then
        if ho : tx.outputs.val.length < 2 ^ 32 then
          let ctx : InputContext := ⟨tx, index, hi, hn, ho⟩
          if ctx.input.scriptSig.bytes.val.length > 1048576 then throw resourceLimit
          let some counted := Serialization.CountedList.ofList? script | throw resourceLimit
          return if checker == "base" then
            verifyJson (verifyScript baseChecker flags ctx.input.scriptSig.bytes.val script)
          else verifyJson (verifyLegacySpend ctx ⟨counted⟩ flags coreVerifier)
        else throw (adapterFailure "context_bounds")
      else throw (adapterFailure "context_bounds")
    else throw (adapterFailure "input_index_out_of_range")

/-- Script and single-signature operations in the oracle format. -/
def operations : List Operation := [
  { name := "script.read_op", args := ["bytes_hex", "cursor"], run := fun args => do
      let bytes ← argScript args
      let cursor ← argU32 args "cursor"
      unless cursor.toNat ≤ bytes.length do throw (.request "cursor exceeds script length")
      return readJson cursor.toNat (readInstruction bytes cursor.toNat) },
  { name := "script.eval", args := ["bytes_hex", "flags", "stack_hex", "checker"], run := fun args => do
      let bytes ← argScript args
      let flags ← argU32 args "flags"
      let stack ← argStack args
      let checker ← argChecker args true
      return evalJson (evalScript (if checker == "base" then some baseChecker else none) flags bytes stack) },
  { name := "pubkey.verify", args := ["pubkey_hex", "sig_hex", "digest_hex"], run := fun args => do
      let key ← argScript args "pubkey_hex"
      let sig ← argScript args "sig_hex"
      let digest ← Block.Exports.argHash args "digest_hex"
      return Json.mkObj [("valid", .bool (coreVerify sig key digest))] },
  verifyLegacy]

end DogeLib.Script.Exports
