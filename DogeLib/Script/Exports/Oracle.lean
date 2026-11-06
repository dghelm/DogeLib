module

public import DogeLib.Exports.Json
public import DogeLib.Script.Eval

/-!
# `Script.Exports.Oracle`

Script adapters for `dogelib-oracle/5` (docs/oracle.md).
The specification supplies instruction results, Script errors and unsupported reasons.
Adapter resource limits precede execution and do not describe consensus rules.
Core sources are SOURCES.md D24 (`GetOp2`), D3 (`EvalScript`) and D25 (`BaseSignatureChecker`).
-/

@[expose] public section

namespace DogeLib.Script.Exports

open Lean (Json)
open DogeLib.Exports

/-- Adapter resource failure, separate from Script rejection. -/
def resourceLimit : Failure := .spec (Json.mkObj [("kind", "adapter"), ("reason", "resource_limit")])

/-- Script bytes, at most 1 MiB, before the specification checks its 10,000-byte limit. -/
def argScript (args : Args) : Except Failure (List UInt8) := do
  let value ← arg args "bytes_hex"
  if let .str text := value then
    if text.utf8ByteSize > 2097152 then throw resourceLimit
  let bytes ← argHex args "bytes_hex"
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

/-- Script operations in the oracle format. -/
def operations : List Operation := [
  { name := "script.read_op", args := ["bytes_hex", "cursor"], run := fun args => do
      let bytes ← argScript args
      let cursor ← argU32 args "cursor"
      unless cursor.toNat ≤ bytes.length do throw (.request "cursor exceeds script length")
      return readJson cursor.toNat (readInstruction bytes cursor.toNat) },
  { name := "script.eval", args := ["bytes_hex", "flags", "stack_hex"], run := fun args => do
      let bytes ← argScript args
      let flags ← argU32 args "flags"
      let stack ← argStack args
      return evalJson (evalScript none flags bytes stack) }]

end DogeLib.Script.Exports
