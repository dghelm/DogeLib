module

public import Lean.Data.Json
public import DogeLib.Base.Bytes

/-!
# `Exports.Json`

The conversions between JSON values and the arguments and results of the oracle, `dogelib-oracle/5`.

`docs/oracle.md` defines the record format. This module implements its rules for arguments:

- A byte string is a string of hexadecimal digits, two per byte, in serialization order. Upper and lower case are accepted.
- A field of at most 32 bits is a JSON number with an integer value, in any notation: `5`, `5.0` and `50e-1` are all 5.
  The check uses the mantissa and exponent of the parsed number, never a floating-point value.
- A 64-bit field is a string of decimal digits with no sign and no leading zero, so that no JSON reader rounds it.

Lean core's `Json.parse` reads the request. It keeps the last value of a repeated key.
-/

@[expose] public section

namespace DogeLib.Exports

open Lean (Json JsonNumber)

/-- A request error, a specification error or an adapter resource failure. -/
inductive Failure where
  /-- The request is malformed: the message says how. -/
  | request (message : String)
  /-- A structured error from the specification or an adapter resource limit. -/
  | spec (error : Json)

/-- The arguments of a request: the fields of its JSON object. -/
abbrev Args := Std.TreeMap.Raw String Json

/-- An operation of the oracle: its name, the names of its arguments, and the function that computes its result. -/
structure Operation where
  /-- The value of the request's `op` field. -/
  name : String
  /-- The argument fields that the operation reads. Any other field except `id` and `op` is a request error. -/
  args : List String
  /-- The `ok` object of the response, or the failure. -/
  run : Args → Except Failure Json

/-- The value of one hexadecimal digit, or `none` for another character. -/
def hexDigit? (c : Char) : Option UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
  else none

/-- The bytes that pairs of hexadecimal digits encode, or `none` for an odd count or another character. -/
def bytesOfHexChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
    let h ← hexDigit? hi
    let l ← hexDigit? lo
    return (h * 16 + l) :: (← bytesOfHexChars rest)

/-- The lowercase hexadecimal digit of a value below 16. -/
def hexChar (n : UInt8) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n.toNat) else Char.ofNat ('a'.toNat + n.toNat - 10)

/-- The lowercase hexadecimal digits of the bytes, two per byte, in order. -/
def hexOf (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun (b : UInt8) => [hexChar (b >>> 4), hexChar (b &&& 0x0f)])

/-- A JSON number with an integer value. -/
def natJson (n : Nat) : Json := .num ⟨n, 0⟩

/-- A 64-bit value as a JSON string of decimal digits. -/
def u64Json (n : UInt64) : Json := .str (toString n.toNat)

/-- A 32-byte hash in both byte orders: `<name>_hex` in serialization order and `<name>_display` reversed, as Core prints it. -/
def hashFields (name : String) (h : Hash256) : List (String × Json) :=
  [(name ++ "_hex", .str (hexOf h.val)), (name ++ "_display", .str (hexOf h.displayBytes))]

/-- The value of argument `key`, or a request error when it is absent. -/
def arg (args : Args) (key : String) : Except Failure Json :=
  match args.get? key with
  | some v => .ok v
  | none => .error (.request s!"missing argument {key}")

/-- Argument `key` as a byte string written in hexadecimal. -/
def argHex (args : Args) (key : String) : Except Failure (List UInt8) := do
  let .str s ← arg args key | throw (.request s!"argument {key} must be a string of hexadecimal digits")
  match bytesOfHexChars s.toList with
  | some bs => return bs
  | none => throw (.request s!"argument {key} must have an even number of hexadecimal digits and no other character")

/-- The integer value of a JSON number, or `none` when its value has a fractional part. -/
def integerOf? (n : JsonNumber) : Option Int :=
  let d : Int := (10 ^ n.exponent : Nat)
  if n.mantissa % d = 0 then some (n.mantissa / d) else none

/-- Argument `key` as an integer from `lo` to `hi`, written as a JSON number. -/
def argInt (args : Args) (key : String) (lo hi : Int) : Except Failure Int := do
  let .num n ← arg args key | throw (.request s!"argument {key} must be a number")
  let some i := integerOf? n | throw (.request s!"argument {key} must be an integer")
  unless lo ≤ i ∧ i ≤ hi do throw (.request s!"argument {key} must be from {lo} to {hi}")
  return i

/-- Argument `key` as a 32-bit unsigned value, written as a JSON number. -/
def argU32 (args : Args) (key : String) : Except Failure UInt32 := do
  return (← argInt args key 0 (2 ^ 32 - 1)).toNat.toUInt32

/-- Whether a string is a decimal numeral with no sign and no leading zero. -/
def isDecimal (s : String) : Bool :=
  match s.toList with
  | [] => false
  | ['0'] => true
  | c :: cs => c ≠ '0' ∧ (c :: cs).all Char.isDigit

/-- Argument `key` as a 64-bit unsigned value, written as a string of decimal digits. -/
def argU64 (args : Args) (key : String) : Except Failure UInt64 := do
  let .str s ← arg args key | throw (.request s!"argument {key} must be a string of decimal digits")
  unless isDecimal s do throw (.request s!"argument {key} must be decimal digits with no sign and no leading zero")
  let n := s.toNat!
  unless n < 2 ^ 64 do throw (.request s!"argument {key} must be below 2^64")
  return n.toUInt64

end DogeLib.Exports
