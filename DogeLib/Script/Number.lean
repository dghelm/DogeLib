module

/-!
# `Script.Number`

Script numbers, Core's `CScriptNum`, and the truth value of a stack item, Core's `CastToBool`.

`CScriptNum` is in `src/script/script.h` lines 198 to 371 of Dogecoin Core `v1.14.9` (SOURCES.md, D24).
`CastToBool` is in `src/script/interpreter.cpp` lines 38 to 51 (D3).

## The encoding

A script number is a byte string in little-endian sign-magnitude form.
The top bit of the last byte is the sign, and the other bits are the magnitude, least significant byte first.
The empty string is zero.
So are the negative-zero strings: zero bytes followed by one `0x80`.

| DogeLib | Core | Lines of D24 |
| --- | --- | --- |
| `ScriptNum.value` | `set_vch` | 353 to 368 |
| `ScriptNum.isMinimal` | the minimality test of the vector constructor | 223 to 240 |
| `ScriptNum.decode` | the vector constructor `CScriptNum(vch, fRequireMinimal, nMaxNumSize)` | 217 to 242 |
| `ScriptNum.encode` | `serialize`, which `getvch` calls | 319 to 351 |
| `ScriptNum.getint` | `getint` | 305 to 312 |
| `defaultMaxNumSize` | `nDefaultMaxNumSize` | 215 |

## Integers, not machine words

Core holds a script number in an `int64_t`.
Here every value is an `Int`, and no operation wraps.
`decode` is total over all lengths, and `encode` takes every integer.
Core's `int64_t` code agrees with these definitions on a smaller domain:

- `set_vch` shifts each byte left by `8*i` bits (line 360).
  For eight bytes or fewer, it computes the value exactly.
  For more than eight bytes, a shift is 64 bits or more, which is undefined in C++.
  The interpreter decodes at most five bytes (D3, lines 377 and 408).
- `serialize` negates its argument (line 326), which is undefined in C++ for the minimum `int64_t`, `-2^63`.
- `getint` returns an `int`. Here its range is that of a 32-bit `int`, `[-2^31, 2^31 - 1]`.

## Decoding

`decode` checks the size first and the minimality second, as the constructor does.
Each failure is a `DecodeError`, where Core throws a `scriptnum_error` (lines 192 to 196).
The interpreter catches the exception and reports `SCRIPT_ERR_UNKNOWN_ERROR` (D3, lines 1037 to 1040).
`Script.execOpcode` gives that mapping for `OP_PICK` and `OP_ROLL`.

The interpreter passes `fRequireMinimal` as the `SCRIPT_VERIFY_MINIMALDATA` flag (D3, line 269).
It decodes with the default size of 4 bytes, except for `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY`, which decode with 5 (D3, lines 377 and 408).
This module specifies no opcode. `DogeLib.Script.Eval` uses these definitions.
-/

@[expose] public section

namespace DogeLib.Script

/-- `CScriptNum::nDefaultMaxNumSize` (D24, line 215): the largest number of bytes in a numeric operand. -/
def defaultMaxNumSize : Nat := 4

namespace ScriptNum

/-- The two failures of the vector constructor of `CScriptNum` (D24, lines 221 and 237). Core throws a `scriptnum_error` for each. -/
inductive DecodeError where
  /-- "script number overflow": the byte string is longer than the maximum size. -/
  | overflow
  /-- "non-minimally encoded script number": the minimal encoding is required, and the byte string fails the test. -/
  | nonMinimal
  deriving DecidableEq, Repr

/-- The little-endian value of a byte string: the first byte is the least significant. -/
def leNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/--
`set_vch` (D24, lines 353 to 368), over `Int`.
The empty string is zero.
Otherwise the magnitude is the little-endian value with the top bit of the last byte cleared, and that bit is the sign.
-/
def value (bytes : List UInt8) : Int :=
  match bytes.getLast? with
  | none => 0
  | some last =>
    let magnitude : Nat := leNat bytes.dropLast + 256 ^ (bytes.length - 1) * (last &&& 0x7f).toNat
    if last &&& 0x80 = 0 then magnitude else -magnitude

/--
The minimality test of the vector constructor (D24, lines 223 to 240), as Core writes it.
A nonempty byte string fails when its last byte without the sign bit is zero.
The exception is a string whose second-to-last byte has its top bit set.
The empty string passes.
-/
def isMinimal (bytes : List UInt8) : Bool :=
  match bytes.reverse with
  | [] => true
  | last :: rest =>
    last &&& 0x7f != 0 || match rest with
      | [] => false
      | prev :: _ => prev &&& 0x80 != 0

/--
The vector constructor `CScriptNum(vch, fRequireMinimal, nMaxNumSize)` (D24, lines 217 to 242).
It fails with `overflow` when the byte string is longer than `maxSize`.
Otherwise, when `requireMinimal` is set, it fails with `nonMinimal` when the string fails `isMinimal`.
Otherwise it returns the value.
-/
def decode (bytes : List UInt8) (requireMinimal : Bool) (maxSize : Nat := defaultMaxNumSize) :
    Except DecodeError Int :=
  if maxSize < bytes.length then .error .overflow
  else if requireMinimal && !isMinimal bytes then .error .nonMinimal
  else .ok (value bytes)

/-- The little-endian bytes of a natural number, with no trailing zero byte: the loop of `serialize` (D24, lines 328 to 332). -/
def leBytes (n : Nat) : List UInt8 :=
  if n = 0 then [] else (n % 256).toUInt8 :: leBytes (n / 256)
termination_by n
decreasing_by omega

/--
`serialize` (D24, lines 319 to 351), over `Int`.
Zero is the empty string.
Otherwise the magnitude is written least significant byte first, and the sign goes into the top bit of the last byte.
If that bit is already set by the magnitude, one more byte carries the sign: `0x80` for a negative number and `0x00` otherwise.
-/
def encode (n : Int) : List UInt8 :=
  let mag := leBytes n.natAbs
  match mag.getLast? with
  | none => []
  | some last =>
    if last &&& 0x80 != 0 then mag ++ [if n < 0 then 0x80 else 0x00]
    else if n < 0 then mag.dropLast ++ [last ||| 0x80]
    else mag

/-- `getint` (D24, lines 305 to 312): the value saturated to the range of a 32-bit `int`, `[-2^31, 2^31 - 1]`. -/
def getint (n : Int) : Int :=
  if 2 ^ 31 - 1 < n then 2 ^ 31 - 1
  else if n < -2 ^ 31 then -2 ^ 31
  else n

end ScriptNum

/--
The loop of `CastToBool` (D3, lines 40 to 49).
The first nonzero byte gives true, unless it is the last byte and equals `0x80`, negative zero.
A string with no nonzero byte gives false.
-/
def castToBoolLoop : List UInt8 → Bool
  | [] => false
  | [b] => b != 0 && b != 0x80
  | b :: rest => b != 0 || castToBoolLoop rest

/--
`CastToBool` (D3, lines 38 to 51): the truth value of a stack item.
Core's loop counts with an `unsigned int` (line 40), so it agrees with this definition for byte strings of at most `UINT_MAX` bytes.
On a longer string the counter wraps, and Core's loop can repeat without end.
This definition is total and has no size limit, so it extends Core's loop beyond that domain.
-/
def castToBool (bytes : List UInt8) : Bool := castToBoolLoop bytes

end DogeLib.Script
