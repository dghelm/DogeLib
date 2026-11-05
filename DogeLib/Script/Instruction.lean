module

public import DogeLib.Transaction.LegacySighash

/-!
# `Script.Instruction`

The instruction reader of the Script interpreter: one call of Core's `CScript::GetOp2` at a cursor.

Core reads Script instructions with `GetOp2`, `src/script/script.h` lines 502 to 552 of Dogecoin Core `v1.14.9` (SOURCES.md, D24).
`EvalScript` calls it through the `GetOp` wrapper at line 492, which passes a vector for the pushed bytes.
A cursor here is the offset of Core's iterator `pc` from `begin()`.

## What `GetOp2` does

`GetOp2` first sets its opcode result to `OP_INVALIDOPCODE` and clears the vector for the pushed bytes.
Then it reads one opcode byte at the cursor and moves the cursor past it.
An opcode up to `OP_PUSHDATA4` (`0x4e`) is a push, and its size `nSize` comes from one of two places:

- An opcode below `OP_PUSHDATA1` (`0x4c`) is its own size, from 0 to 75 bytes.
- `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4` (`0x4c`, `0x4d`, `0x4e`) read a length field of 1, 2 or 4 bytes after the opcode, in little-endian order (`ReadLE16` and `ReadLE32`, D37).

A push then copies the next `nSize` bytes into the vector and moves the cursor past them.
Every other opcode is one byte, and its vector stays empty.

`GetOp2` returns false in three cases, and the cursor stays where the last successful read left it:

| Case | Cursor after the call |
| --- | --- |
| The cursor is at or after the end | Unchanged |
| The length field of `OP_PUSHDATA1`, `OP_PUSHDATA2` or `OP_PUSHDATA4` is short | After the opcode |
| Fewer than `nSize` bytes follow the length field | After the length field, or after the opcode for a direct push |

## The reader

`readInstruction script pc` returns a `ReadResult`.
A successful read gives an `Instruction`: the opcode, the exact bytes of the instruction, the pushed bytes and the next cursor.
The reader does not normalize push encodings.
A nonminimal push, such as `4c 01 07` for the byte that `OP_7` also pushes, keeps its own bytes.

`readInstruction` is defined through `Transaction.readOp`, which the legacy signature serializer uses (`DogeLib.Transaction.LegacySighash`).
So the interpreter and the serializer decode a script with the same definition.
`readOp` takes the bytes after the cursor and returns the bytes after the instruction.
`readInstruction` takes the whole script and a cursor, and returns cursors.

The two failures of Core are two results here: `atEnd` and `truncated`.
Core returns the same `false` for both, with `OP_INVALIDOPCODE` and an empty vector.
`truncated` also holds the opcode byte and the part of the push that is short, for diagnostics.
`EvalScript` never calls `GetOp2` at the end of a script, because its loop runs only `while (pc < pend)`.

## Instruction boundaries

`IsBoundary script pc` holds for the cursors that a loop of `GetOp2` calls from `begin()` reaches.
The reader itself decodes any cursor that it receives, including one inside the bytes of a push.
`DogeLib.Script.Proofs.Instruction` proves that no boundary lies inside an instruction that starts at a boundary.
So a loop from `begin()` never reads a byte of a length field or of pushed data as an opcode.

`DogeLib.Script.Proofs.Instruction` proves the properties of these definitions.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-- The width in bytes of the length field after an opcode. `OP_PUSHDATA1` has 1, `OP_PUSHDATA2` has 2, `OP_PUSHDATA4` has 4, and every other opcode has 0. -/
def lengthFieldWidth (op : UInt8) : Nat :=
  if op = 0x4c then 1 else if op = 0x4d then 2 else if op = 0x4e then 4 else 0

/-- The value of a length field, in little-endian order: `ReadLE16` and `ReadLE32` (D37) for fields of 2 and 4 bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * leValue bs

/--
The size `nSize` of the data that `GetOp2` reads after an opcode and its length field.
A direct push is its own size, and `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4` take the value of the length field.
Every other opcode has no data.
-/
def pushSize (op : UInt8) (lengthField : List UInt8) : Nat :=
  if op < 0x4c then op.toNat else if op ≤ 0x4e then leValue lengthField else 0

/-- The part of a push that `GetOp2` found short. -/
inductive ShortPart where
  /-- The length field of `OP_PUSHDATA1`, `OP_PUSHDATA2` or `OP_PUSHDATA4` is short. The cursor stops after the opcode. -/
  | lengthField
  /-- Fewer than `nSize` bytes follow the length field. The cursor stops after the length field, or after the opcode for a direct push. -/
  | payload
  deriving DecidableEq, Repr

/-- One instruction that `GetOp2` read. -/
structure Instruction where
  /-- The opcode, `opcodeRet`. -/
  opcode : UInt8
  /-- The bytes of the instruction, from the cursor before the call to the cursor after it. -/
  bytes : List UInt8
  /-- The pushed bytes, `*pvchRet`: the data of a push, and empty for every other opcode. -/
  pushed : List UInt8
  /-- The cursor after the instruction. -/
  next : Nat
  deriving DecidableEq, Repr

/-- The result of one `GetOp2` call at a cursor. -/
inductive ReadResult where
  /-- `GetOp2` returned true and read this instruction. -/
  | instruction (i : Instruction)
  /-- `GetOp2` returned false because the cursor was at or after the end of the script. The cursor is unchanged. -/
  | atEnd
  /-- `GetOp2` returned false on a short push that starts with `opcode`. `cursor` is where the call left `pc`. Core's opcode result is `OP_INVALIDOPCODE` here, not `opcode`. -/
  | truncated (opcode : UInt8) (part : ShortPart) (cursor : Nat)
  deriving DecidableEq, Repr

/--
`GetOp2` at cursor `pc` of `script` (D24, lines 502 to 552).

The definition reads `script.drop pc` with `Transaction.readOp`, which the legacy signature serializer also uses.
The pushed bytes are the bytes of the instruction after its opcode and its length field.
On a failure, `readOp` passes the opcode and the part of the length field that it read.
The cursor moves past those bytes.
-/
def readInstruction (script : List UInt8) (pc : Nat) : ReadResult :=
  match readOp (script.drop pc) with
  | .op o b _ => .instruction ⟨o, b, b.drop (1 + lengthFieldWidth o), pc + b.length⟩
  | .stop [] => .atEnd
  | .stop (o :: lf) =>
    .truncated o (if lf.length = lengthFieldWidth o then .payload else .lengthField) (pc + 1 + lf.length)

/--
The instruction boundaries of `script`: the cursors that a loop of `GetOp2` calls from `begin()` reaches.
The start is a boundary, and so is the cursor after each instruction that starts at a boundary.
-/
inductive IsBoundary (script : List UInt8) : Nat → Prop where
  /-- The start of the script, `begin()`. -/
  | start : IsBoundary script 0
  /-- The cursor after an instruction that starts at a boundary. -/
  | step {pc : Nat} {i : Instruction} :
      IsBoundary script pc → readInstruction script pc = .instruction i → IsBoundary script i.next

end DogeLib.Script
