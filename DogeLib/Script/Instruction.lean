module

public import DogeLib.Transaction.LegacySighash

/-!
# Script instructions

The reader reuses `Transaction.readOp`, following Dogecoin Core's `CScript::GetOp2` (SOURCES.md, D24).
Cursors count bytes from the start of the script.
Decoding accepts nonminimal pushes and imposes no execution limits.
-/

@[expose] public section

namespace DogeLib.Script

/-- Bytes pushed by an instruction, or `none` for an opcode above `OP_PUSHDATA4`.
`OP_0` pushes the empty byte string.
The input bytes must be a complete instruction from `Transaction.readOp`. -/
def pushedBytes (opcode : UInt8) (bytes : List UInt8) : Option (List UInt8) :=
  if opcode < 0x4c then some (bytes.drop 1)
  else if opcode = 0x4c then some (bytes.drop 2)
  else if opcode = 0x4d then some (bytes.drop 3)
  else if opcode = 0x4e then some (bytes.drop 5)
  else none

/-- A decoded instruction, retaining its exact encoding and the cursor after its bytes. -/
structure Instruction where
  /-- The first byte of the instruction. -/
  opcode : UInt8
  /-- The opcode, length field and payload, without normalization. -/
  bytes : List UInt8
  /-- The raw payload for a push, including an empty payload for `OP_0`. -/
  pushed : Option (List UInt8)
  /-- The absolute byte offset after this instruction. -/
  nextCursor : Nat
  deriving BEq, Repr

/-- A reader result, with end-of-script distinct from a truncated push.
On either unsuccessful Core read, `opcodeRet` is `OP_INVALIDOPCODE` (0xff) and the returned push value is empty.
`invalidCursor` is an API error with no Core iterator counterpart. -/
inductive ReadResult where
  /-- One complete instruction. -/
  | instruction (value : Instruction)
  /-- The cursor equals the script length. -/
  | endOfScript
  /-- A short length field or payload, with Core's cursor after the failed call. -/
  | truncatedPush (nextCursor : Nat)
  /-- The supplied cursor is beyond the script length. -/
  | invalidCursor
  deriving BEq, Repr

/-- Read at an absolute cursor.
A short length field consumes only the opcode.
A short payload consumes the opcode and the complete length field. -/
def readInstruction (script : List UInt8) (cursor : Nat) : ReadResult :=
  if cursor ≤ script.length then
    match Transaction.readOp (script.drop cursor) with
    | .op opcode bytes _ =>
      .instruction ⟨opcode, bytes, pushedBytes opcode bytes, cursor + bytes.length⟩
    | .stop passed =>
      if script.drop cursor = [] then .endOfScript
      else .truncatedPush (cursor + passed.length)
  else .invalidCursor

/-- Read complete instructions from a suffix, retaining absolute cursors.
The terminal result reports end-of-script or the cursor of a truncated push.
Failed instruction bytes are excluded from the instruction list. -/
def readInstructionsFrom (remaining : List UInt8) (cursor : Nat) : List Instruction × ReadResult :=
  match _h : Transaction.readOp remaining with
  | .op opcode bytes rest =>
    let tail := readInstructionsFrom rest (cursor + bytes.length)
    (⟨opcode, bytes, pushedBytes opcode bytes, cursor + bytes.length⟩ :: tail.1, tail.2)
  | .stop passed =>
    ([], if remaining = [] then .endOfScript else .truncatedPush (cursor + passed.length))
termination_by remaining.length
decreasing_by exact Transaction.readOp_rest_length _h

/-- Read a whole script until its end or its first truncated push. -/
def readInstructions (script : List UInt8) : List Instruction × ReadResult :=
  readInstructionsFrom script 0

end DogeLib.Script
