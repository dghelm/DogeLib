import DogeLib.Script
import KnownAnswers.Transaction

/-!
## Script instruction reader

Runs `readInstruction` on cases from Dogecoin Core's `script_tests.json` and on cases derived from `GetOp2`, through the compiled code.

Every expected result is written by hand.
A case from `script_tests.json` (SOURCES.md, D24 for the reader) names its line at commit `e0a1c15`.
The asm of the fixture is written here as its bytes, and the expected result follows from `GetOp2`, `src/script/script.h` lines 502 to 552.
A case marked `GetOp2` comes from that function alone.

The `OP_0`, high-length-byte and state reset cases are adapted from an independent implementation of this stage (branch `feat/script-state-codex`), with citations to Core added here.
Each case fixes a script, a cursor and the full `ReadResult`.
That result is the opcode, the instruction bytes, the pushed bytes and the next cursor, or the failure, its part and its cursor.
A loop case fixes the results of `readInstruction` calls from cursor 0.
The loop stops after the first result that is not an instruction.

The cases cover direct pushes, `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4`, and every short length field.
They also cover short data for each push kind, nonminimal pushes and code separator bytes inside pushed data.
Some cases read at cursors after 0, and some read opcodes that push nothing.
-/

namespace KnownAnswers.Script

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- A successful read with opcode `o`, instruction bytes `bytes`, pushed bytes `pushed` and next cursor `next`. -/
def ins (o : UInt8) (bytes pushed : List UInt8) (next : Nat) : ReadResult :=
  .instruction ⟨o, bytes, pushed, next⟩

/-- One case: a label with its source, a script, a cursor and the expected result. -/
structure Case where
  label : String
  script : List UInt8
  pc : Nat
  expected : ReadResult

/-- One loop case: a label with its source, a script and the expected results of the loop from cursor 0. -/
structure LoopCase where
  label : String
  script : List UInt8
  expected : List ReadResult

/-- The payload of `script_tests.json` line 25: `A` and then 74 bytes `z`. -/
def az75 : List UInt8 := 0x41 :: rep 74 0x7a

/-- The single-read cases. -/
def cases : List Case := [
  -- script_tests.json: direct pushes, PUSHDATA forms, nonminimal pushes, short pushes.
  ⟨"script_tests.json:23 0x01 0x0b", [0x01, 0x0b], 0, ins 0x01 [0x01, 0x0b] [0x0b] 2⟩,
  ⟨"script_tests.json:24 0x02 0x417a", [0x02, 0x41, 0x7a], 0, ins 0x02 [0x02, 0x41, 0x7a] [0x41, 0x7a] 3⟩,
  ⟨"script_tests.json:25 0x4b and 75 bytes", 0x4b :: az75, 0, ins 0x4b (0x4b :: az75) az75 76⟩,
  ⟨"script_tests.json:28 0x4c 0x01 0x07", [0x4c, 0x01, 0x07], 0, ins 0x4c [0x4c, 0x01, 0x07] [0x07] 3⟩,
  ⟨"script_tests.json:29 0x4d 0x0100 0x08", [0x4d, 0x01, 0x00, 0x08], 0,
    ins 0x4d [0x4d, 0x01, 0x00, 0x08] [0x08] 4⟩,
  ⟨"script_tests.json:30 0x4e 0x01000000 0x09", [0x4e, 0x01, 0x00, 0x00, 0x00, 0x09], 0,
    ins 0x4e [0x4e, 0x01, 0x00, 0x00, 0x00, 0x09] [0x09] 6⟩,
  ⟨"script_tests.json:32 0x4c 0x00", [0x4c, 0x00], 0, ins 0x4c [0x4c, 0x00] [] 2⟩,
  ⟨"script_tests.json:33 0x4d 0x0000", [0x4d, 0x00, 0x00], 0, ins 0x4d [0x4d, 0x00, 0x00] [] 3⟩,
  ⟨"script_tests.json:34 0x4e 0x00000000", [0x4e, 0x00, 0x00, 0x00, 0x00], 0,
    ins 0x4e [0x4e, 0x00, 0x00, 0x00, 0x00] [] 5⟩,
  ⟨"script_tests.json:538 0x4c 0x4b and 75 bytes", [0x4c, 0x4b] ++ rep 75 0x11, 0,
    ins 0x4c ([0x4c, 0x4b] ++ rep 75 0x11) (rep 75 0x11) 77⟩,
  ⟨"script_tests.json:721 0x4c01", [0x4c, 0x01], 0, .truncated 0x4c .payload 2⟩,
  ⟨"script_tests.json:722 0x4d0200ff", [0x4d, 0x02, 0x00, 0xff], 0, .truncated 0x4d .payload 3⟩,
  ⟨"script_tests.json:723 0x4e03000000ffff", [0x4e, 0x03, 0x00, 0x00, 0x00, 0xff, 0xff], 0,
    .truncated 0x4e .payload 5⟩,
  -- GetOp2: OP_0 pushes an empty byte string.
  ⟨"GetOp2: OP_0", [0x00], 0, ins 0x00 [0x00] [] 1⟩,
  -- GetOp2: lengths with a nonzero high byte, read in little-endian order.
  ⟨"GetOp2: 4d 0001 and 256 bytes", [0x4d, 0x00, 0x01] ++ rep 256 0xab, 0,
    ins 0x4d ([0x4d, 0x00, 0x01] ++ rep 256 0xab) (rep 256 0xab) 259⟩,
  ⟨"GetOp2: 4e 00010000 and 256 bytes", [0x4e, 0x00, 0x01, 0x00, 0x00] ++ rep 256 0xab, 0,
    ins 0x4e ([0x4e, 0x00, 0x01, 0x00, 0x00] ++ rep 256 0xab) (rep 256 0xab) 261⟩,
  ⟨"GetOp2: 4d 0001, no data", [0x4d, 0x00, 0x01], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4e 00000100, no data", [0x4e, 0x00, 0x00, 0x01, 0x00], 0, .truncated 0x4e .payload 5⟩,
  ⟨"GetOp2: 4e 00000001, no data", [0x4e, 0x00, 0x00, 0x00, 0x01], 0, .truncated 0x4e .payload 5⟩,
  -- GetOp2: the end of the script.
  ⟨"GetOp2: empty script", [], 0, .atEnd⟩,
  ⟨"GetOp2: cursor at the end", [0x61], 1, .atEnd⟩,
  ⟨"GetOp2: cursor after the end", [0x61], 5, .atEnd⟩,
  -- GetOp2: every short length field. The cursor stops after the opcode.
  ⟨"GetOp2: 4c, no length byte", [0x4c], 0, .truncated 0x4c .lengthField 1⟩,
  ⟨"GetOp2: 4d, no length byte", [0x4d], 0, .truncated 0x4d .lengthField 1⟩,
  ⟨"GetOp2: 4d, one length byte", [0x4d, 0x00], 0, .truncated 0x4d .lengthField 1⟩,
  ⟨"GetOp2: 4e, no length byte", [0x4e], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, one length byte", [0x4e, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, two length bytes", [0x4e, 0x00, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  ⟨"GetOp2: 4e, three length bytes", [0x4e, 0x00, 0x00, 0x00], 0, .truncated 0x4e .lengthField 1⟩,
  -- GetOp2: short data. The cursor stops after the length field, or after a direct push opcode.
  ⟨"GetOp2: 01, no data", [0x01], 0, .truncated 0x01 .payload 1⟩,
  ⟨"GetOp2: 02, one data byte", [0x02, 0xaa], 0, .truncated 0x02 .payload 1⟩,
  ⟨"GetOp2: 4b, 74 data bytes", 0x4b :: rep 74 0xaa, 0, .truncated 0x4b .payload 1⟩,
  ⟨"GetOp2: 4c ff, 254 data bytes", [0x4c, 0xff] ++ rep 254 0xaa, 0, .truncated 0x4c .payload 2⟩,
  ⟨"GetOp2: 4d 0100, no data", [0x4d, 0x01, 0x00], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4d ffff, 3 data bytes", [0x4d, 0xff, 0xff, 0xaa, 0xaa, 0xaa], 0, .truncated 0x4d .payload 3⟩,
  ⟨"GetOp2: 4e 01000000, no data", [0x4e, 0x01, 0x00, 0x00, 0x00], 0, .truncated 0x4e .payload 5⟩,
  ⟨"GetOp2: 4e ffffffff, 1 data byte", [0x4e, 0xff, 0xff, 0xff, 0xff, 0xaa], 0,
    .truncated 0x4e .payload 5⟩,
  -- GetOp2: nonminimal pushes with data keep their own bytes.
  ⟨"GetOp2: 4d 0100 aa", [0x4d, 0x01, 0x00, 0xaa], 0, ins 0x4d [0x4d, 0x01, 0x00, 0xaa] [0xaa] 4⟩,
  ⟨"GetOp2: 4e 02000000 aabb", [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa, 0xbb], 0,
    ins 0x4e [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa, 0xbb] [0xaa, 0xbb] 7⟩,
  ⟨"GetOp2: 4c ff and 255 bytes", [0x4c, 0xff] ++ rep 255 0xaa, 0,
    ins 0x4c ([0x4c, 0xff] ++ rep 255 0xaa) (rep 255 0xaa) 257⟩,
  -- GetOp2: reads at cursors after 0, including one inside pushed data.
  ⟨"GetOp2: 51 02aabb ab at 1", [0x51, 0x02, 0xaa, 0xbb, 0xab], 1,
    ins 0x02 [0x02, 0xaa, 0xbb] [0xaa, 0xbb] 4⟩,
  ⟨"GetOp2: 51 02aabb ab at 2, inside the push", [0x51, 0x02, 0xaa, 0xbb, 0xab], 2,
    ins 0xaa [0xaa] [] 3⟩,
  ⟨"GetOp2: 51 02aabb ab at 4", [0x51, 0x02, 0xaa, 0xbb, 0xab], 4, ins 0xab [0xab] [] 5⟩,
  ⟨"GetOp2: 51 4d01 at 1", [0x51, 0x4d, 0x01], 1, .truncated 0x4d .lengthField 2⟩,
  ⟨"GetOp2: 51 4c02aa at 1", [0x51, 0x4c, 0x02, 0xaa], 1, .truncated 0x4c .payload 3⟩,
  -- GetOp2: opcodes above OP_PUSHDATA4 are one byte and push nothing.
  ⟨"GetOp2: OP_1NEGATE", [0x4f, 0x01], 0, ins 0x4f [0x4f] [] 1⟩,
  ⟨"GetOp2: OP_RESERVED", [0x50, 0x01], 0, ins 0x50 [0x50] [] 1⟩,
  ⟨"GetOp2: OP_NOP", [0x61], 0, ins 0x61 [0x61] [] 1⟩,
  ⟨"GetOp2: OP_CODESEPARATOR", [0xab, 0x01], 0, ins 0xab [0xab] [] 1⟩,
  ⟨"GetOp2: OP_INVALIDOPCODE", [0xff], 0, ins 0xff [0xff] [] 1⟩
]

/-- The loop cases. -/
def loopCases : List LoopCase := [
  ⟨"script_tests.json:442 CODESEPARATOR 1", [0xab, 0x51],
    [ins 0xab [0xab] [] 1, ins 0x51 [0x51] [] 2, .atEnd]⟩,
  ⟨"script_tests.json:721 0x4c01", [0x4c, 0x01], [.truncated 0x4c .payload 2]⟩,
  ⟨"GetOp2: 01 ab, a separator byte as data", [0x01, 0xab], [ins 0x01 [0x01, 0xab] [0xab] 2, .atEnd]⟩,
  ⟨"GetOp2: 02 abab ab, data then a separator", [0x02, 0xab, 0xab, 0xab],
    [ins 0x02 [0x02, 0xab, 0xab] [0xab, 0xab] 3, ins 0xab [0xab] [] 4, .atEnd]⟩,
  ⟨"GetOp2: 4c ab and 171 bytes ab, a separator byte as the length", [0x4c, 0xab] ++ rep 171 0xab,
    [ins 0x4c ([0x4c, 0xab] ++ rep 171 0xab) (rep 171 0xab) 173, .atEnd]⟩,
  ⟨"GetOp2: 4d 0100 ab ab", [0x4d, 0x01, 0x00, 0xab, 0xab],
    [ins 0x4d [0x4d, 0x01, 0x00, 0xab] [0xab] 4, ins 0xab [0xab] [] 5, .atEnd]⟩,
  ⟨"GetOp2: 51 02aabb ab, the loop never reads cursor 2", [0x51, 0x02, 0xaa, 0xbb, 0xab],
    [ins 0x51 [0x51] [] 1, ins 0x02 [0x02, 0xaa, 0xbb] [0xaa, 0xbb] 4, ins 0xab [0xab] [] 5, .atEnd]⟩,
  ⟨"GetOp2: 61 4e000000, a short length field after an instruction", [0x61, 0x4e, 0x00, 0x00, 0x00],
    [ins 0x61 [0x61] [] 1, .truncated 0x4e .lengthField 2]⟩
]

/-- The results of the loop of `readInstruction` calls from cursor 0, up to and including the first result that is not an instruction. Each instruction moves the cursor forward, so `script.length + 1` calls are enough. -/
def loop (script : List UInt8) : List ReadResult :=
  go (script.length + 1) 0
where
  go : Nat → Nat → List ReadResult
    | 0, _ => []
    | fuel + 1, pc =>
      match readInstruction script pc with
      | .instruction i => .instruction i :: go fuel i.next
      | r => [r]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  if cases.length != 50 || loopCases.length != 8 then
    IO.eprintln s!"FAIL script reader: {cases.length} cases and {loopCases.length} loop cases, expected 50 and 8"
    failures := failures + 1
  for c in cases do
    let got := readInstruction c.script c.pc
    unless got == c.expected do
      IO.eprintln s!"FAIL {c.label}: got {repr got}, expected {repr c.expected}"
      failures := failures + 1
  for c in loopCases do
    let got := loop c.script
    unless got == c.expected do
      IO.eprintln s!"FAIL {c.label}: got {repr got}, expected {repr c.expected}"
      failures := failures + 1
  -- EvalScript resets every local at the start of a call (interpreter.cpp lines 258 to 268).
  -- VerifyScript passes only `stack` to the next call (lines 1424 and 1429).
  -- The prior state has a nonempty altstack, cursors, conditional stack and count.
  -- Its stack holds an empty item, negative zero and a two-byte zero, which stay raw.
  let prior : ExecState :=
    { stack := [[], [0x80], [0, 0]], altstack := [[0xff]], pc := 99, beginCodeHash := 80,
      vfExec := [true, false], opCount := 201 }
  let reset : ExecState :=
    { stack := [[], [0x80], [0, 0]], altstack := [], pc := 0, beginCodeHash := 0,
      vfExec := [], opCount := 0 }
  unless prior.handOff == reset && ExecState.init prior.stack == reset && reset.fExec &&
      !prior.fExec do
    IO.eprintln s!"FAIL script state reset and hand-off: got {repr prior.handOff}, expected {repr reset}"
    failures := failures + 1
  IO.println s!"script reader: {cases.length} cases, {loopCases.length} loop cases, state reset and hand-off, {failures} failures"
  return failures

end KnownAnswers.Script


/-!
## Script numbers and truth values

Runs `ScriptNum.encode`, `decode`, `getint` and `castToBool` through the compiled code.

Every expected byte string and value is written by hand from the byte layout of `CScriptNum` (SOURCES.md, D24, lines 198 to 371) and `CastToBool` (D3, lines 38 to 51).
None is computed by the definitions under test.
Each encoding case also fixes the result of decoding its expected bytes at sizes 4 and 5, with and without the minimal requirement.
The expected result is `overflow` when the expected bytes are longer than the size, and the value otherwise.

The sweep takes the integers of the `creation` test of `scriptnum_tests.cpp` (D44): every `values[i]` and `values[i] ± offsets[j]`.
That test compares `CScriptNum` with a copy of the 0.10.0 code and has no literal expected bytes.
Within ±(2^31 − 1), the operand range of the comment at D24 lines 200 to 207, each integer must survive the round trip.
The round trip is `encode`, then a default-size `decode`.
Outside that range the default-size decode must overflow.
`getint` must match a clamp written out below.
-/

namespace KnownAnswers.ScriptNum

open DogeLib.Script DogeLib.Script.ScriptNum

/-- An expected decode result. `Except` has no equality test, so the cases compare through this type. -/
inductive Expected where
  | ok (n : Int)
  | overflow
  | nonMinimal

/-- Whether a decode result is the expected one. -/
def Expected.matches : Expected → Except DecodeError Int → Bool
  | .ok n, .ok m => n == m
  | .overflow, .error .overflow => true
  | .nonMinimal, .error .nonMinimal => true
  | _, _ => false

/-- The expected decode of the encoding `bytes` of `n` at size `size`, from the length of the expected bytes. -/
def expectedAt (n : Int) (bytes : List UInt8) (size : Nat) : Expected :=
  if bytes.length ≤ size then .ok n else .overflow

/-- Integers and their encodings, hand-derived: magnitude little-endian, sign in the top bit of the last byte. -/
def encodeCases : List (Int × List UInt8) := [
  (0, []),
  (1, [0x01]), (-1, [0x81]),
  (127, [0x7f]), (-127, [0xff]),
  (128, [0x80, 0x00]), (-128, [0x80, 0x80]),
  (255, [0xff, 0x00]), (-255, [0xff, 0x80]),
  (256, [0x00, 0x01]), (-256, [0x00, 0x81]),
  (2147483647, [0xff, 0xff, 0xff, 0x7f]), (-2147483647, [0xff, 0xff, 0xff, 0xff]),
  -- Five-byte results: the magnitude fills the top bit, so one more byte carries the sign.
  (2147483648, [0x00, 0x00, 0x00, 0x80, 0x00]), (-2147483648, [0x00, 0x00, 0x00, 0x80, 0x80]),
  (4294967295, [0xff, 0xff, 0xff, 0xff, 0x00]), (-4294967295, [0xff, 0xff, 0xff, 0xff, 0x80]),
  (4294967296, [0x00, 0x00, 0x00, 0x00, 0x01]),
  (549755813887, [0xff, 0xff, 0xff, 0xff, 0x7f]), (-549755813887, [0xff, 0xff, 0xff, 0xff, 0xff]),
  -- 2^39: six bytes, beyond the size 5 of CHECKLOCKTIMEVERIFY.
  (549755813888, [0x00, 0x00, 0x00, 0x00, 0x80, 0x00])]

/-- Decode cases: a label, the bytes, the minimal requirement, the size and the expected result. -/
def decodeCases : List (String × List UInt8 × Bool × Nat × Expected) := [
  ("empty", [], true, 4, .ok 0),
  ("empty at size 0", [], true, 0, .ok 0),
  ("01 at size 0", [0x01], false, 0, .overflow),
  ("negative zero 80", [0x80], false, 4, .ok 0),
  ("negative zero 80, minimal", [0x80], true, 4, .nonMinimal),
  ("00", [0x00], false, 4, .ok 0),
  ("00, minimal", [0x00], true, 4, .nonMinimal),
  ("0000", [0x00, 0x00], false, 4, .ok 0),
  ("0000, minimal", [0x00, 0x00], true, 4, .nonMinimal),
  ("0080", [0x00, 0x80], false, 4, .ok 0),
  ("0080, minimal", [0x00, 0x80], true, 4, .nonMinimal),
  ("7f00", [0x7f, 0x00], false, 4, .ok 127),
  ("7f00, minimal", [0x7f, 0x00], true, 4, .nonMinimal),
  ("8000, minimal: the top bit of 80 needs the sign byte", [0x80, 0x00], true, 4, .ok 128),
  ("ff00, minimal", [0xff, 0x00], true, 4, .ok 255),
  ("ff80, minimal", [0xff, 0x80], true, 4, .ok (-255)),
  ("ffffff7f, minimal", [0xff, 0xff, 0xff, 0x7f], true, 4, .ok 2147483647),
  ("0000000000 at size 4, minimal: overflow first", [0x00, 0x00, 0x00, 0x00, 0x00], true, 4, .overflow),
  ("0000000000 at size 5, minimal", [0x00, 0x00, 0x00, 0x00, 0x00], true, 5, .nonMinimal),
  ("ffffffffff at size 4", [0xff, 0xff, 0xff, 0xff, 0xff], false, 4, .overflow),
  ("ffffffffff at size 5", [0xff, 0xff, 0xff, 0xff, 0xff], true, 5, .ok (-549755813887)),
  ("0000008080 at size 4", [0x00, 0x00, 0x00, 0x80, 0x80], true, 4, .overflow),
  ("0000008080 at size 5", [0x00, 0x00, 0x00, 0x80, 0x80], true, 5, .ok (-2147483648)),
  ("ffffffff00 at size 5", [0xff, 0xff, 0xff, 0xff, 0x00], true, 5, .ok 4294967295)]

/-- `getint` cases: an integer and its value saturated to `[-2^31, 2^31 - 1]`. -/
def getintCases : List (Int × Int) := [
  (0, 0), (-1, -1),
  (2147483647, 2147483647), (-2147483647, -2147483647),
  (2147483648, 2147483647), (-2147483648, -2147483648), (-2147483649, -2147483648),
  (1099511627776, 2147483647), (-1099511627776, -2147483648)]

/-- `castToBool` cases: a label, the bytes and the expected truth value. -/
def castCases : List (String × List UInt8 × Bool) := [
  ("empty", [], false),
  ("00", [0x00], false),
  ("negative zero 80", [0x80], false),
  ("0080", [0x00, 0x80], false),
  ("000080", [0x00, 0x00, 0x80], false),
  ("600 zero bytes", List.replicate 600 0x00, false),
  ("600 zero bytes and 80", List.replicate 600 0x00 ++ [0x80], false),
  ("01", [0x01], true),
  ("81", [0x81], true),
  ("8000: 80 is not the last byte", [0x80, 0x00], true),
  ("008000", [0x00, 0x80, 0x00], true),
  ("0001", [0x00, 0x01], true),
  ("600 zero bytes and 01", List.replicate 600 0x00 ++ [0x01], true)]

/-- `values` of `scriptnum_tests.cpp` (D44, line 17). -/
def sweepValues : List Int :=
  [0, 1, -2, 127, 128, -255, 256, 2 ^ 15 - 1, -(2 ^ 16), 2 ^ 24 - 1, 2 ^ 31, 1 - 2 ^ 32, 2 ^ 40]

/-- `offsets` of `scriptnum_tests.cpp` (D44, line 19). -/
def sweepOffsets : List Int := [1, 0x79, 0x80, 0x81, 0xFF, 0x7FFF, 0x8000, 0xFFFF, 0x10000]

/-- The integers of the `creation` test (D44, lines 169 to 180). Core runs `values[i]` once for each offset, and here it appears once. -/
def sweep : List Int :=
  sweepValues.flatMap fun v => v :: sweepOffsets.flatMap fun o => [v + o, v - o]

/-- The clamp of `getint`, written out: `INT_MAX` above, `INT_MIN` below. -/
def clamp (n : Int) : Int :=
  if n > 2147483647 then 2147483647 else if n < -2147483648 then -2147483648 else n

/-- Every Script number and truth-value known answer. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  let mut count := 0
  for (n, bytes) in encodeCases do
    count := count + 1
    if encode n != bytes then
      IO.eprintln s!"FAIL scriptnum encode {n}: got {encode n}, expected {bytes}"
      failures := failures + 1
    for size in [4, 5] do
      for req in [false, true] do
        count := count + 1
        if !(expectedAt n bytes size).matches (decode bytes req size) then
          IO.eprintln s!"FAIL scriptnum decode of the encoding of {n} at size {size}, minimal {req}"
          failures := failures + 1
  for (name, bytes, req, size, expected) in decodeCases do
    count := count + 1
    if !expected.matches (decode bytes req size) then
      IO.eprintln s!"FAIL scriptnum decode {name}"
      failures := failures + 1
  for (n, expected) in getintCases do
    count := count + 1
    if getint n != expected then
      IO.eprintln s!"FAIL scriptnum getint {n}: got {getint n}, expected {expected}"
      failures := failures + 1
  for (name, bytes, expected) in castCases do
    count := count + 1
    if castToBool bytes != expected then
      IO.eprintln s!"FAIL castToBool {name}"
      failures := failures + 1
  if sweep.length != 247 then
    IO.eprintln s!"FAIL scriptnum: the sweep has {sweep.length} integers, expected 247"
    failures := failures + 1
  for n in sweep do
    count := count + 1
    let inRange := -2147483647 ≤ n && n ≤ 2147483647
    let ok :=
      if inRange then
        (Expected.ok n).matches (decode (encode n) false) && (Expected.ok n).matches (decode (encode n) true)
      else
        Expected.overflow.matches (decode (encode n) false)
    if !ok || getint n != clamp n then
      IO.eprintln s!"FAIL scriptnum sweep {n}"
      failures := failures + 1
  IO.println s!"scriptnum/castToBool: {count} checks, {failures} failures"
  return failures

end KnownAnswers.ScriptNum



/-!
## Script evaluation

Runs `evalScript`, one `EvalScript` call, through the compiled code.

### Core's script corpus

Each record of `tests/script/corpus/script_tests.jsonl` is a `VerifyScript` call (SOURCES.md, D45 and D46), not one `EvalScript` call.
This test composes two calls of `evalScript` as `VerifyScript` does without its P2SH branch (D3, lines 1409 to 1435).
It runs `scriptSig` on an empty stack, and then `scriptPubKey` on the resulting main stack.
Both calls use `transactionChecker` over the record's spending transaction and input index, with `coreVerifier`.
So every record whose verdict needs an elliptic-curve check is compared, and the count of `signature verifier` results must be zero.
An empty final stack or a false top item gives `EVAL_FALSE`.
The composition is test code. DogeLib does not specify `VerifyScript` yet.

Three cases give an unsupported result instead of a comparison:

- A nonempty witness stack, which design record 0003 reports as unsupported.
- An unsupported result of either call. With `coreVerifier`, a signature opcode never gives one.
- Both calls succeed with a true top item, the P2SH flag is set and `scriptPubKey` is the exact P2SH template (D48, `CScript::IsPayToScriptHash`, lines 204 to 211). Core's verdict then depends on the P2SH branch.

The flags are the record's `effective_flags_mask`.
Every other record must give exactly the record's `expected_error`, where `OK` is acceptance.
The test fails on any disagreement, on a record outside the milestone that does not give unsupported, and when no record is compared.

### Hand cases

Each hand case fixes a script, flags, a caller stack and the expected result: the final main stack, Core's error, or the unsupported reason.
Every expected result is written by hand from `EvalScript` (D3, lines 248 to 1046), the limits of D24 lines 22 to 31, and the encoding of `CScriptNum` (D24, lines 198 to 371).
The expected digests of the hash cases come from Core's `script_tests.json` (D45), not from DogeLib's hash definitions.
The cases cover the limit boundaries, short pushes, unbalanced conditionals, and disabled and reserved opcodes in skipped branches.
They also cover stack underflow, negative zero, the operands of `OP_PICK` and `OP_ROLL`, and unsupported capabilities.
For the numeric opcodes they cover operand order, five-byte results, negative zero and non-minimal operands, `OP_NUMEQUALVERIFY` failure and the bounds of `OP_WITHIN`.
Each hand case runs without a checker, as in stage 2, and again with `baseChecker`.
The two runs expect the same result, except for a case that expects an unsupported signature opcode, which runs only without a checker.
-/

namespace KnownAnswers.ScriptEval

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- The outcome of one corpus record. -/
inductive Outcome where
  | accepted
  | rejected (e : ScriptError)
  | unsupported (reason : String)
  deriving BEq, Repr

/-- The label of an unsupported reason, for the counts. With `transactionChecker`, a signature opcode is unsupported only when it reaches the verifier. -/
def reasonLabel : Unsupported → String
  | .flags _ => "flags"
  | .signatureOpcode _ => "signature verifier"
  | .checkLockTimeVerify => "CHECKLOCKTIMEVERIFY"
  | .checkSequenceVerify => "CHECKSEQUENCEVERIFY"

/-- A `VerifyResult` as a corpus outcome. -/
def outcomeOf : VerifyResult → Outcome
  | .accepted => .accepted
  | .rejected e => .rejected e
  | .unsupported u => .unsupported (reasonLabel u)

/-- The fields of one corpus record that this test reads. -/
structure Record where
  line : Nat
  scriptSig : List UInt8
  scriptPubKey : List UInt8
  flags : UInt32
  expected : String
  witness : Bool
  inside : Bool
  /-- The spending transaction of the record's context, decoded in base mode. -/
  spendTx : DogeLib.Transaction.Transaction
  inputIndex : Nat

/-- Reads one line of `script_tests.jsonl`. -/
def parseRecord (text : String) : Except String Record := do
  let j ← Lean.Json.parse text
  let hex (k : String) : Except String (List UInt8) := do
    return (← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? k).getStr?)).toList
  let classification ← j.getObjVal? "classification"
  let context ← j.getObjVal? "context"
  let spendBytes ← KnownAnswers.Sha256Cavp.parseHex (← (← context.getObjVal? "spending_tx_base_hex").getStr?)
  let spendTx ← match DogeLib.Transaction.Transaction.decodeBaseComplete spendBytes.toList with
    | .ok tx => pure tx
    | .error _ => throw "spending_tx_base_hex does not decode"
  return {
    line := ← (← j.getObjVal? "source_line").getNat?
    scriptSig := ← hex "scriptSig_hex"
    scriptPubKey := ← hex "scriptPubKey_hex"
    flags := (← (← j.getObjVal? "effective_flags_mask").getNat?).toUInt32
    expected := ← (← j.getObjVal? "expected_error").getStr?
    witness := (← (← j.getObjVal? "witness").getArr?).size != 0
    inside := (← (← classification.getObjVal? "milestone").getStr?) == "inside"
    spendTx
    inputIndex := ← (← context.getObjVal? "input_index").getNat? }

/-- The name of an outcome in the corpus's terms. -/
def outcomeName : Outcome → String
  | .accepted => "OK"
  | .rejected e => e.name
  | .unsupported r => s!"unsupported ({r})"

/-- Runs every corpus record. Returns the number of failures. -/
def checkCorpus : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/script_tests.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut agree := 0
  let mut agreeAccepted := 0
  let mut unsupported : List (String × Nat) := [("signature verifier", 0)]
  -- Records with P2SH set and the template as `scriptPubKey`.
  let mut p2shAgree := 0
  let mut p2shVerifier := 0
  -- Records with a lock-time flag set and its opcode in a script.
  let mut lockAgree := 0
  let mut lockUnsupported := 0
  if lines.length != 1193 then
    IO.eprintln s!"FAIL {path}: {lines.length} records, expected 1193"
    failures := failures + 1
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    let got :=
      if r.witness then Outcome.unsupported "witness"
      else
        let checker := transactionChecker r.spendTx r.inputIndex.toUInt32 coreVerifier
        outcomeOf (verifyScript checker r.flags r.scriptSig r.scriptPubKey)
    let p2sh := !r.witness && hasFlag r.flags ScriptFlags.p2sh && isPayToScriptHash r.scriptPubKey
    let lock := !r.witness && unsupportedFlagBits r.flags == 0 &&
      ((hasFlag r.flags ScriptFlags.checkLockTimeVerify && (r.scriptSig.contains 0xb1 || r.scriptPubKey.contains 0xb1)) ||
        (hasFlag r.flags ScriptFlags.checkSequenceVerify && (r.scriptSig.contains 0xb2 || r.scriptPubKey.contains 0xb2)))
    match got with
    | .unsupported reason =>
      if p2sh && reason == "signature verifier" then p2shVerifier := p2shVerifier + 1
      if lock then lockUnsupported := lockUnsupported + 1
      unsupported :=
        if unsupported.any (·.1 == reason) then unsupported.map fun (k, n) => (k, if k == reason then n + 1 else n)
        else unsupported ++ [(reason, 1)]
    | _ =>
      if !r.inside then
        IO.eprintln s!"FAIL script_tests.json:{r.line}: outside the milestone, got {outcomeName got}"
        failures := failures + 1
      else if outcomeName got == r.expected then
        agree := agree + 1
        if p2sh then p2shAgree := p2shAgree + 1
        if lock then lockAgree := lockAgree + 1
        if r.expected == "OK" then agreeAccepted := agreeAccepted + 1
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: got {outcomeName got}, expected {r.expected}"
        failures := failures + 1
  if agree == 0 then
    IO.eprintln "FAIL script corpus: no record compared"
    failures := failures + 1
  if unsupported.any fun (k, n) => k == "signature verifier" && n != 0 then
    IO.eprintln "FAIL script corpus: a record reaches an unavailable verifier"
    failures := failures + 1
  let total := unsupported.foldl (fun acc (_, n) => acc + n) 0
  let detail := ", ".intercalate (unsupported.map fun (k, n) => s!"{k} {n}")
  IO.println s!"script corpus: {lines.length} records, {agree} agree with Core ({agreeAccepted} accepted, {agree - agreeAccepted} rejected), {failures} failures, {total} unsupported: {detail}"
  IO.println s!"script corpus: P2SH template with its flag {p2shAgree} agree, {p2shVerifier} reach the verifier; lock-time opcodes with their flags {lockAgree} agree, {lockUnsupported} unsupported"
  return failures

/-- The expected result of a hand case. -/
inductive Expect where
  /-- Success with this final main stack. -/
  | ok (stack : List (List UInt8))
  /-- Success with this final main stack and separator cursor. -/
  | okSeparator (stack : List (List UInt8)) (beginCodeHash : Nat)
  /-- Core's error. -/
  | rejected (e : ScriptError)
  /-- An unsupported capability. -/
  | unsupported (u : Unsupported)

/-- Whether `r` is the expected result `e`. -/
def Expect.matches : Expect → EvalResult → Bool
  | .ok stack, .ok s => s.stack == stack
  | .okSeparator stack b, .ok s => s.stack == stack && s.beginCodeHash == b
  | .rejected e, .rejected e' => e == e'
  | .unsupported u, .unsupported u' => u == u'
  | _, _ => false

/-- One hand case: a label, flags, a script, a caller stack and the expected result. -/
structure Case where
  label : String
  flags : UInt32
  script : List UInt8
  stack : List (List UInt8)
  expected : Expect

/-- `OP_PUSHDATA2` of `n` bytes `0x01`, for `n < 65536`. -/
def push2 (n : Nat) : List UInt8 := [0x4d, (n % 256).toUInt8, (n / 256).toUInt8] ++ rep n 0x01

/-- A script of exactly 10,000 bytes: 19 pushes of 520 bytes, each dropped, a 41-byte push, dropped, and `OP_1`. -/
def script10000 : List UInt8 :=
  (List.replicate 19 (push2 520 ++ [0x75])).flatten ++ [0x29] ++ rep 41 0x02 ++ [0x75, 0x51]

/-- The stack, numeric and hash opcodes on an empty stack, which give `INVALID_STACK_OPERATION` (D3, lines 478 to 871). -/
def underflowOps : List UInt8 :=
  [0x69, 0x6b, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d,
    0x82, 0x87, 0x88, 0x8b, 0x8c, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e, 0x9f, 0xa0,
    0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa]

/-- The bytes of a hexadecimal string. A bad digit gives no bytes, which no hash case expects. -/
def hex (s : String) : List UInt8 :=
  match KnownAnswers.Sha256Cavp.parseHex s with
  | .ok b => b.toList
  | .error _ => []

/-- The hand cases. -/
def cases : List Case := [
  -- MAX_OPS_PER_SCRIPT (D24 line 25, D3 lines 286 and 287).
  ⟨"201 counted NOPs", 0, rep 201 0x61, [], .ok []⟩,
  ⟨"202 counted NOPs", 0, rep 202 0x61, [], .rejected .opCount⟩,
  ⟨"201 counted, 199 of them skipped", 0, [0x00, 0x63] ++ rep 199 0x61 ++ [0x68], [], .ok []⟩,
  ⟨"202 counted, 200 of them skipped", 0, [0x00, 0x63] ++ rep 200 0x61 ++ [0x68], [], .rejected .opCount⟩,
  ⟨"OP_RESERVED does not count", 0, [0x00, 0x63, 0x50] ++ rep 199 0x61 ++ [0x68], [], .ok []⟩,
  ⟨"pushes and OP_1 to OP_16 do not count", 0, rep 201 0x61 ++ [0x00, 0x51, 0x60, 0x01, 0x07], [],
    .ok [[], [1], [16], [7]]⟩,
  -- MAX_SCRIPT_ELEMENT_SIZE (D24 line 22, D3 lines 282 and 283).
  ⟨"520-byte push", 0, push2 520, [], .ok [rep 520 0x01]⟩,
  ⟨"521-byte push", 0, push2 521, [], .rejected .pushSize⟩,
  ⟨"521-byte push in a skipped branch", 0, [0x00, 0x63] ++ push2 521 ++ [0x68], [], .rejected .pushSize⟩,
  -- The combined stack size (D3 line 1033).
  ⟨"1,000 items", 0, rep 1000 0x51, [], .ok (List.replicate 1000 [1])⟩,
  ⟨"1,001 items", 0, rep 1001 0x51, [], .rejected .stackSize⟩,
  ⟨"1,000 items on both stacks", 0, rep 1000 0x51 ++ [0x6b], [], .ok (List.replicate 999 [1])⟩,
  ⟨"1,001 items on both stacks", 0, rep 1000 0x51 ++ [0x6b, 0x51], [], .rejected .stackSize⟩,
  ⟨"1,001-item caller stack, empty script", 0, [], List.replicate 1001 [], .ok (List.replicate 1001 [])⟩,
  ⟨"1,001-item caller stack, OP_NOP", 0, [0x61], List.replicate 1001 [], .rejected .stackSize⟩,
  -- MAX_SCRIPT_SIZE (D24 line 31, D3 lines 266 and 267), checked before the opcode count.
  ⟨"10,000-byte script", 0, script10000, [], .ok [[1]]⟩,
  ⟨"10,001-byte script", 0, script10000 ++ [0x61], [], .rejected .scriptSize⟩,
  ⟨"10,001 NOPs", 0, rep 10001 0x61, [], .rejected .scriptSize⟩,
  -- Short pushes (D3 lines 280 and 281).
  ⟨"short OP_PUSHDATA1 length", 0, [0x4c], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA1 data", 0, [0x4c, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA2 length", 0, [0x4d, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short OP_PUSHDATA4 length", 0, [0x4e, 0x01, 0x00, 0x00], [], .rejected .badOpcode⟩,
  ⟨"short direct push", 0, [0x02, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short push in a skipped branch", 0, [0x00, 0x63, 0x02, 0x01], [], .rejected .badOpcode⟩,
  ⟨"short push after OP_RETURN is not read", 0, [0x6a, 0x02, 0x01], [], .rejected .opReturn⟩,
  -- Conditionals (D3 lines 437 to 476 and 1042 to 1043).
  ⟨"OP_IF without OP_ENDIF", 0, [0x51, 0x63], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_ELSE alone", 0, [0x67], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_ENDIF alone", 0, [0x68], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_IF on an empty stack", 0, [0x63, 0x68], [], .rejected .unbalancedConditional⟩,
  ⟨"OP_IF on an empty stack in a skipped branch", 0, [0x00, 0x63, 0x63, 0x68, 0x68], [], .ok []⟩,
  ⟨"two OP_ELSE", 0, [0x51, 0x63, 0x52, 0x67, 0x53, 0x67, 0x54, 0x68], [], .ok [[2], [4]]⟩,
  ⟨"OP_NOTIF", 0, [0x00, 0x64, 0x52, 0x67, 0x53, 0x68], [], .ok [[2]]⟩,
  ⟨"nested skipped OP_ELSE", 0, [0x00, 0x63, 0x00, 0x63, 0x67, 0x52, 0x68, 0x68], [], .ok []⟩,
  -- Disabled, reserved and invalid opcodes (D3 lines 289 to 304, 311 and 1028 to 1029).
  ⟨"OP_CAT in a skipped branch", 0, [0x00, 0x63, 0x7e, 0x68], [], .rejected .disabledOpcode⟩,
  ⟨"OP_RSHIFT in a skipped branch", 0, [0x00, 0x63, 0x99, 0x68], [], .rejected .disabledOpcode⟩,
  ⟨"OP_2MUL executed", 0, [0x51, 0x8d], [], .rejected .disabledOpcode⟩,
  ⟨"reserved and invalid opcodes in a skipped branch", 0,
    [0x00, 0x63, 0x50, 0x62, 0x89, 0x8a, 0xba, 0xff, 0x68, 0x51], [], .ok [[1]]⟩,
  ⟨"OP_VERIF in a skipped branch", 0, [0x00, 0x63, 0x65, 0x68], [], .rejected .badOpcode⟩,
  ⟨"OP_VERNOTIF in a skipped branch", 0, [0x00, 0x63, 0x66, 0x68], [], .rejected .badOpcode⟩,
  ⟨"OP_RESERVED executed", 0, [0x50], [], .rejected .badOpcode⟩,
  ⟨"OP_VER executed", 0, [0x62], [], .rejected .badOpcode⟩,
  ⟨"OP_RESERVED1 executed", 0, [0x89], [], .rejected .badOpcode⟩,
  ⟨"0xba executed", 0, [0xba], [], .rejected .badOpcode⟩,
  ⟨"0xff executed", 0, [0xff], [], .rejected .badOpcode⟩,
  ⟨"OP_RETURN in a skipped branch", 0, [0x00, 0x63, 0x6a, 0x68], [], .ok []⟩,
  ⟨"OP_RETURN executed", 0, [0x6a], [], .rejected .opReturn⟩,
  -- Underflow (D3 lines 478 to 738).
  ⟨"OP_FROMALTSTACK on an empty altstack", 0, [0x51, 0x6c], [], .rejected .invalidAltstackOperation⟩,
  ⟨"OP_SWAP on one item", 0, [0x51, 0x7c], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_2ROT on five items", 0, rep 5 0x51 ++ [0x71], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK on one item", 0, [0x00, 0x79], [], .rejected .invalidStackOperation⟩,
  -- Negative zero (D3 lines 38 to 51).
  ⟨"negative zero is false for OP_IF", 0, [0x01, 0x80, 0x63, 0x51, 0x67, 0x52, 0x68], [], .ok [[2]]⟩,
  ⟨"negative zero is false for OP_VERIFY", 0, [0x01, 0x80, 0x69], [], .rejected .verify⟩,
  ⟨"negative zero is false for OP_IFDUP", 0, [0x01, 0x80, 0x73], [], .ok [[0x80]]⟩,
  ⟨"0x0080 is false", 0, [0x02, 0x00, 0x80, 0x73], [], .ok [[0x00, 0x80]]⟩,
  ⟨"0x8000 is true", 0, [0x02, 0x80, 0x00, 0x73], [], .ok [[0x80, 0x00], [0x80, 0x00]]⟩,
  ⟨"negative zero and the empty string differ for OP_EQUAL", 0, [0x00, 0x01, 0x80, 0x87], [], .ok [[]]⟩,
  -- OP_PICK and OP_ROLL (D3 lines 648 to 664).
  ⟨"OP_PICK 1", 0, [0x52, 0x53, 0x51, 0x79], [], .ok [[2], [3], [2]]⟩,
  ⟨"OP_ROLL 1", 0, [0x52, 0x53, 0x51, 0x7a], [], .ok [[3], [2]]⟩,
  ⟨"OP_PICK 0", 0, [0x52, 0x53, 0x00, 0x79], [], .ok [[2], [3], [3]]⟩,
  ⟨"OP_PICK past the bottom", 0, [0x51, 0x51, 0x79], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK -1", 0, [0x51, 0x4f, 0x79], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_PICK with a five-byte operand", 0, [0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x79], [],
    .rejected .unknownError⟩,
  ⟨"OP_ROLL with a nonminimal operand", 0, [0x52, 0x53, 0x02, 0x01, 0x00, 0x7a], [], .ok [[3], [2]]⟩,
  ⟨"OP_PICK with the five-byte operand 2^31", 0, [0x51, 0x51, 0x05, 0x00, 0x00, 0x00, 0x80, 0x00, 0x79], [],
    .rejected .unknownError⟩,
  ⟨"OP_PICK with 2^31 - 1", 0, [0x51, 0x51, 0x04, 0xff, 0xff, 0xff, 0x7f, 0x79], [],
    .rejected .invalidStackOperation⟩,
  -- Other stack operations (D3 lines 502 to 706).
  ⟨"OP_2ROT", 0, [0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x71], [], .ok [[3], [4], [5], [6], [1], [2]]⟩,
  ⟨"OP_2SWAP", 0, [0x51, 0x52, 0x53, 0x54, 0x72], [], .ok [[3], [4], [1], [2]]⟩,
  ⟨"OP_ROT", 0, [0x51, 0x52, 0x53, 0x7b], [], .ok [[2], [3], [1]]⟩,
  ⟨"OP_TUCK", 0, [0x51, 0x52, 0x7d], [], .ok [[2], [1], [2]]⟩,
  ⟨"OP_DEPTH", 0, [0x51, 0x74], [], .ok [[1], [1]]⟩,
  ⟨"OP_DEPTH of an empty stack", 0, [0x74], [], .ok [[]]⟩,
  ⟨"OP_SIZE", 0, [0x02, 0x01, 0x02, 0x82], [], .ok [[1, 2], [2]]⟩,
  ⟨"OP_SIZE of 128 bytes", 0, [0x4c, 0x80] ++ rep 128 0x00 ++ [0x82], [], .ok [rep 128 0x00, [0x80, 0x00]]⟩,
  ⟨"OP_1NEGATE", 0, [0x4f], [], .ok [[0x81]]⟩,
  ⟨"altstack round trip", 0, [0x51, 0x52, 0x6b, 0x53, 0x6c], [], .ok [[1], [3], [2]]⟩,
  ⟨"OP_EQUALVERIFY", 0, [0x51, 0x51, 0x88], [], .ok []⟩,
  ⟨"OP_EQUALVERIFY fails", 0, [0x51, 0x52, 0x88], [], .rejected .equalVerify⟩,
  ⟨"OP_CODESEPARATOR", 0, [0x51, 0xab, 0x51], [], .okSeparator [[1], [1]] 2⟩,
  ⟨"OP_CODESEPARATOR in a skipped branch", 0, [0x00, 0x63, 0xab, 0x68], [], .okSeparator [] 0⟩,
  -- NOPs and flags (D3 lines 347 to 435).
  ⟨"OP_NOP1 to OP_NOP10 without their flags", 0, [0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9], [],
    .ok []⟩,
  ⟨"OP_CHECKLOCKTIMEVERIFY with its flag", ScriptFlags.checkLockTimeVerify, [0x51, 0xb1], [],
    .unsupported .checkLockTimeVerify⟩,
  ⟨"OP_CHECKSEQUENCEVERIFY with its flag", ScriptFlags.checkSequenceVerify, [0x51, 0xb2], [],
    .unsupported .checkSequenceVerify⟩,
  ⟨"OP_CHECKLOCKTIMEVERIFY with its flag, skipped", ScriptFlags.checkLockTimeVerify, [0x00, 0x63, 0xb1, 0x68], [],
    .ok []⟩,
  ⟨"all seven supported flags", 0x061f, [0x51], [], .ok [[1]]⟩,
  ⟨"MINIMALDATA is unsupported", ScriptFlags.minimalData, [0x51], [], .unsupported (.flags 0x0040)⟩,
  ⟨"unsupported flags before the script size", ScriptFlags.p2sh ||| ScriptFlags.cleanStack ||| 0x10000,
    rep 10001 0x61, [], .unsupported (.flags 0x10100)⟩,
  -- Numeric opcodes (D3, lines 744 to 841, and D24, lines 198 to 371).
  ⟨"OP_ADD", 0, [0x51, 0x52, 0x93], [], .ok [[3]]⟩,
  ⟨"OP_SUB subtracts the top item", 0, [0x51, 0x52, 0x94], [], .ok [[0x81]]⟩,
  ⟨"OP_LESSTHAN 1 2", 0, [0x51, 0x52, 0x9f], [], .ok [[1]]⟩,
  ⟨"OP_LESSTHAN 2 1", 0, [0x52, 0x51, 0x9f], [], .ok [[]]⟩,
  ⟨"OP_GREATERTHAN -1 1", 0, [0x4f, 0x51, 0xa0], [], .ok [[]]⟩,
  ⟨"OP_LESSTHANOREQUAL 2 2", 0, [0x52, 0x52, 0xa1], [], .ok [[1]]⟩,
  ⟨"OP_GREATERTHANOREQUAL 1 2", 0, [0x51, 0x52, 0xa2], [], .ok [[]]⟩,
  ⟨"OP_MIN", 0, [0x51, 0x52, 0xa3], [], .ok [[1]]⟩,
  ⟨"OP_MAX", 0, [0x51, 0x52, 0xa4], [], .ok [[2]]⟩,
  ⟨"OP_NUMNOTEQUAL", 0, [0x51, 0x52, 0x9e], [], .ok [[1]]⟩,
  ⟨"OP_NEGATE", 0, [0x52, 0x8f], [], .ok [[0x82]]⟩,
  ⟨"OP_ABS -2", 0, [0x01, 0x82, 0x90], [], .ok [[2]]⟩,
  ⟨"OP_NOT 2", 0, [0x52, 0x91], [], .ok [[]]⟩,
  ⟨"OP_0NOTEQUAL 2", 0, [0x52, 0x92], [], .ok [[1]]⟩,
  ⟨"OP_1SUB 1", 0, [0x51, 0x8c], [], .ok [[]]⟩,
  -- Five-byte results are pushed, and a later numeric use gives UNKNOWN_ERROR.
  ⟨"OP_1ADD of 2^31 - 1", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b], [], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"OP_ADD of 2^31 - 1 twice", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x76, 0x93], [],
    .ok [[0xfe, 0xff, 0xff, 0xff, 0x00]]⟩,
  ⟨"OP_1SUB of -(2^31 - 1)", 0, [0x04, 0xff, 0xff, 0xff, 0xff, 0x8c], [], .ok [[0x00, 0x00, 0x00, 0x80, 0x80]]⟩,
  ⟨"OP_SUB of -(2^31 - 1) and 2^31 - 1", 0, [0x04, 0xff, 0xff, 0xff, 0xff, 0x04, 0xff, 0xff, 0xff, 0x7f, 0x94], [],
    .ok [[0xfe, 0xff, 0xff, 0xff, 0x80]]⟩,
  ⟨"a five-byte result fails a later OP_1ADD", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b, 0x8b], [],
    .rejected .unknownError⟩,
  ⟨"a five-byte result passes OP_SIZE", 0, [0x04, 0xff, 0xff, 0xff, 0x7f, 0x8b, 0x82], [],
    .ok [[0x00, 0x00, 0x00, 0x80, 0x00], [5]]⟩,
  ⟨"OP_1ADD on a five-byte operand", 0, [0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8b], [], .rejected .unknownError⟩,
  ⟨"OP_ADD on a five-byte top operand", 0, [0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x93], [],
    .rejected .unknownError⟩,
  ⟨"OP_ADD on a five-byte second operand", 0, [0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x51, 0x93], [],
    .rejected .unknownError⟩,
  ⟨"OP_ADD on one item", 0, [0x51, 0x93], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_1ADD on a five-byte operand in a skipped branch", 0, [0x00, 0x63, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x68],
    [], .ok []⟩,
  -- Negative zero and non-minimal operands, accepted without MINIMALDATA.
  ⟨"OP_1ADD of negative zero", 0, [0x01, 0x80, 0x8b], [], .ok [[1]]⟩,
  ⟨"OP_NOT of negative zero", 0, [0x01, 0x80, 0x91], [], .ok [[1]]⟩,
  ⟨"OP_ABS of negative zero", 0, [0x01, 0x80, 0x90], [], .ok [[]]⟩,
  ⟨"OP_NEGATE of negative zero", 0, [0x01, 0x80, 0x8f], [], .ok [[]]⟩,
  ⟨"OP_0NOTEQUAL of 0x0080", 0, [0x02, 0x00, 0x80, 0x92], [], .ok [[]]⟩,
  ⟨"OP_NUMEQUAL of negative zero and 0", 0, [0x01, 0x80, 0x00, 0x9c], [], .ok [[1]]⟩,
  ⟨"OP_BOOLAND of negative zero and 1", 0, [0x01, 0x80, 0x51, 0x9a], [], .ok [[]]⟩,
  ⟨"OP_BOOLOR of negative zero and 1", 0, [0x01, 0x80, 0x51, 0x9b], [], .ok [[1]]⟩,
  ⟨"OP_NUMEQUAL of 2 and 0x0200", 0, [0x52, 0x02, 0x02, 0x00, 0x9c], [], .ok [[1]]⟩,
  -- OP_NUMEQUALVERIFY (D3, lines 803 and 817 to 823).
  ⟨"OP_NUMEQUALVERIFY of 2 and 0x0200", 0, [0x52, 0x02, 0x02, 0x00, 0x9d], [], .ok []⟩,
  ⟨"OP_NUMEQUALVERIFY fails", 0, [0x51, 0x52, 0x9d], [], .rejected .numEqualVerify⟩,
  ⟨"OP_NUMEQUALVERIFY of 0 and negative zero", 0, [0x51, 0x00, 0x01, 0x80, 0x9d], [], .ok [[1]]⟩,
  -- OP_WITHIN (D3, lines 827 to 841): x lo hi gives lo <= x < hi.
  ⟨"OP_WITHIN at the lower bound", 0, [0x00, 0x00, 0x51, 0xa5], [], .ok [[1]]⟩,
  ⟨"OP_WITHIN at the upper bound", 0, [0x51, 0x00, 0x51, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN with lo above hi", 0, [0x51, 0x52, 0x00, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN with negative bounds", 0, [0x4f, 0x4f, 0x00, 0xa5], [], .ok [[1]]⟩,
  ⟨"OP_WITHIN below the lower bound", 0, [0x4f, 0x00, 0x51, 0xa5], [], .ok [[]]⟩,
  ⟨"OP_WITHIN on two items", 0, [0x51, 0x51, 0xa5], [], .rejected .invalidStackOperation⟩,
  ⟨"OP_WITHIN on a five-byte bound", 0, [0x51, 0x51, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa5], [],
    .rejected .unknownError⟩,
  -- Hash opcodes on the empty input (D3, lines 847 to 871). The digests are those of Core's script_tests.json (D45),
  -- lines 216, 219, 222, 227 and 230.
  ⟨"OP_RIPEMD160 of the empty input", 0, [0x00, 0xa6], [], .ok [hex "9c1185a5c5e9fc54612808977ee8f548b2258d31"]⟩,
  ⟨"OP_SHA1 of the empty input", 0, [0x00, 0xa7], [], .ok [hex "da39a3ee5e6b4b0d3255bfef95601890afd80709"]⟩,
  ⟨"OP_SHA256 of the empty input", 0, [0x00, 0xa8], [],
    .ok [hex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"]⟩,
  ⟨"OP_HASH160 of the empty input", 0, [0x00, 0xa9], [], .ok [hex "b472a266d0bd89c13706a4132ccfb16f7c3b9fcb"]⟩,
  ⟨"OP_HASH256 of the empty input", 0, [0x00, 0xaa], [],
    .ok [hex "5df6e0e2761359d30a8275058e299fcc0381534545f55cf43e41983f5d4c9456"]⟩,
  ⟨"OP_HASH160 is OP_RIPEMD160 of OP_SHA256", 0, [0x01, 0x61, 0x76, 0xa9, 0x7c, 0xa8, 0xa6, 0x87], [], .ok [[1]]⟩,
  ⟨"OP_HASH256 is OP_SHA256 twice", 0, [0x01, 0x61, 0x76, 0xaa, 0x7c, 0xa8, 0xa8, 0x87], [], .ok [[1]]⟩,
  -- Capabilities of later stages.
  ⟨"OP_CHECKSIG executed", 0, [0xac], [], .unsupported (.signatureOpcode 0xac)⟩,
  ⟨"later-stage opcodes in a skipped branch", 0, [0x00, 0x63, 0x93, 0xa5, 0xa9, 0xac, 0xaf, 0x68], [], .ok []⟩
]

/-- Runs every hand case. Returns the number of failures. -/
def checkCases : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript none c.flags c.script c.stack
    unless c.expected.matches got do
      IO.eprintln s!"FAIL script eval {c.label}: got {repr got}"
      failures := failures + 1
    -- Without a checker these opcodes are unsupported. `KnownAnswers.ScriptVerify` covers them with `baseChecker`.
    let needsChecker := match c.expected with
      | .unsupported (.signatureOpcode _) | .unsupported .checkLockTimeVerify | .unsupported .checkSequenceVerify => true
      | _ => false
    unless needsChecker do
      let got := evalScript (some baseChecker) c.flags c.script c.stack
      unless c.expected.matches got do
        IO.eprintln s!"FAIL script eval {c.label} with baseChecker: got {repr got}"
        failures := failures + 1
  for op in underflowOps do
    for checker in [none, some baseChecker] do
      let got := evalScript checker 0 [op] []
      unless got == .rejected .invalidStackOperation do
        IO.eprintln s!"FAIL script eval underflow of {op}: got {repr got}"
        failures := failures + 1
  unless script10000.length == 10000 do
    IO.eprintln s!"FAIL script eval: the 10,000-byte script has {script10000.length} bytes"
    failures := failures + 1
  let table ← IO.FS.readFile "harness/core/script_error_names.inc"
  let names := table.splitOn "\n" |>.filterMap fun line =>
    if line.startsWith "SCRIPT_ERROR(" then (line.splitOn "\"")[1]? else none
  unless names == "OK" :: ScriptError.all.map ScriptError.name do
    IO.eprintln "FAIL Script error names: the Core table and Lean names differ"
    failures := failures + 1
  IO.println s!"script eval: {cases.length} hand cases, {underflowOps.length} underflow cases, {failures} failures"
  return failures

/-- Runs the corpus and the hand cases. Returns the number of failures. -/
def check : IO Nat := do
  return (← checkCases) + (← checkCorpus)

end KnownAnswers.ScriptEval


namespace KnownAnswers.SignatureCode

open DogeLib.Script

/--
All sixteen cases of Core's `script_FindAndDelete` (D46), in source order, as input, pattern, output and count.
Copied from Dogecoin Core `e0a1c157791544e818c901bd9341896965afbf9d`, `src/test/script_tests.cpp`, under the MIT licence.
The opcode constructors are expanded to their exact bytes.
The upstream licence is in `LICENSES/dogecoin-core-MIT.txt`.
-/
def coreCases : List (String × String × String × Nat) := [
  ("5152", "", "5152", 0),
  ("515253", "52", "5153", 1),
  ("535153535453", "53", "5154", 4),
  ("0302ff03", "0302ff03", "", 1),
  ("0302ff030302ff03", "0302ff03", "", 2),
  ("0302ff030302ff03", "02", "0302ff030302ff03", 0),
  ("0302ff030302ff03", "ff", "0302ff030302ff03", 0),
  ("0302ff030302ff03", "03", "02ff0302ff03", 2),
  ("02feed5169", "feed51", "02feed5169", 0),
  ("02feed5169", "02feed51", "69", 1),
  ("516902feed5169", "feed51", "516902feed5169", 0),
  ("516902feed5169", "02feed51", "516969", 1),
  ("00005151", "0051", "0051", 1),
  ("000051005151", "0051", "0051", 2),
  ("0003feed", "03feed", "00", 1),
  ("0003feed", "00", "03feed", 1)]

/-- Malformed suffix cases derived from D24's deletion loop and failed `GetOp2` reads. -/
def tailCases : List (String × String × String × Nat) := [
  ("514c", "51", "4c", 1),
  ("514d01", "51", "4d01", 1),
  ("514e010203", "51", "4e010203", 1),
  ("514c02aa", "51", "4c02aa", 1),
  ("514d0200aa", "51", "4d0200aa", 1),
  ("514e02000000aa", "51", "4e02000000aa", 1),
  ("4c02aa51", "51", "4c02aa51", 0),
  ("4c03aa51", "51", "4c03aa51", 0)]

/-- Push headers at every size transition, derived from Core's vector overload (D24, lines 437 to 464). -/
def pushCases : List (Nat × List UInt8) := [
  (0, [0x00]), (1, [0x01]), (75, [0x4b]), (76, [0x4c, 0x4c]),
  (255, [0x4c, 0xff]), (256, [0x4d, 0x00, 0x01]),
  (65535, [0x4d, 0xff, 0xff]), (65536, [0x4e, 0x00, 0x00, 0x01, 0x00])]

/-- Run Core's complete deletion test, malformed suffix cases, push boundaries and signature-code preparation. -/
def check : IO Nat := do
  let mut failures := 0
  unless coreCases.length == 16 do
    throw (IO.userError "FindAndDelete corpus must contain sixteen cases")
  for (s, b, out, count) in coreCases ++ tailCases do
    let .ok sBytes := Sha256Cavp.parseHex s | throw (IO.userError "invalid input hex")
    let .ok bBytes := Sha256Cavp.parseHex b | throw (IO.userError "invalid pattern hex")
    let .ok outBytes := Sha256Cavp.parseHex out | throw (IO.userError "invalid output hex")
    let got := DogeLib.Transaction.findAndDelete sBytes.toList bBytes.toList
    unless got == (outBytes.toList, count) do
      IO.eprintln s!"FAIL FindAndDelete {s} / {b}: {repr got}"
      failures := failures + 1
  for (n, header) in pushCases do
    let data := List.replicate n (0xab : UInt8)
    let expected := header ++ data
    unless pushEncoding data == expected do
      IO.eprintln s!"FAIL push encoding at {n} bytes"
      failures := failures + 1
    let got := readInstruction (pushEncoding data ++ [0x61]) 0
    let expectedRead := ReadResult.instruction ⟨header.head!, expected, data, expected.length⟩
    unless got == expectedRead do
      IO.eprintln s!"FAIL push reader at {n} bytes"
      failures := failures + 1
  -- Vector construction never substitutes OP_1 or OP_1NEGATE (D24).
  unless pushEncoding [0x01] == [0x01, 0x01] && pushEncoding [0x81] == [0x01, 0x81] do
    IO.eprintln "FAIL single-byte vector push"
    failures := failures + 1
  -- Stack signature suffix [01, 02] has 02 nearest the top (D3, stacktop(-isig-k)).
  -- The script prefix before cursor 2 stays outside the selected code.
  let script := [0x61, 0xab, 0x01, 0x01, 0xab, 0x02, 0x01, 0x02, 0x01, 0x02, 0x4c]
  let first := effectiveScriptCode script 2 [[0x02]]
  let both := effectiveScriptCode script 2 [[0x02], [0x01]]
  unless first == [0x01, 0x01, 0xab, 0x02, 0x01, 0x02, 0x4c] &&
      both == [0xab, 0x02, 0x01, 0x02, 0x4c] &&
      both == effectiveScriptCode first 0 [[0x01]] do
    IO.eprintln "FAIL multisig signature visitation, retained payload or malformed suffix"
    failures := failures + 1
  unless effectiveScriptCode [0x00, 0x61, 0x00] 0 [[]] == [0x61] &&
      effectiveScriptCode script 2 [] == script.drop 2 &&
      effectiveScriptCode script 99 [[0x01]] == [] do
    IO.eprintln "FAIL empty signature or suffix selection"
    failures := failures + 1
  IO.println s!"signature code: 16 Core deletion cases, 8 malformed tails, 8 push boundaries, preparation cases, {failures} failures"
  return failures

end KnownAnswers.SignatureCode


/-!
## Signature and public-key encoding

Runs the encoding checks of `DogeLib.Script.SignatureEncoding` through the compiled code.

### Core's script corpus

The test selects every record of `tests/script/corpus/script_tests.jsonl` (SOURCES.md, D45 and D46) with these properties:

- The record is inside the milestone, and its witness stack is empty.
- Its `scriptPubKey` is one direct push, opcode `0x00` to `0x4b`, then `OP_CHECKSIG` (`0xac`), optionally followed by `OP_NOT` (`0x91`).

The selected records are the P2PK and P2PK NOT records.
The test runs the record's `scriptSig` with `evalScript` and the record's `effective_flags_mask`, and takes the top stack item as the signature.
The pushed bytes of `scriptPubKey` are the public key.
`OP_CHECKSIG` runs `CheckSignatureEncoding` and then `CheckPubKeyEncoding` before it verifies anything (D3, line 898).
So each selected record expects one of these outcomes:

- `SIG_DER`, `SIG_HIGH_S`, `SIG_HASHTYPE` or `PUBKEYTYPE`: the two checks, in Core's order, give exactly that error.
- `OK` or `EVAL_FALSE`: both checks pass.

The test skips and counts a selected record with any other expected error, and one whose `scriptSig` does not give a nonempty stack.
The expected outcome is the record's, never a DogeLib result.
The test fails on any disagreement, and when no record of one of the four errors is compared.
Multisig records are not selected here. The script corpus test compares them through the evaluator.

### Hand cases

Every expected result is written by hand from `IsValidSignatureEncoding` and the other checks (D3, lines 66 to 223), the lax parser (D50, lines 27 to 166) and the order constants (D53, lines 13 to 27).
None is computed by the definitions under test.
The cases cover each strict-DER rule, and the lax parser's length forms, trailing bytes and overflows.
They also cover the LOW_S bound and the overflow case of design record 0003, section 5.
The rest cover the order of the three signature errors, the hash types and the public-key shapes.
-/

namespace KnownAnswers.SignatureEncoding

open DogeLib.Script

/-- `n` copies of the byte `b`. -/
def rep (n : Nat) (b : UInt8) : List UInt8 := List.replicate n b

/-- The bytes of a hexadecimal string. A bad digit gives no bytes, which no case expects. -/
def hex (s : String) : List UInt8 := KnownAnswers.ScriptEval.hex s

/-- The name of a check result: `OK`, or Core's error name. -/
def resultName : Except ScriptError Unit → String
  | .ok () => "OK"
  | .error e => e.name

/-- The public key of a P2PK or P2PK NOT `scriptPubKey`: one push of opcode `0x00` to `0x4b`, then `OP_CHECKSIG`, optionally then `OP_NOT`. -/
def p2pkKey : List UInt8 → Option (List UInt8)
  | [] => none
  | op :: rest =>
    let n := op.toNat
    let key := rest.take n
    let tail := rest.drop n
    if n ≤ 0x4b && key.length == n && (tail == [0xac] || tail == [0xac, 0x91]) then some key else none

/-- The result of `CheckSignatureEncoding` and then `CheckPubKeyEncoding`, as `OP_CHECKSIG` runs them (D3, line 898). -/
def checkBoth (sig key : List UInt8) (flags : UInt32) : String :=
  match checkSignatureEncoding sig flags with
  | .error e => e.name
  | .ok () => resultName (checkPubKeyEncoding key flags)

/-- The four encoding errors. -/
def encodingErrors : List String := ["SIG_DER", "SIG_HIGH_S", "SIG_HASHTYPE", "PUBKEYTYPE"]

/-- Runs the selected corpus records. Returns the number of failures. -/
def checkCorpus : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/script_tests.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut selected := 0
  let mut passes := 0
  let mut skipped := 0
  let mut errors : List (String × Nat) := encodingErrors.map (·, 0)
  for text in lines do
    let r ← match KnownAnswers.ScriptEval.parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if !r.inside || r.witness then continue
    let some key := p2pkKey r.scriptPubKey | continue
    selected := selected + 1
    let sig? := match evalScript none r.flags r.scriptSig [] with
      | .ok s => s.stack.getLast?
      | _ => none
    let some sig := sig? | skipped := skipped + 1; continue
    let got := checkBoth sig key r.flags
    if encodingErrors.contains r.expected then
      if got == r.expected then
        errors := errors.map fun (k, n) => (k, if k == r.expected then n + 1 else n)
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: encoding checks give {got}, expected {r.expected}"
        failures := failures + 1
    else if r.expected == "OK" || r.expected == "EVAL_FALSE" then
      if got == "OK" then passes := passes + 1
      else
        IO.eprintln s!"FAIL script_tests.json:{r.line}: encoding checks give {got}, expected both to pass ({r.expected})"
        failures := failures + 1
    else skipped := skipped + 1
  for (k, n) in errors do
    if n == 0 then
      IO.eprintln s!"FAIL signature encoding corpus: no {k} record compared"
      failures := failures + 1
  let detail := ", ".intercalate (errors.map fun (k, n) => s!"{k} {n}")
  IO.println s!"signature encoding corpus: {selected} P2PK records, {passes} pass both checks, {detail}, {skipped} skipped, {failures} failures"
  return failures

/-- The secp256k1 group order `n`, written out from D53 lines 13 to 16. -/
def orderBytes : List UInt8 := hex "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
/-- `n − 1`. -/
def orderMinusOneBytes : List UInt8 := hex "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140"
/-- Half the order, `⌊n/2⌋`, written out from D53 lines 24 to 27. -/
def halfBytes : List UInt8 := hex "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0"
/-- `⌊n/2⌋ + 1`. -/
def halfPlusOneBytes : List UInt8 := hex "7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A1"

/-- A strict-DER signature with R = 1, S = 1 and hash type `0x01`. -/
def basic : List UInt8 := hex "300602010102010101"
/-- Strict DER with R = 1, S = `⌊n/2⌋ + 1`, a high S, and hash type `0x01`. -/
def highS : List UInt8 := hex "30250201010220" ++ halfPlusOneBytes ++ [0x01]

/-- The `isValidSignatureEncoding` cases: label, bytes, expected result. -/
def derCases : List (String × List UInt8 × Bool) := [
  ("R = 1, S = 1, 9 bytes", basic, true),
  ("8 bytes", hex "3005020101020001", false),
  ("73 bytes, R and S of 33 bytes", hex "3046022100" ++ rep 32 0xff ++ hex "02210080" ++ rep 31 0x00 ++ [0x01], true),
  ("74 bytes", hex "3047022200" ++ rep 33 0xff ++ hex "02210080" ++ rep 31 0x00 ++ [0x01], false),
  ("compound tag 0x31", hex "310602010102010101", false),
  ("total length one more", hex "300702010102010101", false),
  ("total length one less", hex "300502010102010101", false),
  ("R length past the end", hex "300602040102010101", false),
  ("trailing byte: lengths do not add up", hex "30070201010201010101", false),
  ("R tag 0x03", hex "300603010102010101", false),
  ("S tag 0x03", hex "300602010103010101", false),
  ("zero-length R", hex "300602000202010101", false),
  ("zero-length S", hex "300602020101020001", false),
  ("negative R", hex "300602018102010101", false),
  ("negative S", hex "300602010102018101", false),
  ("excess R padding", hex "30070202000102010101", false),
  ("required R padding", hex "30070202008002010101", true),
  ("R = 0, one zero byte", hex "300602010002010101", true),
  ("excess S padding", hex "30070201010202000101", false),
  ("required S padding", hex "30070201010202008001", true),
  ("empty", [], false)]

/-- The `parseDerLax` cases, on bytes without a hash type: label, bytes, expected result. -/
def laxCases : List (String × List UInt8 × Option (Nat × Nat)) := [
  ("R = 1, S = 2", hex "3006020101020102", some (1, 2)),
  ("empty", [], none),
  ("sequence tag 0x31", hex "3106020101020102", none),
  ("sequence length ignored", hex "3000020101020102", some (1, 2)),
  ("long-form sequence length", hex "308106020101020102", some (1, 2)),
  ("long-form sequence length 0x80, no bytes", hex "3080020101020102", some (1, 2)),
  ("long-form sequence length past the end", hex "30850201", none),
  ("long-form R length with leading zeros", hex "30000282000105020107", some (5, 7)),
  ("long-form R length of 8 bytes", hex "3000028801" ++ rep 7 0x00 ++ hex "0101020102", none),
  ("R length past the end", hex "3006020501020102", none),
  ("missing S", hex "3003020101", none),
  ("S tag 0x03", hex "3006020101030102", none),
  ("trailing bytes ignored", hex "3006020101020102ffff", some (1, 2)),
  ("negative R, unsigned value", hex "3006020181020102", some (0x81, 2)),
  ("excess R padding", hex "300702020001020102", some (1, 2)),
  ("zero-length R", hex "30050200020102", some (0, 2)),
  ("R = n − 1 with a leading zero", hex "3026022100" ++ orderMinusOneBytes ++ hex "020101",
    some (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140, 1)),
  ("R = n overflows", hex "30250220" ++ orderBytes ++ hex "020101", some (0, 0)),
  ("S = n overflows", hex "3025020101" ++ [0x02, 0x20] ++ orderBytes, some (0, 0)),
  ("R of 33 significant bytes overflows", hex "3026022101" ++ rep 32 0x00 ++ hex "020101", some (0, 0)),
  ("R of 32 bytes 0xff and a leading zero overflows", hex "3026022100" ++ rep 32 0xff ++ hex "020101", some (0, 0))]

/-- The `laxIntegerLength` cases at position 0 with an 8-byte `size_t`: label, bytes, expected length and next position.
They test the count of significant bytes and the skipped leading zeros of D50, lines 72 to 77. -/
def lengthCases : List (String × List UInt8 × Option (Nat × Nat)) := [
  ("seven significant bytes", hex "8701" ++ rep 6 0x00, some (0x1000000000000, 8)),
  ("eight significant bytes", hex "8801" ++ rep 7 0x00, none),
  ("eight bytes, seven of them leading zeros", hex "88" ++ rep 7 0x00 ++ [0x01], some (1, 9))]

/-- The `checkLowS` cases, on bytes without a hash type: label, bytes, expected result. -/
def lowSCases : List (String × List UInt8 × Bool) := [
  ("S = ⌊n/2⌋", hex "30250201010220" ++ halfBytes, true),
  ("S = ⌊n/2⌋ + 1", hex "30250201010220" ++ halfPlusOneBytes, false),
  ("S = 1", hex "3006020101020101", true),
  ("not parseable", hex "3106020101020101", false),
  ("overflow: R = 2^256 − 1 and S = 2^255 − 1",
    hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff, true)]

/-- The flag sets of the cases. -/
def derSig := ScriptFlags.derSig
def lowS := ScriptFlags.lowS
def strictEnc := ScriptFlags.strictEnc
def allEnc := ScriptFlags.derSig ||| ScriptFlags.lowS ||| ScriptFlags.strictEnc

/-- The `checkSignatureEncoding` cases: label, signature, flags, expected result. -/
def sigCases : List (String × List UInt8 × UInt32 × String) := [
  ("empty, no flags", [], 0, "OK"),
  ("empty, all encoding flags", [], allEnc, "OK"),
  ("not DER, no flags", hex "300603010102010101", 0, "OK"),
  ("not DER, DERSIG", hex "300603010102010101", derSig, "SIG_DER"),
  ("not DER, LOW_S", hex "300603010102010101", lowS, "SIG_DER"),
  ("not DER, STRICTENC", hex "300603010102010101", strictEnc, "SIG_DER"),
  ("high S, LOW_S", highS, lowS, "SIG_HIGH_S"),
  ("high S, DERSIG", highS, derSig, "OK"),
  ("high S, STRICTENC", highS, strictEnc, "OK"),
  ("hash type 0x00, STRICTENC", hex "300602010102010100", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x00, DERSIG", hex "300602010102010100", derSig, "OK"),
  ("hash type 0x00, LOW_S", hex "300602010102010100", lowS, "OK"),
  ("not DER and hash type 0x00, STRICTENC", hex "300603010102010100", strictEnc, "SIG_DER"),
  ("high S and hash type 0x00, LOW_S and STRICTENC",
    hex "30250201010220" ++ halfPlusOneBytes ++ [0x00], lowS ||| strictEnc, "SIG_HIGH_S"),
  ("overflow example, all encoding flags",
    hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff ++ [0x01], allEnc, "OK"),
  ("hash type 0x01", basic, strictEnc, "OK"),
  ("hash type 0x02", hex "300602010102010102", strictEnc, "OK"),
  ("hash type 0x03", hex "300602010102010103", strictEnc, "OK"),
  ("hash type 0x04", hex "300602010102010104", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x81", hex "300602010102010181", strictEnc, "OK"),
  ("hash type 0x83", hex "300602010102010183", strictEnc, "OK"),
  ("hash type 0x84", hex "300602010102010184", strictEnc, "SIG_HASHTYPE"),
  ("hash type 0x80", hex "300602010102010180", strictEnc, "SIG_HASHTYPE")]

/-- The public-key cases: label, key, flags, expected `checkPubKeyEncoding` result, expected `isValidPubKey`. -/
def keyCases : List (String × List UInt8 × UInt32 × String × Bool) := [
  ("compressed 0x02", 0x02 :: rep 32 0x11, strictEnc, "OK", true),
  ("compressed 0x03", 0x03 :: rep 32 0x11, strictEnc, "OK", true),
  ("uncompressed 0x04", 0x04 :: rep 64 0x11, strictEnc, "OK", true),
  ("hybrid 0x06", 0x06 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", true),
  ("hybrid 0x07", 0x07 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", true),
  ("hybrid 0x06, no flags", 0x06 :: rep 64 0x11, 0, "OK", true),
  ("header 0x05", 0x05 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x02 with 32 bytes", 0x02 :: rep 31 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x02 with 65 bytes", 0x02 :: rep 64 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x04 with 33 bytes", 0x04 :: rep 32 0x11, strictEnc, "PUBKEYTYPE", false),
  ("0x04 with 64 bytes", 0x04 :: rep 63 0x11, strictEnc, "PUBKEYTYPE", false),
  ("empty", [], strictEnc, "PUBKEYTYPE", false),
  ("empty, no flags", [], 0, "OK", false)]

/-- Every encoding known answer. Returns the number of failures. -/
def check : IO Nat := do
  let corpusFailures ← checkCorpus
  let mut failures := 0
  let mut count := 0
  for (label, bytes, expected) in derCases do
    count := count + 1
    if isValidSignatureEncoding bytes != expected then
      IO.eprintln s!"FAIL isValidSignatureEncoding {label}: expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in laxCases do
    count := count + 1
    if parseDerLax bytes != expected then
      IO.eprintln s!"FAIL parseDerLax {label}: got {parseDerLax bytes}, expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in lengthCases do
    count := count + 1
    if laxIntegerLength 8 bytes 0 != expected then
      IO.eprintln s!"FAIL laxIntegerLength {label}: got {laxIntegerLength 8 bytes 0}, expected {expected}"
      failures := failures + 1
  for (label, bytes, expected) in lowSCases do
    count := count + 1
    if checkLowS bytes != expected then
      IO.eprintln s!"FAIL checkLowS {label}: expected {expected}"
      failures := failures + 1
  for (label, sig, flags, expected) in sigCases do
    count := count + 1
    let got := resultName (checkSignatureEncoding sig flags)
    if got != expected then
      IO.eprintln s!"FAIL checkSignatureEncoding {label}: got {got}, expected {expected}"
      failures := failures + 1
  for (label, key, flags, expected, valid) in keyCases do
    count := count + 1
    let got := resultName (checkPubKeyEncoding key flags)
    if got != expected || isValidPubKey key != valid then
      IO.eprintln s!"FAIL public key {label}: got {got} and {isValidPubKey key}, expected {expected} and {valid}"
      failures := failures + 1
  IO.println s!"signature encoding hand cases: {count} cases, {failures} failures"
  return corpusFailures + failures

end KnownAnswers.SignatureEncoding


/-!
## Signature opcodes

Runs `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` through `evalScript` with a test checker.

The test checker is a lookup table, a test backend that says nothing about consensus validity.
It answers `some true` for the listed signature and key pairs and `some false` for every other pair.
It answers only for the script code that the case expects, and `none` for any other script code.
So a wrong script code gives an unsupported result, and the case fails.

Every expected result is written by hand from `EvalScript` (D3, lines 880 to 1026) and `CScript::FindAndDelete` (D24, lines 570 to 596).
The expected script codes are written out byte for byte.
The cases cover each error of the two opcodes in Core's order.
They cover 0-of-0, 1-of-1, 2-of-3 with signatures in and out of order, and early exit.
They cover the dummy with and without `NULLDUMMY`, a key count of 21 and an opcode count raised past 201 by keys.
They also cover a code separator before the opcode, a signature push inside the script code, and the order-dependent encoding check of D3 line 969.

The `transactionChecker` cases fix a transaction and use a verifier that answers only for the expected request.
The verifier ignores the digest, which `transactionChecker_verify` in `DogeLib.Script.Proofs.Signature` characterizes.
-/

namespace KnownAnswers.ScriptSignature

open DogeLib.Script
open KnownAnswers.ScriptEval (Expect hex rep)

/-- The test checker: `some true` for a listed pair, `some false` for another pair, and `none` unless the script code is `code`. -/
def tableChecker (code : List UInt8) (valid : List (List UInt8 × List UInt8)) : SignatureChecker where
  checkSig sig key c := if c == code then some (valid.contains (sig, key)) else none
  checkLockTime _ := none
  checkSequence _ := none

/-- Three test signatures and three test keys, of arbitrary bytes. With flags 0 no encoding check reads them. -/
def s1 : List UInt8 := [0xa1, 0x01]
def s2 : List UInt8 := [0xa2, 0x01]
def s3 : List UInt8 := [0xa3, 0x01]
def k1 : List UInt8 := [0xb1]
def k2 : List UInt8 := [0xb2]
def k3 : List UInt8 := [0xb3]

/-- The valid pairs of the table. -/
def table : List (List UInt8 × List UInt8) := [(s1, k1), (s2, k2), (s3, k3)]

/-- A strict-DER signature with R = 1, S = 1 and hash type `0x01`, which passes `STRICTENC`. -/
def derSig : List UInt8 := hex "300602010102010101"
/-- A compressed public key: `0x02` and 32 bytes. -/
def goodKey : List UInt8 := 0x02 :: rep 32 0x11
/-- A key that fails `STRICTENC`: `0x02` and 31 bytes. -/
def badKey : List UInt8 := 0x02 :: rep 31 0x11

/-- `OP_PUSHBYTES_n` of a short item. -/
def push (b : List UInt8) : List UInt8 := b.length.toUInt8 :: b

/-- One case: a label, flags, a checker, a script, a caller stack and the expected result. -/
structure Case where
  label : String
  flags : UInt32
  checker : SignatureChecker
  script : List UInt8
  stack : List (List UInt8)
  expected : Expect

/-- `OP_2 <k1> <k2> <k3> OP_3 OP_CHECKMULTISIG`. -/
def twoOfThree : List UInt8 := [0x52, 0x01, 0xb1, 0x01, 0xb2, 0x01, 0xb3, 0x53, 0xae]

/-- 180 or 181 counted NOPs, 20 empty keys, a key count of 20 and `OP_CHECKMULTISIG`, after a signature count of 0. -/
def twentyKeys (nops : Nat) : List UInt8 := rep nops 0x61 ++ [0x00] ++ rep 20 0x00 ++ [0x01, 0x14, 0xae]

/-- `OP_1 <badKey> <goodKey> OP_2 OP_CHECKMULTISIG`: the loop visits `goodKey` first. -/
def badKeyBelow : List UInt8 := [0x51, 0x20] ++ badKey ++ [0x21] ++ goodKey ++ [0x52, 0xae]

/-- The hand cases. -/
def cases : List Case := [
  -- OP_CHECKSIG and OP_CHECKSIGVERIFY (D3, lines 880 to 918).
  ⟨"CHECKSIG on one item", 0, tableChecker [0xac] table, [0xac], [s1], .rejected .invalidStackOperation⟩,
  ⟨"CHECKSIG valid pair", 0, tableChecker [0xac] table, [0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG invalid pair", 0, tableChecker [0xac] table, [0xac], [s1, k2], .ok [[]]⟩,
  ⟨"CHECKSIGVERIFY valid pair", 0, tableChecker [0xad] table, [0xad], [[7], s1, k1], .ok [[7]]⟩,
  ⟨"CHECKSIGVERIFY invalid pair", 0, tableChecker [0xad] table, [0xad], [s1, k2], .rejected .checkSigVerify⟩,
  ⟨"CHECKSIG empty signature reaches the checker", 0, tableChecker [0xac] table, [0xac], [[], k1], .ok [[]]⟩,
  ⟨"CHECKSIG signature encoding before key encoding", 0x02, tableChecker [0xac] table, [0xac], [s1, badKey],
    .rejected .sigDer⟩,
  ⟨"CHECKSIG key encoding", 0x02, tableChecker [0xac] [], [0xac], [derSig, badKey], .rejected .pubkeyType⟩,
  ⟨"CHECKSIG encoding passes", 0x02, tableChecker [0xac] [(derSig, goodKey)], [0xac], [derSig, goodKey], .ok [[1]]⟩,
  ⟨"CHECKSIG unavailable checker", 0, ⟨fun _ _ _ => none, fun _ => none, fun _ => none⟩, [0xac], [s1, k1],
    .unsupported (.signatureOpcode 0xac)⟩,
  ⟨"CHECKSIG script code from the start", 0, tableChecker [0x61, 0xac] table, [0x61, 0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG after a code separator", 0, tableChecker [0xac] table, [0x61, 0xab, 0xac], [s1, k1], .ok [[1]]⟩,
  ⟨"CHECKSIG deletes its signature push", 0, tableChecker [0x01, 0xb1, 0xac] table,
    [0x02, 0xa1, 0x01, 0x01, 0xb1, 0xac], [], .ok [[1]]⟩,
  ⟨"CHECKSIG keeps a push of other bytes", 0, tableChecker [0x02, 0xa2, 0x01, 0x75, 0xac] table,
    [0x02, 0xa2, 0x01, 0x75, 0xac], [s1, k1], .ok [[1]]⟩,
  -- OP_CHECKMULTISIG and OP_CHECKMULTISIGVERIFY (D3, lines 920 to 1026), errors in Core's order.
  ⟨"CHECKMULTISIG on an empty stack", 0, tableChecker [0xae] table, [0xae], [], .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG key count of five bytes", 0, tableChecker [] table, [0x05, 0x01, 0x00, 0x00, 0x00, 0x00, 0xae],
    [], .rejected .unknownError⟩,
  ⟨"CHECKMULTISIG key count -1", 0, tableChecker [] table, [0x4f, 0xae], [], .rejected .pubkeyCount⟩,
  ⟨"CHECKMULTISIG key count 21", 0, tableChecker [] table, [0x01, 0x15, 0xae], [], .rejected .pubkeyCount⟩,
  ⟨"CHECKMULTISIG 201 counted opcodes with 20 keys", 0, tableChecker [] table, twentyKeys 180, [[]], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 202 counted opcodes with 20 keys", 0, tableChecker [] table, twentyKeys 181, [[]],
    .rejected .opCount⟩,
  ⟨"CHECKMULTISIG key count before keys", 0, tableChecker [] table, [0x52, 0xae], [], .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG missing signature count", 0, tableChecker [] table, [0x01, 0xb1, 0x51, 0xae], [],
    .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG signature count of five bytes", 0, tableChecker [] table,
    [0x05, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01, 0xb1, 0x51, 0xae], [], .rejected .unknownError⟩,
  ⟨"CHECKMULTISIG signature count above key count", 0, tableChecker [] table, [0x52, 0x01, 0xb1, 0x51, 0xae], [],
    .rejected .sigCount⟩,
  ⟨"CHECKMULTISIG signature count -1", 0, tableChecker [] table, [0x4f, 0x01, 0xb1, 0x51, 0xae], [],
    .rejected .sigCount⟩,
  ⟨"CHECKMULTISIG missing signature", 0, tableChecker [] table, [0x51, 0x01, 0xb1, 0x51, 0xae], [[]],
    .rejected .invalidStackOperation⟩,
  ⟨"CHECKMULTISIG missing dummy", 0, tableChecker [] table, [0x51, 0x01, 0xb1, 0x51, 0xae], [s1],
    .rejected .invalidStackOperation⟩,
  -- Matching.
  ⟨"CHECKMULTISIG 0-of-0", 0, tableChecker [] table, [0x00, 0x00, 0xae], [[]], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 0-of-0 keeps the item below the dummy", 0, tableChecker [] table, [0x00, 0x00, 0xae], [[9], []],
    .ok [[9], [1]]⟩,
  ⟨"CHECKMULTISIG 1-of-1", 0, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table, [0x51, 0x01, 0xb1, 0x51, 0xae],
    [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 1-of-1 wrong key", 0, tableChecker [0x51, 0x01, 0xb2, 0x51, 0xae] table,
    [0x51, 0x01, 0xb2, 0x51, 0xae], [[], s1], .ok [[]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 in order", 0, tableChecker twoOfThree table, twoOfThree, [[], s1, s2], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 skipping a key", 0, tableChecker twoOfThree table, twoOfThree, [[], s1, s3], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG 2-of-3 out of order", 0, tableChecker twoOfThree table, twoOfThree, [[], s2, s1], .ok [[]]⟩,
  ⟨"CHECKMULTISIGVERIFY 2-of-3 in order", 0, tableChecker (twoOfThree.dropLast ++ [0xaf]) table,
    twoOfThree.dropLast ++ [0xaf], [[], s2, s3], .ok []⟩,
  ⟨"CHECKMULTISIGVERIFY 2-of-3 out of order", 0, tableChecker (twoOfThree.dropLast ++ [0xaf]) table,
    twoOfThree.dropLast ++ [0xaf], [[], s3, s2], .rejected .checkMultisigVerify⟩,
  -- Early exit (D3, lines 987 to 991): after s1 fails against k3 and k2, two signatures remain for one key.
  -- The pair (s1, k1) would be unavailable, so a visit would give an unsupported result.
  ⟨"CHECKMULTISIG early exit", 0,
    ⟨fun sig key code =>
      if code != twoOfThree then none
      else if sig == s1 && key == k1 then none
      else some (table.contains (sig, key)), fun _ => none, fun _ => none⟩,
    twoOfThree, [[], s2, s1], .ok [[]]⟩,
  -- The order-dependent encoding check (D3, line 969), with STRICTENC.
  ⟨"CHECKMULTISIG never visits a bad key below a match", 0x02, tableChecker badKeyBelow [(derSig, goodKey)],
    badKeyBelow, [[], derSig], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG visits a bad key first", 0x02, tableChecker [] [(derSig, goodKey)],
    [0x51, 0x21] ++ goodKey ++ [0x20] ++ badKey ++ [0x52, 0xae], [[], derSig], .rejected .pubkeyType⟩,
  -- The dummy (D3, lines 1004 to 1014).
  ⟨"CHECKMULTISIG nonempty dummy without NULLDUMMY", 0, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[0x01], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG nonempty dummy with NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[0x01], s1], .rejected .sigNullDummy⟩,
  ⟨"CHECKMULTISIG empty dummy with NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x51, 0x01, 0xb1, 0x51, 0xae], [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG failure with nonempty dummy and NULLDUMMY", 0x10, tableChecker [0x51, 0x01, 0xb2, 0x51, 0xae] table,
    [0x51, 0x01, 0xb2, 0x51, 0xae], [[0x01], s1], .rejected .sigNullDummy⟩,
  -- Script code.
  ⟨"CHECKMULTISIG after a code separator", 0, tableChecker [0xae] table, [0x51, 0x01, 0xb1, 0x51, 0xab, 0xae],
    [[], s1], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG deletes its signature push", 0, tableChecker [0x00, 0x51, 0x01, 0xb1, 0x51, 0xae] table,
    [0x00, 0x02, 0xa1, 0x01, 0x51, 0x01, 0xb1, 0x51, 0xae], [], .ok [[1]]⟩,
  ⟨"CHECKMULTISIG deletes every signature push before the loop", 0, tableChecker (rep 1 0x00 ++ twoOfThree) table,
    [0x00, 0x02, 0xa1, 0x01, 0x02, 0xa2, 0x01] ++ twoOfThree, [], .ok [[1]]⟩,
  -- Skipped branches: no checker call and no key count.
  ⟨"signature opcodes in a skipped branch", 0, ⟨fun _ _ _ => none, fun _ => none, fun _ => none⟩, [0x00, 0x63, 0xac, 0xad, 0xae, 0xaf, 0x68],
    [], .ok []⟩,
  ⟨"CHECKMULTISIG in a skipped branch counts once", 0, tableChecker [] table,
    [0x00, 0x63, 0x01, 0x14, 0xae, 0x68] ++ rep 198 0x61, [], .ok []⟩
]

/-- A transaction with one input and one output, from the context of record 9 of `script_tests.json`. -/
def spendTx? : Option DogeLib.Transaction.Transaction :=
  match DogeLib.Transaction.Transaction.decodeBaseComplete
      (hex "0100000001dc3e1270bc983b5fc117d86201475c85dbac7647c663e275f730cc87200f7a920000000000ffffffff0100000000000000000000000000") with
  | .ok tx => some tx
  | .error _ => none

/-- A verifier that answers `some true` only for the signature `sig` without its hash type and the key `key`, and `none` for every other request. -/
def strictVerifier (sig key : List UInt8) : SignatureVerifier :=
  fun s k _ => if s == sig && k == key then some true else none

/-- The `transactionChecker` cases: label, signature, key and expected answer. -/
def checkerCases : List (String × List UInt8 × List UInt8 × Option Bool) := [
  ("invalid key, verifier not called", derSig, [0x05], some false),
  ("empty key, verifier not called", derSig, [], some false),
  ("empty signature, verifier not called", [], goodKey, some false),
  ("hash type removed", derSig, goodKey, some true),
  ("hybrid key of 65 bytes reaches the verifier", derSig, 0x06 :: rep 64 0x11, none)
]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript (some c.checker) c.flags c.script c.stack
    unless c.expected.matches got do
      IO.eprintln s!"FAIL signature opcode {c.label}: got {repr got}"
      failures := failures + 1
  let stripped := derSig.dropLast
  let some spendTx := spendTx? | throw (IO.userError "the transaction of record 9 does not decode")
  for (label, sig, key, expected) in checkerCases do
    let got := (transactionChecker spendTx 0 (strictVerifier stripped goodKey)).checkSig sig key [0xac]
    unless got == expected do
      IO.eprintln s!"FAIL transactionChecker {label}: got {repr got}"
      failures := failures + 1
  let base := baseChecker.checkSig derSig goodKey [0xac]
  unless base == some false do
    IO.eprintln s!"FAIL baseChecker: got {repr base}"
    failures := failures + 1
  IO.println s!"signature opcodes: {cases.length} hand cases, {checkerCases.length + 1} checker cases, {failures} failures"
  return failures

end KnownAnswers.ScriptSignature


/-!
## `VerifyScript` and the lock-time opcodes

Hand cases for stage 4, each at a boundary that Core's source states:
`OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` (D3, lines 350 to 427), `CheckLockTime` and `CheckSequence` (D3, lines 1274 to 1353), `VerifyScript` (D3, lines 1409 to 1526) and `IsPushOnly` (D48, lines 239 to 259).
Each expected result is read from those lines, not computed by DogeLib.
The P2SH cases build the template from the HASH160 digest of the redeem script, and `lake test` checks HASH160 against its own vectors.
-/

namespace KnownAnswers.ScriptVerify

open DogeLib.Script
open KnownAnswers.ScriptEval (Expect hex rep)

/-- A transaction with one input of sequence `sequence`, no outputs, version bits `version` and lock time `lockTime`. -/
def mkTx (version lockTime sequence : UInt32) : DogeLib.Transaction.Transaction :=
  { version
    inputs := ⟨[{ prevout := DogeLib.Transaction.OutPoint.null, scriptSig := ⟨⟨[], by decide⟩⟩, sequence }], by simp⟩
    outputs := ⟨[], by decide⟩
    lockTime }

/-- `transactionChecker` for input 0 of `mkTx`, with a verifier that is always unavailable. -/
def txChecker (version lockTime sequence : UInt32) : SignatureChecker :=
  transactionChecker (mkTx version lockTime sequence) 0 fun _ _ _ => none

/-- A push of the bytes `b`, for at most 75 bytes. -/
def push (b : List UInt8) : List UInt8 := b.length.toUInt8 :: b

def cltv : UInt32 := ScriptFlags.checkLockTimeVerify
def csv : UInt32 := ScriptFlags.checkSequenceVerify

/-- One hand case of an evaluation: a label, flags, a checker, a script and the expected result on the empty stack. -/
structure Case where
  label : String
  flags : UInt32
  checker : Option SignatureChecker
  script : List UInt8
  expected : Expect

/-- 499,999,999, 500,000,000 and 500,000,001 as script numbers. -/
def n499999999 : List UInt8 := [0xff, 0x64, 0xcd, 0x1d]
def n500000000 : List UInt8 := [0x00, 0x65, 0xcd, 0x1d]
def n500000001 : List UInt8 := [0x01, 0x65, 0xcd, 0x1d]

/-- The lock-time cases. Each operand stays on the stack, because neither opcode pops. -/
def cases : List Case := [
  -- CHECKLOCKTIMEVERIFY: the threshold (D24 line 35, D3 lines 1283 to 1287).
  ⟨"CLTV 499,999,999 against 500,000,000", cltv, txChecker 1 500000000 0, push n499999999 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 500,000,000 against 500,000,000", cltv, txChecker 1 500000000 0, push n500000000 ++ [0xb1],
    .ok [n500000000]⟩,
  ⟨"CLTV 499,999,999 against 499,999,999", cltv, txChecker 1 499999999 0, push n499999999 ++ [0xb1],
    .ok [n499999999]⟩,
  ⟨"CLTV 500,000,001 against 500,000,000", cltv, txChecker 1 500000000 0, push n500000001 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 500,000,000 against 499,999,999", cltv, txChecker 1 499999999 0, push n500000000 ++ [0xb1],
    .rejected .unsatisfiedLocktime⟩,
  -- The comparison (D3 lines 1291 and 1292).
  ⟨"CLTV 6 against 5", cltv, txChecker 1 5 0, [0x56, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV 0 against 0", cltv, txChecker 1 0 0, [0x00, 0xb1], .ok [[]]⟩,
  -- The final sequence (D4 line 76, D3 lines 1304 and 1305).
  ⟨"CLTV with sequence 0xffffffff", cltv, txChecker 1 0 0xffffffff, [0x00, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV with sequence 0xfffffffe", cltv, txChecker 1 0 0xfffffffe, [0x00, 0xb1], .ok [[]]⟩,
  -- The five-byte operand (D3 line 377).
  ⟨"CLTV five-byte 0xffffffff against 0xffffffff", cltv, txChecker 1 0xffffffff 0,
    push [0xff, 0xff, 0xff, 0xff, 0x00] ++ [0xb1], .ok [[0xff, 0xff, 0xff, 0xff, 0x00]]⟩,
  ⟨"CLTV five-byte 2^32 against 0xffffffff", cltv, txChecker 1 0xffffffff 0,
    push [0x00, 0x00, 0x00, 0x00, 0x01] ++ [0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV six-byte operand", cltv, txChecker 1 0xffffffff 0, push [0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ [0xb1],
    .rejected .unknownError⟩,
  -- The negative operand and the empty stack (D3 lines 360, 361, 382 and 383).
  ⟨"CLTV -1", cltv, txChecker 1 0 0, [0x4f, 0xb1], .rejected .negativeLocktime⟩,
  ⟨"CLTV negative zero is not negative", cltv, txChecker 1 0 0, push [0x80] ++ [0xb1], .ok [[0x80]]⟩,
  ⟨"CLTV on an empty stack", cltv, txChecker 1 0 0, [0xb1], .rejected .invalidStackOperation⟩,
  ⟨"CLTV with BaseSignatureChecker", cltv, some baseChecker, [0x00, 0xb1], .rejected .unsatisfiedLocktime⟩,
  ⟨"CLTV without a checker", cltv, none, [0x00, 0xb1], .unsupported .checkLockTimeVerify⟩,
  -- Flag off: NOP2 and NOP3 (D3 lines 352 to 358 and 394 to 400).
  ⟨"NOP2 on an empty stack", 0, txChecker 1 0 0xffffffff, [0xb1], .ok []⟩,
  ⟨"NOP3 on an empty stack", 0, txChecker 1 0 0xffffffff, [0xb2], .ok []⟩,
  ⟨"NOP2 without a checker", csv, none, [0xb1], .ok []⟩,
  -- CHECKSEQUENCEVERIFY: the version as uint32_t (D3 lines 1318 and 1319).
  ⟨"CSV with version 1", csv, txChecker 1 0 10, [0x55, 0xb2], .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV with version 2", csv, txChecker 2 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  ⟨"CSV with version 0xffffffff", csv, txChecker 0xffffffff 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  ⟨"CSV with version 0x80000000", csv, txChecker 0x80000000 0 10, [0x55, 0xb2], .ok [[5]]⟩,
  -- The disable bit in the operand (D4 line 81, D3 lines 418 and 419).
  ⟨"CSV operand with bit 31, version 1", csv, txChecker 1 0 10,
    push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"CSV operand with bit 31, BaseSignatureChecker", csv, some baseChecker,
    push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2], .ok [[0x00, 0x00, 0x00, 0x80, 0x00]]⟩,
  ⟨"CSV operand with bit 31, no checker", csv, none, push [0x00, 0x00, 0x00, 0x80, 0x00] ++ [0xb2],
    .unsupported .checkSequenceVerify⟩,
  -- The disable bit in the sequence (D3 lines 1325 and 1326).
  ⟨"CSV with sequence bit 31", csv, txChecker 2 0 0x8000000a, [0x55, 0xb2], .rejected .unsatisfiedLocktime⟩,
  -- The type bit (D4 line 86, D3 lines 1341 to 1346).
  ⟨"CSV time operand against height sequence", csv, txChecker 2 0 10, push [0x00, 0x00, 0x40] ++ [0xb2],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV height operand against time sequence", csv, txChecker 2 0 0x40000a, [0x55, 0xb2],
    .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV time operand against time sequence", csv, txChecker 2 0 0x40000a, push [0x05, 0x00, 0x40] ++ [0xb2],
    .ok [[0x05, 0x00, 0x40]]⟩,
  -- The masked comparison (D4 line 90, D3 lines 1330 to 1332 and 1350 and 1351).
  ⟨"CSV 11 against 10", csv, txChecker 2 0 10, [0x5b, 0xb2], .rejected .unsatisfiedLocktime⟩,
  ⟨"CSV 10 against 10", csv, txChecker 2 0 10, [0x5a, 0xb2], .ok [[10]]⟩,
  ⟨"CSV operand bits outside the mask", csv, txChecker 2 0 10, push [0x05, 0x00, 0x01] ++ [0xb2],
    .ok [[0x05, 0x00, 0x01]]⟩,
  ⟨"CSV sequence bits outside the mask", csv, txChecker 2 0 0x0001000a, [0x5a, 0xb2], .ok [[10]]⟩,
  ⟨"CSV six-byte operand", csv, txChecker 2 0 10, push [0x00, 0x00, 0x00, 0x00, 0x00, 0x00] ++ [0xb2],
    .rejected .unknownError⟩,
  ⟨"CSV -1", csv, txChecker 2 0 10, [0x4f, 0xb2], .rejected .negativeLocktime⟩,
  ⟨"CSV on an empty stack", csv, txChecker 2 0 10, [0xb2], .rejected .invalidStackOperation⟩
]

/-- The P2SH template for the redeem script `redeem`: `OP_HASH160`, its HASH160 digest, `OP_EQUAL`. -/
def p2shOf (redeem : List UInt8) : List UInt8 :=
  [0xa9, 0x14] ++ (DogeLib.Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList ++ [0x87]

/-- The expected result of a `VerifyScript` case. -/
inductive VExpect where
  | accepted
  | rejected (e : ScriptError)
  | unsupported (u : Unsupported)
  deriving BEq, Repr

def VExpect.matches : VExpect → VerifyResult → Bool
  | .accepted, .accepted => true
  | .rejected e, .rejected e' => e == e'
  | .unsupported u, .unsupported u' => u == u'
  | _, _ => false

def p2sh : UInt32 := ScriptFlags.p2sh

/-- `VerifyScript` cases: label, flags, scriptSig, scriptPubKey and the expected result. -/
def verifyCases : List (String × UInt32 × List UInt8 × List UInt8 × VExpect) := [
  ("P2SH, redeem script OP_1", p2sh, push [0x51], p2shOf [0x51], .accepted),
  ("P2SH, redeem script leaves false", p2sh, push [0x00], p2shOf [0x00], .rejected .evalFalse),
  ("P2SH, redeem script OP_RETURN", p2sh, push [0x6a], p2shOf [0x6a], .rejected .opReturn),
  ("P2SH, redeem script reads the item below", p2sh, [0x51] ++ push [0x75, 0x51], p2shOf [0x75, 0x51], .accepted),
  ("P2SH, empty redeem script leaves nothing", p2sh, [0x00], p2shOf [], .rejected .evalFalse),
  ("P2SH, scriptSig not push-only", p2sh, [0x61] ++ push [0x51], p2shOf [0x51], .rejected .sigPushOnly),
  ("P2SH flag off, scriptSig not push-only", 0, [0x61] ++ push [0x51], p2shOf [0x51], .accepted),
  ("P2SH flag off, redeem script leaves false", 0, push [0x00], p2shOf [0x00], .accepted),
  ("P2SH, wrong redeem script", p2sh, push [0x52], p2shOf [0x51], .rejected .evalFalse),
  ("P2SH, empty scriptSig", p2sh, [], p2shOf [0x51], .rejected .invalidStackOperation),
  ("P2SH, OP_RESERVED in scriptSig", p2sh, [0x50] ++ push [0x51], p2shOf [0x51], .rejected .badOpcode),
  ("P2SH, OP_RESERVED in a skipped branch is not push-only", p2sh, [0x00, 0x63, 0x50, 0x68] ++ push [0x51],
    p2shOf [0x51], .rejected .sigPushOnly),
  ("P2SH, extra items are not checked", p2sh, [0x51, 0x52] ++ push [0x51], p2shOf [0x51], .accepted),
  ("not P2SH: the template and OP_NOP", p2sh, [0x61] ++ push [0x51], p2shOf [0x51] ++ [0x61], .accepted),
  ("bare scripts, true top", p2sh, [0x51], [], .accepted),
  ("bare scripts, false top", p2sh, [0x51], [0x00], .rejected .evalFalse),
  ("bare scripts, empty stack", 0, [], [], .rejected .evalFalse),
  ("scriptSig fails first", p2sh, [0x6a], p2shOf [0x51], .rejected .opReturn),
  ("SIGPUSHONLY is unsupported", ScriptFlags.sigPushOnly, [0x61], [0x51], .unsupported (.flags 0x20)),
  ("CLEANSTACK is unsupported", p2sh ||| ScriptFlags.cleanStack, push [0x51], p2shOf [0x51],
    .unsupported (.flags 0x100))
]

/-- `isPushOnly` cases (D48, lines 239 to 259). -/
def pushOnlyCases : List (List UInt8 × Bool) := [
  ([], true), ([0x00], true), ([0x50], true), ([0x60], true), ([0x4f], true), ([0x4c, 0x01, 0x07], true),
  ([0x61], false), ([0x51, 0x61], false), ([0x02, 0x01], false), ([0x4c], false), ([0xb1], false)
]

/-- The bytes as a transaction script. Every script here is far below 2^64 bytes. -/
def toScript (b : List UInt8) : DogeLib.Transaction.Script :=
  if h : b.length < 2 ^ 64 then ⟨⟨b, h⟩⟩ else ⟨⟨[], by decide⟩⟩

/-- An input context over input 0 of `mkTx`. -/
def ctx (version lockTime sequence : UInt32) : InputContext :=
  ⟨mkTx version lockTime sequence, 0, by simp [mkTx], by simp [mkTx], by simp [mkTx]⟩

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  for c in cases do
    let got := evalScript c.checker c.flags c.script []
    unless c.expected.matches got do
      IO.eprintln s!"FAIL lock time {c.label}: got {repr got}"
      failures := failures + 1
  for (label, flags, ss, spk, expected) in verifyCases do
    let got := verifyScript (txChecker 2 0 0) flags ss spk
    unless expected.matches got do
      IO.eprintln s!"FAIL verifyScript {label}: got {repr got}"
      failures := failures + 1
  for (script, expected) in pushOnlyCases do
    unless isPushOnly script == expected do
      IO.eprintln s!"FAIL isPushOnly {script}: expected {expected}"
      failures := failures + 1
  -- A spend whose P2SH redeem script checks the lock time of the input.
  let redeem : List UInt8 := [0x55, 0xb1]
  let prev := toScript (p2shOf redeem)
  let mkSpend (lockTime sequence : UInt32) : InputContext :=
    let base := ctx 1 lockTime sequence
    let input := { base.input with scriptSig := toScript (push redeem) }
    ⟨{ base.tx with inputs := ⟨[input], by simp⟩ }, 0, by simp, by simp, by simp [base, ctx, mkTx]⟩
  let flags := p2sh ||| cltv
  let spends : List (String × InputContext × VExpect) := [
    ("spend, lock time 5", mkSpend 5 0, .accepted),
    ("spend, lock time 4", mkSpend 4 0, .rejected .unsatisfiedLocktime),
    ("spend, final sequence", mkSpend 5 0xffffffff, .rejected .unsatisfiedLocktime)
  ]
  for (label, c, expected) in spends do
    let got := verifyLegacySpend c prev flags fun _ _ _ => none
    unless expected.matches got do
      IO.eprintln s!"FAIL verifyLegacySpend {label}: got {repr got}"
      failures := failures + 1
  let total := cases.length + verifyCases.length + pushOnlyCases.length + spends.length
  IO.println s!"verify and lock time: {total} hand cases, {failures} failures"
  return failures

end KnownAnswers.ScriptVerify


/-!
## The worked property: multisig with recovery

Spends of the 2-of-3 template of design record 0003, section 7, through `verifyLegacySpend` and so through `verifyScript`.
The redeem script is written byte for byte from section 7, and one case checks that `multisigRecoveryScript` builds the same bytes.
Each expected result is read from section 7 and from `EvalScript` (D3, lines 437 to 476, 880 to 1026 and 1274 to 1308), not computed by DogeLib.

The verifier is a lookup table, a test backend that says nothing about consensus validity.
It answers `some true` for the listed pairs of stripped signature and key, and `some false` for every other request.
It ignores the digest, which `transactionChecker_verify` in `DogeLib.Script.Proofs.Signature` characterizes.
The keys are 33 bytes with the prefix `02`, which every encoding flag accepts.

`checkSighash` compares, for three script codes of the template and six hash types, the production digest with the digest of the transformation reference.
Both sides are DogeLib definitions, so that check is a consistency check, not independent evidence.
-/

namespace KnownAnswers.MultisigRecovery

open DogeLib.Script
open KnownAnswers.ScriptEval (hex rep)
open KnownAnswers.ScriptVerify (VExpect mkTx toScript p2shOf)

def P1 : List UInt8 := 0x02 :: rep 32 0x11
def P2 : List UInt8 := 0x02 :: rep 32 0x22
def P3 : List UInt8 := 0x02 :: rep 32 0x33
def R : List UInt8 := 0x02 :: rep 32 0x44

/-- The 2-of-3 redeem script of section 7, written out: 149 bytes. -/
def redeem : List UInt8 :=
  [0x63, 0x52, 0x21] ++ P1 ++ [0x21] ++ P2 ++ [0x21] ++ P3 ++
    [0x53, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75, 0x21] ++ R ++ [0xac, 0x68]

/-- A push of `b` as `CScript() << b` writes it, for at most 255 bytes. -/
def push (b : List UInt8) : List UInt8 :=
  if b.length < 76 then b.length.toUInt8 :: b else 0x4c :: b.length.toUInt8 :: b

/-- Test signatures of arbitrary bytes, each with the hash type `01`. With no encoding flag no check reads them. -/
def sig1 : List UInt8 := [0xa1, 0x01]
def sig2 : List UInt8 := [0xa2, 0x01]
def sigR : List UInt8 := [0xa4, 0x01]
/-- A strict DER signature: R = 1, S = 1, hash type `01`. -/
def derSigR : List UInt8 := hex "300602010102010101"
/-- The same signature with the undefined hash type `00`. -/
def derSigR0 : List UInt8 := hex "300602010102010100"
/-- A strict DER signature with R = 1 and S = ⌊n/2⌋ + 1, one above the LOW_S bound, and the hash type `01`. -/
def highSigR : List UInt8 := hex "30250201010220" ++ KnownAnswers.SignatureEncoding.halfPlusOneBytes ++ [0x01]
/-- The LOW_S overflow case: R = 2^256 − 1 and S = 2^255 − 1, which `CheckLowS` accepts after lax parsing sets both to zero. -/
def overflowSigR : List UInt8 := hex "3045022100" ++ rep 32 0xff ++ hex "02207f" ++ rep 31 0xff ++ [0x01]

/-- The table verifier, a test backend: `some true` for a listed pair of stripped signature and key. -/
def tableVerifier : SignatureVerifier := fun s k _ =>
  some ([([0xa1], P1), ([0xa2], P2), ([0xa4], R), (derSigR.dropLast, R), (overflowSigR.dropLast, R),
    ([0xa1], [0x06] ++ rep 32 0x44)].contains (s, k))

/-- An input context for input 0 of `mkTx 1 lockTime sequence`, with the `scriptSig` bytes `ss`. -/
def spendCtx (ss : List UInt8) (lockTime sequence : UInt32) : InputContext :=
  let base := KnownAnswers.ScriptVerify.ctx 1 lockTime sequence
  let input := { base.input with scriptSig := toScript ss }
  ⟨{ base.tx with inputs := ⟨[input], by simp⟩ }, 0, by simp, by simp, by simp [base, KnownAnswers.ScriptVerify.ctx, mkTx]⟩

def p2sh : UInt32 := ScriptFlags.p2sh
def cltv : UInt32 := ScriptFlags.checkLockTimeVerify
def base : UInt32 := p2sh ||| cltv

/-- The ordinary unlocking script: a dummy, two signatures in push order and a selector, then the redeem script. -/
def ordinary (dummy a b sel : List UInt8) (red : List UInt8 := redeem) : List UInt8 :=
  push dummy ++ push a ++ push b ++ push sel ++ push red

/-- The recovery unlocking script: a signature and a selector, then the redeem script. -/
def recovery (s sel : List UInt8) (red : List UInt8 := redeem) : List UInt8 := push s ++ push sel ++ push red

/-- A redeem script with the recovery key `r`, for the key-encoding case. -/
def redeemWith (r : List UInt8) : List UInt8 :=
  [0x63, 0x52, 0x21] ++ P1 ++ [0x21] ++ P2 ++ [0x21] ++ P3 ++
    [0x53, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75, 0x21] ++ r ++ [0xac, 0x68]

/-- Cases: label, flags, scriptSig, redeem script, lock time, sequence and expected result. -/
def cases : List (String × UInt32 × List UInt8 × List UInt8 × UInt32 × UInt32 × VExpect) := [
  ("ordinary branch, signatures in key order", base, ordinary [] sig1 sig2 [1], redeem, 0, 0xffffffff, .accepted),
  ("ordinary branch, signatures in the wrong order", base, ordinary [] sig2 sig1 [1], redeem, 0, 0xffffffff,
    .rejected .evalFalse),
  ("ordinary branch, one signature missing", base, push [] ++ push sig1 ++ push [1] ++ push redeem, redeem, 0, 0,
    .rejected .invalidStackOperation),
  ("recovery, lock time 1,000,000", base, recovery sigR [], redeem, 1000000, 0, .accepted),
  ("recovery, lock time 999,999", base, recovery sigR [], redeem, 999999, 0, .rejected .unsatisfiedLocktime),
  ("recovery, lock time 500,000,000 is a time", base, recovery sigR [], redeem, 500000000, 0,
    .rejected .unsatisfiedLocktime),
  ("recovery, final sequence", base, recovery sigR [], redeem, 1000000, 0xffffffff, .rejected .unsatisfiedLocktime),
  ("recovery, wrong signature", base, recovery sig1 [], redeem, 1000000, 0, .rejected .evalFalse),
  ("recovery, empty signature", base, recovery [] [], redeem, 1000000, 0, .rejected .evalFalse),
  ("selector negative zero takes the recovery branch", base, recovery sigR [0x80], redeem, 1000000, 0, .accepted),
  ("selector negative zero, ordinary signatures", base, ordinary [] sig1 sig2 [0x80], redeem, 1000000, 0,
    .rejected .evalFalse),
  ("nonminimal selector 01 00 takes the ordinary branch", base, ordinary [] sig1 sig2 [0x01, 0x00], redeem, 0, 0,
    .accepted),
  ("nonempty dummy without NULLDUMMY", base, ordinary [0x07] sig1 sig2 [1], redeem, 0, 0, .accepted),
  ("nonempty dummy with NULLDUMMY", base ||| ScriptFlags.nullDummy, ordinary [0x07] sig1 sig2 [1], redeem, 0, 0,
    .rejected .sigNullDummy),
  ("empty dummy with NULLDUMMY", base ||| ScriptFlags.nullDummy, ordinary [] sig1 sig2 [1], redeem, 0, 0, .accepted),
  ("CLTV clear, lock time 0", p2sh, recovery sigR [], redeem, 0, 0xffffffff, .accepted),
  ("empty stack below the redeem script", base, push redeem, redeem, 0, 0, .rejected .unbalancedConditional),
  ("DER signature, all encoding flags", base ||| ScriptFlags.derSig ||| ScriptFlags.lowS ||| ScriptFlags.strictEnc,
    recovery derSigR [], redeem, 1000000, 0, .accepted),
  ("undefined hash type 00 under STRICTENC", base ||| ScriptFlags.strictEnc, recovery derSigR0 [], redeem, 1000000, 0,
    .rejected .sigHashtype),
  ("LOW_S overflow case passes the encoding check", base ||| ScriptFlags.lowS, recovery overflowSigR [], redeem,
    1000000, 0, .accepted),
  ("S one above the half order under LOW_S", base ||| ScriptFlags.lowS, recovery highSigR [], redeem, 1000000, 0,
    .rejected .sigHighS),
  ("arbitrary signature bytes under DERSIG", base ||| ScriptFlags.derSig, recovery sigR [], redeem, 1000000, 0,
    .rejected .sigDer),
  ("33-byte key with prefix 06 under STRICTENC", base ||| ScriptFlags.strictEnc,
    recovery [] [] (redeemWith ([0x06] ++ rep 32 0x44)), redeemWith ([0x06] ++ rep 32 0x44), 1000000, 0,
    .rejected .pubkeyType),
  ("33-byte key with prefix 06 without STRICTENC", base,
    recovery sig1 [] (redeemWith ([0x06] ++ rep 32 0x44)), redeemWith ([0x06] ++ rep 32 0x44), 1000000, 0,
    .rejected .evalFalse)
]

/-- A transaction with two inputs and two outputs, so that every hash type below hashes a preimage for input 0. -/
def sighashTx : DogeLib.Transaction.Transaction :=
  { version := 1
    inputs := ⟨[{ prevout := DogeLib.Transaction.OutPoint.null, scriptSig := toScript (recovery sigR []), sequence := 0 },
      { prevout := DogeLib.Transaction.OutPoint.null, scriptSig := toScript [], sequence := 0xfffffffe }], by simp⟩
    outputs := ⟨[⟨100000, toScript (p2shOf redeem)⟩, ⟨5000, toScript [0x51]⟩], by simp⟩
    lockTime := 1000000 }

/--
Three script codes of the template, with their expected lengths:

- the ordinary code, with `sig2` and then `sig1` removed, nearest the stack top first
- the recovery code, with `sigR` removed
- a code with the push of `P1` removed, so that FindAndDelete deletes 34 bytes
-/
def sighashCodes : List (String × List UInt8 × Nat) := [
  ("ordinary", effectiveScriptCode redeem 0 [sig2, sig1], 149),
  ("recovery", effectiveScriptCode redeem 0 [sigR], 149),
  ("P1 removed", effectiveScriptCode redeem 0 [P1], 115)
]

/-- SIGHASH_ALL, NONE and SINGLE, each with and without ANYONECANPAY. -/
def sighashTypes : List UInt32 := [1, 2, 3, 0x81, 0x82, 0x83]

/--
For each template code and hash type, the production digest `legacySignatureHash` equals the digest of `legacyReferencePlan`, and the code parses completely.
This compares two DogeLib definitions with each other: a consistency check of the template corollaries, not an expected value from an independent source.
The independent evidence for `legacySignatureHash` is Core's `sighash.json`.
-/
def checkSighash : IO Nat := do
  let mut failures := 0
  for (label, code, len) in sighashCodes do
    unless code.length == len && (DogeLib.Transaction.scanOps code).2 == [] do
      IO.eprintln s!"FAIL multisig recovery digest {label}: length {code.length} or the parse differs"
      failures := failures + 1
    for h in sighashTypes do
      let prod := DogeLib.Transaction.legacySignatureHash (toScript code) sighashTx 0 h
      let ref := (DogeLib.Transaction.legacyReferencePlan (toScript code) sighashTx 0 h).digest
      unless prod.val == ref.val do
        IO.eprintln s!"FAIL multisig recovery digest {label}, hash type {h}: production and reference differ"
        failures := failures + 1
  return failures

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  failures := failures + (← checkSighash)
  unless redeem.length == 149 && multisigRecoveryScript 2 [P1, P2, P3] R == redeem do
    IO.eprintln "FAIL multisig recovery: the template bytes differ from section 7"
    failures := failures + 1
  for (label, flags, ss, red, lockTime, sequence, expected) in cases do
    let got := verifyLegacySpend (spendCtx ss lockTime sequence) (toScript (p2shOf red)) flags tableVerifier
    unless expected.matches got do
      IO.eprintln s!"FAIL multisig recovery {label}: got {repr got}"
      failures := failures + 1
  IO.println s!"multisig recovery: {cases.length + 1} hand cases, {sighashCodes.length * sighashTypes.length} digest comparisons, {failures} failures"
  return failures

end KnownAnswers.MultisigRecovery


/-!
## Transaction spend corpus

Run the inside-milestone inputs of `tx_spends.jsonl` through `verifyLegacySpend` with `coreVerifier`.
Every eligible input must give a verdict: an unsupported result fails the test.
D28 and D29 supply the transactions, and D30 supplies the per-input acceptance requirement for `tx_valid`.
An invalid transaction supplies no individual Script expectation.
The witness-allowed prefix reader follows D30, while a separate complete base decode checks the oracle input domain.
-/

namespace KnownAnswers.TxSpends

open DogeLib.Script DogeLib.Transaction

/-- The fields needed to check one transaction input against the corpus requirement. -/
structure Record where
  source : String
  line : Nat
  inputIndex : UInt32
  bytes : List UInt8
  prevScript : DogeLib.Transaction.Script
  flags : UInt32
  accept : Bool
  inside : Bool

/-- Read a spend record without deriving an expectation from transaction rejection. -/
def parseRecord (text : String) : Except String Record := do
  let j ← Lean.Json.parse text
  let bytes ← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? "tx_hex").getStr?)
  let prev ← KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? "prevout_scriptPubKey_hex").getStr?)
  let some prevScript := DogeLib.Serialization.CountedList.ofList? prev.toList
    | throw "previous-output script exceeds the counted-list bound"
  let index ← (← j.getObjVal? "input_index").getNat?
  if index ≥ 2 ^ 32 then throw "input index exceeds uint32"
  let expectation ← j.getObjVal? "per_input_expectation"
  let accept ← match expectation with
    | .null => pure false
    | .str "accept" => pure true
    | _ => throw "unknown per-input expectation"
  return {
    source := ← (← j.getObjVal? "source_file").getStr?
    line := ← (← j.getObjVal? "source_line").getNat?
    inputIndex := index.toUInt32
    bytes := bytes.toList
    prevScript := ⟨prevScript⟩
    flags := (← (← j.getObjVal? "flags_mask").getNat?).toUInt32
    accept
    inside := (← (← (← j.getObjVal? "classification").getObjVal? "milestone").getStr?) == "inside" }

/-- Check every eligible input. Unknown expectations contribute outcome counts only. -/
def check : IO Nat := do
  let path : System.FilePath := "tests/script/corpus/tx_spends.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut excluded := 0
  let mut baseDecoded := 0
  let mut accepted := 0
  let mut verifier := 0
  let mut required := 0
  let mut unknownAccepted := 0
  let mut unknownRejected := 0
  let mut unknownVerifier := 0
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if !r.inside then
      excluded := excluded + 1
      continue
    if r.accept then required := required + 1
    match Transaction.decodeBaseComplete r.bytes with
    | .ok _ => baseDecoded := baseDecoded + 1
    | .error _ =>
      IO.eprintln s!"FAIL {r.source}:{r.line}: eligible input does not decode as complete base bytes"
      failures := failures + 1
    let w ← match Transaction.readAllowWitness r.bytes with
      | .ok (w, _) => pure w
      | .error _ => throw (IO.userError s!"{r.source}:{r.line}: transaction prefix does not decode")
    if w.hasWitness then throw (IO.userError "eligible spend has a witness")
    let tx := w.tx
    if hi : r.inputIndex.toNat < tx.inputs.val.length then
      if hn : tx.inputs.val.length < 2 ^ 32 then
        if ho : tx.outputs.val.length < 2 ^ 32 then
          let ctx : InputContext := ⟨tx, r.inputIndex, hi, hn, ho⟩
          let got := verifyLegacySpend ctx r.prevScript r.flags coreVerifier
          match got with
          | .accepted =>
            if r.accept then accepted := accepted + 1 else unknownAccepted := unknownAccepted + 1
          | .unsupported (.signatureOpcode _) =>
            if r.accept then verifier := verifier + 1 else unknownVerifier := unknownVerifier + 1
          | .rejected _ =>
            if r.accept then
              IO.eprintln s!"FAIL {r.source}:{r.line} input {r.inputIndex}: required accept, got {repr got}"
              failures := failures + 1
            else unknownRejected := unknownRejected + 1
          | .unsupported _ =>
            IO.eprintln s!"FAIL {r.source}:{r.line}: unexpected unsupported result {repr got}"
            failures := failures + 1
        else throw (IO.userError "output count exceeds context bound")
      else throw (IO.userError "input count exceeds context bound")
    else throw (IO.userError "spend index outside transaction")
  let unknown := unknownAccepted + unknownRejected + unknownVerifier
  unless lines.length == 267 && excluded == 108 && baseDecoded == 159 && required == 91 && unknown == 68 &&
      verifier == 0 && unknownVerifier == 0 do
    IO.eprintln "FAIL transaction spend corpus counts"
    failures := failures + 1
  IO.println s!"transaction spends: {lines.length} records, {excluded} excluded, {baseDecoded} complete base decodes, {failures} failures"
  IO.println s!"transaction spends required accept: {required} inputs, {accepted} accepted, {verifier} unsupported at a signature opcode"
  IO.println s!"transaction spends unknown expectation: {unknown} inputs, {unknownAccepted} accepted, {unknownRejected} rejected, {unknownVerifier} unsupported at a signature opcode (no agreement claim)"
  return failures

end KnownAnswers.TxSpends


/-!
## Core's signature verifier

### Public-key parsing

libsecp256k1's own test of `secp256k1_ec_pubkey_parse` at the compatibility pin supplies the points and the expectations (SOURCES.md, D57).
`run_ec_pubkey_parse_test` lists 12 valid points, 4 points with a valid `x` only and 7 invalid points.
`ec_pubkey_parse_pointtest` tries each one with every first byte from 0 to 255 and every length from 3 to 65.
Its formulas `xpass` and `ypass` give the expectation, and this test copies them.
No expectation comes from DogeLib.

The 23 points are copied from libsecp256k1 as Dogecoin Core bundles it at `e0a1c157791544e818c901bd9341896965afbf9d`, under the MIT licence in `LICENSES/libsecp256k1-MIT.txt`.
When a key must parse, the test checks the `x` of the point and, for a compressed key, the parity of `y`.
When `ypass` holds, it also checks `y`, as the upstream test does when it serializes the point again.

The points cover every row of design record 0005, section 4.1, and each failure: `x ≥ p`, `y ≥ p`, no square root, the wrong hybrid parity and a point off the curve.

### `coreVerifier` hand cases

- The digest one: `tx_valid.json` (D30) requires the acceptance of input 1 of the `SIGHASH_SINGLE` bug transaction, whose only check signs the fixed digest `01` followed by 31 zero bytes.
  The test runs its signature and key through `coreVerifier` with `Transaction.legacyOne`, and expects `true`.
  With the digest bytes reversed, `e` is 1 instead of `2^248`, and the test expects `false`.
- A high S: the same signature with S replaced by `n − S`, encoded again in DER.
  Core normalizes S before it verifies (D50, line 184), so the test expects `true`.
- Overflow: the same signature with R replaced by `n`, and with S replaced by a 33-byte value.
  The lax parser stores zero for both scalars (D50, lines 132 to 164), and `secp256k1_ecdsa_sig_verify` rejects a zero R, so the test expects `false`.
- Steps 1 to 4 of `CPubKey::Verify`: each gives `false`. The cases are an invalid key length, a key off the curve, the empty signature and a signature that the lax parser rejects.
-/

namespace KnownAnswers.CoreVerifier

open DogeLib DogeLib.Script DogeLib.Cryptography.Secp256k1
open KnownAnswers.Sha256Cavp (parseHex)

/-- Hex to a byte list. Malformed hex gives the empty list, which the length check or the expected result then rejects. -/
def hex (s : String) : List UInt8 :=
  match parseHex s with
  | .ok b => b.toList
  | .error _ => []

/-- The 64-byte `x ‖ y` inputs of `run_ec_pubkey_parse_test` (D57, lines 5231 to 5398), with `xvalid` and `yvalid`. -/
def parsePoints : List (String × Bool × Bool) :=
  -- `valid`: lines 5231 to 5316.
  [ "0000000000000000000000000000425200000000000000000000000000000000000064efa17b7761e1e42706989fb483b8d2d49bf78fae9803f099b834edeb00",
    "7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee4218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2c0e994b14ea72f8c3eb95c71ef692575e775058332d7e52d0995cf8038871b67d",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2cf166b4eb158d073c146a38e1096da8a188afa7ccd281ad2f66a307fb778e45b2",
    "00000000000000000000000000000000000000000000000000000000000000014218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "0000000000000000000000000000000000000000000000000000000000000001bde70df51939b94c9c24979fa7dd04ebd9b3572da7802290438af2a681895441",
    "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff507fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f673fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b5fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e",
    "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff5070000000000000000000000000000000000000000000000000000000000000001",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f6730000000000000000000000000000000000000000000000000000000000000001",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b50000000000000000000000000000000000000000000000000000000000000001"
  ].map (·, true, true) ++
  -- `onlyxvalid`: lines 5317 to 5347.
  [ "1fe1e5ef3fceb5c135ab7741333ce5a6e80d68167653f6b2b24bcbcfaaaff507fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "cbb0deab125754f1fdb2038b0434ed9cb3fb53ab735391129994a535d925f673fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "146d3b65add9f54ccca28533c88e2cbc63f7443e1658783ab41f8ef97c2a10b5fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30",
    "00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000003"
  ].map (·, true, false) ++
  -- `invalid`: lines 5348 to 5398.
  [ "0a2d2ba93507f1df233770c2a797962cc61f6d15da14ecd47d8d27ae1cd5f8530000000000000000000000000000000000000000000000000000000000000001",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc304218f20ae6c646b363db68605822fb14264ca8d2587fdd6fbc750d587e76a7ee",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30bde70df51939b94c9c24979fa7dd04ebd9b3572da7802290438af2a681895441",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2ef484145cb0149b825dff412fa052a83fcb72db61d56f3770ce066b7349a2aa28",
    "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e0b7beba34feb647da200bed05fad57c0348d249e2a90c88f31f9948bb65d5207",
    "00000000000000000000000000000000000000000000000000000000000000008f537eefdfc1606a0727cd69b4a7333d38ed44e3932a7179eecb4b6fba9360dc",
    "000000000000000000000000000000000000000000000000000000000000000070ac8110203e9f95f8d832964b58ccc2c712bb1c6cd58e861134b48f456c9b53"
  ].map (·, false, false)

/--
`ec_pubkey_parse_pointtest` (D57, lines 5154 to 5225) for one input.
Returns the number of failures, and the numbers of keys that parsed by `xpass` and by `ypass`.
-/
def pointTest (input : List UInt8) (xvalid yvalid : Bool) : Nat × Nat × Nat := Id.run do
  let mut failures := 0
  let mut xCount := 0
  let mut yCount := 0
  let x := ofBytesBE (input.take 32)
  let y := ofBytesBE (input.drop 32)
  let ysign := (input.getD 63 0 &&& 1).toNat + 2
  for len in [3:66] do
    for i in [0:256] do
      let key := (i.toUInt8) :: input.take (len - 1)
      let xpass := xvalid && len == 33 && (i &&& 254) == 2
      let ypass := xvalid && yvalid && (i &&& 4) == (if len == 65 then 4 else 0) &&
        (i == 4 || (i &&& 251) == ysign) && (len == 33 || len == 65)
      match parsePubKey key with
      | some (.affine px py) =>
        let ok := (xpass || ypass) && px.val == x &&
          (len != 33 || (py.val % 2 == 1) == (i == 3)) &&
          (!ypass || (py.val % 2) + 2 == ysign && py.val == y)
        if ok then
          if xpass then xCount := xCount + 1
          if ypass then yCount := yCount + 1
        else failures := failures + 1
      | some .infinity => failures := failures + 1
      | none => if xpass || ypass then failures := failures + 1
  return (failures, xCount, yCount)

/-- The DER encoding of a nonnegative integer, with a zero byte before a set top bit. -/
def derInt (v : Nat) : List UInt8 :=
  let rec bytes (fuel v : Nat) (acc : List UInt8) : List UInt8 :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if v = 0 then acc else bytes fuel (v / 256) ((v % 256).toUInt8 :: acc)
  let b := bytes 64 v []
  let b := if b.isEmpty then [0] else b
  let b := if b.headD 0 &&& 0x80 != 0 then 0 :: b else b
  0x02 :: (b.length.toUInt8) :: b

/-- A DER signature of two integer encodings. -/
def derSig (r s : List UInt8) : List UInt8 := 0x30 :: (r.length + s.length).toUInt8 :: (r ++ s)

/-- Input 1 of the `SIGHASH_SINGLE` bug transaction of `tx_valid.json` (D30), lines 53 to 56: R, S and the key. -/
def oneR : Nat := 0xc9cdd08798a28af9d1baf44a6c77bcc7e279f47dc487c8c899911bc48feaffcc
def oneS : Nat := 0x503c5c50ae3998a733263c5c0f7061b483e2b56c4c41b456e7d2f5a78a74c077
def oneKey : List UInt8 := hex "02d5c25adb51b61339d2b05315791e21bbe80ea470a49db0135720983c905aace0"
/-- The signature bytes of that input, without the hash-type byte `03`. -/
def oneSig : List UInt8 :=
  hex "3045022100c9cdd08798a28af9d1baf44a6c77bcc7e279f47dc487c8c899911bc48feaffcc0220503c5c50ae3998a733263c5c0f7061b483e2b56c4c41b456e7d2f5a78a74c077"

/-- Runs the parse test and the hand cases. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  let mut xTotal := 0
  let mut yTotal := 0
  for (h, xvalid, yvalid) in parsePoints do
    let input := hex h
    unless input.length == 64 do throw (IO.userError "point length")
    let (f, xs, ys) := pointTest input xvalid yvalid
    if f != 0 then IO.eprintln s!"FAIL ec_pubkey_parse_pointtest {h}: {f} failures"
    failures := failures + f
    xTotal := xTotal + xs
    yTotal := yTotal + ys
  -- `xpass`: each of the 16 points with a valid `x` parses with 33 bytes and the first byte `02` or `03`.
  -- `ypass`: each of the 12 valid points parses with 33 bytes and its parity byte, with `04`, and with its hybrid byte.
  unless parsePoints.length == 23 && xTotal == 32 && yTotal == 36 do
    IO.eprintln s!"FAIL ec_pubkey_parse_pointtest counts: {xTotal} xpass, {yTotal} ypass"
    failures := failures + 1
  let reversed : Hash256 := ⟨Transaction.legacyOne.val.reverse, by simp [Transaction.legacyOne]⟩
  let n := secp256k1Order
  let cases : List (String × List UInt8 × List UInt8 × Hash256 × Bool) := [
    ("digest one", oneSig, oneKey, Transaction.legacyOne, true),
    ("digest one reversed", oneSig, oneKey, reversed, false),
    ("re-encoded signature", derSig (derInt oneR) (derInt oneS), oneKey, Transaction.legacyOne, true),
    ("high S", derSig (derInt oneR) (derInt (n - oneS)), oneKey, Transaction.legacyOne, true),
    ("high S, digest reversed", derSig (derInt oneR) (derInt (n - oneS)), oneKey, reversed, false),
    ("R overflow", derSig (derInt n) (derInt oneS), oneKey, Transaction.legacyOne, false),
    ("S of 33 bytes", derSig (derInt oneR) (0x02 :: 33 :: 0x01 :: List.replicate 32 0), oneKey,
      Transaction.legacyOne, false),
    ("invalid key length", oneSig, oneKey.dropLast, Transaction.legacyOne, false),
    ("key off the curve", oneSig, 0x04 :: hex (parsePoints[15]!.1), Transaction.legacyOne, false),
    ("empty signature", [], oneKey, Transaction.legacyOne, false),
    ("lax parser rejects", [0x31] ++ oneSig.drop 1, oneKey, Transaction.legacyOne, false)
  ]
  for (label, sig, key, digest, expected) in cases do
    let got := coreVerifier sig key digest
    unless got == some expected do
      IO.eprintln s!"FAIL coreVerifier {label}: got {got}"
      failures := failures + 1
  -- The re-encoded signature is the corpus signature, so the hand encodings start from Core's bytes.
  unless derSig (derInt oneR) (derInt oneS) == oneSig do
    IO.eprintln "FAIL coreVerifier: DER re-encoding differs from the corpus signature"
    failures := failures + 1
  IO.println s!"public-key parse test: {parsePoints.length} points, 256 first bytes, lengths 3 to 65, {xTotal} xpass and {yTotal} ypass parses, {failures} failures"
  IO.println s!"coreVerifier: {cases.length} hand cases"
  return failures

end KnownAnswers.CoreVerifier

/-- Named checks for Script known answers, in alphabetical order. -/
def KnownAnswers.Script.checks : List (String × IO Nat) := [
  ("coreVerifier", KnownAnswers.CoreVerifier.check),
  ("multisigRecovery", KnownAnswers.MultisigRecovery.check),
  ("scriptEval", KnownAnswers.ScriptEval.check),
  ("scriptNum", KnownAnswers.ScriptNum.check),
  ("scriptReader", KnownAnswers.Script.check),
  ("scriptSignature", KnownAnswers.ScriptSignature.check),
  ("scriptVerify", KnownAnswers.ScriptVerify.check),
  ("signatureCode", KnownAnswers.SignatureCode.check),
  ("signatureEncoding", KnownAnswers.SignatureEncoding.check),
  ("txSpends", KnownAnswers.TxSpends.check)
]
