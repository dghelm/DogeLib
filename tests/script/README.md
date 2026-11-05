# Script instruction and state known answers

The `KnownAnswers.ScriptState` section in `tests/KnownAnswers.lean` holds fixed expected reader results and state-reset checks.
`lake test` runs them through the compiled definitions.
No test executes Script opcodes or runs Core.

All Core references use `e0a1c157791544e818c901bd9341896965afbf9d` from [SOURCES.md](../../SOURCES.md).
The expected bytes and cursors follow `CScript::GetOp2`, `src/script/script.h` lines 502 to 552.
The tests keep length fields and payloads literal and never obtain expectations from the reader under test.

The successful push cases include these exact entries from `src/test/data/script_tests.json`:

- `["0x01 0x0b", "11 EQUAL", "P2SH,STRICTENC", "OK", "push 1 byte"]`.
- `["0x02 0x417a", "'Az' EQUAL", "P2SH,STRICTENC", "OK"]`.
- `["0x4c 0x01 0x07", "7 EQUAL", "P2SH,STRICTENC", "OK", "0x4c is OP_PUSHDATA1"]`.
- `["0x4d 0x0100 0x08", "8 EQUAL", "P2SH,STRICTENC", "OK", "0x4d is OP_PUSHDATA2"]`.
- `["0x4e 0x01000000 0x09", "9 EQUAL", "P2SH,STRICTENC", "OK", "0x4e is OP_PUSHDATA4"]`.
- `["0x4c 0x00", "0 EQUAL", "P2SH,STRICTENC", "OK"]`, and its PUSHDATA2 and PUSHDATA4 counterparts.

Only their instruction bytes and decoded push values are tested here.
Their spend expectations require later execution stages.
The direct 75-byte push uses repeated separator bytes instead of the JSON case's ASCII payload.
The expected size 75 follows the direct-push branch of `GetOp2`.
The zero opcode pushes an empty byte string.
Opcodes above PUSHDATA4 have no immediate push payload, including OP_1 and OP_INVALIDOPCODE.

Derived boundary cases cover every proper length-field prefix for PUSHDATA1, PUSHDATA2 and PUSHDATA4.
All leave the failure cursor just after the opcode, because Core checks the whole field before advancing.
A short payload of each push kind leaves the failure cursor after the whole header.
Additional cases test nonzero high length bytes, the maximum four-byte length, nonzero starting offsets, EOF and invalid cursors.
Little-endian lengths of 256 are also checked with complete payloads through PUSHDATA2 and PUSHDATA4.

For `02 ab ab ab`, iteration returns a three-byte push followed by one separator instruction.
For `02 ab ab ab 4d 01`, it returns those same instructions and truncation at cursor 5.
The payload's separator bytes are never returned as instructions.

Reset expectations follow `EvalScript`, `src/script/interpreter.cpp` lines 248 to 276.
Main-stack transfer follows `VerifyScript` lines 1425 to 1432.
The test starts with nonempty local state and byte strings that include empty bytes and negative zero.
It checks preservation of those byte strings and reset of the local fields, without interpreting stack values as numbers.
