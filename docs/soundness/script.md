# Soundness: Script Execution and Worked Properties

This file states what the Script interpreter, encoding, signature-opcode, lock-time, `VerifyScript`, and worked-property proofs establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: Instruction reading, execution state, signature-code preparation, script numbers, `EvalScript`, DER and key encodings, signature and lock-time opcodes, `VerifyScript`, and worked properties.
- **Specification modules**: `DogeLib.Script.*` (`Instruction`, `State`, `SignatureCode`, `Number`, `Error`, `Flags`, `Eval`, `SignatureEncoding`, `Signature`, `Verify`, `MultisigRecovery`).
- **Proof modules**: `DogeLib.Script.Proofs.*` (`Instruction`, `State`, `SignatureCode`, `Number`, `Eval`, `SignatureEncoding`, `Signature`, `Verify`, `MultisigRecovery`, `CheckerExtension`, `FixedDigest`).
- **Key boundaries**: Evaluation covers `SIGVERSION_BASE` and seven supported flags, while unsupported flags return `unsupported` and say nothing about Core (A5).
  Claims about `verifyLegacySpend` hold relative to the verifier parameter, and `coreVerifier` inherits the secp256k1 arithmetic claim in [cryptography.md](cryptography.md#secp256k1-public-key-parser-and-cores-verifier).

## Script instruction reader and execution state

`DogeLib.Script.Instruction` specifies one call of Core's `GetOp2` at a cursor (SOURCES.md, D24).
`readInstruction` is defined through `Transaction.readOp`, so the interpreter and the legacy signature serializer decode a script with the same definition.
`DogeLib.Script.State` specifies the state of one `EvalScript` call, its reset at the start of each call, and the main-stack hand-off of `VerifyScript` (D3).
The theorems are in `DogeLib.Script.Proofs.Instruction` and `DogeLib.Script.Proofs.State`.
For every script `s` and cursor `pc`:

- `readInstruction_eq_instruction_iff`: the reader reads instruction `i` exactly when the bytes from `pc` start with the bytes of `i`. Those bytes must be `opcode :: lengthField ++ pushed` under `InstructionEncoding`. That relation states the width of the length field and the data size without the reader. So the reader keeps the exact bytes of every push, including a nonminimal one.
- `readInstruction_eq_instruction_iff_readOp` and `readInstruction_eq_fail_iff_readOp`: the reader succeeds and fails where `readOp` does, with the same opcode and bytes.
- `readInstruction_consumes`: after an instruction, the next cursor is after `pc` and at most the length of `s`. The bytes from `pc` are the instruction bytes and then the bytes from the next cursor.
- `readInstruction_atEnd_iff` and `readInstruction_truncated_iff`: the reader reports the end exactly when `pc` is at or after the end. It reports a short push exactly when a push opcode is at `pc` and its length field or its data is short. The cursor is then after the opcode or after the length field, as `GetOp2` leaves it.
- `IsBoundary.not_inside`: no instruction boundary lies inside an instruction that starts at a boundary. So a loop of reads from cursor 0 never reads a byte of pushed data as an opcode.

For the state:

- `init_wellFormed`: the start of every call satisfies `ExecState.WellFormed`, for every script and caller stack.
- `handOff_eq_iff`: two states hand off the same start state exactly when their main stacks are equal.
- `WellFormed.advance` and `WellFormed.markSeparator`: a move of the cursor past an instruction that the reader reads, and the separator update `pbegincodehash = pc`, keep the invariants.

`truncated` reports the opcode byte and the short part, where Core returns `OP_INVALIDOPCODE` and an empty vector.
Both `atEnd` and `truncated` correspond to Core's `false`.

The correspondence with `GetOp2` covers a script of fewer than 2^31 bytes.
Core's `CScript` is a `prevector` with a `uint32_t` size and an `int32_t` iterator difference (`src/prevector.h`, line 34).
`GetOp2` tests `end() - pc` in that type, and converts it to `unsigned int` before the test of the push size (D24, line 543).
`readOp` and `readInstruction` compare natural-number lengths, and `isPushOnly` and `scriptCodeBytes` inherit the bound.
`EvalScript` rejects a script above 10,000 bytes before it reads an instruction, so the bound concerns only direct calls of those four definitions.

`evalInstruction_wellFormed` in [Script evaluation](#script-evaluation-one-evalscript-call) shows that each successful step of the evaluator keeps these invariants and the combined stack limit.
The hand-off theorems cover the two `EvalScript` calls of `VerifyScript`, not the P2SH copy and restore of the stack.

That the definitions are Core's rests on a reading of D24 and D3 (A1) and on the known answers.
`lake test` runs 50 single reads and 8 loops with hand-derived results, 15 of them from 14 records of Core's `script_tests.json`.
It also runs `init` and `handOff` on one state with nonempty locals and raw stack entries.
Core itself does not run.

The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `init_fExec`, `handOff_stack`, `handOff_altstack`, `handOff_pc`, `handOff_beginCodeHash`, `handOff_vfExec`, `handOff_opCount` | None |
| `readInstruction_atEnd_iff`, `readInstruction_instruction_unique`, `init_wellFormed`, `handOff_eq_iff`, `handOff_wellFormed`, `WellFormed.markSeparator` | `propext` |
| `readInstruction_eq_instruction_iff_readOp`, `readInstruction_eq_fail_iff_readOp`, `readInstruction_eq_truncated_iff_readOp`, `WithinStackLimit.handOff` | `propext`, `Quot.sound` |
| `readInstruction_eq_instruction_iff`, `readInstruction_consumes`, `readInstruction_nonpush`, `readInstruction_truncated_iff`, `IsBoundary.le_length`, `IsBoundary.eq_or_next_le`, `IsBoundary.not_inside`, `WellFormed.advance`, `WellFormed.pc_le_length`, `WellFormed.beginCodeHash_le_length` | `propext`, `Classical.choice`, `Quot.sound` |

## Script signature-code preparation

`Script.SignatureCode` specifies Core's vector push encoding and legacy script-code preparation (SOURCES.md, D24 and D3).
It reuses `Transaction.findAndDelete`, including its `Nat` count and the exclusion of Core counts above `INT_MAX`.
`readInstruction_pushEncoding` proves that every payload shorter than 2^32 bytes reads as one instruction with exactly that payload and any tail unread.
`pushHeader_encoding` gives the length-field width and exact payload size.
PUSHDATA4 lengths wrap modulo 2^32 outside that domain, as Core's `WriteLE32` does.
Script's 520-byte limit for pushed items lies within the round-trip domain.

`findAndDelete_traversal` proves that every input and pattern follow `DeletionTraversal`, with the exact output and count.
Each pass removes leading copies, retains one whole instruction without a search inside it, and continues at its end.
A failed read preserves every remaining byte after leading deletions, including bytes that the failed reader did not consume.
`dropMatches_decomposition` identifies the removed prefix, and `dropMatches_exhausted` excludes a match at the cursor after leading deletions for every nonempty pattern.
The cursors belong to the input after preceding deletions.
They need not be boundaries of the original script when an arbitrary pattern ends inside an instruction.

The result can contain a match that one pass creates across retained pieces.
For example, deleting `00 51` from `00 00 51 51` leaves `00 51`, as Core's test requires.
The traversal theorem does not assert that the final bytes contain no matches.

`effectiveScriptCode_nil`, `effectiveScriptCode_single` and `effectiveScriptCode_append` give suffix selection, single-signature deletion and ordered composition for every input.
The signature list follows `stacktop(-isig-k)` for increasing `k`, nearest the stack top first, and includes each signature's hash-type byte.
The caller establishes the separator cursor and supplies the signatures.
The existing signature serializer removes remaining separator instructions.

`checkSigStep` calls it with the one signature of `OP_CHECKSIG`, and `checkMultisigStep` with all signatures of `OP_CHECKMULTISIG`, from the separator cursor of the execution state.
[Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker) states their theorems.
No theorem establishes commutation of signature deletion passes.

`lake test` runs all sixteen cases of Core's `script_FindAndDelete` (D46), eight additional malformed suffix cases and eight push-size boundaries.
It also checks exact intermediate and final bytes for two signature deletions, including retained separator and payload bytes.
The expectations come from Core's assertions and a reading of D24 and D3.
Core itself does not run.
These finite tests do not prove equivalence to compiled Core.

The definitions add no axiom, cryptographic hypothesis or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `pushLengthBytes_length` | `propext` |
| `readInstruction_pushEncoding` | `propext`, `Classical.choice`, `Quot.sound` |
| `leValue_pushLengthBytes`, `pushHeader_encoding`, `findAndDelete_empty`, `dropMatches_decomposition`, `dropMatches_exhausted`, `findAndDeleteLoop_traversal`, `DeletionTraversal.zero`, `findAndDeleteLoop_empty`, `findAndDelete_eq_loop`, `findAndDelete_traversal`, `findAndDeleteLoop_malformed`, `effectiveScriptCode_nil`, `effectiveScriptCode_single`, `effectiveScriptCode_append` | `propext`, `Quot.sound` |

The effective script code keeps the parsed-script hypothesis of the transformation-reference theorem.
`readOp_pushEncoding`: `readOp` reads the push encoding of a payload shorter than 2^32 bytes as one instruction, and `scanOps_pushEncoding` follows.
`effectiveScriptCode_scanOps` takes a script of at most 2^32 bytes whose suffix from the cursor parses completely.
For every signature list, the effective script code then parses completely.

It needs no hypothesis on the signatures.
A push of a signature of 2^32 bytes or more is longer than the script code, so it never matches.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `length_lt_pushEncoding` | `propext`, `Quot.sound` |
| `readOp_pushEncoding`, `scanOps_pushEncoding`, `effectiveScriptCode_scanOps` | `propext`, `Classical.choice`, `Quot.sound` |

## Script numbers and truth values

`DogeLib.Script.Number` specifies Core's `CScriptNum` and `CastToBool` (SOURCES.md, D24 and D3).
The theorems are in `DogeLib.Script.Proofs.Number`.
For every integer `n`, byte string `b`, flag `req` and size `maxSize`:

- `value_encode`: `value (encode n) = n`.
- `isMinimal_encode` and `isMinimal_iff_encode_value`: `b` passes Core's minimality test exactly when `encode (value b) = b`. So the test accepts exactly one byte string for each integer, and rejects negative zero and every other string with a removable high byte.
- `encode_length_le_iff`: `encode n` has at most `k` bytes exactly when `2 |n| < 256 ^ k`. So every integer within ±(2^31 − 1) has at most four bytes (`encode_length_le_four`), and the sum or difference of two of them has at most five (`encode_add_length_le_five`, `encode_sub_length_le_five`).
- `decode_eq_ok_iff`, `decode_eq_overflow_iff` and `decode_eq_nonMinimal_iff` give every result of `decode`. Too many bytes give `overflow` whatever the flag. `nonMinimal` needs a length within the size, the flag and a failed test.
- `decode_encode`: if `2 |n| < 256 ^ maxSize`, then `decode (encode n) req maxSize = .ok n`. `decode_false`: without the flag, a string within the size gives its value, also when it is not minimal.
- `decode_natAbs_lt`: every decoded value satisfies `2 |n| < 256 ^ maxSize`. So a default-size decode lies within ±(2^31 − 1), a size-5 decode within ±(2^39 − 1), and a decode of up to 8 bytes within ±(2^63 − 1) (`decode_int64`).
- `getint_eq_max_min`: `getint n` is the clamp of `n` to `[-2^31, 2^31 - 1]`. `getint_decode_default`: it never changes a value that a default-size decode returns.
- `castToBool_eq_false_iff_value` and `castToBool_eq_false_iff`: `castToBool b` is false exactly when `value b = 0`, that is, when `b` is zero bytes, or zero bytes and then one `0x80`. This holds at every length. `castToBool_encode`: `castToBool (encode n)` is `n ≠ 0`.

The definitions use `Int`, and Core uses `int64_t` and `int`.
They agree only where Core's C++ is defined:

- `set_vch` shifts byte `i` left by `8*i` bits (D24, line 360). A string of more than eight bytes needs a shift of 64 bits or more, which is undefined. The constructor checks the size first (lines 220 to 237), so this shift is reachable only with a size argument above 8. `decode_int64` covers the defined sizes, and the interpreter decodes at most five bytes (D3, lines 377 and 408).
- `serialize` negates its argument (D24, line 326), which is undefined for `-2^63`. `encode` takes every integer.
- `getint` assumes a 32-bit `int`. Every supported Core target has one, but no theorem or check here establishes it. On another width Core's `getint` stays defined and clamps to that width's limits (D24, lines 307 to 310).
- `CastToBool` counts with an `unsigned int` (D3, line 40). For strings of at most `UINT_MAX` bytes it agrees with `castToBool`. On a longer string the counter wraps, and Core's loop can repeat without end, while `castToBool` returns a result. The theorems about `castToBool` hold at every length, but the Core correspondence covers only that domain.

That the definitions are Core's rests on a reading of D24 and D3 (A1) and on the known answers.
`lake test` runs 21 hand-derived encodings, 24 decodes, 9 `getint` cases and 13 `castToBool` cases.
It also runs the 247 integers of the `creation` test of `scriptnum_tests.cpp` (D44).
That test compares Core with its own 0.10.0 copy, so it gives the integers but no expected bytes.
Core itself does not run in these tests.

The Core comparison of `script.eval` and `script.verify_legacy` reaches these definitions only through the numeric opcodes and conditionals of the scripts that it sends ([docs/comparison-evidence.md](../comparison-evidence.md#the-comparison)).
No request compares them directly, and the comparison covers only the requests that it sends.

`OP_PICK`, `OP_ROLL` and the numeric opcodes in `Script.execOpcode` map a decode failure to `SCRIPT_ERR_UNKNOWN_ERROR`, as the `catch` of `EvalScript` does (D3, lines 1037 to 1040).
[Script evaluation](#script-evaluation-one-evalscript-call) states how the numeric opcodes stay within the defined domain of Core's `int64_t` operators.
The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `castToBool_concat` | `propext` |
| `isMinimal_encode`, `natAbs_value_lt`, `decode_eq_ok_iff`, `decode_eq_overflow_iff`, `decode_eq_nonMinimal_iff`, `decode_false`, `decode_natAbs_lt`, `decode_default_natAbs_le`, `decode_five_natAbs_le`, `getint_eq_max_min`, `getint_of_ge`, `getint_of_le`, `castToBool_eq_false_iff_value`, `castToBool_eq_false_iff` | `propext`, `Quot.sound` |
| `value_encode`, `isMinimal_iff_encode_value`, `encode_length_le_iff`, `encode_length_le_four`, `encode_add_length_le_five`, `encode_sub_length_le_five`, `decode_encode`, `decode_encode_default`, `decode_int64`, `getint_eq_self_iff`, `getint_mem`, `getint_decode_default`, `castToBool_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The supporting byte and little-endian lemmas of the module use the same three axioms or fewer.

## Script evaluation, one `EvalScript` call

`DogeLib.Script.Eval` specifies one call of Core's `EvalScript` in `SIGVERSION_BASE` (SOURCES.md, D3).
It covers the opcodes of stages 2 and 3 of design record 0003: control flow, stack operations, numbers, hashes and signatures.
[Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker) states the claims about the signature opcodes.
`DogeLib.Script.Error` gives Core's `ScriptError_t` (D49), and `DogeLib.Script.Flags` gives the flag bits of D25.
The theorems are in `DogeLib.Script.Proofs.Eval`.

`evalScript checker flags script stack` returns one of three results.
`ok` is Core's `true` with `SCRIPT_ERR_OK`, and `rejected e` is Core's `false` with error `e`.
`unsupported r` means that this stage lacks a capability that the call needs, and says nothing about Core's verdict.
A flag outside the seven of design record 0003 is unsupported before any other check.
Without a checker, an executed signature opcode is unsupported, and so is `OP_CHECKLOCKTIMEVERIFY` or `OP_CHECKSEQUENCEVERIFY` with its flag set.
A check that the checker cannot decide is also unsupported.

For every flag set, script and caller stack:

- `evalScript_unsupportedFlags`: a flag bit outside `supportedFlags` gives `unsupported`, with exactly those bits.
- `evalScript_scriptSize`: with supported flags, a script of more than 10,000 bytes gives `SCRIPT_SIZE`.
- `evalScript_ok`: a successful call ends at the end of the script, with an empty `vfExec`, in a state that satisfies `ExecState.WellFormed`. If the script is not empty, the two stacks hold at most 1,000 items together.
- `evalScript_flags_congr`: two supported flag sets that agree on every supported flag except `P2SH` give the same result. So `P2SH` does not change one call.

For the loop and each instruction:

- `evalLoop_atEnd`: at the end of the script, the call succeeds exactly when `vfExec` is empty, and gives `UNBALANCED_CONDITIONAL` otherwise. `evalLoop_truncated`: a short push gives `BAD_OPCODE`.
- `evalInstruction_pushSize`, `evalInstruction_opCount` and `evalInstruction_disabled`: the push size, the opcode count and the disabled opcodes are checked in Core's order, whether or not the branch executes. `evalInstruction_verif`: `OP_VERIF` and `OP_VERNOTIF` give `BAD_OPCODE` in a skipped branch too.
- `evalInstruction_skipped`: in a skipped branch, an opcode outside `OP_IF` to `OP_ENDIF` that passes those checks only counts. The two stacks, `vfExec` and the separator cursor stay unchanged.
- `evalInstruction_wellFormed`: from a state that satisfies `ExecState.WellFormed`, a successful step and the cursor move give a state that satisfies it, within the combined stack limit. `OP_CHECKMULTISIG` raises the opcode count by its key count, and the invariant still bounds it by 201.
- `execOpcode_checker_congr`: every opcode outside `0xac` to `0xaf`, `0xb1` and `0xb2` gives the same result for any checker and any script. So those opcodes keep their stage-2 results. `OP_CHECKLOCKTIMEVERIFY` (`0xb1`) and `OP_CHECKSEQUENCEVERIFY` (`0xb2`) can depend on the checker, as [Script lock times and `VerifyScript`](#script-lock-times-and-verifyscript) states.
- The `execOpcode_*` theorems give the stack effect of each implemented opcode, its underflow error, and each unsupported case.

For the numeric and hash opcodes:

- One theorem per opcode, from `execOpcode_1add` to `execOpcode_within` and from `execOpcode_ripemd160` to `execOpcode_hash256`, gives its stack effect. The numeric effect theorems assume successful four-byte decodes without the minimal requirement. The hash effect theorems require only the stated stack shape.
- `execOpcode_numeric_underflow` and `execOpcode_hash_underflow`: too few items give `INVALID_STACK_OPERATION`. `execOpcode_numeric_decode`: an operand that fails to decode gives `UNKNOWN_ERROR`.
- `execOpcode_addSub_length`: `OP_1ADD`, `OP_1SUB`, `OP_ADD` and `OP_SUB` push at most five bytes. `execOpcode_numeric_length_le_four`: every other numeric opcode that pushes a result pushes at most four bytes.

Core computes these opcodes in `int64_t` with the operators of `CScriptNum` (D24, lines 244 to 297), and the definitions compute in `Int`.
They agree where no operator overflows and no assert fires.
Each operand is a four-byte decode and lies within ±(2^31 − 1) (`decode_default_natAbs_le`), so this holds for every operand:

- `numericOperand_ne_int64Min`: the operand of `OP_NEGATE` and `OP_ABS` is not `INT64_MIN`, which `operator-()` asserts (line 273).
- `numericOperand_add_one_le` and `numericOperand_sub_one_ge`: the asserts of `operator+=` and `operator-=` with 1 hold for `OP_1ADD` and `OP_1SUB` (lines 285 and 293).
- `numericOperand_addSub_mem`: the sum and the difference of `OP_ADD` and `OP_SUB` lie within `int64_t`. `operator+` and `operator-` (lines 258 and 259) have no assert.

The comparisons, `OP_MIN`, `OP_MAX` and `OP_WITHIN` only compare values.
The hash opcodes use the hash definitions of the `Cryptography` layer, and inherit the boundaries that their sections state.
`OP_NUMEQUALVERIFY` pushes its comparison and pops it again in Core (D3, lines 817 to 823).
The definition pops both operands directly, which differs only in an intermediate state that no check reads.

The evaluator takes no fuel.
`evalLoop` recurses on the distance from the cursor to the end of the script.
`readInstruction_progress`, in the specification, shows that each instruction moves the cursor forward.
So every call returns a result that depends only on the flags, the script and the caller's stack.

Three boundaries limit the claim:

- Core compares the operand of `OP_PICK` and `OP_ROLL` with `(int)stack.size()` (D3, line 657). Here sizes are `Nat` values. The two agree when the main stack has fewer than 2^31 items. After the first instruction the two stacks hold at most 1,000 items. So only a caller's stack of 2^31 items or more lies outside the correspondence.
- `OP_IF`, `OP_NOTIF`, `OP_VERIFY` and `OP_IFDUP` use `castToBool`, which inherits the boundary of [Script numbers and truth values](#script-numbers-and-truth-values). Core's `CastToBool` counts with an `unsigned int` (D3, line 40), so on an item of more than `UINT_MAX` bytes its loop can repeat without end. `castToBool` returns a result. A push holds at most 520 bytes, so such an item can come only from the caller's stack. Neither Core nor `evalScript` checks the size of a caller's item. For example, `OP_VERIFY` on one caller's item of 2^32 zero bytes gives `VERIFY` here, and Core's loop does not end.
- `MINIMALDATA`, `DISCOURAGE_UPGRADABLE_NOPS` and `MINIMALIF` are unsupported flags, so the evaluator has no `CheckMinimalPush`, no NOP discouragement and no minimal `OP_IF` check. `MINIMALIF` applies only to `SIGVERSION_WITNESS_V0` at the pin.
- An unsupported result can hide a Core rejection. For example, without a checker, `OP_CHECKSIG` on an empty stack is unsupported here, and Core gives `INVALID_STACK_OPERATION`.

That the definitions are Core's rests on a reading of D3 and D24 (A1) and on the known answers.
`lake test` runs 140 hand cases and 46 underflow cases, with results written by hand from D3 and D24.
The expected digests of the hash cases come from Core's `script_tests.json` (D45).
It also runs all 1,193 records of Core's `script_tests.json` (D45) through `verifyScript`.
The checker is `transactionChecker` over the record's spending transaction, with `coreVerifier`.
925 records agree with Core's expected result, 563 acceptances and 362 rejections, and none disagrees.

268 records are unsupported.
Of those, 165 have an unsupported flag and 103 have a witness.
Core itself does not run.

The definitions add no hypothesis or axiom.
The correspondence with Core covers a caller's stack of fewer than 2^31 items, each of at most `UINT_MAX` bytes.
The two boundaries above are its only execution boundaries.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readInstruction_progress`, `evalScript_unsupportedFlags`, `evalScript_scriptSize`, `evalScript_flags_congr`, `evalLoop_atEnd`, `evalLoop_truncated`, `evalLoop_instruction`, the `evalInstruction_*` theorems except `evalInstruction_wellFormed`, `execOpcode_frame`, `execOpcode_flags_congr`, `execOpcode_checker_congr`, `checkSignatureEncoding_flags_congr`, `checkPubKeyEncoding_flags_congr`, `encode_ofBool`, the `execOpcode_*` effect, underflow and decode theorems, `numericOperand_ne_int64Min`, `numericOperand_add_one_le`, `numericOperand_sub_one_ge` | `propext`, `Quot.sound` |
| `evalInstruction_wellFormed`, `evalLoop_ok`, `evalScript_ok`, `execOpcode_addSub_length`, `execOpcode_numeric_length_le_four`, `numericOperand_addSub_mem` | `propext`, `Classical.choice`, `Quot.sound` |

## Script signature and public-key encoding

`DogeLib.Script.SignatureEncoding` specifies the encoding checks that Core's signature opcodes run before they verify a signature (SOURCES.md, D3, D50 to D53).
The theorems are in `DogeLib.Script.Proofs.SignatureEncoding`.
For every byte string and every flag set:

- `isValidSignatureEncoding_iff`: a signature passes `IsValidSignatureEncoding` exactly when it is `derBody r s` and one hash-type byte.
  Here `r` and `s` are DER integers: not empty, first byte below `0x80`, and a leading zero only before a byte of at least `0x80`.
  Together they have at most 66 bytes.
- `laxStore_eq`: the lax parser stores `laxScalars` of the values of R and S.
  That is both values when both are below the order `n`, and zero and zero otherwise.
  Core's test that a value has more than 32 bytes never changes this result.
- `parseDerLax_derBody` and `parseDerLax_dropLast_of_isValidSignatureEncoding`: the lax parser accepts every strict-DER signature without its hash type, and stores those scalars.
- `checkLowS_iff`: `checkLowS` holds exactly when the parser succeeds and stores an S of at most `⌊n/2⌋`.
  `checkLowS_derBody_iff`: on strict DER with R and S below `n`, that is the bound on S itself.
- `checkLowS_derBody_of_overflow`: on strict DER with R or S at least `n`, `checkLowS` holds whatever S is.
  `checkSignatureEncoding_overflowExample` gives one such signature with a high S, which passes `checkSignatureEncoding` with `DERSIG`, `STRICTENC` and `LOW_S`.
- `checkSignatureEncoding_eq_sigDer_iff`, `checkSignatureEncoding_eq_sigHighS_iff` and `checkSignatureEncoding_eq_sigHashtype_iff` state when each error occurs.
  `checkSignatureEncoding_error` shows that no other error occurs, and `checkSignatureEncoding_nil` that the empty signature always passes.
  `isLowDerSignature_ne_sigDer` shows that the `SIG_DER` result of `IsLowDERSignature` is unreachable from `CheckSignatureEncoding`.
- `checkPubKeyEncoding_eq_error_iff`: the only key error is `PUBKEYTYPE`, with `STRICTENC`.
  `isCompressedOrUncompressedPubKey_iff` gives the accepted shapes, and `isValidPubKey_of_isCompressedOrUncompressedPubKey` shows that each gives a valid `CPubKey`.

The LOW_S check follows `CheckLowS` and its parser, not a bound on the S bytes of the signature.
Design record 0003, section 5, requires this case.
A verifier that normalizes S loses the original value, so the definitions do not use one.
The theorems are statements about bytes.
They say nothing about elliptic-curve points, about which signatures verify, or about libsecp256k1's compiled code.

The order `n` and the half order are copied from D53 and checked against SEC 2 (S2) by reading.
`secp256k1HalfOrder_eq` proves that the half order is `n / 2`.
No theorem derives `n` from the curve.

Core's parser compares a long-form length with `sizeof(size_t)` (D50, lines 76 and 114).
`parseDerLaxWith` takes that size as a parameter, and `parseDerLax` uses 8.
`parseDerLaxWith_eq` proves the same result for every size of at least 4 on inputs of fewer than 2^24 bytes.
So 32-bit and 64-bit builds agree on every Script stack item, which has at most 520 bytes.

`checkPubKeyEncoding` omits Core's second test, which needs `SIGVERSION_WITNESS_V0` and `WITNESS_PUBKEYTYPE` (D3, lines 219 to 221).
Design record 0003 runs only `SIGVERSION_BASE`, and that flag is unsupported.

That the definitions are Core's rests on a reading of D3, D50 to D53 (A1), and on the known answers.
`lake test` checks the 60 P2PK and P2PK NOT records of `script_tests.json` (D45) inside the milestone, and 86 hand-derived cases.
The test takes each record's signature from the top of the stack after the specified `evalScript` runs `scriptSig`.
Core itself does not run in these tests.

The Core comparison of `script.eval` and `script.verify_legacy` reaches these checks only through the signature opcodes of the scripts that it sends ([docs/comparison-evidence.md](../comparison-evidence.md#the-comparison)).
No request compares an encoding check directly, and the comparison covers only the requests that it sends.
The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `secp256k1HalfOrder_eq`, `secp256k1Order_lt`, `overflowExample_order_le`, `overflowExample_highS` | None |
| `laxScalars_of_lt` | `propext` |
| `checkLowS_iff`, `checkSignatureEncoding_eq`, `checkSignatureEncoding_nil`, `checkSignatureEncoding_of_flags`, `checkSignatureEncoding_eq_sigDer_iff`, `checkSignatureEncoding_eq_sigHighS_iff`, `checkSignatureEncoding_eq_sigHashtype_iff`, `checkSignatureEncoding_error`, `isLowDerSignature_ne_sigDer`, `isDefinedHashtypeSignature_iff`, `checkPubKeyEncoding_eq_error_iff`, `laxScalars_of_le`, `overflowExample_isValidSignatureEncoding` | `propext`, `Quot.sound` |
| `isValidSignatureEncoding_iff`, `laxStore_eq`, `parseDerLax_derBody`, `parseDerLax_dropLast_of_isValidSignatureEncoding`, `parseDerLaxWith_eq`, `checkLowS_derBody_iff`, `checkLowS_derBody_of_overflow`, `checkSignatureEncoding_overflowExample`, `isCompressedOrUncompressedPubKey_iff`, `isValidPubKey_of_isCompressedOrUncompressedPubKey` | `propext`, `Classical.choice`, `Quot.sound` |

The supporting byte and big-endian lemmas of the module use the same three axioms or fewer.

## Script signature opcodes and the checker

`DogeLib.Script.Signature` specifies the signature checker that `evalScript` takes as a parameter (SOURCES.md, D3 and D25).
`DogeLib.Script.Eval` specifies `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` with that checker (D3, lines 880 to 1026).
The theorems are in `DogeLib.Script.Proofs.Signature` and `DogeLib.Script.Proofs.Eval`.

The checker is a structure with three functions: `checkSig sig key scriptCode`, `checkLockTime n` and `checkSequence n`, each returning `Option Bool`.
[Script lock times and `VerifyScript`](#script-lock-times-and-verifyscript) covers the two lock-time functions.
`none` means that the check is unavailable, and the evaluator then reports `unsupported`, never a rejection.
`baseChecker` is Core's `BaseSignatureChecker`, which fails every check.
`transactionChecker tx nIn verify` is Core's `TransactionSignatureChecker::CheckSig` with `SIGVERSION_BASE`.
For every transaction, input index and verifier:

- `transactionChecker_invalidKey` and `transactionChecker_emptySig`: a key that fails `isValidPubKey` gives `some false`, and with a valid key so does an empty signature. Neither case depends on `verify`.
- `transactionChecker_verify`: for a valid key, a signature `sig ++ [h]` and a script code shorter than 2^64 bytes, the result is `verify sig key d`. Here `d` is `legacySignatureHash` of the script code with the hash type `h` zero-extended to 32 bits.
- `transactionChecker_verify_congr`: two verifiers that agree on that one request give the same result.
- `transactionChecker_checkSig_fixed`: when the request also satisfies `ReachesFixedDigest` for `h`, the result is `verify sig key legacyOne`.
  `transactionChecker_checkSig_fixed_congr`: two such requests give the same answer for any transactions, input indices and script codes shorter than 2^64 bytes.

For the opcodes, with any checker `c`:

- `checkSigStep_underflow`, `checkSigStep_sigEncoding` and `checkSigStep_keyEncoding`: fewer than two items, then the signature encoding, then the key encoding, each before any checker request.
- `checkSigStep_checked`: after both checks, the step asks `c` once, with the signature, the key and `effectiveScriptCode script s.beginCodeHash [sig]`. It pops both items and pushes the answer, or for `OP_CHECKSIGVERIFY` pops on `true` and gives `CHECKSIGVERIFY` on `false`. `checkSigStep_checker_congr`: no other request.
- `checkMultisigStep_empty`, `checkMultisigStep_keyCountDecode`, `checkMultisigStep_pubkeyCount`, `checkMultisigStep_opCount`, `checkMultisigStep_keyDepth` and `checkMultisigStep_sigCount`: the checks before the loop, in Core's order. The last depth check already requires the dummy, so Core's later `stack.size() < 1` (line 1010) is unreachable.
- `checkMultisigStep_counted`: after those checks, the step runs `multisigLoop` on the script code with every signature push removed. It then checks the dummy and pushes the result, with the opcode count raised by the key count.
- `checkMultisigStep_loopError`, `checkMultisigStep_dummy` and `checkMultisigStep_nullDummy`: an error in the loop comes first. Without `NULLDUMMY` any dummy is consumed. With it, a nonempty dummy gives `SIG_NULLDUMMY`.
- `evalInstruction_signature_skipped`: in a skipped branch, a signature opcode only counts as one opcode. The checker is not asked, and `OP_CHECKMULTISIG` adds no key count.

The ordered-matching property is stated over a relation `R` first.
`OrderedMatch R sigs keys` says that the signatures pair in order with a subsequence of the keys.
For every relation and all lists:

- `greedyMatch_iff`: Core's greedy loop succeeds exactly when `OrderedMatch R sigs keys` holds.
- `greedyMatch_eq_noExit`: the early exit of lines 987 to 991 does not change the result.
- `multisigLoop_ok`: when the check returns `R` on every pair of the two lists, `multisigLoop` returns the greedy result. The hypothesis covers every pair, which is stronger than the pairs that Core visits.

`checkMultisigStep_matching` instantiates this for `OP_CHECKMULTISIG`.
It assumes that the counts decode to the lengths of the lists and pass Core's checks.
It assumes that every signature and key passes its encoding check, and that `c` answers `some (R sig key)` on every pair.
It also assumes that `NULLDUMMY` is clear or the dummy is empty.
Then the step pushes `[1]` exactly when `OrderedMatch R sigs keys` holds, and `[]` otherwise.
`checkMultisigStep_matching_verify` gives the same for `OP_CHECKMULTISIGVERIFY`.
`checkMultisigStep_matching_pushOrder` states the property for the lists in script push order.

The checker is the boundary of these claims.
A result of `evalScript` with `transactionChecker` holds for Core only under the verifier-agreement hypothesis.
That hypothesis says that `verify sig key d` returns `some b` only when Core's `CPubKey::Verify` returns `b` on the same signature, key and digest.
`Script.coreVerifier` is DogeLib's instance of the parameter, and for it the hypothesis becomes an A1 claim about a definition.
[Secp256k1 public-key parser and Core's verifier](cryptography.md#secp256k1-public-key-parser-and-cores-verifier) states what is proved about it and the finite evidence from the Core comparison.
For any other verifier, no theorem establishes the hypothesis.

The two `lake test` corpus runners use `coreVerifier`.
All 925 inside-milestone records of `script_tests.json` agree with Core's expected result, including the 44 that need a verification.
All 91 required acceptances among the 159 eligible transaction inputs accept, and no input is unsupported.
A repeated key in a multisig script does not show that different people signed.

`NULLFAIL` is unsupported, so `evalScript` reports any flag set with it before it runs.
Its branches at lines 904, 905 and 996 to 998 are absent from the definitions.
`transactionChecker` gives `none` for a script code of 2^64 bytes or more, which lies outside `Transaction.Script`.
The evaluator never passes such a script code, because its script has at most 10,000 bytes.

That the definitions are Core's rests on a reading of D3 and D25 (A1) and on the known answers.
`lake test` runs 48 signature-opcode cases with a lookup-table test checker, 5 `transactionChecker` cases and one `baseChecker` case, with results written by hand from D3.
The lookup table is a test backend and says nothing about which signatures are valid.
The corpus runners above add the 925 inside-milestone records of `script_tests.json`.
[Script evaluation](#script-evaluation-one-evalscript-call) gives the 268 unsupported records and their reasons.

The oracle's `script.eval` can select `baseChecker`, and its legacy operation can select a transaction checker.
The transaction checker uses `coreVerifier`, so finite Core comparisons also cover signature-opcode results that verify a signature.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `baseChecker_checkSig`, `tail_sublist_of_cons` | None |
| `PairsMatch.length_eq`, `orderedMatch_length`, `multisigLoop_ok`, `multisigLoop_error` | `propext` |
| `transactionChecker_invalidKey`, `transactionChecker_emptySig`, `transactionChecker_verify`, `transactionChecker_verify_congr`, `transactionChecker_checkSig_fixed`, `transactionChecker_checkSig_fixed_congr`, `greedyMatchNoExit_iff`, `greedyMatchNoExit_short`, `greedyMatch_eq_noExit`, `greedyMatch_iff`, `execOpcode_signature_none`, `execOpcode_checkSig`, `execOpcode_checkMultisig`, the `checkSigStep_*` and `checkMultisigStep_*` theorems except `checkMultisigStep_matching_pushOrder`, `multisigCheck_ok`, `multisigLoop_multisigCheck_error`, `evalInstruction_signature_skipped` | `propext`, `Quot.sound` |
| `pairsMatch_append`, `pairsMatch_reverse`, `orderedMatch_reverse`, `checkMultisigStep_matching_pushOrder` | `propext`, `Classical.choice`, `Quot.sound` |

## Script lock times and `VerifyScript`

`DogeLib.Script.Eval` specifies `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` with their flags (D3, lines 350 to 427).
`DogeLib.Script.Signature` gives Core's `CheckLockTime` and `CheckSequence` (D3, lines 1274 to 1353) as `lockTimeSatisfied` and `sequenceSatisfied`, the two new fields of `transactionChecker`.
`DogeLib.Script.Verify` specifies `VerifyScript` with an empty witness (D3, lines 1409 to 1526), `IsPushOnly` and `IsPayToScriptHash` (D48), and the spend predicate `verifyLegacySpend`.
The theorems are in `DogeLib.Script.Proofs.Eval`, `DogeLib.Script.Proofs.Signature` and `DogeLib.Script.Proofs.Verify`.

For the lock-time opcodes, with any checker `c` and the opcode's flag set:

- `execOpcode_cltv_underflow`, `execOpcode_cltv_decode` and `execOpcode_cltv_negative`: an empty stack, then a top item that fails the five-byte decode, then a negative operand, each before any checker request. The `csv` theorems give the same.
- `execOpcode_cltv_checked`: a nonnegative operand goes to `c.checkLockTime`, and `true` leaves the state unchanged. `execOpcode_csv_checked` gives the same for an operand with bit 31 clear.
- `execOpcode_csv_disabled`: an operand with bit 31 set leaves the state unchanged, for every checker.
- `execOpcode_cltv_transaction`: with `transactionChecker` for an `InputContext`, a nonnegative operand passes exactly when it lies on the lock time's side of 500,000,000, does not exceed the lock time, and the input's sequence is not `0xffffffff`.
- `execOpcode_csv_transaction`: with `transactionChecker`, an operand with bit 31 clear passes exactly when the version read as `uint32_t` is at least 2, bit 31 of the sequence is clear, the masked values have the same type bit, and the masked operand does not exceed the masked sequence.

Without a checker, both opcodes with their flags are unsupported (`execOpcode_cltv`, `execOpcode_csv`), as before.
With their flags clear, they are NOPs for every checker.

These checks compare the operand with fields of the spending transaction.
They do not compare the lock time with a block height or time, and they do not establish an input's age.
Design record 0003, section 3, records that the mainnet activation of CSV at the pin is unverified.
So a CSV result may hold only for relay policy (A5).

`CheckSequence` masks the operand as an `int64_t`, and `sequenceSatisfied` masks `n.toNat`.
The two agree for `n ≥ 0`, the only operands that the opcode passes.
`transactionChecker` answers `none` for an input index outside the inputs, where Core's `vin[nIn]` is undefined behavior, so the result makes no claim.
`InputContext` requires an index below the number of inputs, so `verifyLegacySpend` never reaches that case.

For `verifyScript` with any checker `c`:

- `verifyScript_unsupportedFlags`: a flag outside the seven gives `unsupported` before any evaluation. `hasFlag_sigPushOnly_eq_false`, `hasFlag_cleanStack_eq_false` and `hasFlag_witness_eq_false` show that the branches of those flags are unreachable.
- `verifyScript_noP2sh`: without `P2SH` or without the template, the result is the two evaluations with the true-top check.
- `verifyScript_p2sh`: with `P2SH`, the template, a push-only `scriptSig` whose final stack is `S ++ [redeem]`, and a `scriptPubKey` that accepts, the result is `redeem` on `S` with the true-top check.
- `verifyScript_p2sh_notPushOnly`: the same request with a `scriptSig` that is not push-only gives `SIG_PUSHONLY`.
- `verifyScript_p2sh_saved_ne_nil`: Core's assert at line 1469 holds, so the branch of `verifyScript` for an empty saved stack is unreachable. Its value is arbitrary and is not Core's behavior.
- `evalScript_p2shTemplate`: the template on `S ++ [x]` pushes `[1]` when the HASH160 digest of `x` equals its 20 bytes, and `[]` otherwise, given room for two items.
- `verifyScript_p2sh_hash` and `verifyScript_p2sh_hash_ne`: the composition from the digest of the supplied `redeem`.
- `isPushOnly_iff`: `isPushOnly` is Core's loop over the instruction boundaries of `readInstruction`. Like Core, it treats `OP_RESERVED` as push-only.

The P2SH theorems hold for the exact supplied redeem script.
They do not say that no other redeem script has the same digest. That needs a collision hypothesis (A4).
`verifyLegacySpend` takes the previous output's script from the caller, who establishes that it belongs to the referenced outpoint.
A result of `verifyLegacySpend` holds for Core only under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).

That the definitions are Core's rests on a reading of D3, D4, D24 and D48 (A1), and on the known answers.
`lake test` runs 38 lock-time cases, 20 `verifyScript` cases, 11 `isPushOnly` cases and 3 `verifyLegacySpend` cases, with results written by hand from those sources.
On `script_tests.json`, `verifyScript` with `transactionChecker` and `coreVerifier` agrees with Core's expected result on 925 records and disagrees on none.
The oracle exposes `verifyScript` through `script.verify_legacy`, with base and transaction checker selections.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `baseChecker_checkLockTime`, `baseChecker_checkSequence` | None |
| `lockTimeSatisfied_iff`, `InputContext.getElem?_index` | `propext` |
| `transactionChecker_checkLockTime`, `transactionChecker_checkSequence`, `transactionChecker_checkLockTime_none`, `transactionChecker_checkSequence_none`, `sequenceSatisfied_iff`, `checkLockTimeStep_next`, `checkSequenceStep_next`, the `execOpcode_cltv*` and `execOpcode_csv*` theorems, `execOpcode_checker_congr`, `execOpcode_script_congr`, `isPushOnlyFrom_atEnd`, `isPushOnlyFrom_truncated`, `isPushOnlyFrom_instruction`, `verifyScript_unsupportedFlags`, `hasFlag_sigPushOnly_eq_false`, `hasFlag_cleanStack_eq_false`, `hasFlag_witness_eq_false`, `verifyScript_noP2sh`, `verifyScript_p2sh`, `verifyScript_p2sh_notPushOnly`, `verifyLegacySpend_eq` | `propext`, `Quot.sound` |
| `isPushOnlyFrom_iff`, `isPushOnly_iff`, `isPayToScriptHash_iff`, `evalScript_p2shTemplate`, `evalScript_p2shTemplate_nil`, `verifyScript_p2sh_saved_ne_nil`, `verifyScript_p2sh_hash`, `verifyScript_p2sh_hash_ne` | `propext`, `Classical.choice`, `Quot.sound` |

`InputContext.ofDecoded`, in `DogeLib.Script.Proofs.Verify`, builds the input context of an input of a transaction that `decodeBaseComplete` read.
The caller supplies an index below the number of inputs.
`Transaction.decodeBaseComplete_eq_ok_iff` and `Transaction.readBase_eq_ok_iff` give `WithinMaxSize`, and so the two count bounds.
`verifyLegacySpend_ofDecoded` unfolds the spend predicate on it to `verifyScript` with `transactionChecker` for the index.
The definition lives in the proof library, because `WithinMaxSize` does.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `InputContext.ofDecoded_tx`, `InputContext.ofDecoded_index`, `verifyLegacySpend_ofDecoded` | `propext`, `Classical.choice`, `Quot.sound` |

## Script worked property: multisig with recovery

`DogeLib.Script.MultisigRecovery` builds the redeem script of design record 0003, section 7, for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16`:
`OP_IF OP_k <keys> OP_n OP_CHECKMULTISIG OP_ELSE <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <R> OP_CHECKSIG OP_ENDIF`.
`DogeLib.Script.Proofs.MultisigRecovery` proves the equivalence of section 7 for this template and its 2-of-3 instance.

`MultisigRecoverySpend` collects the hypotheses, one field each:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, 33-byte keys and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The `InputContext` of `verifyLegacySpend` gives an input index that selects an input and fewer than 2^32 inputs and outputs.
The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, 149 for 2-of-3 (`multisigRecoveryScript_length`).
Each of its pushes has at most 33 payload bytes.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
The `scriptSig` evaluation checks the 520-byte limit on the push of the redeem script, so `n` is at most 13.

`OrdinaryBranch` and `RecoveryBranch` state the two cases without a hypothesis that execution succeeds:

- Ordinary: `S` is `below ++ dummy :: sigs ++ [sel]` with `k` signatures and `castToBool sel`.
  Every pair that Core's matching loop visits, top first (`multisigVisits`), passes `SigEncodingOk` and `KeyEncodingOk`.
  With `NULLDUMMY` the dummy is empty.
  The signatures pair in order with a subsequence of the keys under `sigAccepted` (`OrderedMatch`).
- Recovery: `S` is `below ++ [sigR, sel]` with `castToBool sel = false`.
  The lock time is at least 1,000,000 and below 500,000,000, and the input's sequence is not `0xffffffff`.
  `sigR` and `R` pass the encoding predicates, and `sigAccepted` holds for `sigR` against `R`.

`checkSignatureEncoding_ok_iff` and `checkPubKeyEncoding_ok_iff` prove that the predicates are exactly the checks of `Script.SignatureEncoding`, including the LOW_S overflow case.
By `sigAccepted_iff`, for script code shorter than 2^64 bytes, `sigAccepted` means that the key passes `isValidPubKey`.
It also means that `verify` answers `some true` on the signature without its hash-type byte and the legacy digest.
Both cases allow any stack below, nonminimal pushes and any selector bytes, with negative zero as false.

The theorems:

- `multisigRecovery_sound`: acceptance implies one of the two branches. It assumes no stack bound on `S` and no totality of `verify`.
- `multisigRecovery_ordinary_complete`: the ordinary branch implies acceptance when `S.length + n + 1 ≤ 1000` and the checker decides every visited pair.
- `multisigRecovery_recovery_complete`: the recovery branch implies acceptance when `S.length + 2 ≤ 1000`. `sigAccepted` is already a decided answer.
- `multisigRecovery_accepted_iff` and `multisigRecovery_twoOfThree_accepted_iff`: the equivalence, for a verifier that decides every request. The first needs `S.length + n + 1 ≤ 1000`, and the second, with `n = 3`, needs `S.length ≤ 996`.
- `multisigRecovery_ordinary_unsupported` and `multisigRecovery_recovery_unsupported`: an answer `none` on a reached call gives `unsupported`, never a rejection.
  The ordinary theorem needs `S.length + n + 1 ≤ 1000`, and the recovery theorem needs `S.length + 2 ≤ 1000`.
- `multisigRecovery_lockTime_lt`: with `CHECKLOCKTIMEVERIFY`, the stack bound `S.length + 2 ≤ 1000`, a false selector and a lock time below 1,000,000 give `UNSATISFIED_LOCKTIME` before any signature check.
  `multisigRecovery_accepted_lockTime_lt`: such a spend is accepted only through the ordinary branch.
  Without the flag, `OP_CHECKLOCKTIMEVERIFY` is `OP_NOP2`, and a known answer accepts the recovery branch with lock time 0.
- `multisigRecovery_lockTime_ge_threshold`: with `CHECKLOCKTIMEVERIFY`, the stack bound `S.length + 2 ≤ 1000`, a false selector and a lock time of at least 500,000,000 give `UNSATISFIED_LOCKTIME` before any signature check.
  `multisigRecovery_finalSequence`: the same for a sequence of `0xffffffff` on the input, at every lock time.
  With `multisigRecovery_lockTime_lt`, they cover each case in which the lock-time check of the recovery branch fails.
- `verifyLegacySpend_scriptSig_rejected` and `verifyLegacySpend_scriptSig_unsupported`: a failed `scriptSig` evaluation passes through.

Every checker call of both branches with a nonempty signature and a key that passes `isValidPubKey` hashes the transformation-reference digest, Core's `SignatureHashOld`.
`multisigRecoveryScript_scanOps`: for `1 ≤ k ≤ n ≤ 16`, 33-byte keys and a 33-byte recovery key, every instruction of the template parses.
`ordinaryCode_scanOps` and `recoveryCode_scanOps`: so does the script code of each branch, for every signature list, by `effectiveScriptCode_scanOps`.
These discharge the parsed-script hypothesis of design record 0003, stage 3, for the template.

`transactionChecker_verify_reference` and `sigAccepted_iff_reference` compose a fully parsed script code with `legacySignatureHash_eq_reference` and the count bounds of the `InputContext`.
`MultisigRecoverySpend.sigAccepted_ordinary_iff_reference` and `MultisigRecoverySpend.sigAccepted_recovery_iff_reference` restate `sigAccepted` on each branch's script code.
It holds exactly when the key passes `isValidPubKey` and `verify` answers `some true` on the stripped signature, the key and the digest of `legacyReferencePlan`.
`MultisigRecoverySpend.checkSig_ordinary_reference` and `MultisigRecoverySpend.checkSig_recovery_reference` give the checker's answer as that `verify` call, for a nonempty signature and a key that passes `isValidPubKey`.
These results concern the digest that the checker passes to `verify`. They add nothing about `verify` itself.

The theorems hold relative to the verifier parameter, under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).
They do not establish unforgeability, private-key ownership, distinct signers or bridge custody.

Duplicate keys are allowed, and a match against duplicate keys is not distinct authorization.
The P2SH composition uses the exact supplied redeem script. A different redeem script with the same digest needs a separate hash-commitment argument (A4).
Every hash type that the flags admit is allowed, including NONE, SINGLE and ANYONECANPAY, so a signature need not commit to the whole transaction.

`MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits` and `MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits` restrict to an `IsAllOnly` hash type.
Then an accepted signature also verifies against the reference digest of every transaction `tx'` with the same `legacyAllFields` as `ctx.tx`, at the same input index.
They do not say that `tx'` passes the template: a different scriptSig of the input changes the execution.

They state invariance of an accepted verifier result under equal fields, not that changing a field invalidates the signature.
A verifier that accepts every digest satisfies them.
The commitment of the preimage to the fields is `legacyReferencePlan_allOnly_commits`. A signature-binding claim also needs cryptographic and verifier assumptions.

The lock-time conditions compare the operand with fields of the spending transaction.
A claim that recovery cannot enter a chain before a height or time needs transaction-finality and chain-context results that DogeLib does not have.
The template is a property target. A production bridge instance needs its own fixtures and custody review.

`lake test` runs 25 hand cases through `verifyLegacySpend` with a table verifier, a test backend that ignores the digest.
They cover both branches, signatures in the wrong order, a missing signature, and the lock-time and sequence boundaries.
They also cover a negative-zero selector, the dummy with and without `NULLDUMMY`, and the CLTV flag clear.
Each encoding error has a case: DER, high S, hash type and key type.

`lake test` also compares, for three script codes of the template and six hash types, `legacySignatureHash` with the digest of `legacyReferencePlan`.
Both are DogeLib definitions, so these 18 comparisons are a consistency check, not independent evidence.
The independent evidence for `legacySignatureHash` is Core's `sighash.json`.

Core's compiled code supplies the verdicts of 25 signed spends of one 2-of-3 instance of the template, with fixed keys.
`lake test` and the live Core comparison check DogeLib against them, as [B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries) states.
They cover the three signer pairs, the recovery branch and the recorded mutations.
They are finite evidence for that instance, not a theorem about other keys, lock times, transactions or flags.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `multisigVisits_cons`, `greedyMatch_cons`, `smallIntOpcode_facts` | None |
| `multisigLoop_cons`, `multisigLoop_visits_error`, `pushEncoding_small`, `countOp_small`, `multisigRecoveryScript_eq`, `trueTop_boolBytes` | `propext` |
| `multisigLoop_visits_ok`, `multisigLoop_ok_visits`, `checkSignatureEncoding_ok_iff`, `checkPubKeyEncoding_ok_iff`, `multisigCheck_eq_ok_iff`, `sigAccepted_iff`, `sigAccepted_of_checkSig`, `multisigRecoveryScript_length`, `checkSigStep_recovery`, `effectiveScriptCode_length_le`, `transactionChecker_checkSig_ne_none`, `hash160_toList_length`, `verifyLegacySpend_scriptSig_rejected`, `verifyLegacySpend_scriptSig_unsupported` and the other layout lemmas | `propext`, `Quot.sound` |
| `multisigRecovery_sound`, `multisigRecovery_ordinary_complete`, `multisigRecovery_recovery_complete`, `multisigRecovery_accepted_iff`, `multisigRecovery_twoOfThree_accepted_iff`, `multisigRecovery_ordinary_unsupported`, `multisigRecovery_recovery_unsupported`, `multisigRecovery_lockTime_lt`, `multisigRecovery_lockTime_ge_threshold`, `multisigRecovery_finalSequence`, `multisigRecovery_accepted_lockTime_lt`, `multisigRecoveryScript_twoOfThree` and the evaluation lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| `multisigRecoveryScript_length_le`, `ordinaryCode_length_lt`, `recoveryCode_length_lt` | `propext`, `Quot.sound` |
| `scanOps_cons_opcode`, `keys_scanOps`, `redeemTail_scanOps`, `multisigRecoveryScript_scanOps`, `ordinaryCode_scanOps`, `recoveryCode_scanOps`, `transactionChecker_verify_reference`, `sigAccepted_iff_reference`, `MultisigRecoverySpend.sigAccepted_ordinary_iff_reference`, `MultisigRecoverySpend.sigAccepted_recovery_iff_reference`, `MultisigRecoverySpend.checkSig_ordinary_reference`, `MultisigRecoverySpend.checkSig_recovery_reference` | `propext`, `Classical.choice`, `Quot.sound` |
| `MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits`, `MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits` | `propext`, `Classical.choice`, `Quot.sound` |

## Script worked property: the fixed digest of `SIGHASH_SINGLE`

Core's `SignatureHash` returns the fixed digest `one` when the hash type is SINGLE and `nIn` is at least the number of outputs (D3, lines 1231 to 1236).
`CheckSig` then verifies the signature against `one` (D3, lines 1253 to 1272).
`SignatureHash` reads the number of inputs and the number of outputs to reach that branch, and the check reads no other part of the transaction.
So that check gives the same answer for the same signature bytes and key in every other transaction that reaches the same condition.
A whole spend can still differ, because its scripts, its flags or its other checks differ.
Every spend that Core verifies with `SIGVERSION_BASE` has this behavior.

`DogeLib.Script.Proofs.CheckerExtension` and `DogeLib.Script.Proofs.FixedDigest` state the behavior for a whole spend.
The statements are about `verifyLegacySpend`, and they add no definition to the specification.

`d.Extends c` says that the checker `d` gives the answer of the checker `c` on every request that `c` answers.
For all checkers `c` and `d` such that `d` extends `c`:

- `evalScript_checker_extends` and `verifyScript_checker_extends`: the call with `c` is unsupported, or the call with `d` gives the same result.
- `verifyScript_checker_congr`: two checkers that extend `c` give the same `verifyScript` result, when the call with `c` is decided.

A result is *decided* when it is not unsupported (`EvalResult.Decided`, `VerifyResult.Decided`).
An unavailable checker answer gives an unsupported result at the opcode that asked.
So a decided call with `c` asked only the requests that `c` answers, and the theorems need no list of the requests of a run.

`fixedDigestChecker verify` is a checker without a transaction.
It gives `some false` for a key that fails `isValidPubKey`, and then for an empty signature, as `transactionChecker` does.
Take a signature whose last byte is a SINGLE hash type, and a script code shorter than 2^64 bytes.
The checker gives `verify` on the signature without that byte, the key and `legacyOne`.
Every other signature check is unavailable, and so is every lock-time and sequence check.
It is a device of the theorems, not a model of a Core class.

- `transactionChecker_extends_fixedDigestChecker`: for a transaction with at most `nIn` outputs, `transactionChecker tx nIn verify` extends `fixedDigestChecker verify`.
- `verifyLegacySpend_eq_fixedDigest`: for an `InputContext` with at most `index` outputs, assume that `verifyScript` with `fixedDigestChecker` is decided on the input's `scriptSig` and the previous `scriptPubKey`.
  Then `verifyLegacySpend` gives the same result.
  That result reads the transaction only through the bytes of `scriptSig`.
- `verifyLegacySpend_fixedDigest_congr`: two such inputs with the same `scriptSig` and the same previous `scriptPubKey` give the same result.
  The two transactions can differ in the version, the outpoints, the sequences, the other inputs, the outputs and the lock time.
  The two indices can differ.

A flag set with an unsupported bit gives the same unsupported result on both sides of each equation.
So the hypothesis applies only to supported flag sets.

`fixedDigestChecker` answers a signature check with an invalid key or an empty signature.
It answers a check with a SINGLE hash type when `verify` decides the request on `legacyOne` (`fixedDigestChecker_checkSig_ne_none`).
`coreVerifier` decides every request.
So such a check does not make the call undecided.
That covers `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIGVERIFY`, `OP_CODESEPARATOR` and a signature push that `FindAndDelete` removes.
The call is not decided when a reached check has a valid key and a nonempty signature with another hash type.
It is also not decided when CLTV or CSV reaches the checker.
The theorems say nothing about such a spend.
So they locate the transaction dependence of a spend in those requests.

Three theorems discharge the hypothesis for a template, for every flag set:

- `verifyLegacySpend_p2pkh_fixedDigest`: `scriptSig` is `pushScript [sig, key]`, and the previous `scriptPubKey` is `p2pkhScriptPubKey h` for 20 bytes `h`.
- `verifyLegacySpend_multisig_fixedDigest`: `scriptSig` is `pushScript (dummy :: sigs)`, and the previous `scriptPubKey` is `multisigScript m keys`.
- `verifyLegacySpend_p2shMultisig_fixedDigest`: `scriptSig` also pushes `multisigScript m keys`, and the previous `scriptPubKey` is its P2SH commitment.

Each assumes at most `index` outputs, `HasSingleHashType` for every signature, and a verifier that decides every request on `legacyOne`.
The multisig theorems assume `1 ≤ m ≤ n ≤ 16` for `n` keys and exactly `m` signatures.
`HasSingleHashType sig` holds when `sig` is empty or the low five bits of its last byte are 3.
That includes `0x03`, `0x83` and undefined bytes such as `0x23`, which the encoding check rejects only under `STRICTENC`.

`pushScript` pushes each item with `CScript() << item`, so the theorems do not cover another encoding of the same pushes.
`coreVerifier` decides every request (`coreVerifier_some`).
The theorems do not assume that the HASH160 digest of the key is `h`, that a signature verifies, or that the spend is accepted.

The theorems compare results of the Lean definitions for two transactions.
They hold relative to the verifier parameter, under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).
They do not say that a signature for `legacyOne` exists for a key, or that one is hard to compute.
They do not say that the second transaction is valid in a chain: a spend also needs an unspent output with that `scriptPubKey`.
`InputContext` excludes an index at or after the number of inputs, where Core's `SignatureHash` also returns `one`.
Core's `CheckInputs` calls the checker only for an index below the number of inputs ([`src/validation.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp), lines 1482 to 1488).

Core's block and mempool validation verifies through a signature cache (SOURCES.md, D111).
The cache stores only successful checks.
Its entry is a hash of a nonce of the process and the three arguments of `VerifySignature`.
The arguments are the signature hash, the public key and the signature without its hash-type byte.
So a cache hit gives the result that `CPubKey::Verify` gives on the same arguments, unless two entries collide under SHA-256.
On the fixed digest, the signature hash does not depend on the transaction.
The key and the signature come from the scripts.
So for the same key and signature bytes, a cache hit does not depend on the rest of the transaction.
DogeLib does not model the cache, and this argument is a reading of D111, not a theorem.

Core's compiled code supplies the verdicts of the 44 records of [`fixed-digest.jsonl`](../../tests/script/signed-spends/README.md#fixed-digest-spends), with fixed test keys.
`lake test` and the live Core comparison check DogeLib against them, as [B4](../../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries) states.
The records reuse one signature of each key in other transactions, at another index, with no outputs, and with another script code.
They include the boundary of one more output, where Core rejects the same signature.
They are finite evidence for these scripts and keys, not a theorem about Core.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `SignatureChecker.Extends.refl` | None |
| `EvalResult.Decided.ne_unsupported`, `VerifyResult.Decided.ne_unsupported`, `forall_byte_of_forall_lt`, `multisigLoop_error_mem`, `pushOpcode_facts` | `propext` |
| `pushHeader_opcode_le` | `Quot.sound` |
| `checkSigStep_checker_extends`, `multisigCheck_checker_extends`, `multisigLoop_extends`, `checkMultisigStep_checker_extends`, `checkLockTimeStep_checker_extends`, `checkSequenceStep_checker_extends`, `execOpcode_checker_extends`, `evalInstruction_checker_extends`, `evalScript_checker_extends`, `verifyScript_checker_extends`, `verifyScript_checker_congr`, `verifyScript_decided`, `transactionChecker_extends_fixedDigestChecker`, `fixedDigestChecker_checkSig_ne_none`, `verifyLegacySpend_eq_fixedDigest`, `verifyLegacySpend_fixedDigest_congr`, `multisigCheck_ne_unsupported`, `checkSigStep_ne_unsupported`, `isPayToScriptHash_multisigScript` | `propext`, `Quot.sound` |
| `evalLoop_pushScript`, `evalScript_pushScript`, `evalScript_p2pkh_decided`, `evalScript_multisigScript_decided`, `verifyLegacySpend_p2pkh_fixedDigest`, `verifyLegacySpend_multisig_fixedDigest`, `verifyLegacySpend_p2shMultisig_fixedDigest`, `coreVerifier_legacyOne_ne_none` | `propext`, `Classical.choice`, `Quot.sound` |
