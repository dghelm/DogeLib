# Model read: Script evaluation and verification

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Script/{Eval,State,Number,Instruction,Flags,Error,Verify,Signature,SignatureCode,SignatureEncoding}.lean`, outside `Proofs/`, against the Core functions that the [brief](briefs/script.md) names.

## Result

The read found no consensus-divergent discrepancy in legacy spend verification with the seven supported flags.
It found three domain-boundary differences in standalone operations, and the Lean files already documented two of them.
Confidence is high from source inspection, on the condition that the signature verifier parameter agrees with Core.
The read ran no executable comparison.

## Findings

**F1. Boolean conversion beyond `UINT_MAX` bytes**

Lean `Number.lean:147` and `Eval.lean:459` against Core `src/script/interpreter.cpp:40–49`.
Core's unsigned counter wraps on an item of 2^32 zero bytes, and the loop never ends.
Lean's mathematical definition returns false.

Concrete input: flags `0`, script `63 68`, and an initial stack of one item of 2^32 zero bytes.
Lean specifies success with an empty stack, and Core loops.
`Number.lean:153–156` and `Eval.lean:172–178` document this extension.

Severity: **domain-boundary**.
Confidence: **high**, from the source, not executed.

**F2. Stack length casts beyond `INT_MAX` items**

Lean `Eval.lean:340–347,554–560` against Core `src/script/interpreter.cpp:926–930,655–659`.
Core casts the stack length to `int`, and Lean uses `Nat` lengths.

Concrete input on a build with a 32-bit `int`: flags `0`, script `ae`, `baseChecker`, and 2^31 initial items with top item `15` (hex).
Core's cast gives a negative length and `INVALID_STACK_OPERATION`.
Lean decodes 21 and gives `PUBKEY_COUNT`.
`Eval.lean:165–178` already excludes this domain from the correspondence.

Severity: **domain-boundary**.
Confidence: **high for that build**, from the source, not executed.

**F3. `GetOp` truncates the remaining byte count modulo 2^32**

Lean `Instruction.lean:106–108` and `DogeLib/Transaction/LegacySighash.lean:109–110` against Core `src/script/script.h:543–547`.
Core converts the remaining byte count to `unsigned int` before the payload check.
Lean compares unbounded lengths.

Concrete standalone input: `01` and then exactly 2^32 zero bytes, at cursor `0`.
Core's `GetOp` returns false, because the converted remainder is zero.
Lean reads a one-byte push and returns cursor `2`.
Consequently, `isPushOnly` returns false in Core and true in Lean for this script, in which every instruction is a push.
`EvalScript` rejects this script with `SCRIPT_SIZE` before it parses, on both sides.

Severity: **domain-boundary**.
Confidence: **high for a 32-bit `unsigned int`**, from the source, not executed.

`verifyLegacySpend` reaches none of these inputs, because of its script and stack limits.

## Checked and agreeing

Lean paths below are relative to `DogeLib/Script/` unless qualified.
Core paths are relative to `src/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `script/interpreter.h:30–108`, flags | `Flags.lean:24–68` | Seven supported bits. `Eval.lean:715` and `Verify.lean:121` check unsupported bits first. |
| `script/script_error.h:9–68`, errors | `Error.lean:25,111,123` | Enum order and numeric codes. |
| `test/script_tests.cpp:60–100`, error names | `Error.lean:126` | Includes `NULLFAIL` spelling. |
| `script/script.h:217–242`, numeric constructor | `Number.lean:80,93,107` | Size before minimality, sign-magnitude, negative zero. |
| `script/script.h:244–351`, arithmetic and serialization | `Number.lean:125,135`, `Eval.lean:260,273` | Reachable arithmetic fits `int64_t`. Results can require five bytes. |
| `script/interpreter.cpp:38–51`, `CastToBool` | `Number.lean:147` | Agrees through `UINT_MAX` bytes. See F1. |
| `script/script.h:492–552`, `GetOp` | `Instruction.lean:106`, `DogeLib/Transaction/LegacySighash.lean:119` | Push widths, truncation cursors, nonminimal pushes. See F3. |
| `script/interpreter.cpp:258–269,275`, state | `State.lean:67,83,86,90` | Locals reset. Only main stack passes between calls. |
| `script/interpreter.cpp:266–311,1033–1045`, loop | `Eval.lean:655,693,713` | Script, push, op-count, disabled, execution, combined stack, final conditionals. |
| `script/interpreter.cpp:317–348`, small integers and NOP | `Eval.lean:428–436` | Exact pushed numbers. |
| `script/interpreter.cpp:350–435`, CLTV, CSV, upgrade NOPs | `Eval.lean:387,405,438–452` | Five-byte decode, negative error, CSV disable bit, operand retained. |
| `script/interpreter.cpp:437–496`, control flow | `Eval.lean:454–478` | Empty IF error, skipped nested IF, ELSE toggle, VERIFY and RETURN errors. |
| `script/interpreter.cpp:502–589`, altstack and multi-item operations | `Eval.lean:480–518` | Underflow errors and item order. |
| `script/interpreter.cpp:591–695`, remaining stack operations | `Eval.lean:521–575` | PICK/ROLL remove index before selection. See F2. |
| `script/interpreter.cpp:698–738`, SIZE and equality | `Eval.lean:578–589` | Raw lengths, byte equality, VERIFY errors. |
| `script/interpreter.cpp:744–841`, numeric opcodes | `Eval.lean:591–626` | Operand order, decode errors, five-byte results, half-open WITHIN. |
| `script/interpreter.cpp:847–871`, hash opcodes | `Eval.lean:282,628–632` | Underflow, selected primitive and stack replacement. |
| `script/interpreter.cpp:873–878`, CODESEPARATOR | `Eval.lean:634` | Cursor after last executed separator. |
| `script/interpreter.cpp:880–918`, CHECKSIG variants | `Eval.lean:296` | Signature before key encoding, script code, checker call, result and VERIFY error. |
| `script/interpreter.cpp:920–1026`, CHECKMULTISIG variants | `Eval.lean:338`, `Signature.lean:151` | Counts, key-count charge, top-first matching, early exit, dummy requirement, NULLDUMMY. |
| `script/interpreter.cpp:289–304,1028–1029`, disabled and reserved opcodes | `Eval.lean:237,645,661–667` | Disabled even when skipped. VERIF/VERNOTIF fail in skipped branches. |
| `script/interpreter.cpp:66–86,110–173`, strict encodings | `SignatureEncoding.lean:76,245` | DER bounds, tags, padding and public-key shapes. |
| `script/interpreter.cpp:175–223`, signature and key checks | `SignatureEncoding.lean:203,213,228,260` | Empty signature exception, LOW_S before hash type, BASE key check. |
| `pubkey.cpp:27–166,289–295`, LOW_S parsing | `SignatureEncoding.lean:105–194` | Lax lengths, scalar overflow zeroes both values, half-order threshold. |
| `script/script.h:418,437–464,570–596`, signature pushes and `FindAndDelete` | `SignatureCode.lean:25–53`, `DogeLib/Transaction/LegacySighashReference.lean:54,89,123` | Boundary-only deletion, repeated matches, malformed suffix retained. |
| `script/interpreter.h:128–147`, base checker | `Signature.lean:61` | Signature, lock-time and sequence checks return false. |
| `script/interpreter.cpp:1253–1272`, transaction signature call | `Signature.lean:131` | Key shape, empty signature, hash byte removal, BASE digest call, verifier arguments. |
| `script/interpreter.cpp:1274–1353`, transaction lock checks | `Signature.lean:85,98,140` | Threshold, final sequence, unsigned version, disable bit and sequence mask. |
| `script/script.cpp:204–211,239–259`, P2SH and push-only tests | `Verify.lean:74,85,91` | Exact 23-byte template. RESERVED counts as push-only. See F3. |
| `script/interpreter.cpp:1409–1526`, `VerifyScript` | `Verify.lean:111,120,164` | Evaluation order, true top, P2SH restore, redeem evaluation and first errors. |

## Not checked

The read omitted no in-scope function or opcode group from the source comparison within the stated BASE and flag domain.
The brief excluded elliptic-curve arithmetic and the internals of the signature-hash digest.
Hash primitive internals and proofs were outside the listed files.

The reader did not execute the three large-input examples.
It ran no differential comparison and no other repository gate.
The oracle binary was absent at `.lake/build/bin/dogelib-oracle`, and the workspace was read-only.

## After the read

A check of F3 against Core at the pin, by the model that prepared this record, found that F3 names the wrong mechanism.
`CScript` is a `prevector` with a `uint32_t` size and an `int32_t` iterator difference (`src/prevector.h`, line 34).
So the input of F3, a script of 2^32 + 1 bytes, has no `CScript`, and the boundary is lower than F3 states.
The correspondence with `GetOp2` covers a script of fewer than 2^31 bytes.
The doc comments of `Transaction.readOp`, `readInstruction` and `isPushOnly` state that bound, as do [SOUNDNESS.md](../../SOUNDNESS.md#script-instruction-reader-and-execution-state) and the *Script instruction reader* row of [COVERAGE.md](../../COVERAGE.md).
This check also read the source only and executed nothing.
