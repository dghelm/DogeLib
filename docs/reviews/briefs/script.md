# Brief of the Script read

This text is the prompt that produced [the record](../script.md).
It is exact, except that two placeholders replace the local clone paths.

````markdown
# Model read: Script evaluation and verification against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides.

- DogeLib (read-only): <DogeLib clone> at commit 865754b
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

These definitions, outside `Proofs/`:
- DogeLib/Script/Eval.lean, State.lean, Number.lean, Instruction.lean, Flags.lean, Error.lean
- DogeLib/Script/Verify.lean, Signature.lean, SignatureCode.lean, SignatureEncoding.lean

The Core side:
- src/script/interpreter.cpp: EvalScript, VerifyScript, CheckSignatureEncoding, CheckPubKeyEncoding, IsLowDERSignature, IsDefinedHashtypeSignature, FindAndDelete, TransactionSignatureChecker
- src/script/script.h and src/script/script.cpp: CScriptNum, GetOp, IsPushOnly, IsPayToScriptHash
- src/script/script_error.h

The declared domain is SIGVERSION_BASE plus the seven supported flags of design record 0003. Flags outside it make Lean return `unsupported`, and that is in scope only to confirm it happens *before* any behaviour diverges. Out of scope: the elliptic-curve arithmetic, and the sighash digest beyond how Script calls it.

## Method

For each Core function or switch case, find the Lean counterpart and compare:
- the order of checks;
- every error code and which check produces it;
- bounds and off-by-one cases;
- integer widths, signedness and overflow;
- empty and edge inputs;
- the order in which the stack is popped;
- what happens on a non-executed branch (`fExec` false);
- op counting;
- the push-size and element-size limits;
- the disabled opcodes;
- the conditional stack;
- the effect of OP_CODESEPARATOR on scriptCode;
- the NULLDUMMY and multisig dummy element;
- the CLTV and CSV operand decoding.

Where they differ, try to give a concrete script and stack that would produce different results. For any you are unsure of, say so, and give the input that would settle it. The project's differential comparison (`scripts/compare_core.py`, plus fixtures under tests/) can test it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: Script evaluation and verification

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: <files>

## Result
<two or three sentences: discrepancies found, yes or no; overall confidence>

## Findings
<one entry per discrepancy or suspected discrepancy: Lean file:line, Core file:line, what differs, a concrete input if known, severity (consensus-divergent / domain-boundary / documentation-only), confidence>

## Checked and agreeing
| Core construct (file:lines) | Lean definition (file:line) | Notes |
<one row per function or opcode group you actually compared>

## Not checked
<anything in scope you did not compare, and why>
```

Be terse. Don't pad the agreeing table with prose.
````
