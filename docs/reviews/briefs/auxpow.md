# Brief of the AuxPoW read

This text is the prompt that produced [the record](../auxpow.md).
It is exact, except that two placeholders replace the local clone paths.

````markdown
# Model read: AuxPoW and header proof of work against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides.

- DogeLib (read-only): <DogeLib clone> at commit 865754b
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

**Lean**, definitions outside `Proofs/` and `Exports/`: DogeLib/Block/AuxPow.lean, AuxPowCheck.lean, Merkle.lean, Header.lean, ProofOfWork.lean, VersionGate.lean, and DogeLib/Work/ProofOfWork.lean

**Core**: src/auxpow.cpp and auxpow.h (CAuxPow::check, getExpectedIndex, CheckMerkleBranch, serialization); src/primitives/pureheader.*, src/primitives/block.*; src/dogecoin.cpp (CheckAuxPowProofOfWork); src/pow.cpp (CheckProofOfWork); src/consensus/merkle.cpp; the relevant chainparams.cpp values

Each Lean module's doc comments state its declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core.

## Method

For each Core function, find the Lean counterpart and compare:
- the order of checks;
- every error or reject reason and which check produces it;
- bounds and off-by-one cases;
- integer widths, signedness, overflow and truncation;
- byte order and serialization;
- empty and edge inputs;
- height and parameter boundaries;
- which network parameters are used.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it. The project's differential comparison (`scripts/compare_core.py`, plus fixtures under tests/) can test it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: AuxPoW and header proof of work

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
