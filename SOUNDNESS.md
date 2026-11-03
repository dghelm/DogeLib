# Soundness

This document says what the proofs of DogeLib establish, and what a user of DogeLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem. Both are assumed to match something outside Lean: the Dogecoin behavior, the code that runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of EthLib's [`SOUNDNESS.md`](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/SOUNDNESS.md), which follows s2n-bignum's.

DogeLib has one definition with a theorem: SHA-256, adapted from EthLib.
No Dogecoin-specific definition exists yet.
Each section states the mitigations that exist today, and the policy for definitions that are not written yet.
A lane that adds a definition, a theorem, an execution path or a dependency updates the affected rows in the same change.

## Ways to use DogeLib

Each way of using DogeLib trusts a different set of things, so the summary table marks which risks apply to which use.
There are four uses:

- **P**: a Lean proof that imports the specification.
- **R**: a Lean program that runs the specification, such as the oracle.
- **I**: an implementation that is proved to refine the specification, such as extracted Rust.
- **F**: a client that compares against the fixtures in `tests/`.

## Summary

The risks fall into four gaps, one per link in the chain from Dogecoin behavior to client.
Gap A asks whether the definition says what Dogecoin does and what the client needs.
Gap B asks whether the code that runs matches the definitions.
Gap C asks whether the proof itself is sound.
Gap D asks whether the use of DogeLib holds together.

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match the pinned Dogecoin behavior | Source mapping in `SOURCES.md`, by review only. SHA-256 has a proof against a FIPS 180-4 model. No fixtures or comparisons yet. | P R I F |
| A2 | A theorem holds only under a hypothesis | Policy: each conditional theorem lists its hypotheses here and in `COVERAGE.md` | P I |
| A3 | Timing reveals secret data | None: no constant-time claim | R I |
| A4 | A security theorem idealises a primitive | None: no security theorem yet | P |
| A5 | A rule depends on a protocol context that the definition does not model | Policy: each operation records its mode, network and era in `SOURCES.md` | P R I F |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | None yet | R |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R |
| B3 | Elaboration runs native code | None yet | P |
| B4 | The oracle's IO adapter or a foreign boundary is wrong | None yet | R F |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R |
| B6 | Extraction or the Rust toolchain is wrong | None: no extraction yet | I |
| C1 | The Lean kernel or its axioms are unsound | None | P I |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any use | P I |
| C3 | A declaration reached the environment unchecked | None | P I |
| D1 | A client misuses an operation, such as a prefix decoder where complete consumption is required | Policy: each public operation documents its input domain and consumption contract | R I |
| D2 | A dependency changes | Pins in `SOURCES.md` and `lean-toolchain`. The package has no Lake dependencies. | P R I |
| D3 | The fixtures are wrong | Policy: provenance recorded for each fixture. No fixtures yet. | F |

## What the proofs say

Each operation with a theorem has a subsection here.
It says what is proved, under which hypotheses and over which input domain, and what is not proved.
[COVERAGE.md](COVERAGE.md) gives the per-operation status. This section explains its meaning and limits.

### SHA-256

`hash_eq_spec` says that `hash` equals `Spec.hash` on every message shorter than 2^61 bytes.
`Spec.hash` restates FIPS 180-4 over 32-bit bit vectors, independently of the executable code.
The theorem depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.

The theorem does not show that `Spec.hash` matches FIPS 180-4.
A reader checks that by comparing the model with the standard (A1).
No known-answer test exercises the compiled code in DogeLib yet (B1).
EthLib tests the same code against the NIST CAVP vectors, through its own bindings.
Both files are adapted from EthLib at commit `6a93711`.

### What cannot be proved yet

A `partial` definition, an `opaque` constant, or a definition that unfolds to one cannot be evaluated by the kernel.
CONTRIBUTING.md says to avoid `partial` definitions in the specification library (*Specification code*), and requires explicit treatment of `opaque` (*Proofs*).
Each such definition that remains is listed here with its reason.

## Gap A: does the definition say what Dogecoin does and what the client needs?

### A1. A wrong definition

A definition can differ from Dogecoin's behavior while every theorem about it holds, because the theorems are proved about the definition, not about Dogecoin Core.
Three things guard against that, once they exist.
Each definition is named and shaped after its source in `SOURCES.md`, so that a reader can compare them line by line.
Fixtures come from pinned Core tests, primary specifications or documented historical data, never from the implementation under test.
Core comparisons run the compiled oracle against the pinned Core revision.
None of the three exists yet beyond the source registry.

A Dogecoin rule can differ from the Bitcoin rule it descends from.
A definition or proof adopted from btc-verified is evidence to investigate, not a compatibility proof for Dogecoin.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
The first planned one is the signature-preimage equivalence, which may require fully parsed script code (ROADMAP.md, milestone C).
Whatever those hypotheses leave unproved is part of what a reader trusts.

### A3. Side channels

DogeLib makes no constant-time claim.
The specification is a reference for behavior, not for timing.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
DogeLib has no security theorem, so it has no idealisation.
Equality of two hash plans needs no assumption about the hash function.
A claim that different preimages give different digests needs a named collision hypothesis or a computational model.

### A5. Protocol context

Some rules apply only under a serialization mode, a network, an activation state or a historical era.
A definition that leaves out its context can be right in one era and wrong in another.
The first operations, base codecs and legacy signature hashing, have few context dependencies.
Script, ledger and activation work will need explicit context.

## Gap B: does the code that runs match the definitions?

DogeLib's theorems are about the Lean definitions, and everything between them and the running code is trusted.
A proof about extracted Rust narrows that gap for the extracted code only.

```text
 Dogecoin behavior --A-- Lean definition == proof == theorem
                              |
                              B
                              |
            compiled oracle, extracted Rust --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.
Core comparisons through the compiled oracle test it end to end, only on the inputs they cover.

### B2. Lean core's own implementations

Lean core implements some `Array`, `ByteArray` and `Nat` operations with `@[implemented_by]` or `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Lean core is a declared trusted baseline.

### B3. Native code during elaboration

If a library sets `precompileModules := true`, then `#eval` or an evaluating tactic in a module that imports it runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The oracle and foreign boundaries

The oracle reads fixture records and writes results through IO.
That adapter is outside the specification library, and no theorem covers it.
Any later foreign boundary, such as a C or Rust binding, is listed here with its size and its error handling.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust. The code that runs is still not the definition a reader reads.

The `DogeLib` and `Proofs` libraries have none of the three, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` contain them on purpose, to test the check, and no library imports them.

| Declaration | Kind | Proof-backed | Justification |
| --- | --- | --- | --- |

### B6. Extraction and the Rust toolchain

A refinement theorem about extracted Rust is about the Lean model that Charon and Aeneas produce.
It trusts the extraction, any manually modeled dependency, and the Rust compiler and runtime.
The extracted model is an implementation artifact. It never becomes the specification.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set. A theorem may use fewer.

`lake exe check-decls` checks dependencies: no declaration may depend on an axiom outside that set.
It does not check the kernel, and it does not show that the axioms are consistent.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

CONTRIBUTING.md does not allow these tactics (*Proofs*).
btc-verified allows the axioms that `bv_decide` records, and its `CompactSize.decode_encode` and `encode_head` use `bv_decide`.
A proof adopted from btc-verified has those steps replaced by proofs the kernel checks alone (design record 0002, section 5).

No theorem in the `DogeLib` and `Proofs` libraries uses them, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` use them on purpose.

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
An independent checker that replays the environment, such as `lean4checker`, would catch it, but none runs yet.

## Gap D: does the use of DogeLib hold together?

### D1. Misuse by a client

A correct definition gives a wrong answer when a client calls it outside its input domain.
A prefix decoder returns a remainder, and a client that ignores it accepts trailing bytes.
Each public operation documents its input domain, its failure behavior and whether it consumes the whole input.

### D2. Dependency changes

A change to a pinned dependency can change a definition or a proof that DogeLib relies on.
`SOURCES.md` records the pins, and a pin changes only in a reviewed change of its own.

### D3. Wrong fixtures

A fixture with a wrong expected value makes a wrong implementation pass.
Each fixture records its provenance, and a test runner compares results with the committed expectations rather than overwriting them.
