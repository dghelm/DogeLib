# Soundness

This document says what the proofs of DogeLib establish, and what a user of DogeLib trusts on top of them.

This document describes DogeLib at revision `b43aff2` (2026-11-23) with Lean `v4.35.0`.
No human line-by-line audit of the specification against Dogecoin Core exists.
[docs/reviews/README.md](docs/reviews/README.md) records AI model reads against Core source, not human audits.

No formal verification is absolute.
A proof links a Lean definition to a theorem. Both are assumed to match something outside Lean: the Dogecoin behavior, the code that runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of EthLib's [`SOUNDNESS.md`](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/SOUNDNESS.md), which follows s2n-bignum's.
The current EthLib pin `bb6dfe5` expands that document with coverage that DogeLib does not adopt.

[COVERAGE.md](COVERAGE.md) lists the definitions and their theorems.
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
| A1 | A definition does not match the pinned Dogecoin behavior | Source mappings, independent known answers and comparisons with pinned Core guard against a wrong definition. Lean model equivalence still requires source review. See [A1](#a1-a-wrong-definition) and [operation evidence](COVERAGE.md#operations). | P R I F |
| A2 | A theorem holds only under a hypothesis | Policy: each conditional theorem lists its hypotheses here and in `COVERAGE.md` | P I |
| A3 | Timing reveals secret data | None: no constant-time claim | R I |
| A4 | A security theorem idealises a primitive | None: no security theorem yet | P |
| A5 | A rule depends on a protocol context that the definition does not model | Policy: each operation records its mode, network and era in `SOURCES.md` | P R I F |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | Known answers and Core comparisons exercise the compiled specification on finite inputs. They do not prove compiler or runtime correctness. See [B1](#b1-the-compilers-and-the-runtime) and [operation evidence](COVERAGE.md#operations). | R |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R |
| B3 | Elaboration runs native code | None yet | P |
| B4 | The oracle's IO adapter or a foreign boundary is wrong | Oracle fixtures and Core comparisons check adapter results on the recorded inputs, and the declaration check includes `Exports`. See [B4](#b4-the-oracle-and-foreign-boundaries) for the trusted conversions and harness boundaries. | R F |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R |
| B6 | Extraction or the Rust toolchain is wrong | `decode_refines` relates the extracted Rust reader model to `decodeBounded`. Charon, Aeneas, library models, the Rust compiler and runtime remain trusted. See [B6](#b6-extraction-and-the-rust-toolchain). | I |
| C1 | The Lean kernel or its axioms are unsound | `lake exe check-decls` rejects transitive axiom dependencies outside the allowed set, including imported unfinished proofs. Kernel soundness and axiom consistency remain trusted. | P I |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any use | P I |
| C3 | A declaration reached the environment unchecked | `scripts/replay.sh` replays each module of `DogeLib`, and of the test-only `ProposalExamples`, into the kernel on each push to `main` and every week, and requires each stored constant to equal the replayed one. `Refinement/` is not replayed. `scripts/check_lean_commands.py` rejects source commands that run code during elaboration, except an allowlist. The declaration check requires every production module to be reachable from its default roots. See [C3](#c3-declarations-the-kernel-did-not-check). | P I |
| D1 | A client misuses an operation, such as a prefix decoder where complete consumption is required | Policy: each public operation documents its input domain and consumption contract | R I |
| D2 | A dependency changes | Source and toolchain pins constrain dependency changes. The root package has no Lake dependencies, while the separate refinement package owns Aeneas and Mathlib. See [D2](#d2-dependency-changes). | P R I |
| D3 | The fixtures are wrong | Each fixture records its provenance. The NIST CAVP files, Wycheproof P1363 records and Core's `sighash.json` are pinned by digest, and CI checks the pins. Core's test cases are copied into `tests/KnownAnswers/` topic modules with their file and line. | F |

## What the proofs say

Per-area files under `docs/soundness/` state what each proof establishes, under which hypotheses and input domain, and what remains unproved.
[COVERAGE.md](COVERAGE.md) gives the per-operation status, and these files explain its meaning and limits.

| Area | File | Scope |
| --- | --- | --- |
| Serialization and Rust refinement | [docs/soundness/serialization.md](docs/soundness/serialization.md) | Codecs, packed codecs, CompactSize, Rust bounded reader refinement, and counted lists |
| Cryptography | [docs/soundness/cryptography.md](docs/soundness/cryptography.md) | SHA-1, SHA-256, HMAC-SHA-256, PBKDF2, RFC 7914 scrypt, Dogecoin scrypt, double SHA-256, RIPEMD-160, Hash160, and secp256k1 |
| Transactions and legacy sighash | [docs/soundness/transactions.md](docs/soundness/transactions.md) | Packed slice reader, base and witness transaction formats, legacy signature hashing, transformation reference, and `SIGHASH_ALL` commitments |
| Proof of work and retarget | [docs/soundness/work.md](docs/soundness/work.md) | Compact targets, difficulty retargets, supplied-hash PoW, 256-bit word models, next-work selection, median time past, and chain work |
| Block headers and AuxPoW | [docs/soundness/headers.md](docs/soundness/headers.md) | Pure and full headers, Merkle roots, AuxPoW check, header PoW, version gating, contextual headers, and header sequences |
| Block validation and coin sets | [docs/soundness/blocks.md](docs/soundness/blocks.md) | Block subsidy, `CheckTransaction`, `CheckBlock`, version bits, contextual body, `ConnectBlock`, issuance bounds, and coin-set restriction |
| Script execution | [docs/soundness/script.md](docs/soundness/script.md) | Instruction reading, execution state, signature code, script numbers, `EvalScript`, encodings, opcodes, `VerifyScript`, and worked properties |
| Proposed revisions | [docs/soundness/proposals.md](docs/soundness/proposals.md) | Script and block frameworks, `RelativeLockTime`, and the test-only examples `ExampleVersionVerify` and `ExampleFaultyLocktime` |
| Oracle and Core harness (B4) | [docs/soundness/oracle-and-harness.md](docs/soundness/oracle-and-harness.md) | Per-operation trust boundaries for `dogelib-oracle`, `dogelib-proposal-oracle`, `core-oracle`, `core-signer`, and snapshots |

### What cannot be proved yet

A `partial` definition, an `opaque` constant, or a definition that unfolds to one cannot be evaluated by the kernel.
CONTRIBUTING.md says to avoid `partial` definitions in the specification library (*Specification code*), and requires explicit treatment of `opaque` (*Proofs*).

On `main` at revision `b43aff2` (2026-11-23), `lake exe check-decls` reports:

```text
check-decls: 13316 declarations under DogeLib and Refinement, 0 findings, 0 in the baseline, 0 new, 0 stale
```

Under [`scripts/CheckDecls.lean`](scripts/CheckDecls.lean), that output covers the seven default roots (`DogeLib`, `DogeLib.Proofs`, `DogeLib.Exports`, `DogeLib.Proposals`, `DogeLib.Proposals.Proofs`, `DogeLib.Proposals.Exports`, and `Refinement`).
It shows zero `partial`, `opaque`, `unsafe`, `extern`, `implemented_by`, `csimp`, or `reaches-opaque` findings across the 13,316 checked declarations under `DogeLib` and `Refinement`.
The `reaches-opaque` check skips declarations in `Proofs` and `Exports` modules, `Repr` and `ToString` formatting helpers, and `initialize` helpers.
It also exempts `System.Platform.getNumBits` reached from `Refinement`, and drops message arguments of `panicCore`, `panic`, `panicWithPos`, and `panicWithPosWithDecl`.
For example, the `Exports` input loop uses Lean core's `partial` `repeat` (B4), and `Refinement` uses `System.Platform.getNumBits` for Rust `usize` (B6, C1).

## Gap A: does the definition say what Dogecoin does and what the client needs?

### A1. A wrong definition

A definition can differ from Dogecoin's behavior while every theorem about it holds, because the theorems are proved about the definition, not about Dogecoin Core.
Three things guard against that.
Each definition is named and shaped after its source in `SOURCES.md`, so that a reader can compare them line by line.
Fixtures come from pinned Core tests, primary specifications or documented historical data, never from the implementation under test.
Core comparisons run the compiled oracle against the pinned Core revision.

The source registry exists. The fixtures are listed per operation in the *Comparison* column of [COVERAGE.md](COVERAGE.md), and each records its provenance.
The Core comparison runs the compiled oracle and Core's own code at the pin on the same requests, for the operations of the oracle ([docs/core-harness.md](docs/core-harness.md#the-core-harness)).
For `block.check_version`, the harness runs a hand transcription that calls Core's helpers, not Core's function ([B4](#b4-the-oracle-and-foreign-boundaries)).
For `block.contextual_check` and `block.header_sequence`, it runs Core's functions on a block index that it builds in memory.

The comparison shows agreement on the requests it sends, and nothing about other inputs.
No person has recorded a line-by-line comparison of a definition with its source.

The real mainnet headers test next-work selection across DigiShield activation against historical `nBits` values.
[Next-work selection and work parameters](docs/soundness/work.md#next-work-selection-and-work-parameters) states the exact branch counts.
Hash links connect headers through 145000 to the pinned Core checkpoint, subject to the hash commitment assumption.
The checkpoint does not authenticate later headers, whose provenance still relies on the public source.
The fixture digest pins all bytes, and the compiled test checks links through 145030.
Neither check establishes proof of work, AuxPoW validity or full header validity.

The multiplication, shift, bit-length and low-64-bit models have arithmetic equivalence proofs, as [256-bit word arithmetic](docs/soundness/work.md#256-bit-word-arithmetic) states.
A reader still checks their correspondence to Core's source.
The division, comparison and subtraction models also have arithmetic equivalence proofs, as [256-bit word division](docs/soundness/work.md#256-bit-word-division) states.
The word division model represents Core's zero-divisor exception.
The arithmetic definition takes a nonzero proof.

The compact, uint64 construction and byte conversion models have arithmetic equivalence proofs, as [Remaining word paths of the retarget](docs/soundness/work.md#remaining-word-paths-of-the-retarget) states.
The composed word retarget uses these models and the proved `CompareTo` model.
Its equality with the arithmetic specification holds for every existing input.
Network powLimit proofs start from Core's hexadecimal literals, through the restricted hex parser and word conversion.
A reader still checks the models against Core's source.

A Dogecoin rule can differ from the Bitcoin rule it descends from.
A definition or proof adopted from btc-verified is evidence to investigate, not a compatibility proof for Dogecoin.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
`legacySignatureHashPlan_eq_reference` equates the field-by-field production plan with the transaction-transformation reference for every input index and hash type.
It requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
[Legacy signature hash: transformation reference](docs/soundness/transactions.md#legacy-signature-hash-transformation-reference) states these hypotheses and explains the short-push difference.

`ordinaryCode_scanOps` and `recoveryCode_scanOps` take the multisig-with-recovery template for `k` of `n` keys, with `1 ≤ k ≤ n ≤ 16`.
Each key and the recovery key have 33 bytes.
For such a template, they discharge the parse hypothesis of its script code, and the `InputContext` gives the count bounds.
For other scripts, `effectiveScriptCode_scanOps` reduces it to the parse of the script suffix from the cursor.
Whatever those hypotheses leave unproved is part of what a reader trusts.

`transactionChecker` takes the elliptic-curve check as a parameter `verify`.
A Script result that uses it holds for Core only under the verifier-agreement hypothesis of [Script signature opcodes and the checker](docs/soundness/script.md#script-signature-opcodes-and-the-checker).
With `verify := coreVerifier`, the theorem keeps no verifier hypothesis.
The agreement is then an A1 claim, with the open step of [Secp256k1 public-key parser and Core's verifier](docs/soundness/cryptography.md#secp256k1-public-key-parser-and-cores-verifier).
The ordered-matching theorems of that subsection also assume a checker answer and passing encoding checks on every pair of signatures and keys.

The worked property of [multisig with recovery](docs/soundness/script.md#script-worked-property-multisig-with-recovery) assumes a checker answer only on the pairs that Core visits, and its soundness direction assumes none.
Its converses also assume a bound on the stack below the redeem script.

`verifyLegacySpend` requires an `InputContext`, whose index selects an input and whose transaction has fewer than 2^32 inputs and outputs.
Core's transaction reader gives the two count bounds, and `InputContext.ofDecoded` takes them from a successful `decodeBaseComplete`.
A caller that builds a transaction from fields must supply them.

`no_wrap_of_validProofOfWorkTarget` discharges the old-target bound of `no_wrap_of_le_powLimit` from Core's target-validity predicate.
Its numerical bound holds for every selected mainnet and testnet record.
Regtest DigiShield uses a separate exact-multiplier argument, and legacy regtest permits wrap in the isolated retarget.
[Target validity and supplied-hash proof of work](docs/soundness/work.md#target-validity-and-supplied-hash-proof-of-work) states the network corollaries and the caller boundary.

A chain-level application still assumes that the previous block passed Core's check with the relevant `powLimit`.
The header path supplies `GetConsensus(0)` to `CheckAuxPowProofOfWork` (D33, `src/validation.cpp` line 2933).
That function passes the record to `CheckProofOfWork` (D6, `src/dogecoin.cpp` lines 107 and 118).
Every record within a network has the same `powLimit` (D14, the record copies at lines 126-136, 282-300 and 425-432).

The round trips of the full header codec assume a payload exactly when the flag is set, and counts within `MAX_SIZE`.
The witness-allowed round trip also assumes a transaction shape.
[Full headers and the AuxPoW payload](docs/soundness/headers.md#full-headers-and-the-auxpow-payload) states them.

The chain-level application also requires that the supplied hash is the correct scrypt digest.

`powHash_eq_spec` and `powHash_eq_fips` prove, for every 80-byte input, that the executable digest equals the RFC 7914 model with Dogecoin's parameters.
`PureBlockHeader.powHash_eq_spec` gives the same equality for the encoded bytes of every pure header.
These theorems relate DogeLib definitions, as [Dogecoin's scrypt digest](docs/soundness/cryptography.md#dogecoins-scrypt-digest) states.
Source review, not a theorem, connects the executable to Core's `scrypt_1024_1_1_256_sp_generic` and the model to RFC 7914 (A1).
The comparison of digests with Core's compiled scrypt covers only the requests that it sends (B4).

`checkAuxPowProofOfWork_iff` characterizes DogeLib's definition of `CheckAuxPowProofOfWork`, and no theorem connects that definition to Core's code.
`verifyLegacySpend_eq_fixedDigest` and `verifyLegacySpend_fixedDigest_congr` require at most `index` outputs and a decided call with `fixedDigestChecker`.
The three template theorems replace the second hypothesis by the template, `HasSingleHashType` for each signature and a verifier that decides every request on `legacyOne`.
[The fixed digest of `SIGHASH_SINGLE`](docs/soundness/script.md#script-worked-property-the-fixed-digest-of-sighash_single) states each hypothesis.
DogeLib does not specify full header validity: [Header proof of work](docs/soundness/headers.md#header-proof-of-work) lists the checks that it omits.

The median-time-past theorems require a view that passes `validateWorkView`, and most of them require at least `medianTimeSpan` entries.
`medianTimePast` checks both conditions and returns an adapter error when one fails, so no caller discharges them silently.
No theorem says that the view is the chain below a given header.
The caller supplies that link, as Core's lookup of `pindexPrev` by hash supplies it.

The theorems of the block-index model take `WellFormed` as a hypothesis.
`lastCheckpointInIndex_eq` also assumes that each checkpoint hash in the index belongs to an entry at its table height.
[The block-index model](docs/soundness/headers.md#the-block-index-model) states both hypotheses and what discharges them.
`checkWellFormed_iff` makes the first hypothesis checkable, and `wellFormed_preserved` shows that each step keeps it.
`accept_genesis_insert` assumes that the index lacks the genesis header's `hashPrevBlock` ([one step](docs/soundness/headers.md#one-step-acceptblockheader)).

### A3. Side channels

DogeLib makes no constant-time claim.
The specification is a reference for behavior, not for timing.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
DogeLib has no security theorem, so it has no idealisation.
Equality of two hash plans needs no assumption about the hash function.
A claim that different preimages give different digests needs a named collision hypothesis or a computational model.
The P2SH theorems of `DogeLib.Script.Proofs.Verify` assume no property of HASH160, and they claim nothing about other redeem scripts with the same digest.

### A5. Protocol context

Some rules apply only under a serialization mode, a network, an activation state or a historical era.
A definition that leaves out its context can be right in one era and wrong in another.
The first operations, base codecs and legacy signature hashing, have few context dependencies.

The transaction readers model two serialization modes of Core's reader: base mode and the witness-allowed format.
The witness-allowed format models serialization only.
Core rejects blocks with witness data on main and test at the pin.
[Transactions: the witness-allowed format](docs/soundness/transactions.md#transactions-the-witness-allowed-format) records the separate script-verification and commitment mechanisms (D36), with their deployment parameters (D9).
No DogeLib theorem establishes consensus acceptance of witness data.

The legacy signature hash is the `SIGVERSION_BASE` mode of `SignatureHash`, and its script code is an input.
[Script signature-code preparation](docs/soundness/script.md#script-signature-code-preparation) specifies the interpreter's preparation of it.

The work-parameter search covers each network and height, and the next-work wrapper selects the candidate height.
The caller's hard-coded activation checks use the previous height, as [Next-work selection and work parameters](docs/soundness/work.md#next-work-selection-and-work-parameters) explains.
Version gating takes its record from the caller, and does not select it from a height.

`block.subsidy` takes the height and the previous block hash from the caller.
Neither the oracle nor the harness checks that the height belongs to a chain or that the hash names its predecessor.
Below height 145,000 the hash selects the random subsidy, so a wrong hash can change the result while both programs agree.
No theorem or adapter establishes that context.

`getContextualParams` selects the contextual fields of a record by network and height.
`lastCheckpoint` takes the node's checkpoint state as an explicit input.
`contextualCheckBlockHeader` selects its record at the candidate height, and takes the network, the adjusted time and the last known checkpoint as explicit inputs.
Its [subsection](docs/soundness/headers.md#contextual-header-validation) records those inputs as execution boundaries.
Script verification takes its flags and its `InputContext` from the caller. Ledger work will need explicit context.

## Gap B: does the code that runs match the definitions?

DogeLib's theorems are about the Lean definitions, and everything between them and the running code is trusted.
A refinement proof relates the extracted functional Lean model to the specification.
Extraction and compiled Rust remain trusted boundaries (B6).

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
Known answers and Core comparisons through the compiled code test it end to end, only on the inputs they cover.
`lake test` runs the 129 NIST CAVP SHA-256 vectors through the compiled `hash`.

### B2. Lean core's own implementations

Lean core implements some `Array`, `ByteArray` and `Nat` operations with `@[implemented_by]` or `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Lean core is a declared trusted baseline.
The packed encoders and decoders run two `@[extern]` operations of core: `ByteArray.push` and `ByteArray.get`.
`ByteSlice.toList` and the tests that call it also run `ByteArray.copySlice`, through `ByteArray.extract`.
The packed decoders of byte lists and of `Bytes n`, `instPackedCodecCountedListBytes` and `instPackedCodecBytes`, call `ByteSlice.toList` to read their bytes, so they run `ByteArray.copySlice` too.

The base-mode slice reader uses `ByteArray.size` (`lean_sarray_size`) for the bounds checks of `ByteSlice.slice` and `ByteArray.toList`.
Its fixed integer reads use `ByteArray.get` (`lean_byte_array_fget`) through `ByteSlice.get`.
Its hash and script reads use `ByteArray.copySlice` (`lean_byte_array_copy_slice`) through `ByteArray.extract` and `ByteSlice.toList`.
`ByteArray.toList` also calls `ByteArray.get!` (`lean_byte_array_get`).

`ByteSlice.size` subtracts its offsets, and `ByteSlice.take` and `ByteSlice.drop` use `ByteSlice.slice` to construct views.
Those slice operations have no separate `@[extern]` or `@[implemented_by]` body in Lean `v4.35.0`.
Only conversion of consumed hash or script bytes to a list copies bytes in this reader.

### B3. Native code during elaboration

If a library sets `precompileModules := true`, then `#eval` or an evaluating tactic in a module that imports it runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The oracle and foreign boundaries

The oracle reads fixture records and writes results through IO.
That adapter is outside the specification library, and no theorem covers it.

The oracle is `dogelib-oracle`, in the `Exports` library ([docs/oracle.md](docs/oracle.md)).
The adapter calls specification functions and converts their arguments and results:

- Lean core's `Json.parse` reads each request, and `Json.compress` writes each response. Both are trusted as Lean core is (B2).
- The adapter's own code converts hexadecimal text to bytes and back, JSON numbers and decimal strings to integers, and the specification's errors to JSON objects.
  The tests check these conversions at their boundaries, against expected values from Core's files, Core's source and Python's `hashlib`.
- The loop over standard input uses `repeat`, which Lean core defines with `partial`. `lake exe check-decls` exempts the `Exports` modules from its check of reachable opaque constants, and checks their axioms and their own declarations.

[docs/soundness/oracle-and-harness.md](docs/soundness/oracle-and-harness.md) records the per-operation adapter, harness, comparator, fixture-generator, forced-CSV, and snapshot boundaries under B4.

Any later foreign boundary, such as a C or Rust binding, is listed here with its size and its error handling.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust. The code that runs is still not the definition a reader reads.

The seven default roots under `DogeLib` and `Refinement` (`DogeLib`, `DogeLib.Proofs`, `DogeLib.Exports`, `DogeLib.Proposals`, `DogeLib.Proposals.Proofs`, `DogeLib.Proposals.Exports` and `Refinement`) have no `@[extern]`, `@[implemented_by]` or `@[csimp]` declarations, by `lake exe check-decls`.
Their safe declarations depend on at most `propext`, `Classical.choice` and `Quot.sound`.
The fixtures in `scripts/CheckDeclsTest` contain them on purpose, to test the check, and no library imports them.

| Declaration | Kind | Proof-backed | Justification |
| --- | --- | --- | --- |

### B6. Extraction and the Rust toolchain

A refinement theorem about extracted Rust is about the Lean model that Charon and Aeneas produce.
It trusts the extraction, any manually modeled dependency, and the Rust compiler and runtime.
The extracted model is an implementation artifact.
It never becomes the specification.

`Refinement/Rust/src/lib.rs` implements the bounded CompactSize reader.
Charon and Aeneas at the pins in SOURCES.md produce `Refinement/Refinement/Rust/Generated/DogelibCompactsize.lean`.
`Refinement/Rust/regenerate.sh --check` compares a fresh extraction with the committed model.
The refinement theorem is about that Lean model, not a proof of the extractors or compiled Rust.
The Rust compiler, standard-library models, extraction tools and runtime remain trusted.

The native example `Refinement/Rust/examples/compactsize_oracle.rs` calls the public Rust reader through a JSON Lines adapter.
`scripts/compare_core.py --rust-compactsize PATH` compares it with the oracle and Core at the pinned revision.
The three programs agree on 404 CompactSize reads: seven existing fixtures and 397 generated boundary, truncation, non-canonical and suffix cases.
The comparison preserves errors, values, consumed counts and remainders on these inputs.

The comparison provides evidence about the compiled binary on these inputs.
No theorem covers the compiled binary or its JSON adapter.
The adapter's `serde_json` development dependency remains outside the extracted library model.

Aeneas represents each input byte with an eight-bit vector and each decoded value with a 64-bit vector.
The abstraction maps those vectors directly to Lean `UInt8` and `UInt64`.
Aeneas slices carry a proof that their length fits Rust `usize`.
This length bound limits the input representation, not the acceptance behavior of the reader.

Rust usize is modeled through Lean core's opaque platform word size.
The refinement holds on both 32- and 64-bit platforms.
The proof does not case on that word size, and it assumes neither 32 nor 64 separately.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set. A theorem may use fewer.

`lake exe check-decls` checks the transitive axiom dependencies of safe declarations under `DogeLib` and `Refinement`, including private proof bodies.
It rejects `sorryAx` even when an unfinished proof comes from an imported module outside that scope.
Unsafe declarations are reported separately.
Detection does not require attribution to a declaration that uses the axiom directly.
It does not check the kernel, and it does not show that the axioms are consistent.

The check walks the dependencies itself and does not use `Lean.collectAxioms`.
In Lean `v4.35.0`, `collectAxioms` can miss an axiom of an imported inductive type that only one of its constructors carries.
It can also miss one that only another type of the same mutual declaration carries.
The check walks an inductive type, the other types of its declaration and all their constructors as one group.
The self-test plants both cases.

The named platform-size exception permits exactly `System.Platform.getNumBits` as a reachable opaque from `Refinement` modules.
This Lean core parameter supplies the word size of Rust `usize`.
The exception does not permit an opaque declaration in either library, another reachable opaque, or this parameter in a `DogeLib` specification definition.
The self-test rejects those cases, imported Aeneas axioms and native proofs.
The allowed axioms remain the same three standard axioms.

Aeneas and Mathlib belong only to the separate refinement package and remain outside the checked module namespaces.
The checker still follows their transitive axiom dependencies at each in-scope use.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

CONTRIBUTING.md does not allow these tactics (*Proofs*).
btc-verified allows the axioms that `bv_decide` records, and its `CompactSize.decode_encode` and `encode_head` use `bv_decide`.
A proof adopted from btc-verified has those steps replaced by proofs the kernel checks alone (design record 0002, section 5).
In `DogeLib.Serialization.Proofs.CompactSize`, `toUInt8_lt_fd` and `toUInt8_ne_zero` replace them.

No theorem across the seven default roots under `DogeLib` and `Refinement` uses them, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` use them on purpose.

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.

`scripts/replay.sh` replays the declarations of each module of `DogeLib` into Lean's kernel, with the function `replayFromImports` of leanchecker in Lean `v4.35.0`.
The replay reads the private part of each module, so it checks the proof bodies again.
The script replays every module: the root `DogeLib.lean` and each `.lean` file under `DogeLib/`.
A second run replays the test-only library of the proposal examples in the same way, the root `tests/ProposalExamples.lean` and each `.lean` file under `tests/ProposalExamples/`.

The script does not read the source to skip a module, and a module without an `.olean` file fails the replay.
The workflow `replay` runs both replays after `lake build --wfail` on each push to `main`, every Monday and on request.
It does not run on pull requests, so a declaration that the kernel did not check can reach `main` before the next replay finds it.

The replay first requires the rejection of a planted theorem that the kernel never checked, `scripts/ReplayFixture.lean`.
Then it replays each module in its own process, with a time budget of 300 seconds for each module.
A module that the kernel rejects, or that does not finish within the budget, fails the replay by name.
`scripts/test_replay.sh` runs the script on planted libraries in CI.
An unchecked theorem in the root fails it, and so does one on the `namespace` line of a module with submodules.

#### Stored inductive types (Lean issues 16730 and 16688)

The replay function of Lean `v4.35.0`, `Kernel.Environment.replay`, sends each inductive declaration to the kernel, but never compares the stored inductive types with the ones that the kernel generates.
In a mutual declaration it sends the kernel the `numParams` of one member only.
A metaprogram can store another member again with a changed `numParams` and `numIndices`, through the private `Lean.Kernel.Environment.add`, which adds a constant without the kernel check.
A module that imports it reads the stored value.
The kernel trusts the stored `numParams` when it types a projection, so the importer can prove `False` with no axiom (Lean issue 16730).
The replay also skips a stored inductive type that its own `all` field does not list, and an importer can use that type too (Lean issue 16688).
Before this change, `scripts/replay.sh` at commit `7444635` accepted the forged module of issue 16730 and its importer.

`scripts/ReplayModule.lean` now keeps the environment that the replay returns.
It requires each constant that the module stores, under its own name, to equal the constant in that environment in every field.
For an inductive type the fields are `levelParams`, `type`, `numParams`, `numIndices`, `all`, `ctors`, `numNested`, `isRec`, `isUnsafe` and `isReflexive`.
The comparison also covers constructors, recursors and every other kind of constant.
It follows Lean pull request 16717, which is not part of Lean `v4.35.0`.
There are two exceptions, both from the replay itself.
The replay skips `unsafe` and `partial` constants, and so does the comparison.
The replay skips a theorem that the imports hold with the same name, type, universe parameters and `all` field, and the comparison accepts it with those fields equal.

An importer can read the exported or the server part of a module instead of the private part, which the replay reads.
So each constant of those parts must equal the constant of the private part, with one exception.
The module system exports a theorem, or a definition without its value, as an axiom with the same name, universe parameters and type.

`scripts/replay.sh` requires the rejection of a second planted module, `scripts/replay-fixtures/ForgedInductive.lean`, the module of issue 16730.
`scripts/test_replay.sh` also compiles its importer, which must prove `False` with no axiom, and a module with the inductive type of issue 16688.
The replay of each forged module fails by name.
The replay of the importer alone passes, because the replay trusts the imports.
So the gate holds only because it replays every module, the imported ones included.

The declaration check runs on pull requests, where the replay does not.
It compares each inductive type in its scope with the other types of its declaration, its constructors and its recursor, which the replay compares with the ones the kernel generates.
A changed `numParams` or `numIndices` shows as a disagreement.
A changed `isRec`, `isReflexive`, `numNested` or `type` does not, so the replay remains the complete check.

#### The source check

`scripts/check_lean_commands.py` reads the Lean source of `DogeLib`, `ProposalExamples` and `Refinement/Refinement`, and runs in CI on each pull request.
It fails on each command that runs code during elaboration, such as `run_cmd`, `#eval`, `elab` and `initialize`.
The script lists them all, with `unsafe` and the attributes that make a declaration an elaborator, a tactic or an initializer.
It also fails on each name that writes the environment, skips the kernel or names a private declaration.
Examples are `setEnv`, `addDecl`, `skipKernelTC`, `_private` and any name with the component `Kernel`.
The allowlist `scripts/check_lean_commands_allowlist.txt` names two lines, each with a reason.
The `initialize` of `DogeLib.Proofs.TheoremTag` registers the attribute described below.
The `elab` of `definition_value%` in `DogeLib.Proposals.Framework.Proofs.Block` returns the stored value of a definition as a term, and writes nothing.
The check matches words in the source, so code that reaches the same functions under another name passes it.
It is a second defence, and the replay is the check of what the modules store.

#### The attribute and the reachability check

`DogeLib.Proofs.TheoremTag` defines the attribute `theorem_tag`, which labels a cited theorem as a property, a model agreement, a refinement, a characterization or a witness.
A proof module that uses the attribute imports that module with `meta import`, and Lean runs the handler of the attribute when it elaborates the module.
The handler rejects an unknown tag and a declaration that is not a theorem, and records the tag in an environment extension.
It adds no declaration, and it does not change a statement or a proof.
A tag is a label that an author chose. No check shows that it describes its theorem.

The default declaration check loads seven roots with their private proof bodies: `DogeLib`, `DogeLib.Proofs`, `DogeLib.Exports`, `DogeLib.Proposals`, `DogeLib.Proposals.Proofs`, `DogeLib.Proposals.Exports` and `Refinement`.
It requires every `.lean` source under `DogeLib/` and `Refinement/Refinement/`, plus their library roots, to appear in that imported environment.
An unreachable module fails the check, including a leaf omitted from its layer root.
This reachability check does not replay kernel checks or detect a metaprogram that bypassed them.
The default imports, checked namespaces and file inventory include the extracted model and its proof.

The default check fails if the separate refinement package is missing, unbuilt or cannot load every requested module.
`--skip-refinement` checks only DogeLib and prints `Refinement NOT checked` in the summary.
Production CI never uses this flag.

#### What C3 still leaves open

The replay uses the same kernel as Lean, so it does not check the kernel itself (C1).
No independent checker, such as one that reads the output of `lean4export`, checks the modules.
The replay does not include the modules under `Refinement/`, which import Aeneas and Mathlib.
For those modules C3 is still open.
The source check covers the Refinement sources of this repository, but not Aeneas or Mathlib.
The replay does not run on pull requests.

## Gap D: does the use of DogeLib hold together?

### D1. Misuse by a client

A correct definition gives a wrong answer when a client calls it outside its input domain.
A prefix decoder returns a remainder, and a client that ignores it accepts trailing bytes.
Each public operation documents its input domain, its failure behavior and whether it consumes the whole input.

`contextualCheckBlockHeader` has three inputs that only the caller can make correct: the adjusted time, the last known checkpoint and the view of the header's chain.
No theorem says that a caller supplies the values that a node would compute.
A client that passes another chain, a stale time or a checkpoint that its block index does not hold gets the result for those inputs.
[Contextual header validation](docs/soundness/headers.md#contextual-header-validation) describes each input.

### D2. Dependency changes

A change to a pinned dependency can change a definition or a proof that DogeLib relies on.
`SOURCES.md` records the pins, and a pin changes only in a reviewed change of its own.
The root DogeLib package has no Lake dependencies.
The separate package under `Refinement/` requires DogeLib and the pinned Aeneas backend, which brings Mathlib.
[ARCHITECTURE.md](ARCHITECTURE.md#lake-libraries) explains the import boundaries, and [BUILDING.md](BUILDING.md#build-and-check) gives the build sequence.

The random block subsidy follows Boost 1.70.0, which the Core pin does not fix ([block subsidy](docs/soundness/blocks.md#block-subsidy)).
The Core comparison prints the Boost release of the harness, so a comparison with another release is visible in its output.

### D3. Wrong fixtures

A fixture with a wrong expected value makes a wrong implementation pass.
Each fixture records its provenance, and a test runner compares results with the committed expectations rather than overwriting them.
A fixture can also carry generated inputs.
The Script corpus's transaction bytes come from a transcription of Core's test builders, which [B4](#b4-the-oracle-and-foreign-boundaries) states.
The subsidy fixture holds block hashes without their headers, so no test repeats the link checks of its fetch ([README](tests/block/mainnet-subsidy-prev-hashes/README.md)).

The fixtures of real mainnet blocks come from the maintainer's node, which the checks treat as untrusted ([README](tests/block/mainnet-blocks/README.md)).
Each block is consistent with its own header: the header has the recorded hash, and the transactions have the Merkle root of the header.
The manifest gives each block the label `pinned` or `linked`.
A `pinned` block has a hash that a committed fixture or a Core checkpoint gives.
If SHA-256 is collision resistant, that hash fixes the 80-byte header and every transaction ID.
It does not fix the bytes of an AuxPoW payload or of witness data.

A `linked` block has no pinned hash: the 1,000 recent blocks of the 11,018 blocks.
Its previous-hash field links it to the block below it in the fixture.
The first block of a linked run was compared with the node's own hash for the height below.
So the run connects to no pinned hash.
The repository therefore does not show that a linked block is the mainnet block of its height. That statement rests on the node.

The four blocks at heights 599,998 to 600,001 are `pinned` by their committed pure headers.
The node and two public TLS Electrum servers returned the same header bytes.
All three sources are untrusted, and no checkpoint connects to this range.
Thus their agreement does not establish mainnet membership.

The comparison result does not depend on that statement.
For each block, pinned or linked, it shows that `checkBlock` and Core's `CheckBlock` give the same result on these bytes.
That result is acceptance with both flags.

Core's acceptance includes the proof-of-work check against the block's own `nBits`.
No check compares that `nBits` with the difficulty that the chain requires, because `CheckBlock` does not read it and the fixtures hold no header context.
So the evidence for a linked block is agreement on a block that passes Core's context-free checks.
Whether the main chain holds the block is a claim that nothing here supports.

The two ranges are release assets, not committed files.
The committed `tests/block/mainnet-blocks/release.json` holds the SHA-256 of each file, and the comparison refuses a file with another hash.
