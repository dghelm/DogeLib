# DogeLib: initial project handoff

**Status:** Design record. Adopted as the starting plan on 2026-11-03. Frozen: track progress in [ROADMAP.md](../../ROADMAP.md) and pins in [SOURCES.md](../../SOURCES.md), not here.  
**Date:** 2026-11-03  
**Companion:** [Contribution policy](../../CONTRIBUTING.md)  
**Audience:** Dogecoin consensus engineers, Lean contributors, Rust implementers, and reviewers

## 1. Purpose and recommended starting point

DogeLib is a proposed executable formal specification and proof library for Dogecoin. Its long-term purpose is to make existing consensus behavior precise, support explicitly versioned protocol proposals, and provide contracts against which implementations and optimizations can be verified.

The first useful release should cover **base transaction encoding and legacy signature-hash construction**. It should include clear executable definitions, meaningful correctness properties, an executable comparison oracle, and a proof that one implementation with a different execution strategy preserves the specification.

The first substantial optimization proof should relate a simple transaction-transformation specification to a streaming signature-preimage implementation. Dogecoin Core already contains a simple historical implementation and randomized comparisons with its production implementation. This provides a concrete starting experiment; it does not establish universal equivalence by itself. [D2]

This document proposes work. No DogeLib implementation, completed proof, Core comparison run, Rust extraction, or performance result is claimed here. The source findings below come from inspection of the referenced repositories.

### Long-term direction

The library should eventually support:

- A faithful account of existing Dogecoin consensus, including relevant historical rules.
- Explicit proposed revisions for features such as SegWit, covenants, proof-verifier operations, and new signature schemes.
- Proofs of properties and compatibility relationships between those revisions.
- Refinement proofs connecting independently reviewed specifications to executable implementations.
- Ledger representation changes such as Utreexo.
- Separate distributed-consensus models if proposals change fork choice or introduce stake-based participation or finality.

Those ambitions do not all belong in the initial release. The initial transaction and signing-commitment slice is useful on its own and supplies definitions needed by later spending rules.

## 2. Starting decisions and source baseline

The following are recommended starting decisions, subject to maintainer adoption.

| Decision | Recommendation |
| --- | --- |
| Initial product | A Lean specification and proof library with a small executable oracle |
| First implementation exercise | Exact byte readers, integer encodings, and CompactSize |
| First useful release | Raw base transaction types, base serialization/parsing, transaction IDs, and legacy signature-hash plans |
| First substantial equivalence proof | Streaming signature-preimage construction versus a reviewed reference transformation |
| First Rust experiment | A small CompactSize implementation extracted through Charon/Aeneas |
| Initial packaging | One repository, with separate specification, proof, and export targets |
| Rule changes | Named proposals separate from the existing-behavior baseline |
| Initial evidence standard | Precise theorem statements plus independently sourced fixtures and Core comparisons |
| First release exclusions | Full Script validity, UTXO/block validity, activation, chain selection, and production-node integration |

### Proposed reference pins

Use exact commits in the source registry and all source links. A tag can remain a human-readable label.

| Repository | Proposed inspected baseline | Role |
| --- | --- | --- |
| Dogecoin Core | `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d` | Compatibility target for the selected functions and modes |
| EthLib | `5d4b58402075ba972936bd446e274c0f4d3e11a5` | Architecture, proof discipline, and candidate primitive reuse |
| btc-verified | `ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce` | Candidate serialization definitions, lemmas, and packed-codec refinement patterns |
| Charon/Aeneas | Select and record compatible exact revisions during the Rust experiment | Implementation extraction and refinement |

The Dogecoin pin is a proposed starting compatibility target, not a claim that every rule in that version has been formalized or that one version exhausts the evidence needed for historical consensus.

Keep the following concepts separate:

- **Reference software revision:** the exact source used to investigate an operation.
- **Protocol context:** the network, branch, activation state, and historical era in which a rule applies.
- **Implemented coverage:** the operations and input domains actually modeled.
- **Proposed revision:** behavior intentionally different from the baseline.

The initial base codecs and legacy hashing functions have relatively limited contextual dependencies. Script, ledger, activation, and historical validation work will need a much richer context.

## 3. Architecture and repository shape

EthLib separates executable definitions, proofs, and exports into distinct Lean library targets. Its architecture also distinguishes concrete protocol definitions from abstract security models. Adopt these boundaries while keeping initial packaging small. [E1] [E2]

### Dependency rules

1. Executable specification modules depend on lower-level specification modules.
2. Proof modules import the definitions they reason about.
3. Export adapters import executable definitions and handle integration concerns.
4. Extracted implementation models depend on their own tool support; refinement proofs connect them to DogeLib.
5. Protocol definitions do not import binding code or extracted implementation models.
6. Abstract security or distributed-consensus models are introduced when a concrete theorem needs them, with an explicit relationship to the executable specification.

Keep heavy mathematical and probabilistic dependencies in proof/model targets where feasible. Do not create multiple repositories or a generic protocol framework before actual consumers require them.

### Suggested initial layout

| Proposed path | Responsibility |
| --- | --- |
| `DogeLib/Base/` | Bytes, fixed-width field meanings, endianness, hash representations |
| `DogeLib/Cryptography/` | Selected reusable primitives and Dogecoin-specific compositions |
| `DogeLib/Serialization/` | Prefix readers, CompactSize, base transaction serialization |
| `DogeLib/Transaction/` | Raw transaction types, transaction IDs, legacy signing commitments |
| `DogeLib/Proofs/` | Codec properties, commitment properties, implementation equivalence |
| `DogeLib/Exports/` | Oracle and later binding-facing adapters |
| `tests/core/` | Pinned fixtures, Core comparisons, minimized regressions |
| `Refinement/Rust/` | Small Rust implementations, extraction configuration, and refinement proofs |

Add Script, Ledger, Rules, and Models areas as the relevant work begins. The paths are proposed organization, not existing modules or implemented commands.

### Minimal project documents

- `SOURCES.md`: pinned references, operation-to-source mappings, and unresolved discrepancies.
- `COVERAGE.md`: operations, domains, modes, eras, theorems, and comparison evidence.
- `SOUNDNESS.md`: logical assumptions, crypto assumptions, execution/extraction boundaries, and integration gaps.
- `CONTRIBUTING.md`: contribution and review policy.
- An architecture section in the README or a short `ARCHITECTURE.md` if needed.

A module must not receive a single undifferentiated “verified” status. Record separately whether it has an executable definition, a particular theorem, Core comparison evidence, and an implementation-refinement theorem.

EthLib's contribution rules and soundness document provide useful examples of source provenance, declaration auditing, and operation-level trust reporting. Adapt those practices to Dogecoin's historical compatibility requirements. [E3] [E4]

## 4. Milestone A: prove a small byte codec

Begin with fixed-width integer encodings, byte readers, and CompactSize. Establish one end-to-end contribution workflow before expanding the library.

### Required specification

Define the encoded-prefix relation independently of the executable decoder. It should describe the marker, payload width, endianness, minimality, size limit, and unconsumed suffix.

Distinguish a generic mathematical encoding from the Core-compatible bounded decoder. In the selected Core source, `WriteCompactSize` accepts a 64-bit value, while `ReadCompactSize` rejects nonminimal encodings and values above `MAX_SIZE = 0x02000000`. [D1]

Therefore, an unrestricted inverse statement over every 64-bit value would be wrong. The intended shape is:

```text
n <= coreMaxSize =>
  decodePrefix(encode(n) ++ suffix) = success(n, suffix)
```

Also establish the two directions of:

```text
decodePrefix(bytes) = success(value, remainder)
  iff ValidCompactSizePrefix(bytes, value, remainder)
```

Round trips alone are insufficient because an encoder and decoder can share the same erroneous interpretation.

### Completion criteria

- The executable decoder is total and returns a typed result.
- The accepted-prefix relation is independently readable.
- Soundness, completeness, and the correctly bounded round trip are proved.
- The returned value and exact remaining bytes agree with the stated relation.
- Core comparisons cover boundary values, nonminimal encodings, oversized values, and truncation.
- Expected answers come from an independent reference, an inspected fixture, or a documented derivation.
- The compiled executable path is exercised, with its compiler/runtime trust boundary documented.

The Core serialization bound is not a statement about the maximum valid block size.

## 5. Milestone B: transaction encoding and legacy signing commitments

The first useful release should answer a concrete question:

> Given base transaction bytes, a script code, an input index, and a hash type, what transaction does the selected parser produce, and what exact legacy signing commitment is computed?

### 5.1 Preserve raw fields

Represent the wire-level fields without silently validating or normalizing them.

| Structure | Required information |
| --- | --- |
| Outpoint | Exact hash bytes and output index |
| Input | Outpoint, raw script bytes, sequence |
| Output | Signed 64-bit amount meaning and raw script bytes |
| Transaction | Signed 32-bit version meaning, inputs, outputs, locktime |
| Hash | Exact 32-byte value, with named wire/display conversions |

A decoder must be able to represent an amount that later validation rejects. Defining every decoded output amount as an already-valid nonnegative money type would merge two different operations.

Scripts must retain their original bytes. A parsed instruction view can be added alongside those bytes, but canonicalizing pushes or discarding encoding distinctions can change commitments.

### 5.2 Select the serialization contract explicitly

The initial contract is base/no-witness transaction serialization and parsing. State the parse mode in APIs, fixtures, and coverage.

Core contains optional witness-format parsing machinery controlled by serialization mode. Some parser paths and reserialization behavior require separate analysis. The initial base parser must not be described as a replacement for every Core network-facing parser. [D4]

Define prefix parsing separately from a wrapper that requires complete input consumption. A caller must not accidentally accept trailing bytes because an internal parser intentionally returns a remainder.

### 5.3 Define the lower-level legacy hash API

The initial specification should cover:

- ALL, NONE, SINGLE, and ANYONECANPAY combinations.
- The actual handling of other raw hash-type values.
- Input-index-out-of-range behavior.
- SINGLE with no corresponding output.
- Null output placeholders and sequence modifications.
- Script-code separator handling.
- Exact appended hash-type encoding.
- Fixed-digest special cases. [D2] [D3]

Distinguish the lower-level `SignatureHash` API, whose hash type is a raw 32-bit field, from the spending-facing wrapper that obtains the hash type from a signature byte. Existing Core tests exercise the broader lower-level API. [D2] [D3]

The caller's preparation of `scriptCode` must be explicit. Script execution, the last executed code separator, and signature-removal behavior are separate integration obligations. A theorem about a supplied script code does not by itself prove the complete CHECKSIG path.

Compatibility claims concern the declared operation and its defined behavior. An implementation crash or C++ undefined behavior outside that contract is a discrepancy to investigate, not an outcome to reproduce as a protocol rule.

### 5.4 Separate preimage construction from hashing

A useful conceptual result type is:

```lean
-- Design sketch; Hash256 is defined elsewhere.
inductive LegacyHashPlan
  | fixedDigest : Hash256 -> LegacyHashPlan
  | hashBytes   : ByteArray -> LegacyHashPlan
```

Ordinary cases produce the bytes to hash. Historical special cases produce a fixed digest.

This structure makes exact commitment construction visible and allows much of the equivalence work to proceed independently of hash implementation verification. Equal plans evaluated with the same deterministic hash give equal digests. No collision-resistance hypothesis is needed for that equality result.

Higher-level claims about authorization or resistance to maliciously chosen collisions require their own definitions and assumptions.

### 5.5 Supply an executable oracle

Provide a small command-line adapter that consumes structured fixture records and returns, as applicable:

- Parsed fields and bytes consumed.
- Remaining input or a complete-consumption result.
- Base serialization and transaction ID.
- Legacy hash plan, preimage, and digest.
- Structured decoding errors.

Use it from Core and Rust comparison harnesses. Production FFI stability is unnecessary for the first release.

Include preimages in diagnostic output so a mismatch can be reduced to the first differing field or byte. Output conventions must make hash display order and raw byte order unambiguous.

## 6. Milestone C: prove one meaningful implementation equivalence

### Existing motivation in Core

The selected Core test file contains `SignatureHashOld`, which copies and modifies a transaction before serializing it. The production path uses `CTransactionSignatureSerializer` to emit the relevant fields directly. The randomized test is configured for 50,000 comparisons, and another test consumes the committed signature-hash corpus. These are source observations, not tests run for this handoff. [D2] [D3]

### Proposed formal experiment

1. Write an independently reviewed transaction-transformation specification.
2. Write a streaming preimage constructor with a different execution strategy.
3. Prove equality of their complete hash plans over the declared domain.
4. Derive digest equality from plan equality.
5. Compare the compiled implementations with the pinned Core behavior.
6. Benchmark only after correctness is established and report measured results separately.

The main contract is:

```text
Preconditions(tx, scriptCode, inputIndex, hashType) =>
  streamingPlan(tx, scriptCode, inputIndex, hashType)
    = referencePlan(tx, scriptCode, inputIndex, hashType)
```

### Domain and malformed scripts

Do not assume the old Core helper and streaming serializer are equivalent on every arbitrary malformed script byte string. The serializer uses Script instruction parsing and cursor advancement, and malformed push tails require their own analysis. The randomized generator in the motivating test uses relatively simple opcode sequences. [D2] [D3]

A useful first theorem may assume a syntactically fully parsed script code. Record that restriction in the theorem, public coverage, and release description. Separately characterize excluded raw API behavior; later Script work must prove that the relevant caller supplies the required preconditions.

Do not silently turn a raw API outcome into a decoder error merely to simplify a proof. Choose and document the intended operation first.

### What the proof establishes

A Lean-versus-Lean equality theorem establishes that those definitions agree under its hypotheses. It does not verify existing C++ object code. Core comparisons provide empirical compatibility evidence. Rust extraction/refinement or a separate C++ verification effort is needed for a stronger implementation claim.

An implementation with fewer intermediate allocations is a candidate optimization. Its actual performance remains unmeasured until benchmarked. Termination also does not establish an acceptable resource bound.

## 7. Milestone D: demonstrate the Rust refinement path

Run this experiment once the first codec contract is stable; it can proceed before the complete signing-commitment release.

1. Implement a small safe Rust CompactSize decoder.
2. Pin the Rust toolchain, Charon/Aeneas revisions, matching support libraries, and extraction configuration.
3. Extract the supported implementation into a Lean model.
4. Define the representation relation for inputs, values, errors, and remaining bytes.
5. Prove the extracted implementation matches DogeLib's independent contract.
6. Exercise the compiled Rust path with the same fixtures and boundary cases.

Aeneas provides a Rust-to-Lean verification workflow with a supported language subset and explicit modeling requirements. Select exact revisions during the experiment rather than promising compatibility from moving branches. [R1]

Keep generated code and extraction support on the implementation side of the theorem. Do not redefine the protocol specification to be whatever the extraction tool emits.

The soundness record must distinguish extraction assumptions, manually modeled dependencies, compiler/runtime assumptions, and any FFI boundary. Successful source-level refinement does not automatically verify all of those layers.

## 8. Reuse strategy

Reuse exact compatible definitions and theorems, after checking their input domains, assumptions, byte conventions, and build requirements.

### EthLib

The inspected SHA-256 proof relates executable code to a separate FIPS-based specification for messages shorter than 2^61 bytes. It is a strong candidate for the transaction-hashing foundation. Define Dogecoin's double-SHA composition and wire/display interpretation explicitly. [E5]

Curve arithmetic may also be reusable, but protocol acceptance wrappers need independent review. For example, the inspected EthLib decoder handles compressed and ordinary uncompressed public keys, while Dogecoin's bundled parser also handles hybrid encodings under the applicable checks. Mathematical ECDSA compatibility does not establish compatibility of public-key encodings, DER handling, or Script flags. [E6] [D5]

### btc-verified

The inspected packed-codec work documents implementations over ByteArray/ByteSlice related to a simpler serialization specification. Its agreement properties cover acceptance, returned values, and unconsumed bytes. This is relevant both as a reuse candidate and as a pattern for DogeLib's own representation refinements. [B1]

Audit any imported Bitcoin rule against Dogecoin. Shared ancestry is evidence to investigate, not a compatibility proof.

### Dependency decisions

During bootstrap, decide whether each candidate should be a pinned dependency, a narrowly maintained adaptation, or a design reference. Preserve attribution and applicable notices. Confirm toolchain compatibility with an actual build before claiming a combination works.

Avoid introducing a general cross-chain primitive framework until concrete reuse demands it.

## 9. Review, evidence, and initial implementation order

The companion contribution policy defines the proposed contribution standards. Its central requirement is to make the semantic contract reviewable independently of the implementation and proof.

### Suggested work order

| Step | Deliverable | Exit condition |
| --- | --- | --- |
| 1 | Source registry, shared types, build boundaries, contribution policy | Baseline and evidence conventions are explicit |
| 2 | CompactSize specification and proofs | Accepted-prefix relation, bounded round trip, and Core comparisons |
| 3 | Raw transaction types and base codecs | Exact field preservation, explicit mode, and parser obligations |
| 4 | Legacy hash-plan specification | Declared lower-level modes and special cases are covered |
| 5 | Streaming implementation and proof | Exact plan equality on the recorded domain |
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract |

These are logical units of review, not a requirement for six separate PRs. Combine closely related changes when they remain easy to assess. The Rust experiment can start after step 2.

### Release acceptance criteria

A first release should have:

- A source mapping and explicit input domain for every public operation.
- Relevant codec soundness and completeness properties, with correctly bounded inverses.
- Raw fields that preserve values rejected by later validation.
- Documented lower-level legacy hash modes and special cases.
- At least one nontrivial implementation-equivalence theorem.
- An executable oracle and reproducible Core comparison harness.
- Independent fixtures, targeted boundary/malformed cases, and minimized mismatches.
- A statement of proof assumptions, execution boundaries, and unsupported areas.
- Validation reports identifying the exact revisions and commands actually run.

The Rust refinement is an early project gate and a useful demonstration. If it is not included in the first release, its status must be explicit and no Rust verification claim should appear in that release.

### Decisions to settle during bootstrap

- Adopt the proposed Core compatibility pin or select another explicit pin.
- Select compatible Lean and dependency revisions.
- Choose the minimal hash and codec reuse strategy.
- Agree on the first signature-proof domain and track the excluded cases.
- Select the oracle record format.
- Adopt a project license and preserve upstream terms; this handoff does not select one.

## 10. Next layers and upgrade work

After the transaction release, build Script decoding, Script numbers, execution, failure behavior, signature wrappers, P2SH, multisig, and CLTV. Then supply the transaction and previous-output context needed for input validation.

That enables a bounded first upgrade experiment, such as a carefully specified NOP-based covenant rule. A local spending-rule theorem must be labeled as local until the block, activation, and legacy-projection obligations have also been established.

| Future work | Required foundation |
| --- | --- |
| SegWit | Versioned serialization, signing commitments, Script rules, block commitments, activation |
| Covenants and zk verification | Authenticated spending context, state effects, verifier semantics, resource bounds |
| Quantum-resistant authorization | Precise verifier and encoding rules, complete spending-policy analysis, migration design |
| Utreexo | UTXO transition semantics and an explicit state-representation relation |
| Hybrid PoS | Ledger and existing work rules plus a separate fork-choice/network/participation model |

A small DigiShield arithmetic module is a reasonable parallel task for another contributor. It should not delay the transaction path. Its contract must account for C++ signed-division rounding and fixed-width arithmetic; proving an isolated retarget function is separate from proving header validity. Core has a dedicated rounding regression that can anchor this work. [D6] [D7]

### Proposed first-release description

> DogeLib defines Dogecoin's base transaction encodings and legacy signing commitments, provides an executable comparison oracle, and proves a streaming commitment implementation equivalent to its specification over a documented input domain.

Use that description only after the stated work is complete. Until then, it is the release target.

## Source references

Dogecoin and candidate-library references are pinned to the inspected commits. The Aeneas documentation link is discovery material; select and record an exact tool revision before implementation.

- **D1 — Dogecoin serialization:** CompactSize reader/writer and MAX_SIZE.
- **D2 — Dogecoin signature-hash tests:** historical helper, randomized comparison, and fixture consumption.
- **D3 — Dogecoin Script interpreter:** signature serializer, legacy SignatureHash, and signature-checker wrapper.
- **D4 — Dogecoin transaction types and serialization:** base and optional witness modes.
- **D5 — Dogecoin bundled public-key parser:** accepted point encodings.
- **D6 — Dogecoin difficulty logic:** CalculateDogecoinNextWorkRequired.
- **D7 — Dogecoin difficulty tests:** DigiShield rounding regression.
- **E1 — EthLib build definition:** specification, proof, and export targets.
- **E2 — EthLib architecture:** executable definitions, properties, models, and dependencies.
- **E3 — EthLib contribution policy:** source provenance, proof discipline, and declaration checks.
- **E4 — EthLib soundness documentation:** exact proof coverage and trust boundaries.
- **E5 — EthLib SHA-256 proof:** executable/specification agreement.
- **E6 — EthLib point encoding:** decoder acceptance.
- **B1 — btc-verified packed serialization:** representation-refinement approach.
- **R1 — Aeneas documentation:** Rust extraction workflow and limitations.

[D1]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/serialize.h
[D2]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/sighash_tests.cpp
[D3]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp
[D4]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/transaction.h
[D5]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/eckey_impl.h
[D6]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp
[D7]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/dogecoin_tests.cpp
[E1]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/lakefile.lean
[E2]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/ARCHITECTURE.md
[E3]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/CONTRIBUTING.md
[E4]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/SOUNDNESS.md
[E5]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/EthLib/Cryptography/Proofs/Hash/Sha256.lean
[E6]: https://github.com/ethereum/EthLib/blob/5d4b58402075ba972936bd446e274c0f4d3e11a5/EthLib/Cryptography/Secp256k1/Encoding.lean
[B1]: https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/README.md
[R1]: https://github.com/AeneasVerif/aeneas

