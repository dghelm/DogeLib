# Roadmap

This roadmap records completed milestones and next work.
[COVERAGE.md](COVERAGE.md) holds detailed evidence, and [SOUNDNESS.md](SOUNDNESS.md) explains its assumptions and limits.
The reasoning behind the work order is in [design record 0001](docs/design/0001-initial-handoff.md) and [design record 0002](docs/design/0002-btc-verified-reuse.md).
Update the *Status* column when the pull request merges, not when work starts.

**Model project.** Where EthLib and btc-verified differ, DogeLib follows EthLib. That covers architecture, the proof-trust policy, the module system, the writing standard and the soundness documentation. The btc-verified project supplies components, mainly its codecs and packed-codec refinements, which DogeLib adapts to EthLib's structure.

## Work order

| Step | Deliverable | Exit condition | Status |
| --- | --- | --- | --- |
| 0 | Toolchain, build skeleton and checks | Lean `v4.35.0` is pinned. The lakefile has the libraries of ARCHITECTURE.md. EthLib's SHA-256 builds. `lake exe check-decls` runs. `BUILDING.md` lists the commands. | Done in `build/toolchain-selection` |
| 0b | Codec adaptation from btc-verified: codec foundations | btc-verified's codec class, fixed-width integer codecs, byte-buffer lemmas and packed codecs are ported to `v4.35.0` and DogeLib's layout, with provenance recorded | Done in `feat/codec-foundations` |
| 0b | Codec adaptation from btc-verified: CompactSize and counted lists | btc-verified's CompactSize and `CountedList` codecs and their packed forms are ported on top of the codec foundations, with `bv_decide` steps replaced and provenance recorded | CompactSize done in `feat/compactsize`. `CountedList` done in `feat/countedlist`, with Core's bounded vector reader. |
| 1 | Source registry, shared types, contribution policy | Baseline and evidence conventions are explicit | Done, as documents |
| 2 | Bounded CompactSize reader and proofs | Accepted-prefix relation, bounded round trip, Core comparisons | Reader, relation, soundness and completeness, bounded round trip, and known answers from Core's tests done in `feat/compactsize`. A packed form of the reader is done in `feat/packed-bounded-compactsize`. The comparison with Core's `ReadCompactSize` and `WriteCompactSize` is done in `test/core-harness`. |
| 3 | Raw transaction types and base codecs | Exact field preservation, explicit parse mode, parser obligations | Fixed-length byte strings and `Hash256` done in `feat/fixed-bytes`. Transaction types, base codecs, Core's base-mode reader, the complete reader and the transaction ID done in `feat/transaction-base`. The base-mode records of Core's transaction corpus are known answers (issue #22). The witness-allowed format, as a serialization format only, done in `feat/transaction-witness-format`. The oracle exposes both witness readers, serialization and hashes. The Core comparison covers all 198 corpus records and malformed variants (issue #36). |
| 4 | Legacy hash-plan specification | Declared lower-level modes and special cases are covered | Done in `feat/legacy-sighash`: `legacySignatureHashPlan` for `SIGVERSION_BASE`, Core's `sighash.json` corpus and hand-derived preimages as known answers. `Script.transactionChecker` uses the plan for the legacy signature checks. The witness v0 digest is not specified. |
| 5 | Field-by-field preimage construction proved equal to the transaction-transformation reference | Exact plan equality on the recorded domain | Done in `proof/legacy-sighash-reference`. `legacySignatureHashPlan_eq_reference` proves the production plan equal to the `SignatureHashOld` transformation. It needs a fully parsed script code and counts below 2^32. The two differ on a script that ends in a short push. |
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract | Done in `feat/rust-compactsize-refinement` (#51). See [milestone D](#d-the-rust-refinement-path-step-6). |

The steps are units of review, not one pull request each.
Step 6 can start after step 2.

Steps 0 and 0b follow design record 0002: the first contributions adopt audited codec foundations and then define Dogecoin's bounded decoding contract. They replace the original plan to build fixed-width encodings and CompactSize from scratch. Design record 0002 preferred a pinned btc-verified dependency first. The decisions below choose an adaptation instead, because btc-verified's toolchain, file structure and trust policy all differ from EthLib's.

## Completed after the work order

Each item below is complete.
[COVERAGE.md](COVERAGE.md#operations) records its evidence, and the linked section of [SOUNDNESS.md](SOUNDNESS.md) states its hypotheses and boundaries.

- **Work arithmetic.** The DigiShield retarget, height-based parameter selection, `GetNextWorkRequired` on a checked finite view and the compact-target check of a supplied hash.
  The 256-bit word paths of the retarget have arithmetic equivalence proofs ([target validity](SOUNDNESS.md#target-validity-and-supplied-hash-proof-of-work), [word division](SOUNDNESS.md#256-bit-word-division)).
  This work ran in parallel with the transaction path, as design record 0001, section 10, requires.
- **Blocks.** 80-byte pure headers, their double SHA-256 hashes, and transaction Merkle roots with mutation detection ([headers and Merkle roots](SOUNDNESS.md#pure-headers-and-transaction-merkle-roots)).
  Full headers with the AuxPoW payload, read and written in each read mode of the embedded transaction ([full headers](SOUNDNESS.md#full-headers-and-the-auxpow-payload)).
  This codec is stage 2 of [design record 0004](docs/design/0004-header-proof-of-work.md).
  `CAuxPow::check`, stage 3, with its merged-mining search and expected index ([the AuxPoW check](SOUNDNESS.md#the-auxpow-check)).
  The Core harness reconstructs all 26 `check_auxpow` payloads with exact byte agreement and compares their verdicts.
- **Header proof of work, [design record 0004](docs/design/0004-header-proof-of-work.md).** Stages 0, 1, 2, 3, 4a, 4b and 5 have their implementation evidence.
  HMAC-SHA256, PBKDF2, the RFC 7914 scrypt model and the fixed Dogecoin executable have their models, agreement theorems and independent vectors.
  The header codec, AuxPoW check, proof-of-work composition and two version gates have their stated theorems and compiled checks.
  The oracle and Core comparison close the three deferred items: exact construction of 26 payloads, Core checks of all 321 historical headers and version-gate comparison.
  The harness also re-mines all 12 `auxpow_pow` cases, including the in-memory flag/payload mismatches, and compares Lean on identical components.
  [The comparison evidence](docs/oracle.md#header-proof-of-work-evidence) records the streams, seeds and limits.
- **Signature verifier, [design record 0005](docs/design/0005-signature-verifier.md).** Stages 1 to 4 are complete.
  Stage 1 adapts the secp256k1 curve arithmetic and scalar ECDSA verifier from EthLib, with independent Wycheproof known answers ([ECDSA](SOUNDNESS.md#secp256k1-curve-and-ecdsa-scalar-verification)).
  Stage 2 adds Core's public-key parser and `coreVerifier`, Core's `CPubKey::Verify`, and runs Core's Script and transaction corpora with it in `lake test` ([Core's verifier](SOUNDNESS.md#secp256k1-public-key-parser-and-cores-verifier)).
  Stage 3 connects the oracle: its verdicts agree with Core on 598 dedicated public-key inputs and on the Script and transaction corpora.
  Stage 4 checks all 25 Core-signed recovery-template fixtures in `lake test`, and the oracle comparison rechecks them with live Core.
  Agreement of the point arithmetic with Core's `secp256k1_ecmult` is finite comparison evidence, without an all-input theorem.
- **SHA-1, RIPEMD-160 and Hash160.** The hash prerequisites of legacy Script, with known answers ([SHA-1](SOUNDNESS.md#sha-1), [RIPEMD-160 and Hash160](SOUNDNESS.md#ripemd-160-and-hash160)).
- **Legacy Script, stages 1 to 5 of [design record 0003](docs/design/0003-legacy-spend-validation.md).** The instruction reader, Script numbers, one `EvalScript` call, signature-code preparation, encoding checks, the signature and lock-time opcodes, `VerifyScript` with P2SH, and `verifyLegacySpend` for one input.
  Script verification takes a signature checker as a parameter, and `coreVerifier` supplies ECDSA verification ([the checker](SOUNDNESS.md#script-signature-opcodes-and-the-checker)).
  The oracle exposes `script.read_op`, `script.eval` and `script.verify_legacy`, and the Core comparison covers them ([counts](docs/oracle.md#the-comparison)).
- **Worked property of design record 0003, section 7.** `multisigRecovery_sound` and its two converses characterize acceptance of the multisig-with-recovery template for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16` ([worked property](SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
  With 33-byte keys, the 520-byte push limit allows at most 13 keys for this template under P2SH.

## Next work

Release 0.1.0 is out, as tag `v0.1.0` at commit `7510cc9`.

The milestone before the current one was contextual header validation, under [design record 0006](docs/design/0006-contextual-header-validation.md).
The maintainer adopted the record on 2026-11-07, with all nine decisions of its section 12.
The milestone specifies the checks of `ContextualCheckBlockHeader` other than the version gates.
They are `nBits` against `GetNextWorkRequired`, the checkpoints, the time checks and the rejection of outdated versions.
Section 10 of the record gives four stages, and section 11 gives their theorem targets:

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | Median time past on a checked view, with its depth requirement | Specified in `Work.MedianTimePast`, with theorems and known answers |
| 2 | Parameters by height: `fAllowLegacyBlocks`, `BIP65Height`, `BIP66Height` and the checkpoint tables | Specified in `Block.ContextualParams`, with theorems and known answers |
| 3 | The composition `contextualCheckBlockHeader`, with its characterization theorems and known answers | Specified in `Block.ContextualCheck`, with the theorems of section 11 and known answers from five mainnet ranges and synthetic views |
| 4 | The oracle operation `block.contextual_check`, the Core harness and the comparison | Implemented with the H2 transcription, independent fixture expectations, boundary cases, seed `20261109` mutations and comparator self-tests. [Evidence boundary](SOUNDNESS.md#contextual-header-validation) and [streams](docs/oracle.md#contextual-header-comparison-evidence) |

The adoption of the scope establishes no target theorem.
Each stage reports its evidence in COVERAGE.md and SOUNDNESS.md when it merges.

[Design record 0007](docs/design/0007-proposed-revisions.md) sets how DogeLib specifies proposed revisions and proves their compatibility with the baseline.
The maintainer adopted the record on 2026-11-07.
Decisions 1 to 10 of its section 13 are accepted, and decision 11 is deferred to a signalling record.
Section 12 of the record gives two stages:

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | The `Proposals` and `ProposalProofs` libraries, the import check, the activation model and the Script loop with a step parameter | Specified in `DogeLib.Proposals.Framework`, with the framework targets of section 11 except `checkBlockHeader_not_versionBitsCondition` (decision 11), and the import-check self-test |
| 2 | The worked example `ExampleVersionVerify`, with its theorem targets and known answers | Specified in `DogeLib.Proposals.ExampleVersionVerify`, with every target of section 10.3 and known answers through the compiled code |

The current milestone is header-sequence validation, under [design record 0008](docs/design/0008-header-sequence-validation.md).
The maintainer adopted the record on 2026-11-07, with every decision of its section 13.
It specifies Core's `AcceptBlockHeader` and `ProcessNewBlockHeaders` over an explicit model of the block index.
The model includes the duplicate test, the predecessor lookup, the failed-ancestor walk and the chain work of each entry.
Section 10 of the record gives five stages, and section 11 gives their theorem targets:

| Stage | Deliverable | Status |
| --- | --- | --- |
| 1 | The block-index model, the ancestor view and the checkpoint search over the index | Specified in `Block.HeaderSequence`, with the targets `ancestorView_congr` and `lastCheckpointInIndex_eq` and known answers from five mainnet ranges |
| 2 | One step, `acceptBlockHeader`, with its characterization theorems | Not started |
| 3 | The sequence, `processNewBlockHeaders`, with the linear theorem `process_linear` | Not started |
| 4 | `GetBlockProof` and the chain work of each entry | Not started |
| 5 | The oracle operation `block.header_sequence`, the Core harness and the comparison | Not started |

One other candidate is unscheduled, and it needs an approved scope before work starts:

- **Arithmetic agreement with Core's verifier.** A Lean proof that `Point.mulAdd` computes Core's `secp256k1_ecmult` result ([design record 0005](docs/design/0005-signature-verifier.md), section 4.3).
  The proof needs Mathlib, so it requires a package proposal first.

DogeLib specifies Dogecoin Core.
A property of an application template belongs in a downstream project.

## Milestones

### A: a small byte codec (steps 0, 0b and 2)

A Dogecoin-compatible bounded CompactSize reader, separate from the generic canonical decoder. Its contract:

```text
dogeDecode(bytes) = success(value, remainder)
  iff genericDecode(bytes) = success(value, remainder)
      and value <= 0x02000000
```

The distinguishing input `fe 01 00 00 02` encodes `0x02000001`. The generic decoder accepts it, and the Core reader rejects it. Do not replace the decoder inside an unconditional `Codec UInt64` instance while keeping its old laws.

### B: transaction encoding and legacy signing commitments (steps 3–4)

Raw fields preserved without validation, base/no-witness parsing with prefix and complete-input forms kept apart, and a `LegacyHashPlan` that separates preimage construction from hashing. Includes the executable oracle.

The oracle, `dogelib-oracle`, exists ([docs/oracle.md](docs/oracle.md)). The Core harness runs Dogecoin Core's code on the same requests, and CI compares the two ([docs/oracle.md](docs/oracle.md#the-core-harness)).

The oracle also exposes pure headers, Merkle roots, RIPEMD-160, Hash160, SHA-1, the work operations and Script.
The Core comparison covers their committed fixtures and generated boundaries ([format and comparison](docs/oracle.md)).

### C: one meaningful implementation equivalence (step 5)

The field-by-field preimage construction is proved equal to the transaction-transformation reference by `legacySignatureHashPlan_eq_reference`.
The theorem requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
It holds for every input index and hash type on that domain.
The implementation constructs the whole preimage as a byte list before hashing.
An incremental hash sink and measured memory or speed gains are later work.

### D: the Rust refinement path (step 6)

The bounded Rust CompactSize decoder and its extracted Lean model are in `Refinement/Rust/` and `Refinement/Refinement/Rust/` (#51).
`decode_refines` proves complete-result agreement with the independent bounded-reader specification.
[SOUNDNESS.md](SOUNDNESS.md#rust-bounded-compactsize-reader) explains the theorem's domain, complete-result equality and extraction boundaries.
[COVERAGE.md](COVERAGE.md#operations) records its proof and fixture evidence.
[Refinement/Rust/README.md](Refinement/Rust/README.md) gives the regeneration and test commands.

## Release acceptance criteria

From design record 0001, section 9. A first release has:

- A source mapping and explicit input domain for every public operation.
- Codec soundness and completeness properties, with correctly bounded inverses.
- Raw fields that preserve values rejected by later validation.
- Documented lower-level legacy hash modes and special cases.
- At least one nontrivial implementation-equivalence theorem.
- An executable oracle and a reproducible Core comparison harness.
- Independent fixtures, targeted boundary and malformed cases, and minimized mismatches.
- A statement of proof assumptions, execution boundaries, and unsupported areas.
- Validation reports identifying the exact revisions and commands actually run ([report command](BUILDING.md#validation-reports)).

## Decisions

The maintainer decided the oracle development policy on 2026-11-06, and on the same day extended it from the pre-release period to all 0.x releases.
A consumer pins a release or commit and uses that release's oracle, harness and comparison tools.
Within an approved scope, additive operations and changes to existing operations receive ordinary independent review.
A change to an existing operation is marked as breaking.
See [format stability](docs/oracle.md#format-stability).

| Decision | Choice | Reason | Confirmed by |
| --- | --- | --- | --- |
| Model project | EthLib | Stronger separation of specification, property and model, and explicit soundness documentation | Maintainer, 2026-11-03 |
| Lean toolchain | `v4.35.0`, EthLib's | Follows the model project and its module system. btc-verified pins `v4.30.0-rc2`. | Step 0 build |
| SHA-256 provider | EthLib | Its `hash_eq_spec` relates the executable code to a separate FIPS 180-4 model. It needs only Lean core, so it is adapted, not required. | Step 0 build |
| Proof-trust policy | EthLib's: standard axioms only, no tactic that trusts compiled code | See SOUNDNESS.md, C2 | Adopted |
| btc-verified reuse form | Adaptation into DogeLib's layout, with provenance, not a dependency | Different toolchain, colocated proofs, and `bv_decide` steps | Step 0b, codec foundations, with Lean core and `Std` only |
| Writing standard | EthLib's `WRITING.md` and checker, with DogeLib vocabulary | Follows the model project | Adopted |
| Oracle record format | JSON Lines, `dogelib-oracle/1`, in [docs/oracle.md](docs/oracle.md) | One request and one response per line, so a harness can keep the oracle open. Hashes in both byte orders, preimages, checker selection and legacy Script verification. | Maintainer, 2026-11-06: reset to `/1` and pre-release development policy. |
| Oracle policy in 0.x | Consumers pin a release. Within an approved scope, additive operations and changes to existing operations get ordinary independent review. A change to an existing operation has `!`, a `BREAKING CHANGE:` footer and a release-notes entry. One format implementation per release. | Keeps routine oracle work out of the maintainer-only public-contract rule after 0.1.0. Core target, theorem weakening, trust assumptions and protocol semantics stay maintainer-only. A 1.0 stability promise is a later decision. | Maintainer, 2026-11-06 |
| Core compatibility pin | Dogecoin Core `v1.14.9`, commit `e0a1c15` | The latest Core release on 2026-11-03 | Maintainer, 2026-11-03, issue #5 |
| First signature-proof domain | Script code with no instruction that fails to parse, in a transaction with fewer than 2^32 inputs and 2^32 outputs | `legacySignatureHashPlan_eq_reference` holds on it. On a script that ends in a short push the two forms differ. | Step 5, `proof/legacy-sighash-reference` (#27) |
| Rust refinement tools | Aeneas `d1e177b` and Charon `a58d159` (Adopted in SOURCES.md). Mathlib only in the separate `Refinement` Lake package. No trust-policy exception for Aeneas's axioms | Both tools target Lean `v4.35.0`. EthLib requires Mathlib. EthLib's trust policy allows only the three standard axioms | Maintainer, 2026-11-04, PR #33 |
| Project licence and contributor terms | MIT, in `LICENSE`. A contributor makes a contribution available under the same licence. Material from other projects follows CONTRIBUTING.md. | The most open licence that is compatible with the material DogeLib takes from other projects | Maintainer, 2026-11-04, issue #4 |

## Open decisions

None. A maintainer decision that blocks a lane becomes an issue with the `needs-maintainer` label.

## Deferred work

Deferred work is tracked as GitHub issues with the `deferred` label.
Decisions that only a maintainer can make carry the `needs-maintainer` label.

The EthLib pin audit leaves these follow-up tasks:

- Port EthLib `d59f0e3a` (SHA-256 kernel evaluation) while preserving DogeLib's public APIs, theorem statements and SHA-1 reuse of padding and word reads.
- Port EthLib `4f798a14` (RIPEMD-160 bounds proofs) while preserving the public `little32` and `compress` contracts and every existing theorem statement.
- Review EthLib `ad1185d6` (writing guide and checker) separately, with an explicit decision about DogeLib's writing rules and vocabulary.
