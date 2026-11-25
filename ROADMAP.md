# Roadmap

This roadmap records completed milestones and next work.
[COVERAGE.md](COVERAGE.md) summarizes evidence (with full details in `docs/coverage/`), and [SOUNDNESS.md](SOUNDNESS.md) explains its assumptions and limits.
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
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract | Done in `feat/rust-compactsize-refinement` (#51). See [milestone D](#milestones). |

The steps are units of review, not one pull request each.
Step 6 can start after step 2.

Steps 0 and 0b follow design record 0002: the first contributions adopt audited codec foundations and then define Dogecoin's bounded decoding contract. They replace the original plan to build fixed-width encodings and CompactSize from scratch. Design record 0002 preferred a pinned btc-verified dependency first. The decisions below choose an adaptation instead, because btc-verified's toolchain, file structure and trust policy all differ from EthLib's.

## Completed milestones

Releases: `v0.1.0` at `7510cc9` ([docs/release-notes/0.1.0.md](docs/release-notes/0.1.0.md)) and `v0.2.0` at `ea335a0` ([docs/release-notes/0.2.0.md](docs/release-notes/0.2.0.md)).
Each row below is complete. [COVERAGE.md](COVERAGE.md#operations) and `docs/coverage/` record per-operation evidence, and [SOUNDNESS.md](SOUNDNESS.md#what-the-proofs-say) links to theorem hypotheses and boundaries.

| Milestone | Scope and recorded qualifiers | Evidence |
| --- | --- | --- |
| Work, pure headers, Merkle roots, and hashes | DigiShield retarget, height parameters, `GetNextWorkRequired` on a checked finite view, supplied-hash target check, and 256-bit word-to-arithmetic equivalences (parallel with transactions per 0001 §10). 80-byte pure headers, double SHA-256, Merkle roots with mutation detection, SHA-1, RIPEMD-160, and Hash160 with known answers. | [docs/soundness/work.md](docs/soundness/work.md#target-validity-and-supplied-hash-proof-of-work), [docs/soundness/headers.md](docs/soundness/headers.md#pure-headers-and-transaction-merkle-roots), [docs/soundness/cryptography.md](docs/soundness/cryptography.md#sha-1) |
| Legacy Script and worked property ([0003](docs/design/0003-legacy-spend-validation.md), stages 1–5, §7) | Instruction reader, `CScriptNum`, `EvalScript`, signature code, encoding checks, signature and lock-time opcodes, `VerifyScript` with P2SH, and `verifyLegacySpend` with parameterized checker (`coreVerifier`). `multisigRecovery_sound` and converses cover `1 ≤ k ≤ n ≤ 16` (at most 13 33-byte keys under P2SH 520-byte limit). Oracle exposes `script.read_op`, `script.eval`, and `script.verify_legacy`. | [docs/soundness/script.md](docs/soundness/script.md#script-worked-property-multisig-with-recovery), [docs/comparison-evidence.md](docs/comparison-evidence.md#the-comparison) |
| Header proof of work ([0004](docs/design/0004-header-proof-of-work.md), stages 0–5) | HMAC-SHA-256, PBKDF2, RFC 7914 scrypt model, and Dogecoin scrypt (`powHash_eq_spec` on 80-byte inputs). Full headers with AuxPoW, `CAuxPow::check`, `CheckAuxPowProofOfWork`, `CheckBlockHeader`, and version gates. Core harness reconstructs 26 payloads byte for byte, checks 321 historical headers, and re-mines 12 `auxpow_pow` cases including in-memory mismatches. | [docs/soundness/headers.md](docs/soundness/headers.md#header-proof-of-work), [docs/comparison-evidence.md](docs/comparison-evidence.md#header-proof-of-work-evidence) |
| Signature verifier ([0005](docs/design/0005-signature-verifier.md), stages 1–4) | EthLib secp256k1 and ECDSA adaptation with Wycheproof vectors, Core's public-key parser, and `coreVerifier` (`CPubKey::Verify`). Oracle agrees with Core on 598 `pubkey.verify` inputs, Script and transaction corpora, and 25 Core-signed recovery spends. Agreement of `Point.mulAdd` with `secp256k1_ecmult` is finite comparison evidence, with no all-input theorem. | [docs/soundness/cryptography.md](docs/soundness/cryptography.md#secp256k1-public-key-parser-and-cores-verifier) |
| Contextual header validation ([0006](docs/design/0006-contextual-header-validation.md), stages 1 to 4, adopted 2026-11-07, 9 decisions) | `Work.MedianTimePast` on a checked view with depth requirement, `Block.ContextualParams` (heights and checkpoints), and `Block.ContextualCheck` (section 11 theorems, five mainnet ranges, synthetic views). `block.contextual_check` calls Core's `ContextualCheckBlockHeader` on an in-memory index (fixture expectations, boundaries, seed `20261109` mutations, comparator self-tests). | [docs/soundness/headers.md](docs/soundness/headers.md#contextual-header-validation), [docs/comparison-evidence.md](docs/comparison-evidence.md#contextual-header-comparison-evidence) |
| Proposed revisions framework and examples ([0007](docs/design/0007-proposed-revisions.md), stages 1 to 2, adopted 2026-11-07, decisions 1 to 10 accepted, 11 deferred) | `Proposals` and `ProposalProofs`, import check and self-test, and `DogeLib.Proposals.Framework` (section 11 targets except `checkBlockHeader_not_versionBitsCondition` per decision 11), plus [docs/in-practice.md](docs/in-practice.md). `ExampleVersionVerify` (section 10.3 targets and known answers) and deliberately faulty `ExampleFaultyLocktime` (false soft-fork claim refuted, corrected variant proved `SoftFork`) live in test-only `ProposalExamples` (`tests/ProposalExamples/`) with `proposal-test-oracle` (#200) as permanent framework tests. `dogelib-proposal-oracle` names only proposed revisions. | [docs/soundness/proposals.md](docs/soundness/proposals.md#proposed-revisions-the-framework), [COVERAGE.md](COVERAGE.md#proposed-revisions) |
| Header-sequence validation ([0008](docs/design/0008-header-sequence-validation.md), stages 1 to 5, adopted 2026-11-07, all §13 decisions) | Explicit block-index model (`Block.HeaderSequence`), `ancestorView_congr`, `lastCheckpointInIndex_eq`, and `acceptBlockHeader` (section 11 targets, with `accept_genesis_known`, `accept_genesis_insert`, `accept_genesis_parent` per §13.1). `processNewBlockHeaders` (`process_linear`, section 11 targets, `process_complete` taking `n ≤ 2147483647` on an empty index per §13.2), `Work.blockProof` (`blockProof_eq`), and `IndexEntry.chainWork` (`chainWork_add`). Known answers cover 34 regtest cases, 11 compact values, and mainnet ranges. `block.header_sequence` calls Core's `AcceptBlockHeader` on an in-memory index (seeded mutations, self-tests). | [docs/soundness/headers.md](docs/soundness/headers.md#the-sequence-processnewblockheaders), [docs/comparison-evidence.md](docs/comparison-evidence.md#header-sequence-comparison-evidence) |
| Bug-finding campaign ([0009](docs/design/0009-bug-finding-campaign.md), stages 1 to 5, adopted 2026-11-08, all §14 decisions) | `scripts/campaign.py`, `core-signer` request mode, two-mode generator for multisig-with-recovery, properties Q1 to Q7, reducer (`campaign.py reduce`), and `proposal-replay` search (`51 00 b3` minimal faulty violation, zero for corrected). L1 and L3 replay label M3 `harness-fault` (upstream `1.14-maint` matched pin on 2026-11-08), with regression fixtures and CI run at reviewed seed. All five §11 theorems are proved (`multisigRecovery_lockTime_ge_threshold`, `multisigRecovery_finalSequence`, `legacySignatureHashPlan_eq_of_none_anyoneCanPay`, `legacySignatureHashPlan_eq_of_single_anyoneCanPay`, `faulty_counterexample_short`). Found no fault in Core or DogeLib. | [docs/campaign.md](docs/campaign.md#campaign-runs-and-replay), [COVERAGE.md](COVERAGE.md#campaign-infrastructure), [COVERAGE.md](COVERAGE.md#production-replay-of-campaign-candidates), [COVERAGE.md](COVERAGE.md#campaign-regression-fixtures) |
| Relative lock time ([0012](docs/design/0012-relative-lock-time.md), stages 1 to 4, adopted 2026-11-20) | `RelativeLockTime` specifies BIP 113 cutoff, BIP 112 CSV flag, and BIP 68 sequence locks at a fixed activation height (not part of baseline, no position on activation). Extensions E1 to E4, `connectChainWith_restricts`, block-level `relativeLockTime_softFork` on supplied state, `relativeLock_enforced`, and known answers. The comparison runs Core's code with the CSV state forced to `ACTIVE` on made blocks and mainnet heights 0 to 10,000 (a state never reached on mainnet, `csv_never_lockedIn`). Historical impact runs (#201) record zero candidates, changed blocks, or unsupported results on heights 0 to 145,000, short range, S, and configured ranges (CI runs 0 to 10,000). | [COVERAGE.md](COVERAGE.md#proposed-revisions), [docs/comparison-evidence.md](docs/comparison-evidence.md#historical-impact-runs) |
| Kernel replay (#198, #206) | `scripts/replay.sh` requires the kernel to reject a planted unchecked theorem and the planted forged inductive type of Lean issue 16730. It replays each module of `DogeLib` and `ProposalExamples` into Lean's kernel on pushes to `main` and weekly (`Refinement/` is not replayed). Each stored constant must equal the replayed one. | [SOUNDNESS.md](SOUNDNESS.md#c3-declarations-the-kernel-did-not-check), [BUILDING.md](BUILDING.md#kernel-replay) |

## Next work

### Block validity

Stages 0010a and 0010b define the checks of a block in its context, through `ConnectBlock`.
Stage 0010c proves three properties of `connectBlock`.
[Design record 0010](docs/design/0010-block-validity.md) defines the milestone. The maintainer adopted it on 2026-11-13.

| Stage | Deliverable | Status |
| --- | --- | --- |
| 0 | The harness compiles Core's `src/validation.cpp`. `block.contextual_check` and `block.header_sequence` call Core's own functions. | Implemented |
| 0010a | Block checks without coins: `CheckTransaction`, `CheckBlock`, `ContextualCheckBlock`, the subsidy and the version-bits state, compared with Core on two mainnet ranges and on mutations | Implemented. `block.subsidy`, `tx.check`, `block.check` and `block.contextual_check_body` agree with Core on mutations for each reachable reject reason ([COVERAGE.md](COVERAGE.md#operations)). `block.check` and `block.contextual_check_body` agree on 11,018 real mainnet blocks: heights 0 to 10,000, the 1,000 blocks from 6,455,302, and 17 blocks at and next to the rule changes ([fixtures](tests/block/mainnet-blocks/README.md)). The version-bits walk agrees with Core on the mainnet header chain through the CSV window, in a run outside CI. `csv_never_lockedIn` and `versionBits_shortcut` justify the `FAILED` seed of decision 3. |
| 0010b | Block connection: the coin set, `ConnectBlock` and `block.validate`, replayed with Core | Part 1 implemented. `block.validate` agrees with Core on mutations for each reachable reject reason of `ConnectBlock`, and on a replay of mainnet heights 0 to 10,000 from the empty coin set, with the digests of each block's coin changes and of the whole set ([COVERAGE.md](COVERAGE.md#operations)). One recorded run outside CI replays heights 0 to 145,000 with the same agreement ([evidence](docs/comparison-evidence.md#replay-of-mainnet-to-height-145000)). `connect_fits` gives the arithmetic domain. Open: the recent range. Decision 5 of [design record 0011](docs/design/0011-mainnet-ranges.md) replaces exit condition 2 of this stage. The coins of the recent range come from a coin-set snapshot, and the fetch tool is not built. Exit condition 2 of stage 1 of that record plants faults in a snapshot. They take the place of the planted faults of the fetch tool. Stage 3 of that record closes the recent range |
| 0010c | Properties of connection: available spends, the value bound and the issuance bound | Proved: `connect_spends_available`, `connect_value_bound` and `chain_issuance_bound`, with the invariant `connect_valuesInRange` ([soundness](docs/soundness/blocks.md#connect_spends_available-each-input-spends-a-present-coin)). The first has the added hypothesis that the block's hash is not the genesis hash. It also has the added conclusion that the outpoints of one transaction are pairwise different. `lake test` pins the total value on a chain of two blocks. The replay of heights 0 to 10,000 compares the total value with Core at each multiple of 1,000. It also checks the total against the sum of the subsidies ([oracle](docs/oracle.md#total-value)) |

### Mainnet replay above height 145,000

[Design record 0011](docs/design/0011-mainnet-ranges.md) defines the replay of mainnet ranges above height 145,000 from coin-set snapshots.
The maintainer adopted it on 2026-11-20, with all 14 decisions of its section 13.
Its section 11 gives the stages and their exit conditions:

| Stage | Deliverable | Status |
| --- | --- | --- |
| 0 | Measurements: the size of the chain, the coins at the tip, and whether the Core pass fits the machine | Done. The tip has 202,470,869 coins, and the chain has about 179.5 GB of blocks and 0.76 billion inputs. The pass fits the disk. The stage selects `CCoinsViewDB` in the place of the harness's map for the pass ([measurements](docs/comparison-evidence.md#measurements-for-the-core-pass)) |
| 1 | The snapshot format `dogelib-coins/1`, `coins_file` in both programs, the theorem target `validateBlock_restrict`, and the self-test range below height 145,000 | Done. `validateBlock_restrict` is proved. Core writes the snapshots at heights 100,000 and 145,000, and the second has the digest of the recorded replay. Range S, heights 100,001 to 101,000, agrees from the snapshot, and every changed snapshot fails. CI runs the short form on heights 9,001 to 10,000 ([recorded run](docs/comparison-evidence.md#ranges-from-a-snapshot)) |
| 2 | The Core pass to height 5,050,000, with the version-bits walk in the harness, and the ranges A, B, C, D, F and H | Done. The pass reached height 6,465,793 with every checkpoint, and the trap build found no overflow. There its `hash_serialized`, `transactions` and coins equal the node's `gettxoutsetinfo` (decision 7). The states of the CSV window agree with both full walks. The six ranges agree from the pass's snapshots under section 3.4, and their hash lists are committed. The pass wrote the snapshot of range G at 6,455,301 ([recorded runs](docs/comparison-evidence.md#the-recorded-core-pass)) |
| 3 | The recent range from the snapshot at 6,455,301, and its run in CI with restricted coins. It closes stage 0010b | The reusable tooling and its short self-test are implemented. The recent-range run and range-specific evidence are deferred. |
| 4 | The CSV window in the oracle: a version in each `chain` entry, and the ranges E1 and E2 | Implemented. `block.validate` takes a version in each `chain` entry and `version_bits_heights` in both programs, and walks the CSV state in the case-3 gap. `versionBitsWalk_reset` and `versionBitsStateFull_of_reset` link the walk to the full walk, and the adapter's boundaries are a comparison gap ([docs/soundness/blocks.md](docs/soundness/blocks.md#version-bits)). E1 is heights 1,198,520 to 1,200,519, around the first block with `STARTED` in the Core pass (1,199,520). E2 is heights 1,702,520 to 1,704,519, around the first block with `FAILED` (1,703,520). Done. A second Core pass from the snapshot of range D reached each digest of the first pass in its heights, and wrote the snapshots at 1,198,519 and 1,702,519. Both ranges agree under section 3.4, and both programs report `DEFINED` and `STARTED` in E1, and `STARTED` and `FAILED` in E2 ([recorded runs](docs/comparison-evidence.md#the-csv-window-ranges-e1-and-e2)) |
| 5 | The conformance corpus: the format document, the range requests, the expected results and the checker | Implemented for the short range and the ranges A to F, E1, E2 and H. [docs/conformance.md](docs/conformance.md) defines the formats. On each range the oracle and the Core harness agree on every block record and on both digests of the restricted set. The harness's results are committed. The checker passes on both results files and fails on each planted fault. CI runs the short range and range D from the released assets. Condition 4 is done, with one caveat: an AI agent ran it, not a person. The agent had no prior access to the repository. Its own driver of the harness passed the checker on the short range and range D. Its own validator passed it on the short range. The maintainer's orchestrating agent downloaded the assets for it, so the run does not test the download. Stage 3's range run is deferred, so condition 5 covers only these two ranges ([recorded runs](docs/comparison-evidence.md#the-conformance-corpus)) |
| 6 | The historical impact of a proposed revision: `connectBlockWith`, the `ProposalExports` executable, and the self-test with the two examples | Part 1 implemented: exit conditions 1 to 3. `connectBlockWith` and `validateBlockWith` are in `DogeLib.Proposals.Framework.Block`, with the four theorem targets of section 10.1 proved. `dogelib-proposal-oracle` answers `block.validate` with `revision`, and without it writes the bytes of `dogelib-oracle` on the requests of the full comparison. The import check covers `ProposalExports`. [Evidence](COVERAGE.md#proposed-revisions). The runs of conditions 4 and 5 are recorded. Before pull request #200, both examples ran on the short range, S and the configured ranges of design record 0011. They ran with no activation height and from height 0. Each candidate list was committed before its runs, and no block changed. COVERAGE.md records each report with the label of section 10.4 ([recorded runs](docs/comparison-evidence.md#historical-impact-runs)) |

Adoption of the record establishes no result.
Each stage reports its evidence in COVERAGE.md and SOUNDNESS.md when it merges.

[Design record 0013](docs/design/0013-rejection-paths.md) is proposed and not adopted: a generated search of the rejection paths of the block operations against Core, and negative conformance vectors.

One other candidate is unscheduled, and it needs an approved scope before work starts:

- **Arithmetic agreement with Core's verifier.** A Lean proof that `Point.mulAdd` computes Core's `secp256k1_ecmult` result ([design record 0005](docs/design/0005-signature-verifier.md), section 4.3).
  The proof needs Mathlib, so it requires a package proposal first.

## Milestones

Historical milestones A to D come from [design record 0001](docs/design/0001-initial-handoff.md) and landed in [0.1.0](docs/release-notes/0.1.0.md):

| Milestone | Contract and qualifiers | Reference |
| --- | --- | --- |
| A: small byte codec (steps 0, 0b, 2) | Bounded CompactSize reader separate from generic canonical `Codec UInt64`: succeeds iff generic decode succeeds with value at most `0x02000000`. Input `fe 01 00 00 02` (`0x02000001`) distinguishes them. Do not replace the decoder inside an unconditional `Codec UInt64` instance while keeping its old laws. | [design record 0001](docs/design/0001-initial-handoff.md#4-milestone-a-prove-a-small-byte-codec), [docs/soundness/serialization.md](docs/soundness/serialization.md#compactsize) |
| B: transaction encoding, legacy signing, and oracle (steps 3–4) | Raw fields preserved without validation, base/no-witness prefix and complete-input forms separated, and `LegacyHashPlan` separating preimage construction from hashing. `dogelib-oracle` exposes transactions, pure headers, Merkle roots, RIPEMD-160, Hash160, SHA-1, work, and Script for Core harness comparison in CI. | [docs/oracle.md](docs/oracle.md), [docs/core-harness.md](docs/core-harness.md#the-core-harness), [docs/comparison-evidence.md](docs/comparison-evidence.md#the-comparison) |
| C: implementation equivalence (step 5) | `legacySignatureHashPlan_eq_reference` proves field-by-field preimage construction equal to the `SignatureHashOld` transformation for every input index and hash type. The theorem requires fully parsed script code and fewer than 2^32 inputs and outputs. The implementation builds the whole preimage as a byte list before hashing. An incremental sink is later work. | [docs/soundness/transactions.md](docs/soundness/transactions.md#legacy-signature-hash-transformation-reference) |
| D: Rust refinement path (step 6, #51) | Bounded Rust CompactSize decoder in `Refinement/Rust/` and extracted Aeneas model in `Refinement/Refinement/Rust/`. `decode_refines` proves complete-result agreement with `decodeBounded` on Rust-representable slices, within stated extraction boundaries. | [docs/soundness/serialization.md](docs/soundness/serialization.md#rust-bounded-compactsize-reader), [Refinement/Rust/README.md](Refinement/Rust/README.md), [COVERAGE.md](COVERAGE.md#operations) |

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
