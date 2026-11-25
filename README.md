# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.
It specifies selected consensus rules of Dogecoin Core `v1.14.9` (commit `e0a1c15`) and states proposed revisions apart from that baseline ([SOURCES.md](SOURCES.md)).
It also proves refinement for an extracted Lean model of a Rust CompactSize reader.
The root Lake package uses Lean core with no external dependencies, while `Refinement/` owns Aeneas and Mathlib ([BUILDING.md](BUILDING.md)).

## Review status

No human line-by-line audit of a Lean definition against Dogecoin Core source code exists.
AI models wrote the definitions from the pinned source, and AI models wrote the recorded pull-request reviews.
Three kinds of evidence connect the definitions to Core ([SOUNDNESS.md](SOUNDNESS.md)):

- **Theorems**: the Lean kernel checks every theorem. `lake exe check-decls` allows only the three standard axioms and rejects `unsafe`, `partial`, `opaque`, and compiler substitutions across all seven production roots. `scripts/replay.sh` replays every `DogeLib` and `ProposalExamples` module into Lean's kernel on pushes to `main` and weekly (`Refinement/` is not replayed). Each stored constant must equal the replayed one. A theorem about a definition that differs from Core still holds ([A1](SOUNDNESS.md#a1-a-wrong-definition)).
- **Finite comparisons**: `lake test` runs independent known answers, and `scripts/compare_core.py` compares `dogelib-oracle` with pinned Core on finite request streams in CI ([docs/comparison-evidence.md](docs/comparison-evidence.md#the-comparison)). Comparisons cover only tested inputs ([B4](SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries)).
- **Pull-request reviews**: the recorded reviews of pull requests by AI models.

[docs/reviews/README.md](docs/reviews/README.md) also records twelve AI model reads of Lean definitions against Core source.
A read executes nothing, and it is not a human audit.

## Status

DogeLib follows Dogecoin Core `v1.14.9` at commit `e0a1c15` with Lean `v4.35.0` ([SOURCES.md](SOURCES.md)).
[COVERAGE.md](COVERAGE.md#operations) gives the per-operation matrix, [docs/coverage/](docs/coverage/) holds per-area details, and [SOUNDNESS.md](SOUNDNESS.md#what-the-proofs-say) links to theorem hypotheses and boundaries.

| Purpose | Area | Implemented scope and key evidence | Detail |
| --- | --- | --- | --- |
| Existing consensus | Serialization and transactions | Fixed-width, CompactSize, and counted-list codecs and bounded readers. Base and witness wire formats, txid, wtxid, `CheckTransaction`, legacy sigops, and legacy sighash (`legacySignatureHashPlan_eq_reference` on parsed script code, `< 2^32` inputs and outputs). | [coverage](docs/coverage/serialization-and-transactions.md), [serialization](docs/soundness/serialization.md), [transactions](docs/soundness/transactions.md) |
| Existing consensus | Cryptography and signatures | SHA-1, SHA-256, double SHA-256, RIPEMD-160, Hash160, HMAC-SHA-256, PBKDF2, RFC 7914 and Dogecoin scrypt (`powHash_eq_spec`), secp256k1 ECDSA, public-key parser, and `coreVerifier`. Point arithmetic agreement with `secp256k1_ecmult` rests on finite comparison only. | [coverage](docs/coverage/cryptography.md), [soundness](docs/soundness/cryptography.md) |
| Existing consensus | Work, headers, and AuxPoW | 256-bit word models, compact targets, DigiShield retarget, next work, median time past, and block proof. Pure and full headers, Merkle roots, AuxPoW, header PoW, version gating, contextual headers, and header sequences. | [work](docs/coverage/work.md), [blocks](docs/coverage/blocks.md), [headers](docs/soundness/headers.md) |
| Existing consensus | Mainnet block validation | Mainnet subsidy (Boost 1.70.0), version bits (`csv_never_lockedIn`), block codec, `CheckBlock`, `ContextualCheckBlock`, coin sets, `CheckTxInputs`, sigop cost, `ConnectBlock`, and `validateBlock` on supplied state. Includes `connect_spends_available`, `chain_issuance_bound`, and `validateBlock_restrict`. | [coverage](docs/coverage/blocks.md), [soundness](docs/soundness/blocks.md) |
| Existing consensus | Legacy Script and campaign | Instruction reader, `CScriptNum`, `EvalScript`, encoding checks, signature and lock-time opcodes, `VerifyScript` with P2SH, `verifyLegacySpend`, and worked properties (`multisigRecovery_sound`, `SIGHASH_SINGLE` fixed digest). Differential campaign (`scripts/campaign.py`) found no fault in Core or DogeLib, and its regression fixtures come from planted faults. | [coverage](docs/coverage/script.md), [campaign](COVERAGE.md#campaign-infrastructure) |
| Proposed revisions | Framework and `RelativeLockTime` | Script and block-level proposal framework (`DogeLib.Proposals.Framework`) isolated from baseline libraries. Its compatibility theorems are Script-local or block-level: each covers one Script evaluation, one transaction input, or one block (or block connection for a list), not the network. Public proposal `RelativeLockTime` states BIP 68, BIP 112, and BIP 113. DogeLib takes no position on activation. Test-only framework examples live in `ProposalExamples` under `tests/`. | [coverage](docs/coverage/proposals.md), [soundness](docs/soundness/proposals.md) |
| Refinement and conformance | Packed codecs, Rust, and oracles | Proved packed-codec and slice-reader refinements (`Proofs`), plus Aeneas model refinement of a Rust CompactSize reader (`decode_refines` in `Refinement/`). `dogelib-oracle` (`dogelib-oracle/1`) compares against pinned Core in CI, with recorded mainnet replays and snapshot ranges. `dogelib-proposal-oracle` runs historical impact checks. | [docs/oracle.md](docs/oracle.md), [docs/comparison-evidence.md](docs/comparison-evidence.md) |

A full comparison with Core sends 389,785 stream requests, and it passes only with zero failures.
The comparator fails if the request count for any operation differs from its table ([counts](docs/comparison-evidence.md#the-comparison)).
The total includes requests with an unsupported Lean result and 12 checked harness refusals.
The comparison counts those requests separately, as neither agreement nor disagreement.

For one operation (`block.check_version`), the harness does not run Core's function.
The version gates compare with a hand transcription of two branches of `src/validation.cpp`.
Contextual header validation and header sequences run Core's own functions on an in-memory block index ([contextual evidence](docs/comparison-evidence.md#contextual-header-comparison-evidence), [sequence evidence](docs/comparison-evidence.md#header-sequence-comparison-evidence)).

DogeLib defines no chain validity and decides the validity of a block only against a supplied predecessor and coin set.
`Block.validateBlock` runs Core's five checks of a mainnet block on that supplied chain view and coin set ([docs/soundness/blocks.md](docs/soundness/blocks.md#the-coin-set-checktxinputs-and-connectblock)).
DogeLib does not specify these parts of Dogecoin:

- `ConnectBlock` and `ContextualCheckBlock` on testnet and regtest, and testnet or regtest subsidy and coinbase maturity.
- `ConnectBlock` with script-check threads, an assumed-valid block, or an active CSV state, and Core's undo data and writes.
- Node clock and peer time offsets, the node's block index, chain selection, reorganization, and the mempool.
- Witness v0 signature hashing and witness script verification.

[ROADMAP.md](ROADMAP.md) records completed milestones and open work.

## Try it

This example builds the oracle and checks the Core-signed recovery-branch spend of the [signed-spend fixtures](tests/script/signed-spends/README.md) with `coreVerifier`.
It needs [elan](BUILDING.md) and `jq`.

```bash
lake build dogelib-oracle
jq -c 'select(.id == "recovery") | {id, op: "script.verify_legacy", tx_hex, input_index,
       prevout_script_hex: .script_pubkey_hex, flags, checker: "transaction"}' \
  tests/script/signed-spends/recovery.jsonl | .lake/build/bin/dogelib-oracle
# {"id":"recovery","ok":{"result":"accepted","script_error":"OK"}}
```

Core's recorded verdict for this spend is also `OK`.
Under the hypotheses of `MultisigRecoverySpend`, `multisigRecovery_sound_coreVerifier` proves that an accepted spend of this template satisfies the ordinary branch or the recovery branch ([worked property](docs/soundness/script.md#script-worked-property-multisig-with-recovery)).
The [verifier section](docs/soundness/cryptography.md#secp256k1-public-key-parser-and-cores-verifier) states the step of `coreVerifier` that no theorem relates to Core.

## Documents

| Reader need | Document | Contents |
| --- | --- | --- |
| Scope and status | [COVERAGE.md](COVERAGE.md) | Compact status matrix with links to per-area files under `docs/coverage/` |
| Scope and status | [ROADMAP.md](ROADMAP.md) | Completed milestones, open work, and project decisions |
| Scope and status | [SOURCES.md](SOURCES.md) | Pinned reference revisions and source-to-operation mappings |
| Trust and proofs | [SOUNDNESS.md](SOUNDNESS.md) | Trust gaps A to D and index to per-area files under `docs/soundness/` |
| Trust and proofs | [docs/reviews/README.md](docs/reviews/README.md) | Twelve AI model reads against Core source (not human audits) |
| Trust and proofs | [docs/in-practice.md](docs/in-practice.md) | Worked examples: vetting a soft fork, Merkle duplication, and Core disagreements |
| Oracle and Core tests | [docs/oracle.md](docs/oracle.md) | Wire format `dogelib-oracle/1`, 36 operations, and proposal hooks |
| Oracle and Core tests | [docs/core-harness.md](docs/core-harness.md) | Core harness build, boundary contract, and comparator mechanics |
| Oracle and Core tests | [docs/comparison-evidence.md](docs/comparison-evidence.md) | Finite stream counts, mainnet replays, snapshot ranges, and impact runs |
| Oracle and Core tests | [docs/campaign.md](docs/campaign.md) | Differential campaign driver, reducer, regtest replay, and recorded results |
| Build and contribute | [BUILDING.md](BUILDING.md) | Build, check, kernel replay, Core comparison, and validation report commands |
| Build and contribute | [ARCHITECTURE.md](ARCHITECTURE.md) | Lake libraries, import boundaries, layers, and proposal contract card |
| Build and contribute | [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution and review policy |
| Build and contribute | [AGENTS.md](AGENTS.md) | Checks table, files to update, and pull-request rules |
| Build and contribute | [docs/agents.md](docs/agents.md) | Optional lane worktrees for several agents at once |
| Build and contribute | [WRITING.md](WRITING.md) | The writing standard |
| Build and contribute | [docs/release.md](docs/release.md) | Release checklist |
| Build and contribute | [SECURITY.md](SECURITY.md) | How to report a vulnerability privately |
| Background | [docs/design/](docs/design/) | Frozen design records |

## License

DogeLib's own material is distributed under the MIT licence, in [LICENSE](LICENSE).
Material from other projects keeps its own licence, as each adapted file and [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects) state.
