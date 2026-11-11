# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.

It specifies part of Dogecoin's consensus behavior: serialization, hashes, header proof of work, header acceptance, and legacy Script verification of one transaction input.
It does not specify transaction, block or chain validity, so it cannot decide whether a block is valid.
It states a proposed protocol revision as a named change against that baseline.
One theorem relates an implementation in another language to the specification: `decode_refines`, for a Rust CompactSize reader.

## Review status

The repository records no line-by-line comparison by a person of a Lean definition with the source code of Dogecoin Core.
AI models wrote the definitions from the pinned source, and the recorded reviews of the pull requests are by AI models.
Three kinds of evidence connect the definitions to Core:

- The theorems, which the Lean kernel checks. A theorem about a definition that differs from Core still holds ([A1](SOUNDNESS.md#a1-a-wrong-definition)).
- The comparison with Core's code on a finite set of requests, which CI runs on every pull request ([docs/oracle.md](docs/oracle.md#the-comparison)).
- Those reviews of the pull requests.

[docs/reviews/](docs/reviews/README.md) also records seven reads of the definitions against Core's source by an AI model.
A read executes nothing, and it is not a review by a person.

## Status

DogeLib follows Dogecoin Core `v1.14.9`, commit `e0a1c15` ([SOURCES.md](SOURCES.md)).
Each item below links to its evidence.
[COVERAGE.md](COVERAGE.md#operations) gives the theorems, known answers and comparisons per operation.
[SOUNDNESS.md](SOUNDNESS.md#what-the-proofs-say) gives the hypotheses, assumptions and execution boundaries of each claim.

- **Serialization.** Fixed-width integer, byte-string and CompactSize codecs, with round trips.
  Core's bounded CompactSize and counted-list readers, with soundness and completeness against a separate relation ([CompactSize](SOUNDNESS.md#compactsize)).
  Transactions in base mode and in the witness-allowed format, as a serialization format only, with the transaction ID and witness hash ([transactions](SOUNDNESS.md#transactions)).
- **Legacy signature hash.** The hash plan for `SIGVERSION_BASE`.
  `legacySignatureHashPlan_eq_reference` proves it equal to Core's transaction-transformation reference on a stated domain ([legacy signature hash](SOUNDNESS.md#legacy-signature-hash-transformation-reference)).
- **Hashes.** SHA-256, double SHA-256, SHA-1, RIPEMD-160 and Hash160, with known answers ([SHA-1](SOUNDNESS.md#sha-1), [RIPEMD-160 and Hash160](SOUNDNESS.md#ripemd-160-and-hash160)).
  HMAC-SHA-256 and PBKDF2-HMAC-SHA-256, each proved equal to a separate list model ([HMAC](SOUNDNESS.md#hmac-sha-256), [PBKDF2](SOUNDNESS.md#pbkdf2-hmac-sha-256)).
- **Work and blocks.** The DigiShield retarget, next-work selection, the compact-target check of a supplied hash, 80-byte pure headers and transaction Merkle roots ([target validity](SOUNDNESS.md#target-validity-and-supplied-hash-proof-of-work)).
- **Header proof of work.** The work of [design record 0004](docs/design/0004-header-proof-of-work.md):
  - Dogecoin's scrypt digest of a header. `powHash_eq_spec` proves it equal to the RFC 7914 scrypt model on every 80-byte input ([scrypt digest](SOUNDNESS.md#dogecoins-scrypt-digest)).
  - Full headers with the AuxPoW payload, and `CAuxPow::check` ([full headers](SOUNDNESS.md#full-headers-and-the-auxpow-payload), [the AuxPoW check](SOUNDNESS.md#the-auxpow-check)).
  - `CheckAuxPowProofOfWork` and `CheckBlockHeader` with `fCheckPOW` true. `checkAuxPowProofOfWork_iff` characterizes acceptance for every parameter record and full header ([header proof of work](SOUNDNESS.md#header-proof-of-work)).
  - The two version gates of `ContextualCheckBlockHeader` ([version gating](SOUNDNESS.md#version-gating)).
- **Contextual header validation.** `ContextualCheckBlockHeader` on a checked view of the predecessor's chain, with the adjusted time and the last known checkpoint as inputs ([design record 0006](docs/design/0006-contextual-header-validation.md)).
  `contextualCheck_eq_ok_iff` and one theorem for each rejection give the exact result on the domain ([contextual header validation](SOUNDNESS.md#contextual-header-validation)).
- **Header sequences.** Core's `AcceptBlockHeader` and `ProcessNewBlockHeaders` over an explicit model of the block index, with the chain work of each entry ([design record 0008](docs/design/0008-header-sequence-validation.md)).
  `process_linear` gives the result for headers that extend one entry in order, under its stated hypotheses ([the sequence](SOUNDNESS.md#the-sequence-processnewblockheaders)).
- **Proposed revisions.** A framework that states a revision of the Script rules and classifies it against the baseline, for example as a `SoftFork` ([design record 0007](docs/design/0007-proposed-revisions.md)).
  It has two invented examples and no proposal for Dogecoin.
  Its compatibility theorems are Script-local: each is about one Script evaluation or one transaction input, not about the network ([the framework](SOUNDNESS.md#proposed-revisions-the-framework)).
- **Campaign.** `scripts/campaign.py` generates spends that Core signs, checks stated properties of them, reduces a failure and replays it on a regtest node ([design record 0009](docs/design/0009-bug-finding-campaign.md)).
  It found no fault in Core or in DogeLib, and its regression fixtures come from planted faults ([campaign](COVERAGE.md#campaign-infrastructure)).
- **Signatures.** The secp256k1 curve and ECDSA verification, adapted from EthLib, and Core's public-key parser and `CPubKey::Verify` as `Script.coreVerifier` ([design record 0005](docs/design/0005-signature-verifier.md)).
  Its theorems give the result of each of Core's checks, and reduce the final test to the point computation `Point.mulAdd` ([Core's verifier](SOUNDNESS.md#secp256k1-public-key-parser-and-cores-verifier)).
  No theorem proves that DogeLib's point arithmetic computes Core's `secp256k1_ecmult` result. Finite comparisons with Core are the evidence for that step.
- **Script.** The legacy Script interpreter of [design record 0003](docs/design/0003-legacy-spend-validation.md): one `EvalScript` call, `VerifyScript` with P2SH, the lock-time opcodes, and `verifyLegacySpend` for one transaction input ([Script evaluation](SOUNDNESS.md#script-evaluation-one-evalscript-call), [`VerifyScript`](SOUNDNESS.md#script-lock-times-and-verifyscript)).
  A worked property proves when a multisig-with-recovery spend is accepted, for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16` ([worked property](SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
- **Rust refinement.** `decode_refines` relates a Lean model extracted from a Rust CompactSize reader to the bounded reader ([Rust reader](SOUNDNESS.md#rust-bounded-compactsize-reader)).

Script verification takes a signature checker as a parameter.
`transactionChecker` computes the legacy signature hash and returns the answer of the verifier that its caller supplies.
With `coreVerifier` as that verifier, `lake test` runs Core's script and transaction corpora.

`lake test` also checks all 25 [signed recovery-template fixtures](tests/script/signed-spends/README.md), including each signer pair and every recorded mutation.
Their verdicts and errors agree with Core's recorded expectations, and the oracle comparison rechecks these spends with live Core.
The oracle uses `coreVerifier` for its transaction checker and exposes single-signature verification through `pubkey.verify`.

The `dogelib-oracle` program runs the specification on JSON requests, and a harness runs the pinned Core code on the same requests ([docs/oracle.md](docs/oracle.md)).
A full comparison sends 385,842 stream requests, and it passes only with zero failures.
The comparator also fails if the number of requests for any operation differs from its table ([counts](docs/oracle.md#the-comparison)).
The four transaction-reader operations receive 263,929 of the requests, Script evaluation and verification 16,975, and header sequences 257.
The total includes requests with an unsupported Lean result and 12 checked harness refusals.
The comparison counts these requests separately, as neither agreement nor disagreement.

For one operation, the harness does not run Core's function.
The version gates compare with a transcription of two branches of `src/validation.cpp`, written by hand in the harness.
Contextual header validation and header sequences run Core's own functions on a block index that the harness builds in memory ([contextual evidence](docs/oracle.md#contextual-header-comparison-evidence), [sequence evidence](docs/oracle.md#header-sequence-comparison-evidence)).

For example, Core's `script_tests.json` has 925 records with no witness and only the seven supported flags ([corpus](tests/script/corpus/README.md)).
Through `script.verify_legacy`, these records give 925 agreements with the base checker and 925 with the transaction checker.
All 159 eligible transaction inputs and 598 public-key inputs agree with Core.
For header proof of work, Core and the oracle agree on all 321 recorded mainnet headers, 207 version-gate boundaries and 1,075 seeded mutations ([header evidence](docs/oracle.md#header-proof-of-work-evidence)).
A comparison covers its requests and no other inputs.

DogeLib has no definition of transaction validity, block validity or chain validity.
It does not specify these parts of Dogecoin:

- `CheckTransaction`, `CheckBlock`, `ContextualCheckBlock` and `ConnectBlock`
- The UTXO set, value accounting and fees, the block subsidy, and the Script flags of each height
- The sources of the inputs of the contextual header check: the node's clock and peer offsets, its block index and its choice of chain
- The witness v0 signature hash, and witness script verification
- Chain selection, reorganization and the mempool

[ROADMAP.md](ROADMAP.md) records completed milestones and next work.

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
Under the hypotheses of `MultisigRecoverySpend`, `multisigRecovery_sound_coreVerifier` proves that an accepted spend of this template satisfies the ordinary branch or the recovery branch ([worked property](SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
The [verifier section](SOUNDNESS.md#secp256k1-public-key-parser-and-cores-verifier) states the step of `coreVerifier` that no theorem relates to Core.

## Documents

| Document | Contents |
| --- | --- |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution and review policy |
| [SECURITY.md](SECURITY.md) | How to report a vulnerability privately |
| [AGENTS.md](AGENTS.md) | How to work here: checks, files to update, pull requests |
| [docs/agents.md](docs/agents.md) | Optional lane worktrees for several agents at once |
| [WRITING.md](WRITING.md) | The writing standard |
| [BUILDING.md](BUILDING.md) | How to build and check the library |
| [ROADMAP.md](ROADMAP.md) | Milestones, work order, and next work |
| [ARCHITECTURE.md](ARCHITECTURE.md) | Library targets, dependency rules, and layout |
| [SOURCES.md](SOURCES.md) | Pinned reference revisions and source mappings |
| [COVERAGE.md](COVERAGE.md) | Implemented definitions, theorems, and evidence |
| [SOUNDNESS.md](SOUNDNESS.md) | Logical assumptions and trust boundaries |
| [docs/oracle.md](docs/oracle.md) | The oracle format and the Core comparison |
| [docs/in-practice.md](docs/in-practice.md) | Worked examples: vetting a proposed soft fork, a known Merkle property and reading a Core disagreement |
| [docs/release.md](docs/release.md) | How to cut a release |
| [docs/design/](docs/design/) | Frozen design records |

## License

DogeLib's own material is distributed under the MIT licence, in [LICENSE](LICENSE).
Material from other projects keeps its own licence, as each adapted file and [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects) state.
