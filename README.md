# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.

It makes existing Dogecoin consensus behavior precise, and states proposed protocol revisions as named changes against that baseline. It proves that implementations and optimizations preserve the specification.

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
- **Work and blocks.** The DigiShield retarget, next-work selection, the compact-target check of a supplied hash, 80-byte pure headers and transaction Merkle roots ([target validity](SOUNDNESS.md#target-validity-and-supplied-hash-proof-of-work)).
  Scrypt, AuxPoW and header validity are not specified.
- **Script.** The legacy Script interpreter of [design record 0003](docs/design/0003-legacy-spend-validation.md): one `EvalScript` call, `VerifyScript` with P2SH, the lock-time opcodes, and `verifyLegacySpend` for one transaction input ([Script evaluation](SOUNDNESS.md#script-evaluation-one-evalscript-call), [`VerifyScript`](SOUNDNESS.md#script-lock-times-and-verifyscript)).
  A worked property proves when a multisig-with-recovery spend is accepted, for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16` ([worked property](SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
- **Rust refinement.** `decode_refines` relates a Lean model extracted from a Rust CompactSize reader to the bounded reader ([Rust reader](SOUNDNESS.md#rust-bounded-compactsize-reader)).

Script verification takes a signature checker as a parameter.
`transactionChecker` returns the answer of the verifier that its caller supplies.
`Script.coreVerifier` is DogeLib's verifier: Core's `CPubKey::Verify` in Lean, with the ECDSA arithmetic adapted from EthLib ([design record 0005](docs/design/0005-signature-verifier.md)).
`lake test` runs Core's script and transaction corpora with it.
The oracle still supplies a verifier that is always unavailable, so an oracle signature check that reaches it gives `unsupported`, not a verdict ([signature opcodes and the checker](SOUNDNESS.md#script-signature-opcodes-and-the-checker)).

The `dogelib-oracle` program runs the specification on JSON requests, and a harness runs the pinned Core code on the same requests ([docs/oracle.md](docs/oracle.md)).
The recorded comparison at DogeLib `c822efa` processed 372,486 stream requests with zero failures ([counts](docs/oracle.md#the-comparison)).
That count includes requests with an unsupported Lean result and 12 checked harness refusals.
The comparison counts these requests separately, as neither agreement nor disagreement.

For example, Core's `script_tests.json` has 925 records with no witness and only the seven supported flags ([corpus](tests/script/corpus/README.md)).
Through `script.verify_legacy`, these records give 925 agreements with the base checker.
With the transaction checker, they give 881 agreements and 44 results that reach the unavailable verifier.
A comparison covers its requests and no other inputs.

DogeLib does not specify these parts of Dogecoin:

- The scrypt digest of a header, and AuxPoW
- The contextual checks of a header against chain history, and block validity
- The witness v0 signature hash, and witness script verification
- ECDSA signature verification
- Full-node validation: the UTXO set, chain selection and the mempool

[ROADMAP.md](ROADMAP.md) records completed milestones and next work.

## Documents

| Document | Contents |
| --- | --- |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution and review policy |
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
| [docs/release.md](docs/release.md) | How to cut a release |
| [docs/design/](docs/design/) | Frozen design records |

## License

DogeLib's own material is distributed under the MIT licence, in [LICENSE](LICENSE).
Material from other projects keeps its own licence, as each adapted file and [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects) state.
