# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.

It makes existing Dogecoin consensus behavior precise, and states proposed protocol revisions as named changes against that baseline. It proves that implementations and optimizations preserve the specification.

## Status

DogeLib defines transaction serialization formats and legacy signing commitments, with proofs and known answers.
[COVERAGE.md](COVERAGE.md) records the implemented coverage, per operation and per kind of evidence.
The [Core harness](docs/oracle.md#the-core-harness) compares selected operations with the pinned Dogecoin Core libraries.
Rust refinement and full-node validation are not implemented.

The field-by-field preimage construction is proved equal to the transaction-transformation reference under the hypotheses of `legacySignatureHashPlan_eq_reference`.
The theorem requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
The implementation constructs the whole preimage as a byte list before hashing.
An incremental hash sink and measured memory or speed gains are later work ([ROADMAP.md](ROADMAP.md)).

## Documents

| Document | Contents |
| --- | --- |
| [CONTRIBUTING.md](CONTRIBUTING.md) | Contribution and review policy |
| [AGENTS.md](AGENTS.md) | How to work here, including parallel lanes in git worktrees |
| [BUILDING.md](BUILDING.md) | How to build and check the library |
| [ROADMAP.md](ROADMAP.md) | Milestones, work order, and open decisions |
| [ARCHITECTURE.md](ARCHITECTURE.md) | Library targets, dependency rules, and layout |
| [SOURCES.md](SOURCES.md) | Pinned reference revisions and source mappings |
| [COVERAGE.md](COVERAGE.md) | Implemented definitions, theorems, and evidence |
| [SOUNDNESS.md](SOUNDNESS.md) | Logical assumptions and trust boundaries |
| [docs/design/](docs/design/) | Frozen design records |

## License

DogeLib's own material is distributed under the MIT licence, in [LICENSE](LICENSE).
Material from other projects keeps its own licence, as each adapted file and [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects) state.
