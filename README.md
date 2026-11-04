# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.

It makes existing Dogecoin consensus behavior precise, and states proposed protocol revisions as named changes against that baseline. It proves that implementations and optimizations preserve the specification.

## Status

DogeLib defines transaction serialization formats, legacy signing commitments and proof-of-work arithmetic, with proofs and known answers.
The bounded CompactSize reader has a refinement proof for a Lean model extracted from Rust.
Full-node validation is not implemented.

[COVERAGE.md](COVERAGE.md) records the detailed evidence per operation.
[SOUNDNESS.md](SOUNDNESS.md) explains theorem hypotheses, assumptions and execution boundaries, including extraction trust.
The [Core harness](docs/oracle.md#the-core-harness) compares selected operations with the pinned Dogecoin Core libraries.
[ROADMAP.md](ROADMAP.md) records completed milestones and next work.

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
