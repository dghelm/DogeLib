# DogeLib

DogeLib is an executable formal specification and proof library for Dogecoin, written in Lean 4.

It makes existing Dogecoin consensus behavior precise, and states proposed protocol revisions as named changes against that baseline. It proves that implementations and optimizations preserve the specification.

## Status

Two primitives exist: SHA-256 and double SHA-256.
Theorems relate both to a model of FIPS 180-4, and known answers from NIST and Dogecoin Core test their compiled code.
No definition of a Dogecoin data structure, Core comparison, or Rust extraction exists yet. [COVERAGE.md](COVERAGE.md) records what is implemented, per operation and per kind of evidence.

The first release target is:

> DogeLib defines Dogecoin's base transaction encodings and legacy signing commitments, provides an executable comparison oracle, and proves a streaming commitment implementation equivalent to its specification over a documented input domain.

That sentence describes the goal, not the current state.

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

Not yet selected. See [ROADMAP.md](ROADMAP.md#open-decisions).
