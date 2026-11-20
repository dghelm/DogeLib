module

public import DogeLib.Proposals.Exports.Validate

/-!
# `DogeLib.Proposals.Exports`

Root of the `ProposalExports` Lake library: the operations of the proposal executable, `dogelib-proposal-oracle`.
Design record 0011, decision 10, adds the library. It may import `Proposals`, `Exports` and `DogeLib`.
No baseline library imports it, and `scripts/CheckRefinementImports.lean` checks that boundary.

`DogeLib.Proposals.Exports.Validate` holds every definition, also the entry point `run`.
`scripts/ProposalOracle.lean` names `run` as `main`. It is outside this library, because `DogeLib.Exports.Main` declares `main` too, and `lake exe check-decls` loads both export libraries in one environment.
-/
