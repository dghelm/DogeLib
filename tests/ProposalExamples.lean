module

public import ProposalExamples.ExampleFaultyLocktime
public import ProposalExamples.ExampleVersionVerify

/-!
# `ProposalExamples`

Root of the test-only `ProposalExamples` Lake library: the two examples of the framework of design record 0007.
Neither is a proposal for Dogecoin, and no production library imports this library.
`scripts/CheckRefinementImports.lean` checks that boundary.

The examples are negative and positive tests of the framework.
`ExampleFaultyLocktime` has a deliberate fault, which the compatibility classification and the campaign proposal search must catch, and a corrected variant.
`ExampleVersionVerify` is the worked example of design record 0007, section 10: a Script-local soft fork that the framework states and proves.

- `ProposalExamples.ExampleFaultyLocktime` is an invented proposal with a deliberate fault, and its corrected variant.
- `ProposalExamples.ExampleVersionVerify` is the worked example.
- `ProposalExamples.Proofs` imports the theorems of both.
- `ProposalExamples.Exports` gives the test executable `proposal-test-oracle`: the operations of `dogelib-proposal-oracle` with both examples added to its revisions.
-/
