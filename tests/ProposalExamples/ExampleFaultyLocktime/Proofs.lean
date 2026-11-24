module

public import ProposalExamples.ExampleFaultyLocktime.Proofs.Block
public import ProposalExamples.ExampleFaultyLocktime.Proofs.Compatibility
public import ProposalExamples.ExampleFaultyLocktime.Proofs.Witnesses

/-!
# `ProposalExamples.ExampleFaultyLocktime.Proofs`

The theorems of the example `ExampleFaultyLocktime`, an invented, deliberately faulty proposal that is not a proposal for Dogecoin.
Each theorem is Script-local, except the block-level theorems of `Proofs.Block`.

- `Proofs.Block`: the block-level theorems of design record 0011, section 10.1, for `blockRevision`.
- `Proofs.Compatibility`: the step, the inactive equality of both variants, and restriction of acceptance for the corrected variant.
- `Proofs.Witnesses`: the counterexample that refutes the faulty variant's soft-fork claim, and the witnesses of the corrected variant's `SoftFork`.
-/
