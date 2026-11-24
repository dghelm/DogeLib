module

public import ProposalExamples.ExampleVersionVerify.Proofs.Block
public import ProposalExamples.ExampleVersionVerify.Proofs.Characterization
public import ProposalExamples.ExampleVersionVerify.Proofs.Compatibility
public import ProposalExamples.ExampleVersionVerify.Proofs.Witnesses

/-!
# `ProposalExamples.ExampleVersionVerify.Proofs`

The theorems of the worked example `ExampleVersionVerify`, which is not a proposal for Dogecoin.
Each theorem is Script-local, except the block-level theorems of `Proofs.Block`.

- `Proofs.Block`: the block-level theorems of design record 0011, section 10.1, for `blockRevision`.
- `Proofs.Compatibility`: the step, the inactive equality, restriction of acceptance, agreement on scripts without `OP_NOP10`, and the legacy projection.
- `Proofs.Characterization`: when the active revision accepts a script that pushes an operand and then runs `OP_NOP10`.
- `Proofs.Witnesses`: the strictness and use witnesses, and the framework's `SoftFork` for the spend predicate.
-/
