module

public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Characterization
public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Compatibility
public import DogeLib.Proposals.ExampleVersionVerify.Proofs.Witnesses

/-!
# `DogeLib.Proposals.ExampleVersionVerify.Proofs`

The theorems of the worked example `ExampleVersionVerify`, which is not a proposal for Dogecoin.
Each theorem is Script-local.

- `Proofs.Compatibility`: the step, the inactive equality, restriction of acceptance, agreement on scripts without `OP_NOP10`, and the legacy projection.
- `Proofs.Characterization`: when the active revision accepts a script that pushes an operand and then runs `OP_NOP10`.
- `Proofs.Witnesses`: the strictness and use witnesses, and the framework's `SoftFork` for the spend predicate.
-/
