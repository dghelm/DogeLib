module

public import DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Compatibility
public import DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Witnesses

/-!
# `DogeLib.Proposals.ExampleFaultyLocktime.Proofs`

The theorems of the example `ExampleFaultyLocktime`, an invented, deliberately faulty proposal that is not a proposal for Dogecoin.
Each theorem is Script-local.

- `Proofs.Compatibility`: the step, the inactive equality of both variants, and restriction of acceptance for the corrected variant.
- `Proofs.Witnesses`: the counterexample that refutes the faulty variant's soft-fork claim, and the witnesses of the corrected variant's `SoftFork`.
-/
