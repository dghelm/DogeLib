module

public import DogeLib.Proposals.Framework.Proofs
public import DogeLib.Proposals.RelativeLockTime.Proofs

/-!
# `DogeLib.Proposals.Proofs`

Root of the `ProposalProofs` Lake library: imports the proofs of the framework and of every proposed revision.
`lake exe check-decls` imports this module, so a proof tree that it leaves out is not checked.
-/
