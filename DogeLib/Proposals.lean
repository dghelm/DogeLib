module

public import DogeLib.Proposals.Framework.Activation
public import DogeLib.Proposals.Framework.Block
public import DogeLib.Proposals.Framework.Compatibility
public import DogeLib.Proposals.Framework.Script
public import DogeLib.Proposals.RelativeLockTime

/-!
# `DogeLib.Proposals`

Root of the `Proposals` Lake library: proposed revisions of the baseline, and the framework that states them.
Design record 0007 sets the contract.

A proposed revision is behaviour intentionally different from the baseline, the specification of Dogecoin Core at the pin in SOURCES.md.
No module of the `DogeLib`, `Proofs` or `Exports` libraries imports this library.
`scripts/CheckRefinementImports.lean` checks that boundary.

- `DogeLib.Proposals.Framework.Script` holds the Script loop with the instruction step as a parameter, and the restriction relation.
- `DogeLib.Proposals.Framework.Activation` holds the activation model.
- `DogeLib.Proposals.Framework.Block` holds `connectBlockWith` and `validateBlockWith`: block connection and block validation with the parts that a revision changes as parameters (design record 0011, section 10.1, and design record 0012, section 6.3).
- `DogeLib.Proposals.Framework.Compatibility` holds the compatibility classes and the legacy projection.
- `DogeLib.Proposals.RelativeLockTime` is the revision of design record 0012: the rules of BIP 68, BIP 112 and BIP 113, which discussion 3509 of `dogecoin/dogecoin` proposed for Dogecoin.

A proposal lives under `DogeLib.Proposals.<Name>`, and this root imports it.
The library states a proposal. It does not argue for or against its activation.

The library holds only proposed revisions. The two examples of the framework, `ExampleFaultyLocktime` and `ExampleVersionVerify`, are in the test-only `ProposalExamples` library under `tests/`, which no production library imports.
-/
