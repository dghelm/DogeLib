module

public import DogeLib.Proposals.ExampleFaultyLocktime
public import DogeLib.Proposals.ExampleVersionVerify
public import DogeLib.Proposals.Framework.Activation
public import DogeLib.Proposals.Framework.Compatibility
public import DogeLib.Proposals.Framework.Script

/-!
# `DogeLib.Proposals`

Root of the `Proposals` Lake library: proposed revisions of the baseline, and the framework that states them.
Design record 0007 sets the contract.

A proposed revision is behaviour intentionally different from the baseline, the specification of Dogecoin Core at the pin in SOURCES.md.
No module of the `DogeLib`, `Proofs` or `Exports` libraries imports this library.
`scripts/CheckRefinementImports.lean` checks that boundary.

- `DogeLib.Proposals.Framework.Script` holds the Script loop with the instruction step as a parameter, and the restriction relation.
- `DogeLib.Proposals.Framework.Activation` holds the activation model.
- `DogeLib.Proposals.Framework.Compatibility` holds the compatibility classes and the legacy projection.
- `DogeLib.Proposals.ExampleFaultyLocktime` is an invented proposal with a deliberate fault, and its corrected variant. It is a teaching example and a test of the framework, not a proposal for Dogecoin.
- `DogeLib.Proposals.ExampleVersionVerify` is the worked example of design record 0007, section 10. It is not a proposal for Dogecoin.

The library has no proposal for Dogecoin.
A proposal lives under `DogeLib.Proposals.<Name>`, and this root imports it.
-/
