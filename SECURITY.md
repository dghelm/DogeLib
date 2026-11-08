# Security policy

This policy covers two kinds of problem:

- A defect in DogeLib itself, such as a false theorem statement or a gap in the trust policy.
  An oracle that reports a wrong result, or a harness that hides a disagreement with Dogecoin Core, is also a defect.
- A suspected vulnerability in Dogecoin Core that DogeLib work found.
  It can come from a bug-finding campaign under [design record 0009](docs/design/0009-bug-finding-campaign.md), or from a disagreement between the specification and Core.

## Supported versions

DogeLib is in its 0.x releases. Fixes go to `main` and to the next release. Older releases get no fixes.

## Report a problem privately

Report privately first. Do not open a public issue, pull request or discussion for a problem that someone could exploit.

1. Use GitHub's private vulnerability reporting for this repository. Open the **Security** tab and choose **Report a vulnerability**.
2. If you cannot use GitHub, email `daniel@dogeos.com`.

Give the DogeLib revision, the commands you ran, what you expected and what happened. Include the smallest input that reproduces the problem, if you have one.

## A suspected vulnerability in Dogecoin Core

A disagreement between DogeLib and Core is a candidate, not a finding. The cause can be in the Lean model, in the Core harness, in a missing caller precondition, or in Core. Section 9 of design record 0009 says how a candidate becomes a finding:

1. Replay it through Core's production code.
2. Check it against the current upstream revision.

For such a candidate:

- Do not publish the input, an exploit or a description of its effect in this repository, an issue, a pull request or a CI log.
- Tell the DogeLib maintainer privately, through one of the channels above.
- Keep the saved failure in the uncommitted `build/campaign/` directory.
- Report a confirmed vulnerability in Core through the process in [Dogecoin Core's SECURITY.md](https://github.com/dogecoin/dogecoin/blob/master/SECURITY.md) at its current revision.
- Add a regression fixture or a public description only after the report is resolved.

Run a campaign with a fresh seed on your own machine, never in CI.
CI runs only fixed seeds whose results a person has already reviewed, so a public CI log never shows a first candidate.

These rules take precedence over the rule in [CONTRIBUTING.md](CONTRIBUTING.md#sources-of-truth) that records a minimal reproducer in SOURCES.md, until the report is resolved.
