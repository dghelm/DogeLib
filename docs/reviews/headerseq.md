# Model read: Contextual header validation and header sequences

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Block/{ContextualCheck,ContextualParams,HeaderSequence}.lean`, the Core validation, index, parameter and work functions that the [brief](briefs/headerseq.md) names, and `harness/core/core_oracle.cpp`.

## Result

The read found no discrepancy within the documented input domains.
Confidence is moderate to high for the compared control flow, constants and state changes, from a review of the source.
This read does not establish equivalence with compiled Core.

## Findings

None.

## Checked and agreeing

Lean file names below are under `DogeLib/Block/` unless another directory appears.
Core paths are relative to `src/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `chainparams.cpp:494–506`, parameter records at `78–141`, `232–306`, `388–437` | `ContextualParams.lean:59`, `contextualTree:95`, `getContextualParams:108` | Network values, copies, activation heights and tree search agree. |
| `chainparams.cpp:180–205`, `340–361`, `461–464` | `ContextualParams.lean:135` | All 43 checkpoint height/hash pairs agree. |
| `checkpoints.cpp:18–30`, `validation.cpp:3093–3100` | `ContextualParams.lean:200`, `HeaderSequence.lean:225` | Reverse table search. Index variant returns the found entry's height. |
| `primitives/pureheader.h:73–95`, `129–155` | `ContextualCheck.lean:78`, `:86`, `VersionGate.lean:71` | Unsigned time widening, signed remainder, AuxPoW and legacy tests agree. |
| `validation.cpp:3072–3100` | `ContextualCheck.lean:173`, `:178`, `:208` | Version gates precede raw `nBits` equality and checkpoint comparison. Checkpoint equality passes. |
| `validation.cpp:3103–3116` | `ContextualCheck.lean:185`, `:190`, `:195` | Median equality fails. Future-time equality passes. BIP65/66 use inclusive heights. |
| `chain.h:284–298` | `DogeLib/Work/MedianTimePast.lean:75` | At most 11 timestamps, sorted upper median. Required history is explicit. |
| `pow.cpp:32–88`, `dogecoin.cpp:26–87` | `DogeLib/Work/NextWork.lean:108`, `:143`, `Retarget.lean:162` | Candidate-height parameters, previous-height switches, lookbacks and retarget arithmetic agree. |
| `validation.cpp:2927–2937`, `dogecoin.cpp:89–125` | `ProofOfWork.lean:212`, `:237` | Height-zero parameters, proof-of-work branch order and `high-hash` mapping agree. |
| `validation.cpp:3212–3239` | `HeaderSequence.lean:485` | Genesis bypass, duplicate handling, PoW, predecessor lookup and contextual checks agree. |
| `chain.h:309–314`, `validation.cpp:3241–3256` | `HeaderSequence.lean:254`, `:408`, `:416`, `:434` | Failure masks, script-validity bypass, ancestor search and child marks agree for corresponding visit order. |
| `chain.cpp:113–147` | `HeaderSequence.lean:378` | Linear predecessor walk gives the same reachable ancestor as skip pointers. Anchor behavior is documented. |
| `chain.cpp:150–163`, `validation.cpp:2755–2788` | `DogeLib/Work/ChainWork.lean:64`, `HeaderSequence.lean:458` | Compact-target work, modulo-2²⁵⁶ addition and new-entry flags agree within documented exclusions. |
| `validation.cpp:3270–3286` | `HeaderSequence.lean:547`, `:568`, `:581` | First failure stops the sequence. Earlier insertions and failure marks remain. Empty success and composition agree with the stated projection. |
| `consensus/validation.h:13–19`, `35–53`, validation rejection sites above | `ContextualCheck.lean:150`, `HeaderSequence.lean:270`, `:280`, `:308`, `:316`, `:326` | Reject reasons, codes and added DoS scores agree. |

The differences of the harness from `validation.cpp` are deliberate.
`core_oracle.cpp:439–462` returns reasons instead of validation state.
Lines `493–506` guard anchor walks.
Lines `520–690` use one adjusted time and the order of failed blocks that the request defines.
They omit node bookkeeping, apply the adapter's preflight, and search before insertion under the documented fixed-point convention.
They also clear `last_hash` on rejection.

Core samples the time in each contextual call, and preserves the caller's previous `ppindex` after a later failure in the sequence.
The declared model states those projections.

A read-only source comparison with `python3 -I -` confirmed 23 mainnet checkpoint pairs, 19 testnet pairs and one regtest pair at the stated revisions.

## Not checked

- The implementations of the cryptographic primitives and the internals of `CAuxPow::check`. The read compared their call sites and branch order.
- Node bookkeeping that the declared model omits, such as best-header selection, dirty sets and notifications.
- Builds: **not run**, as the brief requested.
- Differential execution, fixtures, declaration checks, refinement, writing checks and all other repository gates: **not run**.
