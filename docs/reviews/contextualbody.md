# Model read: version bits and ContextualCheckBlock

- Reader: GPT-6 (Codex; exact build unavailable), an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: cc15d98 (plus the uncommitted changes of this worktree). Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `Block/{VersionBits,ContextualBody,Block,AuxPow}.lean`, `Script/Number.lean`, `Transaction/{Witness,Types}.lean`, and the specified oracle glue, against the specified Core sources.

## Result

No consensus-divergent verdict found within the documented mainnet comparison domain. I found two domain-boundary defects, an unused context-value mismatch, and a documentation error. Confidence is high for the mainnet body checks and the full version-bits walk, subject to the limits below.

## Findings

1. **Candidate height lacks Core’s signed-range check.**  
   Lean: `DogeLib/Block/Exports/Oracle.lean:334–350`. Core: `src/validation.cpp:3123`, `src/chain.h:171`.  
   `bodyStates` validates only the boundary suffix through `medianTimePast`. The predecessor can therefore exceed the safe range for Core’s `int` arithmetic. Example: a contiguous view starting at height `2147483647`, extending through boundary `2147483519` and its ten predecessors, with times below CSV’s start. Lean returns candidate height `2147483648`; Core’s predecessor-height addition overflows signed `int`. This is an unsupported-domain acceptance, not a defined Core verdict to reproduce.  
   **Severity:** domain-boundary. **Confidence:** high.

2. **The oracle passes the boundary median as the predecessor median.**  
   Lean: `DogeLib/Block/Exports/Oracle.lean:344–350`. Core: `src/validation.cpp:3134–3136`.  
   The returned `prevMtp` comes from `boundary`, rather than `chain`. For predecessor height `10090`, let heights `10080–10090` have time `200`, and the preceding boundary window have time `100`. Lean passes `100`; Core’s predecessor median is `200`. Both supplied activeness flags are false in the supported shortcut cases, so the body uses the candidate block time and verdicts agree.  
   **Severity:** domain-boundary, latent. **Confidence:** high.

3. **The generic boundary helper loses median history for periods below 11.**  
   Lean: `DogeLib/Block/VersionBits.lean:197–200`. Core: `src/chain.h:286–297`, `src/versionbits.cpp:44,65,73`.  
   `chainBoundaries` takes median samples only from the current period. Core includes predecessors across period boundaries. Example: `period = 1`, genesis-first times `[0, 1, 100]`. Lean’s third boundary median is `100`; Core’s is `1`. No `period ≥ 11` restriction is stated for this helper. The mainnet caller uses `10080`, so it is unaffected.  
   **Severity:** domain-boundary. **Confidence:** high.

4. **The cutoff documentation reverses the activation condition.**  
   Lean: `DogeLib/Block/ContextualBody.lean:21`. Core: `src/validation.cpp:3134–3136`.  
   The comment says the predecessor median is an input for the “inactive case only”. Both implementations use it only when CSV is active.  
   **Severity:** documentation-only. **Confidence:** high.

## Checked and agreeing

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `IsFinalTx`, `validation.cpp:258–269` | `ContextualBody.lean:80` | Zero locktime, threshold branch, strict `<`, exact unsigned widening, and all-final loop agree for Core-representable heights and cutoffs. |
| Candidate height and cutoff, `validation.cpp:3123–3136` | `Oracle.lean:330`; `ContextualBody.lean:169` | Null predecessor gives height 0. Supported oracle cases use candidate time correctly. Median mismatch recorded above. |
| Finality loop, `validation.cpp:3139–3143` | `ContextualBody.lean:151` | Transaction order, first failure, reason, DoS 10, code 16 agree. |
| BIP34 check, `validation.cpp:3146–3152` | `ContextualBody.lean:179` | Activation height and byte-prefix comparison agree. |
| Height serialization, `script.h:319–349,379–393,437–442` | `Number.lean:113,125`; `ContextualBody.lean:93` | Every representable mainnet BIP34 height exceeds 16. Minimal positive encoding and one-byte push length agree. |
| SegWit commitment branch, `validation.cpp:3161–3181` | `ContextualBody.lean:181` | Explicitly excluded. Timeout 0 prevents mainnet SegWit activation. Core’s nonce-size and commitment-mismatch reasons both use DoS 100/code 16. |
| Witness scan, `validation.cpp:3183–3188`; `transaction.h:371–379` | `ContextualBody.lean:107,182`; `Witness.lean:93` | Scans only `vtx`, including coinbase. A stack containing an empty item counts as witness. Reason/DoS/code agree. |
| Weight rejection, `validation.cpp:3198` | `ContextualBody.lean:183` | Strict `> 4000000`, after witness checks. Reason/DoS/code agree. |
| Weight formula, `block.cpp:43–49` | `ContextualBody.lean:98,104` | Three times base plus full is exactly Core’s formula. |
| Block/header/AuxPoW serialization, `block.h:36–47,87–90`; `auxpow.h:79–84,153–160` | `Block.lean:133,142`; `AuxPow.lean:205,210,222` | Mode propagates into the AuxPoW transaction. Full size can exceed base size even when `vtx` has no witness. |
| Transaction writer, `transaction.h:245–271` | `Witness.lean:196`; `Types.lean:92` | Marker, flag, input witnesses, field widths and serialization order agree. |
| Boundary alignment, `versionbits.cpp:31–34`; `chain.cpp:113–116` | `Oracle.lean:335`; `VersionBits.lean:197,206` | Integer alignment and complete-period truncation agree within height bounds. |
| Backward base cases, `versionbits.cpp:38–50` | `VersionBits.lean:125,143,162` | Null gives `DEFINED`. Reset below start correctly models the backward break for an uncached walk. |
| Forward transitions, `versionbits.cpp:63–100` | `VersionBits.lean:129–136` | Timeout priority, threshold equality, lock-in delay and terminal states agree. |
| Signal counting, `versionbits.cpp:78–86` | `VersionBits.lean:184,197` | Counts the complete boundary period. Mainnet count fits Core’s `int`. |
| Full fold, `versionbits.cpp:24–106` | `VersionBits.lean:143,206`; `Oracle.lean:391` | Genesis-first complete boundaries reproduce the backward/forward computation for the mainnet period. |
| Signal condition, `versionbits.cpp:153–160`; `versionbits.h:14–18` | `VersionBits.lean:60,100` | Top-three-bit test and deployment mask agree, including signed version bit patterns. |
| Mainnet parameters, `chainparams.cpp:84,96–111` | `ContextualBody.lean:68`; `VersionBits.lean:85–94` | BIP34 height, both bits/start times/timeouts, window 10080 and threshold 9576 agree. |
| Documented adapter exclusions, `validation.cpp:3149,3161` | `ContextualBody.lean:120–123,174–181` | Missing coinbase input exclusion is explicit. Reading only `ACTIVE` matches Core’s two state comparisons. |

## Not checked

- Historical CSV nonactivation: source parameters alone do not establish that mainnet never locked in. I did not inspect chain data or the cited proofs.
- Proofs, extraction, compiled behaviour and external harness construction.
- Arithmetic on serialization sizes beyond Core’s representable machine-size domain.
- All builds, tests and other execution gates were **not run**, as requested. No files were edited.

## After the read

This section is an addendum, not part of the read. The line numbers in the findings refer to the worktree at the read, before these changes.

- Finding 1 (candidate-height signed range). `bodyStates` now rejects a predecessor at height 2147483646 or above with a request error.
A candidate height outside Core's signed-`int` range is outside the operation's domain, and the comparison sends no such height.
- Finding 2 (predecessor median). The oracle passes the aligned boundary's median time as a stand-in for the predecessor's own. Both implementations read it only when CSV is active, which mainnet never reaches (`csv_never_lockedIn`).
So the body uses the block time on both sides, and the verdicts agree. The doc comment of `bodyStates` now states this.
- Finding 3 (median window below period 11). `chainBoundaries` takes its median samples from the period alone, which matches Core only when the period is at least `nMedianTimeSpan`. The mainnet window is 10,080, and the doc comment now states the restriction.
- Finding 4 (cutoff documentation). The comment of `DogeLib.Block.ContextualBody` reversed the activation condition. It now says the body reads the predecessor median only when CSV is active.

No finding is consensus-divergent. The remaining findings are domain boundaries that the stated domain excludes, and the documentation error is corrected.
