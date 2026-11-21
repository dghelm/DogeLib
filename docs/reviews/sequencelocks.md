# Model read: the sequence locks of BIP 68

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-20
- DogeLib: 58a30eb. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Proposals/RelativeLockTime/SequenceLocks.lean`, `RelativeLockTime.lean`, `Exports/Validate.lean`, `Framework/Block.lean`, and the specified dependencies. Core’s specified functions, types, constants and coin updates.

## Result

Found one documentation-only discrepancy and no verdict discrepancy inside the declared domain. Confidence is high from source inspection, including arithmetic bounds and executable context propagation. This is not an equivalence proof.

## Findings

1. **The height-bound explanation overlooks the intermediate addition.**  
   Lean: `DogeLib/Proposals/RelativeLockTime/SequenceLocks.lean:50`. Core: `src/validation.cpp:364`.  
   For `c = 2147418113 = 2^31 − 65535` and sequence `0x0000ffff`, the mathematical result `c + 65535 − 1 = 2147483647` **fits** `int`. Core instead overflows at the intermediate addition `c + 65535 = 2147483648`, before subtraction. The exclusion is justified, but its stated explanation is inaccurate at equality. No executable change is needed.
   **Severity:** documentation-only. **Confidence:** high.

## Checked and agreeing

Lean paths below are relative to `DogeLib/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| Initial pair, `validation.cpp:318–319` | `Proposals/RelativeLockTime/SequenceLocks.lean:177` | Starts at `(-1, -1)`. |
| Enforcement, `validation.cpp:324–331`; flag, `consensus/consensus.h:24` | `Proposals/RelativeLockTime/SequenceLocks.lean:164` | `active` represents the flag. Unsigned version comparison agrees, including negative signed versions. |
| Sequence constants, `primitives/transaction.h:71–99` | `Script/Signature.lean:73`; `Proposals/RelativeLockTime/SequenceLocks.lean:93` | Disable bit 31, type bit 22, mask `0xffff`, shift 9. |
| Disable branch, `validation.cpp:339–343` | `Proposals/RelativeLockTime/SequenceLocks.lean:125` | Skips the input before height or ancestor checks. |
| Height calculation, `validation.cpp:364` | `Proposals/RelativeLockTime/SequenceLocks.lean:134` | Same sum and subtraction of 1. |
| Time calculation, `validation.cpp:362` | `Proposals/RelativeLockTime/SequenceLocks.lean:133` | Same mask, shift, widening, sum and subtraction of 1. |
| Maxima, `validation.cpp:362–364` | `Proposals/RelativeLockTime/SequenceLocks.lean:143` | Both maxima preserve the other component. |
| Ancestor selection, `validation.cpp:348`; `chain.cpp:113–141` | `Proposals/RelativeLockTime/SequenceLocks.lean:114` | For `H ≥ 1`, `0 ≤ c ≤ H`, let `a = c ∸ 1 ≤ H−1`. Depth `H−1−a` in the predecessor view reaches height `a`. Thus `c=0,1` reaches genesis and `c=H` reaches the predecessor. |
| Median calculation, `chain.h:274–298` | `Work/MedianTimePast.lean:33,48,52,60` | Same widened times, up to 11 entries, sorting and upper median. The ancestor suffix starts at the correct entry. |
| Index heights and predecessor links, `chain.h:165–171`; `chain.cpp:118–136` | `Work/NextWork.lean:59` | Consecutive nonnegative heights, below `INT_MAX`, establish the finite-view correspondence. |
| Evaluation, `validation.cpp:371–378` | `Proposals/RelativeLockTime/SequenceLocks.lean:157` | Candidate height and predecessor median. Both Core `>=` failures become strict `<` acceptance tests. |
| Composition, `validation.cpp:381–384` | `Proposals/RelativeLockTime/SequenceLocks.lean:164,191` | Calculates all locks before evaluation. `sequenceLocks` supplies the actual view median. |
| C++ arithmetic and conversions, `validation.cpp:324,333–364,375` | `Proposals/RelativeLockTime/SequenceLocks.lean:124–180` | Unbounded-integer rationale holds. Admitted height additions fit `int`. The unsigned shift is below `2^25`, and time sums fit `int64_t`. No in-domain wrap or conversion discrepancy found. |
| Height boundary, `validation.cpp:345,364` | `Proposals/RelativeLockTime/SequenceLocks.lean:96,126` | Restriction is stated and conservatively prevents intermediate overflow. Explanation needs Finding 1’s correction. |
| Coin above candidate, `validation.cpp:348`; `chain.cpp:115–116` | `Proposals/RelativeLockTime/SequenceLocks.lean:128` | Stated reason holds: `c=H+1` reads the candidate itself, and larger `c` dereferences null. Explicitly unsupported. |
| Missing history | `Proposals/RelativeLockTime/SequenceLocks.lean:130,172–175`; `Work/MedianTimePast.lean:60` | Stated reason holds. Wrong starting height, invalid view or insufficient median history produces unsupported, not rejection. |
| Missing predecessor, `validation.cpp:373`; genesis, `validation.cpp:1819–1825` | `Proposals/RelativeLockTime/SequenceLocks.lean:169`; `Proposals/Framework/Block.lean:347` | Empty-view acceptance is stated and implements the applicability convention. It does not claim Core evaluates a null predecessor. Genesis connects no transactions. |
| Calculation before evaluation, `validation.cpp:333–383` | `Proposals/RelativeLockTime/SequenceLocks.lean:143,177–180` | Input-order reason selection is stated and implemented. A later unsupported input takes precedence over an earlier unmet lock because evaluation follows calculation. |
| `prevHeights` mutation, `validation.cpp:341,1951–1956` | `Proposals/RelativeLockTime/SequenceLocks.lean:125` | Omission is stated and justified at the `ConnectBlock` boundary. The vector is not subsequently read and is fully overwritten for the next transaction. |
| Input lookup and test placement, `validation.cpp:1942–1966` | `Block/Connect.lean:214`; `Proposals/Framework/Block.lean:314` | Every non-coinbase is tested after successful input lookup and before sigop counting. Lookup supplies equal-length, ordered coins, matching Core’s assertion and indexing. |
| Coin heights, `coins.h:84–100`; `validation.cpp:1389,1953,1988` | `Block/Coins.lean:78,106,137,165`; `Proposals/Framework/Block.lean:307,325` | Existing coins retain their height. Earlier transactions in the same block create coins at candidate height before subsequent transactions run. |
| CSV activation, `validation.cpp:1906–1911` | `Proposals/RelativeLockTime.lean:179,188`; `Proposals/Framework/Block.lean:353` | `active` reaches the transaction test unchanged. |
| Rejection, `validation.cpp:1956–1958`; `consensus/validation.h:13` | `Proposals/RelativeLockTime/SequenceLocks.lean:77,83`; `Proposals/RelativeLockTime.lean:169,173`; `Proposals/Exports/Validate.lean:259,270` | Embeddings preserve rejection versus unsupported. Export gives `ConnectBlock`, `bad-txns-nonfinal`, DoS `100`, code `0x10`, and transaction index. |
| Predecessor supplied to `SequenceLocks`, `validation.cpp:1956` | `Proposals/Exports/Validate.lean:254`; `Block/Exports/Validate.lean:227–242`; `Block/Validate.lean:60` | Hook captures `run.view` before prepending the candidate. Candidate height is predecessor height plus one. |

## Not checked

No requested executable definition was omitted. Proofs, compilation, tests, runtime comparisons and independent verification of CSV’s historical nonactivation were not checked. No files were edited and no project code was executed.

## After the read

This section is an addendum, not part of the read.

- The record is the last message of the reader. Two links to local paths in finding 1 are now plain file names with their lines.
- Finding 1 is correct. Core computes `nCoinHeight + (int)(txin.nSequence & CTxIn::SEQUENCE_LOCKTIME_MASK) - 1` from the left, so the sum before the subtraction is the one that can overflow.
  The module documentation, the doc comment of `coinHeightBound` and SOUNDNESS.md now name the sum `c + 65535`, before the subtraction of 1.
  No definition changed. `inputLock_fits` already proves that this sum fits `int`: its statement for a height lock has `FitsInt (last + 1)`.
- The read is at DogeLib `58a30eb`, a commit of the branch before its squash. The definitions of the scope are those of the merged change, and only the documentation of finding 1 differs.
