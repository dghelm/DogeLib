# Model read: Block subsidy

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: 4cd73bc. Core: e0a1c157791544e818c901bd9341896965afbf9d. Boost: 1.70.0
- Scope: `DogeLib/Block/Subsidy.lean`; `Hash256.displayBytes` in `DogeLib/Base/Bytes.lean`; Core’s `src/{dogecoin.cpp,amount.h,uint256.cpp,chainparams.cpp,consensus/params.h,validation.cpp}`; Boost’s `random/{mersenne_twister.hpp,uniform_int.hpp,uniform_int_distribution.hpp,detail/signed_unsigned_tools.hpp}`.
- Both Git revisions matched, with clean working trees. The supplied Boost headers identify version 1.70.0.

## Result

No discrepancies found within the documented mainnet and integer domains. Confidence is high from direct source comparison, but this is not a formal equivalence proof or an exhaustive comparison of seeds.

## Findings

None.

Fuel can suppress a result that Core returns, but cannot change the numeric value of a successful result. For example, height `0`, an all-zero previous hash and fuel `0` produce `fuelExhausted`; Core returns `54893900000000` koinu. This difference is documented. I did not establish that fuel `624` suffices for every subsidy seed.

## Checked and agreeing

Paths in the first column are relative to Core’s `src/` or Boost’s `boost/random/`. Lean references without a filename mean `DogeLib/Block/Subsidy.lean`.

| Core or Boost construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `uint256.cpp:21–26,65–68`, `GetHex`, `ToString` | `Base/Bytes.lean:72`, `displayBytes` | Reverse stored bytes. Each byte contributes its high hexadecimal digit first, with leading zeros retained. |
| `dogecoin.cpp:134–137`, seed extraction | `subsidySeed:199` | Exactly display digits 7 through 13. Base-16 accumulation matches `strtol`. Result is below `2^28`, so `long` → `unsigned int` → `uint32_t` preserves it. |
| `dogecoin.cpp:16–20`, `generateMTRandom` | `generateMTRandom:233` | Fresh engine from seed, then one distribution invocation. Core’s `range` and returned value are `int`. |
| `mersenne_twister.hpp:623–624`, `mt19937` | `Mt19937:74`, constants at `85,88,91` | `uint32_t`, `w=32`, `n=624`, `m=397`, `r=31`, and all constants agree. |
| `mersenne_twister.hpp:141–155`, `seed(value)` | `Mt19937.seed:109` | Ascending indices 1–623. Multiplier `1812433253`, shift 30, reduction modulo `2^32`, then normalization. Boost’s `size_t` addition before masking gives the same low 32 bits. Final index is 624. |
| `mersenne_twister.hpp:346–363`, `normalize_state` | `Mt19937.normalizeState:98` | Reads words 396 and 623. Top-bit test, wrapping left shift, replacement of word 0’s low 31 bits, and all-zero repair agree. |
| `mersenne_twister.hpp:538–543`, twist masks and loop bounds | `Mt19937.twist:120` | Masks agree. Boost’s four loops cover indices 0–221, 222–226, 227–622, and an empty fourth range. |
| `mersenne_twister.hpp:547–568`, twist loop bodies | `Mt19937.twist:121` | Ascending, in-place updates agree. Source index is `j+397` below 227 and `j−227` thereafter. Later iterations read updated words where Boost does. |
| `mersenne_twister.hpp:570–573`, final twist step | `Mt19937.twist:122` | At index 623, both read updated words 0 and 396. Low-bit multiplier of `a` agrees. |
| `mersenne_twister.hpp:584–595`, `operator()` | `Mt19937.next:137`, `temper:127`, `output:144` | Twist at index 624, then emit and advance. Tempering shifts `11,7,15,18` and masks agree. All word shifts are below 32. |
| `uniform_int.hpp:35–38,61–63,77–81` | `uniformInt:184` | Default type is `int`. Explicit bounds `(1,maxValue)` pass unchanged to `uniform_int_distribution`. |
| `uniform_int_distribution.hpp:332–337,369–371,243–248` | `uniformInt:184` | Constructor bounds and integral-engine dispatch agree on the stated domain. |
| `uniform_int_distribution.hpp:54–71,188–196` | `uniformInt:184` | `range_type=unsigned int`; engine result and `base_unsigned` are `uint32_t`; `mixed_range_type` is unsigned 32-bit. `bmin=0`, `brange=2^32−1`, `range=maxValue−1`. Only `brange > range` is reachable for documented `maxValue ≥ 2`. |
| `signed_unsigned_tools.hpp:30–49`, `subtract` | `uniformIntBucket:155`, `uniformIntAccept:164` | Signed-bound subtraction takes the `y≥0` branch: unsigned `maxValue−1`. Engine subtraction is unsigned `word−0`. Neither wraps here. |
| `uniform_int_distribution.hpp:198–217`, bucket calculation | `uniformIntBucket:155` | Uses `(2^32−1)/maxValue`, incremented exactly when the remainder equals `maxValue−1`. The `brange+1` branch is unreachable. |
| `uniform_int_distribution.hpp:218–225`, rejection loop | `uniformIntAccept:164`, `uniformInt:184` | Divide by bucket, accept quotient `≤ maxValue−1`, otherwise draw the next word. Fuel counts words, including the accepted word. |
| `signed_unsigned_tools.hpp:57–80`, `add` | `uniformIntAccept:166` | Signed specialization takes `y≥0`. Accepted quotient fits `int`; addition of 1 stays within `INT_MAX`. |
| `amount.h:16–18` | `coin:192` | `COIN` is signed 64-bit `CAmount`, equal to `100000000`. Modeled products are nonnegative and fit `int64_t`. |
| `consensus/params.h:42,74,85–88`; `chainparams.cpp:79,123–141,218` | `mainnetSubsidyHalvingInterval:213`, `mainnetSimplifiedRewards:220` | Interval 100,000 survives both record copies. Static initialization supplies initial `false`; both later records have `true`. Pointer defaults and tree construction agree with selection. |
| `chainparams.cpp:494–506`; `chainparams.h:60–62` | `mainnetSimplifiedRewards:220` | Records selected: base through 144,999; DigiShield 145,000–371,336; AuxPoW from 371,337. Exact activation heights agree. Nonnegative `int` heights convert exactly to `uint32_t`. |
| `dogecoin.cpp:129,138–141`, random reward | `subsidyMaxReward:226`, `getDogecoinBlockSubsidy:249` | Nonnegative division agrees. Reachable signed-`int` shifts are only 0 and 1. `maxReward`, though stored as `CAmount`, converts exactly to `int`: 999,999 or 499,999. Both add the extra 1 before multiplying by `COIN`. |
| `dogecoin.cpp:142–147`, fixed reward | `getDogecoinBlockSubsidy:256` | Strict cutoff at 600,000. Signed 64-bit positive shifts by 1–5 agree with `Nat`. From 600,000 through `INT_MAX`, both return `10000*COIN`. |
| `validation.cpp:1996–2001`, caller | `getDogecoinBlockSubsidy:249`, domain comment at `237–247` | Caller supplies current height, its selected record, and predecessor hash. Fees and coinbase bound are explicitly outside this Lean module. |

## Not checked

No scoped executable construct was omitted. Documented exclusions include other networks, negative or oversized heights, and distribution bounds outside the helper’s stated domain.

Supplementary comparison: `python3 -I -B -` sent 2,117 `block.subsidy` cases to the existing oracle and Core harness. All subsidies agreed, including schedule boundaries, record boundaries, `INT_MAX`, and seeds 0–1,023 at heights 1 and 100,000. The harness reported Boost 1.70.0. Binary provenance was not independently rebuilt.

Build, declaration, refinement, full comparator, exhaustive seed, and other repository gates were not run.
## After the read

This section is an addendum, not part of the read.

- The header names the reader as the model named itself. The Codex log of the run gives the model identifier `gpt-6.1-sol`.
- The read did not establish that 624 words of fuel suffice.
  `scripts/compare_subsidy_seeds.py` compared all 2^28 seeds at heights 1 and 100,000 with Core on 2026-11-13.
  It found no error and at most 2 redraws ([COVERAGE.md](../../COVERAGE.md#operations), *Block subsidy*).
- The reader sent 2,117 cases to the oracle and the harness. A model read needs no execution, and the repository's own comparison covers those cases and more.
- The [brief](briefs/subsidy.md) is the prompt of the read.
