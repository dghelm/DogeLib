# Model read: Difficulty retarget, next work and chain work

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Work/*.lean`, excluding `Proofs.lean`, `Exports.lean` and their directories. Core counterparts in `pow.cpp`, `dogecoin.cpp`, `arith_uint256.{cpp,h}`, `chain.{cpp,h}` and `chainparams.cpp`, as the [brief](briefs/retarget.md) names them.

## Result

The read found no discrepancy within the documented input domains.
Confidence is high for the source comparison, but this read gives no evidence from execution.

## Findings

None.
The Lean files state the restrictions on signed arithmetic, finite history, hexadecimal parsing and shift inputs.

## Checked and agreeing

Core paths below are relative to `src/`, and Lean paths are relative to `DogeLib/Work/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `dogecoin.cpp:43-45` | `Retarget.lean:98` | Candidate height and widened timestamp subtraction |
| `dogecoin.cpp:50-66` | `Retarget.lean:105`, `:119` | Height boundaries 5000/10000, DigiShield filter, division toward zero |
| `dogecoin.cpp:68-72` | `Retarget.lean:127` | Lower clamp precedes upper clamp |
| `dogecoin.cpp:75-86` | `Retarget.lean:162` | Compact flags ignored, uint32 multiplier, wrapped product, uint64 divisor, limit |
| `dogecoin.cpp:75-86` | `RetargetWords.lean:34`, `:48`, `:55` | Word operations and explicit byte limit follow the same sequence |
| `dogecoin.cpp:26-39`, `pow.cpp:17-29` | `NextWork.lean:81`, `:86` | Permission, previous height ≥157500, strict delay comparison |
| `pow.cpp:34-54` | `NextWork.lean:108` | Null tip, minimum difficulty, previous-height 145000 threshold |
| `pow.cpp:54-73` | `NextWork.lean:95`, `:108` | Recovery uses the parameter interval, preserves raw `nBits` |
| `pow.cpp:77-87` | `NextWork.lean:76`, `:108` | First retarget uses interval minus one, later retargets use full interval |
| `chain.cpp:113-141` | `NextWork.lean:124` | Ancestor selection agrees on consecutive, sufficiently complete views |
| `validation.cpp:3068-3070,3089` | `NextWork.lean:143` | Parameters selected for candidate height |
| `chainparams.cpp:88-95,126-141` | `Consensus.lean:57`, `:60`, `:84` | Mainnet work fields and activation tree |
| `chainparams.cpp:233-251,282-306` | `Consensus.lean:63`, `:66`, `:69`, `:84` | Testnet transitions at 145000, 157500 and 158100 |
| `chainparams.cpp:392-397,425-437` | `Consensus.lean:73`, `:77`, `:84` | Regtest transitions at 10 and 20. Caller ignores no-retarget flag |
| `consensus/params.h:69`, `chainparams.cpp:494-506` | `Consensus.lean:32`, `:42` | Positive network intervals and tree-search fallback |
| `arith_uint256.h:51-57,88-95` | `ArithUint256Compact.lean:25`, `:32` | Two low words, remaining words zero |
| `arith_uint256.cpp:21-53` | `ArithUint256.lean:70`, `:73`, `ArithUint256Words.lean:103`, `:117`, `:131`, `:138` | Shift guards, word order and discarded bits |
| `arith_uint256.cpp:55-65` | `ArithUint256.lean:60`, `ArithUint256Words.lean:55`, `:65` | uint64 intermediates, final carry discarded |
| `arith_uint256.h:77-84,135-151,173-188` | `ArithUint256Division.lean:38`, `:47`, `:51`, `:59`, `:62` | Addition, increment, negation and subtraction modulo 2^256 |
| `arith_uint256.cpp:84-119` | `ArithUint256.lean:65`, `ArithUint256Division.lean:27`, `:80`, `:95` | Comparison, quotient loop and zero-divisor error |
| `arith_uint256.cpp:171-184`, `arith_uint256.h:245-249` | `ArithUint256.lean:79`, `:82`, `ArithUint256Words.lean:69`, `:76`, `:83` | Bit count and low 64 bits. Signed-mask boundary documented |
| `arith_uint256.cpp:204-222` | `ArithUint256.lean:107`, `ArithUint256Compact.lean:46` | Flags use mantissa after right shift, overflow boundaries agree |
| `arith_uint256.cpp:224-245` | `ArithUint256.lean:133`, `ArithUint256Compact.lean:60` | Mantissa truncation, sign adjustment and zero |
| `arith_uint256.cpp:254-260`, `crypto/common.h:24-29` | `ArithUint256Bytes.lean:34`, `:39`, `:45`, `:52` | Eight little-endian groups |
| `uint256.cpp:30-56` | `ArithUint256Bytes.lean:57`, `:66` | Backwards nibble scan on declared exact-width hexadecimal domain |
| `chain.h:274-298` | `MedianTimePast.lean:33`, `:48`, `:52`, `:60` | Up to 11 timestamps, upper median, explicit adapter errors |
| `arith_uint256.h:69-75`, `chain.cpp:150-163` | `ChainWork.lean:42`, `:58` | Invalid targets return zero. Wrapped additions and complement agree |
| `pow.cpp:115-132` | `ProofOfWork.lean:30`, `:37`, `:46` | Target checks, internal byte order and inclusive hash bound |

## Not checked

- `pow.cpp:90-113`, `CalculateNextWorkRequired`. It has no Lean counterpart, and `GetNextWorkRequired` calls the Dogecoin-specific calculation.
- Core's arithmetic operations that have no counterpart in the scoped Lean files, such as general 256-bit multiplication and floating-point conversion.
- The accumulation of chain work outside `DogeLib/Work`, proof bodies, exports and compiled behaviour.
- Builds, differential comparisons, fixtures and all repository gates: **not run**. The reader changed no file.
