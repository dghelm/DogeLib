# Coverage: Proof of Work and Retarget

This file holds the per-operation coverage detail for `Work`: 256-bit arithmetic, word models, compact targets, and retargets.
It also covers supplied-hash proof of work, next-work selection, median time past, block proof, and work parameters.
See [COVERAGE.md](../../COVERAGE.md#operations) for the compact matrix and [COVERAGE.md](../../COVERAGE.md#legend) for field meanings and theorem tags.
See [docs/soundness/work.md](../soundness/work.md) for theorem hypotheses and boundaries, and [docs/comparison-evidence.md](../comparison-evidence.md) for finite Core comparison counts.

## 256-bit arithmetic, addition

- **Definition**: `Work.ArithUint256.Words.add`
- **Theorems**: `Words.add_step`: exact 64-bit intermediate for a carry at most one. `addLoop_value`: full sum with final carry.
- **Comparison**: None
- **Refinement**: Core's word loops, modeled in Lean: `Words.add_value` gives addition modulo 2^256 for all word inputs
- **Excluded**: Core's compiled code

## 256-bit arithmetic, bit length

- **Definition**: `Work.ArithUint256.Words.bits`
- **Theorems**: `Words.bits_le`: at most 256, for every word input
- **Comparison**: None
- **Refinement**: Core's word loops, modeled in Lean: `Words.bits_toArith`, `bits_ofArith` agree with the arithmetic bit length on every input
- **Excluded**: Core's compiled code

## 256-bit arithmetic, byte conversion

- **Definition**: `Work.ArithUint256.Words.uintToArith256`, `ofTargetBytes`
- **Theorems**: `Words.readLE32_toNat`: each four-byte group fits exactly in a word
- **Comparison**: Network powLimit literals checked by kernel computation
- **Refinement**: Core's word loops, modeled in Lean: `Words.uintToArith256_toArith` agrees with the independent radix-256 byte interpretation for every 32-byte input
- **Excluded**: Core's compiled code and memory layout

## 256-bit arithmetic, comparison

- **Definition**: `Work.ArithUint256.Words.compareTo`
- **Theorems**: None
- **Comparison**: Exercised by the division cases
- **Refinement**: Core's word loops, modeled in Lean: `Words.compareTo_eq` compares the natural values for all word inputs
- **Excluded**: Core's compiled code

## 256-bit arithmetic, construction and assignment

- **Definition**: `Work.ArithUint256.Words.ofUInt64`, `assignUInt64`
- **Theorems**: `Words.ofUInt64_value`: exact uint64 value for every input
- **Comparison**: D16 line 490 derived assignment runs through the uint64 constructor model
- **Refinement**: Core's word loops, modeled in Lean: `Words.ofUInt64_toArith`, `assignUInt64_toArith` agree with the arithmetic embedding for every input and previous word array. Derived uint64 assignment constructs a temporary and copies its words, because the implicit derived assignment hides the base uint64 overload.
- **Excluded**: Core's compiled code

## 256-bit arithmetic, division

- **Definition**: `Work.ArithUint256.div`, `Words.divide`
- **Theorems**: `Words.divide_eq_none_iff`: exception exactly for zero divisors. `divLoop_spec`: quotient–remainder invariant and remainder bound, under alignment and zero low quotient bits.
- **Comparison**: `lake test`: ten nonzero-divisor cases from D16 lines 357-367 through both models, and both zero-divisor exceptions at lines 362 and 368 through the word model
- **Refinement**: Core's word loops, modeled in Lean: `Words.divide_toArith`, `divide_ofArith` agree with arithmetic division for every dividend and nonzero divisor
- **Excluded**: Core's compiled code and operand state after the throw. The quotient mask models the intended unsigned shift (S1).

## 256-bit arithmetic, low 64 bits

- **Definition**: `Work.ArithUint256.Words.getLow64`
- **Theorems**: None
- **Comparison**: `lake test`: D16 lines 394-396 through both the arithmetic and word models
- **Refinement**: Core's word expression, modeled in Lean: `Words.getLow64_toArith`, `getLow64_ofArith` agree with the arithmetic low 64 bits on every input
- **Excluded**: Core's compiled code

## 256-bit arithmetic, multiplication

- **Definition**: `Work.ArithUint256.Words.mulUInt32`
- **Theorems**: `Words.mul_intermediate_lt`, `mul_step`: no 64-bit overflow when the carry fits in 32 bits. `mulLoop_value`: complete product with final carry.
- **Comparison**: `lake test`: four D16 multiply cases, lines 347-350, through both the arithmetic and word models
- **Refinement**: Core's word loops, modeled in Lean: `Words.mulUInt32_toArith`, `mulUInt32_ofArith` agree with multiplication modulo 2^256 for every input and `UInt32` multiplier
- **Excluded**: Core's compiled code

## 256-bit arithmetic, negation

- **Definition**: `Work.ArithUint256.Words.neg`
- **Theorems**: `Words.incrementLoop_value`: increment modulo the radix power for every word count
- **Comparison**: Exercised by the division cases
- **Refinement**: Core's word loops, modeled in Lean: `Words.neg_value` gives two's-complement negation modulo 2^256 for every word input
- **Excluded**: Core's compiled code

## 256-bit arithmetic, representation

- **Definition**: `Work.ArithUint256.Words`, `Words.ofArith`, `toArith`
- **Theorems**: `Words.ofArith_toArith`, `toArith_ofArith`: inverse conversions for every eight-word array and every 256-bit value
- **Comparison**: Exercised by the multiplication, low-64-bit and shift known answers
- **Refinement**: None
- **Excluded**: Memory layout and foreign bindings

## 256-bit arithmetic, shifts

- **Definition**: `Work.ArithUint256.Words.shiftLeft`, `shiftRight`
- **Theorems**: None
- **Comparison**: `lake test`: 1,792 cases from D16 lines 159-196 and 30 zero-result boundary cases from D13's index guards. Expected bytes from Core's byte helpers, D16 lines 125-154.
- **Refinement**: Core's word loops, modeled in Lean: `Words.shiftLeft_toArith`, `shiftRight_toArith`, `shiftLeft_ofArith`, `shiftRight_ofArith` agree with the arithmetic shifts for every input and natural shift. Includes Core's unsigned 32-bit domain
- **Excluded**: Core's compiled code

## 256-bit arithmetic, subtraction

- **Definition**: `Work.ArithUint256.Words.sub`
- **Theorems**: `Words.sub_value_of_le`: exact natural subtraction when the subtrahend is at most the minuend
- **Comparison**: Exercised by the division cases
- **Refinement**: Core's word loops, modeled in Lean: `Words.sub_value` gives subtraction modulo 2^256 for all word inputs
- **Excluded**: Core's compiled code

## Block proof

- **Definition**: `Work.blockProof`, `Work.ArithUint256.complement` in `Work.ChainWork`
- **Theorems**: `blockProof_eq`: for every compact value, `⌊2^256 / (t + 1)⌋` when `SetCompact` reports no sign and no overflow and the target `t` is not zero, and 0 otherwise. `setCompact_value_ne_max`: no compact value decodes to 2^256 − 1, so the divisor `t + 1` is never zero ([soundness](../soundness/work.md#chain-work))
- **Comparison**: `lake test`: 11 compact values with hand-derived expectations. They include the limits `0x1e0fffff` and `0x207fffff` and the mainnet genesis `nBits` `0x1e0ffff0`. They also include the targets 1, 2^248 and `0xffff * 2^240`, a negative value and an overflow from D16, and three zero targets
- **Refinement**: None
- **Excluded**: No word model of `GetBlockProof`: the arithmetic results of `operator~`, `+` and `/` stand for Core's word loops. No comparison with Core

## Compact target decoding

- **Definition**: `Work.ArithUint256.setCompact`, `Words.setCompact`
- **Theorems**: `setCompact_fOverflow`: the overflow flag is set exactly when the encoded number is at least 2^256, for every compact. `setCompact_getCompact_le`, `setCompact_getCompact_flags`, `setCompact_getCompact_of_lt`: see *Compact target encoding*.
- **Comparison**: `lake test`: Core's `bignum_SetCompact` (D16 lines 412-538), 21 steps through both models: values, `GetCompact` results and both flags. `scripts/compare_core.py`: D16 fixtures and 5120 generated compact inputs against Core at `e0a1c15`, with sign, zero and overflow boundaries. All agree.
- **Refinement**: Core's word loops, modeled in Lean: `Words.setCompact_toArith` agrees with the arithmetic decoder for every compact, including both flags
- **Excluded**: No equivalence theorem to compiled Core

## Compact target encoding

- **Definition**: `Work.ArithUint256.getCompact`, `Words.getCompact`
- **Theorems**: For every 256-bit value `a`: `setCompact_getCompact_le` (decoding the encoding of `a` gives at most `a`), `setCompact_getCompact_flags` (no sign, no overflow), `getCompact_setCompact_getCompact` (encoding again gives the same compact), `getCompact_assertions` (Core's two asserts hold). `setCompact_getCompact_of_lt`: exact for `a < 2^23`. `getCompact_setCompact_iff`: a compact survives decoding and encoding again exactly when `GetCompact` produces it.
- **Comparison**: `lake test`: `bignum_SetCompact`, as above. `scripts/compare_core.py`: D16 fixtures and 1532 generated magnitude/sign inputs against Core at `e0a1c15`. All agree.
- **Refinement**: Core's word loops, modeled in Lean: `Words.getCompact_toArith` agrees with the arithmetic encoder for every word input and both sign arguments
- **Excluded**: No equivalence theorem to compiled Core

## Difficulty retarget

- **Definition**: `Work.calculateDogecoinNextWorkRequired`, `calculateDogecoinNextWorkRequiredWords`, `calculateDogecoinNextWorkRequiredBytes`
- **Theorems**: `modulatedTimespan_mem` and the regime theorems: the modulated timespan lies within the bounds of its regime, for every input. `retarget_decoded_le_powLimit`: the result decodes to at most `powLimit` with no flags set, for every input. `signedSteps_fit`, `modulatedTimespan_eq_int64`: no `int64_t` overflow, and agreement with Lean's `Int64` arithmetic, for block times in `[0, 2^32)` and `nPowTargetTimespan < 2^61`. `retarget_eq_of_no_wrap`, `no_wrap_of_le_powLimit`: closed form when the 256-bit product does not wrap. `retarget_wrap_example`: a wrap that makes a longer timespan give a smaller target.
- **Comparison**: `lake test`: the six `get_next_work_*` cases of Core's `dogecoin_tests.cpp` (D7), through the arithmetic and both word entry points: `difficulty_limit`, `pre_digishield`, `digishield`, `digishield_modulated_upper`, `digishield_modulated_lower`, `digishield_rounding`. 17 cases of `arith_uint256_tests.cpp` (D16) for `mulUInt32`, `div` and `getLow64`. They are `multiply` lines 347 to 350, `divide` lines 357 to 367, and `methods` lines 394 to 396. The word division model also runs both zero-divisor cases. `scripts/compare_core.py`: all six D7 fixtures, 49248 boundary requests and the regtest legacy wrap case against Core at `e0a1c15`. All agree. See *256-bit arithmetic* for the operation-level word refinements and comparisons.
- **Refinement**: Core's word loops, modeled in Lean: `calculateDogecoinNextWorkRequiredWords_eq` returns `some` of the arithmetic target for every existing input. `calculateDogecoinNextWorkRequiredBytes_eq` covers every 32-byte limit with its independent arithmetic interpretation. Includes the divisor constructor and limit comparison.
- **Excluded**: Header validity, AuxPoW, `nPowTargetTimespan <= 0`, an equivalence theorem to compiled Core. Signed Core agreement retains the time and timespan bounds in the theorem column.

## Difficulty retarget, powLimit literals

- **Definition**: `Work.ArithUint256.targetBytesOfHex`
- **Theorems**: `mainnet_powLimit_literal`, `mainnet_digishield_powLimit_literal`, `testnet_powLimit_literal`, `testnet_digishield_powLimit_literal`, `testnet_minDifficulty_powLimit_literal`, `regtest_powLimit_literal`, `regtest_digishield_powLimit_literal`: Core's literal converts to each existing record's arithmetic powLimit. `retarget_mainnet_literal`, `retarget_testnet_literal`, `retarget_regtest_literal`: at every selection height, parsed literal bytes give the specified retarget for every retarget input. Covers all ten tree records.
- **Comparison**: Kernel computation from D14 lines 88, 248 and 392
- **Refinement**: Core's word loops, modeled in Lean: backwards hex scan followed by `Words.uintToArith256`
- **Excluded**: General `SetHex` parsing, whitespace and truncation, Core's compiled code

## Median time past

- **Definition**: `Work.medianTimePast` in `Work.MedianTimePast`
- **Theorems**: For a view with first entry `last` at height `h`, `k = medianTimeSpan last = min(11, h + 1)`. `medianTimePast_eq` and `medianTimePast_short` take a view that passes `validateWorkView`. `medianTimePast_eq`: with at least `k` entries, the result is index `k / 2` of `sortedTimes`. `sortedTimes` is the ascending sort of the first `k` times, for every view (`sortedTimes_perm`, `sortedTimes_sorted`). `medianTimePast_short`: fewer entries return `shortView`. `medianTimePast_invalid`: a view that `validateWorkView` rejects returns `invalidView`. `medianTimePast_nil`: the empty view returns `emptyView`. For every success, with no other hypothesis: `medianTimePast_mem`, the result is the time of one of the first `k` entries. `medianTimePast_bounds`, it lies between their least and greatest times. `medianTimePast_rank`, at least `k / 2 + 1` of those times are at most the result and at least `k - k / 2` are at least it. `medianTimePast_congr_prefix`: two views that pass `validateWorkView`, with the same first `k` entries, give the same result.
- **Comparison**: `lake test`: mainnet heights 0–12 with hand-derived medians, chain acceptance at heights 1–12 and short views. [Provenance](../../tests/work/mainnet-genesis-headers/README.md). The 312 mainnet headers at 144719–145030: 10 short views, chain acceptance at 301 candidates and four hand-derived out-of-order medians. 13 hand-derived synthetic cases: even counts, times out of order, equal times, the UInt32 bounds and each adapter error.
- **Refinement**: None
- **Excluded**: No Core comparison. No header time check: the comparison of a header time with the median belongs to the contextual header check. A short view is an adapter error, where Core with its full chain never stops early above genesis.

## Minimum-difficulty permission

- **Definition**: `Work.delayedBlock`, `Work.allowDigishieldMinDifficultyForBlock`
- **Theorems**: `getNextWorkRequired_minDifficulty`: a checked view satisfying the all-block minimum condition returns compact powLimit
- **Comparison**: `lake test`: source-derived strict-delay and previous-height boundary examples (D6 lines 26-39, D17 line 61)
- **Refinement**: None
- **Excluded**: No header timestamp validity claim

## Next-work selection

- **Definition**: `Work.getNextWorkRequired`, `Work.nextWorkRequired`
- **Theorems**: `getNextWorkRequired_genesis`: null tip returns compact powLimit. `blocksToGoBack_le`: no first-height underflow at a retarget with positive interval. `recoverLastNonMinDifficulty_mem`: successful recovery returns an entry's compact. `retargetInterval_no_recovery`: from previous height 145000 the non-retarget branch is unreachable, for every record. `retargetInterval_eq_record_of_nonretarget`: the local and record intervals are equal wherever recovery can run, for every record. `nextWorkRequired_congr_prefix`: let `h` be the first height, and let `params` be the record at the candidate height. Two checked views with the same first entry that agree on their first `retargetInterval params h + 1` entries give the same result. `nextWorkRequired_ok`: a checked view that reaches height 0 gives a value, for every network and candidate time.
- **Comparison**: `lake test`: synthetic branch and finite-view errors (D17), plus all six D7 arithmetic answers through contiguous synthetic views. Real mainnet headers: 278 difficulty copies, retarget 144960 and 31 DigiShield retargets (145000–145030), with hash links and checkpoint 145000 (D9). `scripts/compare_core.py`: 1011 synthetic network cases, 28 testnet recovery walks, 310 real-header candidates and one traversal across a null skip pointer against Core at `e0a1c15`. All agree. View errors stay outside the Core comparison.
- **Refinement**: None
- **Excluded**: No equivalence theorem to compiled Core or skip-pointer traversal. Truncated views can lack required ancestors. Coherent heights do not establish CheckProofOfWork or the no-wrap hypothesis.

## Proof-of-work target and supplied hash

- **Definition**: `Work.validProofOfWorkTarget`, `checkProofOfWork`, `hashToArith256`
- **Theorems**: `validProofOfWorkTarget_iff`: exactly the four target conditions. `checkProofOfWork_iff`, `validProofOfWorkTarget_iff_exists_hash`, `checkProofOfWork_mono`: acceptance, existence and hash monotonicity for every input. `no_wrap_of_validProofOfWorkTarget`, `retarget_eq_of_validProofOfWorkTarget`: exact retarget under numerical bounds. Mainnet and testnet corollaries discharge those bounds at every selection height. `regtest_no_wrap`, `regtest_retarget_eq`: every compact from selection height ten. `legacy_regtest_wrap_example`: a valid legacy regtest target can wrap the isolated retarget.
- **Comparison**: `lake test`: 20 source-derived D17 branch and boundary cases, and target validity of all 312 mainnet fixture headers
- **Refinement**: `hashToArith256_eq`: word conversion equals the independent radix-256 interpretation
- **Excluded**: Scrypt, AuxPoW, full header validation and compiled Core equivalence. The legacy regtest example uses the isolated retarget with the legacy record, which the normally selected caller never uses at a retarget.

## Work parameters by height

- **Definition**: `Work.ConsensusTree.getConsensus`, `Work.consensusTree`, `Work.getConsensus`
- **Theorems**: `getConsensus_mainnet`, `getConsensus_testnet`, `getConsensus_regtest`: projected tree search equals the network's piecewise work fields at every UInt32 height
- **Comparison**: `lake test`: source-derived network field tuples at activation boundaries and maximum UInt32 height (D14)
- **Refinement**: None
- **Excluded**: Work projection only. AuxPoW records retain their effective heights but repeat the work fields.
