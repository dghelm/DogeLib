# Soundness: Proof of Work, Retarget, and Chain Work

This file states what the proof-of-work, retarget arithmetic, 256-bit word-model, next-work, median-time-past, and chain-work proofs establish.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: Compact target encoding, DigiShield and legacy retargets, supplied-hash proof of work, 256-bit word models, next-work selection, median time past, and chain work.
- **Specification modules**: `DogeLib.Work.*`.
- **Proof modules**: `DogeLib.Work.Proofs.*` and `DogeLib.Block.Proofs.HeaderSequence` (for `chainWork_add`).
- **Key boundaries**: Word-model proofs relate Lean models to Lean arithmetic, while correspondence to Core's C++ loops remains subject to review (A1).
  No theorem assigns semantics to undefined C++ signed shifts, and supplied-hash checks do not compute the scrypt digest.

## Compact encoding and difficulty retarget

The `Work` layer specifies Core's `SetCompact`, `GetCompact` and `CalculateDogecoinNextWorkRequired` (SOURCES.md, D6, D12, D13).

For every 256-bit value `a`, `setCompact_getCompact_le` says that decoding the compact encoding of `a` gives at most `a`.
`setCompact_getCompact_flags` says that the decoder reports no sign and no overflow for it.
`getCompact_setCompact_getCompact` says that encoding the decoded value again gives the same compact.
`setCompact_getCompact_of_lt` says that the round trip is exact for `a < 2^23`.
`getCompact_assertions` says that the two `assert` statements of `GetCompact` hold for every value.

`getCompact_setCompact_iff` says that a 32-bit compact survives decoding and encoding again exactly when `GetCompact` produces it.
Core's tests contain compacts that do not survive, and three theorems record them, such as `0x04923456`, which encodes again as `0x04123456`.
`setCompact_fOverflow` says that `SetCompact` sets its overflow flag exactly when the encoded number is at least 2^256.

`modulatedTimespan_mem` says that the clamped timespan lies within the bounds of its regime, for every input.
Four theorems state those bounds for DigiShield and for each height range before it, and two state them for the mainnet parameters.
`retarget_decoded_le_powLimit` says that the new compact target decodes to at most `powLimit`, with neither flag set, for every input.
The input includes old targets above `powLimit` and 256-bit products that wrap.

The signed arithmetic is specified in `Int`, with `Int.tdiv` for the C++ division.
`signedSteps_fit` says that no `int64_t` step overflows when both block times are in `[0, 2^32)` and the target timespan is below 2^61.
`modulatedTimespan_eq_int64` says that Lean's `Int64` operations compute the same timespan on that domain.
Outside it, a C++ signed overflow is undefined behavior, and the `Int` result is a choice of this specification.

The 256-bit product at line 80 is reduced modulo 2^256, as Core reduces it.
`retarget_eq_of_no_wrap` gives the exact result when the product does not wrap.
`no_wrap_of_le_powLimit` and `mainnet_limit` say that it does not wrap for the mainnet parameters when the old target is at most `powLimit`.
`retarget_wrap_example` shows a wrap for an old target of 2^255: a longer actual timespan gives a smaller target.

`validProofOfWorkTarget_iff` supplies the old-target bound from Core's separate target check, as the supplied-hash subsection explains.
The finite-view caller checks coherent heights without establishing target validity.
A claim about a validated chain still assumes that the previous block passed the required check.

The axioms of the 45 theorems in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `mainnet_limit`, `filteredTimespan_rounding` |
| `propext` | `pow256`, `getCompact_setCompact_zero_mantissa`, `getCompact_setCompact_negative`, `setCompact_overflow_example`, `retargetTimespan_pos` |
| `propext`, `Quot.sound` | `byteLength_bounds`, `byteLength_eq`, `byteLength_le`, `and_two_pow_ne_zero`, `sign_bit`, `tdiv_eq`, `timespanLimits_le` |
| `propext`, `Classical.choice`, `Quot.sound` | Every other theorem in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, including `modulatedTimespan_mem`, `retarget_decoded_le_powLimit`, `setCompact_getCompact_le`, `getCompact_setCompact_iff`, `setCompact_fOverflow`, `signedSteps_fit`, `retarget_eq_of_no_wrap` and `no_wrap_of_le_powLimit` |
Some concrete examples use `decide +kernel`, which the kernel checks without compiled code.

These parts are not proved here:

- The checks of `ContextualCheckBlockHeader` other than the version gates, such as `nBits` against `GetNextWorkRequired`, and `CheckBlock`.
  [Contextual header validation](headers.md#contextual-header-validation) and [`CheckBlock`](blocks.md#block-codec-checktransaction-and-checkblock) specify them.
  [Dogecoin's scrypt digest](cryptography.md#dogecoins-scrypt-digest), [the AuxPoW check](headers.md#the-auxpow-check) and [header proof of work](headers.md#header-proof-of-work) specify the scrypt digest, `CAuxPow::check` and `CheckAuxPowProofOfWork`.
  The supplied-hash check is specified separately below.

The word-model refinements below cover multiplication, division, both shifts, bit length and low-64-bit extraction.
They also cover division's comparison, addition, negation and subtraction dependencies.
The correspondence between Core's source and the Lean models remains subject to review (A1).

`lake test` runs the six `get_next_work_*` cases of `dogecoin_tests.cpp` and the 21 steps of `bignum_SetCompact` through the compiled code (B1).
It also runs 17 cases of the `multiply`, `divide` and `methods` tests of `arith_uint256_tests.cpp` (D16) through `mulUInt32`, `div` and `getLow64`.
All 17 cases also run through the corresponding word models.
The word division model also runs the two zero-divisor cases.

## Target validity and supplied-hash proof of work

`Work.ProofOfWork` specifies `CheckProofOfWork` at D17, `src/pow.cpp` lines 115-132.
The inputs are a supplied `Hash256`, a UInt32 compact target and a parameter record, of which only `powLimit` is read.
`hashToArith256` uses the eight little-endian `UintToArith256` word reads.
`hashToArith256_eq` proves equality to the independent radix-256 interpretation for every supplied hash.
The input bytes have Core's internal order, with byte zero least significant for the arithmetic comparison.

`validProofOfWorkTarget_iff` characterizes acceptance of the target check for every compact and parameter record.
The decoded target must be nonzero, at most `powLimit`, and have neither the negative nor overflow flag set.
The check permits noncanonical compacts, such as `0x04000001`, which decodes to 256.
`checkProofOfWork_iff` adds the condition that the supplied hash is at most the target.
`validProofOfWorkTarget_iff_exists_hash` proves that target validity is equivalent to acceptance of some supplied hash, with zero as a witness.
`checkProofOfWork_mono` proves that a smaller hash remains accepted for a fixed compact and parameter record.

`no_wrap_of_validProofOfWorkTarget` supplies the previous-target bound to `no_wrap_of_le_powLimit`.
It retains the numerical hypothesis `powLimit * 4T < 2^256`, where `T` is the target timespan.
`retarget_eq_of_validProofOfWorkTarget` also assumes `T < 2^30`, and gives the existing exact closed form for all retarget inputs.
The mainnet and testnet `*_proofOfWork_bounds` theorems discharge both numerical hypotheses at every UInt32 parameter-selection height.
They cover every selected record, including the AuxPoW eras, by kernel computation on the records after the selection proof.
Their `*_no_wrap_of_validProofOfWorkTarget` and `*_retarget_eq_of_validProofOfWorkTarget` corollaries retain only previous-target validity.

Selection height and retarget height remain explicit independent inputs.

Both regtest records fail the conservative `powLimit * 4T` bound, because their limit is `2^255 - 1`.
`regtestDigishield_modulatedTimespan` proves that the DigiShield record's multiplier is exactly one for every height and actual timespan.
`regtest_no_wrap` and `regtest_retarget_eq` therefore cover every compact at all regtest selection heights from ten, without a target-validity hypothesis.

`legacy_regtest_wrap_example` records a valid compact `0x207fffff`, actual timespan 901 and retarget height one.
The isolated retarget with the legacy regtest record returns `0x1f02467a`, after the product exceeds 2^256.
This wrap is Core's own behavior: `src/dogecoin.cpp` line 80 calls multiplication modulo 2^256 in `src/arith_uint256.cpp` lines 55-65.
DogeLib models that behavior.
The example is reachable through the isolated `CalculateDogecoinNextWorkRequired` API with that record.
The normally selected regtest `GetNextWorkRequired` caller cannot reach a legacy retarget: the legacy record applies below height ten, with interval 14400.

`lake test` runs 20 synthetic branch and boundary cases derived from D17 lines 124-129.
It also requires target validity for all 312 pinned mainnet headers.
Core's `src/test/auxpow_tests.cpp` lines 333-355 mines passing and failing digests at runtime, rather than supplies fixed digest fixtures.
The Lean tests do not compute scrypt or compare with compiled Core.
A supplied-hash check does not establish that the hash is the correct scrypt digest, or that a header or AuxPoW is valid.
[Header proof of work](headers.md#header-proof-of-work) supplies the scrypt digest and composes this check with the AuxPoW check.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Work.Proofs.ProofOfWork` |
| --- | --- |
| None | `mainnet_proofOfWork_bounds` |
| `propext`, `Quot.sound` | `hashToArith256_eq`, `hashToArith256_zero`, `testnet_proofOfWork_bounds` |
| `propext`, `Classical.choice`, `Quot.sound` | All other theorems, including the target characterizations, monotonicity, retarget corollaries and legacy regtest example |

## 256-bit word arithmetic

`ArithUint256.Words` models Core's eight little-endian `UInt32` words as a function from `Fin 8`.
`ofArith_toArith` and `toArith_ofArith` prove that the word and arithmetic representations have inverse conversions.
The model follows the pinned loops in `arith_uint256.cpp` and the `GetLow64()` expression in `arith_uint256.h` (D12, D13).

`mulUInt32_toArith`, `shiftLeft_toArith`, `shiftRight_toArith`, `bits_toArith` and `getLow64_toArith` relate the word models to the arithmetic definitions.
They quantify over every eight-word input.
Multiplication also quantifies over every `UInt32` multiplier, and both shift theorems cover every natural shift.
Core takes an unsigned 32-bit shift, so that domain is included.
The corresponding `*_ofArith` theorems start from every `ArithUint256` value.
`bits_le` bounds the scan's result by 256.

`mul_intermediate_lt` proves that `carry + b32 * pn[i]` fits in 64 bits when the carry fits in 32 bits.
`mul_step` proves that the `UInt64` operations preserve that exact value.
`mulLoop_value` accounts for the full product, including the final carry, for every word count and initial carry below 2^32.
The exported multiplication theorem discards that carry modulo 2^256.

The axioms of the 24 public theorems in `Work.Proofs.ArithUint256Words`, by `#print axioms` with Lean `v4.35.0`:
All theorem names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `eval_lt`, `digits_eval`, `value_lt`, `ofArith_toArith`, `mul_intermediate_lt`, `mul_step`, `mulLoop_value`, `mulUInt32_toArith`, `getLow64_toArith`, `eval_high`, `eval_testBit`, `shiftRight_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `eval_digits`, `toArith_ofArith`, `mulUInt32_ofArith`, `getLow64_ofArith`, `bitScan_eq`, `bitsLoop_eq`, `bits_toArith`, `bits_ofArith`, `bits_le`, `shiftLeft_toArith`, `shiftLeft_ofArith`, `shiftRight_ofArith` |

`lake test` runs the four multiply and three low-64-bit cases from D16 through both representations.
It also runs 1,792 shift cases from D16 lines 159-196 and 30 zero-result cases at shifts of at least 256.
Core's independent byte helpers (D16 lines 125-154) supply expected bytes for the shift cases.
The boundary cases expect zero from Core's word-index guards (D13 lines 30-33 and 47-50).

These theorems relate Lean models, rather than Core's compiled code.
The correspondence between Core's source and each word model remains subject to review (A1).
Core's bit scan tests `pn[pos] & 1 << bits` with a signed `int` literal.
For a 32-bit `int`, N3337 section 5.8 paragraph 2 leaves `1 << 31` undefined (S1).
The model expresses the intended `0x80000000` mask with `testBit`.
No theorem assigns semantics to undefined C++ execution.

## 256-bit word division

`Work.ArithUint256Division` models Core's comparison, addition, negation, subtraction and division loops over the same eight words (D12, D13).
`compareTo_eq` compares their natural values.
`addLoop_value` accounts for the final carry, with an initial carry of at most one.
`add_step` proves that this carry and two words sum exactly in 64 bits.
`add_value`, `neg_value` and `sub_value` give addition, two's-complement negation and subtraction modulo 2^256 for every word input.
Negation follows Core's complement and prefix increment, including every wrapped word.

`divide_toArith` and `divide_ofArith` equate word division with `ArithUint256.div` for every dividend and nonzero divisor.
`divLoop_spec` preserves `num + quotient * original divisor` and leaves `num` below the original divisor.
Its hypotheses require aligned divisor words, the numerator bound at the current shift, and zero low quotient bits.
`divide_value` establishes these hypotheses from Core's bit-length alignment and zero initial quotient.
The bound also proves that the initial left shift and each accepted subtraction preserve the exact natural value.

`divide_eq_none_iff` proves that the model returns `none` exactly when the divisor's value is zero.
Core zeroes its quotient before the zero-divisor test, then throws `uint_error("Division by zero")` (D13 lines 88-92).
The model represents the exception without the operand state after the throw.
Its separate early-return branch returns the zero quotient when the divisor has more bits than the dividend.
The arithmetic `div` requires a nonzero proof and excludes the exception branch.

The quotient bit update uses Core's intended unsigned mask.
Core writes the signed expression `1 << (shift & 31)` (D13 line 100).
At bit 31, the same N3337 5.8 paragraph 2 boundary applies as for `bitScan` (S1).
No theorem assigns semantics to undefined C++ execution.
The correspondence between Core's source and these Lean models remains subject to review (A1).
No proof covers Core's compiled code or Lean's compiler and runtime (B1, B2).

`lake test` runs all ten nonzero divide cases from D16 lines 357-367 through both models.
It also checks `none` for both `BOOST_CHECK_THROW` cases at lines 362 and 368.
The expected quotients and exceptions come from Core's test file.

`readWords_ofFn` proves that the vector copy at each loop boundary preserves every word.
This copy prevents repeated evaluation of function-valued words from earlier loop states.
It adds Lean core vector and array operations to the compiled path (B2).

The axioms of all 24 public theorems in `Work.Proofs.ArithUint256Division`, by `#print axioms` with Lean `v4.35.0`:
All names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `add_step`, `addLoop_value`, `add_value`, `shiftRight_value` |
| `propext`, `Classical.choice`, `Quot.sound` | `readWords_ofFn`, `compareLoop_eq`, `compareTo_eq`, `incrementLoop_digits`, `incrementLoop_value`, `complement_value`, `neg_value`, `sub_value`, `sub_value_of_le`, `shiftLeft_value`, `quotient_mask`, `quotient_or_value`, `quotient_add_value`, `divLoop_spec`, `bits_eq_zero_iff`, `bits_value_bounds`, `divide_eq_none_iff`, `divide_value`, `divide_toArith`, `divide_ofArith` |

## Remaining word paths of the retarget

`Work.ArithUint256Compact` models Core's uint64 constructor, assignment, `SetCompact` and `GetCompact` over eight words (D12, D13).
`Words.ofUInt64_value` proves that construction stores every input exactly.
`ofUInt64_toArith` and `assignUInt64_toArith` equate construction and assignment with the arithmetic embedding, for every uint64 input and previous word array.
`assignUInt64` describes the explicit base-class overload at D12 lines 88-95, which sets every word.

The implicit `arith_uint256` copy assignment hides this base overload.
Thus `*this = nWord` in `SetCompact` and `num = 0x80` in D16 construct a temporary through D12 line 257, then copy it.
The temporary uses the uint64 constructor at D12 lines 51-57, and the base copy assignment copies its words at lines 44-49.

`Words.setCompact_toArith` equates the complete decoder result with `ArithUint256.setCompact` for every compact input.
The conclusion includes the magnitude and both flags.
For small exponents, both flags read the mantissa after the right shift, as Core does.
`Words.getCompact_toArith` equates the word encoder with `ArithUint256.getCompact` for every word array and both sign arguments.
These models use the proved word shifts, bit scan and low-64-bit extraction.

`Work.ArithUint256Bytes` gives an independent radix-256 interpretation of a 32-byte target.
`Words.uintToArith256_toArith` proves that eight grouped `ReadLE32` reads give that interpretation, for every 32-byte input (D13, D37).
`Words.readLE32_toNat` proves that each group fits exactly in its word.
The portable meaning of Core's `memcpy` and `le32toh` remains a source-review boundary.
Memory layout and Core's compiled code are not proved.

`targetBytesOfHex` models Core's backwards nibble scan for `0x` followed by exactly 64 ASCII hexadecimal digits (D11).
It rejects every other format.
It does not specify Core's general whitespace, prefix and truncation behavior.

Seven `*_powLimit_literal` theorems start from Core's literal strings at D14 lines 88, 248 and 392.
They prove the resulting `Words.toArith` interpretations equal the existing network parameter limits, including inherited DigiShield and AuxPoW limits.
The kernel checks these concrete computations with `decide +kernel`.
The literals come from Core, rather than from the arithmetic values under test.
The hex parser is checked only on the three concrete network strings, with two distinct spellings.

`calculateDogecoinNextWorkRequiredWords_eq` proves that word retarget returns `some` of the arithmetic target for every existing parameter record and input.
The executable model preserves division's `Option`, and the proof uses the positive-timespan field to exclude the exception.
It includes the divisor constructor, compact operations, multiplication, division and word comparison with the limit.
`calculateDogecoinNextWorkRequiredWithWords_eq` covers every explicit word limit, with that limit's arithmetic interpretation.
`calculateDogecoinNextWorkRequiredBytes_eq` also covers every 32-byte limit, through `UintToArith256` and its independent interpretation.

`retarget_mainnet_literal`, `retarget_testnet_literal` and `retarget_regtest_literal` connect each literal directly to the byte retarget.
At every network selection height, each corollary exhibits parsed bytes and proves retarget equality for every retarget input.
These corollaries cover all ten tree records, including the records that share work fields.

The signed timespan calculation reuses Core's lines 41-74 through `Work.Retarget`.
The equality of the Lean retargets has no additional signed-arithmetic hypothesis.
Agreement with Core's signed execution retains the existing block-time and target-timespan bounds from `signedSteps_fit` and `modulatedTimespan_eq_int64`.
The inherited bit-scan and division-mask models retain their intended-unsigned-mask boundary under S1.
The models' correspondence to Core's source remains subject to review (A1), and compiler and runtime trust remains (B1, B2).

The retarget materialises intermediate words with the vector copy from the division model.
`readWords_ofFn` proves that each copy preserves the words.
The copy avoids repeated computation of earlier word operations and retains the Lean core array execution boundary (B2).

`lake test` runs all 21 D16 compact cases through both arithmetic and word models, including both flags.
The derived assignment case at line 490 exercises uint64 construction, followed by a copy whose value is unchanged.
All six D7 retarget cases run through the arithmetic function and both word entry points.
The byte entry point starts from Core's mainnet hexadecimal limit.
These expectations come from Core's tests and are not a comparison with Core's compiled code.

The axioms of all 22 public theorems in `Work.Proofs.ArithUint256Compact`, `Work.Proofs.ArithUint256Bytes` and `Work.Proofs.RetargetWords`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `Words.ofUInt64_value`, `Words.ofUInt64_toArith`, `Words.assignUInt64_toArith`, `Words.readLE32_toNat`, `Words.uintToArith256_value`, `Words.uintToArith256_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `Words.setCompact_toArith`, `Words.getCompact_toArith`, all seven `*_powLimit_literal` theorems, `Words.compareTo_gt`, `calculateDogecoinNextWorkRequiredWithWords_eq`, `calculateDogecoinNextWorkRequiredWords_eq`, `calculateDogecoinNextWorkRequiredBytes_eq`, `retarget_mainnet_literal`, `retarget_testnet_literal`, `retarget_regtest_literal` |

The `Words` and literal theorem names are in `DogeLib.Work.ArithUint256`.
The retarget and network corollary names are in `DogeLib.Work`.

## Next-work selection and work parameters

`DogeLib.Work.Consensus` projects the work fields from Core's parameter records (D14, D15).
`ConsensusTree.getConsensus` follows the left and right search links and checks the right candidate's effective height before accepting it.
The three `getConsensus_*` theorems give the projected work fields at every UInt32 target height.
Mainnet changes at 145000, testnet at 145000 and 157500, and regtest at 10.
AuxPoW records retain separate effective heights but repeat these fields.
The projection makes no claim about the other consensus fields.

`DogeLib.Work.NextWork` specifies the caller of the retarget (D17, lines 32-88).
`nextWorkRequired` selects the candidate height's parameters, as validation and mining do (D33, D34).
The local interval becomes one at previous height 145000.
`retargetInterval_no_recovery` proves that the non-retarget branch cannot execute from that previous height, for every parameter record.

The recovery loop uses the record's interval instead of that local interval.
`retargetInterval_eq_record_of_nonretarget` proves that the local and record intervals agree whenever the caller is off a retarget boundary, for every record.
Recovery requires that condition, so no input can reach recovery with different intervals.
At previous height 144999, the candidate's DigiShield record already has interval one.

The all-block minimum rule checks previous height at least 157500 and a strict delay greater than twice the spacing (D6, lines 26-39).
Selected testnet parameters permit minimum difficulty from candidate height 157500, so that candidate still retargets and candidate 157501 can use the delay rule.
This caller ignores `fPowNoRetargeting`, including on regtest.
It also ignores `fPowAllowDigishieldMinDifficultyBlocks`.

The view is a newest-first list of explicit height, UInt32 time and compact target fields.
The adapter checks consecutive heights and bounds every height below 2147483647.
The last entry may be above genesis, so the view need not contain all history.
A walk that still needs a predecessor returns `missingAncestor` at a truncated suffix.
Core's corresponding ancestor assertion aborts when the required index is absent.

The model omits skip links and uses the predecessor path for ancestor lookup (D35).
No theorem relates Core's skip-pointer traversal to that path.

`blocksToGoBack_le` excludes the negative-first-height assertion when the interval is positive and divides the next height.
The adapter checks `zeroInterval` before the retarget boundary and underflow checks.
Thus `firstHeightUnderflow` is unreachable for every validated view: a positive interval at a retarget satisfies `blocksToGoBack_le`.
Malformed-view errors are separate from both assertion cases.
These errors are adapter contracts, not Core rejection codes.
The UInt32 times widen to Int, and the fixed network spacings of 1 or 60 keep the delay arithmetic within int64_t.

`getNextWorkRequired_genesis` proves the null-tip result for every record and candidate time.
`getNextWorkRequired_minDifficulty` proves the minimum result when validation succeeds and the all-block minimum condition holds.
`recoverLastNonMinDifficulty_mem` proves that a successful recovery returns a supplied entry's compact, without a header-validity hypothesis.
These caller claims do not establish target validity.

Two theorems bound the history that the caller reads.

`nextWorkRequired_congr_prefix` takes two views that pass `validateWorkView` and start with the same entry at height `h`.
If they agree on their first `retargetInterval params h + 1` entries, where `params` is the record at the candidate height, the results are equal.
A retarget reads the entry at index `blocksToGoBack`, at most the interval.
The recovery walk stops at the latest at a height divisible by the interval.
`recoverLastNonMinDifficulty_congr_prefix` takes a positive interval and a first view that passes `validateWorkView`.
Two views that start with the same entry at height `h` and agree on their first `n > h mod interval` entries give the same recovery.

`nextWorkRequired_ok` shows that a checked view that reaches height 0 gives a value, never an adapter error, for every network and candidate time.
It uses `difficultyAdjustmentInterval_getConsensus_pos`: every selected record has a positive interval.
The separate target-check theorem supplies the old-target bound when target validity is assumed.

`lake test` includes source-derived network and branch examples and all six D7 retarget answers through synthetic contiguous views.
The intermediate entries are synthetic, not historical headers.
These examples do not run Core or prove equality to its compiled caller.

`lake test` also reads 312 real mainnet headers at heights 144719–145030 from a public Electrum server.
The [fixture README](../../tests/work/mainnet-headers/README.md) records the source, date and exact request.
The test hashes all headers with compiled `Sha256d`, checks all predecessor links and requires Core's checkpoint hash at 145000 (D9).
It compares `nextWorkRequired .mainnet` with 278 difficulty copies, the interval-240 retarget at 144960 and 31 DigiShield retargets at 145000–145030.
The substantive retarget evidence is 144960 plus those 31 DigiShield blocks.

The first header supplies context.
Retarget 144720 lacks an ancestor, so the test requires `missingAncestor` there.
The test also requires target validity for all 312 headers with the selected mainnet parameters.
Those finite checks establish the old-target bound for these inputs, but neither proof of work nor AuxPoW validity.
They do not run Core or prove equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `getConsensus_mainnet`, `getConsensus_regtest` |
| `propext` | `retargetInterval_after`, `blocksToGoBack_first`, `blocksToGoBack_later`, `recoverLastNonMinDifficulty_mem`, `retargetInterval_no_recovery` |
| `propext`, `Quot.sound` | `getConsensus_testnet`, `retargetInterval_before`, `blocksToGoBack_le`, `retargetInterval_eq_record_of_nonretarget` |
| `propext`, `Quot.sound` | `validateWorkView_cons_cons`, `length_of_validateWorkView`, `recoverLastNonMinDifficulty_congr_prefix`, `difficultyAdjustmentInterval_getConsensus_pos`, `recoverLastNonMinDifficulty_ok` |
| `propext`, `Classical.choice`, `Quot.sound` | `getNextWorkRequired_genesis`, `getNextWorkRequired_minDifficulty`, `getNextWorkRequiredFromView_congr_prefix`, `nextWorkRequired_congr_prefix`, `nextWorkRequired_ok` |

## Median time past

`DogeLib.Work.MedianTimePast` specifies `CBlockIndex::GetMedianTimePast` (D18, lines 284-298).
Core collects the time of the entry and the times of up to ten predecessors, and stops early after genesis.
It sorts the collected times and returns the element at index `count / 2`, so an even count gives the upper median.
`ContextualCheckBlockHeader` calls it on the predecessor of a header (D33, lines 3103-3104).
[Contextual header validation](headers.md#contextual-header-validation) specifies that comparison with the header time.

`medianTimePast` takes the checked finite view of [next-work selection](#next-work-selection-and-work-parameters), newest first.
Let `h` be the height of the first entry, and let `k = medianTimeSpan = min(11, h + 1)`.
Core's walk has the full chain, so it always collects `k` times.
A finite view can stop above genesis, and Core's function on such a view would give a different median, not an error.
So `medianTimePast` returns the adapter error `shortView` for a view with fewer than `k` entries.

`medianTimePast` returns `invalidView` when `validateWorkView` rejects the view, and `emptyView` for the empty view.
These errors are adapter contracts, not Core rejection codes.

The times are UInt32 values widened to Int, as `GetBlockTime` widens them to int64_t (D18, lines 274-277).
The widening is exact, so the sort and the comparisons agree with Core's int64_t order on every UInt32 time.
`sortedTimes` sorts with `List.mergeSort` from Lean core.
`sortedTimes_perm` and `sortedTimes_sorted` prove that it is an ascending permutation of the first `k` times, for every view.

The theorems below hold for every view whose first entry is `last`:

- `medianTimePast_eq`: if the view passes `validateWorkView` and has at least `k` entries, the result is index `k / 2` of `sortedTimes`.
- `medianTimePast_short`: if the view passes `validateWorkView` and has fewer than `k` entries, the result is `shortView`.
- `medianTimePast_invalid` and `medianTimePast_nil` give the two other adapter errors.
- `medianTimePast_ok` gives the hypotheses and the index of `medianTimePast_eq` from a success.
- `medianTimePast_mem`: a success is the time of one of the first `k` entries.
- `medianTimePast_bounds`: a success lies between the least and the greatest of those times.
- `medianTimePast_rank`: for a success, at least `k / 2 + 1` of those times are at most the result, and at least `k - k / 2` are at least the result.
  This statement does not mention the sort, so it fixes the upper median independently of `sortedTimes`.
- `medianTimePast_congr_prefix`: two views that pass `validateWorkView` and agree on their first `k` entries give the same result, success or error.

`lake test` reads a fixture of the 13 mainnet headers at heights 0–12.
Two public Electrum servers returned the same bytes for these headers.
The [fixture README](../../tests/work/mainnet-genesis-headers/README.md) records the sources, the date and the exact request.
The test hashes the headers with compiled `Sha256d`, checks all predecessor links and requires Core's genesis hash (D9).

It compares the median at each height with a table derived by hand.
The table includes the even counts at heights 1, 3, 5, 7 and 9.
It also requires chain acceptance at heights 1–12: each header time is greater than the median of its predecessor.
The genesis hash anchors only height 0, so the provenance of heights 1–12 relies on the two sources.

The test also reads the 312 mainnet headers at heights 144719–145030.
It requires `shortView` for the 10 predecessors with fewer than 11 entries in the view, and chain acceptance for the 301 candidates from 144730.
Four windows have times out of order, so that the median differs from the time of the sixth entry.
The test compares those four medians with heights derived by hand.
Thirteen synthetic cases cover even counts, times out of order, equal times, the UInt32 bounds and each adapter error, with hand-derived results.
These checks do not run Core or prove equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `sortedTimes_perm`, `sortedTimes_sorted`, `length_sortedTimes`, `medianTimePast_nil`, `medianTimePast_invalid` |
| `propext`, `Classical.choice`, `Quot.sound` | `medianTimeSpan_bounds`, `medianTimePast_short`, `medianTimePast_eq`, `medianTimePast_ok`, `medianTimePast_mem`, `medianTimePast_bounds`, `medianTimePast_rank`, `medianTimePast_congr_prefix` |

## Chain work

`blockProof` in `DogeLib.Work.ChainWork` specifies Core's `GetBlockProof` (D75, `src/chain.cpp` lines 150 to 163), design record 0008, stage 4.
It decodes `nBits` with `ArithUint256.setCompact`, and returns 0 when `SetCompact` reports a negative value or an overflow, or when the target is zero.
Otherwise it returns `(~t / (t + 1)) + 1`, with both additions modulo 2^256 (line 162).
`ArithUint256.complement` states `operator~` (D12, lines 69 to 75) as `2^256 - 1 - t`.
The model states each operation by its arithmetic result, as [compact encoding and difficulty retarget](#compact-encoding-and-difficulty-retarget) does, and has no word model.
Source review, not a theorem, connects these results to Core's word loops.

Core's division throws for a zero divisor, and `t + 1` is zero modulo 2^256 only for `t = 2^256 - 1`.
`blockProof` returns 0 in that branch.
`setCompact_value_ne_max` proves that no compact value decodes to `2^256 - 1`, so the branch is unreachable.

`IndexEntry.chainWork` holds Core's `nChainWork` (D18, line 183).
`addToBlockIndex` sets the chain work of a new entry to the predecessor's chain work plus `blockProof` of its `nBits`, modulo 2^256 (D33, line 2780).
Without a predecessor, it is `blockProof` alone, as Core adds the proof to 0.
An anchor holds a chain work that the caller supplies, and `WellFormed` does not constrain it.
So the chain work of an entry above an anchor counts only the headers above the anchor, plus the supplied value.
The model omits `pindexBestHeader` and its comparison of chain work (lines 2782 and 2783), design record 0008, decision 8.

The theorems hold for every compact value, network and context:

- `blockProof_eq` (`Work.Proofs.ChainWork`): if `SetCompact` reports no sign and no overflow and the target `t` is not zero, `blockProof` is `⌊2^256 / (t + 1)⌋`.
  Otherwise it is 0.
- `chainWork_add` (`Block.Proofs.HeaderSequence`): take a well-formed index, and let the step accept a hash that the index lacks, genesis or not.
  If the index has an entry under the header's `hashPrevBlock`, the new entry links to it.
  Its chain work is then that entry's chain work plus `blockProof` of `nBits`, modulo 2^256.
  Otherwise the new entry has no predecessor, and its chain work is `blockProof` of `nBits`.
- `accept_ok_addToBlockIndex`: an acceptance of a hash that the index lacks returns `addToBlockIndex` of the input index.
- `accept_genesis_insert`, `accept_genesis_parent`, `accept_ok_insert` and `addToBlockIndex_of_unknown` state the chain work of the inserted entry with its other fields.

These theorems establish the behaviour of DogeLib's definitions.
No theorem says that a supplied chain work is the value that a node holds.

`lake test` runs the compiled code:

- `blockProof` on 11 compact values with hand-derived expectations.
  They include the limits `0x1e0fffff` of mainnet and testnet and `0x207fffff` of regtest, and the mainnet genesis `nBits` `0x1e0ffff0`.
  They also include three other targets, a negative value and an overflow from D16, and three zero targets.
  `tests/KnownAnswers/Work.lean` records each derivation.
- The chain work of every added entry of the 34 regtest cases (D83).
  Each added entry has a block proof of 2, which the README derives.
  The version cases start from supplied anchor work, and in `version-upgraded-1351` the last entry wraps from 2^256 − 1 to 1.
- The genesis range from an empty index: the entry at height `h` has chain work `0x100010 * (h + 1)`.
- 300 mainnet headers from 144730: five sums of block proofs, computed with Python integers from the fixture's `nBits` fields.

These known-answer checks do not run Core.
The [header-sequence comparison](../oracle.md#header-sequence-comparison-evidence) supplies separate finite evidence from Core's `AcceptBlockHeader`.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` | `setCompact_value_ne_max` and `blockProof_eq` in `Work.Proofs.ChainWork`. `chainWork_add` and `accept_ok_addToBlockIndex` in `Block.Proofs.HeaderSequence` |
