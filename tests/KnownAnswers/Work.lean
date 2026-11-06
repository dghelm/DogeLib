import DogeLib.Work
import KnownAnswers.Common

/-!
## Difficulty retarget

The six `get_next_work_*` cases come from Dogecoin Core `e0a1c15`, `src/test/dogecoin_tests.cpp` (SOURCES.md, D7).
They run through the arithmetic retarget and both word entry points.
Each case gives the last block's height, time and `nBits`, the first block time, the parameter set, and the expected `nBits`.
The inputs and the expected values are copied from the test file, with the line of each value.

## Compact encoding

The `bignum_SetCompact` cases come from `src/test/arith_uint256_tests.cpp` at the same commit (SOURCES.md, D16).
They run through the arithmetic and word compact models.
Each case gives the compact input, the value that `GetHex` shows, the expected `GetCompact` result and the two flags.
-/

namespace KnownAnswers.Work

open DogeLib.Work

/-- Eight lowercase hexadecimal digits of a 32-bit value. -/
def hex32 (n : UInt32) : String :=
  let digits := Nat.toDigits 16 n.toNat
  "0x" ++ String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- One `get_next_work_*` case of `dogecoin_tests.cpp`. -/
structure RetargetCase where
  /-- The name of the Boost test case. -/
  name : String
  /-- The line of the `BOOST_CHECK_EQUAL` that states the expected value. -/
  line : Nat
  /-- The parameters that `Params().GetConsensus(h)` returns in the test. -/
  params : RetargetParams
  /-- `pindexLast.nHeight + 1`, the height of the next block. -/
  nHeight : Int32
  /-- `pindexLast.nTime`. -/
  nLastBlockTime : Int64
  /-- `nLastRetargetTime`, the time of the first block. -/
  nFirstBlockTime : Int64
  /-- `pindexLast.nBits`. -/
  nBits : UInt32
  /-- The expected result. -/
  expected : UInt32

/-- The six `get_next_work_*` cases of `src/test/dogecoin_tests.cpp` at `e0a1c15`.
`GetConsensus(0)` is `mainnetParams`, and `GetConsensus(145000)` is `mainnetDigishieldParams`. -/
def retargetCases : Array RetargetCase := #[
  -- Lines 123-135: GetConsensus(0), nLastRetargetTime 1386474927, nHeight 239.
  { name := "get_next_work_difficulty_limit", line := 134, params := mainnetParams,
    nHeight := 239 + 1, nLastBlockTime := 1386475638, nFirstBlockTime := 1386474927,
    nBits := 0x1e0ffff0, expected := 0x1e00ffff },
  -- Lines 137-149: GetConsensus(0), nLastRetargetTime 1386942008, nHeight 9599.
  { name := "get_next_work_pre_digishield", line := 148, params := mainnetParams,
    nHeight := 9599 + 1, nLastBlockTime := 1386954113, nFirstBlockTime := 1386942008,
    nBits := 0x1c1a1206, expected := 0x1c15ea59 },
  -- Lines 151-164: GetConsensus(145000), nLastRetargetTime 1395094427, nHeight 145000.
  { name := "get_next_work_digishield", line := 163, params := mainnetDigishieldParams,
    nHeight := 145000 + 1, nLastBlockTime := 1395094679, nFirstBlockTime := 1395094427,
    nBits := 0x1b499dfd, expected := 0x1b671062 },
  -- Lines 166-179: GetConsensus(145000), nLastRetargetTime 1395100835, nHeight 145107.
  { name := "get_next_work_digishield_modulated_upper", line := 178, params := mainnetDigishieldParams,
    nHeight := 145107 + 1, nLastBlockTime := 1395101360, nFirstBlockTime := 1395100835,
    nBits := 0x1b3439cd, expected := 0x1b4e56b3 },
  -- Lines 181-194: GetConsensus(145000), nLastRetargetTime 1395380517, nHeight 149423.
  -- The first block time is after the last, so the actual timespan is negative.
  { name := "get_next_work_digishield_modulated_lower", line := 193, params := mainnetDigishieldParams,
    nHeight := 149423 + 1, nLastBlockTime := 1395380447, nFirstBlockTime := 1395380517,
    nBits := 0x1b446f21, expected := 0x1b335358 },
  -- Lines 196-210: GetConsensus(145000), nLastRetargetTime 1395094679, nHeight 145001.
  { name := "get_next_work_digishield_rounding", line := 209, params := mainnetDigishieldParams,
    nHeight := 145001 + 1, nLastBlockTime := 1395094727, nFirstBlockTime := 1395094679,
    nBits := 0x1b671062, expected := 0x1b6558a4 }
]

/-- Runs every retarget case, and checks that there are six.
Returns the number of failures. -/
def checkRetarget : IO Nat := do
  let mut failures := 0
  if retargetCases.size != 6 then
    IO.eprintln s!"FAIL dogecoin_tests.cpp: {retargetCases.size} retarget cases, expected 6"
    failures := failures + 1
  for c in retargetCases do
    let got := calculateDogecoinNextWorkRequired c.params c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    let wordGot := calculateDogecoinNextWorkRequiredWords c.params c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    let byteGot := (ArithUint256.targetBytesOfHex ArithUint256.mainnetPowLimitHex).bind fun limit =>
      calculateDogecoinNextWorkRequiredBytes c.params limit c.nHeight c.nLastBlockTime c.nFirstBlockTime c.nBits
    if got != c.expected || wordGot != some c.expected || byteGot != some c.expected then
      IO.eprintln s!"FAIL dogecoin_tests.cpp:{c.line} {c.name}: got {hex32 got}, words {wordGot}, bytes {byteGot}, expected {hex32 c.expected}"
      failures := failures + 1
  IO.println s!"dogecoin_tests.cpp get_next_work_*: {retargetCases.size} cases, {failures} failures"
  return failures

/-- One step of `bignum_SetCompact` in `arith_uint256_tests.cpp`. -/
structure CompactCase where
  /-- The line of the `SetCompact` call, or of the assignment for the case without one. -/
  line : Nat
  /-- The input: a compact for `SetCompact`, or `none` when the test assigns `value` directly. -/
  nCompact : Option UInt32
  /-- The value that `GetHex` shows, or `none` when the test does not check it. -/
  value : Option Nat
  /-- The argument that the test passes to `GetCompact`. -/
  negativeArgument : Bool
  /-- The expected `GetCompact` result, or `none` when the test does not check it. -/
  compact : Option UInt32
  /-- The expected `*pfNegative`, or `none` without a `SetCompact` call. -/
  fNegative : Option Bool
  /-- The expected `*pfOverflow`, or `none` without a `SetCompact` call. -/
  fOverflow : Option Bool

/-- Every step of `bignum_SetCompact`, lines 412-538 of `src/test/arith_uint256_tests.cpp` at `e0a1c15`. -/
def compactCases : Array CompactCase := #[
  ⟨417, some 0x00000000, some 0, false, some 0, some false, some false⟩,
  ⟨423, some 0x00123456, some 0, false, some 0, some false, some false⟩,
  ⟨429, some 0x01003456, some 0, false, some 0, some false, some false⟩,
  ⟨435, some 0x02000056, some 0, false, some 0, some false, some false⟩,
  ⟨441, some 0x03000000, some 0, false, some 0, some false, some false⟩,
  ⟨447, some 0x04000000, some 0, false, some 0, some false, some false⟩,
  ⟨453, some 0x00923456, some 0, false, some 0, some false, some false⟩,
  ⟨459, some 0x01803456, some 0, false, some 0, some false, some false⟩,
  ⟨465, some 0x02800056, some 0, false, some 0, some false, some false⟩,
  ⟨471, some 0x03800000, some 0, false, some 0, some false, some false⟩,
  ⟨477, some 0x04800000, some 0, false, some 0, some false, some false⟩,
  ⟨483, some 0x01123456, some 0x12, false, some 0x01120000, some false, some false⟩,
  -- Line 490 assigns `num = 0x80` with no `SetCompact` call.
  ⟨490, none, some 0x80, false, some 0x02008000, none, none⟩,
  ⟨493, some 0x01fedcba, some 0x7e, true, some 0x01fe0000, some true, some false⟩,
  ⟨499, some 0x02123456, some 0x1234, false, some 0x02123400, some false, some false⟩,
  ⟨505, some 0x03123456, some 0x123456, false, some 0x03123456, some false, some false⟩,
  ⟨511, some 0x04123456, some 0x12345600, false, some 0x04123456, some false, some false⟩,
  ⟨517, some 0x04923456, some 0x12345600, true, some 0x04923456, some true, some false⟩,
  ⟨523, some 0x05009234, some 0x92340000, false, some 0x05009234, some false, some false⟩,
  ⟨529, some 0x20123456,
    some 0x1234560000000000000000000000000000000000000000000000000000000000, false,
    some 0x20123456, some false, some false⟩,
  ⟨535, some 0xff123456, none, false, none, some false, some true⟩
]

/-- Runs every compact case, and checks that there are twenty-one.
Returns the number of failures. -/
def checkCompact : IO Nat := do
  let mut failures := 0
  if compactCases.size != 21 then
    IO.eprintln s!"FAIL arith_uint256_tests.cpp: {compactCases.size} compact cases, expected 21"
    failures := failures + 1
  for c in compactCases do
    let (value, flags) := match c.nCompact with
      | some n =>
        let r := ArithUint256.setCompact n
        (r.value, some (r.fNegative, r.fOverflow))
      | none => (ArithUint256.ofNat (c.value.getD 0), none)
    let (wordValue, wordFlags) := match c.nCompact with
      | some n =>
        let r := ArithUint256.Words.setCompact n
        (r.value, some (r.fNegative, r.fOverflow))
      | none => (ArithUint256.Words.ofUInt64 (UInt64.ofNat (c.value.getD 0)), none)
    let mut ok := true
    if let some v := c.value then
      if value.val != v || ArithUint256.Words.value wordValue != v then ok := false
    if let some e := c.compact then
      if ArithUint256.getCompact value c.negativeArgument != e ||
          ArithUint256.Words.getCompact wordValue c.negativeArgument != e then ok := false
    if let some (neg, ovf) := flags then
      if c.fNegative != some neg || c.fOverflow != some ovf then ok := false
    if let some (neg, ovf) := wordFlags then
      if c.fNegative != some neg || c.fOverflow != some ovf then ok := false
    if !ok then
      IO.eprintln s!"FAIL arith_uint256_tests.cpp:{c.line}: value {value.val}, flags {flags}, word value {ArithUint256.Words.value wordValue}, word flags {wordFlags}"
      failures := failures + 1
  IO.println s!"arith_uint256_tests.cpp bignum_SetCompact: {compactCases.size} cases, {failures} failures"
  return failures


/-!
### Operators: `multiply`, `divide` and `GetLow64`

The cases of `arith_uint256_tests.cpp` (D16) that use the operators the retarget uses: `operator*` by a 32-bit value, `operator/` and `GetLow64`.
The inputs and expected values are copied from the test file, with the line of each case.
The multiply, nonzero divide and `GetLow64` cases run through both the arithmetic and word models.
Two `divide` cases, lines 362 and 368, expect `uint_error` for a zero divisor.
The word model returns `none` for these `BOOST_CHECK_THROW` expectations.
-/

/-- The value of a string of hexadecimal digits, or `none` for another character. -/
def hexNat? (s : String) : Option Nat :=
  s.toList.foldlM (init := 0) fun acc c => (KnownAnswers.Sha256Cavp.hexDigit? c).map (acc * 16 + ·.toNat)

/-- `R1L` of `arith_uint256_tests.cpp` lines 25 to 30: `R1Array` read as a little-endian number, which is `R1ArrayHex`. -/
def r1Hex : String := "7d1de5eaf9b156d53208f033b5aa8122d2d2355d5e12292b121156cfdb4a529c"

/-- `R2L`, lines 33 to 36: `R2Array` read as a little-endian number. The digits are the bytes of `R2Array` from last to first. -/
def r2Hex : String := "d781cab4f072134971da2d19a3473013bfb69ca6c30a7e26406ba5477c1d3270"

/-- `MaxL`, lines 50 to 53: every bit set. -/
def maxHex : String := "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"

/-- `D1L` and `D2L` of the `divide` test, lines 355 and 356. -/
def d1Hex : String := "ad7133ac1977fa2b7"
def d2Hex : String := "ecd751716"

/-- The value of `a / b` by `ArithUint256.div`, or `none` for a zero divisor. -/
def divide? (a b : ArithUint256) : Option ArithUint256 :=
  if h : b.val ≠ 0 then some (ArithUint256.div a b h) else none

/-- The operator cases, each with its line in `arith_uint256_tests.cpp` and whether it holds. -/
def operatorCases : Except String (List (Nat × Bool)) := do
  let num (s : String) : Except String ArithUint256 :=
    match hexNat? s with
    | some n => pure (ArithUint256.ofNat n)
    | none => throw s!"bad hex {s}"
  let r1 ← num r1Hex
  let r2 ← num r2Hex
  let mx ← num maxHex
  let d1 ← num d1Hex
  let d2 ← num d2Hex
  let one := ArithUint256.ofNat 1
  let zero := ArithUint256.ofNat 0
  let is (a : ArithUint256) (s : String) : Except String Bool := do return a == (← num s)
  let wordDivide (a b : ArithUint256) : Option ArithUint256 :=
    (ArithUint256.Words.divide (ArithUint256.Words.ofArith a) (ArithUint256.Words.ofArith b)).map ArithUint256.Words.toArith
  let divIs (a b : ArithUint256) (c : ArithUint256) : Bool :=
    divide? a b == some c && wordDivide a b == some c
  return [
    (347, ArithUint256.mulUInt32 r1 0 == zero),
    (348, ArithUint256.mulUInt32 r1 1 == r1),
    (349, ← is (ArithUint256.mulUInt32 r1 3) "7759b1c0ed14047f961ad09b20ff83687876a0181a367b813634046f91def7d4"),
    (350, ← is (ArithUint256.mulUInt32 r2 0x87654321) "23f7816e30c4ae2017257b7a0fa64d60402f5234d46e746b61c960d09a26d070"),
    (357, divIs r1 d1 (← num "00000000000000000b8ac01106981635d9ed112290f8895545a7654dde28fb3a")),
    (358, divIs r1 d2 (← num "000000000873ce8efec5b67150bad3aa8c5fcb70e947586153bf2cec7c37c57a")),
    (359, divIs r1 one r1),
    (360, divIs r1 mx zero),
    (361, divIs mx r1 (ArithUint256.ofNat 2)),
    (362, wordDivide r1 zero == none),
    (363, divIs r2 d1 (← num "000000000000000013e1665895a1cc981de6d93670105a6b3ec3b73141b3a3c5")),
    (364, divIs r2 d2 (← num "000000000e8f0abe753bb0afe2e9437ee85d280be60882cf0bd1aaf7fa3cc2c4")),
    (365, divIs r2 one r2),
    (366, divIs r2 mx zero),
    (367, divIs mx r2 one),
    (368, wordDivide r2 zero == none),
    (394, ArithUint256.getLow64 r1 == 0x121156cfdb4a529c),
    (395, ArithUint256.getLow64 (ArithUint256.shiftLeft one 255) == 0),
    (396, ArithUint256.getLow64 one == 1),
    (347, ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 0) == zero),
    (348, ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 1) == r1),
    (349, ← is (ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r1) 3))
      "7759b1c0ed14047f961ad09b20ff83687876a0181a367b813634046f91def7d4"),
    (350, ← is (ArithUint256.Words.toArith (ArithUint256.Words.mulUInt32 (ArithUint256.Words.ofArith r2) 0x87654321))
      "23f7816e30c4ae2017257b7a0fa64d60402f5234d46e746b61c960d09a26d070"),
    (394, (ArithUint256.Words.getLow64 (ArithUint256.Words.ofArith r1)).toNat == 0x121156cfdb4a529c),
    (395, (ArithUint256.Words.getLow64
      (ArithUint256.Words.shiftLeft (ArithUint256.Words.ofArith one) 255)).toNat == 0),
    (396, (ArithUint256.Words.getLow64 (ArithUint256.Words.ofArith one)).toNat == 1)]

/-- Every operator case. Returns the number of failures. -/
def checkOperators : IO Nat := do
  match operatorCases with
  | .error e =>
    IO.eprintln s!"FAIL arith_uint256_tests.cpp operators: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (line, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL arith_uint256_tests.cpp:{line}"
        failures := failures + 1
    IO.println s!"arith_uint256_tests.cpp multiply, divide, GetLow64: {cs.length} cases, {failures} failures"
    return failures

/-!
### Next-work selection

Parameter expectations come from D14 at `e0a1c15`: mainnet lines 88-95 and 126-141,
testnet lines 233-251 and 282-306, regtest lines 392-397 and 425-437.
Synthetic branch fixtures follow D17 lines 32-88 and D6 lines 26-39.
They are source-derived examples, not observed historical headers or a Core comparison.
-/

/-- Compares the full result, including finite-view error categories. -/
private instance : BEq (Except NextWorkError UInt32) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => decide (x = y)
    | _, _ => false

/-- Synthetic view entry. Times and compact targets are supplied without header validation. -/
def workEntry (height : Nat) (time bits : UInt32) : BlockIndex := ⟨height, time, bits⟩

/-- Parameter fields fixed independently by Core's network records (D14).
The tuple is timespan, spacing, DigiShield calculation flag, minimum-difficulty permission and compact limit. -/
def workFields (network : WorkNetwork) (height : UInt32) : Int × Nat × Bool × Bool × UInt32 :=
  let p := getConsensus network height
  (p.nPowTargetTimespan.toInt, p.nPowTargetSpacing, p.fDigishieldDifficultyCalculation,
    p.fPowAllowMinDifficultyBlocks, ArithUint256.getCompact p.powLimit)

/-- Boundary examples from the effective heights in D14, including records whose work fields repeat. -/
def parameterCases : List (String × Bool) :=
  let mainLegacy := (14400, 60, false, false, 0x1e0fffff)
  let mainDigi := (60, 60, true, false, 0x1e0fffff)
  let testLegacy := (14400, 60, false, true, 0x1e0fffff)
  let testMin := (60, 60, true, true, 0x1e0fffff)
  let regLegacy := (14400, 1, false, true, 0x207fffff)
  let regDigi := (1, 1, true, true, 0x207fffff)
  [("main genesis fields", workFields .mainnet 0 == mainLegacy),
   ("main 144999", workFields .mainnet 144999 == mainLegacy),
   ("main 145000", workFields .mainnet 145000 == mainDigi),
   ("main 145001", workFields .mainnet 145001 == mainDigi),
   ("main 371336", workFields .mainnet 371336 == mainDigi),
   ("main 371337", workFields .mainnet 371337 == mainDigi),
   ("main 371338", workFields .mainnet 371338 == mainDigi),
   ("test 144999", workFields .testnet 144999 == testLegacy),
   ("test 145000", workFields .testnet 145000 == mainDigi),
   ("test 145001", workFields .testnet 145001 == mainDigi),
   ("test 157499", workFields .testnet 157499 == mainDigi),
   ("test 157500", workFields .testnet 157500 == testMin),
   ("test 157501", workFields .testnet 157501 == testMin),
   ("test 158099", workFields .testnet 158099 == testMin),
   ("test 158100", workFields .testnet 158100 == testMin),
   ("test 158101", workFields .testnet 158101 == testMin),
   ("regtest 9", workFields .regtest 9 == regLegacy),
   ("regtest 10", workFields .regtest 10 == regDigi),
   ("regtest 11", workFields .regtest 11 == regDigi),
   ("regtest 19", workFields .regtest 19 == regDigi),
   ("regtest 20", workFields .regtest 20 == regDigi),
   ("regtest 21", workFields .regtest 21 == regDigi),
   ("main UInt32 maximum", workFields .mainnet 0xffffffff == mainDigi),
   ("test UInt32 maximum", workFields .testnet 0xffffffff == testMin),
   ("regtest UInt32 maximum", workFields .regtest 0xffffffff == regDigi)]

/-- Synthetic inputs fixed by the return statements and strict comparisons of D17 and D6.
Malformed and truncated inputs check the finite-view adapter, not Core rejection codes. -/
def nextWorkCases : List (String × Bool) :=
  let legacy := testnetWorkParams
  let minParams := testnetMinDifficultyWorkParams
  let e := workEntry
  [("main genesis", nextWorkRequired .mainnet [] 0 == .ok 0x1e0fffff),
   ("test genesis", nextWorkRequired .testnet [] 0 == .ok 0x1e0fffff),
   ("regtest genesis", nextWorkRequired .regtest [] 0 == .ok 0x207fffff),
   -- D17 lines 50-53: threshold uses previous height.
   ("local interval 144999", retargetInterval mainnetWorkParams 144999 == 240),
   ("local interval 145000", retargetInterval mainnetWorkParams 145000 == 1),
   ("local interval 145001", retargetInterval mainnetWorkParams 145001 == 1),
   ("record interval stays 240", mainnetWorkParams.difficultyAdjustmentInterval == 240),
   ("first interval lookback", blocksToGoBack 240 239 == 239),
   ("later interval lookback", blocksToGoBack 240 479 == 240),
   ("main copies compact verbatim", nextWorkRequired .mainnet [e 1 100 0x04923456] 101 == .ok 0x04923456),
   -- D17 lines 54-73: equality is not a delay, and boundary stops recovery.
   ("legacy equal delay", nextWorkRequired .testnet [e 1 100 0x1c123456] 220 == .ok 0x1c123456),
   ("legacy delayed", nextWorkRequired .testnet [e 1 100 0x1c123456] 221 == .ok 0x1e0fffff),
   ("recovery nonminimum", nextWorkRequired .testnet
      [e 3 100 0x1e0fffff, e 2 90 0x1e0fffff, e 1 80 0x1c123456] 101 == .ok 0x1c123456),
   ("recovery interval boundary", nextWorkRequired .testnet
      [e 241 100 0x1e0fffff, e 240 90 0x1e0fffff, e 239 80 0x1c123456] 101 == .ok 0x1e0fffff),
   ("recovery genesis", nextWorkRequired .testnet
      [e 1 100 0x1e0fffff, e 0 90 0x1e0fffff] 101 == .ok 0x1e0fffff),
   ("recovery missing history", nextWorkRequired .testnet [e 1 100 0x1e0fffff] 101 == .error .missingAncestor),
   -- D6 lines 29-38: independent previous-height and permission checks.
   ("DigiShield previous 157499", !allowDigishieldMinDifficultyForBlock minParams (e 157499 100 0) 221),
   ("DigiShield previous 157500", allowDigishieldMinDifficultyForBlock minParams (e 157500 100 0) 221),
   ("DigiShield previous 157501", allowDigishieldMinDifficultyForBlock minParams (e 157501 100 0) 221),
   ("DigiShield equal delay", !allowDigishieldMinDifficultyForBlock minParams (e 157500 100 0) 220),
   ("DigiShield permission false", !allowDigishieldMinDifficultyForBlock testnetDigishieldWorkParams (e 157500 100 0) 221),
   ("test candidate 157500 still retargets", nextWorkRequired .testnet [e 157499 100 0x1c123456] 221 == .error .missingAncestor),
   ("test candidate 157501 minimum", nextWorkRequired .testnet [e 157500 100 0x1c123456] 221 == .ok 0x1e0fffff),
   ("DigiShield equality needs ancestor", nextWorkRequired .testnet [e 157500 100 0x1c123456] 220 == .error .missingAncestor),
   ("activation candidate 145000 needs ancestor", nextWorkRequired .mainnet [e 144999 100 0] 101 == .error .missingAncestor),
   ("main missing retarget ancestor", nextWorkRequired .mainnet [e 239 100 0] 101 == .error .missingAncestor),
   -- Regtest's fPowNoRetargeting is true, but this caller ignores it (D17 line 87).
   -- With T=1 and actual timespan=1, D6 returns the old compact.
   ("regtest retarget at 10", nextWorkRequired .regtest [e 9 100 0x1c123456, e 8 99 0] 101 == .ok 0x1c123456),
   -- D16 bignum_SetCompact lines 511-521: the signed and unsigned forms
   -- decode to the same value, whose unsigned GetCompact is 0x04123456.
   ("regtest ignores no-retarget flag and normalizes compact", nextWorkRequired .regtest
      [e 9 100 0x04923456, e 8 99 0] 101 == .ok 0x04123456),
   ("regtest delayed before retarget", nextWorkRequired .regtest [e 1 100 0x1c123456] 103 == .ok 0x207fffff),
   ("regtest maximum widened time", nextWorkRequired .regtest [e 1 0xffffffff 0x1c123456] 0xffffffff == .ok 0x1c123456),
   ("inconsistent view", nextWorkRequired .mainnet [e 2 100 0, e 0 90 0] 101 == .error .inconsistentHeights),
   ("maximum accepted previous height", nextWorkRequired .mainnet
      [e 2147483646 100 0x1c123456, e 2147483645 40 0] 0 == .ok 0x1c123456),
   ("height overflow", nextWorkRequired .mainnet [e 2147483647 100 0] 101 == .error .heightOutOfRange),
   ("genesis with predecessor", nextWorkRequired .mainnet [e 0 100 0, e 0 90 0] 101 == .error .inconsistentHeights),
   ("zero custom interval", getNextWorkRequired { legacy with nPowTargetSpacing := 20000 }
      [e 1 100 0] 101 == .error .zeroInterval)]

/-- Synthetic contiguous windows with the six pinned D7 arithmetic inputs.
The first and last timestamps and expected compact are from the cited test.
Intermediate timestamps and heights provide context for the caller and make no historical claim. -/
def callerRetargetCases : List (String × Bool) :=
  retargetCases.toList.map fun c =>
    let height := c.nHeight.toInt.toNat - 1
    let back := if height = 239 then 239 else if height < 145000 then 240 else 1
    let view := (List.range (back + 1)).map fun i =>
      workEntry (height - i)
        (UInt32.ofNat (if i = back then c.nFirstBlockTime.toInt.toNat else c.nLastBlockTime.toInt.toNat)) c.nBits
    (s!"caller {c.name}", nextWorkRequired .mainnet view 0 == .ok c.expected)

/-- Runs the source-derived next-work examples and pinned retarget answers through the caller. -/
def checkNextWork : IO Nat := do
  let cases := parameterCases ++ nextWorkCases ++ callerRetargetCases
  let mut failures := 0
  for (name, ok) in cases do
    if !ok then
      IO.eprintln s!"FAIL next work: {name}"
      failures := failures + 1
  IO.println s!"next-work selection: {cases.length} cases, {failures} failures"
  return failures

/-!
### Supplied-hash proof of work

These synthetic known answers derive from D17, `src/pow.cpp` lines 124-129 at `e0a1c15`.
`0x03000100` decodes to 256, so little-endian hashes 255 and 256 pass and 257 fails.
`0x04000001` also decodes to 256, despite its noncanonical encoding.

The custom limit of 256 isolates equality and the above-limit branch.
The full 256-bit limit isolates overflow even when the wrapped target is nonzero and below the limit.
`0x22000101` encodes `257 * 2^248`, which wraps to `2^248` and reports overflow.
These expectations follow from the source's arithmetic and comparisons, not this implementation's output.

Core's `src/test/pow_tests.cpp` has no direct `CheckProofOfWork` cases at this pin.
`src/test/auxpow_tests.cpp` lines 333-355 mines both passing and failing scrypt digests at runtime.
Those tests supply no fixed digest to copy here.
The cases below do not compute scrypt or run Core.
-/

/-- Synthetic internal-order hash with two explicit low bytes and thirty zero bytes. -/
def lowHash (lo hi : UInt8) : DogeLib.Hash256 :=
  ⟨[lo, hi] ++ List.replicate 30 0, by simp⟩

/-- Source-derived branch and boundary cases for the supplied-hash check. -/
def proofOfWorkCases : List (String × Bool) :=
  let params := mainnetParams
  let exactLimit := { params with powLimit := ArithUint256.ofNat 256 }
  let fullLimit := { params with powLimit := ArithUint256.ofNat (2 ^ 256 - 1) }
  [("zero target", !validProofOfWorkTarget 0 params),
   ("shifted zero mantissa", !validProofOfWorkTarget 0x01000001 params),
   ("signed shifted zero", !validProofOfWorkTarget 0x01800001 params),
   ("negative target", !validProofOfWorkTarget 0x03800100 params),
   ("overflow with zero wrapped target", !validProofOfWorkTarget 0x23000001 params),
   ("overflow with nonzero wrapped target", !validProofOfWorkTarget 0x22000101 fullLimit),
   ("above mainnet limit", !validProofOfWorkTarget 0x1f00ffff params),
   ("target equals custom limit", validProofOfWorkTarget 0x03000100 exactLimit),
   ("target exceeds custom limit", !validProofOfWorkTarget 0x03000100
      { params with powLimit := ArithUint256.ofNat 255 }),
   ("zero hash accepted", checkProofOfWork DogeLib.Hash256.zero 0x03000100 params),
   ("hash below target", checkProofOfWork (lowHash 255 0) 0x03000100 params),
   ("hash equals target", checkProofOfWork (lowHash 0 1) 0x03000100 params),
   ("hash above target", !checkProofOfWork (lowHash 1 1) 0x03000100 params),
   ("reversed equality bytes fail", !checkProofOfWork
      ⟨List.replicate 30 0 ++ [1, 0], by decide⟩ 0x03000100 params),
   ("noncanonical positive target accepted", checkProofOfWork (lowHash 0 1) 0x04000001 params),
   ("zero hash cannot rescue negative target", !checkProofOfWork DogeLib.Hash256.zero 0x03800100 params),
   ("zero hash cannot rescue overflow", !checkProofOfWork DogeLib.Hash256.zero 0x22000101 fullLimit),
   ("zero hash cannot rescue zero target", !checkProofOfWork DogeLib.Hash256.zero 0 params),
   ("zero hash cannot rescue above-limit target", !checkProofOfWork DogeLib.Hash256.zero 0x1f00ffff params),
   ("mainnet genesis target in range", validProofOfWorkTarget 0x1e0ffff0 params)]

/-- Runs the supplied-hash check on source-derived known answers and returns the failure count. -/
def checkProofOfWorkCases : IO Nat := do
  let mut failures := 0
  for (name, ok) in proofOfWorkCases do
    if !ok then
      IO.eprintln s!"FAIL proof of work: {name}"
      failures := failures + 1
  IO.println s!"proof-of-work check: {proofOfWorkCases.length} cases, {failures} failures"
  return failures

/-!
### Mainnet headers

The raw fixture and its Electrum provenance are in `tests/work/mainnet-headers/README.md`.
D10 fixes the 80-byte layout.
D9 fixes checkpoint 145000 at Core `e0a1c15`.
The checkpoint anchors its ancestors, but does not authenticate later headers.
These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.
-/

namespace MainnetHeaders

open DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- One pure header, with the int32 version's bits preserved as UInt32.
The fixture height is separate from the 80 serialized bytes (D10). -/
structure Header where
  height : Nat
  versionBits : UInt32
  prev : DogeLib.Hash256
  merkleRoot : DogeLib.Hash256
  time : UInt32
  bits : UInt32
  nonce : UInt32
  digest : ByteArray

/-- Parses all six D10 fields, consumes exactly 80 bytes and hashes those bytes with Sha256d. -/
def parseHeader (height : Nat) (hex : String) : Except String Header := do
  let bytes ← parseHex hex
  if bytes.size != 80 then throw s!"height {height}: expected 80 bytes, got {bytes.size}"
  let some ((version, prev, merkle, time, bits, nonce), rest) :=
      Codec.decode (α := UInt32 × DogeLib.Hash256 × DogeLib.Hash256 × UInt32 × UInt32 × UInt32) bytes.toList
    | throw s!"height {height}: cannot decode header"
  if !rest.isEmpty then throw s!"height {height}: trailing header bytes"
  return ⟨height, version, prev, merkle, time, bits, nonce,
    DogeLib.Cryptography.Hash.Sha256d.hash bytes⟩

/-- Requires exactly the fixture's 312 consecutive heights, so missing records cannot reduce the checks. -/
def parseHeaders (text : String) : Except String (Array Header) := do
  let mut headers := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [heightText, hex] := line.splitOn " " | throw "expected height and header hex"
    let some height := heightText.toNat? | throw s!"bad height: {heightText}"
    if height != 144719 + headers.size then throw s!"unexpected height: {height}"
    headers := headers.push (← parseHeader height hex)
  if headers.size != 312 then throw s!"expected 312 headers, got {headers.size}"
  return headers

/-- Checks every target range, hash link, checkpoint 145000 and next-work result with sufficient prior history.
Only the initial context header and the incomplete retarget at 144720 lack known answers. -/
def check : IO Nat := do
  let headers ← match parseHeaders (← IO.FS.readFile "tests/work/mainnet-headers/headers.txt") with
    | .ok headers => pure headers
    | .error e =>
      IO.eprintln s!"FAIL mainnet headers: {e}"
      return 1
  let mut failures := 0
  let mut previous : Option Header := none
  let mut view : List BlockIndex := []
  let mut copies := 0
  let mut legacyRetargets := 0
  let mut digiRetargets := 0
  for header in headers do
    unless validProofOfWorkTarget header.bits (getConsensus .mainnet (UInt32.ofNat header.height)).toRetargetParams do
      IO.eprintln s!"FAIL mainnet target range {header.height}"
      failures := failures + 1
    if let some prev := previous then
      unless header.prev.val == prev.digest.toList do
        IO.eprintln s!"FAIL mainnet header {header.height}: predecessor hash"
        failures := failures + 1
    if header.height == 145000 then
      let display := toHex ⟨header.digest.toList.reverse.toArray⟩
      unless display == "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72" do
        IO.eprintln s!"FAIL mainnet checkpoint 145000: {display}"
        failures := failures + 1
    if header.height > 144719 then
      let got := nextWorkRequired .mainnet view header.time
      if header.height == 144720 then
        unless got == .error .missingAncestor do
          IO.eprintln s!"FAIL mainnet header 144720: expected missingAncestor, got {repr got}"
          failures := failures + 1
      else
        unless got == .ok header.bits do
          IO.eprintln s!"FAIL mainnet next work {header.height}: got {repr got}, expected {header.bits}"
          failures := failures + 1
        if header.height >= 145000 then digiRetargets := digiRetargets + 1
        else if header.height % 240 == 0 then legacyRetargets := legacyRetargets + 1
        else copies := copies + 1
    view := ⟨header.height, header.time, header.bits⟩ :: view
    previous := some header
  unless copies == 278 && legacyRetargets == 1 && digiRetargets == 31 do
    IO.eprintln "FAIL mainnet headers: unexpected branch counts"
    failures := failures + 1
  IO.println s!"mainnet headers: {headers.size} hashes, 311 links, checkpoint 145000; {failures} failures"
  IO.println s!"mainnet target validity: {headers.size} targets checked"
  IO.println s!"mainnet next work: {copies} legacy copies, {legacyRetargets} interval-240 retarget, {digiRetargets} DigiShield retargets"
  return failures

end MainnetHeaders

/-!
### Shifts

The byte helpers and cases below adapt `src/test/arith_uint256_tests.cpp` lines 125-197 at Core `e0a1c15` (D16).
The adaptation uses total byte lookup and natural shifts before truncation to a byte.
The expected bytes come from Core's byte helpers, independently of the arithmetic and word models.
This adapted section is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notice:

Copyright (c) 2011-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

/-- Core's byte-array left shift, lines 139-154, with zero for an absent byte. -/
def coreBytesLeft (bytes : List UInt8) (shift : Nat) : List UInt8 :=
  (List.range 32).map fun t =>
    if t ≥ shift / 8 then
      let f := t - shift / 8
      UInt8.ofNat (((bytes[f]?.getD 0).toNat <<< (shift % 8)) |||
        (if t ≥ shift / 8 + 1 then (bytes[f - 1]?.getD 0).toNat >>> (8 - shift % 8) else 0))
    else 0

/-- Core's byte-array right shift, lines 125-137, with zero for an absent byte. -/
def coreBytesRight (bytes : List UInt8) (shift : Nat) : List UInt8 :=
  (List.range 32).map fun t =>
    let f := t + shift / 8
    UInt8.ofNat (((bytes[f]?.getD 0).toNat >>> (shift % 8)) |||
      ((bytes[f + 1]?.getD 0).toNat <<< (8 - shift % 8)))

/-- Interpret Core's little-endian byte array as a natural number. -/
def coreBytesValue (bytes : List UInt8) : Nat := bytes.foldr (fun byte acc => byte.toNat + 256 * acc) 0

/-- Run Core's shift cases, lines 159-196, against the arithmetic and word models.
Extra word-loop cases at shifts of at least 256 expect zero from Core's index guards (D13 lines 30-33 and 47-50). -/
def checkShifts : IO Nat := do
  let some r1 := hexNat? r1Hex | throw (IO.userError "bad R1 hex")
  let some mx := hexNat? maxHex | throw (IO.userError "bad Max hex")
  let .ok r1Bytes := KnownAnswers.Sha256Cavp.parseHex r1Hex | throw (IO.userError "bad R1 bytes")
  let inputs := [(1, (1 : UInt8) :: List.replicate 31 0),
    (r1, r1Bytes.toList.reverse), (mx, List.replicate 32 (255 : UInt8))]
  let mut failures := 0
  let mut count := 0
  for shift in [:256] do
    for (input, bytes) in inputs do
      let a := ArithUint256.ofNat input
      let w := ArithUint256.Words.ofArith a
      let left := coreBytesValue (coreBytesLeft bytes shift)
      let right := coreBytesValue (coreBytesRight bytes shift)
      -- Core lines 162, 170, 175, 180 and 185 use the byte-array helpers.
      -- Core lines 165-167 use HalfL >> (255-i) = OneL << i.
      let checks := if input == 1 then
        [(162, (ArithUint256.shiftLeft a shift).val == left &&
          (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == left),
         (165, (ArithUint256.Words.toArith
            (ArithUint256.Words.shiftRight (ArithUint256.Words.ofArith (ArithUint256.ofNat (2 ^ 255))) (255 - shift))).val == left &&
          (ArithUint256.shiftRight (ArithUint256.ofNat (2 ^ 255)) (255 - shift)).val == left)]
        else
          [(if input == r1 then 170 else 180,
            (ArithUint256.shiftLeft a shift).val == left &&
              (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == left),
           (if input == r1 then 175 else 185,
            (ArithUint256.shiftRight a shift).val == right &&
              (ArithUint256.Words.toArith (ArithUint256.Words.shiftRight w shift)).val == right)]
      for (line, ok) in checks do
        count := count + 1
        unless ok do
          failures := failures + 1
          IO.eprintln s!"FAIL arith_uint256_tests.cpp:{line}, shift {shift}"
    -- Core lines 189-196 fix c1L and place c2L 128 bits higher.
    let c1 := ArithUint256.Words.ofArith (ArithUint256.ofNat 0x0123456789abcdef)
    let c2 := ArithUint256.Words.ofArith (ArithUint256.ofNat (0x0123456789abcdef * 2 ^ 128))
    let lhs := ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft c1 shift)
    let rhs := ArithUint256.Words.toArith (if shift < 128 then ArithUint256.Words.shiftRight c2 (128 - shift)
      else ArithUint256.Words.shiftLeft c2 (shift - 128))
    count := count + 1
    unless lhs == rhs do
      failures := failures + 1
      IO.eprintln s!"FAIL arith_uint256_tests.cpp:192/195, shift {shift}"
  for shift in [256, 257, 511, 512, 0xffffffff] do
    for (input, _) in inputs do
      let w := ArithUint256.Words.ofArith (ArithUint256.ofNat input)
      count := count + 2
      unless (ArithUint256.Words.toArith (ArithUint256.Words.shiftLeft w shift)).val == 0 &&
          (ArithUint256.Words.toArith (ArithUint256.Words.shiftRight w shift)).val == 0 do
        failures := failures + 1
        IO.eprintln s!"FAIL word shift at {shift}, expected zero"
  IO.println s!"arith_uint256_tests.cpp shifts and zero boundaries: {count} cases, {failures} failures"
  return failures

end KnownAnswers.Work

/-- Named checks for Work known answers, in alphabetical order. -/
def KnownAnswers.Work.checks : List (String × IO Nat) := [
  ("compact", KnownAnswers.Work.checkCompact),
  ("mainnetHeaders", KnownAnswers.Work.MainnetHeaders.check),
  ("nextWork", KnownAnswers.Work.checkNextWork),
  ("operators", KnownAnswers.Work.checkOperators),
  ("proofOfWork", KnownAnswers.Work.checkProofOfWorkCases),
  ("retarget", KnownAnswers.Work.checkRetarget),
  ("shifts", KnownAnswers.Work.checkShifts)
]
