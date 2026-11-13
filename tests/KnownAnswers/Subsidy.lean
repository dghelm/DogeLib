import DogeLib.Block
import KnownAnswers.Common

/-!
## Block subsidy

The expected values come from Dogecoin Core's unit tests at the pin and from the C++11 draft N3337.
None of them comes from DogeLib.

- `subsidy_first_100k_test`, `subsidy_100k_145k_test` and `subsidy_post_145k_test`: `src/test/dogecoin_tests.cpp`, lines 61 to 121 (SOURCES.md D105).
  The first two tests add each subsidy to a 256-bit number, and use that number as the next previous hash.
  They fix only the sum of the subsidies, so a wrong value at one height changes every later seed.
- Output number 10,000 of `mt19937` with the default seed: N3337, 26.5.5 [rand.predef], paragraph 3.
- The seed of the mainnet genesis hash: characters 7 to 13 of the hash text in D9, `src/chainparams.cpp` line 182, read by hand.
-/
namespace KnownAnswers.Subsidy
open DogeLib DogeLib.Block
open KnownAnswers.Block (require)

/-- Core's `ArithToUint256`: the 32 bytes of a number below `2^256`, least significant byte first. -/
def arithToUint256 (n : Nat) : Hash256 :=
  ⟨(List.range 32).map fun i => (n >>> (8 * i)).toUInt8, by simp⟩

/--
The loop of Core's two random-era tests, from height `first` to height `last`.
It returns the sum of the subsidies and the largest one, or `none` if a subsidy has no value.
-/
def chainedSum (first last : Nat) : Option (Nat × Nat) := Id.run do
  let mut prevHash := 0
  let mut sum := 0
  let mut largest := 0
  for nHeight in [first:last + 1] do
    match getDogecoinBlockSubsidy subsidyFuel nHeight (arithToUint256 prevHash) with
    | .error _ => return none
    | .ok subsidy =>
      sum := sum + subsidy
      largest := max largest subsidy
      prevHash := prevHash + subsidy
  return some (sum, largest)

/-- Whether the subsidy at a height, with the oracle's fuel, is `expected` koinu. -/
def subsidyIs (nHeight : Nat) (prevHash : Hash256) (expected : Nat) : Bool :=
  match getDogecoinBlockSubsidy subsidyFuel nHeight prevHash with
  | .ok subsidy => subsidy == expected
  | .error _ => false

/-- Core's three subsidy tests, the N3337 generator value and the genesis seed. -/
def check : IO Nat := do
  let mut failures := 0
  -- subsidy_first_100k_test: lines 61 to 79.
  failures := failures + (← require "subsidy: first 100k sum and bound"
    (match chainedSum 0 100000 with
     | some (sum, largest) => sum == 54894174438 * coin && largest ≤ 1000000 * coin
     | none => false))
  -- subsidy_100k_145k_test: lines 81 to 99.
  failures := failures + (← require "subsidy: 100k to 145k sum and bound"
    (match chainedSum 100000 145000 with
     | some (sum, largest) => sum == 12349960000 * coin && largest ≤ 500000 * coin
     | none => false))
  -- subsidy_post_145k_test: lines 102 to 121, with the zero hash.
  let zero := arithToUint256 0
  failures := failures + (← require "subsidy: fixed schedule from 145000 to 599999"
    ((List.range (600000 - 145000)).all fun offset =>
      let nHeight := 145000 + offset
      subsidyIs nHeight zero ((500000 >>> (nHeight / 100000)) * coin)))
  failures := failures + (← require "subsidy: 10000 coins at 600000 and 700000"
    (subsidyIs 600000 zero (10000 * coin) && subsidyIs 700000 zero (10000 * coin)))
  failures := failures + (← require "mt19937: output 10000 of the default seed"
    ((Mt19937.seed 5489).output 9999 == 4123659995))
  let genesis := Hash256.ofDisplayBytes?
    [0x1a, 0x91, 0xe3, 0xda, 0xce, 0x36, 0xe2, 0xbe, 0x3b, 0xf0, 0x30, 0xa6, 0x56, 0x79, 0xfe, 0x82,
     0x1a, 0xa1, 0xd6, 0xef, 0x92, 0xe7, 0xc9, 0x90, 0x2e, 0xb3, 0x18, 0x18, 0x2c, 0x35, 0x56, 0x91]
  failures := failures + (← require "subsidy: seed of the genesis hash"
    (genesis.map subsidySeed == some 0xace36e2))
  if failures == 0 then
    IO.println "subsidy: Core's 3 subsidy tests, 1 generator value and 1 seed agree"
  return failures

end KnownAnswers.Subsidy

/-- Named checks for the test driver. -/
def KnownAnswers.Subsidy.checks : List (String × IO Nat) := [
  ("subsidy", KnownAnswers.Subsidy.check)
]
