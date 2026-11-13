module

public import DogeLib.Base.Bytes

/-!
# Block subsidy

Core's `GetDogecoinBlockSubsidy` with the mainnet parameter records, design record 0010, stage 0010a.
`ConnectBlock` adds its result to the fees to bound the coinbase value (SOURCES.md, D101, line 1996).
The sources are at the Core pin and at Boost 1.70.0 (SOURCES.md):

- `generateMTRandom` and `GetDogecoinBlockSubsidy`, `src/dogecoin.cpp` lines 16 to 21 and 127 to 149 (D104).
- `nSubsidyHalvingInterval` and `fSimplifiedRewards` of the mainnet records, `src/chainparams.cpp` lines 79 and 128 (D14), and `COIN`, `src/amount.h` line 18 (D104).
- `base_blob::GetHex`, `src/uint256.cpp` (D11).
- `boost::mt19937`, `boost/random/mersenne_twister.hpp` (B1).
- `boost::uniform_int<>`, `boost/random/uniform_int.hpp` and `boost/random/uniform_int_distribution.hpp` (B2).

Below height 145,000 the subsidy is random.
Core seeds a Mersenne Twister from seven hexadecimal digits of the previous block hash and takes one value of a Boost distribution.
That value follows Boost's algorithm, which Core's own text does not contain.
Another Boost release can give other values.
Core requires only Boost 1.60 or later, and the definitions below follow Boost 1.70.0, which the Core harness builds.

Boost's distribution draws again when it rejects a word, and this module has no proof that the draws end.
So `uniformInt` takes fuel, and `getDogecoinBlockSubsidy` returns the error `fuelExhausted` when the fuel runs out.

The module covers mainnet only.
It does not define the testnet or regtest records, and it does not model `ConnectBlock`.
The theorems are in `DogeLib.Block.Proofs.Subsidy`.

## Source

The adaptation follows the statements of Core and Boost in order.
Core's source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/dogecoin.cpp`:

Copyright (c) 2015-2022 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.

Boost is distributed under the Boost Software License, Version 1.0, with its text in `LICENSES/boost-BSL-1.0.txt`.
Original notice from `boost/random/mersenne_twister.hpp`:

Copyright Jens Maurer 2000-2001
Copyright Steven Watanabe 2010
Distributed under the Boost Software License, Version 1.0. (See
accompanying file LICENSE_1_0.txt or copy at
http://www.boost.org/LICENSE_1_0.txt)

Original notice from `boost/random/uniform_int_distribution.hpp`:

Copyright Jens Maurer 2000-2001
Copyright Steven Watanabe 2011
Distributed under the Boost Software License, Version 1.0. (See
accompanying file LICENSE_1_0.txt or copy at
http://www.boost.org/LICENSE_1_0.txt)
-/

@[expose] public section
namespace DogeLib.Block

/--
The state of `boost::mt19937` (B1, line 623): the words `x` and the position `i` of the next output.
The engine is `mersenne_twister_engine` with `w = 32`, `n = 624`, `m = 397` and `r = 31`.
`i` is at most `n`. At `n`, the next output first calls `twist`.
-/
structure Mt19937 where
  /-- The array `x` of `n = 624` words. -/
  x : Vector UInt32 624
  /-- The index `i` of the next word to temper. -/
  i : Nat
  /-- `i` never exceeds `n`. -/
  hi : i ≤ 624

namespace Mt19937

/-- The parameter `a` of `mt19937` (B1, line 623). -/
def a : UInt32 := 0x9908b0df

/-- `upper_mask` for `r = 31` (B1, lines 348 and 538): the top bit of a word. -/
def upperMask : UInt32 := 0x80000000

/-- `lower_mask` for `r = 31` (B1, lines 349 and 539): the 31 low bits of a word. -/
def lowerMask : UInt32 := 0x7fffffff

/--
Boost's `normalize_state` (B1, lines 346 to 363).
It replaces the 31 low bits of `x[0]`, which no output reads, with the bits that one backward step of the recurrence gives.
If every word is then zero, it sets `x[0]` to the top bit.
-/
def normalizeState (x : Vector UInt32 624) : Vector UInt32 624 :=
  let y0 := x[396] ^^^ x[623]
  let y0 := if y0 &&& upperMask != 0 then ((y0 ^^^ a) <<< 1) ||| 1 else y0 <<< 1
  let x := x.set 0 ((x[0] &&& upperMask) ||| (y0 &&& lowerMask))
  if x.toList.all (· == 0) then x.set 0 upperMask else x

/--
Boost's `seed(value)` (B1, lines 141 to 154), with `f = 1812433253`.
`x[0]` is the seed, and `x[k + 1]` is `f * (x[k] ^ (x[k] >> 30)) + (k + 1)` modulo `2^32`.
Then `normalize_state` runs, and `i` is `n`, so the first output calls `twist`.
-/
def seed (value : UInt32) : Mt19937 :=
  let x := Nat.fold 623 (fun k _ x =>
    x.set (k + 1) ((1812433253 : UInt32) * (x[k] ^^^ (x[k] >>> 30)) + (k + 1).toUInt32))
    ((Vector.replicate 624 0).set 0 value)
  ⟨normalizeState x, 624, Nat.le_refl 624⟩

/--
Boost's `twist` (B1, lines 536 to 574): one in-place pass over the 624 words, in ascending order of `j`.
Boost splits the pass into four loops and a last step, so that no index needs a modulo operation.
Each of them performs the step below, with `x[(j + 1) % n]` and `x[(j + m) % n]` written without the modulo.
-/
def twist (x : Vector UInt32 624) : Vector UInt32 624 :=
  Nat.fold 624 (fun j _ x =>
    let next := x[(j + 1) % 624]'(Nat.mod_lt _ (by decide))
    let y := (x[j] &&& upperMask) ||| (next &&& lowerMask)
    x.set j (x[(j + 397) % 624]'(Nat.mod_lt _ (by decide)) ^^^ (y >>> 1) ^^^ ((next &&& 1) * a))) x

/-- The tempering of one word in Boost's `operator()` (B1, lines 589 to 595), with `u = 11`, `d = 0xffffffff`, `s = 7`, `b = 0x9d2c5680`, `t = 15`, `c = 0xefc60000` and `l = 18`. -/
def temper (z : UInt32) : UInt32 :=
  let z := z ^^^ ((z >>> 11) &&& 0xffffffff)
  let z := z ^^^ ((z <<< 7) &&& 0x9d2c5680)
  let z := z ^^^ ((z <<< 15) &&& 0xefc60000)
  z ^^^ (z >>> 18)

/--
Boost's `operator()` (B1, lines 584 to 596): the next output word, and the state after it.
If `i` is `n`, the call first twists the words and sets `i` to zero.
-/
def next (g : Mt19937) : UInt32 × Mt19937 :=
  if h : g.i < 624 then (temper g.x[g.i], ⟨g.x, g.i + 1, h⟩)
  else
    let x := twist g.x
    (temper x[0], ⟨x, 1, by decide⟩)

/-- Output number `k + 1` of the generator: the result of call `k + 1` of `operator()`. -/
def output (g : Mt19937) : Nat → UInt32
  | 0 => g.next.1
  | k + 1 => output g.next.2 k

end Mt19937

/--
`bucket_size` of Boost's `generate_uniform_int` (B2, lines 198 to 215), for a 32-bit engine and a range of `maxValue` values.
In Boost, `brange` is `2^32 - 1`, the largest `uint32_t`, and `range` is `max - min`, which is `maxValue - 1` here.
The domain is `2 ≤ maxValue < 2^32`. On it, no step of Boost's unsigned 32-bit arithmetic wraps.
-/
def uniformIntBucket (maxValue : Nat) : Nat :=
  if (2 ^ 32 - 1) % maxValue = maxValue - 1 then (2 ^ 32 - 1) / maxValue + 1 else (2 ^ 32 - 1) / maxValue

/--
One pass of the rejection loop of `generate_uniform_int` (B2, lines 216 to 223), for `min = 1` and `max = maxValue`.
The pass divides the engine's word by the bucket size.
It accepts a quotient of at most `range = maxValue - 1`, and returns the quotient plus `min`.
`none` means that Boost draws another word.
-/
def uniformIntAccept (maxValue : Nat) (word : UInt32) : Option Nat :=
  let result := word.toNat / uniformIntBucket maxValue
  if result ≤ maxValue - 1 then some (result + 1) else none

/-- A value of the distribution, with the number of words that the loop rejected before it. -/
structure UniformIntDraw where
  /-- The accepted value, from 1 to `maxValue`. -/
  value : Nat
  /-- The number of rejected words. Core does not observe it. -/
  redraws : Nat
  deriving DecidableEq, Repr

/--
`boost::uniform_int<>(1, maxValue)` applied to a `boost::mt19937` (B2, lines 370 and 371, through `boost/random/uniform_int.hpp` line 80).
With `int` bounds and a 32-bit engine, `generate_uniform_int` takes its last branch, `brange > range` (B2, lines 188 to 226).
The domain is `2 ≤ maxValue ≤ 2^31 - 1`, the values for which Boost reaches that branch with `int` bounds.

Boost's loop has no bound.
This function reads at most `fuel` words, and returns `none` if it rejects all of them.
-/
def uniformInt (maxValue : Nat) (g : Mt19937) : (fuel : Nat) → Option UniformIntDraw
  | 0 => none
  | fuel + 1 =>
    match uniformIntAccept maxValue g.next.1 with
    | some value => some ⟨value, 0⟩
    | none => (uniformInt maxValue g.next.2 fuel).map fun draw => ⟨draw.value, draw.redraws + 1⟩

/-- Core's `COIN` (D104, `src/amount.h` line 18): the number of koinu in one coin. -/
def coin : Nat := 100000000

/--
The seed of the random subsidy (D104, lines 134 to 137).
Core takes `prevHash.ToString().substr(7, 7)`: characters 7 to 13, counted from zero, of the 64 hexadecimal digits that `GetHex` writes (D11).
`strtol` reads them as a base-16 number, which is below `2^28`.
-/
def subsidySeed (prevHash : Hash256) : UInt32 :=
  let digits := prevHash.displayBytes.flatMap fun (byte : UInt8) => [byte >>> 4, byte &&& 0x0f]
  ((digits.drop 7).take 7).foldl (fun value digit => value * 16 + digit.toUInt32) 0

/-- The reason that `getDogecoinBlockSubsidy` returns no value. It is no result of Core. -/
inductive SubsidyError where
  /-- The distribution rejected every word that the fuel allowed. -/
  | fuelExhausted
  deriving DecidableEq, Repr

/-- The number of words that the oracle lets one subsidy read: the 624 words of the first `twist`. -/
def subsidyFuel : Nat := 624

/-- `nSubsidyHalvingInterval` of every mainnet record (D14, line 79). -/
def mainnetSubsidyHalvingInterval : Nat := 100000

/--
`fSimplifiedRewards` of the mainnet record that `GetConsensus(nHeight)` selects (D14, lines 123 to 141 and 494 to 506).
The record below height 145,000 never assigns the field, and the zero initialization of the static `mainParams` object (D14, line 218) makes it false.
The two records from 145,000 have it true (D14, lines 126 to 128 and 134).
-/
def mainnetSimplifiedRewards (nHeight : Nat) : Bool := 145000 ≤ nHeight

/--
`maxReward` of the random subsidy (D104, line 138): `(1000000 >> halvings) - 1`.
On mainnet it is 999,999 below height 100,000 and 499,999 from 100,000 to 144,999.
-/
def subsidyMaxReward (nHeight : Nat) : Nat :=
  (1000000 >>> (nHeight / mainnetSubsidyHalvingInterval)) - 1

/--
Core's `generateMTRandom` (D104, lines 16 to 21): one value of `boost::uniform_int<>(1, range)` from a `boost::mt19937` with the seed `s`.
`none` means that `uniformInt` rejected `fuel` words.
-/
def generateMTRandom (s : UInt32) (range : Nat) (fuel : Nat) : Option UniformIntDraw :=
  uniformInt range (Mt19937.seed s) fuel

/--
Core's `GetDogecoinBlockSubsidy` (D104, lines 127 to 149) on mainnet, in koinu.
`nHeight` is the height of the block, and `prevHash` is the hash of its predecessor.
The domain is `nHeight ≤ 2^31 - 1`, Core's non-negative `int`.
Core's caller selects the record with `GetConsensus(nHeight)` (D101, line 1996).

1. Without `fSimplifiedRewards`, below height 145,000, the subsidy is `(1 + rand) * COIN`.
   `rand` is `generateMTRandom(seed, maxReward)`, with the seed of `subsidySeed`.
2. Otherwise, below `6 * nSubsidyHalvingInterval`, the subsidy is `(500000 * COIN) >> halvings`.
3. From height 600,000, the subsidy is `10000 * COIN`.

Only case 1 reads `prevHash` and `fuel`, and only it can return `fuelExhausted`.
-/
def getDogecoinBlockSubsidy (fuel : Nat) (nHeight : Nat) (prevHash : Hash256) :
    Except SubsidyError Nat :=
  let halvings := nHeight / mainnetSubsidyHalvingInterval
  if !mainnetSimplifiedRewards nHeight then
    match generateMTRandom (subsidySeed prevHash) (subsidyMaxReward nHeight) fuel with
    | some draw => .ok ((1 + draw.value) * coin)
    | none => .error .fuelExhausted
  else if nHeight < 6 * mainnetSubsidyHalvingInterval then .ok ((500000 * coin) >>> halvings)
  else .ok (10000 * coin)

end DogeLib.Block
