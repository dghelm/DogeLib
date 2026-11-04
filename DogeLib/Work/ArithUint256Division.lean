module

public import DogeLib.Work.ArithUint256Words
public import Init.Data.Vector.OfFn

/-!
# Word division and its dependencies

These definitions adapt Dogecoin Core `e0a1c15`, `src/arith_uint256.h` and
`src/arith_uint256.cpp` (SOURCES.md, D12 and D13).
The adapted code is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notices:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work.ArithUint256.Words

/-- Core's descending `CompareTo` scan (D13 lines 110-119), for any word count.
The three results represent Core's return values -1, 0 and 1. -/
def compareLoop : (n : Nat) → (Fin n → UInt32) → (Fin n → UInt32) → Ordering
  | 0, _, _ => .eq
  | n + 1, a, b =>
    if a ⟨n, by omega⟩ < b ⟨n, by omega⟩ then .lt
    else if a ⟨n, by omega⟩ > b ⟨n, by omega⟩ then .gt
    else compareLoop n (fun i => a i.castSucc) (fun i => b i.castSucc)

/-- Core's eight-word `CompareTo` (D13 lines 110-119). -/
def compareTo (a b : Words) : Ordering := compareLoop 8 a b

/-- Core's low-to-high addition loop (D12 lines 135-145), with the final carry retained. -/
def addLoop : (n : Nat) → (Fin n → UInt32) → (Fin n → UInt32) → UInt64 →
    (Fin n → UInt32) × UInt64
  | 0, _, _, carry => (Fin.elim0, carry)
  | n + 1, a, b, carry =>
    let x := carry + (a 0).toUInt64 + (b 0).toUInt64
    let rest := addLoop n (fun i => a i.succ) (fun i => b i.succ) (x >>> 32)
    (Fin.cases x.toUInt32 rest.1, rest.2)

/-- Core's eight-word `operator+=`, with its final carry discarded (D12 lines 135-145). -/
def add (a b : Words) : Words := (addLoop 8 a b 0).1

/-- Core's prefix increment (D12 lines 173-180), with carry propagation only after a word wraps. -/
def incrementLoop : (n : Nat) → (Fin n → UInt32) → (Fin n → UInt32)
  | 0, _ => Fin.elim0
  | n + 1, a =>
    let w := a 0 + 1
    Fin.cases w (if w == 0 then incrementLoop n (fun i => a i.succ) else fun i => a i.succ)

/-- Core's word complement followed by prefix increment (D12 lines 77-84). -/
def neg (a : Words) : Words := incrementLoop 8 (fun i => ~~~a i)

/-- Core's `operator-=` is addition of the negated operand (D12 lines 147-151). -/
def sub (a b : Words) : Words := add a (neg b)

/-- The mutable words of Core's division loop (D13 lines 86-105). -/
structure DivisionState where
  /-- Core's `num`, the remaining numerator. -/
  num : Words
  /-- Core's `div`, the shifted divisor. -/
  divisor : Words
  /-- Core's `*this`, the quotient. -/
  quotient : Words

/-- Read stored word values from a vector, as Core reads its mutable array (D13 lines 98-103).
The loop constructs each vector before it supplies this function to the next iteration. -/
@[noinline] def readWords (words : Vector UInt32 8) : Words := fun i => words[i]

/-- Core's loop over shifts `remaining - 1` through zero (D13 lines 97-105).
At bit 31, Core's signed `1 << (shift & 31)` is undefined under N3337 5.8 paragraph 2 (S1).
This model uses the intended unsigned mask, as the word bit scan does. -/
def divLoop : Nat → DivisionState → DivisionState
  | 0, st => st
  | shift + 1, st =>
    let st := if compareTo st.num st.divisor != .lt then
      { st with num := sub st.num st.divisor
                quotient := orAt st.quotient (shift / 32) ((1 : UInt32) <<< UInt32.ofNat (shift % 32)) }
      else st
    divLoop shift
      { num := readWords (Vector.ofFn st.num)
        divisor := readWords (Vector.ofFn (shiftRight st.divisor 1))
        quotient := readWords (Vector.ofFn st.quotient) }

/-- Core's `operator/=` (D13 lines 84-108), with `none` for its zero-divisor exception.
The copies and zero quotient precede both tests, as in Core.
The operand state after an exception is not modeled: Core has already zeroed `*this` before it throws. -/
def divide (a b : Words) : Option Words :=
  let divisor := b
  let num := a
  let quotient : Words := fun _ => 0
  let numBits := bits num
  let divBits := bits divisor
  if divBits = 0 then none
  else if divBits > numBits then some quotient
  else
    let shift := numBits - divBits
    some (divLoop (shift + 1) { num, divisor := shiftLeft divisor shift, quotient }).quotient

end DogeLib.Work.ArithUint256.Words
