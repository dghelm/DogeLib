module

public import DogeLib.Work.ArithUint256

/-!
# Word models of `arith_uint256`

These definitions model Dogecoin Core `e0a1c15`, `src/arith_uint256.cpp` and
`src/arith_uint256.h` (SOURCES.md, D12 and D13).
The words have little-endian order, with `pn[0]` least significant.
The models describe Lean computations, rather than Core's compiled code.
This file adapts Core's loops into total Lean functions, with fixed-size word indices.
The adapted code is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.

Original notices from `arith_uint256.cpp` and `arith_uint256.h`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work.ArithUint256

/-- Core's `pn[WIDTH]`, with `WIDTH = 8` (`arith_uint256.h` lines 28-29 at `e0a1c15`). -/
abbrev Words := Fin 8 → UInt32

namespace Words

/-- The radix-2^32 value of `n` little-endian words (`arith_uint256.h` lines 28-29 at `e0a1c15`). -/
def eval : (n : Nat) → (Fin n → UInt32) → Nat
  | 0, _ => 0
  | n + 1, pn => (pn 0).toNat + 4294967296 * eval n (fun i => pn i.succ)

/-- The value of all eight words (`arith_uint256.h` lines 28-29 at `e0a1c15`). -/
def value (pn : Words) : Nat := eval 8 pn

/-- The low `n` words of a natural number (`arith_uint256.h` lines 28-29 at `e0a1c15`).
Word extraction uses division by the radix and truncation to `UInt32`. -/
def digits : (n : Nat) → Nat → (Fin n → UInt32)
  | 0, _ => Fin.elim0
  | n + 1, a => Fin.cases (UInt32.ofNat a) (digits n (a / 4294967296))

/-- Split a value into Core's eight words (`arith_uint256.h` lines 28-29 at `e0a1c15`). -/
def ofArith (a : ArithUint256) : Words := digits 8 a.val

/-- Interpret `pn` as a 256-bit value (`arith_uint256.h` lines 28-29 at `e0a1c15`). -/
def toArith (pn : Words) : ArithUint256 := ofNat (value pn)

/-- Core's carry loop, low word first (`arith_uint256.cpp` lines 55-65 at `e0a1c15`).
Each step stores the low 32 bits of `carry + b32 * pn[i]` and advances `carry` by 32 bits.
The result includes the final carry so that proofs can account for the discarded word. -/
def mulLoop (b32 : UInt32) : (n : Nat) → (Fin n → UInt32) → UInt64 →
    (Fin n → UInt32) × UInt64
  | 0, _, carry => (Fin.elim0, carry)
  | n + 1, pn, carry =>
    let x := carry + b32.toUInt64 * (pn 0).toUInt64
    let rest := mulLoop b32 n (fun i => pn i.succ) (x >>> 32)
    (Fin.cases x.toUInt32 rest.1, rest.2)

/-- Core's eight-word multiplication, with the final carry discarded
(`arith_uint256.cpp` lines 55-65 at `e0a1c15`). -/
def mulUInt32 (pn : Words) (b32 : UInt32) : Words := (mulLoop b32 8 pn 0).1

/-- Core's `pn[0] | (uint64_t)pn[1] << 32`
(`arith_uint256.h` lines 245-249 at `e0a1c15`). -/
def getLow64 (pn : Words) : UInt64 := (pn 0).toUInt64 ||| ((pn 1).toUInt64 <<< 32)

/-- Descending mask scan within a nonzero word, with bit zero as the fallback
(`arith_uint256.cpp` lines 175-181 at `e0a1c15`).
Core tests `pn[pos] & 1 << bits`, with a signed `int` literal.
For a 32-bit `int`, N3337 section 5.8 paragraph 2 leaves `1 << 31` undefined (SOURCES.md, S1).
This model uses `testBit` and the intended mask `0x80000000`. -/
def bitScan (w : UInt32) : Nat → Nat
  | 0 => 1
  | bit + 1 => if w.toNat.testBit (bit + 1) then bit + 2 else bitScan w bit

/-- Core's descending scan of the `pn` words
(`arith_uint256.cpp` lines 171-184 at `e0a1c15`).
The recursive call visits the next lower word only when the current word is zero. -/
def bitsLoop : (n : Nat) → (Fin n → UInt32) → Nat
  | 0, _ => 0
  | n + 1, pn =>
    if pn ⟨n, by omega⟩ != 0 then 32 * n + bitScan (pn ⟨n, by omega⟩) 31
    else bitsLoop n (fun i => pn i.castSucc)

/-- Core's `bits()` scan over all eight words
(`arith_uint256.cpp` lines 171-184 at `e0a1c15`).
The result is at most 256, as `bits_le` proves. -/
def bits (pn : Words) : Nat := bitsLoop 8 pn

/-- OR a contribution into `pn[index]` when the index is below `WIDTH = 8`
(`arith_uint256.cpp` lines 30-33 and 47-50 at `e0a1c15`). -/
def orAt (pn : Words) (index : Nat) (word : UInt32) : Words :=
  fun j => if j.val = index then pn j ||| word else pn j

/-- One source-word iteration of Core's left shift
(`arith_uint256.cpp` lines 27-33 at `e0a1c15`).
The high contribution has the `shift != 0` guard to avoid a 32-bit shift.
The full loop supplies `i < 8`, so `i % 8` is its source index. -/
def leftStep (a pn : Words) (shift i : Nat) : Words :=
  let k := shift / 32
  let shift := shift % 32
  let pn := if i + k + 1 < 8 && shift != 0 then
    orAt pn (i + k + 1) (a ⟨i % 8, Nat.mod_lt _ (by decide)⟩ >>> UInt32.ofNat (32 - shift))
    else pn
  if i + k < 8 then
    orAt pn (i + k) (a ⟨i % 8, Nat.mod_lt _ (by decide)⟩ <<< UInt32.ofNat shift)
  else pn

/-- One source-word iteration of Core's right shift
(`arith_uint256.cpp` lines 44-50 at `e0a1c15`).
Natural indices use `k + 1 ≤ i` for Core's signed condition `i - k - 1 >= 0`.
The full loop supplies `i < 8`, so `i % 8` is its source index. -/
def rightStep (a pn : Words) (shift i : Nat) : Words :=
  let k := shift / 32
  let shift := shift % 32
  let pn := if k + 1 ≤ i && shift != 0 then
    orAt pn (i - k - 1) (a ⟨i % 8, Nat.mod_lt _ (by decide)⟩ <<< UInt32.ofNat (32 - shift))
    else pn
  if k ≤ i then
    orAt pn (i - k) (a ⟨i % 8, Nat.mod_lt _ (by decide)⟩ >>> UInt32.ofNat shift)
  else pn

/-- Core's zero output followed by eight ascending source-word iterations
(`arith_uint256.cpp` lines 21-36 at `e0a1c15`).
Core accepts `shift < 2^32`.
This model extends its arithmetic meaning to every natural shift. -/
def shiftLeft (a : Words) (shift : Nat) : Words :=
  (List.range 8).foldl (fun pn i => leftStep a pn shift i) (fun _ => 0)

/-- Core's zero output followed by eight ascending source-word iterations
(`arith_uint256.cpp` lines 38-53 at `e0a1c15`).
Core accepts `shift < 2^32`.
This model extends its arithmetic meaning to every natural shift. -/
def shiftRight (a : Words) (shift : Nat) : Words :=
  (List.range 8).foldl (fun pn i => rightStep a pn shift i) (fun _ => 0)

end Words
end DogeLib.Work.ArithUint256
