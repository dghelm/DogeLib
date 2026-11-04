module

public import DogeLib.Work.ArithUint256Division

/-!
# Word models of uint64 assignment and compact targets

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

/-- Core's uint64 constructor writes two low words and zeroes the rest (D12 lines 51-57). -/
def ofUInt64 (b : UInt64) : Words :=
  fun i => if i.val = 0 then b.toUInt32 else if i.val = 1 then (b >>> 32).toUInt32 else 0

/-- Core's uint64 assignment overwrites all eight words (D12 lines 88-96).
The previous words do not affect the result. -/
def assignUInt64 (_old : Words) (b : UInt64) : Words := ofUInt64 b

/-- The stored words and both output flags of Core's `SetCompact` (D13 lines 204-222). -/
structure CompactResult where
  /-- The stored magnitude, modulo 2^256. -/
  value : Words
  /-- The sign flag, after any right shift of the mantissa. -/
  fNegative : Bool
  /-- The overflow flag, after any right shift of the mantissa. -/
  fOverflow : Bool

/-- Core's `SetCompact`, including both flags, for every 32-bit compact (D13 lines 204-222). -/
def setCompact (nCompact : UInt32) : CompactResult :=
  let nSize := (nCompact >>> 24).toNat
  let nWord := nCompact &&& 0x007fffff
  let nWord := if nSize ≤ 3 then nWord >>> UInt32.ofNat (8 * (3 - nSize)) else nWord
  let pn := assignUInt64 (fun _ => 0) nWord.toUInt64
  let value := if nSize ≤ 3 then pn else shiftLeft pn (8 * (nSize - 3))
  { value
    fNegative := nWord != 0 && (nCompact &&& 0x00800000) != 0
    fOverflow := nWord != 0 &&
      (decide (nSize > 34) || (nWord > 0xff && decide (nSize > 33)) ||
        (nWord > 0xffff && decide (nSize > 32))) }

/-- Core's `GetCompact`, including the requested sign (D13 lines 224-245).
The arithmetic proof establishes Core's two assertions for every word input. -/
def getCompact (pn : Words) (fNegative : Bool := false) : UInt32 :=
  let nSize := (bits pn + 7) / 8
  let nCompact := if nSize ≤ 3 then
    (getLow64 pn <<< UInt64.ofNat (8 * (3 - nSize))).toUInt32
    else (getLow64 (shiftRight pn (8 * (nSize - 3)))).toUInt32
  let (nCompact, nSize) := if nCompact &&& 0x00800000 != 0 then
    (nCompact >>> 8, nSize + 1) else (nCompact, nSize)
  let nCompact := nCompact ||| (UInt32.ofNat nSize <<< 24)
  nCompact ||| (if fNegative && (nCompact &&& 0x007fffff) != 0 then 0x00800000 else 0)

end DogeLib.Work.ArithUint256.Words
