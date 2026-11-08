module

public import DogeLib.Work.ArithUint256

/-!
# Block proof

`GetBlockProof` in Dogecoin Core `e0a1c15`, `src/chain.cpp` lines 150 to 163 (SOURCES.md, D75): the work of one block, from its compact target.
Design record 0008, stage 4, adds it, and `Block.addToBlockIndex` adds it to the predecessor's chain work, as Core's `AddToBlockIndex` does (D33, line 2780).

Core decodes `nBits` with `SetCompact` and returns 0 when the target is negative, overflows or is zero (lines 152 to 157).
Otherwise it returns `(~bnTarget / (bnTarget + 1)) + 1` in 256-bit arithmetic (line 162):

```text
~bnTarget            operator~ (D12, lines 69 to 75)           2^256 - 1 - t
bnTarget + 1         operator+ (D12, lines 135 to 145, 210)    t + 1 mod 2^256, 1 through base_uint(uint64_t)
a / b                operator/ (D13, lines 84 to 108, D12 213) floor(a / b), Core throws when b = 0
q + 1                operator+                                 q + 1 mod 2^256
```

This module states each operation by its arithmetic result on `ArithUint256`, as `DogeLib.Work.ArithUint256` does.
`blockProof_eq` in `DogeLib.Work.Proofs.ChainWork` proves that the result is `⌊2^256 / (t + 1)⌋` when Core does not return 0.
The correspondence between Core's source and the model is checked by review.

The adapted code is under the MIT licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notices from `src/chain.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Work

namespace ArithUint256

/-- `~a`, `operator~` (D12, lines 69 to 75).
Core inverts each of the eight words, so the result is `2^256 - 1 - a`. -/
def complement (a : ArithUint256) : ArithUint256 :=
  ⟨2 ^ 256 - 1 - a.val,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos 256) Nat.one_pos)⟩

end ArithUint256

/--
Core's `GetBlockProof` (D75, lines 150 to 163) for the compact target `nBits` of a block.

The value is 0 when `SetCompact` reports a negative value or an overflow, or when the target is zero (lines 155 to 157).
Otherwise it is `(~target / (target + 1)) + 1`, with both additions modulo 2^256 (line 162).

Core's division throws for a zero divisor.
The divisor `target + 1` is zero only for the target 2^256 - 1, and `SetCompact` never gives that value.
The definition returns 0 in that branch, and `blockProof_eq` proves that no compact value reaches it.
-/
def blockProof (nBits : UInt32) : ArithUint256 :=
  let target := ArithUint256.setCompact nBits
  if target.fNegative || target.fOverflow || target.value.val == 0 then 0
  else
    let divisor := target.value + 1
    if zero : divisor.val = 0 then 0
    else ArithUint256.div (ArithUint256.complement target.value) divisor zero + 1

end DogeLib.Work
