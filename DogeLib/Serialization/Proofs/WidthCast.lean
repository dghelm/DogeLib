module

/-!
# Proofs: width casts

To truncate a value to a smaller width and then widen it back gives the value again, if the value fits in the smaller width.

A codec needs this fact when it writes a value in fewer bytes than its type has.
For example, the CompactSize codec writes a `UInt64` count below `2 ^ 16` as a `UInt16`.

`setWidth_setWidth_eq_self` proves the fact once, for `BitVec`.
The tactic `narrow_widen` applies it to the fixed-width integers.
It rewrites a goal `x.toNarrow.toWide = x` into `BitVec` form with core's simp set `int_toBitVec_meta`, and closes it with `setWidth_setWidth_eq_self`.
Core fills that simp set with the lemmas that have the attribute `int_toBitVec`.
So no lemma is necessary for each pair of widths.

Adapted from btc-verified, [`BtcVerified/Serialize/WidthCast.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/WidthCast.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream imports `Mathlib.Data.UInt`. This file imports only Lean core.
- Upstream closes the bound with `simpa`.
  With Lean core alone, `simp` does not reduce the bound `(2 ^ k).toNat`, so here the tactic evaluates the bound `(2 ^ k).toNat = 2 ^ k` with `decide`, which the kernel checks.
- Upstream names the simp set `int_toBitVec`. In Lean `v4.35.0`, `int_toBitVec` is an attribute that adds lemmas to the simp set `int_toBitVec_meta`, so the tactic names that simp set.
- The two examples at the end of this file test the tactic.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/--
For all widths `n` and `m`, and every `a : BitVec n` with `a.toNat < 2 ^ m`, truncating `a` to `m` bits and widening it back to `n` bits gives `a`.
-/
theorem setWidth_setWidth_eq_self {n m : Nat} {a : BitVec n} (h : a.toNat < 2 ^ m) :
    (a.setWidth m).setWidth n = a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a.isLt]

set_option hygiene false in
/--
`narrow_widen h` closes a goal `x.toNarrow.toWide = x` for fixed-width unsigned integers, from a proof `h` that `x < 2 ^ k`, where `k` is the narrow width.

The source type of `x` is `UInt64`, `UInt32`, `UInt16` or `UInt8`, and the tactic tries each one.
Hygiene is off for the macro, so that `int_toBitVec_meta` names core's simp set.
-/
macro "narrow_widen " h:term : tactic =>
  `(tactic|
    (simp only [int_toBitVec_meta]
     apply DogeLib.Serialization.setWidth_setWidth_eq_self
     first
       | exact Nat.lt_of_lt_of_eq (UInt64.lt_iff_toNat_lt.mp $h) (by decide)
       | exact Nat.lt_of_lt_of_eq (UInt32.lt_iff_toNat_lt.mp $h) (by decide)
       | exact Nat.lt_of_lt_of_eq (UInt16.lt_iff_toNat_lt.mp $h) (by decide)
       | exact Nat.lt_of_lt_of_eq (UInt8.lt_iff_toNat_lt.mp $h) (by decide)))

-- A `UInt64` below `2 ^ 8` survives a cast to `UInt8` and back.
example (n : UInt64) (h : n < 2 ^ 8) : n.toUInt8.toUInt64 = n := by
  narrow_widen h

-- A `UInt32` below `2 ^ 16` survives a cast to `UInt16` and back.
example (n : UInt32) (h : n < 2 ^ 16) : n.toUInt16.toUInt32 = n := by
  narrow_widen h

end DogeLib.Serialization
