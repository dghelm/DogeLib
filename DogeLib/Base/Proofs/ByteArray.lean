module

public import Init.Data.ByteArray

/-!
# Proofs: `ByteArray`

`ByteArray.toList` reads the same bytes as the underlying `Array`.

Lean core defines `ByteArray.toList` by its own accumulator loop, and proves almost nothing about it.
`ByteArray.data`, the underlying `Array UInt8`, has the lemmas of core's `Array` library.
`toList_eq_data_toList` connects the two, so that a statement about `toList` can be proved through `data`.
The corollaries cover the two constructors that the packed codecs use, `push` and `List.toByteArray`.

Adapted from btc-verified, [`BtcVerified/Ext/ByteArray.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteArray.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Lean `v4.35.0` deprecates `if_neg` and `if_pos`, so `toList_loop` uses `ite_eq_right` and `ite_eq_left`.
  Its `simp` step also closes the goal that upstream closes with `rfl`, so that `rfl` is removed.
- The module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace ByteArray

/-- The accumulator loop of `toList`, from index `i`, reverses its accumulator and appends the bytes from `i` on. -/
private theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  generalize hfuel : bs.size - i = fuel
  induction fuel generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop, ite_eq_right (by omega),
      List.drop_eq_nil_of_le (by simpa using Nat.le_of_sub_eq_zero hfuel),
      List.append_nil]
  | succ fuel ih =>
    have hi : i < bs.size := by omega
    have hi' : i < bs.data.toList.length := by simpa using hi
    rw [ByteArray.toList.loop, ite_eq_left hi, ih (i + 1) _ (by omega),
      List.drop_eq_getElem_cons hi']
    simp [ByteArray.get!, hi]

/-- For every byte array `bs`, `bs.toList` equals the list of its underlying array, `bs.data.toList`. -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, toList_loop]
  simp

/-- For every byte array `bs` and byte `b`, the bytes of `bs.push b` are the bytes of `bs` followed by `b`. -/
@[simp] theorem toList_push (bs : ByteArray) (b : UInt8) :
    (bs.push b).toList = bs.toList ++ [b] := by
  simp [toList_eq_data_toList, ByteArray.data_push]

/-- For every byte list `l`, the bytes of `l.toByteArray` are `l`. -/
@[simp] theorem _root_.List.toList_toByteArray (l : List UInt8) :
    l.toByteArray.toList = l := by
  rw [toList_eq_data_toList, List.data_toByteArray]

end ByteArray
