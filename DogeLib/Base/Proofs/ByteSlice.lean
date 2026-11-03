module

public import DogeLib.Base.ByteSlice
public import DogeLib.Base.Proofs.ByteArray
import all Std.Data.ByteSlice

/-!
# Proofs: `Base.ByteSlice`

The reader operations of `DogeLib.Base.ByteSlice` agree with the list operations of the same names, through `ByteSlice.toList`.

These are the results:

- `byteArray_slice`, `start_slice` and `stop_slice`: a sub-slice has the same base array, and its offsets are the clamped bounds.
  Together they describe `ByteSlice.slice` completely.
- `toList_eq`: `toList` is the window of the base array's bytes between the two offsets.
- `toList_of_uncons_some` and `toList_of_uncons_none`: `uncons` on a slice is `uncons` on its bytes.
- `toList_take` and `toList_drop`, with `size_take` and `size_drop`: `take` and `drop` commute with `toList`.

The packed codec proofs use only these lemmas, and no array index.

Lean core does not expose the bodies of `ByteSlice.size`, `ByteSlice.slice` and `ByteSlice.get`.
This module imports `Std.Data.ByteSlice` with `import all` to unfold them, as Batteries does.
That import is private to this module.

Adapted from btc-verified, [`BtcVerified/Ext/ByteSlice.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteSlice.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- This file contains only the theorems of that file. Its definitions are in `DogeLib/Base/ByteSlice.lean`.
- Upstream imports `Batteries.Data.ByteSlice` for `ByteSlice.stop_eq_start_add_size`.
  This file proves that lemma itself, so that DogeLib does not depend on Batteries.
- The last step of `toList_eq` rewrites with `stop_eq_start_add_size`, where upstream uses `rfl`.
- Lean `v4.35.0` deprecates `dif_pos` and `dif_neg`, so `toList_of_uncons_some` uses `dite_eq_left` and `dite_eq_right`.
- The module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace ByteSlice

/-- For every slice `s`, the stop offset of `s` is its start offset plus its size. -/
theorem stop_eq_start_add_size (s : ByteSlice) : s.stop = s.start + s.size := by
  have := s.start_le_stop
  unfold ByteSlice.size
  omega

/-! ## `slice` -/

/-- For every slice `s` and bounds `a` and `b`, the sub-slice `s.slice a b` has the base array of `s`. -/
@[simp] theorem byteArray_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).byteArray = s.byteArray := by
  unfold ByteSlice.slice
  dsimp only
  split
  · split <;> rfl
  · rfl

/--
For every slice `s` and bounds `a` and `b`, the sub-slice `s.slice a b` starts at offset `s.start + min (min a b) s.size`.
That is, its start is `a`, clamped first by `b` and then by the size of `s`.
-/
theorem start_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).start = s.start + min (min a b) s.size := by
  have h1 : s.stop ≤ s.byteArray.size := s.stop_le_size_byteArray
  have h2 := s.stop_eq_start_add_size
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · next h =>
      show s.start + min a s.size = _
      omega
    · next h =>
      show s.start + min b s.size = _
      omega
  · next h => exact absurd (by omega) h

/-- For every slice `s` and bounds `a` and `b`, the sub-slice `s.slice a b` stops at offset `s.start + min b s.size`. -/
theorem stop_slice (s : ByteSlice) (a b : Nat) :
    (s.slice a b).stop = s.start + min b s.size := by
  have h1 : s.stop ≤ s.byteArray.size := s.stop_le_size_byteArray
  have h2 := s.stop_eq_start_add_size
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · next h => rfl
    · next h => rfl
  · next h => exact absurd (by omega) h

/-! ## `toList` -/

/-- For every slice `s`, `s.toList` is the `s.size` bytes of the base array from offset `s.start`. -/
theorem toList_eq (s : ByteSlice) :
    s.toList = (s.byteArray.data.toList.drop s.start).take s.size := by
  rw [toList, ByteArray.toList_eq_data_toList, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop]
  rw [stop_eq_start_add_size, Nat.add_sub_cancel_left]

/-- For every byte array `bytes`, the slice of all of `bytes` has the bytes `bytes.toList`. -/
@[simp] theorem toList_ofByteArray (bytes : ByteArray) :
    (ByteSlice.ofByteArray bytes).toList = bytes.toList := by
  rw [toList]
  show (bytes.extract 0 bytes.size).toList = _
  rw [ByteArray.extract_zero_size]

/-- For every slice `s`, `s.toList` has length `s.size`. -/
@[simp] theorem length_toList (s : ByteSlice) : s.toList.length = s.size := by
  have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
  have h2 := s.stop_eq_start_add_size
  rw [toList_eq]
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

/-! ## `take` and `drop` -/

/-- For every slice `s` and number `n`, `s.take n` has size `min n s.size`. -/
@[simp] theorem size_take (s : ByteSlice) (n : Nat) :
    (s.take n).size = min n s.size := by
  have hst : (s.slice 0 n).start = s.start := by
    rw [start_slice]
    omega
  show (s.slice 0 n).stop - (s.slice 0 n).start = _
  rw [hst, stop_slice]
  omega

/-- For every slice `s` and number `n`, the bytes of `s.take n` are the first `n` bytes of `s`, `s.toList.take n`. -/
@[simp] theorem toList_take (s : ByteSlice) (n : Nat) :
    (s.take n).toList = s.toList.take n := by
  have hst : (s.slice 0 n).start = s.start := by
    rw [start_slice]
    omega
  have hsz : (s.slice 0 n).size = min n s.size := size_take s n
  simp only [take] at hsz ⊢
  rw [toList_eq, toList_eq, byteArray_slice, hst, hsz, List.take_take]

/-- For every slice `s` and number `n`, `s.drop n` has size `s.size - n`. -/
@[simp] theorem size_drop (s : ByteSlice) (n : Nat) :
    (s.drop n).size = s.size - n := by
  have hst : (s.slice n s.size).start = s.start + min n s.size := by
    rw [start_slice]
    omega
  show (s.slice n s.size).stop - (s.slice n s.size).start = _
  rw [hst, stop_slice]
  omega

/-- For every slice `s` and number `n`, the bytes of `s.drop n` are the bytes of `s` after the first `n`, `s.toList.drop n`. -/
@[simp] theorem toList_drop (s : ByteSlice) (n : Nat) :
    (s.drop n).toList = s.toList.drop n := by
  have h2 := s.stop_eq_start_add_size
  have hst : (s.slice n s.size).start = s.start + min n s.size := by
    rw [start_slice]
    omega
  have hsz : (s.slice n s.size).size = s.size - n := size_drop s n
  simp only [drop] at hsz ⊢
  rw [toList_eq, toList_eq, byteArray_slice, hst, hsz]
  rcases Nat.le_total n s.size with h | h
  · rw [Nat.min_eq_left h, List.drop_take, List.drop_drop]
  · have hnil : s.toList.length ≤ n := by
      rw [length_toList]
      omega
    rw [← toList_eq, List.drop_eq_nil_of_le hnil]
    refine List.length_eq_zero_iff.mp ?_
    simp only [List.length_take, List.length_drop, Array.length_toList]
    have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
    omega

/-! ## `uncons` -/

/-- For every slice `s`, if `s.uncons` is `none`, then `s` has no bytes: `s.toList = []`. -/
theorem toList_of_uncons_none {s : ByteSlice} (h : s.uncons = none) :
    s.toList = [] := by
  rw [uncons] at h
  split at h
  · exact absurd h (by simp)
  · next hns =>
    refine List.length_eq_zero_iff.mp ?_
    rw [length_toList]
    omega

/--
For every slice `s`, if `s.uncons` is `some (b, t)`, then the bytes of `s` are `b` followed by the bytes of `t`: `s.toList = b :: t.toList`.
-/
theorem toList_of_uncons_some {s : ByteSlice} {b : UInt8} {t : ByteSlice}
    (h : s.uncons = some (b, t)) : s.toList = b :: t.toList := by
  rw [uncons] at h
  by_cases hpos : 0 < s.size
  · rw [dite_eq_left hpos] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have h1 : s.stop ≤ s.byteArray.data.size := s.stop_le_size_byteArray
    have h2 := s.stop_eq_start_add_size
    have hidx : s.start < s.byteArray.data.toList.length := by
      simp only [Array.length_toList]
      omega
    have hb : s[0]'hpos
        = s.byteArray[s.start]'(by have h4 := s.stop_le_size_byteArray; omega) := rfl
    have htail : (s.drop 1).toList
        = (s.byteArray.data.toList.drop (s.start + 1)).take (s.size - 1) := by
      rw [toList_drop, toList_eq, List.drop_take, List.drop_drop]
    rw [toList_eq, List.drop_eq_getElem_cons hidx,
      show s.size = (s.size - 1) + 1 from by omega, List.take_succ_cons, htail, hb]
    congr 1
  · rw [dite_eq_right hpos] at h
    exact absurd h (by simp)

end ByteSlice
