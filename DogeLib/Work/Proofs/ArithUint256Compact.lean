module

public import DogeLib.Work.ArithUint256Compact
public import DogeLib.Work.Proofs.ArithUint256Division
public import DogeLib.Work.Proofs.ArithUint256

/-! # Arithmetic meaning of uint64 assignment and compact targets -/

@[expose] public section

namespace DogeLib.Work.ArithUint256.Words

/-- The uint64 constructor stores its full input, for every 64-bit value. -/
theorem ofUInt64_value (b : UInt64) : value (ofUInt64 b) = b.toNat := by
  have hb := b.toNat_lt
  simp only [value, eval, ofUInt64]
  simp only [Fin.val_zero, Fin.val_succ, ite_true, Nat.reduceAdd, Nat.reduceEqDiff,
    ite_false, UInt32.toNat_zero, Nat.mul_zero, Nat.add_zero,
    UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  change b.toNat % 4294967296 + 4294967296 * ((b.toNat / 4294967296) % 4294967296) = _
  omega

/-- For every uint64 input, the constructor agrees with the arithmetic embedding. -/
theorem ofUInt64_toArith (b : UInt64) : toArith (ofUInt64 b) = ofNat b.toNat := by
  simp only [toArith, ofUInt64_value]

/-- For every old word array and uint64 input, assignment agrees with the arithmetic embedding. -/
theorem assignUInt64_toArith (old : Words) (b : UInt64) :
    toArith (assignUInt64 old b) = ofNat b.toNat := ofUInt64_toArith b

/-- Interpret the complete word decoder result, including both flags. -/
def CompactResult.toArith (r : CompactResult) : SetCompactResult :=
  ⟨Words.toArith r.value, r.fNegative, r.fOverflow⟩

private theorem ne_zero_nat (w : UInt32) : (w != 0) = (w.toNat != 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro h hz
    exact h (UInt32.toNat_inj.mp hz)
  · intro h hz
    exact h (congrArg UInt32.toNat hz)

/-- For every compact, word decoding agrees with the arithmetic decoder, including both flags. -/
theorem setCompact_toArith (c : UInt32) : (setCompact c).toArith = ArithUint256.setCompact c := by
  have hsize : (c >>> 24).toNat = c.toNat >>> 24 := by
    simp only [UInt32.toNat_shiftRight]; rfl
  have hword : (c &&& 0x007fffff).toNat = c.toNat &&& 0x007fffff := by
    simp only [UInt32.toNat_and]; rfl
  have hshift (h : c.toNat >>> 24 ≤ 3) :
      ((c &&& 0x007fffff) >>> UInt32.ofNat (8 * (3 - (c.toNat >>> 24)))).toNat =
        (c.toNat &&& 0x007fffff) >>> (8 * (3 - (c.toNat >>> 24))) := by
    have hs : 8 * (3 - (c.toNat >>> 24)) < 32 := by omega
    simp only [UInt32.toNat_shiftRight, UInt32.toNat_ofNat', hword]
    rw [Nat.mod_eq_of_lt (show 8 * (3 - (c.toNat >>> 24)) < 2 ^ 32 by omega), Nat.mod_eq_of_lt hs]
  simp only [setCompact, CompactResult.toArith, hsize]
  split <;> rename_i h
  · simp only [assignUInt64_toArith, UInt32.toNat_toUInt64, hshift h,
      ArithUint256.setCompact, h, ite_true]
    congr 1 <;> simp only [ne_zero_nat, hshift h, UInt32.toNat_and, UInt32.reduceToNat,
      UInt32.lt_iff_toNat_lt]
  · simp only [assignUInt64_toArith, UInt32.toNat_toUInt64, shiftLeft_toArith, hword,
      ArithUint256.setCompact, h, ite_false]
    congr 1 <;> simp only [ne_zero_nat, hword, UInt32.toNat_and, UInt32.reduceToNat,
      UInt32.lt_iff_toNat_lt]

private theorem pack_eq (c : UInt32) (s : Nat) (hs : s < 256) (negative : Bool) :
    let packed := c ||| (UInt32.ofNat s <<< 24)
    packed ||| (if negative && (packed &&& 0x007fffff) != 0 then (0x00800000 : UInt32) else 0) =
      UInt32.ofNat ((c.toNat ||| (s <<< 24)) |||
        (if negative && ((c.toNat ||| (s <<< 24)) &&& 0x007fffff) != 0 then 0x00800000 else 0)) := by
  have hshiftlt : s <<< 24 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    omega
  have hshift : (UInt32.ofNat s <<< 24).toNat = s <<< 24 := by
    simp only [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', UInt32.reduceToNat,
      Nat.reduceMod, Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega), Nat.mod_eq_of_lt hshiftlt]
  have hp : (c ||| (UInt32.ofNat s <<< 24)).toNat = c.toNat ||| (s <<< 24) := by
    rw [UInt32.toNat_or, hshift]
  have hm : ((c ||| (UInt32.ofNat s <<< 24)) &&& 0x007fffff != 0) =
      (((c.toNat ||| (s <<< 24)) &&& 0x007fffff) != 0) := by
    rw [ne_zero_nat, UInt32.toNat_and, hp]; rfl
  dsimp only
  rw [hm, UInt32.ofNat_or, UInt32.ofNat_or, UInt32.ofNat_toNat]
  have he : UInt32.ofNat (s <<< 24) = UInt32.ofNat s <<< 24 :=
    UInt32.ofNat_shiftLeft s 24 (by decide)
  rw [he]
  split <;> rfl

/-- For every word array and sign argument, word encoding agrees with the arithmetic encoder. -/
theorem getCompact_toArith (pn : Words) (negative : Bool) :
    getCompact pn negative = ArithUint256.getCompact (toArith pn) negative := by
  let s := (bits pn + 7) / 8
  let raw := if s ≤ 3 then
    (getLow64 pn <<< UInt64.ofNat (8 * (3 - s))).toUInt32
    else (getLow64 (shiftRight pn (8 * (s - 3)))).toUInt32
  have hraw : raw.toNat =
      if s ≤ 3 then (ArithUint256.getLow64 (toArith pn) <<< (8 * (3 - s))) % 2 ^ 64 % 2 ^ 32
      else ArithUint256.getLow64 (ArithUint256.shiftRight (toArith pn) (8 * (s - 3))) % 2 ^ 32 := by
    dsimp only [raw]
    split
    · next h =>
      have hs : 8 * (3 - s) < 64 := by omega
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', getLow64_toArith]
      rw [Nat.mod_eq_of_lt (show 8 * (3 - s) < 2 ^ 64 by omega), Nat.mod_eq_of_lt hs]
    · simp only [UInt64.toNat_toUInt32, getLow64_toArith, shiftRight_toArith]
  have hsize : s ≤ 32 := by have := bits_le pn; dsimp [s]; omega
  have hm : (raw &&& 0x00800000 != 0) = (raw.toNat &&& 0x00800000 != 0) := by
    rw [ne_zero_nat, UInt32.toNat_and]; rfl
  have hr : (raw >>> 8).toNat = raw.toNat >>> 8 := by
    simp only [UInt32.toNat_shiftRight]; rfl
  change (let pair := if raw &&& 0x00800000 != 0 then (raw >>> 8, s + 1) else (raw, s)
    let packed := pair.1 ||| (UInt32.ofNat pair.2 <<< 24)
    packed ||| (if negative && (packed &&& 0x007fffff) != 0 then 0x00800000 else 0)) = _
  rw [hm]
  unfold ArithUint256.getCompact
  rw [← bits_toArith]
  dsimp only
  rw [show (bits pn + 7) / 8 = s from rfl]
  rw [← hraw]
  change _ = (let pair := if raw.toNat &&& 0x00800000 != 0 then (raw.toNat >>> 8, s + 1) else (raw.toNat, s)
    UInt32.ofNat ((pair.1 ||| (pair.2 <<< 24)) |||
      (if negative && ((pair.1 ||| (pair.2 <<< 24)) &&& 0x007fffff) != 0 then 0x00800000 else 0)))
  split
  · simpa only [hr] using pack_eq (raw >>> 8) (s + 1) (by omega) negative
  · exact pack_eq raw s (by omega) negative

end DogeLib.Work.ArithUint256.Words
