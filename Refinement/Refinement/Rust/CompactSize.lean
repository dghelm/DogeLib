module

public import Refinement.Rust.Generated.DogelibCompactsize
public import DogeLib.Serialization.CompactSize

/-!
# Rust bounded CompactSize refinement

The Rust source follows `ReadCompactSize` of pinned Dogecoin Core (SOURCES.md, D1).
The generated model remains separate from the specification.
-/

@[expose] public section

namespace Refinement.Rust.CompactSize

open Aeneas Aeneas.Std
open DogeLib.Serialization

/-- The Lean byte represented by a Rust byte. -/
def toByte (b : U8) : UInt8 := ⟨b.bv⟩

/-- The bytes of a Rust slice, without its representation proof. -/
def toBytes (s : Slice U8) : List UInt8 := s.val.map toByte

/-- The complete observable result, with Rust panics or divergence represented by `none`. -/
def abstractResult (s : Slice U8) (r : Result DogeLibRust.ReadResult) :
    Option (Except CompactSize.ReadError (UInt64 × List UInt8)) :=
  match r.match with
  | .ok .Truncated => some (.error .truncated)
  | .ok .NonCanonical => some (.error .nonCanonical)
  | .ok .TooLarge => some (.error .tooLarge)
  | .ok (.Success value consumed) => some (.ok (⟨value.bv⟩, (toBytes s).drop consumed.val))
  | _ => none

private theorem join_eq (low : U8) (high : U64) :
    DogeLibRust.join low high = .ok ⟨(high.bv : BitVec 64) * 256#64 + low.bv.setWidth 64⟩ := by
  simp [DogeLibRust.join, lift, UScalar.cast, core.num.U64.wrapping_mul,
    core.num.U64.wrapping_add, UScalar.wrapping_mul, UScalar.wrapping_add]

private theorem join_append (low : U8) (high : BitVec n) :
    DogeLibRust.join low ⟨high.setWidth 64⟩ =
      .ok ⟨(high ++ low.bv).setWidth 64⟩ := by
  rw [join_eq]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt low.bv.isLt]
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.add_mod, Nat.mul_mod]

private theorem scalar_mk_val {ty : UScalarTy} (v : BitVec ty.numBits) : (UScalar.mk v).val = v.toNat := rfl

private theorem byte_mod (b : U8) : b.val % 18446744073709551616 = b.val := by
  have h := b.hBounds
  exact Nat.mod_eq_of_lt (by change b.val < 256 at h; omega)

private theorem zero_byte (b : U8) : (0#0 ++ (b.bv : BitVec 8)) = b.bv := by
  exact BitVec.zero_width_append _ _

private theorem payload_mod (v : BitVec n) (h : n ≤ 64) :
    v.toNat % 18446744073709551616 = v.toNat := by
  exact Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- Every Rust-representable byte slice has the same complete result as the bounded specification.
The slice representation carries the Rust `usize` length bound.
Rust `usize` uses Lean core's opaque platform word size, and the refinement holds on both 32- and 64-bit platforms.
No acceptance precondition restricts the bytes, and `none` would expose a Rust panic or divergence.
-/
theorem decode_refines (s : Slice U8) :
    abstractResult s (DogeLibRust.decode s) = some (CompactSize.decodeBounded (toBytes s)) := by
  generalize hs : s.val = bs
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, bs⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals
    simp [abstractResult, DogeLibRust.decode, toBytes, hs, Slice.index_usize,
      CompactSize.decodeBounded, CompactSize.readCanonical, CompactSize.readPayload,
      decodeBitVecLE, decodeByte, toByte, UScalar.eq_equiv,
      UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt64.lt_iff_toNat_lt,
      UScalar.cast, lift, join_append, CompactSize.maxSize,
      scalar_mk_val, BitVec.toNat_setWidth, byte_mod, zero_byte,
      payload_mod]
    <;> split_ifs <;> simp_all [Result.match.ok, byte_mod, payload_mod] <;> omega

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- On every successful Rust slice read, the consumed count fits the input and is a CompactSize form length. -/
theorem consumed_bounds (s : Slice U8) (value : U64) (consumed : Usize)
    (h : DogeLibRust.decode s = .ok (.Success value consumed)) :
    consumed.val ≤ s.length ∧
      (consumed.val = 1 ∨ consumed.val = 3 ∨ consumed.val = 5 ∨ consumed.val = 9) := by
  generalize hs : s.val = bs
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, bs⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals
    simp [DogeLibRust.decode, Slice.index_usize, hs, UScalar.cast, lift, join_append] at h
    <;> split_ifs at h <;> simp_all [Result.ok.injEq]
    <;> (rcases h with ⟨_, rfl⟩; simp_all)

end Refinement.Rust.CompactSize
