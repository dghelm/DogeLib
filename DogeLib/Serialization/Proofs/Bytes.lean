module

public import DogeLib.Base.Proofs.ByteArray
public import DogeLib.Base.Proofs.ByteSlice
public import DogeLib.Base.Proofs.Bytes
public import DogeLib.Serialization.Bytes
public import DogeLib.Serialization.Proofs.Codec
public import DogeLib.Serialization.Proofs.PackedCodec

/-!
# Proofs: `Serialization.Bytes`

The laws of the codec of `Bytes n`, and the agreement of its packed codec.

- `decodeBytes_encode` and `decodeBytes_canonical`: the round trip and canonicality, for every `n`, packaged as `instLawfulCodecBytes`.
- `decodeBytes_eq_none_iff`: the decoder rejects exactly the inputs with fewer than `n` bytes.
- `toList_pushBytes`: `pushBytes` appends exactly the bytes of the list.
- `abstractParse_readBytes`: the packed decoder agrees with `decodeBytes`. With `toList_pushBytes`, it gives `instLawfulPackedCodecBytes`.

Adapted from btc-verified, [`BtcVerified/Serialize/Bytes.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Bytes.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream proves the laws inside the instances. Here they are separate theorems and the instances `instLawfulCodecBytes` and `instLawfulPackedCodecBytes`.
- `abstractParse_readBytes` also shows that the check `Bytes.ofListExact?` of `readBytes` never fails.
- `decodeBytes_eq_none_iff` is DogeLib's.
- Lean `v4.35.0` deprecates `dif_pos` and `dif_neg`, so the proofs use `simp` with the condition, or their replacements `dite_eq_left` and `dite_eq_right`.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/--
For every `n` and all bytes `bs`, `decodeBytes n bs` is the read with the test `n ≤ bs.length`.
It gives the first `n` bytes and the rest when the test holds, and `none` when it fails.
-/
theorem decodeBytes_eq_dite (n : Nat) (bs : List UInt8) :
    decodeBytes n bs =
      if h : n ≤ bs.length then some (⟨bs.take n, List.length_take_of_le h⟩, bs.drop n) else none := by
  unfold decodeBytes
  by_cases h : n ≤ bs.length
  · rw [dite_eq_left (List.length_take_of_le h), dite_eq_left h]
  · have ht : ¬ (bs.take n).length = n := fun e => h (e ▸ List.length_take_le' n bs)
    rw [dite_eq_right ht, dite_eq_right h]

/-- The round trip: for every `n`, every `b : Bytes n` and all bytes `rest`, `decodeBytes n (b.val ++ rest) = some (b, rest)`. -/
theorem decodeBytes_encode {n : Nat} (b : Bytes n) (rest : List UInt8) :
    decodeBytes n (b.val ++ rest) = some (b, rest) := by
  obtain ⟨bs, hb⟩ := b
  subst hb
  simp [decodeBytes_eq_dite]

/-- Canonicality: for every `n`, if `decodeBytes n bs = some (b, rest)`, then `bs = b.val ++ rest`. -/
theorem decodeBytes_canonical {n : Nat} (bs : List UInt8) (b : Bytes n) (rest : List UInt8)
    (h : decodeBytes n bs = some (b, rest)) : bs = b.val ++ rest := by
  rw [decodeBytes_eq_dite] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (List.take_append_drop n bs).symm
  · cases h

/-- For every `n` and all bytes `bs`, `decodeBytes n bs = none` exactly when `bs` has fewer than `n` bytes. -/
theorem decodeBytes_eq_none_iff (n : Nat) (bs : List UInt8) :
    decodeBytes n bs = none ↔ bs.length < n := by
  rw [decodeBytes_eq_dite]
  split
  · next h => simp only [reduceCtorEq, false_iff, Nat.not_lt]; exact h
  · next h => simp only [true_iff]; omega

/-- For every `n`, the codec of `Bytes n` is lawful. -/
instance instLawfulCodecBytes (n : Nat) : LawfulCodec (Bytes n) where
  decode_encode := decodeBytes_encode
  decode_canonical := decodeBytes_canonical

/-- For every `b : Bytes n`, the encoding of `b` has `n` bytes. -/
theorem _root_.DogeLib.Bytes.encode_length {n : Nat} (b : Bytes n) : (Codec.encode b).length = n := b.property

/-- For every list of bytes `bs` and buffer `acc`, the bytes of `pushBytes bs acc` are the bytes of `acc` followed by `bs`. -/
theorem toList_pushBytes (bs : List UInt8) (acc : ByteArray) :
    (pushBytes bs acc).toList = acc.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [pushBytes]
  | cons b bs ih =>
    change (pushBytes bs (acc.push b)).toList = _
    rw [ih, ByteArray.toList_push, List.append_assoc, List.singleton_append]

/--
For every `n` and every slice `s`, `abstractParse (readBytes n s) = decodeBytes n s.toList`.
So the check `Bytes.ofListExact?` inside `readBytes` never fails.
-/
theorem abstractParse_readBytes (n : Nat) (s : ByteSlice) :
    abstractParse (readBytes n s) = decodeBytes n s.toList := by
  rw [decodeBytes_eq_dite]
  unfold readBytes
  by_cases h : n ≤ s.size
  · have hl : ((s.take n).toList).length = n := by
      rw [ByteSlice.length_toList, ByteSlice.size_take, Nat.min_eq_left h]
    have e : Bytes.ofListExact? (n := n) (s.take n).toList = some ⟨(s.take n).toList, hl⟩ :=
      Bytes.ofListExact?_val ⟨(s.take n).toList, hl⟩
    simp only [h, ite_true, e]
    simp [h, ByteSlice.toList_take]
  · simp [h, abstractParse_none]

/-- For every `n`, the packed codec of `Bytes n` agrees with its codec. -/
instance instLawfulPackedCodecBytes (n : Nat) : LawfulPackedCodec (Bytes n) where
  toList_encodeInto b acc := toList_pushBytes b.val acc
  abstractParse_decodeSlice := abstractParse_readBytes n

end DogeLib.Serialization
