module

public import DogeLib.Serialization.Codec

/-!
# Proofs: `Serialization.Codec`

The codec laws, and a proof of both laws for each codec of `DogeLib.Serialization.Codec`.

The class `LawfulCodec` states the two laws of a codec:

- `decode_encode`, the round trip: decoding the encoding of `a`, followed by any bytes `rest`, returns `a` and the remainder `rest`.
- `decode_canonical`, canonicality: if decoding `bs` returns `a` and the remainder `rest`, then `bs` is the encoding of `a` followed by `rest`.
  So the decoder accepts no encoding of a value other than `encode a`.

Together the laws say that `encode` is a bijection onto the byte strings that the decoder accepts and consumes completely.

These are the results:

- `encode_injective`: two values with the same encoding are equal.
- `instLawfulCodecProd`: the pair of two lawful codecs is lawful.
- `LawfulCodec.ofEquiv`: a codec carried along two inverse functions is lawful.
- `decodeBitVecLE_encodeBitVecLE` and `decodeBitVecLE_canonical`: the two laws for the little-endian codec of `BitVec (8 * n)`, packaged as `lawfulCodec_bitVecCodecLE`.
- `decodeBitVecLE_of_le_length` and `encodeBitVecLE_length`: the little-endian decoder succeeds on every input of at least `n` bytes, and the encoding has exactly `n` bytes.
- `instLawfulCodecUInt8` to `instLawfulCodecUInt64`: the fixed-width integer codecs are lawful.

Adapted from btc-verified, [`BtcVerified/Serialize/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Codec.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- This file contains only the laws and the theorems of that file.
  Its definitions are in `DogeLib/Serialization/Codec.lean`.
- Upstream states the laws as fields of the class `Codec`.
  Here they are the fields of the class `LawfulCodec`, with the same statements.
- Upstream `Codec.ofEquiv` proves the laws from a Mathlib `Equiv`.
  Here `LawfulCodec.ofEquiv` takes the two inverse laws of that `Equiv` as hypotheses, and its proof uses no Mathlib lemma.
- `LawfulCodec.ofEquiv` and `lawfulCodec_bitVecCodecLE` take and give the laws as explicit terms, not as instances.
  Instance search cannot match `BitVec 8` with `BitVec (8 * n)`, so the fixed-width instances pass the laws explicitly.
- Lean `v4.35.0` deprecates `if_pos` and `if_neg`, so the `BitVec` lemmas use `ite_eq_left` and `ite_eq_right`.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/--
The laws of a codec: the round trip and canonicality.

An instance is a proof that the `Codec α` instance satisfies both laws.
-/
class LawfulCodec (α : Type) [Codec α] : Prop where
  /--
  The round trip: for every value `a` and bytes `rest`, decoding `encode a ++ rest` returns `a` and the remainder `rest`.
  -/
  decode_encode : ∀ (a : α) (rest : List UInt8),
    Codec.decode (Codec.encode a ++ rest) = some (a, rest)
  /--
  Canonicality: for all bytes `bs`, values `a` and bytes `rest`, if decoding `bs` returns `a` and the remainder `rest`, then `bs = encode a ++ rest`.
  -/
  decode_canonical : ∀ (bs : List UInt8) (a : α) (rest : List UInt8),
    Codec.decode bs = some (a, rest) → bs = Codec.encode a ++ rest

/-- For every lawful codec, two values with the same encoding are equal: `encode` is injective. -/
theorem encode_injective {α : Type} [Codec α] [LawfulCodec α] {a b : α}
    (h : Codec.encode a = Codec.encode b) : a = b := by
  have ha := LawfulCodec.decode_encode a ([] : List UInt8)
  have hb := LawfulCodec.decode_encode b ([] : List UInt8)
  rw [List.append_nil] at ha hb
  rw [h, hb] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  exact ha.1.symm

/-! ## Pairs -/

/--
For lawful codecs of `α` and `β`, and for all `a`, `b` and `rest`, `decodeProd ((encode a ++ encode b) ++ rest)` returns `(a, b)` and the remainder `rest`.
-/
theorem decodeProd_encode {α β : Type} [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β]
    (a : α) (b : β) (rest : List UInt8) :
    decodeProd ((Codec.encode a ++ Codec.encode b) ++ rest) = some ((a, b), rest) := by
  unfold decodeProd
  simp only [List.append_assoc, Option.bind_eq_bind, LawfulCodec.decode_encode,
    Option.bind_some, Option.pure_def]

/--
For lawful codecs of `α` and `β`, if `decodeProd bs` returns `(a, b)` and the remainder `rest`, then `bs = (encode a ++ encode b) ++ rest`.
-/
theorem decodeProd_canonical {α β : Type} [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β]
    (bs : List UInt8) (a : α) (b : β) (rest : List UInt8) :
    decodeProd bs = some ((a, b), rest) →
    bs = (Codec.encode a ++ Codec.encode b) ++ rest := by
  intro h
  unfold decodeProd at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨a', r1⟩, hd, ⟨b', r2⟩, hd2, ⟨ha, hb⟩, hr⟩ := h
  subst ha; subst hb; subst hr
  rw [LawfulCodec.decode_canonical bs a' r1 hd, LawfulCodec.decode_canonical r1 b' r2 hd2,
    List.append_assoc]

/-- For lawful codecs of `α` and `β`, the codec of pairs `instCodecProd` is lawful. -/
instance instLawfulCodecProd {α β : Type} [Codec α] [Codec β] [LawfulCodec α] [LawfulCodec β] :
    LawfulCodec (α × β) where
  decode_encode := fun (a, b) rest => decodeProd_encode a b rest
  decode_canonical := fun bs (a, b) rest h => decodeProd_canonical bs a b rest h

/-! ## Transport -/

/--
For a lawful codec `cb` of `β`, and functions `toFun : α → β` and `invFun : β → α` that are inverse to each other, the codec `Codec.ofEquiv toFun invFun cb` of `α` is lawful.

The hypotheses are the two laws of a bijection:
`invFun (toFun a) = a` for every `a`, and `toFun (invFun b) = b` for every `b`.
-/
theorem LawfulCodec.ofEquiv {α β : Type} (toFun : α → β) (invFun : β → α)
    (left_inv : ∀ a, invFun (toFun a) = a) (right_inv : ∀ b, toFun (invFun b) = b)
    (cb : Codec β) (hb : @LawfulCodec β cb) :
    @LawfulCodec α (Codec.ofEquiv toFun invFun cb) :=
  letI := cb
  @LawfulCodec.mk α (Codec.ofEquiv toFun invFun cb)
    (fun a rest => by
      show (cb.decode (cb.encode (toFun a) ++ rest)).map _ = _
      rw [LawfulCodec.decode_encode (α := β) (toFun a) rest]
      simp [left_inv])
    (fun bs a rest h => by
      change (cb.decode bs).map (fun p => (invFun p.1, p.2)) = some (a, rest) at h
      show bs = cb.encode (toFun a) ++ rest
      cases hdec : cb.decode bs with
      | none => rw [hdec] at h; simp [Option.map] at h
      | some p =>
        obtain ⟨b, rest'⟩ := p
        rw [hdec] at h
        simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hb, hr⟩ := h
        subst hr
        have hb' : b = toFun a := by rw [← hb, right_inv]
        subst hb'
        exact LawfulCodec.decode_canonical (α := β) bs (toFun a) rest' hdec)

/-! ## Little-endian fixed-width values -/

/-- For every `n` and `hi : BitVec (8 * n)`, and every byte `lo : BitVec 8`, the low byte of `hi ++ lo` is `lo`. -/
private theorem setWidth_append_low {n : Nat} (hi : BitVec (8 * n)) (lo : BitVec 8) :
    (hi ++ lo).setWidth 8 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi8
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi8]

/-- For every `n` and `hi : BitVec (8 * n)`, and every byte `lo : BitVec 8`, shifting `hi ++ lo` right by 8 bits and truncating to `8 * n` bits gives `hi`. -/
private theorem setWidth_ushiftRight_append {n : Nat} (hi : BitVec (8 * n)) (lo : BitVec 8) :
    ((hi ++ lo) >>> 8).setWidth (8 * n) = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hin
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  have h1 : ¬ (8 + i < 8) := by omega
  have h2 : 8 + i - 8 = i := by omega
  rw [ite_eq_right h1, h2]
  simp [hin]

/-- For every `v : BitVec (8 * (n + 1))`, the high `8 * n` bits of `v`, followed by its low byte, are `v`. -/
private theorem append_split {n : Nat} (v : BitVec (8 * (n + 1))) :
    ((v >>> 8).setWidth (8 * n)) ++ (v.setWidth 8) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hilt
  rw [BitVec.getLsbD_append]
  by_cases h8 : i < 8
  · rw [ite_eq_left h8, BitVec.getLsbD_setWidth]; simp [h8]
  · rw [ite_eq_right h8, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    have h1 : i - 8 < 8 * n := by omega
    have h2 : 8 + (i - 8) = i := by omega
    rw [h2]; simp [h1]

/--
The round trip of the little-endian codec: for every `n`, value `v : BitVec (8 * n)` and bytes `rest`, `decodeBitVecLE n (encodeBitVecLE n v ++ rest) = some (v, rest)`.
-/
theorem decodeBitVecLE_encodeBitVecLE :
    ∀ (n : Nat) (v : BitVec (8 * n)) (rest : List UInt8),
      decodeBitVecLE n (encodeBitVecLE n v ++ rest) = some (v, rest) := by
  intro n
  induction n with
  | zero =>
    intro v rest
    have hv : v = 0#0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; exact absurd hi (by omega)
    subst hv
    rfl
  | succ n ih =>
    intro v rest
    simp only [encodeBitVecLE, List.cons_append, decodeBitVecLE, decodeByte,
      Option.bind_eq_bind, Option.bind_some, ih, Option.pure_def]
    rw [append_split v]

/--
Canonicality of the little-endian codec: for every `n` and all bytes `bs`, if `decodeBitVecLE n bs = some (v, rest)`, then `bs = encodeBitVecLE n v ++ rest`.
-/
theorem decodeBitVecLE_canonical :
    ∀ (n : Nat) (bs : List UInt8) (v : BitVec (8 * n)) (rest : List UInt8),
      decodeBitVecLE n bs = some (v, rest) → bs = encodeBitVecLE n v ++ rest := by
  intro n
  induction n with
  | zero =>
    intro bs v rest h
    simp only [decodeBitVecLE, Option.some.injEq, Prod.mk.injEq] at h
    simp only [encodeBitVecLE, List.nil_append, h.2]
  | succ n ih =>
    intro bs v rest h
    cases bs with
    | nil => simp [decodeBitVecLE, decodeByte] at h
    | cons b bs' =>
      simp only [decodeBitVecLE, decodeByte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hi, r⟩, hd, hv, hr'⟩ := h
      have ihbs := ih bs' hi r hd
      subst hr'; subst hv
      simp only [encodeBitVecLE, List.cons_append, setWidth_append_low,
        setWidth_ushiftRight_append, UInt8.ofBitVec_toBitVec, ihbs]

/--
For every `n` and all bytes `bs` with at least `n` bytes, `decodeBitVecLE n bs` succeeds and returns the remainder `bs.drop n`.
-/
theorem decodeBitVecLE_of_le_length :
    ∀ (n : Nat) (bs : List UInt8), n ≤ bs.length →
      ∃ v, decodeBitVecLE n bs = some (v, bs.drop n) := by
  intro n
  induction n with
  | zero => exact fun bs _ => ⟨0#0, rfl⟩
  | succ n ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bs' =>
      obtain ⟨v, hv⟩ := ih bs' (by simpa using h)
      exact ⟨v ++ b.toBitVec, by simp [decodeBitVecLE, decodeByte, hv]⟩

/-- For every `n` and `v : BitVec (8 * n)`, `encodeBitVecLE n v` has exactly `n` bytes. -/
theorem encodeBitVecLE_length :
    ∀ (n : Nat) (v : BitVec (8 * n)), (encodeBitVecLE n v).length = n := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih => intro v; simp [encodeBitVecLE, List.length_cons, ih]

/-- For every `n`, the little-endian codec `bitVecCodecLE n` is lawful. -/
theorem lawfulCodec_bitVecCodecLE (n : Nat) : @LawfulCodec (BitVec (8 * n)) (bitVecCodecLE n) :=
  @LawfulCodec.mk _ (bitVecCodecLE n)
    (decodeBitVecLE_encodeBitVecLE n) (decodeBitVecLE_canonical n)

/-- The `UInt8` codec `instCodecUInt8` is lawful. -/
instance instLawfulCodecUInt8 : LawfulCodec UInt8 :=
  LawfulCodec.ofEquiv UInt8.toBitVec UInt8.ofBitVec (fun _ => rfl) (fun _ => rfl)
    (bitVecCodecLE 1) (lawfulCodec_bitVecCodecLE 1)

/-- The `UInt16` codec `instCodecUInt16` is lawful. -/
instance instLawfulCodecUInt16 : LawfulCodec UInt16 :=
  LawfulCodec.ofEquiv UInt16.toBitVec UInt16.ofBitVec (fun _ => rfl) (fun _ => rfl)
    (bitVecCodecLE 2) (lawfulCodec_bitVecCodecLE 2)

/-- The `UInt32` codec `instCodecUInt32` is lawful. -/
instance instLawfulCodecUInt32 : LawfulCodec UInt32 :=
  LawfulCodec.ofEquiv UInt32.toBitVec UInt32.ofBitVec (fun _ => rfl) (fun _ => rfl)
    (bitVecCodecLE 4) (lawfulCodec_bitVecCodecLE 4)

/-- The `UInt64` codec `instCodecUInt64` is lawful. -/
instance instLawfulCodecUInt64 : LawfulCodec UInt64 :=
  LawfulCodec.ofEquiv UInt64.toBitVec UInt64.ofBitVec (fun _ => rfl) (fun _ => rfl)
    (bitVecCodecLE 8) (lawfulCodec_bitVecCodecLE 8)

end DogeLib.Serialization
