module

public import DogeLib.Serialization.PackedCodec
public import DogeLib.Serialization.Proofs.Codec
public import DogeLib.Base.Proofs.ByteSlice

/-!
# Proofs: `Serialization.PackedCodec`

Each packed codec of `DogeLib.Serialization.PackedCodec` computes what its `Codec` computes, on every input.

`abstractParse` reads a packed decoder result as a list decoder result: it keeps the value, and replaces the remaining slice by its bytes.
The class `LawfulPackedCodec` states the two agreement laws of a packed codec with a `Codec`:

- `toList_encodeInto`: for every value `a` and buffer `acc`, the bytes of `encodeInto a acc` are the bytes of `acc`, followed by `Codec.encode a`.
- `abstractParse_decodeSlice`: for every slice `s`, `abstractParse (decodeSlice s) = Codec.decode s.toList`.
  So the packed decoder fails exactly when the list decoder fails.
  When they succeed, they return the same value, and remainders with the same bytes.

The laws are agreement laws, not codec laws.
A property of the `Codec`, such as its round trip, carries over to the packed codec by a rewrite with these two laws.
No separate theorem states the round trip of a packed codec.

These are the results:

- `instLawfulPackedCodecProd`: the packed pair of two lawful packed codecs agrees with the pair codec.
- `LawfulPackedCodec.ofEquiv`: transport along two functions keeps agreement, as `Codec.ofEquiv` does.
- `abstractParse_readBitVecLE` and `toList_pushBitVecLE`: the packed little-endian primitive agrees with `decodeBitVecLE` and `encodeBitVecLE`.
- `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`: the packed fixed-width integer codecs agree with their codecs.
- `LawfulPackedCodec.toList_encode`, `LawfulPackedCodec.abstractParse_decode` and `LawfulPackedCodec.abstractParse_decode_toByteArray`: the same agreement for a whole byte array.

Adapted from btc-verified, [`BtcVerified/Packed/Codec.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/Codec.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- This file contains `abstractParse` and the theorems of that file.
  The packed codec operations are in `DogeLib/Serialization/PackedCodec.lean`.
- Upstream states the agreement laws as fields of the class `PackedCodec`.
  Here they are the fields of the class `LawfulPackedCodec`, with the same statements.
- Upstream `PackedCodec.ofEquiv` takes a Mathlib `Equiv`.
  Here `LawfulPackedCodec.ofEquiv` takes the two conversion functions and needs no inverse laws, because agreement holds for every pair of functions.
- `LawfulPackedCodec.ofEquiv` and `lawfulPackedCodec_packedBitVecLE` take and give the laws as explicit terms, not as instances, as in `DogeLib.Serialization.Proofs.Codec`.
- The theorems for a whole byte array are in the namespace `LawfulPackedCodec`, where upstream has them in `PackedCodec`.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization

/-! ## The abstraction of packed decoder results -/

/--
A packed decoder result, read as a list decoder result.
It keeps the value, and replaces the remaining slice by its bytes, `ByteSlice.toList`.
It is `Option.map` of `Prod.map id ByteSlice.toList`.
-/
def abstractParse {α : Type} : Option (α × ByteSlice) → Option (α × List UInt8) :=
  Option.map (Prod.map id ByteSlice.toList)

/-- `abstractParse` maps failure to failure. -/
@[simp] theorem abstractParse_none {α : Type} : abstractParse (α := α) none = none := rfl

/-- `abstractParse` maps a result `(a, s)` to `(a, s.toList)`. -/
@[simp] theorem abstractParse_some {α : Type} (a : α) (s : ByteSlice) :
    abstractParse (some (a, s)) = some (a, s.toList) := rfl

/--
One decoder step through the abstraction.
If the packed continuation `f` agrees with the list continuation `g` on every value and slice, then `p.bind f` agrees with `(abstractParse p).bind g`.

The agreement proofs of composite decoders are chains of this lemma, one link per decoded field.
-/
theorem abstractParse_bind {α β : Type} (p : Option (α × ByteSlice))
    {f : α × ByteSlice → Option (β × ByteSlice)}
    {g : α × List UInt8 → Option (β × List UInt8)}
    (h : ∀ a s, abstractParse (f (a, s)) = g (a, s.toList)) :
    abstractParse (p.bind f) = (abstractParse p).bind g := by
  unfold abstractParse
  rw [Option.map_bind, Option.bind_map]
  exact congrArg _ (funext fun q => h q.1 q.2)

/--
A step that reads no bytes, such as a check on a decoded value, through the abstraction.
If the packed continuation `f` agrees with the list continuation `g` on every value, then `p.bind f` agrees with `p.bind g`.
-/
theorem abstractParse_bindValue {α β : Type} (p : Option α)
    {f : α → Option (β × ByteSlice)} {g : α → Option (β × List UInt8)}
    (h : ∀ a, abstractParse (f a) = g a) :
    abstractParse (p.bind f) = p.bind g := by
  unfold abstractParse
  rw [Option.map_bind]
  exact congrArg _ (funext h)

/--
A packed reader result with a typed error, read as a list reader result.
It keeps the error or the value, and replaces the remaining slice by its bytes.
It is the `Except` counterpart of `abstractParse`.
-/
def abstractRead {ε α : Type} : Except ε (α × ByteSlice) → Except ε (α × List UInt8) :=
  Except.map (Prod.map id ByteSlice.toList)

/-- `abstractRead` keeps an error. -/
@[simp] theorem abstractRead_error {ε α : Type} (e : ε) :
    abstractRead (α := α) (.error e : Except ε (α × ByteSlice)) = .error e := rfl

/-- `abstractRead` maps a result `(a, s)` to `(a, s.toList)`. -/
@[simp] theorem abstractRead_ok {ε α : Type} (a : α) (s : ByteSlice) :
    abstractRead (ε := ε) (.ok (a, s)) = .ok (a, s.toList) := rfl

/-- For every slice `s`, `s.uncons` through the abstraction is `decodeByte s.toList`. -/
theorem abstractParse_uncons (s : ByteSlice) :
    abstractParse s.uncons = decodeByte s.toList := by
  cases hu : s.uncons with
  | none =>
    rw [abstractParse_none, ByteSlice.toList_of_uncons_none hu]
    rfl
  | some p =>
    obtain ⟨b, t⟩ := p
    rw [abstractParse_some, ByteSlice.toList_of_uncons_some hu]
    rfl

/-! ## The agreement laws -/

/--
The agreement of a packed codec with a codec of the same type.

An instance is a proof that the `PackedCodec α` instance computes what the `Codec α` instance computes, on every input.
-/
class LawfulPackedCodec (α : Type) [Codec α] [PackedCodec α] : Prop where
  /--
  For every value `a` and buffer `acc`, the bytes of `PackedCodec.encodeInto a acc` are the bytes of `acc` followed by `Codec.encode a`.
  -/
  toList_encodeInto : ∀ (a : α) (acc : ByteArray),
    (PackedCodec.encodeInto a acc).toList = acc.toList ++ Codec.encode a
  /--
  For every slice `s`, `abstractParse (PackedCodec.decodeSlice s) = Codec.decode s.toList`.
  The packed decoder fails exactly when the list decoder fails on the bytes of `s`.
  When they succeed, they return the same value, and remainders with the same bytes.
  -/
  abstractParse_decodeSlice : ∀ s : ByteSlice,
    abstractParse (PackedCodec.decodeSlice (α := α) s) = Codec.decode (α := α) s.toList

namespace LawfulPackedCodec

/-- For a lawful packed codec and every value `a`, the bytes of `PackedCodec.encode a` are `Codec.encode a`. -/
theorem toList_encode {α : Type} [Codec α] [PackedCodec α] [LawfulPackedCodec α] (a : α) :
    (PackedCodec.encode a).toList = Codec.encode a := by
  rw [PackedCodec.encode, toList_encodeInto, ByteArray.toList_empty, List.nil_append]

/--
For a lawful packed codec and every byte array `bytes`, `abstractParse (PackedCodec.decode bytes) = Codec.decode bytes.toList`.
The packed decoder fails exactly when the list decoder fails, and otherwise returns the same value and a remainder with the same bytes.
-/
theorem abstractParse_decode {α : Type} [Codec α] [PackedCodec α] [LawfulPackedCodec α]
    (bytes : ByteArray) :
    abstractParse (PackedCodec.decode (α := α) bytes) = Codec.decode (α := α) bytes.toList := by
  rw [PackedCodec.decode, abstractParse_decodeSlice, ByteSlice.toList_ofByteArray]

/--
For a lawful packed codec and every byte list `bs`, `abstractParse (PackedCodec.decode bs.toByteArray) = Codec.decode bs`.
So on every input of the codec, the packed decoder has the same failures, values and remainder bytes.
-/
theorem abstractParse_decode_toByteArray {α : Type} [Codec α] [PackedCodec α]
    [LawfulPackedCodec α] (bs : List UInt8) :
    abstractParse (PackedCodec.decode (α := α) bs.toByteArray) = Codec.decode (α := α) bs := by
  rw [abstractParse_decode, List.toList_toByteArray]

end LawfulPackedCodec

/-! ## Pairs -/

/-- For lawful packed codecs of `α` and `β`, the packed pair codec `instPackedCodecProd` agrees with the pair codec `instCodecProd`. -/
instance instLawfulPackedCodecProd {α β : Type} [Codec α] [Codec β]
    [PackedCodec α] [PackedCodec β] [LawfulPackedCodec α] [LawfulPackedCodec β] :
    LawfulPackedCodec (α × β) where
  toList_encodeInto p acc := by
    change (PackedCodec.encodeInto p.2 (PackedCodec.encodeInto p.1 acc)).toList
      = acc.toList ++ (Codec.encode p.1 ++ Codec.encode p.2)
    rw [LawfulPackedCodec.toList_encodeInto, LawfulPackedCodec.toList_encodeInto,
      List.append_assoc]
  abstractParse_decodeSlice s := by
    change _ = decodeProd s.toList
    unfold decodeProd
    rw [← LawfulPackedCodec.abstractParse_decodeSlice (α := α) s]
    refine abstractParse_bind _ fun a s1 => ?_
    dsimp only
    rw [← LawfulPackedCodec.abstractParse_decodeSlice (α := β) s1]
    exact abstractParse_bind _ fun b s2 => rfl

/-! ## Transport -/

/--
For functions `toFun : α → β` and `invFun : β → α`, and a packed codec `pb` that agrees with the codec `cb`, the packed codec `PackedCodec.ofEquiv toFun invFun pb` agrees with `Codec.ofEquiv toFun invFun cb`.

Agreement needs no inverse laws.
The laws of `Codec.ofEquiv toFun invFun cb` need them (`LawfulCodec.ofEquiv`).
-/
theorem LawfulPackedCodec.ofEquiv {α β : Type} (toFun : α → β) (invFun : β → α)
    (cb : Codec β) (pb : PackedCodec β) (hb : @LawfulPackedCodec β cb pb) :
    @LawfulPackedCodec α (Codec.ofEquiv toFun invFun cb) (PackedCodec.ofEquiv toFun invFun pb) :=
  letI := cb
  letI := pb
  @LawfulPackedCodec.mk α (Codec.ofEquiv toFun invFun cb) (PackedCodec.ofEquiv toFun invFun pb)
    (fun a acc => LawfulPackedCodec.toList_encodeInto (α := β) (toFun a) acc)
    (fun s => by
      change abstractParse ((pb.decodeSlice s).map fun p => (invFun p.1, p.2))
        = (cb.decode s.toList).map fun p => (invFun p.1, p.2)
      rw [show cb.decode s.toList = Codec.decode (α := β) s.toList from rfl,
        ← LawfulPackedCodec.abstractParse_decodeSlice (α := β) s]
      cases pb.decodeSlice s with
      | none => rfl
      | some p => rfl)

/-! ## Little-endian fixed-width values -/

/-- For every `n` and slice `s`, `abstractParse (readBitVecLE n s) = decodeBitVecLE n s.toList`. -/
theorem abstractParse_readBitVecLE :
    ∀ (n : Nat) (s : ByteSlice),
      abstractParse (readBitVecLE n s) = decodeBitVecLE n s.toList := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [readBitVecLE, decodeBitVecLE]
    rw [← abstractParse_uncons s]
    refine abstractParse_bind _ fun b s1 => ?_
    dsimp only
    rw [← ih s1]
    exact abstractParse_bind _ fun hi rest => rfl

/-- For every `n`, `v : BitVec (8 * n)` and buffer `acc`, the bytes of `pushBitVecLE n v acc` are the bytes of `acc` followed by `encodeBitVecLE n v`. -/
theorem toList_pushBitVecLE :
    ∀ (n : Nat) (v : BitVec (8 * n)) (acc : ByteArray),
      (pushBitVecLE n v acc).toList = acc.toList ++ encodeBitVecLE n v := by
  intro n
  induction n with
  | zero => intro v acc; simp [pushBitVecLE, encodeBitVecLE]
  | succ n ih =>
    intro v acc
    simp [pushBitVecLE, encodeBitVecLE, ih]

/-- For every `n`, the packed little-endian codec `packedBitVecLE n` agrees with `bitVecCodecLE n`. -/
theorem lawfulPackedCodec_packedBitVecLE (n : Nat) :
    @LawfulPackedCodec (BitVec (8 * n)) (bitVecCodecLE n) (packedBitVecLE n) :=
  @LawfulPackedCodec.mk _ (bitVecCodecLE n) (packedBitVecLE n)
    (toList_pushBitVecLE n) (abstractParse_readBitVecLE n)

/-- The packed `UInt8` codec agrees with `instCodecUInt8`. -/
instance instLawfulPackedCodecUInt8 : LawfulPackedCodec UInt8 :=
  LawfulPackedCodec.ofEquiv UInt8.toBitVec UInt8.ofBitVec
    (bitVecCodecLE 1) (packedBitVecLE 1) (lawfulPackedCodec_packedBitVecLE 1)

/-- The packed `UInt16` codec agrees with `instCodecUInt16`. -/
instance instLawfulPackedCodecUInt16 : LawfulPackedCodec UInt16 :=
  LawfulPackedCodec.ofEquiv UInt16.toBitVec UInt16.ofBitVec
    (bitVecCodecLE 2) (packedBitVecLE 2) (lawfulPackedCodec_packedBitVecLE 2)

/-- The packed `UInt32` codec agrees with `instCodecUInt32`. -/
instance instLawfulPackedCodecUInt32 : LawfulPackedCodec UInt32 :=
  LawfulPackedCodec.ofEquiv UInt32.toBitVec UInt32.ofBitVec
    (bitVecCodecLE 4) (packedBitVecLE 4) (lawfulPackedCodec_packedBitVecLE 4)

/-- The packed `UInt64` codec agrees with `instCodecUInt64`. -/
instance instLawfulPackedCodecUInt64 : LawfulPackedCodec UInt64 :=
  LawfulPackedCodec.ofEquiv UInt64.toBitVec UInt64.ofBitVec
    (bitVecCodecLE 8) (packedBitVecLE 8) (lawfulPackedCodec_packedBitVecLE 8)

end DogeLib.Serialization
