module

public import DogeLib.Base.Proofs.ByteArray
public import DogeLib.Serialization.Proofs.Bytes
public import DogeLib.Serialization.CountedList
public import DogeLib.Serialization.Proofs.Codec
public import DogeLib.Serialization.Proofs.CompactSize
public import DogeLib.Serialization.Proofs.PackedCodec

/-!
# Proofs: `Serialization.CountedList`

The laws of the generic counted-list codec, the agreement of its packed forms, and the contract of Core's bounded reader.

## The generic codec

- `decodeElems_encodeElems` and `decodeElems_canonical`: the round trip and canonicality of a sequence of `n` elements, for every lawful element codec.
- `decode_encode` and `decode_canonical`: the round trip and canonicality of `CountedList.decode`, packaged as `instLawfulCodecCountedList`.
  They hold for every lawful element codec, every counted list, every input and every remainder.
- `decode_eq_some_iff`: `CountedList.decode` accepts exactly a count from `CompactSize.decode`, followed by that many elements.

## The packed codecs

- `instLawfulPackedCodecCountedList`: the packed codec agrees with the codec, for every element codec whose packed codec agrees with it.
- `encode_uint8`, `encodeElems_uint8` and `decodeElems_uint8`: a list of bytes encodes as itself, and `n` byte elements decode as the first `n` bytes.
- `instLawfulPackedCodecCountedListBytes`: the packed codec of byte lists, which reads the bytes as one block, agrees with the same codec.

## Core's bounded reader

The contract of `CountedList.decodeBounded` assumes that the element reader `elem` accepts exactly what the element codec accepts: `(elem bs).toOption = Codec.decode bs` for every `bs`.
The hypothesis says nothing about which error `elem` reports.
`readByte_toOption` proves it for `readByte` and the codec of `UInt8`.

- `decodeBounded_eq_ok_iff`: the reader returns `(cl, rest)` exactly when the generic `CountedList.decode` returns `(cl, rest)` and `cl` has at most `0x02000000` elements.
- `decodeBounded_encode`: the round trip, for lawful element codecs and lists of at most `0x02000000` elements.
- `decodeBounded_of_count_error`: for every element reader, an error of Core's count reader is the error of the list reader.
  So a count above `MAX_SIZE` is `tooLarge` whatever bytes follow it.
- `decodeBoundedBytes_eq`: the block read of bytes, `decodeBoundedBytes`, is `decodeBounded readByte`.

No theorem says which error the reader reports when an element fails.
That error is the error of `elem`.

## Source

The sections *The generic codec* and *The packed codecs* of this file are adapted from btc-verified.
The source is [`BtcVerified/Serialize/CountedList.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CountedList.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream proves the laws inside the instances of `Codec` and `PackedCodec`.
  Here they are the instances `instLawfulCodecCountedList`, `instLawfulPackedCodecCountedList` and `instLawfulPackedCodecCountedListBytes`.
- The theorems take the hypotheses `LawfulCodec α` and `LawfulPackedCodec α`, because the classes `Codec` and `PackedCodec` here have no laws.
- `decode_eq_some_iff` is DogeLib's.
- Lean `v4.35.0` deprecates `if_pos` and `if_neg`, so the proofs use `simp` with the condition.
- The namespace, the module header and the doc comments are DogeLib's.

The section *Core's bounded reader* is DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization.CountedList

/-! ## The generic codec -/

/-- For every list `l` with fewer than `2 ^ 64` elements, `ofList? l` is `l` as a counted list. -/
theorem ofList?_eq_some {α : Type} {l : List α} (h : l.length < 2 ^ 64) :
    ofList? l = some ⟨l, h⟩ := by
  simp only [ofList?, h, dite_true]

/-- If `ofList? l = some cl`, then the list of `cl` is `l`. -/
theorem val_of_ofList? {α : Type} {l : List α} {cl : CountedList α}
    (h : ofList? l = some cl) : cl.val = l := by
  unfold ofList? at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · exact absurd h (by simp)

/-- For every element codec, if `decodeElems n bs = some (xs, rest)`, then `xs` has `n` elements. -/
theorem decodeElems_length {α : Type} [Codec α] (n : Nat) (bs : List UInt8)
    (xs : List α) (rest : List UInt8) (h : decodeElems n bs = some (xs, rest)) :
    xs.length = n := by
  induction n generalizing bs xs rest with
  | zero =>
    simp only [decodeElems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; rfl
  | succ n ih =>
    simp only [decodeElems, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨x, r1⟩, _, ⟨xs', r2⟩, hd2, rfl, rfl⟩ := h
    simp only [List.length_cons]
    rw [ih r1 xs' r2 hd2]

/--
The round trip of a sequence of elements: for every lawful element codec, every list `xs` and all bytes `rest`, `decodeElems xs.length (encodeElems xs ++ rest) = some (xs, rest)`.
-/
theorem decodeElems_encodeElems {α : Type} [Codec α] [LawfulCodec α]
    (xs : List α) (rest : List UInt8) :
    decodeElems xs.length (encodeElems xs ++ rest) = some (xs, rest) := by
  induction xs generalizing rest with
  | nil => rfl
  | cons x xs ih =>
    simp only [encodeElems, List.append_assoc, List.length_cons, decodeElems, Option.bind_eq_bind,
      LawfulCodec.decode_encode, Option.bind_some, ih, Option.pure_def]

/--
Canonicality of a sequence of elements: for every lawful element codec, if `decodeElems n bs = some (xs, rest)`, then `bs = encodeElems xs ++ rest`.
-/
theorem decodeElems_canonical {α : Type} [Codec α] [LawfulCodec α] (n : Nat) (bs : List UInt8)
    (xs : List α) (rest : List UInt8) (h : decodeElems n bs = some (xs, rest)) :
    bs = encodeElems xs ++ rest := by
  induction n generalizing bs xs rest with
  | zero =>
    simp only [decodeElems, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | succ n ih =>
    simp only [decodeElems, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨x, r1⟩, hd, ⟨xs', r2⟩, hd2, rfl, rfl⟩ := h
    have e1 := LawfulCodec.decode_canonical bs x r1 hd
    have e2 := ih r1 xs' r2 hd2
    rw [e1, e2, encodeElems, List.append_assoc]

/--
For every element codec, `CountedList.decode bs = some (cl, rest)` exactly when `CompactSize.decode bs` reads a count with a remainder `r`, and `decodeElems` reads the elements of `cl` from `r` with the remainder `rest`.
-/
theorem decode_eq_some_iff {α : Type} [Codec α] (bs : List UInt8) (cl : CountedList α)
    (rest : List UInt8) :
    CountedList.decode bs = some (cl, rest) ↔
      ∃ count r, CompactSize.decode bs = some (count, r) ∧
        decodeElems count.toNat r = some (cl.val, rest) := by
  constructor
  · intro h
    simp only [CountedList.decode, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨count, r0⟩, hc, ⟨xs, r1⟩, he, cl', hof, rfl, rfl⟩ := h
    rw [val_of_ofList? hof]
    exact ⟨count, r0, hc, he⟩
  · rintro ⟨count, r, hc, he⟩
    simp only [CountedList.decode, Option.bind_eq_bind, Option.pure_def, hc, Option.bind_some, he,
      ofList?_eq_some cl.property]

/--
The round trip of the generic codec: for every lawful element codec, every counted list `cl` and all bytes `rest`, `CountedList.decode (CountedList.encode cl ++ rest) = some (cl, rest)`.
-/
theorem decode_encode {α : Type} [Codec α] [LawfulCodec α]
    (cl : CountedList α) (rest : List UInt8) :
    CountedList.decode (CountedList.encode cl ++ rest) = some (cl, rest) := by
  obtain ⟨l, hl⟩ := cl
  rw [decode_eq_some_iff]
  have hc : (UInt64.ofNat l.length).toNat = l.length := UInt64.toNat_ofNat_of_lt' hl
  refine ⟨UInt64.ofNat l.length, encodeElems l ++ rest, ?_, ?_⟩
  · rw [CountedList.encode, List.append_assoc, CompactSize.decode_encode]
  · rw [hc]
    exact decodeElems_encodeElems l rest

/--
Canonicality of the generic codec: for every lawful element codec, if `CountedList.decode bs = some (cl, rest)`, then `bs = CountedList.encode cl ++ rest`.
So the decoder accepts only the canonical count, followed by the canonical encodings of the elements.
-/
theorem decode_canonical {α : Type} [Codec α] [LawfulCodec α]
    (bs : List UInt8) (cl : CountedList α) (rest : List UInt8)
    (h : CountedList.decode bs = some (cl, rest)) :
    bs = CountedList.encode cl ++ rest := by
  obtain ⟨count, r0, hcs, hln⟩ := (decode_eq_some_iff bs cl rest).mp h
  have ecs := CompactSize.decode_canonical bs count r0 hcs
  have eel := decodeElems_canonical count.toNat r0 cl.val rest hln
  have hlen : cl.val.length = count.toNat := decodeElems_length count.toNat r0 cl.val rest hln
  have hcnt : count = UInt64.ofNat cl.val.length := by
    rw [hlen, UInt64.ofNat_toNat]
  unfold CountedList.encode
  rw [ecs, eel, hcnt, List.append_assoc]

end DogeLib.Serialization.CountedList

namespace DogeLib.Serialization

open CountedList

/-- For every lawful element codec, the codec of counted lists `instCodecCountedList` is lawful. -/
instance instLawfulCodecCountedList {α : Type} [Codec α] [LawfulCodec α] :
    LawfulCodec (CountedList α) where
  decode_encode := CountedList.decode_encode
  decode_canonical := CountedList.decode_canonical

end DogeLib.Serialization

namespace DogeLib.Serialization.CountedList

/-! ## The packed codecs -/

/-- For every element codec with a lawful packed codec, the bytes of `pushElems xs acc` are the bytes of `acc` followed by `encodeElems xs`. -/
theorem toList_pushElems {α : Type} [Codec α] [PackedCodec α] [LawfulPackedCodec α]
    (xs : List α) (acc : ByteArray) :
    (pushElems xs acc).toList = acc.toList ++ encodeElems xs := by
  induction xs generalizing acc with
  | nil => simp [pushElems, encodeElems]
  | cons x xs ih =>
    rw [pushElems, ih, LawfulPackedCodec.toList_encodeInto, encodeElems, List.append_assoc]

/-- For every element codec with a lawful packed codec, every `n` and every slice `s`, `abstractParse (readElems n s) = decodeElems n s.toList`. -/
theorem abstractParse_readElems {α : Type} [Codec α] [PackedCodec α] [LawfulPackedCodec α] :
    ∀ (n : Nat) (s : ByteSlice),
      abstractParse (readElems (α := α) n s) = decodeElems (α := α) n s.toList := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [readElems, decodeElems]
    rw [← LawfulPackedCodec.abstractParse_decodeSlice (α := α) s]
    refine abstractParse_bind _ fun x s1 => ?_
    dsimp only
    rw [← ih s1]
    exact abstractParse_bind _ fun xs s2 => rfl

/-- For every byte `b`, the codec of `UInt8` encodes `b` as the one byte `[b]`. -/
theorem encode_uint8 (b : UInt8) : Codec.encode b = [b] := by
  change encodeBitVecLE 1 b.toBitVec = [b]
  simp [encodeBitVecLE, BitVec.setWidth_eq, UInt8.ofBitVec_toBitVec]

/-- For every byte `b` and all bytes `t`, the codec of `UInt8` decodes `b :: t` as `b` with the remainder `t`. -/
theorem decode_uint8_cons (b : UInt8) (t : List UInt8) :
    Codec.decode (α := UInt8) (b :: t) = some (b, t) := by
  rw [show b :: t = Codec.encode b ++ t by rw [encode_uint8]; rfl]
  exact LawfulCodec.decode_encode b t

/-- The codec of `UInt8` rejects the empty input. -/
theorem decode_uint8_nil : Codec.decode (α := UInt8) [] = none := rfl

/-- For every list of bytes `bs`, the byte elements of `bs` encode as `bs`. -/
theorem encodeElems_uint8 (bs : List UInt8) : encodeElems (α := UInt8) bs = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => rw [encodeElems, encode_uint8, ih, List.singleton_append]

/--
For every `n` and all bytes `bs`, `n` byte elements decode as the first `n` bytes of `bs`, with the rest as the remainder.
The result is `none` exactly when `bs` has fewer than `n` bytes.
-/
theorem decodeElems_uint8 (n : Nat) (bs : List UInt8) :
    decodeElems (α := UInt8) n bs
      = if n ≤ bs.length then some (bs.take n, bs.drop n) else none := by
  induction n generalizing bs with
  | zero => simp [decodeElems]
  | succ n ih =>
    cases bs with
    | nil => simp [decodeElems, decode_uint8_nil]
    | cons b t =>
      by_cases h : n ≤ t.length
      · simp [decodeElems, decode_uint8_cons, ih, h]
      · simp [decodeElems, decode_uint8_cons, ih, h]

/-- For every `n` and every slice `s`, `abstractParse (readByteList n s) = decodeElems n s.toList` for byte elements. -/
theorem abstractParse_readByteList (n : Nat) (s : ByteSlice) :
    abstractParse (readByteList n s) = decodeElems (α := UInt8) n s.toList := by
  rw [readByteList, decodeElems_uint8]
  by_cases h : n ≤ s.size
  · simp [h, abstractParse_some]
  · simp [h, abstractParse_none]

end DogeLib.Serialization.CountedList

namespace DogeLib.Serialization

open CountedList

/--
For every element codec with a lawful packed codec, the packed codec of counted lists `instPackedCodecCountedList` agrees with `instCodecCountedList`.
-/
instance instLawfulPackedCodecCountedList {α : Type} [Codec α] [PackedCodec α]
    [LawfulPackedCodec α] : LawfulPackedCodec (CountedList α) where
  toList_encodeInto cl acc := by
    change (CountedList.encodeInto cl acc).toList = acc.toList ++ CountedList.encode cl
    rw [CountedList.encodeInto, CountedList.encode, toList_pushElems,
      CompactSize.toList_encodeInto, List.append_assoc]
  abstractParse_decodeSlice s := by
    change abstractParse (CountedList.decodeSlice s) = CountedList.decode s.toList
    unfold CountedList.decodeSlice CountedList.decode
    rw [← CompactSize.abstractParse_decodeSlice s]
    refine abstractParse_bind _ fun count s1 => ?_
    dsimp only
    rw [← abstractParse_readElems (α := α) count.toNat s1]
    refine abstractParse_bind _ fun xs s2 => ?_
    dsimp only
    exact abstractParse_bindValue _ fun cl => rfl

/--
The packed codec of counted lists of bytes, `instPackedCodecCountedListBytes`, agrees with `instCodecCountedList`.
It writes the same bytes, and gives the same failures, values and remainder bytes, as the codec that reads one element at a time.
-/
instance (priority := high) instLawfulPackedCodecCountedListBytes :
    LawfulPackedCodec (CountedList UInt8) where
  toList_encodeInto cl acc := by
    change (CountedList.encodeIntoBytes cl acc).toList = acc.toList ++ CountedList.encode cl
    rw [CountedList.encodeIntoBytes, CountedList.encode, toList_pushBytes,
      CompactSize.toList_encodeInto, encodeElems_uint8, List.append_assoc]
  abstractParse_decodeSlice s := by
    change abstractParse (CountedList.decodeSliceBytes s) = CountedList.decode s.toList
    unfold CountedList.decodeSliceBytes CountedList.decode
    rw [← CompactSize.abstractParse_decodeSlice s]
    refine abstractParse_bind _ fun count s1 => ?_
    dsimp only
    rw [← abstractParse_readByteList count.toNat s1]
    refine abstractParse_bind _ fun bytes s2 => ?_
    dsimp only
    exact abstractParse_bindValue _ fun cl => rfl

end DogeLib.Serialization

namespace DogeLib.Serialization.CountedList

open CompactSize (ReadError)

/-! ## Core's bounded reader -/

/-- An `Except` result is `ok a` exactly when its `toOption` is `some a`. -/
private theorem except_eq_ok_iff {ε β : Type} (x : Except ε β) (a : β) :
    x = .ok a ↔ x.toOption = some a := by
  cases x <;> simp [Except.toOption]

/--
For every element codec and every element reader `elem` that accepts exactly what the codec accepts, `readElemsBounded elem n bs` accepts exactly what `decodeElems n bs` accepts.
-/
theorem readElemsBounded_toOption {α : Type} [Codec α]
    {elem : List UInt8 → Except ReadError (α × List UInt8)}
    (hElem : ∀ bs, (elem bs).toOption = Codec.decode bs) (n : Nat) (bs : List UInt8) :
    (readElemsBounded elem n bs).toOption = decodeElems n bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih =>
    have he := hElem bs
    simp only [readElemsBounded, decodeElems, Option.bind_eq_bind, Option.pure_def]
    cases h : elem bs with
    | error e =>
      rw [h] at he
      simp only [Except.toOption] at he
      rw [← he]
      rfl
    | ok p =>
      obtain ⟨x, r⟩ := p
      rw [h] at he
      simp only [Except.toOption] at he
      rw [← he, Option.bind_some]
      dsimp only
      rw [← ih r]
      cases readElemsBounded elem n r with
      | error e => rfl
      | ok q => rfl

/--
For every element reader, `decodeBounded elem bs = ok (cl, rest)` exactly when Core's count reader reads a count with a remainder `r`, and `readElemsBounded` reads the elements of `cl` from `r` with the remainder `rest`.
-/
theorem decodeBounded_eq_ok_iff_parts {α : Type}
    (elem : List UInt8 → Except ReadError (α × List UInt8)) (bs : List UInt8)
    (cl : CountedList α) (rest : List UInt8) :
    decodeBounded elem bs = .ok (cl, rest) ↔
      ∃ count r, CompactSize.decodeBounded bs = .ok (count, r) ∧
        readElemsBounded elem count.toNat r = .ok (cl.val, rest) := by
  unfold decodeBounded
  constructor
  · intro h
    split at h
    · cases h
    · next count r hc =>
      split at h
      · cases h
      · next xs r' he =>
        split at h
        · cases h
        · next cl' hof =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [val_of_ofList? hof]
          exact ⟨count, r, hc, he⟩
  · rintro ⟨count, r, hc, he⟩
    rw [hc]
    dsimp only
    rw [he]
    dsimp only
    rw [ofList?_eq_some cl.property]

/--
An error of the count is the error of the list.
For every element reader `elem` and all bytes `bs`, if `CompactSize.decodeBounded bs` reports the error `e`, then `decodeBounded elem bs` reports `e`.
So a count above `MAX_SIZE` is `tooLarge`, and the reader reads no element.
-/
theorem decodeBounded_of_count_error {α : Type}
    (elem : List UInt8 → Except ReadError (α × List UInt8)) {bs : List UInt8} {e : ReadError}
    (h : CompactSize.decodeBounded bs = .error e) :
    decodeBounded elem bs = .error e := by
  unfold decodeBounded
  rw [h]

/--
The contract of Core's vector reader.
For every element codec, every element reader `elem` that accepts exactly what the codec accepts, and all bytes `bs` and `rest`:
`decodeBounded elem bs = ok (cl, rest)` exactly when the generic `CountedList.decode bs = some (cl, rest)` and `cl` has at most `0x02000000` elements.
-/
theorem decodeBounded_eq_ok_iff {α : Type} [Codec α]
    {elem : List UInt8 → Except ReadError (α × List UInt8)}
    (hElem : ∀ bs, (elem bs).toOption = Codec.decode bs)
    (bs : List UInt8) (cl : CountedList α) (rest : List UInt8) :
    decodeBounded elem bs = .ok (cl, rest) ↔
      CountedList.decode bs = some (cl, rest) ∧ cl.val.length ≤ 0x02000000 := by
  rw [decodeBounded_eq_ok_iff_parts, decode_eq_some_iff]
  constructor
  · rintro ⟨count, r, hc, he⟩
    obtain ⟨hcd, hle⟩ := (CompactSize.decodeBounded_eq_ok_iff_decode bs count r).mp hc
    rw [except_eq_ok_iff, readElemsBounded_toOption hElem] at he
    have hlen := decodeElems_length count.toNat r cl.val rest he
    exact ⟨⟨count, r, hcd, he⟩, hlen ▸ hle⟩
  · rintro ⟨⟨count, r, hcd, he⟩, hle⟩
    have hlen := decodeElems_length count.toNat r cl.val rest he
    refine ⟨count, r, ?_, ?_⟩
    · exact (CompactSize.decodeBounded_eq_ok_iff_decode bs count r).mpr ⟨hcd, hlen ▸ hle⟩
    · rw [except_eq_ok_iff, readElemsBounded_toOption hElem]
      exact he

/--
The bounded round trip: for every lawful element codec, every element reader `elem` that accepts exactly what the codec accepts, every counted list `cl` with at most `0x02000000` elements and all bytes `rest`, `decodeBounded elem (CountedList.encode cl ++ rest) = ok (cl, rest)`.
-/
theorem decodeBounded_encode {α : Type} [Codec α] [LawfulCodec α]
    {elem : List UInt8 → Except ReadError (α × List UInt8)}
    (hElem : ∀ bs, (elem bs).toOption = Codec.decode bs)
    (cl : CountedList α) (hcl : cl.val.length ≤ 0x02000000) (rest : List UInt8) :
    decodeBounded elem (CountedList.encode cl ++ rest) = .ok (cl, rest) :=
  (decodeBounded_eq_ok_iff hElem _ cl rest).mpr ⟨decode_encode cl rest, hcl⟩

/-- `readByte` accepts exactly what the codec of `UInt8` accepts, on every input. -/
theorem readByte_toOption (bs : List UInt8) :
    (readByte bs).toOption = Codec.decode (α := UInt8) bs := by
  cases bs with
  | nil => rfl
  | cons b t => rw [decode_uint8_cons]; rfl

/-- For every `n` and all bytes `bs`, reading `n` bytes one at a time with `readByte` gives the same result as the block read `readBytes n bs`, including the error. -/
theorem readElemsBounded_readByte (n : Nat) (bs : List UInt8) :
    readElemsBounded readByte n bs = readBytes n bs := by
  induction n generalizing bs with
  | zero => simp [readElemsBounded, readBytes]
  | succ n ih =>
    cases bs with
    | nil => simp [readElemsBounded, readByte, readBytes]
    | cons b t =>
      simp only [readElemsBounded, readByte, ih, readBytes, List.length_cons]
      by_cases h : n ≤ t.length
      · simp [h]
      · simp [h]

/-- Core's block read of a vector of bytes, `decodeBoundedBytes`, is `decodeBounded readByte` on every input. -/
theorem decodeBoundedBytes_eq (bs : List UInt8) :
    decodeBoundedBytes bs = decodeBounded readByte bs := by
  unfold decodeBoundedBytes decodeBounded
  cases CompactSize.decodeBounded bs with
  | error e => rfl
  | ok p =>
    obtain ⟨count, r⟩ := p
    dsimp only
    rw [readElemsBounded_readByte]
    cases readBytes count.toNat r with
    | error e => rfl
    | ok q =>
      obtain ⟨xs, r'⟩ := q
      dsimp only
      cases ofList? xs <;> rfl

/-! ## The distinguishing input -/

/--
The count `fe 01 00 00 02`, which is `0x02000001`, with no elements after it: Core's reader of byte vectors reports `tooLarge`.
-/
theorem decodeBoundedBytes_maxSize_succ :
    decodeBoundedBytes [0xfe, 0x01, 0x00, 0x00, 0x02] = .error .tooLarge := rfl

/--
The generic decoder reads the same count, and then fails because the elements are missing.
It does not distinguish this input from any other truncated list.
-/
theorem decode_maxSize_succ :
    CountedList.decode (α := UInt8) [0xfe, 0x01, 0x00, 0x00, 0x02] = none := by
  rw [CountedList.decode, CompactSize.decode_maxSize_succ]
  simp [decodeElems_uint8]

end DogeLib.Serialization.CountedList
