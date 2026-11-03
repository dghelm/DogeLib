module

public import DogeLib.Serialization.CompactSize
public import DogeLib.Serialization.Proofs.Codec
public import DogeLib.Serialization.Proofs.PackedCodec
public import DogeLib.Serialization.Proofs.WidthCast

/-!
# Proofs: `Serialization.CompactSize`

The laws of the generic CompactSize codec, the agreement of its packed form, and the contract of Core's bounded reader.

## The generic codec

- `decode_encode` and `decode_canonical`: the round trip and canonicality of `decode`, on every `UInt64`, packaged as `lawfulCodec`.
- `encode_length_le`: an encoding has at most 9 bytes.
- `encode_head`: an encoding starts with a byte, and that byte is `0x00` only for the value 0.
- `toList_encodeInto` and `abstractParse_decodeSlice`: the packed codec agrees with the codec, packaged as `lawfulPackedCodec`.

## The accepted bytes, stated separately

`CanonicalCompactSizePrefix bytes value rest` says that `bytes` starts with the canonical encoding of `value`, followed by `rest`.
It lists the four forms with their markers, payload widths and minimum values, and reads the payload with `leValue`, a little-endian sum.
`ValidCompactSizePrefix` adds the bound of Core, `value ≤ 0x02000000`.
Neither relation refers to a decoder or to the codec primitives.

- `decode_eq_some_iff`: `decode` accepts exactly the canonical prefixes.
- `decodeBounded_eq_ok_iff_valid`: `decodeBounded` accepts exactly the valid prefixes.
- `decodeBounded_eq_ok_iff_decode`: `decodeBounded` accepts exactly what `decode` accepts with a value up to `0x02000000`.
- `decodeBounded_eq_error_tooLarge_iff`: `decodeBounded` reports `tooLarge` exactly when `decode` accepts a value above `0x02000000`.
- `decodeBounded_encode`: the round trip of `decodeBounded`, for values up to `0x02000000`.

## Source

The sections *The generic codec* and *The packed codec* of this file are adapted from btc-verified.
The source is [`BtcVerified/Serialize/CompactSize.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/CompactSize.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream `decode_encode` proves `n.toUInt8 < 0xFD` from `n < 253` with `bv_decide`.
  Here `toUInt8_lt_fd` proves it from the values as natural numbers, with `omega`.
- Upstream `encode_head` proves `n.toUInt8 ≠ 0` from `n < 253` and `n ≠ 0` with `bv_decide`.
  Here `toUInt8_ne_zero` proves it the same way as `toUInt8_lt_fd`.
- Upstream uses Mathlib's `split_ifs`. Here the proofs use `split` and `by_cases` of Lean core.
- Lean `v4.35.0` deprecates `if_pos` and `if_neg`, so the proofs use `simp` with the condition.
- `lawfulCodec` and `lawfulPackedCodec` give the laws as explicit terms, because `codec` and `packedCodec` are not instances.
- The namespace, the module header and the doc comments are DogeLib's.

The sections *The accepted bytes* and *Core's bounded reader* are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Serialization.CompactSize

/-! ## Small facts about the one-byte form

These replace the two `bv_decide` steps of the upstream proofs.
Each one reduces the claim to natural numbers, where `omega` decides it.
-/

/-- For every `n : UInt64` with `n < 253`, the byte `n.toUInt8` is below `0xFD`. -/
theorem toUInt8_lt_fd {n : UInt64} (h : n < 253) : n.toUInt8 < 0xFD := by
  rw [UInt8.lt_iff_toNat_lt, UInt64.toNat_toUInt8]
  have := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.reduceToNat, UInt8.reduceToNat] at this ⊢
  omega

/-- For every `n : UInt64` with `n < 253` and `n ≠ 0`, the byte `n.toUInt8` is not `0`. -/
theorem toUInt8_ne_zero {n : UInt64} (h : n < 253) (hn : n ≠ 0) : n.toUInt8 ≠ 0 := by
  intro h0
  have h1 := congrArg UInt8.toNat h0
  rw [UInt64.toNat_toUInt8] at h1
  have h2 := UInt64.lt_iff_toNat_lt.mp h
  have h3 : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by simpa using e))
  simp only [UInt64.reduceToNat, UInt8.reduceToNat] at h1 h2
  omega

/-! ## The generic codec -/

/-- For `n m : UInt64` with `n < m`, and `m.toNat = k`, `n.toNat < k`. -/
private theorem toNat_lt_of_lt {n m : UInt64} {k : Nat} (h : n < m) (hm : m.toNat = k) :
    n.toNat < k :=
  hm ▸ UInt64.lt_iff_toNat_lt.mp h

/-- For `n m : UInt64` with `¬ n < m`, and `m.toNat = k`, `k ≤ n.toNat`. -/
private theorem le_toNat_of_not_lt {n m : UInt64} {k : Nat} (h : ¬ n < m) (hm : m.toNat = k) :
    k ≤ n.toNat :=
  hm ▸ UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)

/-- For `n m : UInt64` with `n.toNat < k` and `m.toNat = k`, `n < m`. -/
private theorem lt_of_toNat_lt {n m : UInt64} {k : Nat} (h : n.toNat < k) (hm : m.toNat = k) :
    n < m :=
  UInt64.lt_iff_toNat_lt.mpr (hm ▸ h)

/-- For `n m : UInt64` with `k ≤ n.toNat` and `m.toNat = k`, `¬ n < m`. -/
private theorem not_lt_of_le_toNat {n m : UInt64} {k : Nat} (h : k ≤ n.toNat) (hm : m.toNat = k) :
    ¬ n < m :=
  UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (hm ▸ h))

/-- For every `byteWidth` and `n`, the payload `encodeFixedWidth byteWidth n` has exactly `byteWidth` bytes. -/
theorem encodeFixedWidth_length (byteWidth : Nat) (n : UInt64) :
    (encodeFixedWidth byteWidth n).length = byteWidth :=
  encodeBitVecLE_length byteWidth (n.toBitVec.setWidth (8 * byteWidth))

/--
For every `n` with `minValue ≤ n < 2 ^ (8 * byteWidth)`, and all bytes `xs`, `decodeFixedWidth byteWidth minValue` reads the payload `encodeFixedWidth byteWidth n ++ xs` as `n` with the remainder `xs`.
-/
theorem decodeFixedWidth_encodeFixedWidth (byteWidth minValue : Nat) (n : UInt64)
    (hlo : minValue ≤ n.toNat) (hhi : n.toNat < 2 ^ (8 * byteWidth)) (xs : List UInt8) :
    decodeFixedWidth byteWidth minValue (encodeFixedWidth byteWidth n ++ xs) = some (n, xs) := by
  have hw : (n.toBitVec.setWidth (8 * byteWidth)).toNat = n.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hhi
  simp only [encodeFixedWidth, decodeFixedWidth, decodeBitVecLE_encodeBitVecLE,
    Option.bind_eq_bind, Option.bind_some, hw]
  simp [guard, hlo, setWidth_setWidth_eq_self hhi]

/--
For `8 * byteWidth ≤ 64`: if `decodeFixedWidth byteWidth minValue bs` returns `n` with the remainder `rest`, then `minValue ≤ n < 2 ^ (8 * byteWidth)` and `bs = encodeFixedWidth byteWidth n ++ rest`.
-/
theorem decodeFixedWidth_canonical (byteWidth minValue : Nat) (hbw : 8 * byteWidth ≤ 64)
    (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decodeFixedWidth byteWidth minValue bs = some (n, rest) →
      minValue ≤ n.toNat ∧ n.toNat < 2 ^ (8 * byteWidth) ∧
        bs = encodeFixedWidth byteWidth n ++ rest := by
  intro parses
  unfold decodeFixedWidth at parses
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at parses
  obtain ⟨⟨w, rest'⟩, hd, _, hg, parses⟩ := parses
  dsimp only at hg parses
  by_cases hw : minValue ≤ w.toNat
  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at parses
    obtain ⟨rfl, rfl⟩ := parses
    have hwlt : w.toNat < 2 ^ (8 * byteWidth) := w.isLt
    have hw64 : w.toNat < 2 ^ 64 :=
      Nat.lt_of_lt_of_le hwlt (Nat.pow_le_pow_right (by omega) hbw)
    have hval : (⟨w.setWidth 64⟩ : UInt64).toNat = w.toNat := by
      rw [UInt64.toNat_ofBitVec, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hw64
    refine ⟨?_, ?_, ?_⟩
    · rw [hval]; exact hw
    · rw [hval]; exact hwlt
    · have hbs := decodeBitVecLE_canonical byteWidth bs w rest' hd
      have hb : encodeFixedWidth byteWidth (⟨w.setWidth 64⟩ : UInt64)
          = encodeBitVecLE byteWidth w := by
        unfold encodeFixedWidth
        rw [UInt64.toBitVec_ofBitVec, setWidth_setWidth_eq_self hw64]
      rw [hbs, hb]
  · simp [guard, hw] at hg

private theorem decode_FD (t : List UInt8) :
    decode (0xFD :: t) = decodeFixedWidth 2 253 t := rfl

private theorem decode_FE (t : List UInt8) :
    decode (0xFE :: t) = decodeFixedWidth 4 (2 ^ 16) t := rfl

private theorem decode_FF (t : List UInt8) :
    decode (0xFF :: t) = decodeFixedWidth 8 (2 ^ 32) t := rfl

/--
The round trip of the generic decoder: for every `n : UInt64` and all bytes `xs`, `decode (encode n ++ xs) = some (n, xs)`.
-/
theorem decode_encode (n : UInt64) (xs : List UInt8) : decode (encode n ++ xs) = some (n, xs) := by
  unfold encode
  by_cases h1 : n < 253
  · have hb := toUInt8_lt_fd h1
    have hv : n.toUInt8.toUInt64 = n := by
      narrow_widen (show n < 2 ^ 8 from UInt64.lt_trans h1 (by decide))
    simp [h1, decode, hb, hv]
  · by_cases h2 : n < 2 ^ 16
    · simp only [h1, h2, ite_false, ite_true, List.cons_append, decode_FD]
      exact decodeFixedWidth_encodeFixedWidth 2 253 n
        (le_toNat_of_not_lt h1 rfl) (toNat_lt_of_lt h2 rfl) xs
    · by_cases h3 : n < 2 ^ 32
      · simp only [h1, h2, h3, ite_false, ite_true, List.cons_append, decode_FE]
        exact decodeFixedWidth_encodeFixedWidth 4 (2 ^ 16) n
          (le_toNat_of_not_lt h2 rfl) (toNat_lt_of_lt h3 rfl) xs
      · simp only [h1, h2, h3, ite_false, List.cons_append, decode_FF]
        exact decodeFixedWidth_encodeFixedWidth 8 (2 ^ 32) n
          (le_toNat_of_not_lt h3 rfl) n.toBitVec.isLt xs

/-- For every `n : UInt64`, `encode n` has at most 9 bytes: one marker and at most 8 payload bytes. -/
theorem encode_length_le (n : UInt64) : (encode n).length ≤ 9 := by
  unfold encode
  split
  · simp
  · split
    · simp [encodeFixedWidth_length]
    · split <;> simp [encodeFixedWidth_length]

/--
For every `n : UInt64`, `encode n` is a byte `b` followed by more bytes, and `b ≠ 0` when `n ≠ 0`.
So only the value 0 has an encoding that starts with `0x00`.
-/
theorem encode_head (n : UInt64) :
    ∃ b t, encode n = b :: t ∧ (n ≠ 0 → b ≠ 0) := by
  unfold encode
  split
  · next h1 => exact ⟨n.toUInt8, [], rfl, toUInt8_ne_zero h1⟩
  · split
    · exact ⟨0xFD, encodeFixedWidth 2 n, rfl, fun _ => by decide⟩
    · split
      · exact ⟨0xFE, encodeFixedWidth 4 n, rfl, fun _ => by decide⟩
      · exact ⟨0xFF, encodeFixedWidth 8 n, rfl, fun _ => by decide⟩

/--
Canonicality of the generic decoder: for all bytes `bs`, if `decode bs = some (n, rest)`, then `bs = encode n ++ rest`.
So `decode` accepts only the shortest encoding of each value.
-/
theorem decode_canonical (bs : List UInt8) (n : UInt64) (rest : List UInt8) :
    decode bs = some (n, rest) → bs = encode n ++ rest := by
  intro parses
  match bs with
  | [] => simp [decode] at parses
  | h :: t =>
    simp only [decode] at parses
    by_cases c1 : h < 0xFD
    · simp only [c1, ite_true, Option.some.injEq, Prod.mk.injEq] at parses
      obtain ⟨rfl, rfl⟩ := parses
      have h253 : h.toUInt64 < 253 :=
        lt_of_toNat_lt (by rw [UInt8.toNat_toUInt64]; exact UInt8.lt_iff_toNat_lt.mp c1) rfl
      simp [encode, h253]
    · simp only [c1, ite_false] at parses
      by_cases c2 : h = 0xFD
      · simp only [c2, ite_true] at parses
        subst c2
        obtain ⟨hlo, hhi, rfl⟩ := decodeFixedWidth_canonical 2 253 (by decide) t n rest parses
        have hn1 : ¬ n < 253 := not_lt_of_le_toNat hlo rfl
        have hn2 : n < 2 ^ 16 := lt_of_toNat_lt hhi rfl
        simp [encode, hn1, hn2]
      · simp only [c2, ite_false] at parses
        by_cases c3 : h = 0xFE
        · simp only [c3, ite_true] at parses
          subst c3
          obtain ⟨hlo, hhi, rfl⟩ :=
            decodeFixedWidth_canonical 4 (2 ^ 16) (by decide) t n rest parses
          have hn1 : ¬ n < 2 ^ 16 := not_lt_of_le_toNat hlo rfl
          have hn2 : n < 2 ^ 32 := lt_of_toNat_lt hhi rfl
          have hn0 : ¬ n < 253 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
          simp [encode, hn0, hn1, hn2]
        · simp only [c3, ite_false] at parses
          by_cases c4 : h = 0xFF
          · simp only [c4, ite_true] at parses
            subst c4
            obtain ⟨hlo, hhi, rfl⟩ :=
              decodeFixedWidth_canonical 8 (2 ^ 32) (by decide) t n rest parses
            have hn1 : ¬ n < 2 ^ 32 := not_lt_of_le_toNat hlo rfl
            have hn2 : ¬ n < 2 ^ 16 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
            have hn0 : ¬ n < 253 := fun hc => hn1 (UInt64.lt_trans hc (by decide))
            simp [encode, hn0, hn2, hn1]
          · simp [c4] at parses

/-- The generic CompactSize codec `codec` is lawful: round trip and canonicality on every `UInt64`. -/
theorem lawfulCodec : @LawfulCodec UInt64 codec :=
  @LawfulCodec.mk UInt64 codec decode_encode decode_canonical

/-! ## The packed codec -/

/-- For every `byteWidth`, `n` and buffer `acc`, the bytes of `pushFixedWidth byteWidth n acc` are the bytes of `acc` followed by `encodeFixedWidth byteWidth n`. -/
theorem toList_pushFixedWidth (byteWidth : Nat) (n : UInt64) (acc : ByteArray) :
    (pushFixedWidth byteWidth n acc).toList = acc.toList ++ encodeFixedWidth byteWidth n :=
  toList_pushBitVecLE byteWidth _ acc

/-- For every `byteWidth`, `minValue` and slice `s`, `abstractParse (readFixedWidth byteWidth minValue s) = decodeFixedWidth byteWidth minValue s.toList`. -/
theorem abstractParse_readFixedWidth (byteWidth minValue : Nat) (s : ByteSlice) :
    abstractParse (readFixedWidth byteWidth minValue s)
      = decodeFixedWidth byteWidth minValue s.toList := by
  unfold readFixedWidth decodeFixedWidth
  rw [← abstractParse_readBitVecLE byteWidth s]
  refine abstractParse_bind _ fun w rest => ?_
  dsimp only
  exact abstractParse_bindValue _ fun _ => rfl

/-- For every `n` and buffer `acc`, the bytes of `encodeInto n acc` are the bytes of `acc` followed by `encode n`. -/
theorem toList_encodeInto (n : UInt64) (acc : ByteArray) :
    (encodeInto n acc).toList = acc.toList ++ encode n := by
  unfold encodeInto encode
  split
  · simp
  · split
    · simp [toList_pushFixedWidth]
    · split <;> simp [toList_pushFixedWidth]

/-- `decode` as a read of one byte, followed by the dispatch on the marker. -/
private theorem decode_eq_decodeByte_bind (bs : List UInt8) :
    decode bs = (decodeByte bs).bind fun p =>
      if p.1 < 0xFD then some (p.1.toUInt64, p.2)
      else if p.1 = 0xFD then decodeFixedWidth 2 253 p.2
      else if p.1 = 0xFE then decodeFixedWidth 4 (2 ^ 16) p.2
      else if p.1 = 0xFF then decodeFixedWidth 8 (2 ^ 32) p.2
      else none := by
  cases bs <;> rfl

/-- For every slice `s`, `abstractParse (decodeSlice s) = decode s.toList`. -/
theorem abstractParse_decodeSlice (s : ByteSlice) :
    abstractParse (decodeSlice s) = decode s.toList := by
  unfold decodeSlice
  rw [decode_eq_decodeByte_bind, ← abstractParse_uncons s]
  refine abstractParse_bind _ fun b t => ?_
  dsimp only
  split
  · rfl
  · split
    · apply abstractParse_readFixedWidth
    · split
      · apply abstractParse_readFixedWidth
      · split
        · apply abstractParse_readFixedWidth
        · rfl

/--
The packed generic CompactSize codec `packedCodec` agrees with `codec`.
It writes the same bytes for every value, and gives the same failures, values and remainder bytes on every slice.
-/
theorem lawfulPackedCodec : @LawfulPackedCodec UInt64 codec packedCodec :=
  @LawfulPackedCodec.mk UInt64 codec packedCodec toList_encodeInto abstractParse_decodeSlice

/-! ## The accepted bytes, stated separately -/

/--
The little-endian value of a byte list: the first byte is the least significant.
`leValue [b₀, b₁, …, bₖ] = b₀ + 256 * b₁ + … + 256 ^ k * bₖ`.
-/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/--
`CanonicalCompactSizePrefix bytes value rest`: `bytes` starts with the canonical CompactSize encoding of `value`, and `rest` is the bytes after it.

There is one constructor per form.
Each marked form gives the marker, the number of payload bytes, the little-endian value of the payload, and the smallest value that needs the form:

```text
form      bytes                       payload   value
oneByte   b :: rest                   none      b, where b < 253
fd        0xfd :: payload ++ rest     2 bytes   leValue payload >= 253
fe        0xfe :: payload ++ rest     4 bytes   leValue payload >= 0x10000
ff        0xff :: payload ++ rest     8 bytes   leValue payload >= 0x100000000
```

The relation has no upper bound on `value`, other than the type `UInt64`.
-/
inductive CanonicalCompactSizePrefix : List UInt8 → UInt64 → List UInt8 → Prop where
  /-- A first byte below 253 is the value itself. -/
  | oneByte (b : UInt8) (rest : List UInt8) (value : UInt64)
      (hb : b.toNat < 253) (hval : value.toNat = b.toNat) :
      CanonicalCompactSizePrefix (b :: rest) value rest
  /-- Marker `0xfd`, then 2 little-endian bytes with a value of at least 253. -/
  | fd (payload rest : List UInt8) (value : UInt64)
      (hlen : payload.length = 2) (hval : value.toNat = leValue payload)
      (hmin : 253 ≤ value.toNat) :
      CanonicalCompactSizePrefix (0xfd :: payload ++ rest) value rest
  /-- Marker `0xfe`, then 4 little-endian bytes with a value of at least `0x10000`. -/
  | fe (payload rest : List UInt8) (value : UInt64)
      (hlen : payload.length = 4) (hval : value.toNat = leValue payload)
      (hmin : 0x10000 ≤ value.toNat) :
      CanonicalCompactSizePrefix (0xfe :: payload ++ rest) value rest
  /-- Marker `0xff`, then 8 little-endian bytes with a value of at least `0x100000000`. -/
  | ff (payload rest : List UInt8) (value : UInt64)
      (hlen : payload.length = 8) (hval : value.toNat = leValue payload)
      (hmin : 0x100000000 ≤ value.toNat) :
      CanonicalCompactSizePrefix (0xff :: payload ++ rest) value rest

/--
`ValidCompactSizePrefix bytes value rest`: `bytes` starts with the canonical encoding of `value` (`CanonicalCompactSizePrefix`), `rest` is the bytes after it, and `value ≤ 0x02000000`, the `MAX_SIZE` of Core (D1).

`decodeBounded`, the model of Core's `ReadCompactSize`, accepts exactly these inputs (`decodeBounded_eq_ok_iff_valid`).
No input with the marker `0xff` satisfies the relation, because that form needs a value of at least `0x100000000`.
-/
def ValidCompactSizePrefix (bytes : List UInt8) (value : UInt64) (rest : List UInt8) : Prop :=
  CanonicalCompactSizePrefix bytes value rest ∧ value.toNat ≤ 0x02000000

/-- For every `n` and `hi : BitVec (8 * n)`, and every byte `b`, the value of `hi ++ b.toBitVec` is `hi * 256 + b`. -/
private theorem toNat_append_byte {n : Nat} (hi : BitVec (8 * n)) (b : UInt8) :
    (hi ++ b.toBitVec).toNat = hi.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.toBitVec.isLt, Nat.shiftLeft_eq]
  rfl

/--
Let `decodeBitVecLE n bs = some (w, rest)`.
Then `bs` is a payload of `n` bytes followed by `rest`, and `w` is the little-endian value of the payload.
-/
private theorem decodeBitVecLE_some :
    ∀ (n : Nat) (bs : List UInt8) (w : BitVec (8 * n)) (rest : List UInt8),
      decodeBitVecLE n bs = some (w, rest) →
        ∃ payload, bs = payload ++ rest ∧ payload.length = n ∧ w.toNat = leValue payload := by
  intro n
  induction n with
  | zero =>
    intro bs w rest h
    simp only [decodeBitVecLE, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, rfl⟩
  | succ n ih =>
    intro bs w rest h
    cases bs with
    | nil => simp [decodeBitVecLE, decodeByte] at h
    | cons b bs' =>
      simp only [decodeBitVecLE, decodeByte, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨hi, r⟩, hd, hv, hr⟩ := h
      subst hv; subst hr
      obtain ⟨p, hp, hlen, hval⟩ := ih bs' hi r hd
      refine ⟨b :: p, by simp [hp], by simp [hlen], ?_⟩
      rw [toNat_append_byte, hval, leValue]
      omega

/--
Let `payload` have `n` bytes.
Then `decodeBitVecLE n (payload ++ rest)` succeeds with the remainder `rest`.
Its value is the little-endian value of the payload.
-/
private theorem decodeBitVecLE_payload :
    ∀ (n : Nat) (payload rest : List UInt8), payload.length = n →
      ∃ w : BitVec (8 * n), decodeBitVecLE n (payload ++ rest) = some (w, rest) ∧
        w.toNat = leValue payload := by
  intro n
  induction n with
  | zero =>
    intro payload rest h
    rw [List.length_eq_zero_iff] at h
    subst h
    exact ⟨0#0, rfl, rfl⟩
  | succ n ih =>
    intro payload rest h
    cases payload with
    | nil => simp at h
    | cons b p =>
      obtain ⟨w, hw, hval⟩ := ih p rest (by simpa using h)
      refine ⟨w ++ b.toBitVec, ?_, ?_⟩
      · simp [decodeBitVecLE, decodeByte, hw]
      · rw [toNat_append_byte, hval, leValue]
        omega

/--
Let `8 * byteWidth ≤ 64`.
Then `decodeFixedWidth byteWidth minValue bs = some (v, rest)` exactly when three conditions hold.
`bs` is a payload of `byteWidth` bytes followed by `rest`.
The little-endian value of the payload is `v`.
`minValue ≤ v`.
-/
private theorem decodeFixedWidth_eq_some_iff (byteWidth minValue : Nat) (hbw : 8 * byteWidth ≤ 64)
    (bs : List UInt8) (v : UInt64) (rest : List UInt8) :
    decodeFixedWidth byteWidth minValue bs = some (v, rest) ↔
      ∃ payload, bs = payload ++ rest ∧ payload.length = byteWidth ∧
        v.toNat = leValue payload ∧ minValue ≤ v.toNat := by
  constructor
  · intro h
    obtain ⟨hlo, -, -⟩ := decodeFixedWidth_canonical byteWidth minValue hbw bs v rest h
    unfold decodeFixedWidth at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨w, rest'⟩, hd, _, hg, h⟩ := h
    dsimp only at hg h
    by_cases hw : minValue ≤ w.toNat
    · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨p, hp, hlen, hval⟩ := decodeBitVecLE_some byteWidth bs w rest' hd
      have hw64 : w.toNat < 2 ^ 64 :=
        Nat.lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) hbw)
      have hv : (⟨w.setWidth 64⟩ : UInt64).toNat = w.toNat := by
        rw [UInt64.toNat_ofBitVec, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt hw64
      exact ⟨p, hp, hlen, by rw [hv, hval], hlo⟩
    · simp [guard, hw] at hg
  · rintro ⟨p, rfl, hlen, hval, hmin⟩
    obtain ⟨w, hw, hwval⟩ := decodeBitVecLE_payload byteWidth p rest hlen
    have hw64 : w.toNat < 2 ^ 64 :=
      Nat.lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) hbw)
    have hv : (⟨w.setWidth 64⟩ : UInt64) = v := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofBitVec, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hw64, hwval, hval]
    have hmin' : minValue ≤ w.toNat := by rw [hwval, ← hval]; exact hmin
    simp [decodeFixedWidth, hw, guard, hmin', hv]

/--
Soundness and completeness of the generic decoder: for all bytes `bytes`, values `value` and bytes `rest`, `decode bytes = some (value, rest)` exactly when `CanonicalCompactSizePrefix bytes value rest`.
-/
theorem decode_eq_some_iff (bytes : List UInt8) (value : UInt64) (rest : List UInt8) :
    decode bytes = some (value, rest) ↔ CanonicalCompactSizePrefix bytes value rest := by
  constructor
  · intro h
    match bytes with
    | [] => simp [decode] at h
    | b :: t =>
      simp only [decode] at h
      by_cases c1 : b < 0xFD
      · simp only [c1, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb : b.toNat < 253 := by simpa [UInt8.lt_iff_toNat_lt] using c1
        exact .oneByte b t b.toUInt64 hb (UInt8.toNat_toUInt64 b)
      · simp only [c1, ite_false] at h
        by_cases c2 : b = 0xFD
        · simp only [c2, ite_true] at h
          subst c2
          obtain ⟨p, rfl, hlen, hval, hmin⟩ :=
            (decodeFixedWidth_eq_some_iff 2 253 (by decide) t value rest).mp h
          exact .fd p rest value hlen hval hmin
        · simp only [c2, ite_false] at h
          by_cases c3 : b = 0xFE
          · simp only [c3, ite_true] at h
            subst c3
            obtain ⟨p, rfl, hlen, hval, hmin⟩ :=
              (decodeFixedWidth_eq_some_iff 4 (2 ^ 16) (by decide) t value rest).mp h
            exact .fe p rest value hlen hval hmin
          · simp only [c3, ite_false] at h
            by_cases c4 : b = 0xFF
            · simp only [c4, ite_true] at h
              subst c4
              obtain ⟨p, rfl, hlen, hval, hmin⟩ :=
                (decodeFixedWidth_eq_some_iff 8 (2 ^ 32) (by decide) t value rest).mp h
              exact .ff p rest value hlen hval hmin
            · simp [c4] at h
  · intro h
    cases h with
    | oneByte b rest value hb hval =>
      have c1 : b < 0xFD := by rw [UInt8.lt_iff_toNat_lt]; simpa using hb
      have hv : b.toUInt64 = value := by
        apply UInt64.toNat_inj.mp; rw [UInt8.toNat_toUInt64, hval]
      simp [decode, c1, hv]
    | fd payload rest value hlen hval hmin =>
      exact (decodeFixedWidth_eq_some_iff 2 253 (by decide) _ value rest).mpr
        ⟨payload, rfl, hlen, hval, hmin⟩
    | fe payload rest value hlen hval hmin =>
      exact (decodeFixedWidth_eq_some_iff 4 (2 ^ 16) (by decide) _ value rest).mpr
        ⟨payload, rfl, hlen, hval, hmin⟩
    | ff payload rest value hlen hval hmin =>
      exact (decodeFixedWidth_eq_some_iff 8 (2 ^ 32) (by decide) _ value rest).mpr
        ⟨payload, rfl, hlen, hval, hmin⟩

/-! ## Core's bounded reader -/

/-- The value of `maxSize` is `0x02000000`. -/
theorem maxSize_toNat : maxSize.toNat = 0x02000000 := rfl

/--
For every `byteWidth`, `minValue` and bytes `bs`, `readPayload` succeeds exactly when `decodeFixedWidth` succeeds, with the same value and remainder.
-/
private theorem readPayload_toOption (byteWidth minValue : Nat) (bs : List UInt8) :
    (readPayload byteWidth minValue bs).toOption = decodeFixedWidth byteWidth minValue bs := by
  unfold readPayload decodeFixedWidth
  cases decodeBitVecLE byteWidth bs with
  | none => rfl
  | some p =>
    obtain ⟨w, rest⟩ := p
    by_cases h : w.toNat < minValue
    · have h' : ¬ minValue ≤ w.toNat := by omega
      simp [h, h', guard, Except.toOption]
      rfl
    · have h' : minValue ≤ w.toNat := by omega
      simp [h, h', guard, Except.toOption]

/-- For every `byteWidth`, `minValue` and bytes `bs`, `readPayload` never reports `tooLarge`. -/
private theorem readPayload_ne_tooLarge (byteWidth minValue : Nat) (bs : List UInt8) :
    readPayload byteWidth minValue bs ≠ .error .tooLarge := by
  unfold readPayload
  cases decodeBitVecLE byteWidth bs with
  | none => simp
  | some p =>
    obtain ⟨w, rest⟩ := p
    dsimp only
    split <;> simp

/--
For every byte `b` that is not below 253, not 253 and not 254, `b = 0xFF`.
So the last branch of `ReadCompactSize` reads only the marker 255.
-/
private theorem eq_ff_of_ge {b : UInt8} (h1 : ¬ b < 253) (h2 : b ≠ 253) (h3 : b ≠ 254) :
    b = 0xFF := by
  have n1 : ¬ b.toNat < 253 := fun h => h1 (UInt8.lt_iff_toNat_lt.mpr h)
  have n2 : b.toNat ≠ 253 := fun h => h2 (UInt8.toNat_inj.mp h)
  have n3 : b.toNat ≠ 254 := fun h => h3 (UInt8.toNat_inj.mp h)
  apply UInt8.toNat_inj.mp
  have := b.toNat_lt
  simp only [UInt8.reduceToNat] at *
  omega

/--
For all bytes `bs`, `readCanonical bs` succeeds exactly when the generic `decode bs` succeeds, with the same value and remainder.
-/
theorem readCanonical_toOption (bs : List UInt8) :
    (readCanonical bs).toOption = decode bs := by
  match bs with
  | [] => rfl
  | b :: t =>
    simp only [readCanonical, decode]
    by_cases c1 : b < 253
    · simp [c1, Except.toOption]
    · simp only [c1, ite_false]
      by_cases c2 : b = 253
      · simp only [c2, ite_true]
        exact readPayload_toOption 2 253 t
      · simp only [c2, ite_false]
        by_cases c3 : b = 254
        · simp only [c3, ite_true]
          exact readPayload_toOption 4 0x10000 t
        · have c4 : b = 0xFF := eq_ff_of_ge c1 c2 c3
          subst c4
          simp only [c3, ↓reduceIte]
          exact readPayload_toOption 8 0x100000000 t

/-- For all bytes `bs`, `readCanonical bs` never reports `tooLarge`. -/
private theorem readCanonical_ne_tooLarge (bs : List UInt8) :
    readCanonical bs ≠ .error .tooLarge := by
  match bs with
  | [] => simp [readCanonical]
  | b :: t =>
    simp only [readCanonical]
    split
    · simp
    · split
      · exact readPayload_ne_tooLarge _ _ _
      · split
        · exact readPayload_ne_tooLarge _ _ _
        · exact readPayload_ne_tooLarge _ _ _

/-- An `Except` result is `ok a` exactly when its `toOption` is `some a`. -/
private theorem except_eq_ok_iff {ε α : Type} (x : Except ε α) (a : α) :
    x = .ok a ↔ x.toOption = some a := by
  cases x <;> simp [Except.toOption]

/--
The relation of design record 0002, section 3: for all bytes `bytes`, values `value` and bytes `rest`, `decodeBounded bytes = ok (value, rest)` exactly when the generic `decode bytes = some (value, rest)` and `value ≤ 0x02000000`.
-/
theorem decodeBounded_eq_ok_iff_decode (bytes : List UInt8) (value : UInt64) (rest : List UInt8) :
    decodeBounded bytes = .ok (value, rest) ↔
      decode bytes = some (value, rest) ∧ value.toNat ≤ 0x02000000 := by
  rw [← readCanonical_toOption, ← except_eq_ok_iff]
  unfold decodeBounded
  cases readCanonical bytes with
  | error e => simp
  | ok p =>
    obtain ⟨n, r⟩ := p
    have hle : (n > maxSize) ↔ ¬ n.toNat ≤ 0x02000000 := by
      rw [GT.gt, UInt64.lt_iff_toNat_lt, maxSize_toNat]; omega
    by_cases h : n > maxSize
    · have h' := hle.mp h
      simp only [h, ite_true]
      constructor
      · intro hc; cases hc
      · rintro ⟨hc, hb⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact absurd hb h'
    · have h' : n.toNat ≤ 0x02000000 := Classical.not_not.mp (mt hle.mpr h)
      simp only [h, ite_false, Except.ok.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, h'⟩
      · rintro ⟨⟨rfl, rfl⟩, -⟩; exact ⟨rfl, rfl⟩

/--
Soundness and completeness of Core's reader: for all bytes `bytes`, values `value` and bytes `rest`, `decodeBounded bytes = ok (value, rest)` exactly when `ValidCompactSizePrefix bytes value rest`.

So the reader accepts an input exactly when the input starts with the canonical encoding of a value up to `0x02000000`.
It then returns that value, and exactly the bytes after the encoding.
-/
theorem decodeBounded_eq_ok_iff_valid (bytes : List UInt8) (value : UInt64) (rest : List UInt8) :
    decodeBounded bytes = .ok (value, rest) ↔ ValidCompactSizePrefix bytes value rest := by
  rw [decodeBounded_eq_ok_iff_decode, decode_eq_some_iff]
  rfl

/--
The bounded round trip: for every `n : UInt64` with `n ≤ 0x02000000`, and all bytes `rest`, `decodeBounded (encode n ++ rest) = ok (n, rest)`.

The bound is necessary: `decodeBounded_encode_maxSize_succ` shows that the round trip fails for `0x02000001`.
-/
theorem decodeBounded_encode (n : UInt64) (hn : n.toNat ≤ 0x02000000) (rest : List UInt8) :
    decodeBounded (encode n ++ rest) = .ok (n, rest) :=
  (decodeBounded_eq_ok_iff_decode _ n rest).mpr ⟨decode_encode n rest, hn⟩

/--
For all bytes `bytes`, `decodeBounded bytes` reports `tooLarge` exactly when the generic `decode` accepts `bytes` with a value above `0x02000000`.
-/
theorem decodeBounded_eq_error_tooLarge_iff (bytes : List UInt8) :
    decodeBounded bytes = .error .tooLarge ↔
      ∃ value rest, decode bytes = some (value, rest) ∧ 0x02000000 < value.toNat := by
  rw [← readCanonical_toOption]
  have hne := readCanonical_ne_tooLarge bytes
  unfold decodeBounded
  cases hc : readCanonical bytes with
  | error e =>
    rw [hc] at hne
    simp only [Except.toOption, reduceCtorEq, false_and, exists_false, iff_false]
    exact hne
  | ok p =>
    obtain ⟨n, r⟩ := p
    have hle : (n > maxSize) ↔ 0x02000000 < n.toNat := by
      rw [GT.gt, UInt64.lt_iff_toNat_lt, maxSize_toNat]
    by_cases h : n > maxSize
    · simp only [h, ite_true, true_iff]
      exact ⟨n, r, rfl, hle.mp h⟩
    · simp only [h, ite_false, reduceCtorEq, false_iff, not_exists, not_and]
      intro v r' hs
      simp only [Except.toOption, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact fun hv => h (hle.mpr hv)

/-! ## The distinguishing input -/

/--
`fe 01 00 00 02` is the canonical encoding of `0x02000001`, the smallest value above `MAX_SIZE`.
-/
theorem encode_maxSize_succ : encode 0x02000001 = [0xfe, 0x01, 0x00, 0x00, 0x02] := rfl

/-- The generic decoder accepts `fe 01 00 00 02` as `0x02000001`, with no remainder. -/
theorem decode_maxSize_succ : decode [0xfe, 0x01, 0x00, 0x00, 0x02] = some (0x02000001, []) := rfl

/-- Core's reader rejects `fe 01 00 00 02` as `tooLarge`. -/
theorem decodeBounded_maxSize_succ :
    decodeBounded [0xfe, 0x01, 0x00, 0x00, 0x02] = .error .tooLarge := rfl

/--
The bounded round trip fails for `0x02000001`: `decodeBounded (encode 0x02000001)` is `tooLarge`.
So the hypothesis `n ≤ 0x02000000` of `decodeBounded_encode` cannot be removed.
-/
theorem decodeBounded_encode_maxSize_succ :
    decodeBounded (encode 0x02000001) = .error .tooLarge := rfl

end DogeLib.Serialization.CompactSize
