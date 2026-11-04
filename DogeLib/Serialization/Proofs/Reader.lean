module

public import DogeLib.Serialization.Reader
public import DogeLib.Serialization.Proofs.Codec

/-!
# Proofs: `Serialization.Reader`

The agreement of a reader with a codec, and its preservation by `readFixed`, `readPair` and `readMap`.

`ReaderAgrees c r P` says that the reader `r` accepts exactly what the codec `c` accepts with a value that satisfies `P`.
On those inputs it returns the same value and remainder.
It says nothing about which error the reader reports on the other inputs.

- `readFixed_agrees`: `readFixed` agrees with its codec, with no condition.
- `readPair_agrees`: the pair of two agreeing readers agrees with the pair codec, with both conditions.
- `readMap_agrees`: a reader carried along `invFun` agrees with `Codec.ofEquiv toFun invFun`, if `toFun (invFun b) = b` for every `b`.
- `ReaderAgrees.congr`: the condition can be replaced by an equivalent one.
-/

@[expose] public section

namespace DogeLib.Serialization

open CompactSize (ReadError)

/--
The reader `r` agrees with the codec `c` under the condition `P`: for all bytes `bs`, values `a` and bytes `rest`, `r bs = ok (a, rest)` exactly when `c.decode bs = some (a, rest)` and `P a`.
-/
def ReaderAgrees {α : Type} (c : Codec α) (r : List UInt8 → Except ReadError (α × List UInt8))
    (P : α → Prop) : Prop :=
  ∀ bs a rest, r bs = .ok (a, rest) ↔ c.decode bs = some (a, rest) ∧ P a

/-- If `r` agrees with `c` under `P`, and `P` and `Q` hold for the same values, then `r` agrees with `c` under `Q`. -/
theorem ReaderAgrees.congr {α : Type} {c : Codec α} {r : List UInt8 → Except ReadError (α × List UInt8)}
    {P Q : α → Prop} (h : ReaderAgrees c r P) (hPQ : ∀ a, P a ↔ Q a) : ReaderAgrees c r Q := by
  intro bs a rest
  rw [h, hPQ]

/-- For every codec, `readFixed` agrees with it with no condition. -/
theorem readFixed_agrees {α : Type} [c : Codec α] :
    ReaderAgrees c (readFixed (α := α)) (fun _ => True) := by
  intro bs a rest
  unfold readFixed
  cases h : Codec.decode (α := α) bs with
  | none => simp
  | some p => simp

/-- If `r1` agrees with `ca` under `P1` and `r2` agrees with `cb` under `P2`, then `readPair r1 r2` agrees with the pair codec under both conditions. -/
theorem readPair_agrees {α β : Type} {ca : Codec α} {cb : Codec β}
    {r1 : List UInt8 → Except ReadError (α × List UInt8)}
    {r2 : List UInt8 → Except ReadError (β × List UInt8)} {P1 : α → Prop} {P2 : β → Prop}
    (h1 : ReaderAgrees ca r1 P1) (h2 : ReaderAgrees cb r2 P2) :
    ReaderAgrees (@instCodecProd α β ca cb) (readPair r1 r2) (fun p => P1 p.1 ∧ P2 p.2) := by
  letI := ca
  letI := cb
  intro bs p rest
  obtain ⟨a, b⟩ := p
  show _ ↔ decodeProd bs = some ((a, b), rest) ∧ _
  constructor
  · intro h
    unfold readPair at h
    split at h
    · cases h
    · next a' r ha =>
      split at h
      · cases h
      · next b' r' hb =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        obtain ⟨da, pa⟩ := (h1 _ _ _).mp ha
        obtain ⟨db, pb⟩ := (h2 _ _ _).mp hb
        refine ⟨?_, pa, pb⟩
        simp only [decodeProd, Option.bind_eq_bind, Option.pure_def]
        rw [show Codec.decode bs = some (a', r) from da, Option.bind_some]
        dsimp only
        rw [show Codec.decode r = some (b', _) from db, Option.bind_some]
  · rintro ⟨hd, pa, pb⟩
    simp only [decodeProd, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨⟨a', r⟩, da, ⟨b', r'⟩, db, ⟨rfl, rfl⟩, rfl⟩ := hd
    have ha := (h1 _ _ _).mpr ⟨da, pa⟩
    have hb := (h2 _ _ _).mpr ⟨db, pb⟩
    unfold readPair
    rw [ha]
    dsimp only
    rw [hb]

/--
If `r` agrees with `cb` under `P`, and `toFun (invFun b) = b` for every `b`, then `readMap invFun r` agrees with `Codec.ofEquiv toFun invFun cb` under `P ∘ toFun`.
-/
theorem readMap_agrees {α β : Type} (toFun : α → β) (invFun : β → α)
    (right_inv : ∀ b, toFun (invFun b) = b) {cb : Codec β}
    {r : List UInt8 → Except ReadError (β × List UInt8)} {P : β → Prop}
    (h : ReaderAgrees cb r P) :
    ReaderAgrees (Codec.ofEquiv toFun invFun cb) (readMap invFun r) (fun a => P (toFun a)) := by
  intro bs a rest
  show _ ↔ (cb.decode bs).map (fun p => (invFun p.1, p.2)) = some (a, rest) ∧ _
  unfold readMap
  cases hr : r bs with
  | error e =>
    simp only [reduceCtorEq, false_iff, not_and]
    intro hd hp
    cases hdec : cb.decode bs with
    | none => rw [hdec] at hd; cases hd
    | some q =>
      obtain ⟨b, r'⟩ := q
      rw [hdec] at hd
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      rw [right_inv] at hp
      have := (h bs b r').mpr ⟨hdec, hp⟩
      rw [hr] at this
      cases this
  | ok q =>
    obtain ⟨b, r'⟩ := q
    obtain ⟨hdec, hp⟩ := (h bs b r').mp hr
    rw [hdec]
    simp only [Except.ok.injEq, Prod.mk.injEq, Option.map_some, Option.some.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, rfl⟩, by rw [right_inv]; exact hp⟩
    · rintro ⟨⟨rfl, rfl⟩, -⟩
      exact ⟨rfl, rfl⟩

end DogeLib.Serialization
