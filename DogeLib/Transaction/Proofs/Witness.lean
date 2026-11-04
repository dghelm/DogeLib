module

public import DogeLib.Transaction.Proofs.Serialization
public import DogeLib.Transaction.Proofs.Txid
public import DogeLib.Transaction.Witness

/-!
# Proofs: `Transaction.Witness`

The contract of Core's reader of the witness-allowed format, which models a serialization format only.
Core rejects blocks with witness data on main and test at the pin.
`DogeLib.Transaction.Witness` documents the separate consensus mechanisms and their sources.

- `Transaction.readAllowWitness_eq_readBase`: suppose the first input count reads as a list that is not empty.
  Then the reader returns what the base-mode reader returns, with an empty stack per input, and the same error.
- `WitnessTransaction.readAllowWitness_encode`: the round trip, for a transaction with witness data, or with inputs, or with no outputs.
  The counts must be within `MAX_SIZE`.
- `Transaction.readAllowWitness_flags_zero`: a zero input count and zero flags give a transaction with no inputs and no outputs.
- `noInputsExample_not_roundTrip`: a transaction with no inputs and one output is not read back.
  Its base serialization reads as a different transaction, with bytes left over.
- `readAllowWitness_flags_two`, `readAllowWitness_flags_three`: complete transactions with flags `02` and `03` fail with `unknownOptionalData`.
- `readStacks_length`: `readStacks` returns one stack per input, so the last check of the reader never fails.
- `WitnessTransaction.wtxid_of_hasWitness_false`: without witness data, the witness hash is the transaction ID.

The theorems do not say which error the reader reports on an input that it rejects.
The known answers check the errors and their order.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization
open DogeLib.Serialization.CompactSize (ReadError)

/-! ## The codec and the bounds of a witness stack -/

/-- The codec of a witness stack is lawful. -/
instance instLawfulCodecWitnessStack : LawfulCodec WitnessStack :=
  LawfulCodec.ofEquiv WitnessStack.items WitnessStack.mk (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- A witness stack has at most `0x02000000` items, and each item has at most `0x02000000` bytes: the bounds of Core's reader. -/
def WitnessStack.WithinMaxSize (s : WitnessStack) : Prop :=
  s.items.val.length ≤ 0x02000000 ∧ ∀ i ∈ s.items.val, i.val.length ≤ 0x02000000

/-- Every count of the transaction and of each witness stack is within `MAX_SIZE`. The writer needs no bound, but Core's reader does. -/
def WitnessTransaction.WithinMaxSize (w : WitnessTransaction) : Prop :=
  w.tx.WithinMaxSize ∧ ∀ s ∈ w.witnesses, s.WithinMaxSize

/-- `WitnessStack.read` agrees with the codec of a witness stack, under `WitnessStack.WithinMaxSize`. -/
theorem WitnessStack.read_agrees :
    ReaderAgrees instCodecWitnessStack WitnessStack.read WitnessStack.WithinMaxSize :=
  (readMap_agrees WitnessStack.items WitnessStack.mk (fun _ => rfl)
    (CountedList.decodeBounded_agrees CountedList.decodeBoundedBytes_agrees)).congr
    (fun _ => Iff.rfl)

/-- A stack is empty exactly when it is `WitnessStack.empty`. -/
theorem WitnessStack.isEmpty_iff (s : WitnessStack) : s.isEmpty = true ↔ s = WitnessStack.empty := by
  obtain ⟨⟨l, hl⟩⟩ := s
  cases l with
  | nil => simp [WitnessStack.isEmpty, WitnessStack.empty]
  | cons x xs => simp [WitnessStack.isEmpty, WitnessStack.empty]

/-! ## One stack per input -/

/-- For every element reader, `n` and input: a list that `readElemsBounded` returns has `n` elements. -/
theorem readElemsBounded_length {α : Type} (elem : List UInt8 → Except ReadError (α × List UInt8))
    (n : Nat) (bs : List UInt8) (xs : List α) (r : List UInt8)
    (h : CountedList.readElemsBounded elem n bs = .ok (xs, r)) : xs.length = n := by
  induction n generalizing bs xs r with
  | zero =>
    simp only [CountedList.readElemsBounded, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | succ n ih =>
    unfold CountedList.readElemsBounded at h
    split at h
    · cases h
    · split at h
      · cases h
      · next x _ _ xs' r' hxs =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, ih _ _ _ hxs]

/-- `readStacks` returns one stack for each of the `n` inputs. So the last check of `Transaction.readAllowWitness` never fails. -/
theorem readStacks_length (flag : Bool) (n : Nat) (bs : List UInt8) (ws : List WitnessStack)
    (r : List UInt8) (h : readStacks flag n bs = .ok (ws, r)) : ws.length = n := by
  unfold readStacks at h
  split at h
  · rw [CountedList.readElemsBoundedLoop_nil] at h
    exact readElemsBounded_length _ _ _ _ _ h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_replicate]

/-! ## Bounds after a successful read -/

/-- Successful sections contain input and output lists, including their scripts, within `MAX_SIZE`. -/
private theorem readSections_withinMaxSize (bs : List UInt8) (flags : UInt8)
    (vin : CountedList TxIn) (vout : CountedList TxOut) (rest : List UInt8)
    (h : readSections bs = .ok ((flags, vin, vout), rest)) :
    (vin.val.length ≤ 0x02000000 ∧ ∀ i ∈ vin.val, i.WithinMaxSize) ∧
      (vout.val.length ≤ 0x02000000 ∧ ∀ o ∈ vout.val, o.WithinMaxSize) := by
  unfold readSections at h
  split at h
  · cases h
  · next ins r hin =>
    have hi := ((CountedList.decodeBounded_agrees TxIn.read_agrees _ _ _).mp hin).2
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
          exact ⟨hi, by simp⟩
        · split at h
          · cases h
          · next ins' outs r' hpair =>
            have hb := ((readPair_agrees
              (CountedList.decodeBounded_agrees TxIn.read_agrees)
              (CountedList.decodeBounded_agrees TxOut.read_agrees) _ _ _).mp hpair).2
            cases h
            exact hb
    · split at h
      · cases h
      · next outs r' hout =>
        have ho := ((CountedList.decodeBounded_agrees TxOut.read_agrees _ _ _).mp hout).2
        cases h
        exact ⟨hi, ho⟩

/--
A successful witness-allowed read returns base fields whose input, output and script counts are within `MAX_SIZE`.
This bound concerns the serialization format and does not establish consensus acceptance of witness data.
-/
theorem Transaction.readAllowWitness_withinMaxSize (bs : List UInt8)
    (w : WitnessTransaction) (rest : List UInt8)
    (hRead : Transaction.readAllowWitness bs = .ok (w, rest)) : w.tx.WithinMaxSize := by
  unfold Transaction.readAllowWitness at hRead
  split at hRead
  · cases hRead
  · split at hRead
    · cases hRead
    · next _ _ flags vin vout r2 hsections =>
      have hb := readSections_withinMaxSize _ _ _ _ _ hsections
      split at hRead
      · cases hRead
      · split at hRead
        · cases hRead
        · split at hRead
          · cases hRead
          · dsimp only at hRead
            split at hRead
            · cases hRead
              exact ⟨hb.1.1, hb.1.2, hb.2.1, hb.2.2⟩
            · cases hRead

/-! ## Agreement with the base mode -/

/-- The fixed-length reader returns the value that the codec wrote, and the bytes after it. -/
private theorem readFixed_encode {α : Type} [Codec α] [LawfulCodec α] (a : α) (rest : List UInt8) :
    readFixed (Codec.encode a ++ rest) = .ok (a, rest) := by
  unfold readFixed
  rw [LawfulCodec.decode_encode]

/--
Agreement with the base mode, for every input `bs` whose first input count reads as a list that is not empty.

Then `readAllowWitness bs` is `readBase bs`, with an empty stack for each input, and an error of `readBase` is the same error, wrapped in `WitnessReadError.read`.
The hypothesis covers the inputs where the version or the input list fails to read, since it then holds vacuously.
-/
theorem Transaction.readAllowWitness_eq_readBase (bs : List UInt8)
    (h : ∀ v r1 vin r2, readFixed (α := UInt32) bs = .ok (v, r1) →
      CountedList.decodeBounded TxIn.read r1 = .ok (vin, r2) → vin.val ≠ []) :
    Transaction.readAllowWitness bs =
      ((Transaction.readBase bs).map fun p => (WitnessTransaction.ofBase p.1, p.2)).mapError .read := by
  unfold Transaction.readAllowWitness Transaction.readBase readMap readPair readSections
  cases hv : readFixed (α := UInt32) bs with
  | error e => rfl
  | ok p =>
    obtain ⟨v, r1⟩ := p
    simp only
    cases hin : CountedList.decodeBounded TxIn.read r1 with
    | error e => rfl
    | ok q =>
      obtain ⟨vin, r2⟩ := q
      have hne := h v r1 vin r2 hv hin
      have hempty : vin.val.isEmpty = false := by simpa using hne
      simp only [hempty, Bool.false_eq_true, ↓reduceIte]
      cases hout : CountedList.decodeBounded TxOut.read r2 with
      | error e => rfl
      | ok s =>
        obtain ⟨vout, r3⟩ := s
        simp only [readStacks, show ((0 : UInt8) &&& 1 = 1) = False by decide, show ((0 : UInt8) &&& 0xfe ≠ 0) = False by decide,
          decide_false, Bool.false_eq_true, ↓reduceIte]
        cases hl : readFixed (α := UInt32) r3 with
        | error e => rfl
        | ok t =>
          obtain ⟨l, r4⟩ := t
          simp [List.length_replicate, Except.map, Except.mapError, WitnessTransaction.ofBase, Transaction.ofProd]

/-! ## Round trip -/

/-- The encoding of the empty input list is the single byte `0x00`. -/
private theorem encode_emptyInputs (rest : List UInt8) :
    CountedList.decodeBounded TxIn.read (0x00 :: rest) = .ok (⟨[], by decide⟩, rest) := by
  show CountedList.decodeBounded TxIn.read (Codec.encode (⟨[], by decide⟩ : CountedList TxIn) ++ rest) = _
  exact (CountedList.decodeBounded_agrees TxIn.read_agrees _ _ _).mpr
    ⟨LawfulCodec.decode_encode _ rest, by simp, by simp⟩

/-- A counted list within `MAX_SIZE` whose elements satisfy the condition of an agreeing reader is read back by `decodeBounded`. -/
private theorem decodeBounded_encode_of_agrees {α : Type} [c : Codec α] [LawfulCodec α]
    {elem : List UInt8 → Except ReadError (α × List UInt8)} {P : α → Prop}
    (h : ReaderAgrees c elem P) (cl : CountedList α) (hlen : cl.val.length ≤ 0x02000000)
    (hp : ∀ x ∈ cl.val, P x) (rest : List UInt8) :
    CountedList.decodeBounded elem (Codec.encode cl ++ rest) = .ok (cl, rest) :=
  (CountedList.decodeBounded_agrees h _ _ _).mpr ⟨LawfulCodec.decode_encode _ rest, hlen, hp⟩

/-- The stacks of `ws`, each within `MAX_SIZE`, are read back one per input. -/
private theorem readStacks_encode (ws : List WitnessStack) (hm : ∀ s ∈ ws, s.WithinMaxSize)
    (n : Nat) (hn : ws.length = n) (rest : List UInt8) :
    readStacks true n (CountedList.encodeElems ws ++ rest) = .ok (ws, rest) := by
  subst hn
  unfold readStacks
  simp only [↓reduceIte]
  rw [CountedList.readElemsBoundedLoop_nil]
  exact (CountedList.readElemsBounded_eq_ok_iff_of_agrees WitnessStack.read_agrees _ _ _ _).mpr
    ⟨CountedList.decodeElems_encodeElems ws rest, hm⟩

/-- Without witness data, every stack is empty, so the stacks are those of `ofBase`. -/
private theorem witnesses_eq_replicate (w : WitnessTransaction) (hw : w.hasWitness = false) :
    w.witnesses = List.replicate w.tx.inputs.val.length WitnessStack.empty := by
  rw [List.eq_replicate_iff]
  refine ⟨w.witnesses_length, fun s hs => ?_⟩
  have := List.any_eq_false.mp hw s hs
  simpa [WitnessStack.isEmpty_iff] using this

/-- Two values with the same transaction and the same stacks are equal. -/
private theorem WitnessTransaction.ext' {a b : WitnessTransaction} (h1 : a.tx = b.tx)
    (h2 : a.witnesses = b.witnesses) : a = b := by
  cases a; cases b; cases h1; cases h2; rfl

/--
The round trip of Core's reader of the witness-allowed format.

Let `w` be a transaction whose counts are within `MAX_SIZE`, and `rest` any bytes.
If `w` has witness data, or has an input, or has no output, then `readAllowWitness (w.encode ++ rest) = ok (w, rest)`.

A transaction with no inputs, some outputs and no witness data is excluded. Its base serialization is not guaranteed to be read back.
`noInputsExample_not_roundTrip` gives one such transaction.
-/
theorem WitnessTransaction.readAllowWitness_encode (w : WitnessTransaction) (hm : w.WithinMaxSize)
    (hshape : w.hasWitness = true ∨ w.tx.inputs.val ≠ [] ∨ w.tx.outputs.val = [])
    (rest : List UInt8) :
    Transaction.readAllowWitness (w.encode ++ rest) = .ok (w, rest) := by
  obtain ⟨⟨hinLen, hinP, houtLen, houtP⟩, hstacks⟩ := hm
  obtain ⟨⟨v, vin, vout, l⟩, ws, hws⟩ := w
  by_cases hw : WitnessTransaction.hasWitness ⟨⟨v, vin, vout, l⟩, ws, hws⟩ = true
  · -- The extended form.
    simp only [WitnessTransaction.encode, hw, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append]
    unfold Transaction.readAllowWitness readSections
    rw [readFixed_encode]
    simp only
    rw [encode_emptyInputs]
    simp only [List.isEmpty_nil, ↓reduceIte, CountedList.readByte,
      show ((1 : UInt8) = 0) = False by decide, readPair]
    rw [decodeBounded_encode_of_agrees TxIn.read_agrees vin hinLen hinP]
    simp only
    rw [decodeBounded_encode_of_agrees TxOut.read_agrees vout houtLen houtP]
    simp only [show ((1 : UInt8) &&& 1 = 1) = True by decide, decide_true]
    rw [readStacks_encode ws hstacks _ hws]
    simp only [show ((1 : UInt8) &&& 0xfe ≠ 0) = False by decide, ↓reduceIte]
    rw [readFixed_encode]
    simp [hws]
  · -- The base form.
    have hwf : WitnessTransaction.hasWitness ⟨⟨v, vin, vout, l⟩, ws, hws⟩ = false := by simpa using hw
    have hrep := witnesses_eq_replicate _ hwf
    simp only at hrep
    simp only [WitnessTransaction.encode, hwf, Bool.false_eq_true, ↓reduceIte]
    have henc : Codec.encode (⟨v, vin, vout, l⟩ : Transaction) =
        Codec.encode v ++ (Codec.encode vin ++ (Codec.encode vout ++ Codec.encode l)) := rfl
    by_cases hne : vin.val ≠ []
    · rw [Transaction.readAllowWitness_eq_readBase]
      · rw [Transaction.readBase_encode _ ⟨hinLen, hinP, houtLen, houtP⟩]
        simp only [Except.map, Except.mapError, Except.ok.injEq, Prod.mk.injEq, and_true]
        exact WitnessTransaction.ext' rfl hrep.symm
      · intro v' r1 vin' r2 hv hvin
        rw [henc, List.append_assoc, readFixed_encode] at hv
        simp only [Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        rw [List.append_assoc, decodeBounded_encode_of_agrees TxIn.read_agrees vin hinLen hinP] at hvin
        simp only [Except.ok.injEq, Prod.mk.injEq] at hvin
        rw [← hvin.1]
        exact hne
    · have hvin : vin.val = [] := by simpa using hne
      have hnil : vout.val = [] := by
        rcases hshape with h | h | h
        · exact absurd h hw
        · exact absurd hvin h
        · exact h
      have hvin' : vin = ⟨[], by decide⟩ := Subtype.ext hvin
      have hvout' : vout = ⟨[], by decide⟩ := Subtype.ext hnil
      subst hvin' hvout'
      have hws' : ws = [] := List.eq_nil_of_length_eq_zero hws
      subst hws'
      rw [henc]
      have h0 : Codec.encode (⟨[], by decide⟩ : CountedList TxIn) = [0x00] := rfl
      have h0' : Codec.encode (⟨[], by decide⟩ : CountedList TxOut) = [0x00] := rfl
      rw [h0, h0']
      unfold Transaction.readAllowWitness readSections
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [readFixed_encode]
      simp only
      rw [encode_emptyInputs]
      simp only [List.isEmpty_nil, ↓reduceIte, CountedList.readByte, readStacks,
        show ((0 : UInt8) &&& 1 = 1) = False by decide, show ((0 : UInt8) &&& 0xfe ≠ 0) = False by decide,
        decide_false, Bool.false_eq_true]
      rw [readFixed_encode]
      simp

/--
A zero input count and zero flags give a transaction with no inputs and no outputs.
This holds for every version `v`, lock time `l` and bytes `rest`.
It reads no output count (D4, lines 220 to 226).
-/
theorem Transaction.readAllowWitness_flags_zero (v l : UInt32) (rest : List UInt8) :
    Transaction.readAllowWitness (Codec.encode v ++ [0x00, 0x00] ++ Codec.encode l ++ rest) =
      .ok (⟨⟨v, ⟨[], by decide⟩, ⟨[], by decide⟩, l⟩, [], rfl⟩, rest) := by
  unfold Transaction.readAllowWitness readSections
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [readFixed_encode]
  simp only
  rw [encode_emptyInputs]
  simp only [List.isEmpty_nil, ↓reduceIte, CountedList.readByte, readStacks,
    show ((0 : UInt8) &&& 1 = 1) = False by decide, show ((0 : UInt8) &&& 0xfe ≠ 0) = False by decide,
    decide_false, Bool.false_eq_true]
  rw [readFixed_encode]
  simp

/-! ## The ambiguity of a transaction with no inputs -/

/-- Version 1, no inputs, one output of value 0 with an empty script, lock time 0. -/
def noInputsExample : Transaction :=
  ⟨1, ⟨[], by decide⟩, ⟨[⟨0, ⟨⟨[], by decide⟩⟩⟩], by decide⟩, 0⟩

/--
The base serialization of `noInputsExample` is not read back by the reader of the witness-allowed format.
Core reads its output count `01` as flags.
It then reads the zero bytes of the output as an empty input list, an empty output list and the lock time.
Seven bytes remain, so the complete reader reports them.
-/
theorem noInputsExample_not_roundTrip :
    Transaction.decodeAllowWitnessComplete (Codec.encode noInputsExample) = .error (.trailingBytes 7) := by
  rfl

/-! ## Flags other than bit 0 -/

/-- One input with a zero outpoint, an empty script and sequence `0xffffffff`. Then one output of value 0 with an empty script. -/
def oneInputOneOutput : List UInt8 :=
  [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x01] ++ List.replicate 8 0 ++ [0x00]

/--
Flags `02`, with complete lists and a lock time: Core reads the lists, and then fails with "Unknown transaction optional data" (D4, lines 238 to 241).
-/
theorem readAllowWitness_flags_two :
    Transaction.readAllowWitness ([0x01, 0, 0, 0, 0x00, 0x02] ++ oneInputOneOutput ++ [0, 0, 0, 0]) =
      .error .unknownOptionalData := by
  rfl

/--
Flags `03`, with complete lists, a stack and a lock time: Core clears bit 0, reads the stack, and then fails on bit 1.
-/
theorem readAllowWitness_flags_three :
    Transaction.readAllowWitness ([0x01, 0, 0, 0, 0x00, 0x03] ++ oneInputOneOutput ++ [0x01, 0x01, 0xab] ++ [0, 0, 0, 0]) =
      .error .unknownOptionalData := by
  rfl

/-! ## The witness hash -/

/-- Without witness data, the witness hash is the transaction ID: Core's `GetWitnessHash` returns `GetHash` (D23). -/
theorem WitnessTransaction.wtxid_of_hasWitness_false (w : WitnessTransaction) (h : w.hasWitness = false) :
    w.wtxid = w.tx.txid := by
  simp [WitnessTransaction.wtxid, h]

end DogeLib.Transaction
