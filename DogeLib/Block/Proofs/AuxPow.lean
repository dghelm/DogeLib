module

public import DogeLib.Block.AuxPow
public import DogeLib.Block.Proofs.Header
public import DogeLib.Transaction.Proofs.Witness

/-!
# Properties of the full header codec

The theorems relate `BlockHeader.read` and `BlockHeader.encode` in each read mode of the embedded transaction.

- `BlockHeader.read_auxpow_isSome`: a decoded header has a payload exactly when its AuxPoW flag is set.
- `BlockHeader.read_pure` and `BlockHeader.encode_take`: the first 80 bytes are the pure header in the existing 80-byte codec.
- `BlockHeader.read_encode_allowWitness`: the round trip in the witness-allowed mode.
- `BlockHeader.read_encode_base`: the round trip in base mode, which returns the base projection of the header.
- `BlockHeader.read_encode_flag_clear`: with the flag clear, the reader consumes exactly the 80 bytes of the pure header.
- `BlockHeader.read_extends`: bytes appended to an accepted input stay in the remainder, in each mode.
- `BlockHeader.read_take_encode_allowWitness` and `BlockHeader.read_take_encode_base`: under the round-trip hypotheses, the reader rejects every proper prefix of an encoding.
- `extendedEmptyStacks_read`: the reader keeps Core's acceptance of an extended witness encoding whose stacks are all empty.
- `extendedEmptyStacks_read_base`: base mode reads the same bytes as a different transaction and leaves bytes over.

The round trips are canonicality over encoder output: the reader accepts the encoding of a header and returns that header.
No theorem says that every accepted byte string is the encoding of its result.
In the witness-allowed mode that claim is false: `extendedEmptyStacks_read` gives two byte strings that read as one header.

The theorems do not say which error the reader reports on an input that it rejects.
The known answers check errors, and they check truncation at every proper prefix of each fixture.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization
open DogeLib.Transaction
open CompactSize (ReadError)

/-! ## Conditions -/

/-- Each branch of the payload has at most `MAX_SIZE = 0x02000000` hashes: the bound of Core's vector reader (D1). -/
def AuxPow.WithinMaxSize (a : AuxPow) : Prop :=
  a.merkleBranch.val.length ≤ 0x02000000 ∧ a.chainMerkleBranch.val.length ≤ 0x02000000

/--
The conditions of the witness-allowed round trip, for a payload `a`.
The branches and the transaction counts are within `MAX_SIZE`.
The transaction has the shape of `WitnessTransaction.readAllowWitness_encode`: witness data, or an input, or no output.
-/
def AuxPow.RoundTripsAllowWitness (a : AuxPow) : Prop :=
  a.WithinMaxSize ∧ a.tx.WithinMaxSize ∧
    (a.tx.hasWitness = true ∨ a.tx.tx.inputs.val ≠ [] ∨ a.tx.tx.outputs.val = [])

/-- The conditions of the base-mode round trip, for a payload `a`: the branches and the base transaction counts are within `MAX_SIZE`. -/
def AuxPow.RoundTripsBase (a : AuxPow) : Prop :=
  a.WithinMaxSize ∧ a.tx.tx.WithinMaxSize

/-- The payload with its transaction's stacks replaced by empty ones: what a base-mode read of its base-mode encoding returns. -/
def AuxPow.baseProjection (a : AuxPow) : AuxPow :=
  { a with tx := WitnessTransaction.ofBase a.tx.tx }

/-- The header with the base projection of its payload, if it has one. -/
def BlockHeader.baseProjection (h : BlockHeader) : BlockHeader :=
  ⟨h.pure, h.auxpow.map AuxPow.baseProjection⟩

/-! ## The fields after the transaction -/

/-- Core's vector reader of hashes agrees with the codec of counted lists of hashes, for lists within `MAX_SIZE`. -/
theorem readHashes_agrees :
    ReaderAgrees (instCodecCountedList (α := Hash256)) readHashes
      (fun cl => cl.val.length ≤ 0x02000000) :=
  (CountedList.decodeBounded_agrees (readFixed_agrees (α := Hash256))).congr (fun _ => by simp)

/-- The fields after the transaction are read back from their encoding when both branches are within `MAX_SIZE`. -/
theorem AuxPow.readTail_encode (a : AuxPow) (hm : a.WithinMaxSize) (rest : List UInt8) :
    AuxPow.readTail (Codec.encode a.tail ++ rest) = .ok (a.tail, rest) := by
  have hr := readPair_agrees (readFixed_agrees (α := Hash256))
    (readPair_agrees readHashes_agrees
      (readPair_agrees (readFixed_agrees (α := UInt32))
        (readPair_agrees readHashes_agrees
          (readPair_agrees (readFixed_agrees (α := UInt32)) (readFixed_agrees (α := PureBlockHeader))))))
  exact (hr _ _ _).mpr ⟨LawfulCodec.decode_encode _ rest, trivial, hm.1, trivial, hm.2, trivial, trivial⟩

/-- A payload is rebuilt from its transaction and the fields after it. -/
theorem AuxPow.ofTail_tail (a : AuxPow) : AuxPow.ofTail a.tx a.tail = a := rfl

/-! ## The payload -/

/-- The witness-allowed round trip of a payload, under `AuxPow.RoundTripsAllowWitness`, with every suffix `rest` preserved. -/
theorem AuxPow.read_encode_allowWitness (a : AuxPow) (ha : a.RoundTripsAllowWitness)
    (rest : List UInt8) :
    AuxPow.read .allowWitness (AuxPow.encode .allowWitness a ++ rest) = .ok (a, rest) := by
  obtain ⟨hm, htx, hshape⟩ := ha
  unfold AuxPow.read AuxPow.encode
  simp only [encodeTx, readTx, List.append_assoc]
  rw [WitnessTransaction.readAllowWitness_encode a.tx htx hshape]
  simp only
  rw [AuxPow.readTail_encode a hm]
  rfl

/-- The base-mode round trip of a payload, under `AuxPow.RoundTripsBase`: the result is the base projection, and every suffix `rest` is preserved. -/
theorem AuxPow.read_encode_base (a : AuxPow) (ha : a.RoundTripsBase) (rest : List UInt8) :
    AuxPow.read .base (AuxPow.encode .base a ++ rest) = .ok (a.baseProjection, rest) := by
  obtain ⟨hm, htx⟩ := ha
  unfold AuxPow.read AuxPow.encode
  simp only [encodeTx, readTx, List.append_assoc]
  rw [Transaction.readBase_encode a.tx.tx htx]
  simp only
  rw [AuxPow.readTail_encode a hm]
  rfl

/-! ## The full header -/

/-- For every mode and input, a header that the reader returns has a payload exactly when its AuxPoW flag is set (design record 0004, item 12). -/
theorem BlockHeader.read_auxpow_isSome (mode : TxReadMode) (bs : List UInt8) (h : BlockHeader)
    (rest : List UInt8) (hr : BlockHeader.read mode bs = .ok (h, rest)) :
    h.auxpow.isSome = h.pure.isAuxpow := by
  unfold BlockHeader.read at hr
  split at hr
  · cases hr
  · next pure r1 _ =>
    split at hr
    · next hflag =>
      split at hr
      · cases hr
      · cases hr
        simp [hflag]
    · next hflag =>
      cases hr
      simp at hflag
      simp [hflag]

/--
For every mode and input, a header that the reader returns starts with its pure header in the 80-byte codec.
The pure-header decoder returns that header with the input after its first 80 bytes.
-/
theorem BlockHeader.read_pure (mode : TxReadMode) (bs : List UInt8) (h : BlockHeader)
    (rest : List UInt8) (hr : BlockHeader.read mode bs = .ok (h, rest)) :
    Codec.decode (α := PureBlockHeader) bs = some (h.pure, bs.drop 80) := by
  unfold BlockHeader.read readFixed at hr
  split at hr
  · cases hr
  · next pure r1 hd =>
    split at hd
    · next p hdec =>
      cases hd
      have hbs := PureBlockHeader.decode_sound _ _ _ hdec
      have hdrop : bs.drop 80 = r1 := by
        rw [hbs, ← PureBlockHeader.encode_length pure, List.drop_left]
      have hpure : h.pure = pure := by
        split at hr
        · split at hr
          · cases hr
          · cases hr; rfl
        · cases hr; rfl
      rw [hpure, hdrop, hdec]
    · cases hd

/-- For every mode, the first 80 bytes of a header's encoding are the encoding of its pure header in the 80-byte codec. -/
theorem BlockHeader.encode_take (mode : TxReadMode) (h : BlockHeader) :
    (BlockHeader.encode mode h).take 80 = Codec.encode h.pure := by
  unfold BlockHeader.encode
  rw [← PureBlockHeader.encode_length h.pure, List.take_left]

/-- The pure header is read back from its encoding with every suffix preserved. -/
private theorem readFixed_pure (p : PureBlockHeader) (rest : List UInt8) :
    readFixed (α := PureBlockHeader) (Codec.encode p ++ rest) = .ok (p, rest) := by
  unfold readFixed
  rw [PureBlockHeader.decode_encode]

/--
Suppose the AuxPoW flag of `p` is clear.
Then the reader returns `p` without a payload and consumes exactly its 80 bytes, in every mode and with every suffix `rest`.
-/
theorem BlockHeader.read_encode_flag_clear (mode : TxReadMode) (p : PureBlockHeader)
    (hflag : p.isAuxpow = false) (rest : List UInt8) :
    BlockHeader.read mode (Codec.encode p ++ rest) = .ok (⟨p, none⟩, rest) := by
  unfold BlockHeader.read
  rw [readFixed_pure]
  simp [hflag]

/--
The round trip of the full header in the witness-allowed mode, with every suffix `rest` preserved.

The header must have a payload exactly when its flag is set.
A payload must satisfy `AuxPow.RoundTripsAllowWitness`: its branches and transaction counts are within `MAX_SIZE`.
Its transaction must also have witness data, or an input, or no output.
The theorem is canonicality over encoder output only.
-/
theorem BlockHeader.read_encode_allowWitness (h : BlockHeader)
    (hflag : h.auxpow.isSome = h.pure.isAuxpow)
    (ha : ∀ a ∈ h.auxpow, a.RoundTripsAllowWitness) (rest : List UInt8) :
    BlockHeader.read .allowWitness (BlockHeader.encode .allowWitness h ++ rest) = .ok (h, rest) := by
  obtain ⟨p, aux⟩ := h
  cases aux with
  | none =>
    have hf : p.isAuxpow = false := by simpa using hflag.symm
    have henc : BlockHeader.encode .allowWitness ⟨p, none⟩ = Codec.encode p := by
      simp [BlockHeader.encode]
    rw [henc, BlockHeader.read_encode_flag_clear _ _ hf]
  | some a =>
    have hf : p.isAuxpow = true := by simpa using hflag.symm
    unfold BlockHeader.encode BlockHeader.read
    simp only [hf, ↓reduceIte, Option.map_some, Option.getD_some, List.append_assoc]
    rw [readFixed_pure]
    simp only [hf, ↓reduceIte]
    rw [AuxPow.read_encode_allowWitness a (ha a rfl)]

/--
The round trip of the full header in base mode, with every suffix `rest` preserved.

The header must have a payload exactly when its flag is set.
A payload must satisfy `AuxPow.RoundTripsBase`: its branches and base transaction counts are within `MAX_SIZE`.
The reader returns the base projection: the base-mode encoding drops every witness stack.
`BlockHeader.baseProjection_eq` gives the cases where the projection is the header itself.
-/
theorem BlockHeader.read_encode_base (h : BlockHeader)
    (hflag : h.auxpow.isSome = h.pure.isAuxpow)
    (ha : ∀ a ∈ h.auxpow, a.RoundTripsBase) (rest : List UInt8) :
    BlockHeader.read .base (BlockHeader.encode .base h ++ rest) = .ok (h.baseProjection, rest) := by
  obtain ⟨p, aux⟩ := h
  cases aux with
  | none =>
    have hf : p.isAuxpow = false := by simpa using hflag.symm
    have henc : BlockHeader.encode .base ⟨p, none⟩ = Codec.encode p := by
      simp [BlockHeader.encode]
    rw [henc, BlockHeader.read_encode_flag_clear _ _ hf]
    rfl
  | some a =>
    have hf : p.isAuxpow = true := by simpa using hflag.symm
    unfold BlockHeader.encode BlockHeader.read
    simp only [hf, ↓reduceIte, Option.map_some, Option.getD_some, List.append_assoc]
    rw [readFixed_pure]
    simp only [hf, ↓reduceIte]
    rw [AuxPow.read_encode_base a (ha a rfl)]
    rfl

/-- A transaction without witness data is its own base form: every stack is empty. -/
theorem WitnessTransaction.ofBase_of_hasWitness_false (w : WitnessTransaction)
    (hw : w.hasWitness = false) : WitnessTransaction.ofBase w.tx = w := by
  obtain ⟨tx, ws, hws⟩ := w
  have hrep : ws = List.replicate tx.inputs.val.length WitnessStack.empty := by
    rw [List.eq_replicate_iff]
    refine ⟨hws, fun s hs => ?_⟩
    have := List.any_eq_false.mp hw s hs
    simpa [WitnessStack.isEmpty_iff] using this
  subst hrep
  rfl

/-- A header whose payload, if any, has a transaction without witness data is its own base projection. -/
theorem BlockHeader.baseProjection_eq (h : BlockHeader)
    (hw : ∀ a ∈ h.auxpow, a.tx.hasWitness = false) : h.baseProjection = h := by
  obtain ⟨p, aux⟩ := h
  cases aux with
  | none => rfl
  | some a =>
    simp only [BlockHeader.baseProjection, Option.map_some, AuxPow.baseProjection,
      WitnessTransaction.ofBase_of_hasWitness_false a.tx (hw a rfl)]

/-! ## Prefix extension and truncation -/

/--
A reader *extends to the right* when it leaves appended bytes in the remainder.
For all `bs`, `a`, `rest` and `t`, `r bs = ok (a, rest)` implies `r (bs ++ t) = ok (a, rest ++ t)`.
-/
def ReaderExtends {ε α : Type} (r : List UInt8 → Except ε (α × List UInt8)) : Prop :=
  ∀ bs a rest t, r bs = .ok (a, rest) → r (bs ++ t) = .ok (a, rest ++ t)

/-- A reader that agrees with a lawful codec under any condition extends to the right. -/
theorem readerExtends_of_agrees {α : Type} [c : Codec α] [LawfulCodec α]
    {r : List UInt8 → Except ReadError (α × List UInt8)} {P : α → Prop}
    (h : ReaderAgrees c r P) : ReaderExtends r := by
  intro bs a rest t hr
  obtain ⟨hd, hp⟩ := (h _ _ _).mp hr
  have hbs := LawfulCodec.decode_canonical bs a rest hd
  refine (h _ _ _).mpr ⟨?_, hp⟩
  rw [hbs, List.append_assoc, LawfulCodec.decode_encode]

/-- The element loop of Core's vector reader extends to the right when its element reader does. -/
theorem readElemsBounded_extends {α : Type} {elem : List UInt8 → Except ReadError (α × List UInt8)}
    (h : ReaderExtends elem) (n : Nat) : ReaderExtends (CountedList.readElemsBounded elem n) := by
  induction n with
  | zero =>
    intro bs a rest t hr
    simp only [CountedList.readElemsBounded, Except.ok.injEq, Prod.mk.injEq] at hr ⊢
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro bs a rest t hr
    unfold CountedList.readElemsBounded at hr ⊢
    split at hr
    · cases hr
    · next x r1 hx =>
      rw [h _ _ _ _ hx]
      simp only
      split at hr
      · cases hr
      · next xs r2 hxs =>
        rw [ih _ _ _ _ hxs]
        cases hr
        rfl

/-- `readSections` extends to the right. -/
theorem readSections_extends : ReaderExtends readSections := by
  have hin := (readerExtends_of_agrees (CountedList.decodeBounded_agrees TxIn.read_agrees))
  have hout := (readerExtends_of_agrees (CountedList.decodeBounded_agrees TxOut.read_agrees))
  have hbyte := (readerExtends_of_agrees CountedList.readByte_agrees)
  have hpair := (readerExtends_of_agrees (readPair_agrees (CountedList.decodeBounded_agrees TxIn.read_agrees)
    (CountedList.decodeBounded_agrees TxOut.read_agrees)))
  intro bs a rest t hr
  unfold readSections at hr ⊢
  split at hr
  · cases hr
  · next vin r1 hvin =>
    rw [hin _ _ _ _ hvin]
    simp only
    split at hr
    · next hemp =>
      simp only [hemp, ↓reduceIte]
      split at hr
      · cases hr
      · next flags r2 hf =>
        rw [hbyte _ _ _ _ hf]
        simp only
        split at hr
        · next hz =>
          cases hr
          simp [hz]
        · next hz =>
          simp only [hz, ↓reduceIte]
          split at hr
          · cases hr
          · next vin' vout r3 hp =>
            rw [hpair _ _ _ _ hp]
            cases hr
            rfl
    · next hemp =>
      simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      split at hr
      · cases hr
      · next vout r2 hv =>
        rw [hout _ _ _ _ hv]
        cases hr
        rfl

/-- `readStacks` extends to the right, for each flag and number of inputs. -/
theorem readStacks_extends (flag : Bool) (n : Nat) : ReaderExtends (readStacks flag n) := by
  intro bs a rest t hr
  unfold readStacks at hr ⊢
  split at hr
  · next hflag =>
    simp only [hflag, ↓reduceIte, CountedList.readElemsBoundedLoop_nil] at hr ⊢
    exact readElemsBounded_extends (readerExtends_of_agrees WitnessStack.read_agrees) n _ _ _ _ hr
  · next hflag =>
    simp only [hflag, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hr ⊢
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, rfl⟩

/-- Core's reader of the witness-allowed format extends to the right. -/
theorem readAllowWitness_extends : ReaderExtends Transaction.readAllowWitness := by
  have hfix := (readerExtends_of_agrees (readFixed_agrees (α := UInt32)))
  intro bs a rest t hr
  unfold Transaction.readAllowWitness at hr ⊢
  split at hr
  · cases hr
  · next v r1 hv =>
    rw [hfix _ _ _ _ hv]
    simp only
    split at hr
    · cases hr
    · next flags vin vout r2 hs =>
      rw [readSections_extends _ _ _ _ hs]
      simp only
      split at hr
      · cases hr
      · next stacks r3 hst =>
        rw [readStacks_extends _ _ _ _ _ _ hst]
        simp only
        split at hr
        · cases hr
        · next hfl =>
          simp only [hfl, ↓reduceIte]
          split at hr
          · cases hr
          · next l r4 hl =>
            rw [hfix _ _ _ _ hl]
            simp only at hr ⊢
            split at hr
            · next hlen =>
              cases hr
              simp [hlen]
            · cases hr

/-- The reader of the embedded transaction extends to the right in each mode. -/
theorem readTx_extends (mode : TxReadMode) : ReaderExtends (readTx mode) := by
  cases mode with
  | allowWitness => exact readAllowWitness_extends
  | base =>
    intro bs a rest t hr
    simp only [readTx] at hr ⊢
    split at hr
    · cases hr
    · next tx r1 htx =>
      rw [(readerExtends_of_agrees Transaction.readBase_agrees) _ _ _ _ htx]
      cases hr
      rfl

/-- The reader of the payload fields after the transaction extends to the right. -/
theorem AuxPow.readTail_extends : ReaderExtends AuxPow.readTail :=
  (readerExtends_of_agrees (readPair_agrees (readFixed_agrees (α := Hash256))
    (readPair_agrees readHashes_agrees
      (readPair_agrees (readFixed_agrees (α := UInt32))
        (readPair_agrees readHashes_agrees
          (readPair_agrees (readFixed_agrees (α := UInt32))
            (readFixed_agrees (α := PureBlockHeader))))))))

/-- The payload reader extends to the right in each mode. -/
theorem AuxPow.read_extends (mode : TxReadMode) : ReaderExtends (AuxPow.read mode) := by
  intro bs a rest t hr
  unfold AuxPow.read at hr ⊢
  split at hr
  · cases hr
  · next tx r1 htx =>
    rw [readTx_extends mode _ _ _ _ htx]
    simp only
    split at hr
    · cases hr
    · next tl r2 htl =>
      rw [AuxPow.readTail_extends _ _ _ _ htl]
      cases hr
      rfl

/--
The full header reader extends to the right in each mode.
For every input `bs` that it accepts with remainder `rest`, it accepts `bs ++ t` with the same header and remainder `rest ++ t`.
-/
theorem BlockHeader.read_extends (mode : TxReadMode) : ReaderExtends (BlockHeader.read mode) := by
  have hfix := (readerExtends_of_agrees (readFixed_agrees (α := PureBlockHeader)))
  intro bs a rest t hr
  unfold BlockHeader.read at hr ⊢
  split at hr
  · cases hr
  · next p r1 hp =>
    rw [hfix _ _ _ _ hp]
    simp only
    split at hr
    · next hflag =>
      simp only [hflag, ↓reduceIte]
      split at hr
      · cases hr
      · next aux r2 ha =>
        rw [AuxPow.read_extends mode _ _ _ _ ha]
        cases hr
        rfl
    · next hflag =>
      simp only [hflag, Bool.false_eq_true, ↓reduceIte]
      cases hr
      rfl

/--
A reader that extends to the right rejects every proper prefix of an input that it reads with an empty remainder.
If `r bs = ok (a, [])` and `k < bs.length`, then `r (bs.take k)` is an error.
-/
theorem ReaderExtends.take_error {ε α : Type} {r : List UInt8 → Except ε (α × List UInt8)}
    (h : ReaderExtends r) (bs : List UInt8) (a : α) (hr : r bs = .ok (a, [])) (k : Nat)
    (hk : k < bs.length) : ∀ x, r (bs.take k) ≠ .ok x := by
  intro ⟨a', rest'⟩ hp
  have he := h _ _ _ (bs.drop k) hp
  rw [List.take_append_drop, hr] at he
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  have hlen := congrArg List.length he.2
  simp only [List.length_nil, List.length_append, List.length_drop] at hlen
  omega

/--
Truncation in the witness-allowed mode: under the hypotheses of `BlockHeader.read_encode_allowWitness`, the reader rejects every proper prefix of the encoding of `h`.
-/
theorem BlockHeader.read_take_encode_allowWitness (h : BlockHeader)
    (hflag : h.auxpow.isSome = h.pure.isAuxpow)
    (ha : ∀ a ∈ h.auxpow, a.RoundTripsAllowWitness) (k : Nat)
    (hk : k < (BlockHeader.encode .allowWitness h).length) :
    ∀ x, BlockHeader.read .allowWitness ((BlockHeader.encode .allowWitness h).take k) ≠ .ok x := by
  have hr := BlockHeader.read_encode_allowWitness h hflag ha []
  rw [List.append_nil] at hr
  exact (BlockHeader.read_extends .allowWitness).take_error _ _ hr k hk

/--
Truncation in base mode: under the hypotheses of `BlockHeader.read_encode_base`, the reader rejects every proper prefix of the base-mode encoding of `h`.
-/
theorem BlockHeader.read_take_encode_base (h : BlockHeader)
    (hflag : h.auxpow.isSome = h.pure.isAuxpow)
    (ha : ∀ a ∈ h.auxpow, a.RoundTripsBase) (k : Nat)
    (hk : k < (BlockHeader.encode .base h).length) :
    ∀ x, BlockHeader.read .base ((BlockHeader.encode .base h).take k) ≠ .ok x := by
  have hr := BlockHeader.read_encode_base h hflag ha []
  rw [List.append_nil] at hr
  exact (BlockHeader.read_extends .base).take_error _ _ hr k hk

/-! ## Noncanonical witness encodings -/

/-- A pure header with only the AuxPoW flag set in its version, and every other field zero. -/
def flaggedPureBytes : List UInt8 := [0x00, 0x01, 0x00, 0x00] ++ List.replicate 76 0

/--
The payload fields after the transaction, all zero.
The hash fields and the parent header are zero bytes, both branches are empty, and both indices are 0.
-/
def zeroTailBytes : List UInt8 :=
  List.replicate 32 0 ++ [0x00] ++ [0, 0, 0, 0] ++ [0x00] ++ [0, 0, 0, 0] ++ List.replicate 80 0

/-- A transaction in base form: version 1, one input with a zero outpoint, an empty script and sequence `0xffffffff`, no outputs, lock time 0. -/
def oneInputBaseBytes : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x00] ++ [0, 0, 0, 0]

/-- The same transaction in the extended form with flags `01` and one empty witness stack (`00`). -/
def oneInputExtendedBytes : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x00, 0x01] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++
    [0x00] ++ [0x00] ++ [0, 0, 0, 0]

set_option maxRecDepth 8000 in
/--
Core's acceptance of an extended witness encoding whose stacks are all empty, inside a full header (D4, lines 214 to 243).

Two full headers differ only in the encoding of the embedded transaction: the base form and the extended form with one empty stack.
In the witness-allowed mode the reader accepts both, returns the same header for both, and consumes all of each input.
The two inputs differ in length by three bytes.
-/
theorem extendedEmptyStacks_read :
    ∃ h, BlockHeader.read .allowWitness (flaggedPureBytes ++ oneInputBaseBytes ++ zeroTailBytes) = .ok (h, []) ∧
      BlockHeader.read .allowWitness (flaggedPureBytes ++ oneInputExtendedBytes ++ zeroTailBytes) = .ok (h, []) :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 8000 in
/--
Base mode on the extended encoding of `extendedEmptyStacks_read` (D4, lines 210 to 230).
With `fAllowWitness` false, Core reads the zero byte as an empty input list and goes to the `else` branch at line 229.
It reads no flags byte, and reads the flags byte `01` as an output count.
So the reader accepts a different transaction, with no inputs and one output, and the payload fields that follow come from the wrong bytes.
The read leaves 35 bytes.
-/
theorem extendedEmptyStacks_read_base :
    ∃ h rest, BlockHeader.read .base (flaggedPureBytes ++ oneInputExtendedBytes ++ zeroTailBytes) = .ok (h, rest) ∧
      rest.length = 35 ∧ h.auxpow.map (fun a => (a.tx.tx.inputs.val.length, a.tx.tx.outputs.val.length)) = some (0, 1) :=
  ⟨_, _, rfl, rfl, rfl⟩

end DogeLib.Block
