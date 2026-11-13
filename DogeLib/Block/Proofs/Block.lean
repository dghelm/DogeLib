module

public import DogeLib.Block.Block
public import DogeLib.Block.Proofs.AuxPow
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the block codec

The theorems relate `Block.read` and `Block.encode` in each read mode.

- `Block.read_encode_allowWitness`: the round trip in the witness-allowed mode.
- `Block.read_encode_base`: the round trip in base mode, which returns the base projection of the block.
- `Block.baseProjection_eq`: a block without witness data is its own base projection.

The round trips are canonicality over encoder output: the reader accepts the encoding of a block and returns that block.
No theorem says that every accepted byte string is the encoding of its result.
In the witness-allowed mode that claim is false, as for the full header (`extendedEmptyStacks_read`).
The theorems do not say which error the reader reports on an input that it rejects.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization
open DogeLib.Transaction
open CompactSize (ReadError)

/-! ## Conditions -/

/--
The conditions of the witness-allowed round trip, for a block `b`.
The header has a payload exactly when its AuxPoW flag is set, and a payload satisfies `AuxPow.RoundTripsAllowWitness`.
The block has at most `MAX_SIZE = 0x02000000` transactions.
Each transaction has its counts within `MAX_SIZE` and the shape of `WitnessTransaction.readAllowWitness_encode`: witness data, or an input, or no output.
-/
def Block.RoundTripsAllowWitness (b : Block) : Prop :=
  b.header.auxpow.isSome = b.header.pure.isAuxpow ∧
    (∀ a ∈ b.header.auxpow, a.RoundTripsAllowWitness) ∧
    b.vtx.val.length ≤ 0x02000000 ∧
    ∀ w ∈ b.vtx.val, w.WithinMaxSize ∧
      (w.hasWitness = true ∨ w.tx.inputs.val ≠ [] ∨ w.tx.outputs.val = [])

/--
The conditions of the base-mode round trip, for a block `b`.
The header has a payload exactly when its AuxPoW flag is set, and a payload satisfies `AuxPow.RoundTripsBase`.
The block has at most `MAX_SIZE` transactions, and the base counts of each transaction are within `MAX_SIZE`.
-/
def Block.RoundTripsBase (b : Block) : Prop :=
  b.header.auxpow.isSome = b.header.pure.isAuxpow ∧
    (∀ a ∈ b.header.auxpow, a.RoundTripsBase) ∧
    b.vtx.val.length ≤ 0x02000000 ∧
    ∀ w ∈ b.vtx.val, w.tx.WithinMaxSize

/-- The block with every witness stack replaced by an empty one, in the header's payload and in each transaction.
A base-mode read of its base-mode encoding returns this block. -/
def Block.baseProjection (b : Block) : Block :=
  ⟨b.header.baseProjection,
    ⟨b.vtx.val.map fun w => WitnessTransaction.ofBase w.tx, by
      rw [List.length_map]; exact b.vtx.property⟩⟩

/-! ## The transaction loop -/

/-- The witness-allowed loop reads back the encodings of `ws`, after the values in `acc`, and leaves `rest`. Each transaction must satisfy the conditions of `WitnessTransaction.readAllowWitness_encode`. -/
theorem readTransactionsLoop_encode_allowWitness (ws : List WitnessTransaction)
    (h : ∀ w ∈ ws, w.WithinMaxSize ∧
      (w.hasWitness = true ∨ w.tx.inputs.val ≠ [] ∨ w.tx.outputs.val = []))
    (rest : List UInt8) (acc : Array WitnessTransaction) :
    readTransactionsLoop .allowWitness ws.length (ws.flatMap (encodeTx .allowWitness) ++ rest) acc =
      .ok (acc.toList ++ ws, rest) := by
  induction ws generalizing acc with
  | nil => simp [readTransactionsLoop]
  | cons w ws ih =>
    have hw := h w (List.mem_cons_self ..)
    simp only [List.length_cons, readTransactionsLoop, List.flatMap_cons, encodeTx, readTx,
      List.append_assoc]
    rw [WitnessTransaction.readAllowWitness_encode w hw.1 hw.2]
    simp only
    have := ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) (acc.push w)
    rw [this]
    simp

/-- The base-mode loop reads back the base encodings of `ws` as transactions with empty stacks, after the values in `acc`, and leaves `rest`. The base counts of each transaction must be within `MAX_SIZE`. -/
theorem readTransactionsLoop_encode_base (ws : List WitnessTransaction)
    (h : ∀ w ∈ ws, w.tx.WithinMaxSize) (rest : List UInt8) (acc : Array WitnessTransaction) :
    readTransactionsLoop .base ws.length (ws.flatMap (encodeTx .base) ++ rest) acc =
      .ok (acc.toList ++ ws.map (fun w => WitnessTransaction.ofBase w.tx), rest) := by
  induction ws generalizing acc with
  | nil => simp [readTransactionsLoop]
  | cons w ws ih =>
    simp only [List.length_cons, readTransactionsLoop, List.flatMap_cons, encodeTx, readTx,
      List.append_assoc]
    rw [Transaction.readBase_encode w.tx (h w (List.mem_cons_self ..))]
    simp only
    have := ih (fun w' hw' => h w' (List.mem_cons_of_mem _ hw')) (acc.push (WitnessTransaction.ofBase w.tx))
    rw [this]
    simp

/-- The count of a list of at most `MAX_SIZE` entries, as the `UInt64` that the writer encodes, is the length of the list. -/
theorem toNat_ofNat_length {α : Type} (l : List α) (h : l.length ≤ 0x02000000) :
    (UInt64.ofNat l.length).toNat = l.length := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The block -/

/--
The round trip of the block codec in the witness-allowed mode, the mode of Core's network and disk paths.
For every block `b` with `Block.RoundTripsAllowWitness` and all bytes `rest`, the reader returns `b` from `Block.encode .allowWitness b ++ rest`, and leaves `rest`.
The theorem is canonicality over encoder output only.
-/
@[theorem_tag property]
theorem Block.read_encode_allowWitness (b : Block) (hb : b.RoundTripsAllowWitness)
    (rest : List UInt8) :
    Block.read .allowWitness (Block.encode .allowWitness b ++ rest) = .ok (b, rest) := by
  obtain ⟨hflag, haux, hlen, htx⟩ := hb
  obtain ⟨header, ⟨txs, htxs⟩⟩ := b
  simp only [Block.read, Block.encode, List.append_assoc]
  rw [BlockHeader.read_encode_allowWitness header hflag haux]
  simp only
  rw [CompactSize.decodeBounded_encode _ (by rw [toNat_ofNat_length txs hlen]; exact hlen)]
  simp only [toNat_ofNat_length txs hlen]
  rw [readTransactionsLoop_encode_allowWitness txs htx]
  simp only [List.nil_append, CountedList.ofList?_eq_some htxs]

/--
The round trip of the block codec in base mode.
For every block `b` with `Block.RoundTripsBase` and all bytes `rest`, the reader returns the base projection of `b` from `Block.encode .base b ++ rest`, and leaves `rest`.
The base-mode encoding drops every witness stack, so the reader cannot return them.
`Block.baseProjection_eq` gives the blocks that are their own base projection.
-/
@[theorem_tag property]
theorem Block.read_encode_base (b : Block) (hb : b.RoundTripsBase) (rest : List UInt8) :
    Block.read .base (Block.encode .base b ++ rest) = .ok (b.baseProjection, rest) := by
  obtain ⟨hflag, haux, hlen, htx⟩ := hb
  obtain ⟨header, ⟨txs, htxs⟩⟩ := b
  simp only [Block.read, Block.encode, List.append_assoc]
  rw [BlockHeader.read_encode_base header hflag haux]
  simp only
  rw [CompactSize.decodeBounded_encode _ (by rw [toNat_ofNat_length txs hlen]; exact hlen)]
  simp only [toNat_ofNat_length txs hlen]
  rw [readTransactionsLoop_encode_base txs htx]
  have hmap : (txs.map fun w => WitnessTransaction.ofBase w.tx).length < 2 ^ 64 := by
    rw [List.length_map]; exact htxs
  simp only [List.nil_append, CountedList.ofList?_eq_some hmap]
  rfl

/-- A block is its own base projection when no transaction has witness data, in the header's payload or in `vtx`. -/
theorem Block.baseProjection_eq (b : Block) (ha : ∀ a ∈ b.header.auxpow, a.tx.hasWitness = false)
    (hw : ∀ w ∈ b.vtx.val, w.hasWitness = false) : b.baseProjection = b := by
  obtain ⟨header, ⟨txs, htxs⟩⟩ := b
  have hmap : (txs.map fun w => WitnessTransaction.ofBase w.tx) = txs := by
    conv => rhs; rw [← List.map_id txs]
    exact List.map_congr_left fun w hmem => WitnessTransaction.ofBase_of_hasWitness_false w (hw w hmem)
  simp only [Block.baseProjection, BlockHeader.baseProjection_eq header ha, hmap]

end DogeLib.Block
