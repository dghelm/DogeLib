module

public import DogeLib.Serialization.Proofs.Bytes
public import DogeLib.Serialization.Proofs.CountedList
public import DogeLib.Serialization.Proofs.Reader
public import DogeLib.Transaction.Serialization

/-!
# Proofs: `Transaction.Serialization`

The codec laws of the base serialization, the agreement of the packed codecs, and the contract of Core's base-mode reader.

## Codecs

Each codec is the codec of the tuple of its fields, carried by `Codec.ofEquiv`.
So the laws follow from the laws of the field codecs, by `instLawfulCodecProd` and `LawfulCodec.ofEquiv`, with no other proof.
The same holds for the packed codecs, by `instLawfulPackedCodecProd` and `LawfulPackedCodec.ofEquiv`.

## Core's reader

`Transaction.WithinMaxSize tx` says that each list of `tx` has at most `0x02000000` entries: the inputs, the outputs, and the bytes of each script.
`MAX_SIZE` of Core bounds exactly these counts (SOURCES.md, D1).

- `Transaction.readBase_eq_ok_iff`: for all bytes, `readBase bs = ok (tx, rest)` exactly when the generic codec decodes `bs` as `(tx, rest)` and `tx.WithinMaxSize`.
- `Transaction.readBase_encode`: the round trip of `readBase`, for transactions with `WithinMaxSize`.
- `Transaction.decodeBaseComplete_eq_ok_iff`: the complete reader accepts `tx` exactly when `readBase` reads `tx` with no remainder.

The theorems do not say which error the reader reports on an input that it rejects.
The known answers check the errors and their order on short inputs.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization
open DogeLib.Serialization.CompactSize (ReadError)

/-! ## Codec laws -/

/-- The codec of an outpoint is lawful. -/
instance instLawfulCodecOutPoint : LawfulCodec OutPoint :=
  LawfulCodec.ofEquiv OutPoint.toProd OutPoint.ofProd (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- The codec of a script is lawful. -/
instance instLawfulCodecScript : LawfulCodec Script :=
  LawfulCodec.ofEquiv Script.bytes Script.mk (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- The codec of an input is lawful. -/
instance instLawfulCodecTxIn : LawfulCodec TxIn :=
  LawfulCodec.ofEquiv TxIn.toProd TxIn.ofProd (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- The codec of an output is lawful. -/
instance instLawfulCodecTxOut : LawfulCodec TxOut :=
  LawfulCodec.ofEquiv TxOut.toProd TxOut.ofProd (fun _ => rfl) (fun _ => rfl) _ inferInstance

/-- The codec of the base serialization of a transaction is lawful: round trip and canonicality on every transaction, input and remainder. -/
instance instLawfulCodecTransaction : LawfulCodec Transaction :=
  LawfulCodec.ofEquiv Transaction.toProd Transaction.ofProd (fun _ => rfl) (fun _ => rfl) _
    inferInstance

/-! ## Packed agreement -/

/-- The packed codec of an outpoint agrees with its codec. -/
instance instLawfulPackedCodecOutPoint : LawfulPackedCodec OutPoint :=
  LawfulPackedCodec.ofEquiv OutPoint.toProd OutPoint.ofProd _ _ inferInstance

/-- The packed codec of a script agrees with its codec. -/
instance instLawfulPackedCodecScript : LawfulPackedCodec Script :=
  LawfulPackedCodec.ofEquiv Script.bytes Script.mk _ _ inferInstance

/-- The packed codec of an input agrees with its codec. -/
instance instLawfulPackedCodecTxIn : LawfulPackedCodec TxIn :=
  LawfulPackedCodec.ofEquiv TxIn.toProd TxIn.ofProd _ _ inferInstance

/-- The packed codec of an output agrees with its codec. -/
instance instLawfulPackedCodecTxOut : LawfulPackedCodec TxOut :=
  LawfulPackedCodec.ofEquiv TxOut.toProd TxOut.ofProd _ _ inferInstance

/-- The packed codec of the base serialization of a transaction agrees with its codec. -/
instance instLawfulPackedCodecTransaction : LawfulPackedCodec Transaction :=
  LawfulPackedCodec.ofEquiv Transaction.toProd Transaction.ofProd _ _ inferInstance

/-! ## The bounds of Core's reader -/

/-- A script has at most `0x02000000` bytes, the bound `MAX_SIZE` of Core's reader. -/
def Script.WithinMaxSize (s : Script) : Prop := s.bytes.val.length ≤ 0x02000000

/-- The script of an input is within `MAX_SIZE`. -/
def TxIn.WithinMaxSize (i : TxIn) : Prop := i.scriptSig.WithinMaxSize

/-- The script of an output is within `MAX_SIZE`. -/
def TxOut.WithinMaxSize (o : TxOut) : Prop := o.scriptPubKey.WithinMaxSize

/--
Every count of the transaction is within `MAX_SIZE = 0x02000000`:
the number of inputs, the number of outputs, and the number of bytes of each script.
-/
def Transaction.WithinMaxSize (tx : Transaction) : Prop :=
  tx.inputs.val.length ≤ 0x02000000 ∧ (∀ i ∈ tx.inputs.val, i.WithinMaxSize) ∧
    tx.outputs.val.length ≤ 0x02000000 ∧ ∀ o ∈ tx.outputs.val, o.WithinMaxSize

/-- A transaction within `MAX_SIZE` has fewer than 2^32 inputs. -/
theorem Transaction.WithinMaxSize.inputs_lt {tx : Transaction}
    (h : tx.WithinMaxSize) : tx.inputs.val.length < 2 ^ 32 := by
  have := h.1
  omega

/-- A transaction within `MAX_SIZE` has fewer than 2^32 outputs. -/
theorem Transaction.WithinMaxSize.outputs_lt {tx : Transaction}
    (h : tx.WithinMaxSize) : tx.outputs.val.length < 2 ^ 32 := by
  have := h.2.2.1
  omega

/-! ## Agreement of the readers -/

/-- `OutPoint.read` agrees with the codec of an outpoint, with no condition. -/
theorem OutPoint.read_agrees : ReaderAgrees instCodecOutPoint OutPoint.read (fun _ => True) :=
  (readMap_agrees OutPoint.toProd OutPoint.ofProd (fun _ => rfl)
    (readPair_agrees readFixed_agrees readFixed_agrees)).congr (fun _ => by simp)

/-- `Script.read` agrees with the codec of a script, under `Script.WithinMaxSize`. -/
theorem Script.read_agrees : ReaderAgrees instCodecScript Script.read Script.WithinMaxSize :=
  (readMap_agrees Script.bytes Script.mk (fun _ => rfl) CountedList.decodeBoundedBytes_agrees).congr
    (fun _ => Iff.rfl)

/-- `TxIn.read` agrees with the codec of an input, under `TxIn.WithinMaxSize`. -/
theorem TxIn.read_agrees : ReaderAgrees instCodecTxIn TxIn.read TxIn.WithinMaxSize :=
  (readMap_agrees TxIn.toProd TxIn.ofProd (fun _ => rfl)
    (readPair_agrees OutPoint.read_agrees (readPair_agrees Script.read_agrees readFixed_agrees))).congr
    (fun _ => by simp [TxIn.WithinMaxSize, TxIn.toProd])

/-- `TxOut.read` agrees with the codec of an output, under `TxOut.WithinMaxSize`. -/
theorem TxOut.read_agrees : ReaderAgrees instCodecTxOut TxOut.read TxOut.WithinMaxSize :=
  (readMap_agrees TxOut.toProd TxOut.ofProd (fun _ => rfl)
    (readPair_agrees readFixed_agrees Script.read_agrees)).congr
    (fun _ => by simp [TxOut.WithinMaxSize, TxOut.toProd])

/-- `Transaction.readBase` agrees with the codec of the base serialization, under `Transaction.WithinMaxSize`. -/
theorem Transaction.readBase_agrees :
    ReaderAgrees instCodecTransaction Transaction.readBase Transaction.WithinMaxSize :=
  (readMap_agrees Transaction.toProd Transaction.ofProd (fun _ => rfl)
    (readPair_agrees readFixed_agrees
      (readPair_agrees (CountedList.decodeBounded_agrees TxIn.read_agrees)
        (readPair_agrees (CountedList.decodeBounded_agrees TxOut.read_agrees)
          readFixed_agrees)))).congr
    (fun _ => by simp [Transaction.WithinMaxSize, Transaction.toProd, and_assoc])

/-! ## The contract of Core's reader -/

/--
The contract of Core's base-mode reader: for all bytes `bs`, transactions `tx` and bytes `rest`,
`Transaction.readBase bs = ok (tx, rest)` exactly when the generic codec decodes `bs` as `(tx, rest)` and every count of `tx` is within `MAX_SIZE`.
-/
theorem Transaction.readBase_eq_ok_iff (bs : List UInt8) (tx : Transaction) (rest : List UInt8) :
    Transaction.readBase bs = .ok (tx, rest) ↔
      Codec.decode bs = some (tx, rest) ∧ tx.WithinMaxSize :=
  Transaction.readBase_agrees bs tx rest

/--
The round trip of Core's base-mode reader: for every transaction `tx` with every count within `MAX_SIZE`, and all bytes `rest`,
`Transaction.readBase (Codec.encode tx ++ rest) = ok (tx, rest)`.
-/
theorem Transaction.readBase_encode (tx : Transaction) (h : tx.WithinMaxSize) (rest : List UInt8) :
    Transaction.readBase (Codec.encode tx ++ rest) = .ok (tx, rest) :=
  (Transaction.readBase_eq_ok_iff _ tx rest).mpr ⟨LawfulCodec.decode_encode tx rest, h⟩

/-- For all bytes `bs`, `decodeBaseComplete bs = ok tx` exactly when `readBase bs = ok (tx, [])`. -/
theorem Transaction.decodeBaseComplete_eq_ok_iff (bs : List UInt8) (tx : Transaction) :
    Transaction.decodeBaseComplete bs = .ok tx ↔ Transaction.readBase bs = .ok (tx, []) := by
  unfold Transaction.decodeBaseComplete
  cases Transaction.readBase bs with
  | error e => simp
  | ok p =>
    obtain ⟨tx', rest⟩ := p
    cases rest with
    | nil => simp
    | cons b t => simp

/--
For every transaction `tx` with every count within `MAX_SIZE`, `decodeBaseComplete (Codec.encode tx) = ok tx`.
-/
theorem Transaction.decodeBaseComplete_encode (tx : Transaction) (h : tx.WithinMaxSize) :
    Transaction.decodeBaseComplete (Codec.encode tx) = .ok tx := by
  rw [Transaction.decodeBaseComplete_eq_ok_iff]
  have := Transaction.readBase_encode tx h []
  rwa [List.append_nil] at this

/-! ## Signed fields -/

/-- The amount of an output is the two's-complement reading of the bits of `value`. -/
theorem TxOut.toInt_amount (o : TxOut) : o.amount.toInt = o.value.toBitVec.toInt := rfl

/-- The signed version is the two's-complement reading of the bits of `version`. -/
theorem Transaction.toInt_signedVersion (tx : Transaction) :
    tx.signedVersion.toInt = tx.version.toBitVec.toInt := rfl

/-- For every slice, `OutPoint.readSlice` preserves the list reader's error, value and remainder bytes. -/
theorem OutPoint.abstractRead_readSlice (s : ByteSlice) :
    abstractRead (OutPoint.readSlice s) = OutPoint.read s.toList := by
  unfold OutPoint.readSlice OutPoint.read
  apply abstractRead_readMapSlice
  exact abstractRead_readPairSlice _ _ _ _ abstractRead_readFixedSlice abstractRead_readFixedSlice

/-- For every slice, `Script.readSlice` preserves the list reader's error, value and remainder bytes. -/
theorem Script.abstractRead_readSlice (s : ByteSlice) :
    abstractRead (Script.readSlice s) = Script.read s.toList := by
  unfold Script.readSlice Script.read
  apply abstractRead_readMapSlice
  exact CountedList.abstractRead_decodeBoundedBytesSlice

/-- For every slice, `TxIn.readSlice` preserves the list reader's error, value and remainder bytes. -/
theorem TxIn.abstractRead_readSlice (s : ByteSlice) :
    abstractRead (TxIn.readSlice s) = TxIn.read s.toList := by
  unfold TxIn.readSlice TxIn.read
  apply abstractRead_readMapSlice
  exact abstractRead_readPairSlice _ _ _ _ OutPoint.abstractRead_readSlice
    (abstractRead_readPairSlice _ _ _ _ Script.abstractRead_readSlice abstractRead_readFixedSlice)

/-- For every slice, `TxOut.readSlice` preserves the list reader's error, value and remainder bytes. -/
theorem TxOut.abstractRead_readSlice (s : ByteSlice) :
    abstractRead (TxOut.readSlice s) = TxOut.read s.toList := by
  unfold TxOut.readSlice TxOut.read
  apply abstractRead_readMapSlice
  exact abstractRead_readPairSlice _ _ _ _ abstractRead_readFixedSlice Script.abstractRead_readSlice

/-- For every slice, `Transaction.readBaseSlice` preserves the list reader's error, value and remainder bytes. -/
theorem Transaction.abstractRead_readBaseSlice (s : ByteSlice) :
    abstractRead (Transaction.readBaseSlice s) = Transaction.readBase s.toList := by
  unfold Transaction.readBaseSlice Transaction.readBase
  apply abstractRead_readMapSlice
  exact abstractRead_readPairSlice _ _ _ _ abstractRead_readFixedSlice
    (abstractRead_readPairSlice _ _ _ _
      (CountedList.abstractRead_decodeBoundedSlice _ _ TxIn.abstractRead_readSlice)
      (abstractRead_readPairSlice _ _ _ _
        (CountedList.abstractRead_decodeBoundedSlice _ _ TxOut.abstractRead_readSlice)
        abstractRead_readFixedSlice))

end DogeLib.Transaction
