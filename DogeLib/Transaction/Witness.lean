module

public import DogeLib.Transaction.Txid

/-!
# `Transaction.Witness`

The witness-allowed serialization format of Dogecoin Core `v1.14.9`: its reader, its writer and the witness hash.

This module models a serialization format that Core's code reads and writes.
It does not model segregated witness as a consensus rule.
At the pinned commit, `IsWitnessEnabled` returns false on every network (`src/validation.cpp`, lines 3002 to 3008, SOURCES.md D36).
`ConnectBlock` uses that function, so it never enables `SCRIPT_VERIFY_WITNESS` (lines 1913 to 1917).
Separately, `ContextualCheckBlock` checks `DEPLOYMENT_SEGWIT` through versionbits directly for witness commitments (lines 3163 to 3181).
Without a checked commitment, it rejects witness data as `unexpected-witness` (lines 3183 to 3187).

The deployment timeout is 0 on main and test, and 999999999999 on regtest (`src/chainparams.cpp`, lines 111, 267 and 408, D9).
Thus main and test reject blocks with witness data.
Regtest's deployment parameters do not enable witness script verification.
No definition here says that a transaction in this format is valid, or that any network accepts it.

## Core's format

`UnserializeTransaction` and `SerializeTransaction` in `src/primitives/transaction.h`, lines 194 to 272 (D4), choose the format by the stream version.
Without `SERIALIZE_TRANSACTION_NO_WITNESS`, the reader allows witness data:

- It reads the version, then a list of inputs.
- If the list is empty, it reads a flags byte. If the flags are not zero, it reads the inputs and the outputs.
  If the flags are zero, the transaction has no inputs and no outputs, and Core reads no output count.
- If the list is not empty, it reads the outputs, as in base mode.
- If flag bit 0 is set, it clears the bit and reads one witness stack per input.
- If any flag bit is still set, it fails with "Unknown transaction optional data".
- It reads the lock time.

A witness section of empty stacks is accepted: Core `v1.14.9` has no check for it.
The writer uses the extended form only when some stack is not empty, so such a transaction is written back in the base form.

`Transaction.readBase` is the base-mode reader. `Transaction.Proofs.Witness` relates the two.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization
open CompactSize (ReadError)

/-- The witness of one input: Core's `CScriptWitness::stack`, a vector of byte vectors (`src/script/script.h`, line 651). -/
structure WitnessStack where
  /-- The items of the stack, each a vector of bytes. -/
  items : CountedList (CountedList UInt8)
  deriving DecidableEq

/-- The stack with no items, which Core's `CScriptWitness::IsNull` accepts. -/
def WitnessStack.empty : WitnessStack := ⟨⟨[], by decide⟩⟩

/-- Whether the stack has no items: Core's `CScriptWitness::IsNull`. A stack whose only item is empty is not empty. -/
def WitnessStack.isEmpty (s : WitnessStack) : Bool := s.items.val.isEmpty

/-- The codec of a witness stack: the CompactSize count of items, then each item as a CompactSize length and its bytes. -/
instance instCodecWitnessStack : Codec WitnessStack :=
  Codec.ofEquiv WitnessStack.items WitnessStack.mk inferInstance

/-- Core's read of a witness stack: a vector of byte vectors, each count read with `ReadCompactSize` (D1). -/
def WitnessStack.read : List UInt8 → Except ReadError (WitnessStack × List UInt8) :=
  readMap WitnessStack.mk (CountedList.decodeBounded CountedList.decodeBoundedBytes)

/--
A transaction with the witness stacks of its inputs: the fields of Core's `CTransaction` that the witness-allowed format writes.

Core keeps each stack in its `CTxIn`. Here the stacks are a separate list with one stack per input, which `witnesses_length` requires.
-/
structure WitnessTransaction where
  /-- The fields of the base serialization. -/
  tx : Transaction
  /-- The witness stack of each input, in input order. -/
  witnesses : List WitnessStack
  /-- One stack per input. -/
  witnesses_length : witnesses.length = tx.inputs.val.length

/-- Two values are equal when their transactions and their stacks are equal. -/
instance : DecidableEq WitnessTransaction := fun a b =>
  if h : a.tx = b.tx ∧ a.witnesses = b.witnesses then
    .isTrue (by cases a; cases b; cases h.1; cases h.2; rfl)
  else
    .isFalse (by intro e; cases e; exact h ⟨rfl, rfl⟩)

/-- A transaction with an empty stack for each input, as Core reads it from the base format. -/
def WitnessTransaction.ofBase (tx : Transaction) : WitnessTransaction :=
  ⟨tx, List.replicate tx.inputs.val.length WitnessStack.empty, List.length_replicate⟩

/-- Whether some input has a stack that is not empty: Core's `CTransaction::HasWitness` (D4, lines 371 to 379). -/
def WitnessTransaction.hasWitness (w : WitnessTransaction) : Bool :=
  w.witnesses.any (fun s => !s.isEmpty)

/-- The reasons that `Transaction.readAllowWitness` rejects an input. -/
inductive WitnessReadError where
  /-- A field of the stream fails to read, as in base mode. -/
  | read (e : ReadError)
  /-- A flag bit other than bit 0 is set: Core's "Unknown transaction optional data". -/
  | unknownOptionalData
  deriving DecidableEq, Repr

/--
The sections that follow the version: the flags, the inputs, the outputs and the remainder.

These sections follow Core's branch on the first input count (D4, lines 219 to 230).
After an empty input list it reads the flags byte. Non-zero flags are followed by the inputs and the outputs.
Zero flags end the sections, with no inputs and no outputs.
-/
def readSections (bs : List UInt8) :
    Except ReadError ((UInt8 × CountedList TxIn × CountedList TxOut) × List UInt8) :=
  match CountedList.decodeBounded TxIn.read bs with
  | .error e => .error e
  | .ok (vin, rest) =>
    if vin.val.isEmpty then
      match CountedList.readByte rest with
      | .error e => .error e
      | .ok (flags, rest') =>
        if flags = 0 then .ok ((0, vin, ⟨[], by decide⟩), rest')
        else
          match readPair (CountedList.decodeBounded TxIn.read) (CountedList.decodeBounded TxOut.read) rest' with
          | .error e => .error e
          | .ok ((vin', vout), rest'') => .ok ((flags, vin', vout), rest'')
    else
      match CountedList.decodeBounded TxOut.read rest with
      | .error e => .error e
      | .ok (vout, rest') => .ok ((0, vin, vout), rest')

/--
The witness stacks of `n` inputs: one stack each when flag bit 0 is set, else `n` empty stacks and no bytes read (D4, lines 231 to 237).
-/
def readStacks (witnessFlag : Bool) (n : Nat) (bs : List UInt8) :
    Except ReadError (List WitnessStack × List UInt8) :=
  if witnessFlag then CountedList.readElemsBoundedLoop WitnessStack.read n bs #[]
  else .ok (List.replicate n WitnessStack.empty, bs)

/--
Dogecoin Core's reader of a transaction with witness data allowed: `UnserializeTransaction` of `src/primitives/transaction.h`, lines 210 to 243 (D4), for a stream without `SERIALIZE_TRANSACTION_NO_WITNESS`.

It reads the version, the sections of `readSections`, the witness stacks of `readStacks`, checks the flags, and reads the lock time, in this order.
The result is the first error in this order. So `unknownOptionalData` comes after every list and stack is read, and before the lock time.

It models the serialization format only.
Core rejects blocks with witness data on main and test at the pin (see the module documentation for the separate consensus mechanisms).

The last check, that the reader found one stack per input, never fails: `readStacks` returns `n` stacks for `n` inputs.
If it failed, the result would be `tooLarge`.

It reads a prefix of the input and returns the remainder. `decodeAllowWitnessComplete` requires an empty remainder.
-/
def Transaction.readAllowWitness (bs : List UInt8) :
    Except WitnessReadError (WitnessTransaction × List UInt8) :=
  match readFixed (α := UInt32) bs with
  | .error e => .error (.read e)
  | .ok (version, r1) =>
    match readSections r1 with
    | .error e => .error (.read e)
    | .ok ((flags, vin, vout), r2) =>
      match readStacks (flags &&& 1 = 1) vin.val.length r2 with
      | .error e => .error (.read e)
      | .ok (stacks, r3) =>
        if flags &&& 0xfe ≠ 0 then .error .unknownOptionalData
        else
          match readFixed (α := UInt32) r3 with
          | .error e => .error (.read e)
          | .ok (lockTime, r4) =>
            let tx : Transaction := ⟨version, vin, vout, lockTime⟩
            if h : stacks.length = tx.inputs.val.length then .ok (⟨tx, stacks, h⟩, r4)
            else .error (.read .tooLarge)

/-- The reasons that `decodeAllowWitnessComplete` rejects an input. -/
inductive CompleteWitnessReadError where
  /-- `Transaction.readAllowWitness` rejects the input with this error. -/
  | read (e : WitnessReadError)
  /-- The input has this many bytes after the transaction. -/
  | trailingBytes (count : Nat)
  deriving DecidableEq, Repr

/-- A transaction in the witness-allowed format that is the whole input: `readAllowWitness`, then a check that no bytes remain. -/
def Transaction.decodeAllowWitnessComplete (bs : List UInt8) :
    Except CompleteWitnessReadError WitnessTransaction :=
  match Transaction.readAllowWitness bs with
  | .error e => .error (.read e)
  | .ok (w, []) => .ok w
  | .ok (_, rest) => .error (.trailingBytes rest.length)

/--
Core's writer with witness data allowed: `SerializeTransaction` (D4, lines 245 to 272), for a stream without `SERIALIZE_TRANSACTION_NO_WITNESS`.

When `hasWitness` holds, it writes the extended form.
That is the version, an empty input list (`00`) and the flags byte `01`.
The inputs, the outputs, the stack of each input and the lock time follow.
Otherwise it writes the base serialization, `Codec.encode w.tx`.
-/
def WitnessTransaction.encode (w : WitnessTransaction) : List UInt8 :=
  if w.hasWitness then
    Codec.encode w.tx.version ++ [0x00, 0x01] ++ Codec.encode w.tx.inputs ++ Codec.encode w.tx.outputs ++
      CountedList.encodeElems w.witnesses ++ Codec.encode w.tx.lockTime
  else Codec.encode w.tx

/--
The witness hash: Core's `CTransaction::GetWitnessHash` (D23, `src/primitives/transaction.cpp` lines 70 to 76).
Without witness data it is the transaction ID. Otherwise it is the double SHA-256 of `encode`, the witness-allowed serialization.
For a default-constructed `CTransaction()`, Core returns the cached zero hash, and this definition returns the computed digest (see `Transaction.txid`).
-/
def WitnessTransaction.wtxid (w : WitnessTransaction) : Hash256 :=
  if w.hasWitness then digestToHash256 (Cryptography.Hash.Sha256d.hash (w.encode).toByteArray)
  else w.tx.txid

end DogeLib.Transaction
