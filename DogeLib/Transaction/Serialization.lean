module

public import DogeLib.Serialization.Bytes
public import DogeLib.Serialization.CountedList
public import DogeLib.Serialization.Reader
public import DogeLib.Transaction.Types

/-!
# `Transaction.Serialization`

The base serialization of a transaction: the serialization without witness data.

Core writes and reads a transaction with `SerializeTransaction` and `UnserializeTransaction` in `src/primitives/transaction.h` (SOURCES.md, D4).
When the stream version has the flag `SERIALIZE_TRANSACTION_NO_WITNESS`, both functions use the base format:

```text
nVersion    4 bytes, little-endian
vin         CompactSize count, then each input: prevout hash (32), prevout n (4), scriptSig, nSequence (4)
vout        CompactSize count, then each output: nValue (8), scriptPubKey
nLockTime   4 bytes, little-endian
```

A script is a CompactSize count and then its bytes.
This module defines only this format.
Without the flag, Core's reader treats an empty `vin` as a marker, and reads a flags byte after it (D4, lines 218 to 241).
That witness-allowed mode is not defined here.
So a base-mode reader here is not a model of every reader in Core.

This module defines:

- Codecs and packed codecs of `OutPoint`, `Script`, `TxIn`, `TxOut` and `Transaction`.
  Each one is the codec of the tuple of its fields in wire order, carried to the structure by `Codec.ofEquiv`.
- Core's readers in base mode: `OutPoint.read`, `Script.read`, `TxIn.read`, `TxOut.read` and `Transaction.readBase`.
  They read the counts with Core's `ReadCompactSize`, so they reject a count above `MAX_SIZE`.
- `Transaction.decodeBaseComplete`, which also requires that the transaction is the whole input.

`DogeLib.Transaction.Proofs.Serialization` proves the codec laws, the agreement of the packed codecs, and the contract of the readers.

## Source

The codecs and the packed codecs are adapted from btc-verified, commit `ecf4f0d`: `BtcVerified/Transaction/OutPoint.lean`, `TxIn.lean`, `TxOut.lean`, `TxBody.lean` and `BtcVerified/Script/Script.lean`.
Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream transports along Mathlib `Equiv` values such as `OutPoint.equivProd`.
  Here `Codec.ofEquiv` takes the two functions, such as `OutPoint.toProd` and `OutPoint.ofProd`.
- Upstream puts the codec laws in the instances. Here they are in the proof library.
- The namespace, the module header and the doc comments are DogeLib's.

The readers, `CompleteReadError` and `decodeBaseComplete` are DogeLib's.
They follow `UnserializeTransaction` and the `SerializationOp` methods of `COutPoint`, `CTxIn` and `CTxOut` of Dogecoin Core `v1.14.9`, commit `e0a1c15` (D4).
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization
open DogeLib.Serialization.CompactSize (ReadError)

/-! ## Fields in wire order -/

/-- The fields of an outpoint, in wire order. -/
def OutPoint.toProd (o : OutPoint) : Hash256 × UInt32 := (o.hash, o.n)

/-- The outpoint with these fields. -/
def OutPoint.ofProd (p : Hash256 × UInt32) : OutPoint := ⟨p.1, p.2⟩

/-- The fields of an input, in wire order. -/
def TxIn.toProd (i : TxIn) : OutPoint × Script × UInt32 := (i.prevout, i.scriptSig, i.sequence)

/-- The input with these fields. -/
def TxIn.ofProd (p : OutPoint × Script × UInt32) : TxIn := ⟨p.1, p.2.1, p.2.2⟩

/-- The fields of an output, in wire order. -/
def TxOut.toProd (o : TxOut) : UInt64 × Script := (o.value, o.scriptPubKey)

/-- The output with these fields. -/
def TxOut.ofProd (p : UInt64 × Script) : TxOut := ⟨p.1, p.2⟩

/-- The fields of a transaction, in the order of its base serialization. -/
def Transaction.toProd (tx : Transaction) :
    UInt32 × CountedList TxIn × CountedList TxOut × UInt32 :=
  (tx.version, tx.inputs, tx.outputs, tx.lockTime)

/-- The transaction with these fields. -/
def Transaction.ofProd (p : UInt32 × CountedList TxIn × CountedList TxOut × UInt32) :
    Transaction :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩

/-! ## Codecs -/

/-- The codec of an outpoint: the 32 bytes of the hash, then the index as 4 little-endian bytes. -/
instance instCodecOutPoint : Codec OutPoint :=
  Codec.ofEquiv OutPoint.toProd OutPoint.ofProd inferInstance

/-- The codec of a script: the CompactSize count, then the bytes. -/
instance instCodecScript : Codec Script :=
  Codec.ofEquiv Script.bytes Script.mk inferInstance

/-- The codec of an input: the outpoint, the script and the sequence number. -/
instance instCodecTxIn : Codec TxIn :=
  Codec.ofEquiv TxIn.toProd TxIn.ofProd inferInstance

/-- The codec of an output: the bits of the amount as 8 little-endian bytes, then the script. -/
instance instCodecTxOut : Codec TxOut :=
  Codec.ofEquiv TxOut.toProd TxOut.ofProd inferInstance

/--
The codec of the base serialization of a transaction: version, inputs, outputs and lock time.
It reads the counts with the generic `CompactSize.decode`, so it accepts counts above `MAX_SIZE`.
Core's reader is `Transaction.readBase`.
-/
instance instCodecTransaction : Codec Transaction :=
  Codec.ofEquiv Transaction.toProd Transaction.ofProd inferInstance

/-! ## Packed codecs -/

/-- The packed codec of an outpoint, the packed form of `instCodecOutPoint`. -/
instance instPackedCodecOutPoint : PackedCodec OutPoint :=
  PackedCodec.ofEquiv OutPoint.toProd OutPoint.ofProd inferInstance

/-- The packed codec of a script, the packed form of `instCodecScript`. It reads the bytes as one block. -/
instance instPackedCodecScript : PackedCodec Script :=
  PackedCodec.ofEquiv Script.bytes Script.mk inferInstance

/-- The packed codec of an input, the packed form of `instCodecTxIn`. -/
instance instPackedCodecTxIn : PackedCodec TxIn :=
  PackedCodec.ofEquiv TxIn.toProd TxIn.ofProd inferInstance

/-- The packed codec of an output, the packed form of `instCodecTxOut`. -/
instance instPackedCodecTxOut : PackedCodec TxOut :=
  PackedCodec.ofEquiv TxOut.toProd TxOut.ofProd inferInstance

/-- The packed codec of the base serialization of a transaction, the packed form of `instCodecTransaction`. -/
instance instPackedCodecTransaction : PackedCodec Transaction :=
  PackedCodec.ofEquiv Transaction.toProd Transaction.ofProd inferInstance

/-! ## Core's readers, base mode -/

/-- Core's read of an outpoint: `READWRITE(hash)`, then `READWRITE(n)` (D4, lines 36 and 37). Each read fails only with `truncated`. -/
def OutPoint.read : List UInt8 → Except ReadError (OutPoint × List UInt8) :=
  readMap OutPoint.ofProd (readPair readFixed readFixed)

/-- Core's read of a script: a vector of bytes, read by `CountedList.decodeBoundedBytes`. -/
def Script.read : List UInt8 → Except ReadError (Script × List UInt8) :=
  readMap Script.mk CountedList.decodeBoundedBytes

/-- Core's read of an input: the outpoint, the script and `nSequence`, in this order (D4, lines 113 to 115). -/
def TxIn.read : List UInt8 → Except ReadError (TxIn × List UInt8) :=
  readMap TxIn.ofProd (readPair OutPoint.read (readPair Script.read readFixed))

/-- Core's read of an output: `nValue`, then the script (D4, lines 153 and 154). -/
def TxOut.read : List UInt8 → Except ReadError (TxOut × List UInt8) :=
  readMap TxOut.ofProd (readPair readFixed Script.read)

/--
Dogecoin Core's reader of a transaction in base mode: `UnserializeTransaction` of `src/primitives/transaction.h`, lines 210 to 243 (D4), for a stream with `SERIALIZE_TRANSACTION_NO_WITNESS`.

With that flag, `fAllowWitness` is false, so Core reads `nVersion`, `vin`, `vout` and `nLockTime`, in this order, and reads no flags byte.
An empty `vin` is an empty list of inputs.
Each list is read by `CountedList.decodeBounded`, so a count above `MAX_SIZE` is `tooLarge` before any element is read.
The result is the first error in this order.

It reads a prefix of the input and returns the remainder. `decodeBaseComplete` requires an empty remainder.
-/
def Transaction.readBase : List UInt8 → Except ReadError (Transaction × List UInt8) :=
  readMap Transaction.ofProd
    (readPair readFixed
      (readPair (CountedList.decodeBounded TxIn.read)
        (readPair (CountedList.decodeBounded TxOut.read) readFixed)))

/-- The reasons that `decodeBaseComplete` rejects an input. -/
inductive CompleteReadError where
  /-- `Transaction.readBase` rejects the input with this error. -/
  | read (e : ReadError)
  /-- The input has this many bytes after the transaction. -/
  | trailingBytes (count : Nat)
  deriving DecidableEq, Repr

/--
A transaction that is the whole input, in base mode.

It is `Transaction.readBase`, followed by a check that no bytes remain.
A caller that reads a transaction from a field of known length, such as a hexadecimal argument, uses this function.
A caller that reads the next transaction of a block uses the prefix reader `readBase`.
-/
def Transaction.decodeBaseComplete (bs : List UInt8) : Except CompleteReadError Transaction :=
  match Transaction.readBase bs with
  | .error e => .error (.read e)
  | .ok (tx, []) => .ok tx
  | .ok (_, rest) => .error (.trailingBytes rest.length)

end DogeLib.Transaction
