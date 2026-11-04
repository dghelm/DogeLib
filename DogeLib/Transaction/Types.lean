module

public import DogeLib.Base.Bytes
public import DogeLib.Serialization.CountedList

/-!
# `Transaction.Types`

The fields of a Dogecoin transaction, as they are on the wire.

The types follow `COutPoint`, `CTxIn`, `CTxOut` and `CTransaction` of Dogecoin Core `v1.14.9`, `src/primitives/transaction.h` (SOURCES.md, D4).
They keep every field as raw bits, and check nothing.
A value that a later rule rejects, such as a negative amount, is still a value of these types.

| DogeLib | Core | Wire format |
| --- | --- | --- |
| `OutPoint.hash`, `OutPoint.n` | `COutPoint::hash`, `COutPoint::n` | 32 bytes, then 4 little-endian bytes |
| `Script.bytes` | the bytes of `CScript`, a `prevector<28, unsigned char>` | a CompactSize count, then the bytes |
| `TxIn.prevout`, `TxIn.scriptSig`, `TxIn.sequence` | `CTxIn::prevout`, `scriptSig`, `nSequence` | in this order |
| `TxOut.value`, `TxOut.scriptPubKey` | `CTxOut::nValue`, `scriptPubKey` | 8 little-endian bytes, then the script |
| `Transaction.version`, `inputs`, `outputs`, `lockTime` | `nVersion`, `vin`, `vout`, `nLockTime` | in this order, without witness data |

Core declares `nValue` as `CAmount`, which is `int64_t`, and `nVersion` as `int32_t`.
The wire format stores their two's-complement bits.
Here `TxOut.value` and `Transaction.version` are the bits, as `UInt64` and `UInt32`, and `TxOut.amount` and `Transaction.signedVersion` are the signed values.
So a decoder never loses or changes the bits of these fields.

## Source

Adapted from btc-verified, commit `ecf4f0d`: [`BtcVerified/Transaction/OutPoint.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/OutPoint.lean), [`TxIn.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/TxIn.lean), [`TxOut.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/TxOut.lean), [`TxBody.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Transaction/TxBody.lean) and [`BtcVerified/Script/Script.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Script/Script.lean).
Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
These are the changes:

- Upstream names the fields `txid`, `vout`, `scriptSig`, `sequence`, `value`, `scriptPubKey`, `version`, `inputs`, `outputs` and `lockTime`.
  Here the outpoint fields are `hash` and `n`, as in Core, because the hash of an outpoint is a transaction ID only by the rules of a later layer.
- Upstream `TxBody` is the transaction without witness data. Here it is `Transaction`, and this layer has no witness type.
- `OutPoint.null` uses `Hash256.zero`. Upstream uses an `OfNat` literal.
- `TxOut.amount` and `Transaction.signedVersion` are DogeLib's.
- The codecs of the upstream files are in `DogeLib/Transaction/Serialization.lean`.
- The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-- A reference to an output of an earlier transaction: Core's `COutPoint` (D4). -/
structure OutPoint where
  /-- The hash of the transaction that has the output, `COutPoint::hash`. -/
  hash : Hash256
  /-- The index of the output in that transaction, `COutPoint::n`. -/
  n : UInt32
  deriving DecidableEq

/-- The outpoint of a coinbase input: the zero hash and the index `0xffffffff`, as `COutPoint::SetNull` sets them (D4, line 40). -/
def OutPoint.null : OutPoint := ⟨Hash256.zero, 0xffffffff⟩

/--
The bytes of a script, unparsed: Core's `CScript`, serialized as a `prevector<28, unsigned char>` (D4).
The type does not check that the bytes are a valid program.
-/
structure Script where
  /-- The bytes of the script, with their count. -/
  bytes : CountedList UInt8
  deriving DecidableEq

/-- A transaction input: Core's `CTxIn` (D4). -/
structure TxIn where
  /-- The output that the input spends, `CTxIn::prevout`. -/
  prevout : OutPoint
  /-- The script that satisfies the conditions of that output, `CTxIn::scriptSig`. -/
  scriptSig : Script
  /-- The sequence number, `CTxIn::nSequence`. -/
  sequence : UInt32
  deriving DecidableEq

/-- A transaction output: Core's `CTxOut` (D4). -/
structure TxOut where
  /-- The bits of the amount, `CTxOut::nValue`, an `int64_t` in Core. `TxOut.amount` is the signed value. -/
  value : UInt64
  /-- The conditions to spend the output, `CTxOut::scriptPubKey`. -/
  scriptPubKey : Script
  deriving DecidableEq

/-- The amount of an output as Core's `CAmount`: the bits of `value` read as a two's-complement `Int64`. -/
def TxOut.amount (o : TxOut) : Int64 := o.value.toInt64

/-- A transaction without witness data: the fields of Core's `CTransaction` that its base serialization writes (D4). -/
structure Transaction where
  /-- The bits of the version, `CTransaction::nVersion`, an `int32_t` in Core. `Transaction.signedVersion` is the signed value. -/
  version : UInt32
  /-- The inputs, `CTransaction::vin`. -/
  inputs : CountedList TxIn
  /-- The outputs, `CTransaction::vout`. -/
  outputs : CountedList TxOut
  /-- The lock time, `CTransaction::nLockTime`. -/
  lockTime : UInt32
  deriving DecidableEq

/-- The version as Core's `int32_t`: the bits of `version` read as a two's-complement `Int32`. -/
def Transaction.signedVersion (tx : Transaction) : Int32 := tx.version.toInt32

end DogeLib.Transaction
