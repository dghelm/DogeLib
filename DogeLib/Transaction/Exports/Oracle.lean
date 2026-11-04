module

public import DogeLib.Serialization.Exports.Oracle
public import DogeLib.Transaction.LegacySighash
public import DogeLib.Transaction.Witness

/-!
# `Transaction.Exports.Oracle`

The transaction and signature-hash operations of the oracle. `docs/oracle.md` defines their arguments and results.

- `tx.read_base` runs `Transaction.readBaseSlice`, the prefix reader of Core's base mode.
- `tx.decode_base` runs `Transaction.decodeBaseCompleteSlice`, then the base encoder and `Transaction.txid`.
- `tx.read_witness` and `tx.decode_witness` run the witness-allowed readers, writer and hashes.
- `sighash.legacy` reads its transaction with `decodeBaseCompleteSlice`, then runs `legacySignatureHashPlan` and `LegacyHashPlan.digest`.

The witness operations use list readers and model serialization only.
Core rejects blocks with witness data on main and test at the pin (SOURCES.md D36).
-/

@[expose] public section

namespace DogeLib.Transaction.Exports

open Lean (Json)
open DogeLib.Exports
open DogeLib.Serialization
open DogeLib.Serialization.Exports (readErrorJson)

/-- The JSON object of an outpoint. -/
def outPointJson (o : OutPoint) : Json :=
  Json.mkObj (hashFields "hash" o.hash ++ [("n", natJson o.n.toNat)])

/-- The JSON object of an input. -/
def txInJson (i : TxIn) : Json :=
  Json.mkObj [("prevout", outPointJson i.prevout), ("script_sig_hex", .str (hexOf i.scriptSig.bytes.val)),
    ("sequence", natJson i.sequence.toNat)]

/-- The JSON object of an output. -/
def txOutJson (o : TxOut) : Json :=
  Json.mkObj [("value", u64Json o.value), ("script_pubkey_hex", .str (hexOf o.scriptPubKey.bytes.val))]

/-- The JSON object of a transaction, with every field as it was read. -/
def transactionJson (tx : Transaction) : Json :=
  Json.mkObj [("version", natJson tx.version.toNat),
    ("inputs", .arr (tx.inputs.val.map txInJson).toArray),
    ("outputs", .arr (tx.outputs.val.map txOutJson).toArray),
    ("lock_time", natJson tx.lockTime.toNat)]

/-- The `error` object of a failure of `decodeBaseComplete`. -/
def completeReadErrorJson : CompleteReadError → Json
  | .read e => readErrorJson e
  | .trailingBytes n => Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n)]

/-- `tx.read_base`: the transaction at the start of `bytes_hex`, the count of bytes read, and the remainder. -/
def txReadBase : Operation where
  name := "tx.read_base"
  args := ["bytes_hex"]
  run args := do
    let bs := (ByteArray.mk (← argHex args "bytes_hex").toArray).toByteSlice
    match Transaction.readBaseSlice bs with
    | .error e => throw (.spec (readErrorJson e))
    | .ok (tx, rest) =>
      return Json.mkObj [("tx", transactionJson tx), ("consumed", natJson (bs.size - rest.size)),
        ("rest_hex", .str (hexOf rest.toList))]

/-- `tx.decode_base`: the transaction that is all of `bytes_hex`, its base serialization and its ID. -/
def txDecodeBase : Operation where
  name := "tx.decode_base"
  args := ["bytes_hex"]
  run args := do
    let bs := (ByteArray.mk (← argHex args "bytes_hex").toArray).toByteSlice
    match Transaction.decodeBaseCompleteSlice bs with
    | .error e => throw (.spec (completeReadErrorJson e))
    | .ok tx =>
      return Json.mkObj ([("tx", transactionJson tx), ("serialized_hex", .str (hexOf (Codec.encode tx)))] ++
        hashFields "txid" tx.txid)

/-- The read error of the witness-allowed format, including unknown optional data. -/
def witnessReadErrorJson : WitnessReadError → Json
  | .read e => readErrorJson e
  | .unknownOptionalData => Json.mkObj [("kind", "read"), ("reason", "unknown_optional_data")]

/-- The complete witness reader's error, including trailing bytes. -/
def completeWitnessReadErrorJson : CompleteWitnessReadError → Json
  | .read e => witnessReadErrorJson e
  | .trailingBytes n => Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n)]

/-- The base fields, witness stacks, witness-allowed serialization and both transaction hashes. -/
def witnessFields (w : WitnessTransaction) : List (String × Json) :=
  [("tx", transactionJson w.tx),
    ("witnesses", .arr (w.witnesses.map fun s =>
      Json.arr (s.items.val.map fun i => Json.str (hexOf i.val)).toArray).toArray),
    ("has_witness", .bool w.hasWitness), ("serialized_hex", .str (hexOf w.encode))] ++
    hashFields "txid" w.tx.txid ++ hashFields "wtxid" w.wtxid

/-- `tx.read_witness`: witness-allowed prefix reading, its serialization, hashes, consumed count and remainder. -/
def txReadWitness : Operation where
  name := "tx.read_witness"
  args := ["bytes_hex"]
  run args := do
    let bs ← argHex args "bytes_hex"
    match Transaction.readAllowWitness bs with
    | .error e => throw (.spec (witnessReadErrorJson e))
    | .ok (w, rest) =>
      return Json.mkObj (witnessFields w ++ [("consumed", natJson (bs.length - rest.length)),
        ("rest_hex", .str (hexOf rest))])

/-- `tx.decode_witness`: a witness-allowed transaction that fills the input, its serialization and hashes. -/
def txDecodeWitness : Operation where
  name := "tx.decode_witness"
  args := ["bytes_hex"]
  run args := do
    let bs ← argHex args "bytes_hex"
    match Transaction.decodeAllowWitnessComplete bs with
    | .error e => throw (.spec (completeWitnessReadErrorJson e))
    | .ok w => return Json.mkObj (witnessFields w)

/-- `hash_type` as Core's `int nHashType` reaches `SignatureHash`: an integer from -2^31 to 2^32 - 1, modulo 2^32. -/
def argHashType (args : Args) : Except Failure UInt32 := do
  let i ← argInt args "hash_type" (-2 ^ 31) (2 ^ 32 - 1)
  return (i % 2 ^ 32).toNat.toUInt32

/-- `sighash.legacy`: the plan and digest of `SignatureHash` with `SIGVERSION_BASE`. -/
def sighashLegacy : Operation where
  name := "sighash.legacy"
  args := ["tx_hex", "script_code_hex", "input_index", "hash_type"]
  run args := do
    let txBytes := (ByteArray.mk (← argHex args "tx_hex").toArray).toByteSlice
    let codeBytes ← argHex args "script_code_hex"
    let nIn ← argU32 args "input_index"
    let hashType ← argHashType args
    let tx ← match Transaction.decodeBaseCompleteSlice txBytes with
      | .ok tx => pure tx
      | .error e => throw (.spec ((completeReadErrorJson e).setObjVal! "argument" "tx_hex"))
    let some code := CountedList.ofList? codeBytes
      | throw (.request "argument script_code_hex is too long")
    let plan := legacySignatureHashPlan ⟨code⟩ tx nIn hashType
    let planFields : List (String × Json) := match plan with
      | .fixedDigest _ => [("plan", "fixed_digest")]
      | .hashBytes p => [("plan", "hash_bytes"), ("preimage_hex", .str (hexOf p))]
    return Json.mkObj (planFields ++ hashFields "digest" plan.digest)

/-- The operations of this layer. -/
def operations : List Operation := [txReadBase, txDecodeBase, txReadWitness, txDecodeWitness, sighashLegacy]

end DogeLib.Transaction.Exports
