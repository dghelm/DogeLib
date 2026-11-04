module

public import DogeLib.Serialization.Exports.Oracle
public import DogeLib.Transaction.LegacySighash

/-!
# `Transaction.Exports.Oracle`

The transaction and signature-hash operations of the oracle. `docs/oracle.md` defines their arguments and results.

- `tx.read_base` runs `Transaction.readBase`, the prefix reader of Core's base mode.
- `tx.decode_base` runs `Transaction.decodeBaseComplete`, then the base encoder and `Transaction.txid`.
- `sighash.legacy` reads its transaction with `decodeBaseComplete`, then runs `legacySignatureHashPlan` and `LegacyHashPlan.digest`.

These operations model Core's serialization in base mode only. No operation reads witness data.
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
    let bs ← argHex args "bytes_hex"
    match Transaction.readBase bs with
    | .error e => throw (.spec (readErrorJson e))
    | .ok (tx, rest) =>
      return Json.mkObj [("tx", transactionJson tx), ("consumed", natJson (bs.length - rest.length)),
        ("rest_hex", .str (hexOf rest))]

/-- `tx.decode_base`: the transaction that is all of `bytes_hex`, its base serialization and its ID. -/
def txDecodeBase : Operation where
  name := "tx.decode_base"
  args := ["bytes_hex"]
  run args := do
    let bs ← argHex args "bytes_hex"
    match Transaction.decodeBaseComplete bs with
    | .error e => throw (.spec (completeReadErrorJson e))
    | .ok tx =>
      return Json.mkObj ([("tx", transactionJson tx), ("serialized_hex", .str (hexOf (Codec.encode tx)))] ++
        hashFields "txid" tx.txid)

/-- `hash_type` as Core's `int nHashType` reaches `SignatureHash`: an integer from -2^31 to 2^32 - 1, modulo 2^32. -/
def argHashType (args : Args) : Except Failure UInt32 := do
  let i ← argInt args "hash_type" (-2 ^ 31) (2 ^ 32 - 1)
  return (i % 2 ^ 32).toNat.toUInt32

/-- `sighash.legacy`: the plan and digest of `SignatureHash` with `SIGVERSION_BASE`. -/
def sighashLegacy : Operation where
  name := "sighash.legacy"
  args := ["tx_hex", "script_code_hex", "input_index", "hash_type"]
  run args := do
    let txBytes ← argHex args "tx_hex"
    let codeBytes ← argHex args "script_code_hex"
    let nIn ← argU32 args "input_index"
    let hashType ← argHashType args
    let tx ← match Transaction.decodeBaseComplete txBytes with
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
def operations : List Operation := [txReadBase, txDecodeBase, sighashLegacy]

end DogeLib.Transaction.Exports
