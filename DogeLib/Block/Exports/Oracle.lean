module

public import DogeLib.Exports.Json
public import DogeLib.Block.Header
public import DogeLib.Block.Merkle
public import DogeLib.Block.ProofOfWork
public import DogeLib.Transaction.Exports.Oracle
public import DogeLib.Work.Exports.Oracle

/-!
# Block oracle operations

The adapter exposes the pure header codec, block hash and transaction Merkle computation.
SOURCES.md D10, D40 and D42 name the pinned Core functions.
`docs/oracle.md` defines the JSON contract and the Merkle leaf bound.
The full-header operations also expose the AuxPoW and header proof-of-work checks.
-/

@[expose] public section
namespace DogeLib.Block.Exports
open Lean (Json)
open DogeLib.Exports
open DogeLib.Serialization

/-- Argument `key` as exactly 32 bytes in internal hash order. -/
def argHash (args : Args) (key : String) : Except Failure Hash256 := do
  let bs ← argHex args key
  if h : bs.length = 32 then return ⟨bs, h⟩
  else throw (.request s!"argument {key} must contain exactly 32 bytes")

/-- The six raw fields of a header, with unknown nested fields rejected. -/
def argHeader (args : Args) : Except Failure PureBlockHeader := do
  let .obj fields ← arg args "header" | throw (.request "header must be an object")
  for (key, _) in fields do
    unless ["version", "prev_block_hex", "merkle_root_hex", "time", "bits", "nonce"].contains key do
      throw (.request s!"unknown header field {key}")
  return ⟨← argU32 fields "version", ← argHash fields "prev_block_hex",
    ← argHash fields "merkle_root_hex", ← argU32 fields "time", ← argU32 fields "bits",
    ← argU32 fields "nonce"⟩

/-- Every raw header field, with both hash byte orders and unsigned version bits. -/
def headerJson (h : PureBlockHeader) : Json :=
  Json.mkObj ([("version", natJson h.nVersion.toNat), ("time", natJson h.nTime.toNat),
    ("bits", natJson h.nBits.toNat), ("nonce", natJson h.nNonce.toNat)] ++
    hashFields "prev_block" h.hashPrevBlock ++ hashFields "merkle_root" h.hashMerkleRoot)

/-- Read an 80-byte pure header prefix and preserve all bytes after it. -/
def readHeader : Operation where
  name := "header.read"
  args := ["bytes_hex"]
  run fields := do
    let bs ← argHex fields "bytes_hex"
    match Codec.decode (α := PureBlockHeader) bs with
    | none => throw (.spec (Json.mkObj [("kind", "read"), ("reason", "truncated")]))
    | some (h, rest) => return Json.mkObj [("header", headerJson h),
        ("consumed", natJson (bs.length - rest.length)), ("rest_hex", .str (hexOf rest))]

/-- Serialize the supplied raw fields as exactly 80 pure header bytes. -/
def encodeHeader : Operation where
  name := "header.encode"
  args := ["header"]
  run fields := do
    return Json.mkObj [("bytes_hex", .str (hexOf (Codec.encode (← argHeader fields))))]

/-- Double SHA-256 of the supplied pure header fields, in both byte orders. -/
def hashHeader : Operation where
  name := "header.hash"
  args := ["header"]
  run fields := do
    return Json.mkObj (hashFields "hash" (← argHeader fields).getHash)

/-- Compute a Merkle root and mutation flag for at most 2^31 internal-order leaves. -/
def computeMerkle : Operation where
  name := "merkle.compute"
  args := ["leaves_hex"]
  run fields := do
    let .arr entries ← arg fields "leaves_hex" | throw (.request "leaves_hex must be an array")
    unless entries.size ≤ 2 ^ 31 do throw (.request "leaves_hex must have at most 2^31 entries")
    let leaves ← entries.toList.zipIdx.mapM fun (entry, index) => do
      let key := s!"leaves_hex[{index}]"
      argHash (Std.TreeMap.Raw.ofList [(key, entry)]) key
    let result := computeMerkleRoot leaves
    return Json.mkObj (hashFields "root" result.root ++ [("mutated", .bool result.mutated)])

/-- The explicit transaction mode of a full-header or payload reader. -/
def argMode (fields : Args) : Except Failure TxReadMode := do
  match ← arg fields "mode" with
  | .str "base" => return .base
  | .str "allow_witness" => return .allowWitness
  | _ => throw (.request "mode must be base or allow_witness")

/-- All decoded payload fields, with unsigned bits for the two signed indices. -/
def auxPowJson (a : AuxPow) : Json :=
  Json.mkObj ([("transaction", Json.mkObj (Transaction.Exports.witnessFields a.tx)),
    ("merkle_branch_hex", .arr (a.merkleBranch.val.map (fun h => Json.str (hexOf h.val))).toArray),
    ("index", natJson a.index.toNat),
    ("chain_merkle_branch_hex", .arr (a.chainMerkleBranch.val.map (fun h => Json.str (hexOf h.val))).toArray),
    ("chain_index", natJson a.chainIndex.toNat), ("parent", headerJson a.parentBlock)] ++
    hashFields "hash_block" a.hashBlock)

/-- A decoded full header, with null for an absent payload. -/
def blockHeaderJson (h : BlockHeader) : Json :=
  Json.mkObj [("pure", headerJson h.pure), ("auxpow", h.auxpow.map auxPowJson |>.getD .null)]

/-- Predicate verdict and the separate Lean diagnostic, which is not compared with Core. -/
def verdictJson {ε : Type} [Repr ε] (result : Except ε Unit) : Json :=
  match result with
  | .ok () => Json.mkObj [("valid", .bool true), ("diagnostic", .null)]
  | .error e => Json.mkObj [("valid", .bool false), ("diagnostic", .str (reprStr e))]

/-- Scrypt-1024-1-1-256 of exactly 80 bytes, in output byte order. -/
def scryptHash : Operation where
  name := "scrypt.hash"
  args := ["bytes_hex"]
  run fields := do
    let bs ← argHex fields "bytes_hex"
    let some bytes := Bytes.ofListExact? (n := 80) bs
      | throw (.request "bytes_hex must contain exactly 80 bytes")
    return Json.mkObj [("digest_hex", .str (hexOf (Cryptography.Hash.Scrypt.scrypt_1024_1_1_256 bytes).val))]

/-- Read a full-header prefix with an explicit embedded-transaction mode. -/
def readBlockHeader : Operation where
  name := "block.header.read"
  args := ["bytes_hex", "mode"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "bytes_hex"
    match BlockHeader.read mode bs with
    | .error e => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .ok (h, rest) => return Json.mkObj [("header", blockHeaderJson h),
        ("consumed", natJson (bs.length - rest.length)), ("rest_hex", .str (hexOf rest))]

/-- Check a complete payload against an explicit child hash, chain ID and strictness flag. -/
def checkAuxPow : Operation where
  name := "auxpow.check"
  args := ["bytes_hex", "mode", "hash_hex", "chain_id", "strict_chain_id"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "bytes_hex"
    let hash ← argHash fields "hash_hex"
    let chainId := Int32.ofInt (← argInt fields "chain_id" (-2147483648) 2147483647)
    let strict ← Work.Exports.argBool fields "strict_chain_id"
    match AuxPow.read mode bs with
    | .error e => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .ok (a, rest) =>
      unless rest.isEmpty do
        throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson rest.length)]))
      return verdictJson (a.check hash chainId strict)

/-- Check complete full-header bytes with the selected network record. -/
def checkPow : Operation where
  name := "block.check_pow"
  args := ["bytes_hex", "mode", "network", "selection_height"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "bytes_hex"
    let network ← Work.Exports.argNetwork fields
    let height := (← argInt fields "selection_height" 0 2147483647).toNat.toUInt32
    match BlockHeader.decodeComplete mode bs with
    | .error (.read e) => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .error (.trailingBytes n) =>
      throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n)]))
    | .ok h => return verdictJson (checkAuxPowProofOfWork (getAuxPowParams network height) h)

/-- The activation field selected by network and height in Core's records (SOURCES.md D14). -/
def allowLegacyAt (network : Work.WorkNetwork) (height : UInt32) : Bool :=
  height < match network with
    | .mainnet => 371337
    | .testnet => 158100
    | .regtest => 20

/-- The two version gates on an exact pure header and a selected network record. -/
def checkHeaderVersion : Operation where
  name := "block.check_version"
  args := ["bytes_hex", "network", "selection_height"]
  run fields := do
    let bs ← argHex fields "bytes_hex"
    unless bs.length == 80 do throw (.request "bytes_hex must contain exactly 80 bytes")
    let network ← Work.Exports.argNetwork fields
    let height := (← argInt fields "selection_height" 0 2147483647).toNat.toUInt32
    let some (h, _) := Codec.decode (α := PureBlockHeader) bs
      | throw (.request "bytes_hex must contain exactly 80 bytes")
    return verdictJson (checkVersion ⟨allowLegacyAt network height⟩ h)

/-- The block, Merkle and header proof-of-work operations of the oracle. -/
def operations : List Operation := [readHeader, encodeHeader, hashHeader, computeMerkle,
  scryptHash, readBlockHeader, checkAuxPow, checkPow, checkHeaderVersion]

end DogeLib.Block.Exports
