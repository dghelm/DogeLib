module

public import DogeLib.Exports.Json
public import DogeLib.Block.Check
public import DogeLib.Block.Header
public import DogeLib.Block.Merkle
public import DogeLib.Block.ContextualCheck
public import DogeLib.Block.HeaderSequence
public import DogeLib.Block.Subsidy
public import DogeLib.Transaction.Exports.Oracle
public import DogeLib.Work.Exports.Oracle

/-!
# Block oracle operations

The adapter exposes the pure header codec, block hash and transaction Merkle computation.
SOURCES.md D10, D40 and D42 name the pinned Core functions.
`docs/oracle.md` defines the JSON contract and the Merkle leaf bound.
The full-header operations also expose the AuxPoW and header proof-of-work checks.
`tx.check` and `block.check` expose `checkTransaction` and `checkBlock` (D106), with the legacy count of signature operations.
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

/-- A complete header, or exact pure bytes with an explicit optional payload.
The split form can represent the flag/payload mismatches that a full-header reader excludes. -/
def argPowHeader (fields : Args) (mode : TxReadMode) (bs : List UInt8) : Except Failure BlockHeader := do
  match fields.get? "payload_hex" with
  | none =>
    match BlockHeader.decodeComplete mode bs with
    | .error (.read e) => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .error (.trailingBytes n) =>
      throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n)]))
    | .ok h => return h
  | some payload =>
    unless bs.length == 80 do throw (.request "split bytes_hex must contain exactly 80 bytes")
    let some (pure, _) := Codec.decode (α := PureBlockHeader) bs
      | throw (.request "split bytes_hex must contain exactly 80 bytes")
    if payload == Json.null then return ⟨pure, none⟩
    let raw ← argHex fields "payload_hex"
    match AuxPow.read mode raw with
    | .error e => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .ok (a, rest) =>
      unless rest.isEmpty do
        throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson rest.length)]))
      return ⟨pure, some a⟩

/-- Check complete full-header bytes with the selected network record. -/
def checkPow : Operation where
  name := "block.check_pow"
  args := ["bytes_hex", "mode", "network", "selection_height", "payload_hex"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "bytes_hex"
    let network ← Work.Exports.argNetwork fields
    let height := (← argInt fields "selection_height" 0 2147483647).toNat.toUInt32
    let h ← argPowHeader fields mode bs
    return verdictJson (checkAuxPowProofOfWork (getAuxPowParams network height) h)

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
    return verdictJson (checkVersion (getContextualParams network height).toVersionGateParams h)

/-- Contextual validation on exact pure bytes and an explicit finite node context.
Adapter errors remain separate from the seven Core rejection reasons. -/
def contextualCheck : Operation where
  name := "block.contextual_check"
  args := ["bytes_hex", "network", "chain", "adjusted_time", "checkpoints_enabled", "known_checkpoints"]
  run fields := do
    let bs ← argHex fields "bytes_hex"
    unless bs.length == 80 do throw (.request "bytes_hex must contain exactly 80 bytes")
    let some (header, _) := Codec.decode (α := PureBlockHeader) bs
      | throw (.request "bytes_hex must contain exactly 80 bytes")
    let network ← Work.Exports.argNetwork fields
    let view ← Work.Exports.argView fields
    let time ← argInt fields "adjusted_time" (-9223372036854775808) maxAdjustedTime
    let enabled ← Work.Exports.argBool fields "checkpoints_enabled"
    let .arr entries ← arg fields "known_checkpoints"
      | throw (.request "known_checkpoints must be an array")
    let known ← entries.toList.mapM fun entry => do
      let n ← argInt (Std.TreeMap.Raw.ofList [("height", entry)]) "height" 0 2147483647
      unless (checkpointHeights network).contains n.toNat do
        throw (.request "known checkpoint height is outside the network table")
      return n.toNat
    match contextualCheckBlockHeaderWithCheckpoints network header view (Int64.ofInt time) enabled known with
    | .ok () => return Json.mkObj [("valid", .bool true), ("reject_reason", .null), ("diagnostic", .null)]
    | .error error =>
      if let some reason := error.rejectReason then
        return Json.mkObj [("valid", .bool false), ("reject_reason", .str reason),
          ("diagnostic", .str (reprStr error))]
      else
        match error with
        | .invalidView e | .nextWork e => throw (.spec (Work.Exports.viewErrorJson e))
        | .adjustedTimeOutOfRange => throw (.request "adjusted_time is outside the signed safe range")
        | _ => throw (.spec (Json.mkObj [("kind", .str "work_view"),
            ("reason", .str (if error == .emptyView then "empty_view" else "short_view"))]))

/-- One supplied index entry, with exact pure bytes and explicit node state. -/
def sequenceEntry (json : Json) : Except Failure (Hash256 × IndexEntry) := do
  let .obj fields := json | throw (.request "index entries must be objects")
  for (key, _) in fields do
    unless ["header_hex", "height", "anchor", "failed_valid", "failed_child", "scripts_valid", "chain_work"].contains key do
      throw (.request s!"unknown index field {key}")
  let raw ← argHex fields "header_hex"
  unless raw.length == 80 do throw (.request "header_hex must contain exactly 80 bytes")
  let some (header, _) := Codec.decode (α := PureBlockHeader) raw
    | throw (.request "header_hex must contain exactly 80 bytes")
  let height := (← argInt fields "height" 0 2147483646).toNat
  let anchor ← Work.Exports.argBool fields "anchor"
  let work ← argHex fields "chain_work"
  unless work.length == 32 do throw (.request "chain_work must contain exactly 32 bytes")
  return (header.getHash, ⟨header, height,
    if anchor || height == 0 then none else some header.hashPrevBlock,
    ← Work.Exports.argBool fields "failed_valid", ← Work.Exports.argBool fields "failed_child",
    ← Work.Exports.argBool fields "scripts_valid",
    Work.ArithUint256.ofNat (work.foldl (fun n b => n * 256 + b.toNat) 0)⟩)

/-- The display-order hash used by the sequence interface. -/
def sequenceHash (hash : Hash256) : Json := .str (hexOf hash.displayBytes)

/-- Process full headers against a supplied, checked index, preserving prefix insertions and failure marks. -/
def headerSequence : Operation where
  name := "block.header_sequence"
  args := ["network", "mode", "adjusted_time", "checkpoints_enabled", "index", "failed_blocks", "headers"]
  run fields := do
    let network ← Work.Exports.argNetwork fields
    let mode ← argMode fields
    let time ← argInt fields "adjusted_time" (-9223372036854775808) maxAdjustedTime
    let enabled ← Work.Exports.argBool fields "checkpoints_enabled"
    let .arr entries ← arg fields "index" | throw (.request "index must be an array")
    let .arr failed ← arg fields "failed_blocks" | throw (.request "failed_blocks must be an array")
    let .arr raws ← arg fields "headers" | throw (.request "headers must be an array")
    unless entries.size ≤ 4096 && failed.size ≤ 4096 && raws.size ≤ 4096 do
      throw (.request "sequence arrays must have at most 4096 entries")
    let pairs ← entries.toList.mapM sequenceEntry
    unless (pairs.map Prod.fst).eraseDups.length == pairs.length do
      throw (.request "duplicate index hash")
    let failedHashes ← failed.toList.mapM fun json => do
      let hash ← argHash (Std.TreeMap.Raw.ofList [("hash", json)]) "hash"
      return ⟨hash.val.reverse, by simp [hash.property]⟩
    let index : HeaderIndex := ⟨pairs, failedHashes⟩
    unless checkWellFormed network index do throw (.request "index is not well formed")
    let mut total := 0
    for json in raws do
      let .str raw := json | throw (.request "headers must contain hexadecimal strings")
      unless raw.utf8ByteSize ≤ 2097152 do throw (.request "header exceeds 1 MiB")
      total := total + raw.utf8ByteSize / 2
    unless total ≤ 16777216 do throw (.request "headers exceed 16 MiB")
    let headers ← raws.toList.mapM fun json =>
      argHex (Std.TreeMap.Raw.ofList [("header", json)]) "header"
    let headers ← headers.mapM fun raw => argPowHeader (Std.TreeMap.Raw.ofList ([] : List (String × Json))) mode raw
    let (after, result) := processNewBlockHeaders ⟨network, Int64.ofInt time, enabled⟩ index headers
    let (position, rejection, last, diagnostic) ← match result with
      | .ok last => pure (Json.null, none, last.map sequenceHash |>.getD .null, Json.null)
      | .error error => match error.error with
        | .rejection rejection => pure (natJson error.position, some rejection, Json.null, .str (reprStr error))
        | .adapter error => match error with
          | .contextual (.invalidView e) | .contextual (.nextWork e) =>
            throw (.spec (Work.Exports.viewErrorJson e))
          | .contextual .shortView | .contextual .emptyView =>
            throw (.spec (Json.mkObj [("kind", .str "work_view"), ("reason", .str "short_view")]))
          | _ => throw (.request (reprStr error))
    let added := ((headers.map (fun header => header.pure.getHash)).eraseDups.filter fun hash =>
      (index.lookup hash).isNone).filterMap fun hash => (after.lookup hash).map (hash, ·)
    let marked := match result with
      | .error ⟨position, .rejection (.failedAncestor member)⟩ =>
        match headers[position]? with
        | some header =>
          match after.lookup header.pure.hashPrevBlock with
          | some prev => failedChildPath after (prev.height + 1) header.pure.hashPrevBlock prev member
          | none => []
        | none => []
      | _ => []
    return Json.mkObj [("valid", .bool rejection.isNone), ("failed_at", position),
      ("reject_reason", rejection.map (Json.str ∘ HeaderRejection.rejectReason) |>.getD .null),
      ("dos", rejection.map (natJson ∘ HeaderRejection.dosScore) |>.getD .null),
      ("reject_code", rejection.map (natJson ∘ HeaderRejection.rejectCode) |>.getD .null),
      ("last_hash", last), ("diagnostic", diagnostic),
      ("added", .arr (added.map fun (hash, entry) => Json.mkObj [("hash", sequenceHash hash),
        ("height", natJson entry.height), ("chain_work", .str (Work.Exports.targetHex entry.chainWork))]).toArray),
      ("marked_failed_child", .arr ((marked.map (fun hash => hexOf hash.displayBytes)).eraseDups.mergeSort (· ≤ ·) |>.map Json.str).toArray)]

/-- One case of `block.subsidy`: a height and a previous block hash in internal order. -/
def subsidyCase (json : Json) : Except Failure (Nat × Hash256) := do
  let .obj fields := json | throw (.request "cases must contain objects")
  for (key, _) in fields do
    unless ["height", "prev_hash_hex"].contains key do
      throw (.request s!"unknown case field {key}")
  return ((← argInt fields "height" 0 2147483647).toNat, ← argHash fields "prev_hash_hex")

/--
The mainnet block subsidy of each case, with `subsidyFuel` words of fuel.
`redraws` is a Lean diagnostic, which Core does not report: the number of rejected words, or null from height 145,000, where Core draws no word.
-/
def blockSubsidy : Operation where
  name := "block.subsidy"
  args := ["cases"]
  run fields := do
    let .arr entries ← arg fields "cases" | throw (.request "cases must be an array")
    unless entries.size ≤ 65536 do throw (.request "cases must have at most 65536 entries")
    let mut subsidies := #[]
    let mut redraws := #[]
    for entry in entries do
      let (height, prevHash) ← subsidyCase entry
      match getDogecoinBlockSubsidy subsidyFuel height prevHash with
      | .error .fuelExhausted =>
        throw (.spec (Json.mkObj [("kind", "subsidy"), ("reason", "fuel_exhausted"),
          ("index", natJson subsidies.size)]))
      | .ok subsidy =>
        subsidies := subsidies.push (Json.str (toString subsidy))
        redraws := redraws.push <|
          if mainnetSimplifiedRewards height then Json.null
          else match generateMTRandom (subsidySeed prevHash) (subsidyMaxReward height) subsidyFuel with
            | some draw => natJson draw.redraws
            | none => Json.null
    return Json.mkObj [("subsidies", .arr subsidies), ("redraws", .arr redraws)]

/-- The fields of a verdict of `CheckTransaction` or `CheckBlock`: the reject reason, score and code of Core's `CValidationState`, or nulls. -/
def rejectionFields (rejection : Option (String × Nat × Nat)) : List (String × Json) :=
  [("valid", .bool rejection.isNone),
    ("reject_reason", rejection.map (Json.str ·.1) |>.getD .null),
    ("dos", rejection.map (natJson ·.2.1) |>.getD .null),
    ("reject_code", rejection.map (natJson ·.2.2) |>.getD .null)]

/--
`tx.check`: `checkTransaction` on a transaction that is all of `tx_hex`, read in `mode`.
`legacy_sigops` is `Transaction.getLegacySigOpCount` modulo `2^32`, and `base_size` is the length of the base serialization.
`diagnostic` is the Lean error, which Core does not report.
-/
def txCheck : Operation where
  name := "tx.check"
  args := ["tx_hex", "mode", "check_duplicate_inputs"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "tx_hex"
    let duplicates ← Work.Exports.argBool fields "check_duplicate_inputs"
    match readTx mode bs with
    | .error e => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .ok (w, rest) =>
      unless rest.isEmpty do
        throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson rest.length)]))
      let result := Transaction.checkTransaction w.tx duplicates
      let rejection := match result with
        | .ok () => none
        | .error e => some (e.rejectReason, e.dosScore, e.rejectCode)
      return Json.mkObj (rejectionFields rejection ++
        [("legacy_sigops", natJson (w.tx.getLegacySigOpCount % 2 ^ 32)),
          ("base_size", natJson (Codec.encode w.tx).length),
          ("diagnostic", match result with | .ok () => .null | .error e => .str (reprStr e))])

/--
`block.check`: `checkBlock` on mainnet for a block that is all of `block_hex`, read in `mode`.
`legacy_sigops` is `legacySigOpCount` modulo `2^32`, and `base_size` is `Block.baseSize`.
`diagnostic` is the Lean error, which Core does not report. It names the position of a rejected transaction.
-/
def blockCheck : Operation where
  name := "block.check"
  args := ["block_hex", "mode", "check_pow", "check_merkle_root"]
  run fields := do
    let mode ← argMode fields
    let bs ← argHex fields "block_hex"
    let checkPow ← Work.Exports.argBool fields "check_pow"
    let checkMerkle ← Work.Exports.argBool fields "check_merkle_root"
    match Block.decodeComplete mode bs with
    | .error (.read e) => throw (.spec (Transaction.Exports.witnessReadErrorJson e))
    | .error (.trailingBytes n) =>
      throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n)]))
    | .ok b =>
      let result := checkBlock .mainnet checkPow checkMerkle b
      let rejection := match result with
        | .ok () => none
        | .error e => some (e.rejectReason, e.dosScore, e.rejectCode)
      return Json.mkObj (rejectionFields rejection ++
        [("corruption_possible", match result with
            | .ok () => .null | .error e => .bool e.corruptionPossible),
          ("legacy_sigops", natJson (legacySigOpCount b.transactions % 2 ^ 32)),
          ("base_size", natJson b.baseSize),
          ("transactions", natJson b.vtx.val.length),
          ("diagnostic", match result with | .ok () => .null | .error e => .str (reprStr e))] ++
        hashFields "hash" b.header.pure.getHash)

/-- The block, Merkle, header proof-of-work, subsidy and check operations of the oracle. -/
def operations : List Operation := [readHeader, encodeHeader, hashHeader, computeMerkle,
  scryptHash, readBlockHeader, checkAuxPow, checkPow, checkHeaderVersion, contextualCheck, headerSequence,
  blockSubsidy, txCheck, blockCheck]

end DogeLib.Block.Exports
