import DogeLib.Block
import KnownAnswers.Serialization
import KnownAnswers.Work

/-!
## Pure headers and Merkle roots

`tests/block/README.md` records fixture provenance and the limits of the independent expectations.
Header hashes use successor fields or independent Python hashlib expectations.
The Merkle vectors transcribe Core's deterministic transaction lists at the pinned revision.
-/
namespace KnownAnswers.Block
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- Parse a display-order hash without padding or truncation. -/
def parseHash (s : String) : Except String Hash256 := do
  let some h := Hash256.ofDisplayBytes? (← parseHex s).toList | throw "expected 32-byte hash"
  return h

/-- Whether `BlockHeader.read mode bs` returns exactly `h` and `rest`. -/
def readsAs (mode : TxReadMode) (bs : List UInt8) (h : BlockHeader) (rest : List UInt8) : Bool :=
  match BlockHeader.read mode bs with
  | .ok (h', rest') => h' == h && rest' == rest
  | .error _ => false

/-- Whether `BlockHeader.read mode bs` fails with `e`. -/
def readFails (mode : TxReadMode) (bs : List UInt8) (e : Transaction.WitnessReadError) : Bool :=
  match BlockHeader.read mode bs with
  | .ok _ => false
  | .error e' => e' == e

/-- Whether `BlockHeader.read mode bs` fails. -/
def readRejects (mode : TxReadMode) (bs : List UInt8) : Bool :=
  match BlockHeader.read mode bs with
  | .ok _ => false
  | .error _ => true

/-- Check pure-header decoding, encoding, hash bytes, all truncated prefixes and an arbitrary suffix. -/
def checkHeader (label : String) (raw : List UInt8) (expected : Hash256) : IO Nat := do
  let some (h, rest) := Codec.decode (α := PureBlockHeader) raw
    | return ← require s!"{label}: decode" false
  let mut failures ← require s!"{label}: exact encoding" (rest.isEmpty && Codec.encode h == raw)
  failures := failures + (← require s!"{label}: 80 bytes" (raw.length == 80))
  failures := failures + (← require s!"{label}: hash" (h.getHash == expected))
  failures := failures + (← require s!"{label}: suffix"
    (Codec.decode (raw ++ [0x42, 0xff]) == some (h, [0x42, 0xff])))
  for n in [:80] do
    failures := failures + (← require s!"{label}: truncated at {n}"
      ((Codec.decode (α := PureBlockHeader) (raw.take n)).isNone))
  if !h.isAuxpow then
    for mode in [TxReadMode.allowWitness, .base] do
      failures := failures + (← require s!"{label}: full header without payload, {repr mode}"
        (readsAs mode (raw ++ [0x42, 0xff]) ⟨h, none⟩ [0x42, 0xff]))
  return failures

/-- Check all 312 recorded mainnet headers against recorded links and the independent final digest. -/
def checkHeaders : IO Nat := do
  let text ← IO.FS.readFile "tests/work/mainnet-headers/headers.txt"
  let records ← match KnownAnswers.Work.MainnetHeaders.parseHeaders text with
    | .ok r => pure r
    | .error e => throw (IO.userError e)
  let last ← match parseHash (← IO.FS.readFile "tests/block/last-header-hash.txt").trimAscii.toString with
    | .ok h => pure h
    | .error e => throw (IO.userError e)
  let lines := (text.splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  for i in [:records.size] do
    let some record := records[i]? | throw (IO.userError "missing header")
    let expected := match records[i+1]? with
      | some next => next.prev
      | none => last
    let some line := lines[i]? | throw (IO.userError s!"missing raw header at index {i}")
    let some hex := (line.splitOn " ")[1]? | throw (IO.userError "bad header line")
    let raw ← match parseHex hex with
      | .ok b => pure b.toList
      | .error e => throw (IO.userError e)
    failures := failures + (← checkHeader s!"height {record.height}" raw expected)
  IO.println s!"pure headers: {records.size} records, 24960 truncated prefixes; {failures} failures"
  return failures

/-- Check real transaction lists against Merkle roots in the fetched raw headers. -/
def checkMainnet : IO Nat := do
  let rows ← match (← jsonFile "tests/block/mainnet.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "three mainnet block fixtures" (rows.size == 3)
  for row in rows do
    let parsed : Except String (Nat × List UInt8 × Hash256 × List Transaction.Transaction × List Hash256) := do
      let height ← (← row.getObjVal? "height").getNat?
      let raw := (← parseHex (← row.getObjValAs? String "header")).toList
      let expected ← parseHash (← row.getObjValAs? String "blockHash")
      let txs ← (← row.getObjVal? "transactions").getArr?
      let ids ← (← row.getObjVal? "txids").getArr?
      let transactions ← txs.toList.mapM fun j => do
        let bytes := (← parseHex (← j.getStr?)).toList
        match Transaction.Transaction.decodeBaseComplete bytes with
        | .ok tx => pure tx
        | .error _ => throw "transaction decode failed"
      let hashes ← ids.toList.mapM fun j => do parseHash (← j.getStr?)
      return (height, raw, expected, transactions, hashes)
    let (height, raw, expected, txs, ids) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    failures := failures + (← checkHeader s!"block {height}" raw expected)
    let some (h, _) := Codec.decode (α := PureBlockHeader) raw
      | throw (IO.userError "pure header decode failed")
    failures := failures + (← require s!"block {height}: transaction IDs" (txs.map (·.txid) == ids))
    failures := failures + (← require s!"block {height}: Merkle root"
      (blockMerkleRoot txs == (⟨h.hashMerkleRoot, false⟩ : MerkleResult)))
  return failures

/-- Check independently computed roots and mutation flags for deterministic Core transaction lists. -/
def checkMerkleVectors : IO Nat := do
  let rows ← match (← jsonFile "tests/block/merkle.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "34 deterministic Merkle vectors" (rows.size == 34)
  for row in rows do
    let parsed : Except String (Nat × Nat × List Hash256 × MerkleResult) := do
      let count ← (← row.getObjVal? "count").getNat?
      let mutation ← (← row.getObjVal? "mutation").getNat?
      let leaves ← (← (← row.getObjVal? "leaves").getArr?).toList.mapM fun j => do
        parseHash (← j.getStr?)
      let root ← parseHash (← row.getObjValAs? String "root")
      let mutated ← row.getObjValAs? Bool "mutated"
      return (count, mutation, leaves, ⟨root, mutated⟩)
    let (count, mutation, leaves, expected) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    failures := failures + (← require s!"Merkle size {count}, mutation {mutation}"
      (computeMerkleRoot leaves == expected))
    let base : List Transaction.Transaction := (List.range count).map fun j =>
      ⟨1, ⟨[], by decide⟩, ⟨[], by decide⟩, j.toUInt32⟩
    let baseHashes := base.map (·.txid)
    let baseRoot := (computeMerkleRoot baseHashes).root
    failures := failures + (← require s!"Merkle size {count}: root unchanged"
      (expected.root == baseRoot))
    failures := failures + (← require s!"Merkle size {count}: mutation flag"
      (expected.mutated == (mutation != 0)))
    let mut rebuilt := baseHashes
    for _ in [:mutation] do
      let mut n := rebuilt.length
      let mut duplicate := 1
      while n > 0 && n % 2 == 0 do
        duplicate := duplicate * 2
        n := n / 2
      if duplicate >= rebuilt.length then
        throw (IO.userError s!"Merkle size {count}: duplication would add a whole tree level")
      rebuilt := rebuilt ++ rebuilt.drop (rebuilt.length - duplicate)
    failures := failures + (← require s!"Merkle size {count}, mutation {mutation}: reconstructed leaves"
      (rebuilt == leaves))
  return failures

/-- One recorded AuxPoW payload: the fields that the independent importer parsed and checked against Blockchair's decoded JSON. -/
structure PayloadRecord where
  txHex : List UInt8
  txid : Hash256
  hashBlock : List UInt8
  merkleBranch : List (List UInt8)
  index : Int
  chainMerkleBranch : List (List UInt8)
  chainIndex : Int
  parentBlock : List UInt8

/-- Parse the `payload` object of an AuxPoW header record. -/
def parsePayload (j : Lean.Json) : Except String PayloadRecord := do
  let hexField (k : String) : Except String (List UInt8) := do
    return (← parseHex (← j.getObjValAs? String k)).toList
  let hexList (k : String) : Except String (List (List UInt8)) := do
    (← (← j.getObjVal? k).getArr?).toList.mapM fun e => do return (← parseHex (← e.getStr?)).toList
  return {
    txHex := ← hexField "txHex", txid := ← parseHash (← j.getObjValAs? String "txid"),
    hashBlock := ← hexField "hashBlock", merkleBranch := ← hexList "merkleBranch",
    index := ← (← j.getObjVal? "index").getInt?, chainMerkleBranch := ← hexList "chainMerkleBranch",
    chainIndex := ← (← j.getObjVal? "chainIndex").getInt?, parentBlock := ← hexField "parentBlock" }

/--
Check the full mainnet headers of `tests/block/auxpow-headers.json` in both read modes.
Each record is a whole raw block. The test checks the consumed length, the remainder and the payload fields.
It also checks the re-encoding, the checkpoint hash, every proper prefix and the transaction list in the remainder.
-/
def checkAuxPowHeaders : IO Nat := do
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "six AuxPoW header fixtures" (rows.size == 6)
  let mut prefixes := 0
  for row in rows do
    let parsed : Except String (Nat × Hash256 × Bool × Nat × Nat × List UInt8 × PayloadRecord) := do
      let height ← (← row.getObjVal? "height").getNat?
      let hash ← parseHash (← row.getObjValAs? String "blockHash")
      let flag ← row.getObjValAs? Bool "auxpowFlag"
      let len ← (← row.getObjVal? "headerLength").getNat?
      let txCount ← (← row.getObjVal? "txCount").getNat?
      let block := (← parseHex (← row.getObjValAs? String "block")).toList
      let payload ← parsePayload (← row.getObjVal? "payload")
      return (height, hash, flag, len, txCount, block, payload)
    let (height, hash, flag, len, txCount, block, p) ← match parsed with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    let label := s!"AuxPoW header {height}"
    let header := block.take len
    let remainder := block.drop len
    for mode in [TxReadMode.allowWitness, .base] do
      let ml := s!"{label}, {repr mode}"
      match BlockHeader.read mode block with
      | .error _ => failures := failures + (← require s!"{ml}: read" false)
      | .ok (h, rest) =>
        failures := failures + (← require s!"{ml}: remainder" (rest == remainder))
        failures := failures + (← require s!"{ml}: checkpoint hash" (h.pure.getHash == hash))
        failures := failures + (← require s!"{ml}: flag" (h.pure.isAuxpow == flag))
        failures := failures + (← require s!"{ml}: re-encoding" (BlockHeader.encode mode h == header))
        failures := failures + (← require s!"{ml}: complete read"
          (match BlockHeader.decodeComplete mode header with
           | .ok h' => h' == h
           | .error _ => false))
        match h.auxpow with
        | none => failures := failures + (← require s!"{ml}: payload" false)
        | some a =>
          failures := failures + (← require s!"{ml}: transaction bytes"
            (encodeTx .allowWitness a.tx == p.txHex))
          failures := failures + (← require s!"{ml}: no witness data" (!a.tx.hasWitness))
          failures := failures + (← require s!"{ml}: transaction ID" (a.tx.tx.txid == p.txid))
          failures := failures + (← require s!"{ml}: hashBlock" (a.hashBlock.val == p.hashBlock))
          failures := failures + (← require s!"{ml}: coinbase branch"
            (a.merkleBranch.val.map (·.val) == p.merkleBranch))
          failures := failures + (← require s!"{ml}: nIndex" (a.signedIndex.toInt == p.index))
          failures := failures + (← require s!"{ml}: chain branch"
            (a.chainMerkleBranch.val.map (·.val) == p.chainMerkleBranch))
          failures := failures + (← require s!"{ml}: nChainIndex" (a.signedChainIndex.toInt == p.chainIndex))
          failures := failures + (← require s!"{ml}: parent header" (Codec.encode a.parentBlock == p.parentBlock))
        match CountedList.decodeBounded Transaction.Transaction.readBase rest with
        | .ok (txs, []) =>
          failures := failures + (← require s!"{ml}: transaction count" (txs.val.length == txCount))
          failures := failures + (← require s!"{ml}: Merkle root"
            (blockMerkleRoot txs.val == (⟨h.pure.hashMerkleRoot, false⟩ : MerkleResult)))
        | _ => failures := failures + (← require s!"{ml}: transaction list" false)
      for k in [:len] do
        failures := failures + (← require s!"{ml}: truncated at {k}" (readRejects mode (header.take k)))
      prefixes := prefixes + len
  IO.println s!"AuxPoW headers: {rows.size} records, {prefixes} truncated prefixes across both modes"
  return failures

/-- A pure header with only the AuxPoW flag set: version `0x00000100`, every other field zero. -/
def flaggedPure : List UInt8 := [0x00, 0x01, 0x00, 0x00] ++ List.replicate 76 0

/-- A coinbase-shaped transaction in base form: one input with a zero outpoint, an empty script, sequence `0xffffffff`, no outputs. -/
def oneInputTx : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x00] ++ [0, 0, 0, 0]

/-- The same transaction in the extended form, flags `01`, with one empty witness stack. -/
def oneInputTxExtended : List UInt8 :=
  [0x01, 0, 0, 0] ++ [0x00, 0x01] ++ [0x01] ++ List.replicate 36 0 ++ [0x00, 0xff, 0xff, 0xff, 0xff] ++
    [0x00] ++ [0x00] ++ [0, 0, 0, 0]

/-- The payload fields after the transaction, all zero, with empty branches. -/
def zeroTail : List UInt8 :=
  List.replicate 32 0 ++ [0x00] ++ [0, 0, 0, 0] ++ [0x00] ++ [0, 0, 0, 0] ++ List.replicate 80 0

/--
Hand-written full headers, from Core's format (D41, D54, D4): the read mode of the embedded transaction, errors and truncation.
The bytes are written here from the format, not produced by the encoder under test.
-/
def checkAuxPowCases : IO Nat := do
  let base := flaggedPure ++ oneInputTx ++ zeroTail
  let ext := flaggedPure ++ oneInputTxExtended ++ zeroTail
  let mut failures := 0
  -- Both encodings read as one header in the witness-allowed mode, with nothing left over.
  match BlockHeader.read .allowWitness base, BlockHeader.read .allowWitness ext with
  | .ok (h1, []), .ok (h2, []) =>
    failures := failures + (← require "empty stacks: same header" (h1 == h2))
    failures := failures + (← require "empty stacks: writer emits base form"
      (BlockHeader.encode .allowWitness h2 == base))
  | _, _ => failures := failures + (← require "empty stacks: both encodings read" false)
  -- Base mode reads the extended form as a different transaction and leaves 35 bytes.
  failures := failures + (← require "empty stacks: base mode"
    (match BlockHeader.read .base ext with
     | .ok (h, rest) => rest.length == 35 &&
        h.auxpow.map (fun (a : AuxPow) => (a.tx.tx.inputs.val.length, a.tx.tx.outputs.val.length)) == some (0, 1)
     | .error _ => false))
  failures := failures + (← require "base form: base mode" (readsAs .base base
    (match BlockHeader.read .allowWitness base with | .ok (h, _) => h | .error _ => ⟨⟨0, Hash256.zero, Hash256.zero, 0, 0, 0⟩, none⟩) []))
  -- A flag set with only the pure header: the payload read is truncated.
  for mode in [TxReadMode.allowWitness, .base] do
    failures := failures + (← require s!"flag set, no payload, {repr mode}"
      (readFails mode flaggedPure (.read .truncated)))
  -- Flags 02 in the embedded transaction.
  let flags2 := flaggedPure ++ ([0x01, 0, 0, 0, 0x00, 0x02] ++ [0x01] ++ List.replicate 36 0 ++
    [0x00, 0xff, 0xff, 0xff, 0xff] ++ [0x00] ++ [0, 0, 0, 0]) ++ zeroTail
  failures := failures + (← require "flags 02" (readFails .allowWitness flags2 .unknownOptionalData))
  -- A coinbase branch count of MAX_SIZE + 1 (0x02000001), before any hash.
  let tooLarge := flaggedPure ++ oneInputTx ++ List.replicate 32 0 ++ [0xfe, 0x01, 0x00, 0x00, 0x02]
  for mode in [TxReadMode.allowWitness, .base] do
    failures := failures + (← require s!"branch count above MAX_SIZE, {repr mode}"
      (readFails mode tooLarge (.read .tooLarge)))
  -- Every proper prefix of the hand-written headers.
  for (label, bytes, mode) in [("base form", base, TxReadMode.allowWitness), ("base form", base, .base),
      ("extended form", ext, .allowWitness)] do
    for k in [:bytes.length] do
      failures := failures + (← require s!"{label}, {repr mode}: truncated at {k}"
        (readRejects mode (bytes.take k)))
  IO.println s!"AuxPoW hand-written cases: {failures} failures"
  return failures

/-- Check genesis commitments, the AuxPoW bit predicate, and all block fixtures. -/
def check : IO Nat := do
  let mut failures ← checkHeaders
  failures := failures + (← checkMainnet)
  failures := failures + (← checkMerkleVectors)
  failures := failures + (← checkAuxPowHeaders)
  failures := failures + (← checkAuxPowCases)
  let parsed : Except String (PureBlockHeader × Transaction.Transaction × Hash256) := do
    let raw := (← parseHex KnownAnswers.Codec.headerHex).toList
    let some (h, []) := Codec.decode (α := PureBlockHeader) raw | throw "genesis header"
    let tx ← match Transaction.Transaction.decodeBaseComplete (← KnownAnswers.Genesis.coinbase).toList with
      | .ok tx => pure tx
      | .error _ => throw "genesis transaction"
    return (h, tx, ← parseHash "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691")
  let (h, tx, expected) ← match parsed with
    | .ok p => pure p
    | .error e => throw (IO.userError e)
  failures := failures + (← require "genesis header hash" (h.getHash == expected))
  failures := failures + (← require "genesis block Merkle root"
    (blockMerkleRoot [tx] == (⟨h.hashMerkleRoot, false⟩ : MerkleResult)))
  for version in ([0, 1, 255, 256, 257, 511, 512, 0x80000100, 0xffffffff] : List UInt32) do
    failures := failures + (← require s!"AuxPoW flag {version}"
      (({h with nVersion := version}).isAuxpow == (version.toNat / 256 % 2 == 1)))
  failures := failures + (← require "signed version high bit"
    (({h with nVersion := 0x80000100}).signedVersion.toInt == -2147483392))
  failures := failures + (← require "signed version minus one"
    (({h with nVersion := 0xffffffff}).signedVersion.toInt == -1))
  IO.println s!"block known answers: {failures} failures"
  return failures
end KnownAnswers.Block

/-- Named checks for Block known answers, in alphabetical order. -/
def KnownAnswers.Block.checks : List (String × IO Nat) := [
  ("blocks", KnownAnswers.Block.check)
]
