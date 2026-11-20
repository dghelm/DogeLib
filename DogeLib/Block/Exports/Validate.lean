module

public import DogeLib.Block.Exports.Oracle
public import DogeLib.Block.Validate
public import DogeLib.Block.Proofs.ConnectProperties
public import DogeLib.Script.CoreVerifier

/-!
# The `block.validate` operation

`block.validate` runs `validateBlock` on a range of mainnet blocks, and carries the coin set and the chain view from each accepted block to the next.
`docs/oracle.md` defines the request, the response and the digests.

The request supplies the state before the first block: a chain view, the coins, and the hash of the ancestor at `BIP34Height`.
All three are empty for a range that starts at the genesis block.
A block that the checks reject changes no state, and the next block must again extend the last accepted block.

## Digests

A digest is a chain of double SHA-256 values over tagged coin records.
It starts from 32 zero bytes, and each record replaces the digest `d` with `SHA256d(d ‖ record)`.
A record is one tag byte, the outpoint (36 bytes), the height (4 bytes, little-endian), the coinbase flag (1 byte), and the output as Core serializes a `CTxOut`.
The tag is 0 for a spent coin, 1 for a created coin, and 2 for a member of the whole set.

- The digest of a block's changes visits `ConnectResult.changes` in order.
- The digest of the whole set visits the entries in the order of their transaction IDs as byte strings, and the outputs of an entry by index.

## Total value

Wherever the operation reports the digest of the whole set, it also reports `CoinSet.totalValue` of that set.
That is the sum of the amounts of its coins, the quantity of `chain_issuance_bound`.
-/

@[expose] public section
namespace DogeLib.Block.Exports
open Lean (Json)
open DogeLib.Exports
open DogeLib.Serialization
open DogeLib.Transaction

/-- The first digest of a chain: 32 zero bytes. -/
def digestStart : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- The record of one coin under a tag: the tag, the outpoint, the height, the coinbase flag and the serialized output. -/
def coinRecord (tag : UInt8) (o : OutPoint) (c : Coin) : List UInt8 :=
  tag :: Codec.encode o ++ Codec.encode (UInt32.ofNat c.height) ++ [if c.coinbase then 1 else 0] ++
    Codec.encode c.out

/-- One step of a digest chain: the double SHA-256 of the digest so far and the record. -/
def digestStep (digest : ByteArray) (record : List UInt8) : ByteArray :=
  Cryptography.Hash.Sha256d.hash (digest ++ record.toByteArray)

/-- The digest of the changes of one block, in order. -/
def changesDigest (changes : List CoinChange) : ByteArray :=
  changes.foldl (fun d change => match change with
    | .spent o c => digestStep d (coinRecord 0 o c)
    | .created o c => digestStep d (coinRecord 1 o c)) digestStart

/-- The digest of the whole coin set and the number of its coins, in the order of the keys and then of the outputs. -/
def setDigest (s : CoinSet) : ByteArray × Nat :=
  s.entries.foldl (fun acc _ entry =>
    entry.coins.foldl (fun (d, n) (o, c) => (digestStep d (coinRecord 2 o c), n + 1)) acc) (digestStart, 0)

/-- An error of the adapter of `block.validate` that is not a malformed request. -/
def validateFailure (reason : String) (extra : List (String × Json) := []) : Failure :=
  .spec (Json.mkObj ([("kind", .str "block_validate"), ("reason", .str reason)] ++ extra))

/-- One supplied entry of the coin set: `{txid_hex, coinbase, height, outputs}`, where each output is `{n, value, script_hex}`. -/
def coinEntry (json : Json) : Except Failure TxCoins := do
  let .obj fields := json | throw (.request "coins must contain objects")
  for (key, _) in fields do
    unless ["txid_hex", "coinbase", "height", "outputs"].contains key do
      throw (.request s!"unknown coin field {key}")
  let txid ← argHash fields "txid_hex"
  let coinbase ← Work.Exports.argBool fields "coinbase"
  let height := (← argInt fields "height" 0 2147483646).toNat
  let .arr entries ← arg fields "outputs" | throw (.request "outputs must be an array")
  if entries.isEmpty then throw (.request "a coin entry needs an output")
  let mut outputs : List (Nat × TxOut) := []
  for entry in entries do
    let .obj output := entry | throw (.request "outputs must contain objects")
    for (key, _) in output do
      unless ["n", "value", "script_hex"].contains key do
        throw (.request s!"unknown output field {key}")
    let n := (← argInt output "n" 0 1048575).toNat
    if outputs.any (·.1 == n) then throw (.request "duplicate output index")
    let value ← argU64 output "value"
    -- Design record 0010, section 3: every supplied amount is from 0 to MAX_MONEY.
    unless value.toNat ≤ maxMoney.toNat do throw (validateFailure "coin_value_out_of_range")
    let script ← argHex output "script_hex"
    let some counted := CountedList.ofList? script | throw (.request "script_hex is too long")
    if isUnspendable ⟨counted⟩ then throw (.request "a supplied coin must be spendable")
    outputs := (n, ⟨value, ⟨counted⟩⟩) :: outputs
  let size := outputs.foldl (fun m o => max m (o.1 + 1)) 0
  return ⟨txid, coinbase, height, (List.range size).map fun n => (outputs.find? (·.1 == n)).map (·.2)⟩

/-- The supplied coin set, with each transaction ID at most once. -/
def argCoins (fields : Args) : Except Failure CoinSet := do
  let .arr entries ← arg fields "coins" | throw (.request "coins must be an array")
  let mut set := CoinSet.empty
  for entry in entries do
    let coins ← coinEntry entry
    if (set.accessCoins coins.txid).isSome then throw (.request "duplicate coin transaction ID")
    set := ⟨set.entries.insert (txidKey coins.txid) coins⟩
  return set

/-- A total value as a string of decimal digits. The total can exceed `2^63`, so it is not a JSON number. -/
def valueJson (value : Int) : Json := .str (toString value)

/-- The verdict of one block, with nulls where a field does not apply. `set` is the digest and the total value of the whole set. -/
def blockRecord (height : Nat) (hash : Hash256) (rejection : Option (String × Nat × Nat))
    (changes : Option (List CoinChange)) (set : Option (ByteArray × Int)) (diagnostic : Json) : Json :=
  Json.mkObj ([("height", natJson height)] ++ hashFields "hash" hash ++ rejectionFields rejection ++
    [("changes_digest_hex", changes.map (fun c => Json.str (hexOf (changesDigest c).toList)) |>.getD .null),
      ("spent", changes.map (fun c => natJson (c.filter (· matches .spent ..)).length) |>.getD .null),
      ("created", changes.map (fun c => natJson (c.filter (· matches .created ..)).length) |>.getD .null),
      ("set_digest_hex", set.map (fun d => Json.str (hexOf d.1.toList)) |>.getD .null),
      ("set_value", set.map (fun d => valueJson d.2) |>.getD .null),
      ("diagnostic", diagnostic)])

/-- The interval of the whole-set digest: after each accepted block whose height is a multiple of it (design record 0010, section 5). -/
def setDigestInterval : Nat := 1000

/-- The fixed arguments of a `block.validate` request: the read mode, the two flags and the adjusted time. -/
structure ValidateOptions where
  /-- The read mode of each block. -/
  mode : TxReadMode
  /-- Core's `fCheckPOW`. -/
  checkPow : Bool
  /-- Core's `fCheckMerkleRoot`. -/
  checkMerkle : Bool
  /-- The adjusted time of the header check. -/
  time : Int64

/-- The state that `block.validate` carries from one block of a request to the next. -/
structure ValidateRun where
  /-- The chain view from the last accepted block, newest first. -/
  view : List Work.BlockIndex
  /-- The hash of the ancestor at `BIP34Height`, when the view reaches that height. -/
  ancestor : Option Hash256
  /-- The coin set after the last accepted block. -/
  coins : CoinSet
  /-- The hash that the next block must name as its predecessor, once a block has fixed it. -/
  tip : Option Hash256
  /-- The records of the blocks so far. -/
  records : Array Json
  /-- The position of the block that left the `int64_t` range, which ends the range. -/
  outOfDomain : Option Nat

/-- The options and the first state of a `block.validate` request, from every argument except the blocks. -/
def validateStart (fields : Args) : Except Failure (ValidateOptions × ValidateRun) := do
  let mode ← argMode fields
  let checkPow ← Work.Exports.argBool fields "check_pow"
  let checkMerkle ← Work.Exports.argBool fields "check_merkle_root"
  let time := Int64.ofInt (← argInt fields "adjusted_time" (-9223372036854775808) maxAdjustedTime)
  let view ← Work.Exports.argView fields
  let ancestor ← match ← arg fields "bip34_ancestor_hex" with
    | .null => pure none
    | _ => some <$> argHash fields "bip34_ancestor_hex"
  let aboveBip34 := match view with
    | [] => false
    | prev :: _ => bip34Height ≤ prev.nHeight
  unless ancestor.isSome == aboveBip34 do
    throw (.request "bip34_ancestor_hex must be a hash exactly when the predecessor is at or above height 1034383")
  let coins ← argCoins fields
  return (⟨mode, checkPow, checkMerkle, time⟩, ⟨view, ancestor, coins, none, #[], none⟩)

/--
One block of a `block.validate` request: the bytes `bs` at the position `run.records.size`.
`fileHeight` is the height that a record of `blocks_file` gives, which must be the candidate height.
The result is the next state, in which `outOfDomain` is set when the block ends the range.
-/
def validateStep (options : ValidateOptions) (run : ValidateRun) (bs : List UInt8) (fileHeight : Option Nat := none) :
    Except Failure ValidateRun := do
  let index := run.records.size
  let b ← match Block.decodeComplete options.mode bs with
    | .error (.read e) => throw (.spec ((Transaction.Exports.witnessReadErrorJson e).setObjVal! "index" (natJson index)))
    | .error (.trailingBytes n) =>
      throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n), ("index", natJson index)]))
    | .ok b => pure b
  let hash := b.header.pure.getHash
  let genesis := some hash == genesisHash? .mainnet
  let mut tip := run.tip
  -- A block extends the last accepted block. The first block names the supplied predecessor.
  if genesis then
    unless run.view.isEmpty do throw (validateFailure "genesis_after_start" [("index", natJson index)])
  else
    if run.view.isEmpty then throw (validateFailure "no_predecessor" [("index", natJson index)])
    match tip with
    | none =>
      -- At height 1034383 the predecessor is its own ancestor at that height.
      if run.view.head?.map (·.nHeight) == some bip34Height && run.ancestor != some b.header.pure.hashPrevBlock then
        throw (.request "bip34_ancestor_hex must be the predecessor's hash at height 1034383")
      tip := some b.header.pure.hashPrevBlock
    | some t =>
      unless t == b.header.pure.hashPrevBlock do
        throw (validateFailure "not_linked" [("index", natJson index)])
  let (height, csvActive, segwitActive, prevMtp) ← bodyStates run.view
  if let some h := fileHeight then
    unless h == height do throw (validateFailure "file_height" [("index", natJson index)])
  let ctx : ValidateContext := ⟨run.view, options.time, none, csvActive, segwitActive, prevMtp, run.ancestor⟩
  match validateBlock Script.coreVerifier options.checkPow options.checkMerkle ctx run.coins b with
  | .ok result =>
    let set := if height % setDigestInterval == 0 then
      some ((setDigest result.coins).1, result.coins.totalValue) else none
    return { run with
      coins := result.coins
      view := ⟨height, b.header.pure.nTime, b.header.pure.nBits⟩ :: run.view
      tip := some hash
      ancestor := if height == bip34Height then some hash else run.ancestor
      records := run.records.push (blockRecord height hash none (some result.changes) set .null) }
  | .error e =>
    match e.rejectReason with
    | some reason =>
      return { run with
        tip := tip
        records := run.records.push (blockRecord height hash (some (reason, e.dosScore, e.rejectCode)) none none
          (.str s!"{e.step}: {reprStr e}")) }
    | none =>
      if e == .connect .outOfDomain then return { run with tip := tip, outOfDomain := some index }
      else throw (validateFailure "outside_model" [("index", natJson index), ("detail", .str (reprStr e))])

/-- The `ok` object of a `block.validate` request after its last block. -/
def validateResult (run : ValidateRun) : Json :=
  let (digest, count) := setDigest run.coins
  Json.mkObj [("blocks", .arr run.records), ("out_of_domain_at", (run.outOfDomain.map natJson).getD .null),
    ("set_digest_hex", .str (hexOf digest.toList)), ("set_coins", natJson count),
    ("set_value", valueJson run.coins.totalValue)]

/-- The arguments of `block.validate` that give the state before the first block. -/
def validateStateArgs : List String :=
  ["mode", "check_pow", "check_merkle_root", "adjusted_time", "chain", "bip34_ancestor_hex", "coins"]

/--
`block.validate`: `validateBlock` with `coreVerifier` on each block of `blocks_hex`, in order.
The module documentation and `docs/oracle.md` give the state, the digests and the errors.
Checkpoints are disabled.
A block whose sums leave the `int64_t` range ends the range: the response holds the blocks before it, and `out_of_domain_at` is its position.
A request with `blocks_file` in the place of `blocks_hex` reads a file, so `blockValidateFile` answers it.
-/
def blockValidate : Operation where
  name := "block.validate"
  args := validateStateArgs ++ ["blocks_hex"]
  run fields := do
    let (options, start) ← validateStart fields
    let .arr raws ← arg fields "blocks_hex" | throw (.request "blocks_hex must be an array")
    let mut run := start
    for raw in raws do
      let bs ← argHex (Std.TreeMap.Raw.ofList [("blocks_hex", raw)]) "blocks_hex"
      run ← validateStep options run bs
      if run.outOfDomain.isSome then break
    return validateResult run

/-- The greatest length of a block record in a `blocks.bin` file: Core's `MAX_SIZE`. -/
def maxFileBlockSize : Nat := 0x02000000

/-- Up to `count` bytes of a file. The result is shorter only at the end of the file. -/
def readUpTo (handle : IO.FS.Handle) (count : Nat) : IO ByteArray := do
  let mut bytes := ByteArray.empty
  while bytes.size < count do
    let chunk ← handle.read (count - bytes.size).toUSize
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
  return bytes

/-- A little-endian number of four bytes at `offset`. -/
def fileU32 (bytes : ByteArray) (offset : Nat) : Nat :=
  (List.range 4).foldr (fun i acc => acc * 256 + (bytes.get! (offset + i)).toNat) 0

/--
`block.validate` on the blocks of the file `blocks_file`, in the place of `blocks_hex`.
The file has the format of `blocks.bin` of `scripts/fetch_blocks.py`: for each block the height and the length as 4-byte little-endian integers, then the block.
The function reads one block at a time, so the file can be larger than memory.
Each record's height must be the candidate height.
The other arguments, the state and the response are those of `blockValidate`.
After each accepted block whose height is a multiple of `setDigestInterval`, it writes the height to standard error.
-/
def blockValidateFile (fields : Args) : IO (Except Failure Json) := do
  for (key, _) in fields do
    unless key == "id" || key == "op" || key == "blocks_file" || validateStateArgs.contains key do
      return .error (.request s!"unknown argument {key} for operation block.validate with blocks_file")
  let .ok (.str path) := arg fields "blocks_file" | return .error (.request "blocks_file must be a string")
  let (options, start) ← match validateStart fields with
    | .ok r => pure r
    | .error f => return .error f
  let handle ← try IO.FS.Handle.mk path .read
    catch _ => return .error (validateFailure "file_unreadable")
  let mut run := start
  repeat
    let index := run.records.size
    let head ← try readUpTo handle 8
      catch _ => return .error (validateFailure "file_unreadable")
    if head.isEmpty then break
    if head.size != 8 then return .error (validateFailure "file_truncated" [("index", natJson index)])
    let length := fileU32 head 4
    if length > maxFileBlockSize then return .error (validateFailure "file_record_too_long" [("index", natJson index)])
    let raw ← try readUpTo handle length
      catch _ => return .error (validateFailure "file_unreadable")
    if raw.size != length then return .error (validateFailure "file_truncated" [("index", natJson index)])
    -- The step is the last use of `run`, so that it can change the records and the coin set in place.
    let before := run.view.head?.map (·.nHeight)
    match validateStep options run raw.toList (some (fileU32 head 0)) with
    | .error f => return .error f
    | .ok next =>
      -- An accepted block puts its own height, which is new, at the head of the view.
      if let some entry := next.view.head? then
        if some entry.nHeight != before && entry.nHeight % setDigestInterval == 0 then
          IO.eprintln s!"block.validate: accepted height {entry.nHeight}"
      run := next
    if run.outOfDomain.isSome then break
  return .ok (validateResult run)

end DogeLib.Block.Exports
