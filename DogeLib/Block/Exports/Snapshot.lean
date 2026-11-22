module

public import Std.Data.TreeSet
public import DogeLib.Block.Exports.Validate

/-!
# Coin-set snapshots in `block.validate`

A `block.validate` request with `coins_file` takes the coin set before its first block from a snapshot file, in the place of `coins` (design record 0011, section 3).
`docs/oracle.md` defines the format `dogelib-coins/1`, the request and the errors.

## The format

A snapshot is the coin records of a whole coin set under the tag 2, in the order of the digest of the whole set (`setDigest`).
A record starts with the tag, the outpoint (36 bytes), the height (4 bytes, little-endian) and the coinbase byte.
The amount (8 bytes, little-endian), the CompactSize length of the script and the script follow.
The file has no other framing.
So the digest of the whole set is the digest chain over the records of the file, in the order of the file.

`snapshotHead`, `readSnapshotCoin` and `snapshotOrder` reject each fault of section 3.1 of the design record.

## The restricted run

The oracle does not hold the whole set (section 3.3 of the design record).
`blockValidateSnapshot` works in four steps:

1. It reads the blocks once and collects `T`: the keys of the transaction IDs that the blocks name (`blockKeys`).
2. It reads the snapshot once. It computes the digest of all records, and keeps the coins whose key is in `T`.
3. It runs the blocks on the kept coins, with `validateFileRun`. Before each block, it requires that `T` has every key that the block names.
4. It reads the snapshot again, and computes the digest of the set after the run. That set has the records of the file whose key is not in `T`, and the entries of the run, in key order.

`validateBlock_restrict` (in `DogeLib.Block.Proofs.Restrict`) is the reason for step 4.
On a set and on its restriction to keys that hold every key of a block, `validateBlock` gives the same error, or the same coin changes.
The new set has the entries of the restricted run at the keys of `T`, and the entries of the old set at the other keys.
The check of step 3 establishes the hypothesis of the theorem for each block, whatever step 1 collected.

No theorem covers the reads of the files or the merge of step 4 (SOUNDNESS.md, B4).
The functions of this module run in `IO`.

With `coins_in_memory` true, the oracle keeps every coin of the snapshot and runs the blocks on the whole set.
It computes the last digest from that set with `setDigest`.
That form reads the snapshot once, and it does not use the merge.
-/

@[expose] public section
namespace DogeLib.Block.Exports
open Lean (Json)
open DogeLib.Exports
open DogeLib.Serialization
open DogeLib.Transaction

/-- A fault of a snapshot file. `record` is the position of the coin record. -/
def coinsFileFailure (reason : String) (record : Option Nat := none) : Failure :=
  validateFailure reason ((record.map fun n => [("record", natJson n)]).getD [])

/-- One coin record of a snapshot: the outpoint and the coin. -/
structure SnapshotCoin where
  /-- The outpoint of the coin. -/
  outpoint : OutPoint
  /-- The coin: the output, the height and the coinbase flag. -/
  coin : Coin

/-- A little-endian number of `count` bytes at `offset`. -/
def fileNat (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldr (fun i acc => acc * 256 + (bytes.get! (offset + i)).toNat) 0

/-- The length of the fixed part of a record: the tag, the outpoint, the height, the coinbase byte and the amount. -/
def snapshotHeadSize : Nat := 50

/-- The greatest output index of a record, as for an output of the `coins` argument. -/
def maxSnapshotIndex : Nat := 1048575

/-- The greatest height of a record, as for an entry of the `coins` argument. -/
def maxSnapshotHeight : Nat := 2147483646

/--
The fixed part of the record at position `record`: the transaction ID, the output index, the height, the coinbase flag and the amount.
`head` has `snapshotHeadSize` bytes.
The checks run in this order: the tag, the index, the height, the coinbase byte and the amount.
An amount above `MAX_MONEY` as an unsigned number is a fault, which includes every negative `int64_t` amount.
-/
def snapshotHead (record : Nat) (head : ByteArray) : Except Failure (Hash256 × UInt32 × Nat × Bool × UInt64) := do
  unless head.get! 0 == 2 do throw (coinsFileFailure "coins_file_tag" record)
  let some txid := Hash256.ofBytes? (head.extract 1 33).toList | throw (coinsFileFailure "coins_file_truncated" record)
  let index := fileNat head 33 4
  let height := fileNat head 37 4
  let coinbase := head.get! 41
  let amount := fileNat head 42 8
  unless index ≤ maxSnapshotIndex do throw (coinsFileFailure "coins_file_index" record)
  unless height ≤ maxSnapshotHeight do throw (coinsFileFailure "coins_file_height" record)
  unless coinbase ≤ 1 do throw (coinsFileFailure "coins_file_coinbase" record)
  unless (amount : Int) ≤ maxMoney do throw (coinsFileFailure "coins_file_value" record)
  return (txid, UInt32.ofNat index, height, coinbase == 1, UInt64.ofNat amount)

/-- The number of bytes that follow the first byte of a CompactSize value. -/
def compactSizeExtra (first : UInt8) : Nat :=
  if first < 253 then 0 else if first == 253 then 2 else if first == 254 then 4 else 8

/-- The least value that has a CompactSize form with `extra` bytes after the first byte as its shortest form. -/
def compactSizeLeast (extra : Nat) : Nat :=
  if extra == 2 then 253 else if extra == 4 then 0x10000 else 0x100000000

/--
The next coin record of a snapshot file, at position `record`, or `none` at the end of the file.
After the fixed part, the function reads the CompactSize length of the script, which must be in its shortest form, and the script.
A script that `isUnspendable` rejects is a fault. A length above `maxScriptSize` is that fault, and the function does not read such a script.
A file that ends inside a record is truncated.
-/
def readSnapshotCoin (handle : IO.FS.Handle) (record : Nat) : IO (Except Failure (Option SnapshotCoin)) := do
  let truncated : Except Failure (Option SnapshotCoin) := .error (coinsFileFailure "coins_file_truncated" record)
  try
    let head ← readUpTo handle snapshotHeadSize
    if head.isEmpty then return .ok none
    if head.size != snapshotHeadSize then return truncated
    match snapshotHead record head with
    | .error f => return .error f
    | .ok (txid, index, height, coinbase, amount) =>
      let first ← readUpTo handle 1
      if first.size != 1 then return truncated
      let extra := compactSizeExtra (first.get! 0)
      let mut length := (first.get! 0).toNat
      if extra != 0 then
        let more ← readUpTo handle extra
        if more.size != extra then return truncated
        length := fileNat more 0 extra
        if length < compactSizeLeast extra then return .error (coinsFileFailure "coins_file_script_length" record)
      if length > maxScriptSize then return .error (coinsFileFailure "coins_file_script" record)
      let raw ← readUpTo handle length
      if raw.size != length then return truncated
      let some script := CountedList.ofList? raw.toList | return .error (coinsFileFailure "coins_file_script" record)
      if isUnspendable ⟨script⟩ then return .error (coinsFileFailure "coins_file_script" record)
      return .ok (some ⟨⟨txid, index⟩, ⟨⟨amount, ⟨script⟩⟩, height, coinbase⟩⟩)
  catch _ => return .error (coinsFileFailure "coins_file_unreadable")

/--
The order of a snapshot: the record `next` at position `record` follows the record `last`.
The key of `next` is above the key of `last`, or the two have one transaction ID and the index of `next` is above the index of `last`.
Two records of one transaction ID have the same height and the same coinbase flag, because they are outputs of one transaction.
-/
def snapshotOrder (record : Nat) (last : Option SnapshotCoin) (next : SnapshotCoin) : Except Failure Unit := do
  let some last := last | return
  let lastKey := txidKey last.outpoint.hash
  let key := txidKey next.outpoint.hash
  unless lastKey < key || (lastKey == key && last.outpoint.n < next.outpoint.n) do
    throw (coinsFileFailure "coins_file_order" record)
  if lastKey == key && (last.coin.height != next.coin.height || last.coin.coinbase != next.coin.coinbase) then
    throw (coinsFileFailure "coins_file_entry" record)

/--
The set `s` with one more coin of a snapshot.
The coin joins the entry of its transaction ID, or starts that entry.
The outputs of the entry below the index of the coin that have no record are null.
`snapshotOrder` shows that the index is above every index of the entry.
-/
def addSnapshotCoin (s : CoinSet) (c : SnapshotCoin) : CoinSet :=
  let key := txidKey c.outpoint.hash
  let index := c.outpoint.n.toNat
  let outputs := match s.entries[key]? with
    | none => []
    | some entry => entry.outputs
  ⟨s.entries.insert key ⟨c.outpoint.hash, c.coin.coinbase, c.coin.height,
    outputs ++ List.replicate (index - outputs.length) none ++ [some c.coin.out]⟩⟩

/-- The keys of the transaction IDs that a block names: the ID of each transaction, and the ID in the outpoint of each input. -/
def blockKeys (b : Block) : List Nat :=
  b.transactions.flatMap fun tx => txidKey tx.txid :: tx.inputs.val.map fun input => txidKey input.prevout.hash

/--
The keys that the blocks of a file name, for step 1 of the restricted run.
The function stops at the end of the file, and at the first record that does not read as a block.
It reports no fault: the run of the blocks reads the file again and reports it.
-/
def collectBlockKeys (path : String) (mode : TxReadMode) : IO (Std.TreeSet Nat) := do
  let mut keys : Std.TreeSet Nat := {}
  try
    let handle ← IO.FS.Handle.mk path .read
    repeat
      let head ← readUpTo handle 8
      if head.size != 8 then break
      let length := fileU32 head 4
      if length > maxFileBlockSize then break
      let raw ← readUpTo handle length
      if raw.size != length then break
      match Block.decodeComplete mode raw.toList with
      | .error _ => break
      | .ok b => keys := (blockKeys b).foldl (fun set key => set.insert key) keys
  catch _ => pure ()
  return keys

/-- What one read of a snapshot returns. -/
structure SnapshotStart where
  /-- The digest of all records of the file: the digest of the whole set. -/
  digest : ByteArray
  /-- The number of the records. -/
  count : Nat
  /-- The coins that the read kept, as a coin set. -/
  coins : CoinSet

/--
Step 2 of the restricted run: one read of the snapshot at `path`.
The result has the digest and the number of all records, and the set of the coins whose key satisfies `keep`.
-/
def readSnapshot (path : String) (keep : Nat → Bool) : IO (Except Failure SnapshotStart) := do
  let handle ← try IO.FS.Handle.mk path .read
    catch _ => return .error (coinsFileFailure "coins_file_unreadable")
  let mut digest := digestStart
  let mut count := 0
  let mut coins := CoinSet.empty
  let mut last : Option SnapshotCoin := none
  repeat
    match ← readSnapshotCoin handle count with
    | .error f => return .error f
    | .ok none => break
    | .ok (some coin) =>
      if let .error f := snapshotOrder count last coin then return .error f
      digest := digestStep digest (coinRecord 2 coin.outpoint coin.coin)
      if keep (txidKey coin.outpoint.hash) then coins := addSnapshotCoin coins coin
      count := count + 1
      last := some coin
  return .ok ⟨digest, count, coins⟩

/-- The digest, the number of coins and the total value of a whole coin set. -/
structure SetTotals where
  /-- The digest so far, with the number of its coins. -/
  digest : ByteArray × Nat := (digestStart, 0)
  /-- The sum of the amounts of the coins. -/
  value : Int := 0

/-- The totals after the coins of one entry of a run. -/
def SetTotals.addEntry (t : SetTotals) (entry : TxCoins) : SetTotals :=
  ⟨entryDigest t.digest entry, t.value + entry.value⟩

/-- The totals after one coin record of a snapshot. -/
def SetTotals.addCoin (t : SetTotals) (c : SnapshotCoin) : SetTotals :=
  ⟨(digestStep t.digest.1 (coinRecord 2 c.outpoint c.coin), t.digest.2 + 1), t.value + c.coin.value⟩

/--
Step 4 of the restricted run: the totals of the set after the run, from a second read of the snapshot at `path`.
`entries` are the entries of the run in key order, and `named` holds for the keys of `T`.
The set after the run has the records of the file whose key is not in `T`, and the entries of the run.
The function visits both in key order: before each record of the file, it takes the entries of the run with a lower key.
The file must have `count` records, the number of the first read.
-/
def mergedTotals (path : String) (named : Nat → Bool) (count : Nat) (entries : List (Nat × TxCoins)) :
    IO (Except Failure SetTotals) := do
  let handle ← try IO.FS.Handle.mk path .read
    catch _ => return .error (coinsFileFailure "coins_file_unreadable")
  let mut totals : SetTotals := {}
  let mut pending := entries
  let mut position := 0
  let mut last : Option SnapshotCoin := none
  repeat
    match ← readSnapshotCoin handle position with
    | .error f => return .error f
    | .ok none => break
    | .ok (some coin) =>
      if let .error f := snapshotOrder position last coin then return .error f
      let key := txidKey coin.outpoint.hash
      let (below, rest) := pending.span (·.1 < key)
      totals := below.foldl (fun t entry => t.addEntry entry.2) totals
      pending := rest
      unless named key do totals := totals.addCoin coin
      position := position + 1
      last := some coin
  unless position == count do return .error (coinsFileFailure "coins_file_changed")
  return .ok (pending.foldl (fun t entry => t.addEntry entry.2) totals)

/-- The arguments of a `block.validate` request with `coins_file`. -/
def snapshotArgs : List String :=
  ["id", "op", "blocks_file", "coins_file", "coins_in_memory"] ++ validateStateArgs.filter (· != "coins")

/--
`block.validate` with the coin set of the snapshot file `coins_file`, in the place of `coins`, on the blocks of `blocks_file`.
The module documentation gives the four steps of the restricted run, and the form with `coins_in_memory`.

The result has the fields of `blockValidate`, with `start_set_digest_hex` and `start_set_coins`: the digest and the number of the coins of the snapshot.
No block record has a digest of the whole set.
`set_digest_hex`, `set_coins` and `set_value` are those of the whole set after the last record.
The function writes the progress of its reads to standard error.
`extraArgs` and `hookOf` are the added arguments and the hook of `blockValidateFileWith`.
The hook runs on the same restricted coin set as the baseline step.
-/
def blockValidateSnapshotWith (extraArgs : List String) (hookOf : HookReader) (fields : Args) :
    IO (Except Failure Json) := do
  for (key, _) in fields do
    unless snapshotArgs.contains key || extraArgs.contains key do
      return .error (.request s!"unknown argument {key} for operation block.validate with coins_file")
  let hook ← match hookOf fields with
    | .ok hook => pure hook
    | .error f => return .error f
  unless fields.contains "blocks_file" do return .error (.request "coins_file needs blocks_file")
  let .ok (.str blocks) := arg fields "blocks_file" | return .error (.request "blocks_file must be a string")
  let .ok (.str path) := arg fields "coins_file" | return .error (.request "coins_file must be a string")
  let whole ← match fields.get? "coins_in_memory" with
    | none => pure false
    | some (.bool b) => pure b
    | some _ => return .error (.request "coins_in_memory must be a Boolean")
  -- The other arguments are those of a request with no coins.
  let (options, start) ← match validateStart (fields.insert "coins" (.arr #[])) with
    | .ok (options, start) => pure ({ options with setDigests := false }, start)
    | .error f => return .error f
  let names ← if whole then pure {} else collectBlockKeys blocks options.mode
  let keep : Nat → Bool := fun key => whole || names.contains key
  let snapshot ← match ← readSnapshot path keep with
    | .ok snapshot => pure snapshot
    | .error f => return .error f
  IO.eprintln s!"block.validate: read {snapshot.count} coins of the snapshot"
  -- Step 3. The check gives the hypothesis of `validateBlock_restrict` for each block.
  let check : Nat → List UInt8 → Except Failure Unit := fun index bytes =>
    if whole then .ok () else
      match Block.decodeComplete options.mode bytes with
      | .error _ => .ok ()
      | .ok b =>
        if (blockKeys b).all names.contains then .ok ()
        else .error (validateFailure "blocks_file_changed" [("index", natJson index)])
  let run ← match ← validateFileRun blocks options { start with coins := snapshot.coins } hook check with
    | .ok run => pure run
    | .error f => return .error f
  let startFields := [("start_set_digest_hex", Json.str (hexOf snapshot.digest.toList)),
    ("start_set_coins", natJson snapshot.count)]
  if whole then return .ok ((validateResult run).mergeObj (Json.mkObj startFields))
  let totals ← match ← mergedTotals path names.contains snapshot.count run.coins.entries.toList with
    | .ok totals => pure totals
    | .error f => return .error f
  IO.eprintln s!"block.validate: read the snapshot again for the digest of {totals.digest.2} coins"
  return .ok (Json.mkObj ([("blocks", .arr run.records), ("out_of_domain_at", (run.outOfDomain.map natJson).getD .null),
    ("set_digest_hex", .str (hexOf totals.digest.1.toList)), ("set_coins", natJson totals.digest.2),
    ("set_value", valueJson totals.value)] ++ startFields ++ versionBitsField run))

/-- `block.validate` with `coins_file` of `dogelib-oracle`: `blockValidateSnapshotWith` with no added argument and no hook. -/
def blockValidateSnapshot (fields : Args) : IO (Except Failure Json) := blockValidateSnapshotWith [] noHook fields

end DogeLib.Block.Exports
