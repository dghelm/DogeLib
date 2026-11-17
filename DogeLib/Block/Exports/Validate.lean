module

public import DogeLib.Block.Exports.Oracle
public import DogeLib.Block.Validate
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

/-- The verdict of one block, with nulls where a field does not apply. -/
def blockRecord (height : Nat) (hash : Hash256) (rejection : Option (String × Nat × Nat))
    (changes : Option (List CoinChange)) (set : Option ByteArray) (diagnostic : Json) : Json :=
  Json.mkObj ([("height", natJson height)] ++ hashFields "hash" hash ++ rejectionFields rejection ++
    [("changes_digest_hex", changes.map (fun c => Json.str (hexOf (changesDigest c).toList)) |>.getD .null),
      ("spent", changes.map (fun c => natJson (c.filter (· matches .spent ..)).length) |>.getD .null),
      ("created", changes.map (fun c => natJson (c.filter (· matches .created ..)).length) |>.getD .null),
      ("set_digest_hex", set.map (fun d => Json.str (hexOf d.toList)) |>.getD .null),
      ("diagnostic", diagnostic)])

/-- The interval of the whole-set digest: after each accepted block whose height is a multiple of it (design record 0010, section 5). -/
def setDigestInterval : Nat := 1000

/--
`block.validate`: `validateBlock` with `coreVerifier` on each block of `blocks_hex`, in order.
The module documentation and `docs/oracle.md` give the state, the digests and the errors.
Checkpoints are disabled.
A block whose sums leave the `int64_t` range ends the range: the response holds the blocks before it, and `out_of_domain_at` is its position.
-/
def blockValidate : Operation where
  name := "block.validate"
  args := ["mode", "check_pow", "check_merkle_root", "adjusted_time", "chain", "bip34_ancestor_hex", "coins",
    "blocks_hex"]
  run fields := do
    let mode ← argMode fields
    let checkPow ← Work.Exports.argBool fields "check_pow"
    let checkMerkle ← Work.Exports.argBool fields "check_merkle_root"
    let time := Int64.ofInt (← argInt fields "adjusted_time" (-9223372036854775808) maxAdjustedTime)
    let mut view ← Work.Exports.argView fields
    let mut ancestor ← match ← arg fields "bip34_ancestor_hex" with
      | .null => pure none
      | _ => some <$> argHash fields "bip34_ancestor_hex"
    let aboveBip34 := match view with
      | [] => false
      | prev :: _ => bip34Height ≤ prev.nHeight
    unless ancestor.isSome == aboveBip34 do
      throw (.request "bip34_ancestor_hex must be a hash exactly when the predecessor is at or above height 1034383")
    let mut coins ← argCoins fields
    let .arr raws ← arg fields "blocks_hex" | throw (.request "blocks_hex must be an array")
    let mut tip : Option Hash256 := none
    let mut records := #[]
    let mut outOfDomain := Json.null
    for raw in raws do
      let index := records.size
      let bs ← argHex (Std.TreeMap.Raw.ofList [("blocks_hex", raw)]) "blocks_hex"
      let b ← match Block.decodeComplete mode bs with
        | .error (.read e) => throw (.spec ((Transaction.Exports.witnessReadErrorJson e).setObjVal! "index" (natJson index)))
        | .error (.trailingBytes n) =>
          throw (.spec (Json.mkObj [("kind", "trailing_bytes"), ("count", natJson n), ("index", natJson index)]))
        | .ok b => pure b
      let hash := b.header.pure.getHash
      let genesis := some hash == genesisHash? .mainnet
      -- A block extends the last accepted block. The first block names the supplied predecessor.
      if genesis then
        unless view.isEmpty do throw (validateFailure "genesis_after_start" [("index", natJson index)])
      else
        if view.isEmpty then throw (validateFailure "no_predecessor" [("index", natJson index)])
        match tip with
        | none =>
          -- At height 1034383 the predecessor is its own ancestor at that height.
          if view.head?.map (·.nHeight) == some bip34Height && ancestor != some b.header.pure.hashPrevBlock then
            throw (.request "bip34_ancestor_hex must be the predecessor's hash at height 1034383")
          tip := some b.header.pure.hashPrevBlock
        | some t =>
          unless t == b.header.pure.hashPrevBlock do
            throw (validateFailure "not_linked" [("index", natJson index)])
      let (height, csvActive, segwitActive, prevMtp) ← bodyStates view
      let ctx : ValidateContext := ⟨view, time, none, csvActive, segwitActive, prevMtp, ancestor⟩
      match validateBlock Script.coreVerifier checkPow checkMerkle ctx coins b with
      | .ok result =>
        coins := result.coins
        view := ⟨height, b.header.pure.nTime, b.header.pure.nBits⟩ :: view
        tip := some hash
        if height == bip34Height then ancestor := some hash
        let set := if height % setDigestInterval == 0 then some (setDigest coins).1 else none
        records := records.push (blockRecord height hash none (some result.changes) set .null)
      | .error e =>
        match e.rejectReason with
        | some reason =>
          records := records.push (blockRecord height hash (some (reason, e.dosScore, e.rejectCode)) none none
            (.str s!"{e.step}: {reprStr e}"))
        | none =>
          if e == .connect .outOfDomain then
            outOfDomain := natJson index
            break
          else
            throw (validateFailure "outside_model" [("index", natJson index), ("detail", .str (reprStr e))])
    let (digest, count) := setDigest coins
    return Json.mkObj [("blocks", .arr records), ("out_of_domain_at", outOfDomain),
      ("set_digest_hex", .str (hexOf digest.toList)), ("set_coins", natJson count)]

end DogeLib.Block.Exports
