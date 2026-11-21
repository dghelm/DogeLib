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

## A second check of each block

`validateStep` takes an optional `BlockHook`.
A hook is a function of the options, the context, the coin set before the block and the block, and it returns a JSON value.
With a hook, each block record gains the field `revised` with that value.
The hook changes no state of the run and no other field.
`blockValidate` and `blockValidateFile` use no hook, so `dogelib-oracle` writes no such field.
`blockValidateWith` and `blockValidateFileWith` take the names of added arguments and a function that reads the hook from the request.
This library defines no hook.

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

/-- One entry in the digest of a whole coin set. `acc` is the digest and the count so far. The result is the digest and the count after the coins of the entry, in the order of the outputs. -/
def entryDigest (acc : ByteArray × Nat) (entry : TxCoins) : ByteArray × Nat :=
  entry.coins.foldl (fun (d, n) (o, c) => (digestStep d (coinRecord 2 o c), n + 1)) acc

/-- The digest of the whole coin set and the number of its coins, in the order of the keys and then of the outputs. -/
def setDigest (s : CoinSet) : ByteArray × Nat :=
  s.entries.foldl (fun acc _ entry => entryDigest acc entry) (digestStart, 0)

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
  /-- Whether a block record has the digest of the whole set at each multiple of `setDigestInterval`. A request with `coins_file` clears it. -/
  setDigests : Bool := true
  /-- The heights of `version_bits_heights`: after the supplied predecessor and after each accepted block at one of them, the response reports the states of CSV and SegWit for the next block. `none` without the argument. -/
  versionBitsHeights : Option (List Nat) := none

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
  /-- The version of each entry of `view`, newest first, or `none` for a supplied entry without one. -/
  versions : List (Option UInt32) := []
  /-- The state of CSV at the last aligned boundary in the case-3 gap that the run walked: its height and the state. -/
  csvCache : Option (Nat × ThresholdState) := none
  /-- The reported states of `version_bits_heights`, or `none` without the argument. -/
  versionBitsStates : Option (Array Json) := none

/-- One entry of the `chain` of `block.validate`: `{height, time, bits}`, with the optional `version` of its header. -/
def versionedEntryOfJson (j : Json) : Except Failure (Work.BlockIndex × Option UInt32) := do
  let .obj fields := j | throw (.request "chain entries must be objects")
  for (key, _) in fields do
    unless ["height", "time", "bits", "version"].contains key do
      throw (.request s!"unknown chain entry field {key}")
  let entry : Work.BlockIndex := ⟨(← argU32 fields "height").toNat, ← argU32 fields "time", ← argU32 fields "bits"⟩
  let version ← match fields.get? "version" with
    | none => pure none
    | some _ => some <$> argU32 fields "version"
  return (entry, version)

/-- The request error of a chain that does not reach the boundary below the CSV start, with its ten predecessors. -/
def shortWindowError : Failure := .request "chain does not reach a version-bits boundary below the CSV start"

/--
The backward walk of `GetStateFor` (D102, lines 58 to 66): from the boundary at height `k`, one period at a time, to the latest boundary whose median time is below the CSV start.
`mtpAt` gives the median time past at a height.
The result is the height of that boundary, the *base*, and the boundaries above it with their median times, oldest first, after those of `acc`.
A boundary of the first period at or after the start gives an error, as in the harness. On mainnet the first boundary is in 2014.
-/
def csvBackwardWalk (mtpAt : Nat → Except Failure Int) : Nat → Nat → List (Nat × Int) → Except Failure (Nat × List (Nat × Int))
  | 0, _, _ => throw shortWindowError
  | fuel + 1, k, acc => do
    let m ← mtpAt k
    if m < csvDeployment.startTime then return (k, acc)
    if k < minerConfirmationWindow then
      throw (.spec (Json.mkObj [("kind", .str "version_bits"), ("reason", .str "first_period")]))
    csvBackwardWalk mtpAt fuel (k - minerConfirmationWindow) ((k, m) :: acc)

/--
The state of CSV at the aligned boundary at height `aligned`, whose median time is in the case-3 gap, by Core's walk in `GetStateFor` (D102, lines 24 to 106).
`view` and `versions` are the chain view and the versions of its entries, newest first, and `top` is the height of the first entry.
`csvBackwardWalk` finds the base: the latest boundary at or below `aligned` whose median time is below the CSV start.
The state is `versionBitsWalk` over the boundaries above the base, oldest first, each with its median time and the number of blocks of its period that signal CSV.
`versionBitsStateFull_of_reset` shows that this walk equals the full walk from the genesis block, when these boundaries are those of the chain.
The view must reach the base and its ten predecessors, and every entry above the base needs a version, as in the harness.
-/
def csvWindowState (view : Array Work.BlockIndex) (versions : Array (Option UInt32)) (top aligned : Nat) :
    Except Failure ThresholdState := do
  let lowest := top + 1 - view.size
  let mtpAt : Nat → Except Failure Int := fun h => do
    if h < lowest + min 10 h || top < h then throw shortWindowError
    match Work.medianTimePast (view.extract (top - h) (top - h + 11)).toList with
    | .ok m => pure m
    | .error _ => throw shortWindowError
  let (base, above) ← csvBackwardWalk mtpAt (aligned / minerConfirmationWindow + 1) aligned []
  unless versions.size == view.size && (versions.extract 0 (top - base)).all Option.isSome do
    throw (.request "a chain entry in the CSV window has no version")
  -- The period of the boundary at height `j` is the heights from `j - 10079` to `j`, at the indices from `top - j`.
  let boundaries := above.map fun (j, m) =>
    (⟨m, (List.range minerConfirmationWindow).countP fun i =>
      match versions[top - j + i]? with
      | some (some v) => versionBitsCondition csvDeployment v
      | _ => false⟩ : PeriodBoundary)
  return versionBitsWalk csvDeployment ruleChangeActivationThreshold boundaries

/--
The candidate height, the states of CSV and SegWit, and the median time of `viewStates` for the next block of `run`, and the run with the updated cache.
In the case-3 gap of CSV the state comes from `csvWindowState`, or from the cache when the run already walked that boundary.
The chain only grows within a request, so the state at one aligned boundary does not change.
-/
def runStates (run : ValidateRun) : Except Failure ((Nat × ThresholdState × ThresholdState × Int) × ValidateRun) := do
  let top := (run.view.head?.map (·.nHeight)).getD 0
  let gap : Nat → Int → Except Failure ThresholdState := fun aligned _ =>
    match run.csvCache with
    | some (k, s) => if k == aligned then pure s else csvWindowState run.view.toArray run.versions.toArray top aligned
    | none => csvWindowState run.view.toArray run.versions.toArray top aligned
  let (height, csv, seg, mtp) ← viewStates run.view gap
  -- The median time is that of the aligned boundary. It is in the gap only when the walk gave the state.
  let csvCache := if run.view.isEmpty || (versionBitsShortcut csvDeployment mtp).isSome then run.csvCache
    else some ((top - (top + 1) % minerConfirmationWindow), csv)
  return ((height, csv, seg, mtp), { run with csvCache })

/-- The run after the report of the states for the next block, when `version_bits_heights` lists the height of its predecessor. -/
def reportVersionBits (options : ValidateOptions) (run : ValidateRun) : Except Failure ValidateRun := do
  let some heights := options.versionBitsHeights | return run
  let some prev := run.view.head? | return run
  unless heights.contains prev.nHeight do return run
  let ((_, csv, seg, _), run) ← runStates run
  let state := Json.mkObj [("height", natJson prev.nHeight), ("csv", .str csv.name), ("segwit", .str seg.name)]
  return { run with versionBitsStates := run.versionBitsStates.map (·.push state) }

/-- The heights of `version_bits_heights`, in increasing order, or `none` without the argument. -/
def argVersionBitsHeights (fields : Args) : Except Failure (Option (List Nat)) := do
  let some value := fields.get? "version_bits_heights" | return none
  let .arr entries := value | throw (.request "version_bits_heights must be an array")
  let heights ← entries.toList.mapM fun entry =>
    return (← argInt (Std.TreeMap.Raw.ofList [("version_bits_heights", entry)]) "version_bits_heights" 0 2147483646).toNat
  unless (heights.zip heights.tail).all (fun (a, b) => a < b) do
    throw (.request "version_bits_heights must be in increasing order")
  return some heights

/-- The options and the first state of a `block.validate` request, from every argument except the blocks. -/
def validateStart (fields : Args) : Except Failure (ValidateOptions × ValidateRun) := do
  let mode ← argMode fields
  let checkPow ← Work.Exports.argBool fields "check_pow"
  let checkMerkle ← Work.Exports.argBool fields "check_merkle_root"
  let time := Int64.ofInt (← argInt fields "adjusted_time" (-9223372036854775808) maxAdjustedTime)
  let .arr entries ← arg fields "chain" | throw (.request "chain must be an array")
  let versioned ← entries.toList.mapM versionedEntryOfJson
  let view := versioned.map (·.1)
  let ancestor ← match ← arg fields "bip34_ancestor_hex" with
    | .null => pure none
    | _ => some <$> argHash fields "bip34_ancestor_hex"
  let aboveBip34 := match view with
    | [] => false
    | prev :: _ => bip34Height ≤ prev.nHeight
  unless ancestor.isSome == aboveBip34 do
    throw (.request "bip34_ancestor_hex must be a hash exactly when the predecessor is at or above height 1034383")
  let coins ← argCoins fields
  let versionBitsHeights ← argVersionBitsHeights fields
  let options : ValidateOptions := { mode, checkPow, checkMerkle, time, versionBitsHeights }
  let start : ValidateRun :=
    { view := view
      ancestor := ancestor
      coins := coins
      tip := none
      records := #[]
      outOfDomain := none
      versions := versioned.map (·.2)
      versionBitsStates := versionBitsHeights.map (fun _ => #[]) }
  return (options, ← reportVersionBits options start)

/--
A second check of one block, for a caller outside this library.
It reads the options of the request, the context that `validateBlock` gets, the coin set before the block, and the block.
Its value becomes the field `revised` of the block record.
-/
abbrev BlockHook : Type := ValidateOptions → ValidateContext → CoinSet → Block → Json

/-- The function that reads the hook of a request from its arguments. `noHook` is the one of `block.validate` in this library. -/
abbrev HookReader : Type := Args → Except Failure (Option BlockHook)

/-- The reader that gives no hook for every request. -/
def noHook : HookReader := fun _ => pure none

/--
One block of a `block.validate` request: the bytes `bs` at the position `run.records.size`.
`fileHeight` is the height that a record of `blocks_file` gives, which must be the candidate height.
The result is the next state, in which `outOfDomain` is set when the block ends the range.
With a `hook`, the record of the block gains the field `revised`, and nothing else changes.
-/
def validateStep (options : ValidateOptions) (run : ValidateRun) (bs : List UInt8) (fileHeight : Option Nat := none)
    (hook : Option BlockHook := none) : Except Failure ValidateRun := do
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
  let ((height, csv, seg, prevMtp), run) ← runStates run
  let csvActive := csv == .active
  let segwitActive := seg == .active
  if let some h := fileHeight then
    unless h == height do throw (validateFailure "file_height" [("index", natJson index)])
  let ctx : ValidateContext := ⟨run.view, options.time, none, csvActive, segwitActive, prevMtp, run.ancestor⟩
  -- The hook runs before the baseline check, so that it holds no reference to the coin set afterwards.
  let revised := hook.map fun h => h options ctx run.coins b
  let withRevised := fun (record : Json) => match revised with
    | none => record
    | some value => record.setObjVal! "revised" value
  match validateBlock Script.coreVerifier options.checkPow options.checkMerkle ctx run.coins b with
  | .ok result =>
    let set := if options.setDigests && height % setDigestInterval == 0 then
      some ((setDigest result.coins).1, result.coins.totalValue) else none
    reportVersionBits options { run with
      coins := result.coins
      view := ⟨height, b.header.pure.nTime, b.header.pure.nBits⟩ :: run.view
      versions := some b.header.pure.nVersion :: run.versions
      tip := some hash
      ancestor := if height == bip34Height then some hash else run.ancestor
      records := run.records.push (withRevised (blockRecord height hash none (some result.changes) set .null)) }
  | .error e =>
    match e.rejectReason with
    | some reason =>
      return { run with
        tip := tip
        records := run.records.push (withRevised (blockRecord height hash (some (reason, e.dosScore, e.rejectCode))
          none none (.str s!"{e.step}: {reprStr e}"))) }
    | none =>
      if e == .connect .outOfDomain then return { run with tip := tip, outOfDomain := some index }
      else throw (validateFailure "outside_model" [("index", natJson index), ("detail", .str (reprStr e))])

/-- The field `version_bits_states` of a run with `version_bits_heights`, and no field without it. -/
def versionBitsField (run : ValidateRun) : List (String × Json) :=
  match run.versionBitsStates with
  | none => []
  | some states => [("version_bits_states", .arr states)]

/-- The `ok` object of a `block.validate` request after its last block. -/
def validateResult (run : ValidateRun) : Json :=
  let (digest, count) := setDigest run.coins
  Json.mkObj ([("blocks", .arr run.records), ("out_of_domain_at", (run.outOfDomain.map natJson).getD .null),
    ("set_digest_hex", .str (hexOf digest.toList)), ("set_coins", natJson count),
    ("set_value", valueJson run.coins.totalValue)] ++ versionBitsField run)

/-- The arguments of `block.validate` that give the state before the first block, and `version_bits_heights`. -/
def validateStateArgs : List String :=
  ["mode", "check_pow", "check_merkle_root", "adjusted_time", "chain", "bip34_ancestor_hex", "coins",
    "version_bits_heights"]

/--
`block.validate` with the added arguments `extraArgs` and the hook that `hookOf` reads from the request.
`validateBlock` runs with `coreVerifier` on each block of `blocks_hex`, in order.
The module documentation and `docs/oracle.md` give the state, the digests and the errors.
Checkpoints are disabled.
A block whose sums leave the `int64_t` range ends the range: the response holds the blocks before it, and `out_of_domain_at` is its position.
A request with `blocks_file` in the place of `blocks_hex` reads a file, so `blockValidateFileWith` answers it.
-/
def blockValidateWith (extraArgs : List String) (hookOf : HookReader) : Operation where
  name := "block.validate"
  args := validateStateArgs ++ ["blocks_hex"] ++ extraArgs
  run fields := do
    let hook ← hookOf fields
    let (options, start) ← validateStart fields
    let .arr raws ← arg fields "blocks_hex" | throw (.request "blocks_hex must be an array")
    let mut run := start
    for raw in raws do
      let bs ← argHex (Std.TreeMap.Raw.ofList [("blocks_hex", raw)]) "blocks_hex"
      run ← validateStep options run bs none hook
      if run.outOfDomain.isSome then break
    return validateResult run

/-- `block.validate` of `dogelib-oracle`: `blockValidateWith` with no added argument and no hook. -/
def blockValidate : Operation := blockValidateWith [] noHook

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
The run of `block.validate` over the blocks of the file at `path`, from the state `start`.
The file has the format of `blocks.bin` of `scripts/fetch_blocks.py`: for each block the height and the length as 4-byte little-endian integers, then the block.
The function reads one block at a time, so the file can be larger than memory.
Each record's height must be the candidate height.
`hook` is the hook of `validateStep`.
`check` gets the position and the bytes of each block before its step, and its failure ends the run.
After each accepted block whose height is a multiple of `setDigestInterval`, the function writes the height to standard error.
-/
def validateFileRun (path : String) (options : ValidateOptions) (start : ValidateRun)
    (hook : Option BlockHook := none)
    (check : Nat → List UInt8 → Except Failure Unit := fun _ _ => .ok ()) : IO (Except Failure ValidateRun) := do
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
    let bytes := raw.toList
    if let .error f := check index bytes then return .error f
    -- The step is the last use of `run`, so that it can change the records and the coin set in place.
    let before := run.view.head?.map (·.nHeight)
    match validateStep options run bytes (some (fileU32 head 0)) hook with
    | .error f => return .error f
    | .ok next =>
      -- An accepted block puts its own height, which is new, at the head of the view.
      if let some entry := next.view.head? then
        if some entry.nHeight != before && entry.nHeight % setDigestInterval == 0 then
          IO.eprintln s!"block.validate: accepted height {entry.nHeight}"
      run := next
    if run.outOfDomain.isSome then break
  return .ok run

/--
`block.validate` on the blocks of the file `blocks_file`, in the place of `blocks_hex`, with the added arguments `extraArgs` and the hook that `hookOf` reads from the request.
`validateFileRun` reads the file and gives the format.
The other arguments, the state and the response are those of `blockValidate`.
A request of `dogelib-oracle` that also has `coins_file` reads a snapshot, so `blockValidateSnapshot` answers it.
-/
def blockValidateFileWith (extraArgs : List String) (hookOf : HookReader) (fields : Args) :
    IO (Except Failure Json) := do
  for (key, _) in fields do
    unless key == "id" || key == "op" || key == "blocks_file" || validateStateArgs.contains key ||
        extraArgs.contains key do
      return .error (.request s!"unknown argument {key} for operation block.validate with blocks_file")
  let hook ← match hookOf fields with
    | .ok hook => pure hook
    | .error f => return .error f
  let .ok (.str path) := arg fields "blocks_file" | return .error (.request "blocks_file must be a string")
  let (options, start) ← match validateStart fields with
    | .ok r => pure r
    | .error f => return .error f
  match ← validateFileRun path options start hook with
  | .error f => return .error f
  | .ok run => return .ok (validateResult run)

/-- `block.validate` with `blocks_file` of `dogelib-oracle`: `blockValidateFileWith` with no added argument and no hook. -/
def blockValidateFile (fields : Args) : IO (Except Failure Json) := blockValidateFileWith [] noHook fields

end DogeLib.Block.Exports
