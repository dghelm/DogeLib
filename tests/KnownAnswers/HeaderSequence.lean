import DogeLib.Block
import KnownAnswers.Block
import KnownAnswers.ContextualCheck

/-!
## The block-index model

Known answers for the block-index model of design record 0008, stage 1, through the compiled code.
Each check builds a `HeaderIndex` from one of the five mainnet fixtures.
The key of each entry is the double SHA-256 of its header, and its predecessor is the header's `hashPrevBlock`.
The first header of a fixture is the genesis entry at height 0, or an anchor.
No entry has a failure flag, and the failed list is empty.

The expected values come from the fixture data and from hand derivation, never from `ancestorView` or `lastCheckpointInIndex`:

- The expected view of a candidate lists the fixture records from its predecessor down, by position in the fixture.
  Its length is the smaller of the records below the candidate and the depth that `contextualViewDepth_eq` states.
  On mainnet, that depth is 241 below candidate height 145000 and 11 from it.
- The expected last checkpoint is the one table height in the range of the fixture, from the table of D9.
  The READMEs of the fixtures record the checkpoint hashes in their ranges.
- The expected verdict of `contextualCheckBlockHeader` on the view and the last checkpoint comes from chain acceptance and design record 0006.
  A real header passes, with two exceptions.
  A view with fewer than 11 entries above an anchor gives `shortView`.
  Check 4 rejects a candidate below the last checkpoint (D33, lines 3093 to 3100).

These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.

The checks of stage 2 run one step, `acceptBlockHeader`, through the compiled code.
`checkRegtestSteps` takes each request and expectation of the regtest fixture (D83).
`checkMainnetSteps` and `checkSyntheticSteps` take expectations that this module derives by hand from D33, design record 0008 and chain acceptance.
-/

namespace KnownAnswers.HeaderSequence
open DogeLib DogeLib.Block DogeLib.Work
open KnownAnswers.ContextualCheck (Record loadRange viewBelow timeOf checkpoint371337 bip66CommentHash
  bip65CommentHash)
open KnownAnswers.Sha256Cavp (toHex)

/-- Checks a condition, and reports the label on failure. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL header sequence: {label}"
  return 1

/-- Compares the full result of the contextual check, including the error constructor and its fields. -/
private def sameResult (a b : Except ContextualHeaderError Unit) : Bool :=
  match a, b with
  | .ok (), .ok () => true
  | .error x, .error y => decide (x = y)
  | _, _ => false

/-- The display-order hexadecimal digits of a hash. -/
def displayHex (h : Hash256) : String := toHex ⟨h.displayBytes.toArray⟩

/-- The entry of the record at position `i`.
The record at position `lo` has no predecessor: the genesis entry when its height is 0, and otherwise an anchor. -/
def entryAt (records : Array Record) (lo i : Nat) : IndexEntry :=
  let r := records[i]!
  ⟨r.header, r.height, if i = lo then none else some r.header.hashPrevBlock, false, false, false⟩

/-- The index of the records at positions `lo` to `hi - 1`, inserted in height order, with an empty failed list. -/
def indexOf (records : Array Record) (lo hi : Nat) : HeaderIndex :=
  (List.range' lo (hi - lo)).foldl
    (fun index i => index.insert records[i]!.header.getHash (entryAt records lo i)) ⟨[], []⟩

/-- The mainnet depth of the view of a candidate, as `contextualViewDepth_eq` states it: 241 below candidate height 145000, and 11 from it. -/
def depthAt (candidate : Nat) : Nat := if candidate < 145000 then 241 else 11

/-- The expected verdict for the real header at a candidate height with `below` records under it in the index.
Fewer than 11 entries above an anchor give `shortView`.
A candidate below the last checkpoint gives `bad-fork-prior-to-checkpoint`. -/
def expectedVerdict (genesis : Bool) (below candidate : Nat) (last : Option Nat) :
    Except ContextualHeaderError Unit :=
  if !genesis && below < 11 then .error .shortView
  else match last with
    | some c => if candidate < c then .error .badForkPriorToCheckpoint else .ok ()
    | none => .ok ()

/--
Checks one fixture range with the index of all its records.

- The lookup of each record's hash gives its entry.
- The view of each predecessor is the expected list of fixture records.
- `lastCheckpointInIndex` with checkpoints enabled is `expectedLast`, and `none` with them disabled.
  `checkpointHeightsInIndex` is the list of `expectedLast`.
- For each candidate header in the fixture, the contextual check on the view and the last checkpoint gives `expectedVerdict`.
  With checkpoints disabled, only `shortView` remains.

Returns the number of failures and the number of candidates.
-/
def checkRange (label : String) (records : Array Record) (expectedLast : Option Nat) :
    IO (Nat × Nat) := do
  let first := records[0]!.height
  let genesis := first == 0
  let index := indexOf records 0 records.size
  let mut failures := 0
  let last := lastCheckpointInIndex .mainnet true index
  failures := failures + (← require s!"{label}: last checkpoint {repr last}" (last == expectedLast))
  failures := failures + (← require s!"{label}: last checkpoint disabled"
    (lastCheckpointInIndex .mainnet false index == none))
  failures := failures + (← require s!"{label}: checkpoint heights in the index"
    (checkpointHeightsInIndex .mainnet index == expectedLast.toList))
  for i in [0:records.size] do
    let r := records[i]!
    let candidate := r.height + 1
    let some prev := index.lookup r.header.getHash
      | do failures := failures + (← require s!"{label}: lookup at {r.height}" false); continue
    failures := failures + (← require s!"{label}: entry at {r.height}" (prev == entryAt records 0 i))
    let expected := (viewBelow records first candidate).take (depthAt candidate)
    failures := failures + (← require s!"{label}: view of {r.height}"
      (ancestorView .mainnet index prev == expected))
  let mut count := 0
  for i in [1:records.size] do
    let r := records[i]!
    let some prev := index.lookup records[i - 1]!.header.getHash
      | do failures := failures + (← require s!"{label}: lookup below {r.height}" false); continue
    let view := ancestorView .mainnet index prev
    count := count + 1
    failures := failures + (← require s!"{label}: verdict at {r.height}"
      (sameResult (contextualCheckBlockHeader .mainnet r.header view (timeOf r.header) last)
        (expectedVerdict genesis i r.height expectedLast)))
    failures := failures + (← require s!"{label}: verdict without checkpoints at {r.height}"
      (sameResult (contextualCheckBlockHeader .mainnet r.header view (timeOf r.header)
          (lastCheckpointInIndex .mainnet false index))
        (expectedVerdict genesis i r.height none)))
  return (failures, count)

/-! ### Mainnet heights 0 to 12 -/

/--
The genesis range: the index holds heights 0 to 12, with the genesis entry at height 0.
The view of every predecessor reaches height 0 and equals the whole chain, `ancestorChain`.
The only table hash in the range is genesis, so the last checkpoint is height 0.
`genesisHash?` of mainnet equals the hash of the fixture's first header, whose display form the README records.
-/
def checkGenesisRange : IO Nat := do
  let some records ← loadRange "tests/work/mainnet-genesis-headers/headers.txt" 0 13
      [(0, KnownAnswers.MedianTimePast.genesisHash)]
    | return 1
  let (failures, count) ← checkRange "0-12" records (some 0)
  let mut failures := failures
  let index := indexOf records 0 13
  failures := failures + (← require "mainnet genesis hash"
    (genesisHash? .mainnet == some records[0]!.header.getHash))
  for i in [0:13] do
    let some prev := index.lookup records[i]!.header.getHash
      | do failures := failures + (← require s!"genesis lookup at {i}" false); continue
    let chain := ancestorChain index prev
    failures := failures + (← require s!"genesis chain of {i} has {i + 1} entries ending at 0"
      (chain.length == i + 1 && chain.getLast?.map BlockIndex.nHeight == some 0))
    failures := failures + (← require s!"genesis view equals the chain at {i}"
      (ancestorView .mainnet index prev == chain))
  IO.println s!"header index 0-12: {count} candidates and 13 chains; {failures} failures"
  return failures

/-! ### Mainnet heights 144719 to 145030 -/

/--
The range 144719 to 145030, with an anchor at 144719.
The index holds checkpoint 145000, so the last checkpoint is 145000, and every candidate from 144730 to 144999 fails check 4.
Without that entry, an index of the records up to 144999 has no table hash.

With the anchor moved up to 144720, the view of the predecessor of the retarget at 144960 has 240 entries.
It lacks the entry 240 below its predecessor (D17, lines 77 to 85), and the expected result is the adapter error `nextWork missingAncestor`.
-/
def checkDigishieldRange : IO Nat := do
  let first := 144719
  let some records ← loadRange "tests/work/mainnet-headers/headers.txt" first 312
      [(145000, "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72")]
    | return 1
  let (failures, count) ← checkRange "144719-145030" records (some 145000)
  let mut failures := failures
  let at145000 := records[145000 - first]!.header.getHash
  let some checkpoint := (checkpoints .mainnet).find? (·.height == 145000)
    | return failures + (← require "checkpoint 145000 in the table" false)
  failures := failures + (← require "checkpoint 145000 hash" (checkpoint.blockHash? == some at145000))
  -- The index without the checkpoint block.
  let below := indexOf records 0 (145000 - first)
  failures := failures + (← require "no checkpoint below 145000"
    (lastCheckpointInIndex .mainnet true below == none && checkpointHeightsInIndex .mainnet below == []))
  -- The anchor at 144720.
  let raised := indexOf records 1 records.size
  let r := records[144960 - first]!
  let some prev := raised.lookup records[144959 - first]!.header.getHash
    | return failures + (← require "lookup of 144959" false)
  let view := ancestorView .mainnet raised prev
  failures := failures + (← require "view above the raised anchor has 240 entries" (view.length == 240))
  failures := failures + (← require "retarget at 144960 above the raised anchor"
    (sameResult (contextualCheckBlockHeader .mainnet r.header view (timeOf r.header) none)
      (.error (.nextWork .missingAncestor))))
  IO.println s!"header index 144719-145030: {count} candidates, a raised anchor and the checkpoint; {failures} failures"
  return failures

/-! ### Mainnet AuxPoW activation, BIP66 and BIP65 ranges -/

/--
The range 371320 to 371340 holds checkpoint 371337, so the last checkpoint is 371337.
Candidates from 371331 to 371336 fail check 4, and candidates from 371337 pass.
The ranges at `BIP66Height` and `BIP65Height` hold no table hash, so their last checkpoint is `none`.
-/
def checkLaterRanges : IO Nat := do
  let some auxpow ← loadRange "tests/block/mainnet-auxpow-activation-headers/headers.txt" 371320 21
      [(371337, checkpoint371337)]
    | return 1
  let some bip66 ← loadRange "tests/block/mainnet-bip66-headers/headers.txt" 1032483 1908
      [(1032483, bip66CommentHash)]
    | return 1
  let some bip65 ← loadRange "tests/block/mainnet-bip65-headers/headers.txt" 3464739 22
      [(3464751, bip65CommentHash)]
    | return 1
  let (f₁, n₁) ← checkRange "371320-371340" auxpow (some 371337)
  let (f₂, n₂) ← checkRange "1032483-1034390" bip66 none
  let (f₃, n₃) ← checkRange "3464739-3464760" bip65 none
  let mut failures := f₁ + f₂ + f₃
  let some checkpoint := (checkpoints .mainnet).find? (·.height == 371337)
    | return failures + (← require "checkpoint 371337 in the table" false)
  failures := failures + (← require "checkpoint 371337 hash"
    (checkpoint.blockHash?.map displayHex == some checkpoint371337))
  IO.println s!"header index 371320-371340, 1032483-1034390 and 3464739-3464760: {n₁ + n₂ + n₃} candidates; {failures} failures"
  return failures

/-! ### Interface and genesis hashes -/

/--
The lookup and insertion interface, on entries of the genesis fixture.
An insertion under a known key shadows the earlier entry.
It leaves other keys and the failed list unchanged.
The genesis hashes of testnet and regtest equal the height-0 entries of their checkpoint tables (D9).
-/
def checkInterface : IO Nat := do
  let some records ← loadRange "tests/work/mainnet-genesis-headers/headers.txt" 0 13
      [(0, KnownAnswers.MedianTimePast.genesisHash)]
    | return 1
  let index := indexOf records 0 3
  let key := records[1]!.header.getHash
  let other := records[2]!.header.getHash
  let flagged := { entryAt records 0 1 with failedValid := true }
  let failedIndex : HeaderIndex := { index with failedBlocks := [key] }
  let updated := failedIndex.insert key flagged
  let mut failures := 0
  failures := failures + (← require "inserted entry shadows" (updated.lookup key == some flagged))
  failures := failures + (← require "other key unchanged" (updated.lookup other == some (entryAt records 0 2)))
  failures := failures + (← require "failed list unchanged" (updated.failedBlocks == [key]))
  failures := failures + (← require "unknown key" (index.lookup records[5]!.header.getHash == none))
  for network in [WorkNetwork.testnet, .regtest] do
    let tableGenesis := (checkpoints network).head?.bind Checkpoint.blockHash?
    failures := failures + (← require s!"genesis hash of {repr network}"
      (genesisHash? network == tableGenesis && tableGenesis.isSome))
  failures := failures + (← require "malformed literal" (hash256OfHex? "0x1a91" == none))
  IO.println s!"header index interface and genesis hashes: {failures} failures"
  return failures

/-! ### One step -/

/-- A placeholder full header for out-of-range array reads. Every read in this module is in range. -/
private instance : Inhabited BlockHeader := ⟨⟨default, none⟩⟩

/-- The expected result of one step.
It is an acceptance with its hash and added entries, a Core rejection with its observables and marks, or an adapter error. -/
inductive StepExpectation where
  /-- Acceptance with the display hash of the result and the added entries as display hash and height. -/
  | accept (hash : String) (added : List (String × Nat))
  /-- Rejection with Core's reason, denial-of-service score and reject code, and the display hashes that step 6 marks. -/
  | reject (reason : String) (dos code : Nat) (marked : List String)
  /-- An adapter error, by the name that `adapterName` gives. -/
  | adapter (name : String)

/-- The name of an adapter error, as the regtest fixture writes it. -/
def adapterName : HeaderAdapterError → String
  | .notWellFormed => "notWellFormed"
  | .contextual .shortView => "shortView"
  | .contextual (.nextWork .missingAncestor) => "nextWork missingAncestor"
  | .contextual e => s!"contextual {repr e}"
  | .adjustedTimeOutOfRange => "adjustedTimeOutOfRange"
  | .heightOutOfRange => "heightOutOfRange"

/-- The keys of an index without repeats. -/
def keysOf (index : HeaderIndex) : List Hash256 := (index.entries.map Prod.fst).eraseDups

/-- Display strings in ascending order. -/
def sorted (l : List String) : List String := l.mergeSort fun a b => decide (a ≤ b)

/-- The entries that the step added: keys that the result has and the input lacks, as display hash and height. -/
def addedBy (before after : HeaderIndex) : List (String × Nat) :=
  (keysOf after).filterMap fun key =>
    match before.lookup key, after.lookup key with
    | none, some entry => some (displayHex key, entry.height)
    | _, _ => none

/-- The keys whose `failedChild` the step changed from false to true, as display hashes. -/
def markedBy (before after : HeaderIndex) : List String :=
  (keysOf before).filterMap fun key =>
    match before.lookup key, after.lookup key with
    | some entry, some entry' => if !entry.failedChild && entry'.failedChild then some (displayHex key) else none
    | _, _ => none

/-- The step changed no field of an existing entry except `failedChild`, and kept the failed list. -/
def onlyMarksChanged (before after : HeaderIndex) : Bool :=
  after.failedBlocks == before.failedBlocks &&
    (keysOf before).all fun key =>
      match before.lookup key, after.lookup key with
      | some entry, some entry' => entry' == { entry with failedChild := entry'.failedChild }
      | _, _ => false

/-- Runs one step and compares its result with the expectation, including the change to the index. -/
def checkStep (label : String) (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
    (expected : StepExpectation) : IO Nat := do
  let (after, result) := acceptBlockHeader ctx index header
  let ok := match expected, result with
    | .accept hash added, .ok h =>
      displayHex h == hash && sorted (addedBy index after).unzip.1 == sorted added.unzip.1 &&
        (addedBy index after).all (added.contains ·) && markedBy index after == [] &&
        onlyMarksChanged index after
    | .reject reason dos code marked, .error (.rejection r) =>
      r.rejectReason == reason && r.dosScore == dos && r.rejectCode == code &&
        sorted (markedBy index after) == sorted marked && addedBy index after == [] &&
        onlyMarksChanged index after && (marked != [] || after == index)
    | .adapter name, .error (.adapter e) => adapterName e == name && after == index
    | _, _ => false
  unless ok do
    IO.eprintln s!"FAIL header step {label}: {repr result}, added {addedBy index after}, marked {markedBy index after}"
  return if ok then 0 else 1

/-- The network of a fixture request. -/
def networkOf : String → Except String WorkNetwork
  | "mainnet" => .ok .mainnet
  | "testnet" => .ok .testnet
  | "regtest" => .ok .regtest
  | other => .error s!"unknown network {other}"

/-- A nullable field of a fixture object. -/
def optField {α : Type} (j : Lean.Json) (key : String) (read : Lean.Json → Except String α) :
    Except String (Option α) := do
  match j.getObjValD key with
  | .null => return none
  | v => return some (← read v)

/-- The index of a fixture request.
The key of each entry is the hash of its 80-byte header.
Its predecessor is `hashPrevBlock`, except for an anchor and for an entry at height 0. -/
def fixtureIndex (request : Lean.Json) : Except String HeaderIndex := do
  let entries ← (← request.getObjVal? "index").getArr?
  let mut index : HeaderIndex := ⟨[], []⟩
  for e in entries do
    let bytes := (← KnownAnswers.Sha256Cavp.parseHex (← e.getObjValAs? String "header_hex")).toList
    let some (header, []) := DogeLib.Serialization.Codec.decode (α := PureBlockHeader) bytes | throw "expected an 80-byte header"
    let height ← (← e.getObjVal? "height").getNat?
    let anchor ← e.getObjValAs? Bool "anchor"
    let prev := if anchor || height == 0 then none else some header.hashPrevBlock
    index := index.insert header.getHash ⟨header, height, prev, ← e.getObjValAs? Bool "failed_valid",
      ← e.getObjValAs? Bool "failed_child", ← e.getObjValAs? Bool "scripts_valid"⟩
  let failed ← (← request.getObjVal? "failed_blocks").getArr?
  let failedBlocks ← failed.toList.mapM fun j => do KnownAnswers.Block.parseHash (← j.getStr?)
  return { index with failedBlocks := failedBlocks }

/-- The expectation for the first header of a fixture case.
A failure at position 0 gives the fixture's rejection or adapter error.
Otherwise the first step accepts.
It adds the first entry of the fixture's `added` list when the request's index lacks the first header's 80 bytes, and nothing otherwise. -/
def firstStepExpectation (case : Lean.Json) : Except String StepExpectation := do
  let request ← case.getObjVal? "request"
  let expected ← case.getObjVal? "expected"
  let failedAt ← optField expected "failed_at" Lean.Json.getNat?
  if failedAt == some 0 then
    if let some name ← optField expected "adapter_error" Lean.Json.getStr? then
      return .adapter name
    let reason ← expected.getObjValAs? String "reject_reason"
    let dos ← (← expected.getObjVal? "dos").getNat?
    let code ← (← expected.getObjVal? "reject_code").getNat?
    let marked ← (← (← expected.getObjVal? "marked_failed_child").getArr?).toList.mapM (·.getStr?)
    return .reject reason dos code marked
  let added ← (← (← expected.getObjVal? "added").getArr?).toList.mapM fun a => do
    return (← a.getObjValAs? String "hash", ← (← a.getObjVal? "height").getNat?)
  let headers ← (← request.getObjVal? "headers").getArr?
  let first ← headers[0]!.getStr?
  let indexHex ← (← (← request.getObjVal? "index").getArr?).toList.mapM (·.getObjValAs? String "header_hex")
  if indexHex.contains (first.take 160).toString then
    if headers.size != 1 then throw "a known first header in a case with several headers is not pinned"
    let lastHash ← expected.getObjValAs? String "last_hash"
    return .accept lastHash []
  let some entry := added.head? | throw "expected an added entry"
  return .accept entry.1 [entry]

/--
The regtest fixture (D83), one step for each case with at least one header.
Each step uses the fixture's request: the network, the read mode, the adjusted time, the checkpoint option, the index and the failed list.
`checkWellFormed` must accept each index, so that the theorems of stage 2 apply to it.

A case with one header compares the whole expectation of the fixture.
A case with several headers runs only its first header, with `firstStepExpectation`.
A known first header occurs only in cases with one header, and it accepts with the fixture's `last_hash`.
-/
def checkRegtestSteps : IO Nat := do
  let fixture ← KnownAnswers.Block.jsonFile "tests/block/regtest-header-sequences/sequences.json"
  let some cases := (fixture.getObjVal? "cases" >>= Lean.Json.getArr?).toOption
    | return (← require "regtest fixture cases" false)
  let mut failures := 0
  let mut count := 0
  for case in cases do
    let parsed : Except String (String × HeaderContext × HeaderIndex × Option BlockHeader × StepExpectation × Nat) := do
      let name ← case.getObjValAs? String "name"
      let request ← case.getObjVal? "request"
      let network ← networkOf (← request.getObjValAs? String "network")
      let mode ← match ← request.getObjValAs? String "mode" with
        | "base" => pure TxReadMode.base
        | "allow_witness" => pure TxReadMode.allowWitness
        | other => throw s!"unknown mode {other}"
      let adjusted ← (← request.getObjVal? "adjusted_time").getInt?
      let ctx : HeaderContext := ⟨network, Int64.ofInt adjusted, ← request.getObjValAs? Bool "checkpoints_enabled"⟩
      let index ← fixtureIndex request
      let headers ← (← request.getObjVal? "headers").getArr?
      match headers[0]? with
      | none => return (name, ctx, index, none, .adapter "", headers.size)
      | some first =>
        let bytes := (← KnownAnswers.Sha256Cavp.parseHex (← first.getStr?)).toList
        let header ← match BlockHeader.decodeComplete mode bytes with
          | .ok h => pure h
          | .error e => throw s!"{name}: cannot decode the first header: {repr e}"
        return (name, ctx, index, some header, ← firstStepExpectation case, headers.size)
    match parsed with
    | .error e => failures := failures + (← require s!"regtest fixture: {e}" false)
    | .ok (name, ctx, index, header?, expected, size) =>
      failures := failures + (← require s!"{name}: well-formed index" (checkWellFormed ctx.network index))
      if let some header := header? then
        count := count + 1
        failures := failures + (← checkStep s!"{name} ({size} headers)" ctx index header expected)
  IO.println s!"header step, regtest fixture: {count} first steps; {failures} failures"
  return failures

/-- The full header of a fixture line, decoded in the base mode with its AuxPoW payload. -/
def parseFullRange (text : String) (first count : Nat) : Except String (Array (Nat × BlockHeader)) := do
  let mut out : Array (Nat × BlockHeader) := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [heightText, hex] := line.splitOn " " | throw "expected height and header hex"
    let some height := heightText.toNat? | throw s!"bad height: {heightText}"
    if height != first + out.size then throw s!"unexpected height: {height}"
    let bytes := (← KnownAnswers.Sha256Cavp.parseHex hex).toList
    match BlockHeader.decodeComplete .base bytes with
    | .ok h =>
      if let some (_, previous) := out.back? then
        unless h.pure.hashPrevBlock == previous.pure.getHash do throw s!"height {height}: predecessor link"
      out := out.push (height, h)
    | .error e => throw s!"height {height}: {repr e}"
  if out.size != count then throw s!"expected {count} headers, got {out.size}"
  return out

/-- Reads a full-header fixture with `parseFullRange`, and requires the display hash at the anchor height. -/
def loadFullRange (path : System.FilePath) (first count anchor : Nat) (hash : String) :
    IO (Option (Array Record × Array BlockHeader)) := do
  match parseFullRange (← IO.FS.readFile path) first count with
  | .error e =>
    IO.eprintln s!"FAIL header step fixture {path}: {e}"
    return none
  | .ok out =>
    let headers := out.map (·.2)
    unless displayHex headers[anchor - first]!.pure.getHash == hash do
      IO.eprintln s!"FAIL header step anchor {anchor} in {path}"
      return none
    return some (out.map fun (height, h) => ⟨height, h.pure⟩, headers)

/-- The context of a mainnet step: the header time as the adjusted time, so that check 6 passes, and the checkpoint option. -/
def mainnetCtx (header : PureBlockHeader) (checkpoints : Bool) : HeaderContext :=
  ⟨.mainnet, timeOf header, checkpoints⟩

/-- Accepts the real header at `candidate` against the index of the records from `lo` to the candidate, with the anchor at `lo`.
The expected added entry is the candidate's display hash at its height. -/
def acceptReal (label : String) (records : Array Record) (headers : Array BlockHeader) (first lo candidate : Nat)
    (checkpoints : Bool) : IO Nat := do
  let index := indexOf records (lo - first) (candidate - first)
  let header := headers[candidate - first]!
  let hash := displayHex header.pure.getHash
  checkStep s!"{label} {candidate}" (mainnetCtx header.pure checkpoints) index header
    (.accept hash [(hash, candidate)])

/--
Mainnet steps with real full headers, expected from chain acceptance and hand derivation from D33 and design record 0008.

- Genesis: the genesis header against an empty index inserts an entry at height 0 (item 2).
  Against an index whose genesis entry has `failedValid`, it accepts and changes nothing (item 1).
  The header at height 1 then extends the genesis entry.
- The retarget at 144960 and the first DigiShield height 145000, each against the records from the anchor 144719 up to its predecessor.
  The index has no table hash, so check 4 passes with checkpoints enabled.
- Checkpoint 145000 as an anchor above the records 144719 to 144989.
  The header at 144990 fails check 4 with checkpoints enabled: `bad-fork-prior-to-checkpoint`, DoS 100 and `REJECT_CHECKPOINT` 0x43 (D33, line 3099, and D84).
  With checkpoints disabled, it is accepted.
- The anchor raised to 144720: the retarget at 144960 lacks the ancestor 240 below its predecessor, the adapter error `nextWork missingAncestor`.
- AuxPoW activation: each candidate from 371331 to 371340 against the records from the anchor 371320, with checkpoints enabled.
  The candidate 371337 is the first AuxPoW header, and step 2 checks its payload.
- `BIP66Height` 1034383, `BIP65Height` 3464751 and the heights below them, each against the 20 records below it.
- The header at `BIP66Height` with the base version 2 (`0x00620102`).
  The AuxPoW payload commits to the real header's hash.
  So step 2 rejects the changed header with `high-hash`, DoS 50 and `REJECT_INVALID`, before check 7 runs (D33, lines 3224 and 3225).
-/
def checkMainnetSteps : IO Nat := do
  let mut failures := 0
  -- Genesis.
  let some genesisRecords ← loadRange "tests/work/mainnet-genesis-headers/headers.txt" 0 13
      [(0, KnownAnswers.MedianTimePast.genesisHash)]
    | return 1
  let genesisHeader : BlockHeader := ⟨genesisRecords[0]!.header, none⟩
  let genesisHex := displayHex genesisRecords[0]!.header.getHash
  failures := failures + (← checkStep "mainnet genesis into an empty index" (mainnetCtx genesisHeader.pure true)
    ⟨[], []⟩ genesisHeader (.accept genesisHex [(genesisHex, 0)]))
  let flagged := (indexOf genesisRecords 0 1).insert genesisRecords[0]!.header.getHash
    { entryAt genesisRecords 0 0 with failedValid := true }
  failures := failures + (← checkStep "mainnet flagged genesis" (mainnetCtx genesisHeader.pure true)
    flagged genesisHeader (.accept genesisHex []))
  failures := failures + (← acceptReal "mainnet" genesisRecords (genesisRecords.map (⟨·.header, none⟩)) 0 0 1 true)
  -- Retarget, DigiShield and checkpoint 145000.
  let first := 144719
  let some records ← loadRange "tests/work/mainnet-headers/headers.txt" first 312
      [(145000, "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72")]
    | return failures + 1
  let headers := records.map (⟨·.header, none⟩ : Record → BlockHeader)
  failures := failures + (← acceptReal "mainnet retarget" records headers first first 144960 true)
  failures := failures + (← acceptReal "mainnet DigiShield" records headers first first 145000 true)
  let at145000 := records[145000 - first]!
  let withCheckpoint := (indexOf records 0 (144990 - first)).insert at145000.header.getHash
    ⟨at145000.header, 145000, none, false, false, false⟩
  let fork := headers[144990 - first]!
  failures := failures + (← checkStep "mainnet fork below checkpoint 145000" (mainnetCtx fork.pure true)
    withCheckpoint fork (.reject "bad-fork-prior-to-checkpoint" 100 0x43 []))
  let forkHex := displayHex fork.pure.getHash
  failures := failures + (← checkStep "mainnet fork with checkpoints disabled" (mainnetCtx fork.pure false)
    withCheckpoint fork (.accept forkHex [(forkHex, 144990)]))
  let raised := indexOf records 1 (144960 - first)
  failures := failures + (← checkStep "mainnet retarget above a raised anchor"
    (mainnetCtx headers[144960 - first]!.pure true) raised headers[144960 - first]!
    (.adapter "nextWork missingAncestor"))
  -- AuxPoW activation.
  let some (auxRecords, auxHeaders) ← loadFullRange "tests/block/mainnet-auxpow-activation-full-headers/headers.txt"
      371320 21 371337 checkpoint371337
    | return failures + 1
  for candidate in [371331:371341] do
    failures := failures + (← acceptReal "mainnet AuxPoW activation" auxRecords auxHeaders 371320 371320 candidate true)
  failures := failures + (← require "AuxPoW payload at 371337" auxHeaders[371337 - 371320]!.auxpow.isSome)
  -- BIP66 and BIP65.
  let some (records66, headers66) ← loadFullRange "tests/block/mainnet-bip66-full-headers/headers.txt"
      1032483 1908 1032483 bip66CommentHash
    | return failures + 1
  let some (records65, headers65) ← loadFullRange "tests/block/mainnet-bip65-full-headers/headers.txt"
      3464739 22 3464751 bip65CommentHash
    | return failures + 1
  for candidate in [1034382, 1034383] do
    failures := failures + (← acceptReal "mainnet BIP66" records66 headers66 1032483 (candidate - 20) candidate true)
  for candidate in [3464750, 3464751] do
    failures := failures + (← acceptReal "mainnet BIP65" records65 headers65 3464739 (candidate - 20) candidate true)
  let real := headers66[1034383 - 1032483]!
  failures := failures + (← require "version at 1034383" (real.pure.nVersion == 0x00620103))
  let old := { real with pure := { real.pure with nVersion := 0x00620102 } }
  failures := failures + (← checkStep "mainnet base version 2 at BIP66Height" (mainnetCtx old.pure true)
    (indexOf records66 (1034363 - 1032483) (1034383 - 1032483)) old (.reject "high-hash" 50 0x10 []))
  IO.println s!"header step, mainnet: 23 steps; {failures} failures"
  return failures

/--
Synthetic steps at the height bound of decision 17, with the mined regtest headers `genesis` and `a` of the fixture (D83).
`a` links to `genesis` and passes step 2.

- With `genesis` as an anchor at 2147483646, the step returns `heightOutOfRange` (design record 0008, section 7.1).
- With `genesis` as an anchor at 2147483645, the candidate is at 2147483646.
  Its view has one entry, so the median time past returns the adapter error `shortView`.

`checkWellFormed` accepts `a` at height 1 above `genesis` at height 0, and an anchor at 2147483646.
It rejects `a` at height 2 above `genesis` at height 0, an anchor at 2147483647, and a failed list whose member lacks `failedValid` (design record 0008, section 5.5).
-/
def checkSyntheticSteps : IO Nat := do
  let fixture ← KnownAnswers.Block.jsonFile "tests/block/regtest-header-sequences/sequences.json"
  let read (name : String) : Except String PureBlockHeader := do
    let hex ← ((← fixture.getObjVal? "headers").getObjValD name).getObjValAs? String "header_hex"
    let bytes := (← KnownAnswers.Sha256Cavp.parseHex hex).toList
    let some (header, []) := DogeLib.Serialization.Codec.decode (α := PureBlockHeader) bytes | throw s!"{name}: expected 80 bytes"
    return header
  let .ok genesis := read "genesis" | return (← require "regtest genesis header" false)
  let .ok a := read "a" | return (← require "regtest header a" false)
  let ctx : HeaderContext := ⟨.regtest, Int64.ofInt 1296688702, false⟩
  let anchorAt (height : Nat) : HeaderIndex := (⟨[], []⟩ : HeaderIndex).insert genesis.getHash
    ⟨genesis, height, none, false, false, false⟩
  let mut failures := 0
  failures := failures + (← checkStep "predecessor at 2147483646" ctx (anchorAt 2147483646) ⟨a, none⟩
    (.adapter "heightOutOfRange"))
  failures := failures + (← checkStep "predecessor at 2147483645" ctx (anchorAt 2147483645) ⟨a, none⟩
    (.adapter "shortView"))
  let chain : HeaderIndex := (anchorAt 0).insert a.getHash ⟨a, 1, some genesis.getHash, false, false, false⟩
  let skipped : HeaderIndex := (anchorAt 0).insert a.getHash ⟨a, 2, some genesis.getHash, false, false, false⟩
  failures := failures + (← require "well-formed chain" (checkWellFormed .regtest chain))
  failures := failures + (← require "anchor at 2147483646" (checkWellFormed .regtest (anchorAt 2147483646)))
  failures := failures + (← require "height gap" (!checkWellFormed .regtest skipped))
  failures := failures + (← require "anchor at 2147483647" (!checkWellFormed .regtest (anchorAt 2147483647)))
  failures := failures + (← require "failed member without failedValid"
    (!checkWellFormed .regtest { chain with failedBlocks := [a.getHash] }))
  IO.println s!"header step, height bound and well-formed checks: 2 steps and 5 checks; {failures} failures"
  return failures

end KnownAnswers.HeaderSequence

/-- Named checks for the block-index model, in alphabetical order. -/
def KnownAnswers.HeaderSequence.checks : List (String × IO Nat) := [
  ("acceptHeightBound", KnownAnswers.HeaderSequence.checkSyntheticSteps),
  ("acceptMainnet", KnownAnswers.HeaderSequence.checkMainnetSteps),
  ("acceptRegtest", KnownAnswers.HeaderSequence.checkRegtestSteps),
  ("digishieldRange", KnownAnswers.HeaderSequence.checkDigishieldRange),
  ("genesisRange", KnownAnswers.HeaderSequence.checkGenesisRange),
  ("interface", KnownAnswers.HeaderSequence.checkInterface),
  ("laterRanges", KnownAnswers.HeaderSequence.checkLaterRanges)
]
