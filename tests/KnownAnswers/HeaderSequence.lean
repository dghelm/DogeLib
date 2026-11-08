import DogeLib.Block
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

end KnownAnswers.HeaderSequence

/-- Named checks for the block-index model, in alphabetical order. -/
def KnownAnswers.HeaderSequence.checks : List (String × IO Nat) := [
  ("digishieldRange", KnownAnswers.HeaderSequence.checkDigishieldRange),
  ("genesisRange", KnownAnswers.HeaderSequence.checkGenesisRange),
  ("interface", KnownAnswers.HeaderSequence.checkInterface),
  ("laterRanges", KnownAnswers.HeaderSequence.checkLaterRanges)
]
