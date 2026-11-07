import DogeLib.Block
import DogeLib.Work
import KnownAnswers.Block
import KnownAnswers.MedianTimePast

/-!
## Contextual header validation

Known answers for `contextualCheckBlockHeader` (design record 0006, stage 3), through the compiled code.
Core's `ContextualCheckBlockHeader` is in `src/validation.cpp`, lines 3066 to 3119, at Core `e0a1c15` (SOURCES.md, D33).

The expected results come from three sources, never from `contextualCheckBlockHeader`:

- Chain acceptance of real mainnet headers.
  Mainnet accepted each header, so checks 1, 2, 3, 5 and 7 pass for it.
  The adjusted time and the known checkpoints are not chain data.
  Each case chooses them, and the expected results of checks 4 and 6 follow by hand from D33.
- Mutations of real headers, with the expected result derived by hand from D33 and the pinned parameters.
- Synthetic testnet, regtest and mainnet views, with the required `nBits` derived by hand from `GetNextWorkRequired` (D17, lines 32 to 88) and `CalculateDogecoinNextWorkRequired` (D6, lines 41 to 87).

The real headers are in five fixtures: `tests/work/mainnet-genesis-headers`, `tests/work/mainnet-headers` and the three ranges under `tests/block`.
Their READMEs record the sources and the anchor hashes.
These checks do not establish proof of work, AuxPoW validity or agreement with compiled Core.
-/

namespace KnownAnswers.ContextualCheck
open DogeLib DogeLib.Block DogeLib.Work DogeLib.Serialization
open KnownAnswers.Block (require)
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- Compares the full result, including the error constructor and its fields. -/
private instance : BEq (Except ContextualHeaderError Unit) where
  beq a b := match a, b with
    | .ok (), .ok () => true
    | .error x, .error y => decide (x = y)
    | _, _ => false

/-- A placeholder header for out-of-range array reads. Every read in this module is in range. -/
private instance : Inhabited PureBlockHeader := ⟨⟨0, Hash256.zero, Hash256.zero, 0, 0, 0⟩⟩

/-- A short display of a result for failure messages. -/
def show? : Except ContextualHeaderError Unit → String
  | .ok () => "ok"
  | .error e => s!"{repr e}"

/-- Compares a result with its expected value, and reports the label on failure. -/
def expect (label : String) (got expected : Except ContextualHeaderError Unit) : IO Nat := do
  if got == expected then return 0
  IO.eprintln s!"FAIL contextual check {label}: got {show? got}, expected {show? expected}"
  return 1

/-! ### Fixtures -/

/-- A real header with its height. -/
structure Record where
  /-- The height that the fixture line records. -/
  height : Nat
  /-- The decoded 80-byte pure header. -/
  header : PureBlockHeader

/-- A placeholder record for out-of-range array reads. Every read in this module is in range. -/
private instance : Inhabited Record := ⟨⟨0, default⟩⟩

/-- Parses a fixture of `height hex` lines that must start at `first` and hold exactly `count` consecutive heights.
It decodes each 80-byte pure header, and requires each header after the first to link to its predecessor's hash. -/
def parseRange (text : String) (first count : Nat) : Except String (Array Record) := do
  let mut records : Array Record := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [heightText, hex] := line.splitOn " " | throw "expected height and header hex"
    let some height := heightText.toNat? | throw s!"bad height: {heightText}"
    if height != first + records.size then throw s!"unexpected height: {height}"
    let bytes ← parseHex hex
    if bytes.size != 80 then throw s!"height {height}: expected 80 bytes"
    let some (header, rest) := Codec.decode (α := PureBlockHeader) bytes.toList
      | throw s!"height {height}: cannot decode"
    unless rest.isEmpty do throw s!"height {height}: trailing bytes"
    if let some previous := records.back? then
      unless header.hashPrevBlock == previous.header.getHash do
        throw s!"height {height}: predecessor link"
    records := records.push ⟨height, header⟩
  if records.size != count then throw s!"expected {count} headers, got {records.size}"
  return records

/-- Reads a fixture with `parseRange`, and requires the display-order hash at each anchor height. -/
def loadRange (path : System.FilePath) (first count : Nat) (anchors : List (Nat × String)) :
    IO (Option (Array Record)) := do
  match parseRange (← IO.FS.readFile path) first count with
  | .error e =>
    IO.eprintln s!"FAIL contextual check fixture {path}: {e}"
    return none
  | .ok records =>
    for (height, hash) in anchors do
      let display := toHex ⟨records[height - first]!.header.getHash.displayBytes.toArray⟩
      unless display == hash do
        IO.eprintln s!"FAIL contextual check anchor {height} in {path}: {display}"
        return none
    return some records

/-- The view entry of a real header. -/
def entryOf (r : Record) : BlockIndex := ⟨r.height, r.header.nTime, r.header.nBits⟩

/-- The newest-first view of the predecessors of the candidate at `candidate`, down to the first fixture height. -/
def viewBelow (records : Array Record) (first candidate : Nat) : List BlockIndex :=
  (List.range (candidate - first)).map fun i => entryOf records[candidate - 1 - first - i]!

/-- The adjusted time equal to the header time, so that check 6 passes with 7200 seconds to spare. -/
def timeOf (h : PureBlockHeader) : Int64 := Int64.ofNat h.nTime.toNat

/-- The mainnet checkpoint heights up to `height`: the known set of a node whose block index holds the chain up to `height`. -/
def knownUpTo (height : Nat) : List Nat := (checkpointHeights .mainnet).filter (· ≤ height)

/--
Chain acceptance over a fixture: every candidate with at least 11 predecessors in the fixture passes.
Each case uses the header time as the adjusted time.
It runs twice, with no last checkpoint, and with checkpoints enabled and every table height up to the candidate known.
In the second run, `GetLastCheckpoint` (D67) returns the greatest of those heights, which is at most the candidate height, so check 4 passes.
Returns the number of failures and the number of candidates.
-/
def checkAcceptance (label : String) (records : Array Record) (first : Nat) : IO (Nat × Nat) := do
  let mut failures := 0
  let mut count := 0
  for i in [11:records.size] do
    let r := records[i]!
    let view := viewBelow records first r.height
    count := count + 1
    failures := failures + (← expect s!"{label} acceptance at {r.height}"
      (contextualCheckBlockHeader .mainnet r.header view (timeOf r.header) none) (.ok ()))
    failures := failures + (← expect s!"{label} acceptance with checkpoints at {r.height}"
      (contextualCheckBlockHeaderWithCheckpoints .mainnet r.header view (timeOf r.header) true
        (knownUpTo r.height)) (.ok ()))
  return (failures, count)

/-! ### Mainnet heights 0 to 12 and 144719 to 145030 -/

/--
The genesis range: every candidate from 1 to 12 with its full view down to genesis.
Each real header passes.
The time of the median comes from the hand-derived table in `tests/work/mainnet-genesis-headers/README.md`.
A header time equal to the median fails with `time-too-old` (D33, line 3103), and one second later passes.
Below height 240 on mainnet, the required work is the predecessor's `nBits`, whatever the header time (D17, line 72).
So a change of time does not change check 3.
-/
def checkGenesisRange : IO Nat := do
  let some records ← loadRange "tests/work/mainnet-genesis-headers/headers.txt" 0 13
      [(0, KnownAnswers.MedianTimePast.genesisHash)]
    | return 1
  let mut failures := 0
  for (h, medianHeight) in KnownAnswers.MedianTimePast.genesisMedianHeights do
    let c := h + 1
    if c > 12 then continue
    let r := records[c]!
    let view := viewBelow records 0 c
    let median := records[medianHeight]!.header.nTime
    failures := failures + (← expect s!"genesis acceptance at {c}"
      (contextualCheckBlockHeader .mainnet r.header view (timeOf r.header) none) (.ok ()))
    let atMedian := { r.header with nTime := median }
    failures := failures + (← expect s!"genesis time equal to the median at {c}"
      (contextualCheckBlockHeader .mainnet atMedian view (timeOf r.header) none) (.error .timeTooOld))
    let afterMedian := { r.header with nTime := median + 1 }
    failures := failures + (← expect s!"genesis time one second after the median at {c}"
      (contextualCheckBlockHeader .mainnet afterMedian view (timeOf r.header) none) (.ok ()))
  IO.println s!"contextual check genesis range: 12 candidates, 3 cases each; {failures} failures"
  return failures

/--
The range 144719 to 145030: every candidate from 144730 passes.
The retarget at candidate 144960 reads the entry 240 below its predecessor, the first fixture header (D17, lines 77 to 85).
A view of the 241 entries from 144959 down to 144719 gives the same result as the full view (`contextualCheck_congr_prefix`).
A view of 240 entries lacks that ancestor, and the expected result is the adapter error `nextWork missingAncestor`.
-/
def checkDigishieldRange : IO Nat := do
  let some records ← loadRange "tests/work/mainnet-headers/headers.txt" 144719 312
      [(145000, "cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72")]
    | return 1
  let (failures, count) ← checkAcceptance "144719-145030" records 144719
  let mut failures := failures
  let r := records[144960 - 144719]!
  let view := viewBelow records 144719 144960
  failures := failures + (← require "retarget view has 241 entries" (view.length == 241))
  failures := failures + (← expect "retarget at 144960 with 240 entries"
    (contextualCheckBlockHeader .mainnet r.header (view.take 240) (timeOf r.header) none)
    (.error (.nextWork .missingAncestor)))
  failures := failures + (← expect "retarget at 144960 with 11 entries"
    (contextualCheckBlockHeader .mainnet r.header (view.take 11) (timeOf r.header) none)
    (.error (.nextWork .missingAncestor)))
  IO.println s!"contextual check 144719-145030: {count} acceptances, 2 short retarget views; {failures} failures"
  return failures

/-! ### Mainnet AuxPoW activation, heights 371320 to 371340 -/

/-- The hash of checkpoint 371337 (`src/chainparams.cpp`, D9, line 185). -/
def checkpoint371337 : String := "60323982f9c5ff1b5a954eac9dc1269352835f47c2c5222691d80f0d50dcf053"

/--
Checks 1, 2, 3, 4 and 6 and the order of the checks around AuxPoW activation at 371337 (D14, line 135).
The real versions are `0x00620002` up to 371336 except `0x00000002` at 371330, and `0x00620102` at 371337.
The expectations follow D33 and the records of D14:

- From 371337, `fAllowLegacyBlocks` is false. Version 1 or 2 is legacy and fails with `late-legacy-block`.
- Below 371337, `fAllowLegacyBlocks` is true. A version with the AuxPoW flag fails with `early-auxpow-block`, and a legacy version passes.
- `nBits` plus or minus one fails with `bad-diffbits`.
- Check 4 compares the candidate height with the greatest known table height (D67), with `<`.
- Check 6 accepts a header time equal to the adjusted time plus 7200 and rejects one second more.
-/
def checkAuxpowActivation : IO Nat := do
  let first := 371320
  let some records ← loadRange "tests/block/mainnet-auxpow-activation-headers/headers.txt" first 21
      [(371337, checkpoint371337)]
    | return 1
  let (failures, count) ← checkAcceptance "371320-371340" records first
  let mut failures := failures
  let at37 := records[371337 - first]!.header
  let view37 := viewBelow records first 371337
  let at36 := records[371336 - first]!.header
  let view36 := viewBelow records first 371336
  let run (h : PureBlockHeader) (view : List BlockIndex) (t : Int64) (c : Option Nat) :=
    contextualCheckBlockHeader .mainnet h view t c
  -- The real versions that the expectations name.
  failures := failures + (← require "version at 371337" (at37.nVersion == 0x00620102))
  failures := failures + (← require "version at 371336" (at36.nVersion == 0x00620002))
  failures := failures + (← require "version at 371330" (records[371330 - first]!.header.nVersion == 2))
  -- Checks 1 and 2.
  for v in [(1 : UInt32), 2] do
    failures := failures + (← expect s!"legacy version {v} at 371337"
      (run { at37 with nVersion := v } view37 (timeOf at37) none) (.error .lateLegacyBlock))
    failures := failures + (← expect s!"legacy version {v} at 371336"
      (run { at36 with nVersion := v } view36 (timeOf at36) none) (.ok ()))
  failures := failures + (← expect "chain ID without AuxPoW flag at 371337"
    (run { at37 with nVersion := 0x00620002 } view37 (timeOf at37) none) (.ok ()))
  failures := failures + (← expect "AuxPoW flag at 371336"
    (run { at36 with nVersion := 0x00620102 } view36 (timeOf at36) none) (.error .earlyAuxpowBlock))
  -- Check 3.
  failures := failures + (← expect "nBits plus one at 371337"
    (run { at37 with nBits := at37.nBits + 1 } view37 (timeOf at37) none) (.error .badDiffbits))
  failures := failures + (← expect "nBits minus one at 371337"
    (run { at37 with nBits := at37.nBits - 1 } view37 (timeOf at37) none) (.error .badDiffbits))
  -- Check 4.
  let withCheckpoints (h : PureBlockHeader) (view : List BlockIndex) (enabled : Bool) (known : List Nat) :=
    contextualCheckBlockHeaderWithCheckpoints .mainnet h view (timeOf h) enabled known
  failures := failures + (← expect "last checkpoint at the candidate height"
    (withCheckpoints at37 view37 true [371337]) (.ok ()))
  failures := failures + (← expect "last checkpoint one above the candidate height"
    (withCheckpoints at36 view36 true [371337]) (.error .badForkPriorToCheckpoint))
  failures := failures + (← expect "last checkpoint far above the candidate height"
    (withCheckpoints at37 view37 true [145000, 371337, 450000]) (.error .badForkPriorToCheckpoint))
  failures := failures + (← expect "no known checkpoint"
    (withCheckpoints at37 view37 true []) (.ok ()))
  failures := failures + (← expect "known height outside the table"
    (withCheckpoints at36 view36 true [371400, 500000]) (.ok ()))
  failures := failures + (← expect "checkpoints disabled with a higher known checkpoint"
    (withCheckpoints at37 view37 false [450000]) (.ok ()))
  -- Check 6.
  let time := (at37.nTime.toNat : Int)
  let adjusted (t : Int) : Int64 := Int64.ofInt t
  failures := failures + (← expect "header time equal to adjusted time plus 7200"
    (run at37 view37 (adjusted (time - 7200)) none) (.ok ()))
  failures := failures + (← expect "header time one second above adjusted time plus 7200"
    (run at37 view37 (adjusted (time - 7201)) none) (.error .timeTooNew))
  failures := failures + (← expect "negative adjusted time"
    (run at37 view37 (adjusted (-1)) none) (.error .timeTooNew))
  failures := failures + (← expect "least adjusted time"
    (run at37 view37 Int64.minValue none) (.error .timeTooNew))
  failures := failures + (← expect "adjusted time INT64_MAX - 7200"
    (run at37 view37 (adjusted 9223372036854768607) none) (.ok ()))
  failures := failures + (← expect "adjusted time INT64_MAX - 7199"
    (run at37 view37 (adjusted 9223372036854768608) none) (.error .adjustedTimeOutOfRange))
  failures := failures + (← expect "adjusted time INT64_MAX"
    (run at37 view37 Int64.maxValue none) (.error .adjustedTimeOutOfRange))
  -- Order: each header fails two checks, and the result is the first.
  failures := failures + (← expect "legacy version and bad nBits"
    (run { at37 with nVersion := 1, nBits := at37.nBits + 1 } view37 (timeOf at37) none)
    (.error .lateLegacyBlock))
  failures := failures + (← expect "AuxPoW flag and bad nBits"
    (run { at36 with nVersion := 0x00620102, nBits := at36.nBits + 1 } view36 (timeOf at36) none)
    (.error .earlyAuxpowBlock))
  failures := failures + (← expect "bad nBits and a fork below a checkpoint"
    (withCheckpoints { at36 with nBits := at36.nBits + 1 } view36 true [371337]) (.error .badDiffbits))
  failures := failures + (← expect "fork below a checkpoint and time zero"
    (contextualCheckBlockHeaderWithCheckpoints .mainnet { at36 with nTime := 0 } view36 (timeOf at36) true
      [371337]) (.error .badForkPriorToCheckpoint))
  -- Adapter errors.
  failures := failures + (← expect "view of 10 entries at 371337"
    (run at37 (view37.take 10) (timeOf at37) none) (.error .shortView))
  failures := failures + (← expect "empty view"
    (run at37 [] (timeOf at37) none) (.error .emptyView))
  failures := failures + (← expect "unlinked view"
    (run at37 (view37.take 1 ++ view37.drop 2) (timeOf at37) none)
    (.error (.invalidView .inconsistentHeights)))
  IO.println s!"contextual check 371320-371340: {count} acceptances and the activation mutations; {failures} failures"
  return failures

/-! ### Mainnet `BIP66Height` and `BIP65Height` -/

/-- The hash in the comments on `BIP34Hash` and `BIP66Height` (`src/chainparams.cpp`, D14, lines 85 and 87).
It is the hash of the block at height 1032483, 1900 blocks below `BIP66Height`, not of the block at 1034383. -/
def bip66CommentHash : String := "80d1364201e5df97e696c03bdd24dc885e8617b9de51e453c10a4f629b1e797a"

/-- The hash in the comment on `BIP65Height` (D14, line 86): the block at height 3464751. -/
def bip65CommentHash : String := "34cd2cbba4ba366f47e5aa0db5f02c19eba2adf679ceb6653ac003bdc9a0ef1f"

/--
Check 7 and the order of checks 5, 6 and 7 at mainnet `BIP66Height` 1034383 and `BIP65Height` 3464751 (D14, lines 86 and 87).
The base version is the signed `nVersion % 256` (D10, lines 88 to 95), and the reason prints it with `%08x` (D33, line 3115).
The real versions are `0x00620103` at 1034382, 1034383 and 3464750, and `0x00620104` at 3464751.
-/
def checkVersionThresholds : IO Nat := do
  let first66 := 1032483
  let some records66 ← loadRange "tests/block/mainnet-bip66-headers/headers.txt" first66 1908
      [(1032483, bip66CommentHash)]
    | return 1
  let first65 := 3464739
  let some records65 ← loadRange "tests/block/mainnet-bip65-headers/headers.txt" first65 22
      [(3464751, bip65CommentHash)]
    | return 1
  let (f66, n66) ← checkAcceptance "1032483-1034390" records66 first66
  let (f65, n65) ← checkAcceptance "3464739-3464760" records65 first65
  let mut failures := f66 + f65
  let case (records : Array Record) (first c : Nat) (v : UInt32) (expected : Except ContextualHeaderError Unit) :
      IO Nat := do
    let h := { records[c - first]!.header with nVersion := v }
    expect s!"version {v} at {c}"
      (contextualCheckBlockHeader .mainnet h (viewBelow records first c) (timeOf h) none) expected
  failures := failures + (← require "version at 1034382" (records66[1034382 - first66]!.header.nVersion == 0x00620103))
  failures := failures + (← require "version at 1034383" (records66[1034383 - first66]!.header.nVersion == 0x00620103))
  failures := failures + (← require "version at 3464750" (records65[3464750 - first65]!.header.nVersion == 0x00620103))
  failures := failures + (← require "version at 3464751" (records65[3464751 - first65]!.header.nVersion == 0x00620104))
  -- BIP66Height: base version 2 passes below it and fails from it. The AuxPoW flag and chain ID do not change the base version.
  failures := failures + (← case records66 first66 1034382 0x00620102 (.ok ()))
  failures := failures + (← case records66 first66 1034383 0x00620102 (.error (.badVersion 2)))
  failures := failures + (← case records66 first66 1034383 0x00620103 (.ok ()))
  failures := failures + (← case records66 first66 1034383 0x00000003 (.ok ()))
  failures := failures + (← case records66 first66 1034383 0x00000000 (.error (.badVersion 0)))
  -- 0x80000003 is −2147483645 as int32, and its truncated remainder by 256 is −253.
  failures := failures + (← case records66 first66 1034383 0x80000003 (.error (.badVersion (-253))))
  -- 0x80000000 is −2147483648, a multiple of 256, so the base version is 0.
  failures := failures + (← case records66 first66 1034383 0x80000000 (.error (.badVersion 0)))
  -- BIP65Height: base version 3 passes below it and fails from it.
  failures := failures + (← case records65 first65 3464750 0x00620103 (.ok ()))
  failures := failures + (← case records65 first65 3464750 0x00620102 (.error (.badVersion 2)))
  failures := failures + (← case records65 first65 3464751 0x00620103 (.error (.badVersion 3)))
  failures := failures + (← case records65 first65 3464751 0x00620104 (.ok ()))
  failures := failures + (← case records65 first65 3464751 0x00620105 (.ok ()))
  -- 0xffffffff is −1 as int32, so the base version is −1.
  failures := failures + (← case records65 first65 3464751 0xffffffff (.error (.badVersion (-1))))
  -- 0x80620104 is −2141060860 as int32: 2141060860 = 8363518 * 256 + 252, so the base version is −252.
  failures := failures + (← case records65 first65 3464751 0x80620104 (.error (.badVersion (-252))))
  -- Order: a bad version with a time at most the median, and with a time too far in the future.
  let h83 := records66[1034383 - first66]!.header
  let view83 := viewBelow records66 first66 1034383
  failures := failures + (← expect "time zero and base version 2 at 1034383"
    (contextualCheckBlockHeader .mainnet { h83 with nTime := 0, nVersion := 0x00620102 } view83 (timeOf h83) none)
    (.error .timeTooOld))
  failures := failures + (← expect "time too new and base version 2 at 1034383"
    (contextualCheckBlockHeader .mainnet { h83 with nVersion := 0x00620102 } view83
      (Int64.ofInt ((h83.nTime.toNat : Int) - 7201)) none)
    (.error .timeTooNew))
  IO.println s!"contextual check BIP66 and BIP65 ranges: {n66 + n65} acceptances and the version mutations; {failures} failures"
  return failures

/-! ### Reject reasons -/

/-- Core's reject reasons (D33, lines 3077, 3086, 3090, 3099, 3104, 3108 and 3115), with `%08x` of the base version worked out by hand. -/
def reasonCases : List (ContextualHeaderError × Option String) := [
  (.lateLegacyBlock, some "late-legacy-block"),
  (.earlyAuxpowBlock, some "early-auxpow-block"),
  (.badDiffbits, some "bad-diffbits"),
  (.badForkPriorToCheckpoint, some "bad-fork-prior-to-checkpoint"),
  (.timeTooOld, some "time-too-old"),
  (.timeTooNew, some "time-too-new"),
  (.badVersion 2, some "bad-version(0x00000002)"),
  (.badVersion 3, some "bad-version(0x00000003)"),
  (.badVersion 0, some "bad-version(0x00000000)"),
  (.badVersion 255, some "bad-version(0x000000ff)"),
  -- −253 as a 32-bit two's-complement pattern is 2^32 − 253 = 0xffffff03.
  (.badVersion (-253), some "bad-version(0xffffff03)"),
  (.badVersion (-252), some "bad-version(0xffffff04)"),
  (.badVersion (-1), some "bad-version(0xffffffff)"),
  (.badVersion (-255), some "bad-version(0xffffff01)"),
  (.emptyView, none),
  (.shortView, none),
  (.nextWork .missingAncestor, none),
  (.adjustedTimeOutOfRange, none)
]

/-- Checks `ContextualHeaderError.rejectReason` for every case of `reasonCases`. -/
def checkReasons : IO Nat := do
  let mut failures := 0
  for (e, expected) in reasonCases do
    failures := failures + (← require s!"reject reason of {repr e}" (e.rejectReason == expected))
  IO.println s!"contextual check reject reasons: {reasonCases.length} cases; {failures} failures"
  return failures

/-! ### Synthetic views -/

/-- A header with zero hashes and nonce. No contextual check reads those fields (`contextualCheck_congr_header`). -/
def mk (version time bits : UInt32) : PureBlockHeader := ⟨version, Hash256.zero, Hash256.zero, time, bits, 0⟩

/-- The synthetic time of height `h`: 1000000 plus 60 seconds a block. -/
def timeAt (h : Nat) : UInt32 := UInt32.ofNat (1000000 + 60 * h)

/-- A newest-first view of `count` entries from height `top` down, with `timeAt` times and the bits that `bitsAt` gives. -/
def chain (top count : Nat) (bitsAt : Nat → UInt32) : List BlockIndex :=
  (List.range count).map fun i => ⟨top - i, timeAt (top - i), bitsAt (top - i)⟩

/-- Compact `powLimit` of mainnet and testnet: 2^236 − 1 has 30 bytes, and its top three bytes are `0x0fffff` (D14, lines 88 and 248). -/
def testnetLimit : UInt32 := 0x1e0fffff

/-- Compact `powLimit` of regtest: 2^255 − 1 has 32 bytes, and its top three bytes are `0x7fffff` (D14, line 392). -/
def regtestLimit : UInt32 := 0x207fffff

/-- A testnet compact value below the limit. It is the result of `GetCompact` for its own target, because its first mantissa byte is not zero and its sign bit is clear. -/
def testnetBits : UInt32 := 0x1e0ffff0

/-- One synthetic case: a label, a network, a header, a view, an adjusted time, a last checkpoint and the expected result. -/
structure Case where
  /-- The label in a failure message. -/
  label : String
  /-- The network. -/
  network : WorkNetwork
  /-- The candidate header. -/
  header : PureBlockHeader
  /-- The predecessor view. -/
  view : List BlockIndex
  /-- The expected result. -/
  expected : Except ContextualHeaderError Unit

/--
Synthetic testnet cases.
Every view entry has `testnetBits` unless the case says otherwise, and the times rise 60 seconds a block.
A candidate time 60 seconds after the predecessor passes checks 5 and 6, with the adjusted time equal to the candidate time.

- From predecessor height 145000, every block is a retarget with an interval of one (D17, line 50).
  With 60 seconds between the last two entries, DigiShield gives `60 + (60 - 60) / 8 = 60`, so the target and the compact value stay the same (D6, lines 41 to 87).
- `AllowDigishieldMinDifficultyForBlock` needs a predecessor at height 157500 or more, and a candidate time more than 120 seconds after it (D6, lines 26 to 39).
  Then the required value is `testnetLimit`.
- Below candidate 145000, at a height that is not a retarget, a candidate time more than 120 seconds after the predecessor requires `testnetLimit` (D17, lines 60 and 61).
  Otherwise the walk goes back from the predecessor and stops at the first entry that meets one of three conditions (D17, lines 65 to 69).
  Its `nBits` is not `testnetLimit`, or its height is a multiple of 240, or it has no predecessor.
  The walk returns the `nBits` of that entry, which can be `testnetLimit` at a multiple of 240.
-/
def testnetCases : List Case :=
  let base := fun (_ : Nat) => testnetBits
  let at_ (c : Nat) (version : UInt32) (delay : Nat) (bits : UInt32) :=
    mk version (UInt32.ofNat (1000000 + 60 * (c - 1) + delay)) bits
  [
    -- AuxPoW activation at 158100 (D14, line 298).
    ⟨"testnet AuxPoW version at 158100", .testnet, at_ 158100 0x00620102 60 testnetBits, chain 158099 11 base, .ok ()⟩,
    ⟨"testnet legacy version at 158100", .testnet, at_ 158100 1 60 testnetBits, chain 158099 11 base,
      .error .lateLegacyBlock⟩,
    ⟨"testnet AuxPoW flag at 158099", .testnet, at_ 158099 0x00620102 60 testnetBits, chain 158098 11 base,
      .error .earlyAuxpowBlock⟩,
    ⟨"testnet chain ID without AuxPoW flag at 158099", .testnet, at_ 158099 0x00620002 60 testnetBits,
      chain 158098 11 base, .ok ()⟩,
    -- Candidate 157500: the predecessor is below 157500, so no minimum-difficulty rule applies.
    ⟨"testnet 157500, delay 120, retarget value", .testnet, at_ 157500 0x00620002 120 testnetBits,
      chain 157499 11 base, .ok ()⟩,
    ⟨"testnet 157500, delay 121, retarget value", .testnet, at_ 157500 0x00620002 121 testnetBits,
      chain 157499 11 base, .ok ()⟩,
    ⟨"testnet 157500, delay 121, limit", .testnet, at_ 157500 0x00620002 121 testnetLimit,
      chain 157499 11 base, .error .badDiffbits⟩,
    -- Candidate 157501: the predecessor is at 157500, so a delay of more than 120 seconds requires the limit.
    ⟨"testnet 157501, delay 120, retarget value", .testnet, at_ 157501 0x00620002 120 testnetBits,
      chain 157500 11 base, .ok ()⟩,
    ⟨"testnet 157501, delay 120, limit", .testnet, at_ 157501 0x00620002 120 testnetLimit,
      chain 157500 11 base, .error .badDiffbits⟩,
    ⟨"testnet 157501, delay 121, limit", .testnet, at_ 157501 0x00620002 121 testnetLimit,
      chain 157500 11 base, .ok ()⟩,
    ⟨"testnet 157501, delay 121, retarget value", .testnet, at_ 157501 0x00620002 121 testnetBits,
      chain 157500 11 base, .error .badDiffbits⟩,
    -- Candidate 100001: (100000 + 1) % 240 = 161, so it is not a retarget.
    ⟨"testnet 100001, delay 121, limit", .testnet, at_ 100001 2 121 testnetLimit, chain 100000 11 base, .ok ()⟩,
    ⟨"testnet 100001, delay 120, limit", .testnet, at_ 100001 2 120 testnetLimit, chain 100000 11 base,
      .error .badDiffbits⟩,
    ⟨"testnet 100001, delay 120, last value", .testnet, at_ 100001 2 120 testnetBits, chain 100000 11 base,
      .ok ()⟩,
    ⟨"testnet 100001, delay 121, last value", .testnet, at_ 100001 2 121 testnetBits, chain 100000 11 base,
      .error .badDiffbits⟩,
    -- The entries at 100000 and 99999 have the limit. Their heights are not multiples of 240, so the walk returns the value at 99998.
    ⟨"testnet 100001, walk past two limit entries", .testnet, at_ 100001 2 120 testnetBits,
      chain 100000 11 (fun h => if h ≥ 99999 then testnetLimit else testnetBits), .ok ()⟩,
    ⟨"testnet 100001, walk past two limit entries, limit", .testnet, at_ 100001 2 120 testnetLimit,
      chain 100000 11 (fun h => if h ≥ 99999 then testnetLimit else testnetBits), .error .badDiffbits⟩,
    -- Testnet BIP66Height 708658 and BIP65Height 1854705 (D14, lines 246 and 247).
    ⟨"testnet base version 2 at 708657", .testnet, at_ 708657 0x00620102 60 testnetBits, chain 708656 11 base,
      .ok ()⟩,
    ⟨"testnet base version 2 at 708658", .testnet, at_ 708658 0x00620102 60 testnetBits, chain 708657 11 base,
      .error (.badVersion 2)⟩,
    ⟨"testnet base version 3 at 1854704", .testnet, at_ 1854704 0x00620103 60 testnetBits, chain 1854703 11 base,
      .ok ()⟩,
    ⟨"testnet base version 3 at 1854705", .testnet, at_ 1854705 0x00620103 60 testnetBits, chain 1854704 11 base,
      .error (.badVersion 3)⟩
  ]

/--
Synthetic regtest cases.
Every entry has `regtestLimit`, and the times rise 60 seconds a block.

- From candidate 10, the DigiShield record has a timespan of one second, so the interval is one (D14, lines 425 to 428).
  The bounds are `1 - 1 / 4 = 1` and `1 + 1 / 2 = 1`, so the modulated timespan is 1, and the target stays the same (D6, lines 41 to 87).
- Below candidate 10, the interval is 14400 (D14, lines 392 to 397), and minimum-difficulty blocks are allowed.
  Without a delay of more than 2 seconds, the walk passes every entry with the limit and stops at height 0, which returns the limit.
-/
def regtestCases : List Case :=
  let limit := fun (_ : Nat) => regtestLimit
  let at_ (c : Nat) (version : UInt32) (delay : Nat) :=
    mk version (UInt32.ofNat (1000000 + 60 * (c - 1) + delay)) regtestLimit
  [
    -- AuxPoW activation at 20 (D14, line 432).
    ⟨"regtest AuxPoW version at 20", .regtest, at_ 20 0x00620102 60, chain 19 11 limit, .ok ()⟩,
    ⟨"regtest legacy version at 20", .regtest, at_ 20 1 60, chain 19 11 limit, .error .lateLegacyBlock⟩,
    ⟨"regtest AuxPoW flag at 19", .regtest, at_ 19 0x00620102 60, chain 18 11 limit, .error .earlyAuxpowBlock⟩,
    ⟨"regtest legacy version at 19", .regtest, at_ 19 1 60, chain 18 11 limit, .ok ()⟩,
    -- Below candidate 10: the walk reaches genesis.
    ⟨"regtest 5 without delay", .regtest, at_ 5 1 1, chain 4 5 limit, .ok ()⟩,
    ⟨"regtest 5 without genesis", .regtest, at_ 5 1 1, chain 4 4 limit, .error .shortView⟩,
    -- BIP66Height 1251 and BIP65Height 1351 (D14, lines 390 and 391).
    ⟨"regtest base version 2 at 1250", .regtest, at_ 1250 0x00620102 60, chain 1249 11 limit, .ok ()⟩,
    ⟨"regtest base version 2 at 1251", .regtest, at_ 1251 0x00620102 60, chain 1250 11 limit,
      .error (.badVersion 2)⟩,
    ⟨"regtest base version 3 at 1251", .regtest, at_ 1251 0x00620103 60, chain 1250 11 limit, .ok ()⟩,
    ⟨"regtest base version 3 at 1350", .regtest, at_ 1350 0x00620103 60, chain 1349 11 limit, .ok ()⟩,
    ⟨"regtest base version 3 at 1351", .regtest, at_ 1351 0x00620103 60, chain 1350 11 limit,
      .error (.badVersion 3)⟩,
    ⟨"regtest base version 4 at 1351", .regtest, at_ 1351 0x00620104 60, chain 1350 11 limit, .ok ()⟩
  ]

/--
Synthetic mainnet cases.

- Below candidate 145000, at a height that is not a retarget, the required value is the predecessor's raw `nBits` (D17, line 72).
  `0x1c7fff00` and `0x1d007fff` encode the same target, `0x7fff * 256^26`.
  Check 3 compares the 32-bit values, so the second encoding fails (D33, line 3089).
- Check 5 takes the median of 11 times out of order.
  The times of heights 99 down to 89 are 50, 1000, 30, 900, 70, 800, 10, 700, 90, 600 and 20.
  Sorted, they are 10, 20, 30, 50, 70, 90, 600, 700, 800, 900 and 1000, so index 5 is 90.
  The sixth entry has the time 800, so a rule that reads it gives a different result.
-/
def mainnetCases : List Case :=
  let bits := (0x1c7fff00 : UInt32)
  let flat := chain 99 11 (fun _ => bits)
  let times : List UInt32 := [50, 1000, 30, 900, 70, 800, 10, 700, 90, 600, 20]
  let shuffled := (List.range 11).zip times |>.map fun (i, t) => (⟨99 - i, t, bits⟩ : BlockIndex)
  [
    ⟨"mainnet same target, canonical encoding", .mainnet, mk 1 (timeAt 100) bits, flat, .ok ()⟩,
    ⟨"mainnet same target, other encoding", .mainnet, mk 1 (timeAt 100) 0x1d007fff, flat, .error .badDiffbits⟩,
    ⟨"mainnet median 90, time 90", .mainnet, mk 1 90 bits, shuffled, .error .timeTooOld⟩,
    ⟨"mainnet median 90, time 91", .mainnet, mk 1 91 bits, shuffled, .ok ()⟩,
    ⟨"mainnet median 90, time 800", .mainnet, mk 1 800 bits, shuffled, .ok ()⟩
  ]

/-- Runs the synthetic cases with the adjusted time equal to the header time and no last checkpoint. -/
def checkSynthetic : IO Nat := do
  let cases := testnetCases ++ regtestCases ++ mainnetCases
  let mut failures := 0
  for c in cases do
    failures := failures + (← expect c.label
      (contextualCheckBlockHeader c.network c.header c.view (timeOf c.header) none) c.expected)
  IO.println s!"contextual check synthetic: {cases.length} cases; {failures} failures"
  return failures

end KnownAnswers.ContextualCheck

/-- Named checks for contextual header validation, in alphabetical order. -/
def KnownAnswers.ContextualCheck.checks : List (String × IO Nat) := [
  ("auxpowActivation", KnownAnswers.ContextualCheck.checkAuxpowActivation),
  ("digishieldRange", KnownAnswers.ContextualCheck.checkDigishieldRange),
  ("genesisRange", KnownAnswers.ContextualCheck.checkGenesisRange),
  ("reasons", KnownAnswers.ContextualCheck.checkReasons),
  ("synthetic", KnownAnswers.ContextualCheck.checkSynthetic),
  ("versionThresholds", KnownAnswers.ContextualCheck.checkVersionThresholds)
]
