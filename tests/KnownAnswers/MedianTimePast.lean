import DogeLib.Work
import KnownAnswers.Work

/-!
## Median time past

`GetMedianTimePast` is in `src/chain.h`, lines 284-298, at Core `e0a1c15` (SOURCES.md, D18).
It collects the times of at most 11 entries, sorts them and returns the element at index `count / 2`.
`ContextualCheckBlockHeader` rejects a header whose time is at most the median of its predecessor (D33, lines 3103-3104).

The expected values come from three sources, never from `medianTimePast`:

- Real mainnet headers at heights 0-12, with a median table derived by hand in `tests/work/mainnet-genesis-headers/README.md`.
- The 312 real mainnet headers of `tests/work/mainnet-headers`, with chain acceptance and four medians derived by hand.
- Synthetic views with hand-derived medians: even counts, times out of order, equal times and the UInt32 bounds.

Chain acceptance says that each real header's time is greater than the median of its predecessor.
These checks do not establish proof of work, full header validity or agreement with compiled Core.
-/

namespace KnownAnswers.MedianTimePast

open DogeLib.Work
open KnownAnswers.Work.MainnetHeaders (Header parseHeader parseHeaders)
open KnownAnswers.Sha256Cavp (toHex)

/-- Compares the full result, including the adapter error. -/
private instance : BEq (Except MedianTimeError Int) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => decide (x = y)
    | _, _ => false

/-- A placeholder header for out-of-range array reads. Every read in this module is in range. -/
private instance : Inhabited Header := ⟨⟨0, 0, ⟨List.replicate 32 0, by simp⟩, ⟨List.replicate 32 0, by simp⟩, 0, 0, 0, .empty⟩⟩

/-- Check a condition and report its label on failure. Returns the number of failures. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL median time past: {label}"
  return 1

/-- The view entry of a fixture header. -/
def entryOf (header : Header) : BlockIndex := ⟨header.height, header.time, header.bits⟩

/-- The newest-first view of the headers at heights `low` to `high` of a fixture that starts at height `first`. -/
def viewOf (headers : Array Header) (first low high : Nat) : List BlockIndex :=
  ((List.range (high + 1 - low)).map fun i => entryOf headers[high - first - i]!)

/-- The widened time of a fixture header, as `GetBlockTime` gives it (D10, lines 73-76). -/
def timeOf (header : Header) : Int := header.time.toNat

/-!
### Mainnet heights 0-12
-/

/-- The display-order hash of the mainnet genesis block (`src/chainparams.cpp`, D9, lines 160 and 182). -/
def genesisHash : String := "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"

/-- For each height `h` from 0 to 12: the height whose time is the median of the view from `h` down to 0.
Derived by hand in `tests/work/mainnet-genesis-headers/README.md`: the times increase strictly, and index `count / 2` of `min(11, h + 1)` times selects that height. -/
def genesisMedianHeights : List (Nat × Nat) :=
  [(0, 0), (1, 1), (2, 1), (3, 2), (4, 2), (5, 3), (6, 3), (7, 4), (8, 4), (9, 5), (10, 5),
    (11, 6), (12, 7)]

/-- Parses exactly the 13 headers at heights 0 to 12. -/
def parseGenesisHeaders (text : String) : Except String (Array Header) := do
  let mut headers := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let [heightText, hex] := line.splitOn " " | throw "expected height and header hex"
    let some height := heightText.toNat? | throw s!"bad height: {heightText}"
    if height != headers.size then throw s!"unexpected height: {height}"
    headers := headers.push (← parseHeader height hex)
  if headers.size != 13 then throw s!"expected 13 headers, got {headers.size}"
  return headers

/-- Checks the fixture at heights 0-12: hashes, links, the genesis hash, the hand-derived medians, chain acceptance and short views. -/
def checkGenesisRange : IO Nat := do
  let headers ← match parseGenesisHeaders
      (← IO.FS.readFile "tests/work/mainnet-genesis-headers/headers.txt") with
    | .ok headers => pure headers
    | .error e =>
      IO.eprintln s!"FAIL mainnet genesis headers: {e}"
      return 1
  let mut failures := 0
  -- Hashes and links: D10 layout, D9 genesis hash.
  failures := failures + (← require "genesis previous hash is null"
    (headers[0]!.prev.val == List.replicate 32 0))
  failures := failures + (← require "genesis hash (D9)"
    (toHex ⟨headers[0]!.digest.toList.reverse.toArray⟩ == genesisHash))
  for h in [1:13] do
    failures := failures + (← require s!"predecessor link at height {h}"
      (headers[h]!.prev.val == headers[h - 1]!.digest.toList))
    -- The hand derivation of the median table needs strictly increasing times.
    failures := failures + (← require s!"strictly increasing time at height {h}"
      (headers[h - 1]!.time < headers[h]!.time))
  -- Hand-derived medians.
  for (h, medianHeight) in genesisMedianHeights do
    failures := failures + (← require s!"median at height {h}"
      (medianTimePast (viewOf headers 0 0 h) == .ok (timeOf headers[medianHeight]!)))
  -- Chain acceptance: each accepted header's time exceeds the median of its predecessor (D33, line 3103).
  for h in [1:13] do
    let accepted := match medianTimePast (viewOf headers 0 0 (h - 1)) with
      | .ok median => decide (median < timeOf headers[h]!)
      | .error _ => false
    failures := failures + (← require s!"chain acceptance at height {h}" accepted)
  -- Short views: the walk needs min(11, h + 1) entries.
  failures := failures + (← require "height 5 without genesis is short"
    (medianTimePast (viewOf headers 0 1 5) == .error .shortView))
  failures := failures + (← require "height 12 with ten entries is short"
    (medianTimePast (viewOf headers 0 3 12) == .error .shortView))
  failures := failures + (← require "height 12 with eleven entries equals the full view"
    (medianTimePast (viewOf headers 0 2 12) == medianTimePast (viewOf headers 0 0 12)))
  IO.println s!"mainnet genesis headers: 13 hashes, 12 links, genesis hash; {genesisMedianHeights.length} medians, 12 acceptances; {failures} failures"
  return failures

/-!
### Mainnet heights 144719-145030

The view at predecessor height `p` holds the fixture headers from `p` down to 144719.
From `p = 144729`, the view has the 11 entries that the walk needs.
Below that height, the view lacks history, and the expected result is `shortView`.

Four windows have times out of order such that the median differs from the time of the sixth entry.
The heights below come by hand from the times in `tests/work/mainnet-headers/headers.txt`.
At 144980 and 144981, the times are 1395093332 and 1395093331, and every other time in the two windows is further from them.
At 145010 and 145011, the times are 1395095166 and 1395095154, with the same property.
So index 5 of each sorted window is one of the two swapped times.
It is the smaller time when five other times of the window are smaller, and the larger time when four are.
-/

/-- Predecessor heights with times out of order, and the height whose time is the median.
For predecessor 144985, the window is 144975-144985. Five times are below both swapped times, so index 5 is the smaller swapped time, at 144981.
For predecessor 144986, the window is 144976-144986. Four times are below both, so index 5 is the larger swapped time, at 144980.
Predecessors 145015 and 145016 follow the same pattern with heights 145011 and 145010. -/
def outOfOrderMedians : List (Nat × Nat) :=
  [(144985, 144981), (144986, 144980), (145015, 145011), (145016, 145010)]

/-- Checks short views, chain acceptance for every candidate from 144730 and the four hand-derived medians. -/
def checkMainnetRange : IO Nat := do
  let headers ← match parseHeaders (← IO.FS.readFile "tests/work/mainnet-headers/headers.txt") with
    | .ok headers => pure headers
    | .error e =>
      IO.eprintln s!"FAIL mainnet headers: {e}"
      return 1
  let first := 144719
  let headerAt (h : Nat) := headers[h - first]!
  let mut failures := 0
  let mut short := 0
  let mut accepted := 0
  for p in [first:first + 10] do
    short := short + 1
    failures := failures + (← require s!"short view at {p}"
      (medianTimePast (viewOf headers first first p) == .error .shortView))
  for c in [first + 11:first + 312] do
    accepted := accepted + 1
    let ok := match medianTimePast (viewOf headers first first (c - 1)) with
      | .ok median => decide (median < timeOf (headerAt c))
      | .error _ => false
    failures := failures + (← require s!"chain acceptance at {c}" ok)
  for (p, medianHeight) in outOfOrderMedians do
    failures := failures + (← require s!"out-of-order median at {p}"
      (medianTimePast (viewOf headers first first p) == .ok (timeOf (headerAt medianHeight))))
    -- The sixth entry differs from the median, so a rule that reads it fails this check.
    failures := failures + (← require s!"sixth entry differs at {p}"
      (timeOf (headerAt (p - 5)) != timeOf (headerAt medianHeight)))
  unless short == 10 && accepted == 301 do
    IO.eprintln "FAIL mainnet median: unexpected counts"
    failures := failures + 1
  IO.println s!"mainnet headers median: {short} short views, {accepted} acceptances, {outOfOrderMedians.length} out-of-order medians; {failures} failures"
  return failures

/-!
### Synthetic views
-/

/-- A newest-first view with consecutive heights from `top` down, and the given times. -/
def synthetic (top : Nat) (times : List UInt32) : List BlockIndex :=
  times.zipIdx.map fun (time, i) => ⟨top - i, time, 0x1e0ffff0⟩

/-- Hand-derived cases: a label, a view and the expected result. -/
def syntheticCases : List (String × List BlockIndex × Except MedianTimeError Int) := [
  -- Count 2 at height 1. Sorted 100, 200. Index 1 is the upper median 200, not 100 or the mean 150.
  ("even count 2", synthetic 1 [100, 200], .ok 200),
  -- Count 4 at height 3. Sorted 10, 20, 30, 40. Index 2 is 30, not the lower median 20 or the mean 25.
  ("even count 4, out of order", synthetic 3 [40, 10, 30, 20], .ok 30),
  -- Count 10 at height 9. Sorted 1..10. Index 5 is 6.
  ("even count 10, reversed", synthetic 9 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], .ok 6),
  -- Count 11 at height 20. Sorted 1, 2, 3, 5, 7, 9, 60, 70, 80, 90, 100. Index 5 is 9. The sixth entry is 80.
  ("count 11, out of order", synthetic 20 [5, 100, 3, 90, 7, 80, 1, 70, 9, 60, 2], .ok 9),
  -- Count 11 at height 14 of a 15-entry view. The last four entries are outside the walk.
  -- Sorted first 11: 10..110. Index 5 is 60. The extra entries are below every collected time.
  ("count 11 of 15 entries", synthetic 14 [110, 100, 90, 80, 70, 60, 50, 40, 30, 20, 10, 0, 0, 0, 0],
    .ok 60),
  -- Equal times: every index gives 7.
  ("equal times", synthetic 10 [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7], .ok 7),
  -- Count 2 with the UInt32 bounds. The widened value 4294967295 stays positive, so it is the upper median.
  ("UInt32 bounds", synthetic 1 [0, 0xffffffff], .ok 4294967295),
  -- Count 1 at height 0.
  ("genesis only", synthetic 0 [1386325540], .ok 1386325540),
  -- Errors of the adapter.
  ("empty view", [], .error .emptyView),
  ("short view at height 5", synthetic 5 [1, 2, 3, 4, 5], .error .shortView),
  ("short view at height 20", synthetic 20 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], .error .shortView),
  ("inconsistent heights", [⟨5, 1, 0⟩, ⟨3, 1, 0⟩], .error (.invalidView .inconsistentHeights)),
  ("height out of range", [⟨2147483647, 1, 0⟩], .error (.invalidView .heightOutOfRange))
]

/-- Runs the hand-derived synthetic cases. -/
def checkSynthetic : IO Nat := do
  let mut failures := 0
  for (label, view, expected) in syntheticCases do
    let got := medianTimePast view
    unless got == expected do
      IO.eprintln s!"FAIL median time past {label}: got {repr got}, expected {repr expected}"
      failures := failures + 1
  IO.println s!"median time past synthetic: {syntheticCases.length} cases, {failures} failures"
  return failures

end KnownAnswers.MedianTimePast

/-- Named checks for median-time-past known answers, in alphabetical order. -/
def KnownAnswers.MedianTimePast.checks : List (String × IO Nat) := [
  ("genesisRange", KnownAnswers.MedianTimePast.checkGenesisRange),
  ("mainnetRange", KnownAnswers.MedianTimePast.checkMainnetRange),
  ("synthetic", KnownAnswers.MedianTimePast.checkSynthetic)
]
