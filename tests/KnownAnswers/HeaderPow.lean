import DogeLib.Block
import KnownAnswers.Common

/-!
## Header proof of work

Known answers for `checkAuxPowProofOfWork` and `checkBlockHeader`, the specification of Core's `CheckAuxPowProofOfWork` (D6) and `CheckBlockHeader` (D33).
`tests/block/README.md` records the provenance of the fixtures.

Every expected acceptance comes from the chain: each header is in Dogecoin's mainnet chain, so Core accepted it.
The six AuxPoW headers are at checkpoint heights.
The 312 headers at heights 144719 to 145030 connect to checkpoint 145000.
The three headers of `mainnet.json` are at heights 1, 3000 and 4000.

Each expected rejection comes from Core's order of checks in D6, lines 89 to 125, and names the line that the case reaches.
A mutation of a field that the digest covers is expected to fail its target.
A random 256-bit digest meets a target `t` with probability about `t / 2 ^ 256`.
That is about `2 ^ -20` for the initial target of the header at height 1, and about `2 ^ -33` at heights 3000 and 4000.
For every other target here it is below `2 ^ -41`.
The argument is for these test expectations only, and no theorem relies on it.
-/

namespace KnownAnswers.HeaderPow
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Block (require jsonFile)

/-- The line of `src/dogecoin.cpp` whose `return error` each error stands for (D6). -/
def errorLine : CheckPowError → Nat
  | .wrongChainId => 96
  | .auxpowFlagWithoutPayload => 104
  | .proofOfWorkFailed => 108
  | .payloadWithoutFlag => 116
  | .auxProofOfWorkFailed => 119
  | .auxPow _ => 122

/-- A description of a result for failure messages. -/
def describe : Except CheckPowError Unit → String
  | .ok () => "accepted"
  | .error e => s!"line {errorLine e}: {repr e}"

/-- Check that `result` equals `expected` and report both on failure. -/
def expect (label : String) (result expected : Except CheckPowError Unit) : IO Nat := do
  let same := match result, expected with
    | .ok (), .ok () => true
    | .error e, .error e' => e == e'
    | _, _ => false
  if same then return 0
  IO.eprintln s!"FAIL header PoW: {label}: got {describe result}, expected {describe expected}"
  return 1

/-- The compact encoding of mainnet's `powLimit`, `0x00000fff…ff` (D14 line 88): the easiest valid target. -/
def easiestBits : UInt32 := 0x1e0fffff

/-- A valid compact encoding of the target 1, which no digest of a real header meets. -/
def hardestBits : UInt32 := 0x03000001

/-- A compact target in hexadecimal, as Core prints `nBits`. -/
def hexBits (b : UInt32) : String := String.ofList (Nat.toDigits 16 b.toNat)

/-- The version with its chain ID bits replaced by `id`. -/
def withChainId (v id : UInt32) : UInt32 := (v &&& (0xffff : UInt32)) ||| (id <<< (16 : UInt32))

/-- Read the 312 raw headers of `tests/work/mainnet-headers/headers.txt` with their heights. -/
def readRangeHeaders : IO (Array (Nat × PureBlockHeader)) := do
  let text ← IO.FS.readFile "tests/work/mainnet-headers/headers.txt"
  let mut out := #[]
  for line in (text.splitOn "\n").filter (!·.isEmpty) do
    let [height, hex] := line.splitOn " " | throw (IO.userError s!"bad header line {line}")
    let some height := height.toNat? | throw (IO.userError s!"bad height {height}")
    let raw ← match parseHex hex with
      | .ok b => pure b.toList
      | .error e => throw (IO.userError e)
    let some (h, []) := Codec.decode (α := PureBlockHeader) raw
      | throw (IO.userError s!"header at {height} is not 80 bytes")
    out := out.push (height, h)
  return out

/-- Read the three pure headers of `tests/block/mainnet.json` with their heights. -/
def readMainnetHeaders : IO (Array (Nat × PureBlockHeader)) := do
  let rows ← match (← jsonFile "tests/block/mainnet.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  rows.mapM fun row => do
    let parsed : Except String (Nat × List UInt8) := do
      return (← (← row.getObjVal? "height").getNat?, (← parseHex (← row.getObjValAs? String "header")).toList)
    let (height, raw) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    let some (h, []) := Codec.decode (α := PureBlockHeader) raw
      | throw (IO.userError s!"header at {height} is not 80 bytes")
    return (height, h)

/-- Read the six full headers of `tests/block/auxpow-headers.json` in the witness-allowed mode, as Core's network and disk readers do. -/
def readAuxPowHeaders : IO (Array (Nat × BlockHeader)) := do
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  rows.mapM fun row => do
    let parsed : Except String (Nat × List UInt8) := do
      return (← (← row.getObjVal? "height").getNat?, (← parseHex (← row.getObjValAs? String "block")).toList)
    let (height, block) ← match parsed with
      | .ok p => pure p
      | .error e => throw (IO.userError e)
    match BlockHeader.read .allowWitness block with
    | .ok (h, _) => return (height, h)
    | .error _ => throw (IO.userError s!"AuxPoW header {height} does not read")

/-- The three mainnet records that `GetConsensus` selects (D14): heights 0, 145000 and 371337. -/
def mainnetRecords : List (Nat × AuxPowParams) :=
  [0, 145000, 371337].map fun height => (height, getAuxPowParams .mainnet height.toUInt32)

/-- Pre-AuxPoW headers: every recorded header is accepted, and a few mutations are rejected at the expected lines. -/
def checkLegacy : IO Nat := do
  let range ← readRangeHeaders
  let blocks ← readMainnetHeaders
  let mut failures ← require "312 range headers" (range.size == 312)
  let start ← IO.monoNanosNow
  for (height, h) in range do
    failures := failures + (← expect s!"height {height}" (checkBlockHeader .mainnet ⟨h, none⟩) (.ok ()))
  let stop ← IO.monoNanosNow
  let micros := (stop - start) / 1000
  IO.println s!"header PoW: {range.size} pre-AuxPoW headers, {micros / 1000} ms, {micros / range.size} µs per header"
  for (height, h) in blocks do
    failures := failures + (← expect s!"block {height}" (checkBlockHeader .mainnet ⟨h, none⟩) (.ok ()))
  for (height, h) in range.toList.take 4 ++ blocks.toList do
    let label := s!"height {height}"
    -- The nonce is part of the digest input, so the digest fails the unchanged target (line 108).
    failures := failures + (← expect s!"{label}, nNonce + 1"
      (checkBlockHeader .mainnet ⟨{ h with nNonce := h.nNonce + 1 }, none⟩) (.error .proofOfWorkFailed))
    -- Version 0x00620002 is not legacy, has the right chain ID and no flag, so the header's own digest is checked (item 13).
    -- The version is part of the digest input, so the digest fails the target (line 108).
    failures := failures + (← expect s!"{label}, chain ID 0x62 without flag"
      (checkBlockHeader .mainnet ⟨{ h with nVersion := withChainId h.nVersion 0x62 }, none⟩) (.error .proofOfWorkFailed))
    -- A version that is not legacy, with chain ID 0x63, fails the chain ID test first (line 96).
    failures := failures + (← expect s!"{label}, chain ID 0x63"
      (checkBlockHeader .mainnet ⟨{ h with nVersion := withChainId h.nVersion 0x63 }, none⟩) (.error .wrongChainId))
    -- The same header with the AuxPoW flag set and no payload is rejected at line 104.
    failures := failures + (← expect s!"{label}, flag without payload"
      (checkBlockHeader .mainnet ⟨{ h with nVersion := withChainId h.nVersion 0x62 ||| 0x100 }, none⟩)
      (.error .auxpowFlagWithoutPayload))
    for (recordHeight, p) in mainnetRecords do
      failures := failures + (← expect s!"{label}, record of height {recordHeight}"
        (checkAuxPowProofOfWork p ⟨h, none⟩) (.ok ()))
  return failures

/-- AuxPoW headers: all six are accepted, and each mutation is rejected at the expected line. -/
def checkAuxPow : IO Nat := do
  let headers ← readAuxPowHeaders
  let mut failures ← require "six AuxPoW headers" (headers.size == 6)
  let start ← IO.monoNanosNow
  for (height, h) in headers do
    failures := failures + (← expect s!"AuxPoW {height}" (checkBlockHeader .mainnet h) (.ok ()))
  let stop ← IO.monoNanosNow
  IO.println s!"header PoW: {headers.size} AuxPoW headers, {(stop - start) / 1000000} ms"
  for (height, h) in headers do
    let label := s!"AuxPoW {height}"
    let some a := h.auxpow | throw (IO.userError s!"{label}: no payload")
    -- An observation, not an expected value: whether the parent's digest meets the parent's own target.
    let ownTarget := Work.checkProofOfWork a.parentBlock.powHash a.parentBlock.nBits (getAuxPowParams .mainnet 0).toRetargetParams
    IO.println s!"header PoW: {label}: parent nBits {hexBits a.parentBlock.nBits}, child nBits {hexBits h.pure.nBits}, parent digest meets its own target: {ownTarget}"
    -- Each parent mutation changes the 80 parent bytes, so the recomputed digest fails the unchanged child target (line 119).
    -- `AuxPow.check` reads no parent field except the Merkle root and the version, so line 119 is the only place to reject.
    let parents : List (String × PureBlockHeader) := [
      ("parent nBits = easiest", { a.parentBlock with nBits := easiestBits }),
      ("parent nBits = child nBits", { a.parentBlock with nBits := h.pure.nBits }),
      ("parent nBits + 1", { a.parentBlock with nBits := a.parentBlock.nBits + 1 }),
      ("parent nNonce + 1", { a.parentBlock with nNonce := a.parentBlock.nNonce + 1 }),
      ("parent nTime + 1", { a.parentBlock with nTime := a.parentBlock.nTime + 1 })]
    for (name, parent) in parents do
      failures := failures + (← expect s!"{label}, {name}"
        (checkBlockHeader .mainnet { h with auxpow := some { a with parentBlock := parent } }) (.error .auxProofOfWorkFailed))
    -- No digest meets the target 1 (line 119).
    failures := failures + (← expect s!"{label}, child nBits = target 1"
      (checkBlockHeader .mainnet { h with pure := { h.pure with nBits := hardestBits } }) (.error .auxProofOfWorkFailed))
    -- The easiest target still accepts the unchanged parent digest.
    -- The child's hash changes, so its chain root no longer occurs in the coinbase script (D55 line 120).
    failures := failures + (← expect s!"{label}, child nBits = easiest"
      (checkBlockHeader .mainnet { h with pure := { h.pure with nBits := easiestBits } })
      (.error (.auxPow .missingChainRoot)))
    -- Chain ID 0x63 fails the chain ID test on mainnet, where fStrictChainId is set (line 96).
    let other := { h with pure := { h.pure with nVersion := withChainId h.pure.nVersion 0x63 } }
    failures := failures + (← expect s!"{label}, chain ID 0x63" (checkBlockHeader .mainnet other) (.error .wrongChainId))
    -- Testnet has fStrictChainId false, so the chain ID test passes, and so does the parent's digest.
    -- The changed version changes the child's hash, so its chain root no longer occurs (D55 line 120).
    failures := failures + (← expect s!"{label}, chain ID 0x63 on testnet" (checkBlockHeader .testnet other)
      (.error (.auxPow .missingChainRoot)))
    -- The two in-memory mismatches (lines 104 and 116).
    failures := failures + (← expect s!"{label}, payload removed" (checkBlockHeader .mainnet { h with auxpow := none })
      (.error .auxpowFlagWithoutPayload))
    failures := failures + (← expect s!"{label}, flag cleared"
      (checkBlockHeader .mainnet { h with pure := { h.pure with nVersion := h.pure.nVersion &&& ~~~0x100 } })
      (.error .payloadWithoutFlag))
    for (recordHeight, p) in mainnetRecords do
      failures := failures + (← expect s!"{label}, record of height {recordHeight}" (checkAuxPowProofOfWork p h) (.ok ()))
  return failures

/-- Run all header proof-of-work known answers. -/
def check : IO Nat := do
  let failures := (← checkLegacy) + (← checkAuxPow)
  IO.println s!"header PoW known answers: {failures} failures"
  return failures

end KnownAnswers.HeaderPow

/-- Named checks for header proof of work, in alphabetical order. -/
def KnownAnswers.HeaderPow.checks : List (String × IO Nat) := [
  ("header PoW", KnownAnswers.HeaderPow.check)
]
