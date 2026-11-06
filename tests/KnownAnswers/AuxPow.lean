import DogeLib.Block
import KnownAnswers.Common

/-!
## `CAuxPow::check`

`tests/block/check-auxpow.json` holds the 26 deterministic cases of Core's `check_auxpow` and the boundary cases of design record 0004, stage 3.
`tests/block/import_check_auxpow.py` built their bytes with Python, independently of DogeLib.
The expected Boolean of a Core case is its `BOOST_CHECK`.
The expected Boolean of a boundary case is argued from the source.

`error_line` names the `return error` of `src/auxpow.cpp` that the case reaches, worked out by reading the source.
The test compares it with the Lean diagnostic. That comparison checks the Lean error order. It is not evidence from Core.

The six mainnet headers of `tests/block/auxpow-headers.json` are checked with their own hash and chain ID and the mainnet value of `fStrictChainId`.
-/

namespace KnownAnswers.AuxPowCheck
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Block (require jsonFile)

/-- The line of `src/auxpow.cpp` whose `return error` each error stands for (D55). -/
def errorLine : AuxPowCheckError → Nat
  | .notCoinbase => 85
  | .parentHasChainId => 88
  | .chainBranchTooLong => 91
  | .merkleRootIncorrect => 102
  | .noInputs => 106
  | .missingChainRoot => 120
  | .multipleMarkers => 127
  | .markerNotBeforeRoot => 129
  | .rootTooLate => 137
  | .missingSizeAndNonce => 145
  | .sizeMismatch => 152
  | .wrongIndex => 158

/-- One record: a label, the payload bytes, the arguments of `check`, the expected result and the expected error line. -/
structure Case where
  label : String
  payload : List UInt8
  hashAux : Hash256
  chainId : Int32
  strict : Bool
  expected : Bool
  errorLine : Option Nat

/-- Parse one record of `check-auxpow.json`. -/
def parseCase (j : Lean.Json) : Except String Case := do
  let kind ← j.getObjValAs? String "kind"
  let label ← if kind == "check_auxpow" then do
      pure s!"check_auxpow line {(← (← j.getObjVal? "line").getNat?)}"
    else do pure s!"boundary {(← j.getObjValAs? String "name")}"
  let payload := (← parseHex (← j.getObjValAs? String "payload_hex")).toList
  let some hashAux := Hash256.ofBytes? (← parseHex (← j.getObjValAs? String "hash_aux_block_hex")).toList
    | throw s!"{label}: hash_aux_block_hex is not 32 bytes"
  let chainId ← (← j.getObjVal? "chain_id").getInt?
  let errorLine ← match (← j.getObjVal? "error_line") with
    | .null => pure none
    | v => some <$> v.getNat?
  let strict ← j.getObjValAs? Bool "strict_chain_id"
  let expected ← j.getObjValAs? Bool "expected"
  return { label, payload, hashAux, chainId := Int32.ofInt chainId, strict, expected, errorLine }

/-- Check every record of `tests/block/check-auxpow.json`. -/
def checkCases : IO Nat := do
  let doc ← jsonFile "tests/block/check-auxpow.json"
  let rows ← match doc.getObjValAs? (Array Lean.Json) "cases" with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "check-auxpow: 42 records" (rows.size == 42)
  let mut core := 0
  for row in rows do
    let c ← match parseCase row with
      | .ok c => pure c
      | .error e => throw (IO.userError e)
    if c.label.startsWith "check_auxpow" then core := core + 1
    match AuxPow.read .allowWitness c.payload with
    | .ok (a, []) =>
      let result := a.check c.hashAux c.chainId c.strict
      let accepted := match result with | .ok () => true | .error _ => false
      failures := failures + (← require s!"{c.label}: result" (accepted == c.expected))
      let line := match result with | .ok () => none | .error e => some (errorLine e)
      failures := failures + (← require s!"{c.label}: Lean diagnostic line {line}, expected {c.errorLine}"
        (line == c.errorLine))
    | _ => failures := failures + (← require s!"{c.label}: payload reads completely" false)
  failures := failures + (← require "check-auxpow: 26 Core cases" (core == 26))
  IO.println s!"AuxPoW check: {rows.size} records, {core} from check_auxpow"
  return failures

/-- Check the six mainnet AuxPoW headers with their own hash, their own chain ID and `fStrictChainId` true (D14 lines 120 to 121). -/
def checkMainnet : IO Nat := do
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  let mut failures ← require "AuxPoW check: six mainnet headers" (rows.size == 6)
  for row in rows do
    let parsed : Except String (Nat × List UInt8) := do
      return (← (← row.getObjVal? "height").getNat?, (← parseHex (← row.getObjValAs? String "block")).toList)
    let (height, block) ← match parsed with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    match BlockHeader.read .allowWitness block with
    | .ok (⟨pure, some a⟩, _) =>
      failures := failures + (← require s!"AuxPoW check: mainnet {height} chain ID 98" (pure.chainId == 98))
      failures := failures + (← require s!"AuxPoW check: mainnet {height}"
        (match a.check pure.getHash pure.chainId true with | .ok () => true | .error _ => false))
    | _ => failures := failures + (← require s!"AuxPoW check: mainnet {height} reads with a payload" false)
  IO.println s!"AuxPoW check: {rows.size} mainnet headers"
  return failures

/-- Small known answers of the helpers, from Core's definitions (D55). -/
def checkHelpers : IO Nat := do
  let mut failures := 0
  -- `GetChainId` of version 0x00620104, and the arithmetic shift of a negative version.
  failures := failures + (← require "chain ID of 0x00620104"
    ((⟨0x00620104, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == 98))
  failures := failures + (← require "chain ID of 0xffff0104"
    ((⟨0xffff0104, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == -1))
  failures := failures + (← require "chain ID of 0x80000000"
    ((⟨0x80000000, Hash256.zero, Hash256.zero, 0, 0, 0⟩ : PureBlockHeader).chainId == -32768))
  -- The marker and the first-occurrence search.
  failures := failures + (← require "marker bytes" (mergedMiningMarker == [0xfa, 0xbe, 0x6d, 0x6d]))
  failures := failures + (← require "first occurrence" (findSubseq? [1, 2] [0, 1, 2, 1, 2] == some 1))
  failures := failures + (← require "no occurrence" (findSubseq? [1, 2] [0, 1, 3, 2] == none))
  failures := failures + (← require "occurrence at the end" (findSubseq? [1, 2] [0, 1, 2] == some 1))
  failures := failures + (← require "needle longer than input" (findSubseq? [1, 2, 3] [1, 2] == none))
  return failures

/-- Run every `CAuxPow::check` known answer. -/
def check : IO Nat := do
  let mut failures ← checkHelpers
  failures := failures + (← checkCases)
  failures := failures + (← checkMainnet)
  IO.println s!"AuxPoW check known answers: {failures} failures"
  return failures
end KnownAnswers.AuxPowCheck

/-!
## Version gating

The version checks of `ContextualCheckBlockHeader` (D33, lines 3072 to 3086), with records at the activation height of each network.

`fAllowLegacyBlocks` of each record comes from `src/chainparams.cpp` (D14).
Each network's first record sets it true, and each later record copies it until the AuxPoW record sets it false:

| Network | True | False | AuxPoW `nHeightEffective` |
| --- | --- | --- | --- |
| Mainnet | line 122, copied at 126 and 134 | line 136 | 371337, line 135 |
| Testnet | line 279, copied at 282, 291 and 297 | line 300 | 158100, line 298 |
| Regtest | line 419, copied at 425 and 430 | line 431 | 20, line 432 |

`GetConsensus` (D14, lines 494 to 506) returns the AuxPoW record from its `nHeightEffective` on, and the previous record at the height before.
DogeLib does not model that selection for this field, so each case states the record that Core selects.
The expected results are worked out by hand from `IsLegacy` and `IsAuxpow` (D10, lines 129 to 132 and 150 to 155).

Real headers add two checks.
The 312 mainnet headers at heights 144719 to 145030 have version 2 and pass with `fAllowLegacyBlocks` true.
The six AuxPoW headers of `tests/block/auxpow-headers.json` start at height 371337 and pass with it false.
Each set is rejected with the other value.
-/

namespace KnownAnswers.VersionGate
open DogeLib DogeLib.Block
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Block (require jsonFile)

/-- A pure header with the given version bits and zero in every other field. -/
def header (v : UInt32) : PureBlockHeader := ⟨v, Hash256.zero, Hash256.zero, 0, 0, 0⟩

/-- The result as Core's reject reason, or `ok`. -/
def outcome (r : Except VersionGateError Unit) : String :=
  match r with
  | .ok () => "ok"
  | .error e => e.rejectReason

/--
Version bits with the expected outcome under each value of `fAllowLegacyBlocks`, as (bits, outcome if true, outcome if false).
Versions 1 and 2 are legacy. Bit 8 is the AuxPoW flag.
-/
def versions : List (UInt32 × String × String) :=
  [ (0x00000001, "ok", "late-legacy-block"),
    (0x00000002, "ok", "late-legacy-block"),
    (0x00000000, "ok", "ok"),
    (0x00000003, "ok", "ok"),
    -- Chain ID 98 without the flag is not legacy.
    (0x00620002, "ok", "ok"),
    (0x00620102, "early-auxpow-block", "ok"),
    (0x00000102, "early-auxpow-block", "ok"),
    (0x00000101, "early-auxpow-block", "ok"),
    -- −1 as a signed version: bit 8 is set and the version is not legacy.
    (0xffffffff, "early-auxpow-block", "ok") ]

/-- The record that Core selects at each height, as (label, height, `fAllowLegacyBlocks`), from the table above. -/
def records : List (String × Nat × Bool) :=
  [ ("mainnet", 371336, true), ("mainnet", 371337, false),
    ("testnet", 158099, true), ("testnet", 158100, false),
    ("regtest", 19, true), ("regtest", 20, false) ]

/-- Check each version against the record at each side of each activation height. -/
def checkActivation : IO Nat := do
  let mut failures := 0
  for (net, height, allow) in records do
    for (v, ifTrue, ifFalse) in versions do
      let got := outcome (checkVersion ⟨allow⟩ (header v))
      let want := if allow then ifTrue else ifFalse
      failures := failures + (← require s!"{net} height {height}, version {v}: {got}, expected {want}" (got == want))
  return failures

/-- Check the recorded mainnet headers under both values of `fAllowLegacyBlocks`. -/
def checkMainnet : IO Nat := do
  let mut failures := 0
  let text ← IO.FS.readFile "tests/work/mainnet-headers/headers.txt"
  let lines := (text.splitOn "\n").filter (!·.isEmpty)
  failures := failures + (← require "version gating: 312 legacy-era headers" (lines.length == 312))
  for line in lines do
    let [height, hex] := line.splitOn " " | throw (IO.userError "bad header line")
    let raw ← match parseHex hex with
      | .ok b => pure b.toList
      | .error e => throw (IO.userError e)
    match Serialization.Codec.decode (α := PureBlockHeader) raw with
    | some (h, []) =>
      failures := failures + (← require s!"mainnet {height}: allowed" (outcome (checkVersion ⟨true⟩ h) == "ok"))
      failures := failures + (← require s!"mainnet {height}: late legacy"
        (outcome (checkVersion ⟨false⟩ h) == "late-legacy-block"))
    | _ => failures := failures + (← require s!"mainnet {height}: reads" false)
  let rows ← match (← jsonFile "tests/block/auxpow-headers.json").getArr? with
    | .ok rows => pure rows
    | .error e => throw (IO.userError e)
  failures := failures + (← require "version gating: six AuxPoW headers" (rows.size == 6))
  for row in rows do
    let parsed : Except String (Nat × List UInt8) := do
      return (← (← row.getObjVal? "height").getNat?, (← parseHex (← row.getObjValAs? String "block")).toList)
    let (height, block) ← match parsed with
      | .ok r => pure r
      | .error e => throw (IO.userError e)
    failures := failures + (← require s!"mainnet {height}: at or after activation" (height ≥ 371337))
    match Serialization.Codec.decode (α := PureBlockHeader) block with
    | some (h, _) =>
      failures := failures + (← require s!"mainnet {height}: allowed" (outcome (checkVersion ⟨false⟩ h) == "ok"))
      failures := failures + (← require s!"mainnet {height}: early AuxPoW"
        (outcome (checkVersion ⟨true⟩ h) == "early-auxpow-block"))
    | none => failures := failures + (← require s!"mainnet {height}: reads" false)
  return failures

/-- Run every version-gating known answer. -/
def check : IO Nat := do
  let mut failures ← checkActivation
  failures := failures + (← checkMainnet)
  IO.println s!"version gating: {records.length * versions.length} activation cases, 318 mainnet headers; {failures} failures"
  return failures
end KnownAnswers.VersionGate

/-- Named checks for AuxPow known answers, in alphabetical order. -/
def KnownAnswers.AuxPow.checks : List (String × IO Nat) := [
  ("auxpowCheck", KnownAnswers.AuxPowCheck.check),
  ("versionGate", KnownAnswers.VersionGate.check)
]
