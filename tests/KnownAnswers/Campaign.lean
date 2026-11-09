import DogeLib.Proposals
import DogeLib.Script.CoreVerifier
import KnownAnswers.Common

/-!
# Campaign regression fixtures

Each request of `tests/script/campaign/requests.jsonl` is a `script.verify_legacy` request with the transaction checker.
The test runs it through `verifyLegacySpend` with `coreVerifier`, and compares the verdict and ScriptError name with the response on the same line of `expected.jsonl`.
It also runs `revisedVerifyLegacySpend` of `ExampleFaultyLocktime` with `active` true, against `expected-faulty.jsonl` and `expected-corrected.jsonl`.
`proposal-replay` answers these requests with the same functions.

The fixture README records the source of each expected value: a property of design record 0009 and a hand check against pinned Core.
No expected value comes from DogeLib.
These compiled checks are finite regression evidence, not a proof.
-/

namespace KnownAnswers.Campaign

open DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework DogeLib.Proposals.ExampleFaultyLocktime

/-- The input context, previous-output script and flags of one request. -/
structure Request where
  id : String
  ctx : InputContext
  prevScript : DogeLib.Transaction.Script
  flags : UInt32

/-- Read a `script.verify_legacy` request with the transaction checker, and check each bound before constructing its context. -/
def parseRequest (text : String) : Except String Request := do
  let j ← Lean.Json.parse text
  let str (field : String) := do (← j.getObjVal? field).getStr?
  unless (← str "op") == "script.verify_legacy" do throw "operation is not script.verify_legacy"
  unless (← str "checker") == "transaction" do throw "checker is not transaction"
  let bytes ← KnownAnswers.Sha256Cavp.parseHex (← str "tx_hex")
  let tx ← match Transaction.decodeBaseComplete bytes.toList with
    | .ok tx => pure tx
    | .error _ => throw "transaction does not decode as complete base bytes"
  let index ← (← j.getObjVal? "input_index").getNat?
  if index ≥ 2 ^ 32 then throw "input index exceeds uint32"
  let inputIndex := index.toUInt32
  let flags ← (← j.getObjVal? "flags").getNat?
  if flags ≥ 2 ^ 32 then throw "flags exceed uint32"
  let prev ← KnownAnswers.Sha256Cavp.parseHex (← str "prevout_script_hex")
  let some prev := DogeLib.Serialization.CountedList.ofList? prev.toList
    | throw "previous-output script exceeds the counted-list bound"
  if hi : inputIndex.toNat < tx.inputs.val.length then
    if hn : tx.inputs.val.length < 2 ^ 32 then
      if ho : tx.outputs.val.length < 2 ^ 32 then
        return { id := ← str "id", ctx := ⟨tx, inputIndex, hi, hn, ho⟩, prevScript := ⟨prev⟩, flags := flags.toUInt32 }
      else throw "output count exceeds context bound"
    else throw "input count exceeds context bound"
  else throw "spend index outside transaction"

/-- The identifier, `result` and `script_error` of an expected `ok` response. -/
def parseExpected (text : String) : Except String (String × String × String) := do
  let j ← Lean.Json.parse text
  let ok ← j.getObjVal? "ok"
  return (← (← j.getObjVal? "id").getStr?, ← (← ok.getObjVal? "result").getStr?,
    ← (← ok.getObjVal? "script_error").getStr?)

/-- The `result` and `script_error` fields that the oracle writes for an outcome. An unsupported outcome never matches a fixture. -/
def fields : VerifyOutcome ScriptError → String × String
  | .accepted => ("accepted", "OK")
  | .rejected e => ("rejected", e.name)
  | .unsupported _ => ("unsupported", "")

/-- The non-empty lines of a fixture file. -/
def lines (path : System.FilePath) : IO (List String) := do
  return ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)

/-- Compare every request with its three expected responses. Returns the number of failures. -/
def check : IO Nat := do
  let dir : System.FilePath := "tests/script/campaign"
  let requests ← lines (dir / "requests.jsonl")
  let mut failures := 0
  let programs : List (String × (Request → VerifyOutcome ScriptError)) := [
    ("expected.jsonl", fun r => VerifyOutcome.ofBaseline id (verifyLegacySpend r.ctx r.prevScript r.flags coreVerifier)),
    ("expected-faulty.jsonl", fun r => revisedVerifyLegacySpend .faulty true r.ctx r.prevScript r.flags coreVerifier),
    ("expected-corrected.jsonl", fun r => revisedVerifyLegacySpend .corrected true r.ctx r.prevScript r.flags coreVerifier)
  ]
  for (file, run) in programs do
    let expected ← lines (dir / file)
    unless expected.length == requests.length do
      IO.eprintln s!"FAIL campaign fixture {file}: {expected.length} responses for {requests.length} requests"
      failures := failures + 1
    for (text, want) in requests.zip expected do
      let r ← match parseRequest text with
        | .ok r => pure r
        | .error e => throw (IO.userError s!"{dir / "requests.jsonl"}: {e}")
      let (wantId, result, error) ← match parseExpected want with
        | .ok e => pure e
        | .error e => throw (IO.userError s!"{dir / file}: {e}")
      let got := fields (run r)
      unless wantId == r.id && got == (result, error) do
        IO.eprintln s!"FAIL campaign fixture {r.id} against {file}: got {got}, expected {wantId} {result} {error}"
        failures := failures + 1
  IO.println s!"campaign fixtures: {requests.length} requests, {programs.length} expectations each, {failures} failures"
  return failures

/-- Named checks for the campaign regression fixtures. -/
def checks : List (String × IO Nat) := [
  ("campaign fixtures", check)
]

end KnownAnswers.Campaign
