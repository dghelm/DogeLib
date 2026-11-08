module

public import DogeLib.Exports.Oracle
public import DogeLib.Proposals

/-!
Replay the invented lock-time proposal on oracle-shaped requests.
This test executable belongs to neither the baseline libraries nor `Exports`.
-/

public section

open DogeLib.Exports DogeLib.Script
open DogeLib.Proposals.ExampleFaultyLocktime DogeLib.Proposals.Framework

/-- Encode the proposal outcome with the baseline oracle's Script response fields. -/
def baselineResult : VerifyOutcome ScriptError → VerifyResult
  | .accepted => .accepted
  | .rejected e => .rejected e
  | .unsupported u => .unsupported u

/-- Answer legacy spend requests for one variant and activation state. -/
def proposalOperation (v : Variant) (active : Bool) : Operation :=
  Exports.verifyLegacyWith
    (fun ctx script flags => baselineResult (revisedVerifyLegacySpend v active ctx script flags coreVerifier))
    (fun flags sig script => baselineResult (revisedVerifyScript v active baseChecker flags sig script))

/-- Read JSON lines for the named test proposal, or print its version. -/
def main (argv : List String) : IO UInt32 := do
  if argv == ["--version"] then
    IO.println versionJson.compress
    return 0
  let (name, variant, active) ← match argv with
    | [name, variant, "--active"] => pure (name, variant, true)
    | [name, variant] => pure (name, variant, false)
    | _ =>
      IO.eprintln "usage: proposal-replay ExampleFaultyLocktime (faulty|corrected) [--active]"
      return 2
  unless name == "ExampleFaultyLocktime" && (variant == "faulty" || variant == "corrected") do
    IO.eprintln "unknown proposal or variant"
    return 2
  let v := if variant == "faulty" then Variant.faulty else Variant.corrected
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if let some response := respondWith [proposalOperation v active] line then
      stdout.putStrLn response.compress
      stdout.flush
  return 0
