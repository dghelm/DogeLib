import DogeLib.Script.CoreVerifier
import DogeLib.Script.MultisigRecovery
import KnownAnswers.Common

/-!
# Signed recovery-template spends

Every record of `tests/script/signed-spends/recovery.jsonl` runs through `verifyLegacySpend` with `coreVerifier`.
The expected Boolean verdict and ScriptError name come from pinned Core's `VerifyScript`, as the fixture README records.
These compiled checks provide finite comparison evidence, not a proof of agreement with Core on every input.
-/

namespace KnownAnswers.SignedSpends

open DogeLib.Script DogeLib.Transaction

/-- The spending context, flags and Core expectation of one signed fixture. -/
structure Record where
  id : String
  ctx : InputContext
  prevScript : DogeLib.Transaction.Script
  flags : UInt32
  valid : Bool
  error : String
  keys : List (List UInt8)

/-- Read a complete base transaction and check each bound before constructing its input context. -/
def parseRecord (text : String) : Except String Record := do
  let j ← Lean.Json.parse text
  let hex (field : String) := do
    KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? field).getStr?)
  let keys ← (← (← j.getObjVal? "keys").getArr?).toList.mapM fun key => do
    return (← KnownAnswers.Sha256Cavp.parseHex (← (← key.getObjVal? "pubkey_hex").getStr?)).toList
  let bytes ← hex "tx_hex"
  let tx ← match Transaction.decodeBaseComplete bytes.toList with
    | .ok tx => pure tx
    | .error _ => throw "signed transaction does not decode as complete base bytes"
  let index ← (← j.getObjVal? "input_index").getNat?
  if index ≥ 2 ^ 32 then throw "input index exceeds uint32"
  let inputIndex := index.toUInt32
  let flags ← (← j.getObjVal? "flags").getNat?
  if flags ≥ 2 ^ 32 then throw "flags exceed uint32"
  let prev ← hex "script_pubkey_hex"
  let some prev := DogeLib.Serialization.CountedList.ofList? prev.toList
    | throw "previous-output script exceeds the counted-list bound"
  if hi : inputIndex.toNat < tx.inputs.val.length then
    if hn : tx.inputs.val.length < 2 ^ 32 then
      if ho : tx.outputs.val.length < 2 ^ 32 then
        return {
          id := ← (← j.getObjVal? "id").getStr?
          ctx := ⟨tx, inputIndex, hi, hn, ho⟩
          prevScript := ⟨prev⟩
          flags := flags.toUInt32
          valid := ← (← j.getObjVal? "core_valid").getBool?
          error := ← (← j.getObjVal? "core_error").getStr?
          keys }
      else throw "output count exceeds context bound"
    else throw "input count exceeds context bound"
  else throw "spend index outside transaction"

/--
Compute the `MultisigRecoverySpend` premises of `multisigRecovery_sound_coreVerifier` for a 2-of-3 baseline.
The successful `scriptSig` evaluation supplies the existential stack and state witnesses.
The main comparison checks the theorem's remaining premise, acceptance.
This is a compiled sanity check, not a proof term.
-/
def templatePremises (r : Record) : Bool :=
  match r.keys with
  | [p1, p2, p3, recovery] =>
    let keys := [p1, p2, p3]
    let redeem := multisigRecoveryScript 2 keys recovery
    unsupportedFlagBits r.flags == 0 && hasFlag r.flags ScriptFlags.p2sh &&
      hasFlag r.flags ScriptFlags.checkLockTimeVerify && decide (1 ≤ (2 : Nat)) &&
      decide (2 ≤ keys.length) && decide (keys.length ≤ 16) &&
      keys.all (·.length == 33) && recovery.length == 33 &&
      r.prevScript.bytes.val == p2shScriptPubKey redeem && isPushOnly r.ctx.input.scriptSig.bytes.val &&
      (match evalScript (some (transactionChecker r.ctx.tx r.ctx.index coreVerifier)) r.flags
          r.ctx.input.scriptSig.bytes.val [] with
        | .ok state => state.stack.getLast? == some redeem
        | _ => false)
  | _ => false

/-- Compare all 25 Core verdicts and errors, including every signer pair and the recovery baseline. -/
def check : IO Nat := do
  let path : System.FilePath := "tests/script/signed-spends/recovery.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut ids : List String := []
  let mut premises := 0
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if ids.contains r.id then throw (IO.userError s!"duplicate signed-spend id: {r.id}")
    ids := r.id :: ids
    if ["multisig-12", "multisig-13", "multisig-23", "recovery"].contains r.id then
      premises := premises + 1
      unless r.valid && r.error == "OK" && templatePremises r do
        IO.eprintln s!"FAIL signed spend {r.id}: worked-property premises"
        failures := failures + 1
    let got := verifyLegacySpend r.ctx r.prevScript r.flags coreVerifier
    let agrees := match got with
      | .accepted => r.valid && r.error == "OK"
      | .rejected e => !r.valid && e.name == r.error
      | .unsupported _ => false
    unless agrees do
      IO.eprintln s!"FAIL signed spend {r.id}: got {repr got}, expected valid={r.valid}, error={r.error}"
      failures := failures + 1
  unless lines.length == 25 && ["multisig-12", "multisig-13", "multisig-23", "recovery"].all ids.contains do
    IO.eprintln "FAIL signed-spend fixture count or baseline coverage"
    failures := failures + 1
  IO.println s!"signed recovery theorem premises: {premises} baselines checked"
  IO.println s!"signed recovery spends: {lines.length} verdict/error comparisons, {failures} failures"
  return failures

/-- Named checks for the signed recovery-template fixtures. -/
def checks : List (String × IO Nat) := [
  ("signed recovery spends", check)
]

end KnownAnswers.SignedSpends
