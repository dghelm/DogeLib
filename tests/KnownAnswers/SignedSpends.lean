import DogeLib.Script.CoreVerifier
import DogeLib.Script.MultisigRecovery
import DogeLib.Script.Proofs.FixedDigest
import KnownAnswers.Common

/-!
# Signed recovery-template spends

Every record of `tests/script/signed-spends/recovery.jsonl` runs through `verifyLegacySpend` with `coreVerifier`.
The expected Boolean verdict and ScriptError name come from pinned Core's `VerifyScript`, as the fixture README records.
These compiled checks provide finite comparison evidence, not a proof of agreement with Core on every input.

Every record of `tests/script/signed-spends/fixed-digest.jsonl` runs through the same comparison.
Those records reach, or just miss, the fixed digest of `SIGHASH_SINGLE` (D3, lines 1231 to 1236).
For them, `legacySignatureHash` is also compared with each digest that Core's `SignatureHash` returned.
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

/-- The legacy signature hash of one request, or `none` for a script code outside `Transaction.Script`. -/
def digestOf (code : ByteArray) (tx : Transaction) (index : Nat) (hashType : Nat) : Option (List UInt8) :=
  (DogeLib.Serialization.CountedList.ofList? code.toList).map fun sc =>
    (legacySignatureHash ⟨sc⟩ tx index.toUInt32 hashType.toUInt32).val

/--
Compare the 44 fixed-digest records with Core.

1. `verifyLegacySpend` with `coreVerifier` gives Core's verdict and ScriptError name.
2. `legacySignatureHash` gives Core's digest for each signing request and for each request of the spend.
3. For a spend with at most `input_index` outputs and only SINGLE hash types, `verifyScript` with `fixedDigestChecker` also gives Core's verdict.
   That call has no transaction. It is the right side of `verifyLegacySpend_eq_fixedDigest`.

The third check is a compiled sanity check of the theorem's hypotheses on these records, not a proof term.
-/
def checkFixedDigest : IO Nat := do
  let path : System.FilePath := "tests/script/signed-spends/fixed-digest.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut failures := 0
  let mut ids : List String := []
  let mut digests := 0
  let mut free := 0
  let mut accepted := 0
  for text in lines do
    let r ← match parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if ids.contains r.id then throw (IO.userError s!"duplicate fixed-digest id: {r.id}")
    ids := r.id :: ids
    let agrees (got : VerifyResult) : Bool := match got with
      | .accepted => r.valid && r.error == "OK"
      | .rejected e => !r.valid && e.name == r.error
      | .unsupported _ => false
    let got := verifyLegacySpend r.ctx r.prevScript r.flags coreVerifier
    if r.valid then accepted := accepted + 1
    unless agrees got do
      IO.eprintln s!"FAIL fixed-digest spend {r.id}: got {repr got}, expected valid={r.valid}, error={r.error}"
      failures := failures + 1
    let extra : Except String (List Nat × List (Option (List UInt8) × List UInt8)) := do
      let j ← Lean.Json.parse text
      let hex (field : String) := do
        KnownAnswers.Sha256Cavp.parseHex (← (← j.getObjVal? field).getStr?)
      let hexes (field : String) := do
        (← (← j.getObjVal? field).getArr?).toList.mapM fun v => do
          return (← KnownAnswers.Sha256Cavp.parseHex (← v.getStr?)).toList
      let types ← (← (← j.getObjVal? "hash_types").getArr?).toList.mapM (·.getNat?)
      let signingTx ← match Transaction.decodeBaseComplete (← hex "signing_tx_hex").toList with
        | .ok tx => pure tx
        | .error _ => throw "signing transaction does not decode"
      let signingIndex ← (← j.getObjVal? "signing_input_index").getNat?
      let signingCode ← hex "signing_script_code_hex"
      let code ← hex "script_code_hex"
      let signing ← hexes "digests_hex"
      let spend ← hexes "spend_digests_hex"
      unless signing.length == types.length && spend.length == types.length do throw "digest count"
      let pairs := (types.zip signing).map (fun (h, d) => (digestOf signingCode signingTx signingIndex h, d)) ++
        (types.zip spend).map (fun (h, d) => (digestOf code r.ctx.tx r.ctx.index.toNat h, d))
      return (types, pairs)
    match extra with
    | .error e => throw (IO.userError s!"{path}: {r.id}: {e}")
    | .ok (types, pairs) =>
      for (ours, core) in pairs do
        digests := digests + 1
        unless ours == some core do
          IO.eprintln s!"FAIL fixed-digest spend {r.id}: signature hash differs from Core"
          failures := failures + 1
      if r.ctx.tx.outputs.val.length ≤ r.ctx.index.toNat ∧ types.all (fun h => h % 32 == 3) then
        free := free + 1
        let got := verifyScript (fixedDigestChecker coreVerifier) r.flags r.ctx.input.scriptSig.bytes.val
          r.prevScript.bytes.val
        unless agrees got do
          IO.eprintln s!"FAIL fixed-digest spend {r.id}: transaction-free result {repr got}"
          failures := failures + 1
  unless lines.length == 44 && accepted == 32 && free == 37 do
    IO.eprintln s!"FAIL fixed-digest fixture counts: {lines.length} records, {accepted} accepted, {free} transaction-free"
    failures := failures + 1
  IO.println s!"fixed-digest spends: {lines.length} verdict/error comparisons, {digests} digests, {free} transaction-free results, {failures} failures"
  return failures

/-- Named checks for the signed fixtures. -/
def checks : List (String × IO Nat) := [
  ("fixed-digest spends", checkFixedDigest),
  ("signed recovery spends", check)
]

end KnownAnswers.SignedSpends
