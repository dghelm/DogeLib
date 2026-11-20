import DogeLib.Proposals
import KnownAnswers.Proposals.RelativeLockTime
import KnownAnswers.Script

/-!
## Proposals: the proposed revision `RelativeLockTime`, the opcode of BIP 112

`RelativeLockTime` is the revision of design record 0012. It is partial: it has the rules of BIP 113 and BIP 112.
Through extension E1, the revision adds `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` to the script flags of a block.
These cases run `verifyLegacySpend`, `verifyScript` and `validateBlockWithActive` through the compiled code.
No expected value comes from DogeLib.

### Core's records with the flag

Design record 0012, section 10.1, names the records of Core's corpora that hold `CHECKSEQUENCEVERIFY` (reference R13: SOURCES.md, D28, D29 and D45).
This check is the named gate of each record with the flag `CHECKSEQUENCEVERIFY` and with supported flags alone.

| File | Records with the flag | Run here | Unsupported |
| --- | ---: | ---: | --- |
| `tx_valid.json` | 30 | 30 | None. Each record has the flags `P2SH,CHECKSEQUENCEVERIFY`. |
| `tx_invalid.json` | 16 | 16 | None. Each record has the flags `P2SH,CHECKSEQUENCEVERIFY`. |
| `script_tests.json` | 6 | 5 | Line 2511, with the flag `MINIMALDATA`. |

Each record of the two transaction files has one input.

- `tx_valid.json`: Core's runner requires that `VerifyScript` accepts every input (D30, `src/test/transaction_tests.cpp`, lines 155 to 176). The check requires `accepted`.
- `tx_invalid.json`: Core's runner requires that `CheckTransaction` rejects or that an input fails (lines 239 to 261). It gives no error for one input.
  So each expected error here is derived by hand from the record, its comment and Core's code of the opcode (D3, `src/script/interpreter.cpp`, lines 392 to 427 and 1310 to 1354).
  `invalidCases` lists the 16 records by source line, with the derivation.
  Without the flag, opcode `0xb2` is `OP_NOP3`, and every one of the 16 scripts leaves a true item. So the check also requires `accepted` with the flag `P2SH` alone.
- `script_tests.json`: each record names Core's expected `ScriptError`. The check requires that error, as `KnownAnswers.ScriptEval.checkCorpus` does for the whole file.
  Line 2511 has a flag outside `supportedFlags`. The check requires an unsupported result for it, and the record is no evidence.

Six more records of `script_tests.json` hold the word `CHECKSEQUENCEVERIFY` in a script without the flag (lines 235, 236, 446, 860, 861 and 866).
There the opcode is `OP_NOP3`. `checkCorpus` runs the first five, and line 866 has the unsupported flag `DISCOURAGE_UPGRADABLE_NOPS`.

### Made blocks

The block cases run the whole of `validateBlock` and of the revision on a made block at height 1 on the mainnet genesis block, as the cutoff cases do.
The coin set has one coin, with a script that holds opcode `0xb2`. The second transaction of the block spends it.
Each expected result is derived by hand from BIP 112 (SOURCES.md, P2) and from Core's code of the opcode (D3) and of the two script runs of `CheckInputs` (D101, `src/validation.cpp`, lines 1488 to 1512).
A spend that fails with the CSV flag and passes without it is not a mandatory failure: Core's reason is `non-mandatory-script-verify-flag`.
-/

namespace KnownAnswers.Proposals.RelativeLockTimeOpcode

open DogeLib DogeLib.Block DogeLib.Work DogeLib.Transaction DogeLib.Script
open DogeLib.Proposals.Framework DogeLib.Proposals.RelativeLockTime
open KnownAnswers.Proposals.RelativeLockTime (require scriptOf counted coinbaseTx blockOf genesisTime genesisHash
  heightOneContext noVerifier activationAt baselineError outcomeIs)

/-! ### Core's records with the flag -/

/-- The flags of every transaction record with the CSV flag: `P2SH` and `CHECKSEQUENCEVERIFY`. -/
def csvRecordFlags : UInt32 := ScriptFlags.p2sh ||| ScriptFlags.checkSequenceVerify

/--
The 16 records of `tx_invalid.json` with the CSV flag: the source line and the expected error of the one input.
Each transaction has version 2 unless the note says otherwise. `sequence` is the sequence of the input, and `n` is the operand.
The mask of the comparison is `0x0040ffff`, and bit 22 is the type bit.
-/
def invalidCases : List (Nat × ScriptError) := [
  -- `1 CSV 1`, sequence 0: both are height locks, and n = 1 is above 0.
  (203, .unsatisfiedLocktime),
  -- `4259839 CSV 1`, sequence 0x0040fffe: both are time locks, and n = 0x40ffff is above the sequence.
  (205, .unsatisfiedLocktime),
  -- `4194305 CSV 1`, sequence 0x00400000: both are time locks, and n = 0x400001 is above the sequence.
  (209, .unsatisfiedLocktime),
  -- `4259839 CSV 1`, sequence 0x0040fffe: as line 205.
  (211, .unsatisfiedLocktime),
  -- `CSV 1` with an empty `scriptSig`: the stack is empty.
  (215, .invalidStackOperation),
  -- `-1 CSV 1`, sequence 0: the operand is negative.
  (219, .negativeLocktime),
  -- `-1 CSV 1`, sequence 0x00400000: the operand is negative.
  (223, .negativeLocktime),
  -- `0 CSV 1`, sequence 0x00400000: a height operand against a time sequence.
  (227, .unsatisfiedLocktime),
  -- `65535 CSV 1`, sequence 0x00400000: a height operand against a time sequence.
  (229, .unsatisfiedLocktime),
  -- `4194304 CSV 1`, sequence 0: a time operand against a height sequence.
  (231, .unsatisfiedLocktime),
  -- `4259839 CSV 1`, sequence 0: a time operand against a height sequence.
  (233, .unsatisfiedLocktime),
  -- A push of six zero bytes: the operand is longer than five bytes, and the decode fails.
  (237, .unknownError),
  -- `scriptSig` `1 CSV` against `scriptPubKey` `1`, sequence 0: n = 1 is above 0, in the `scriptSig`.
  (241, .unsatisfiedLocktime),
  -- A P2SH spend whose redeem script is `1 CSV`, sequence 0: n = 1 is above 0, in the redeem script.
  (245, .unsatisfiedLocktime),
  -- `0 CSV 1`, sequence 0, transaction version 1: the version is below 2.
  (249, .unsatisfiedLocktime),
  -- `4194304 CSV 1`, sequence 0x00400000, transaction version 1: the version is below 2.
  (251, .unsatisfiedLocktime)]

/-- The expected errors of the five records of `script_tests.json` with the CSV flag and supported flags, by source line. Each is the `expected_error` of the record. -/
def scriptTestLines : List Nat := [704, 2509, 2510, 2512, 2513]

/-- `verifyLegacySpend` on the input of a transaction record, with the flags `flags`. -/
def spend (r : KnownAnswers.TxSpends.Record) (flags : UInt32) : Except String VerifyResult := do
  let tx ← match Transaction.readAllowWitness r.bytes with
    | .ok (w, _) => if w.hasWitness then throw "the record has a witness" else pure w.tx
    | .error _ => throw "the transaction does not decode"
  if hi : r.inputIndex.toNat < tx.inputs.val.length then
    if hn : tx.inputs.val.length < 2 ^ 32 then
      if ho : tx.outputs.val.length < 2 ^ 32 then
        return verifyLegacySpend ⟨tx, r.inputIndex, hi, hn, ho⟩ r.prevScript flags coreVerifier
      else throw "the output count is outside the context bound"
    else throw "the input count is outside the context bound"
  else throw "the input index is outside the transaction"

/-- Runs the records of Core's corpora with the CSV flag. Returns the number of failures and the number of records that it ran. -/
def checkRecords : IO (Nat × Nat) := do
  let mut failures := 0
  let path : System.FilePath := "tests/script/corpus/tx_spends.jsonl"
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.isEmpty)
  let mut valid := 0
  let mut invalid := 0
  for text in lines do
    let r ← match KnownAnswers.TxSpends.parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{path}: {e}")
    if !hasFlag r.flags ScriptFlags.checkSequenceVerify then continue
    let where_ := s!"{r.source}:{r.line}"
    -- Every record with the flag is inside the milestone, with one input and no unsupported flag.
    failures := failures + (← require s!"{where_}: the flags are P2SH and CHECKSEQUENCEVERIFY"
      (r.flags == csvRecordFlags && r.inside && r.inputIndex == 0))
    let withFlag ← match spend r r.flags with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"{where_}: {e}")
    let withoutFlag ← match spend r ScriptFlags.p2sh with
      | .ok v => pure v
      | .error e => throw (IO.userError s!"{where_}: {e}")
    if r.source == "tx_valid.json" then
      valid := valid + 1
      failures := failures + (← require s!"{where_}: accepted with the flag" (withFlag == .accepted && r.accept))
    else
      invalid := invalid + 1
      match invalidCases.lookup r.line with
      | none => failures := failures + (← require s!"{where_}: the record has an expected error" false)
      | some e =>
        failures := failures + (← require s!"{where_}: {e.name} with the flag" (withFlag == .rejected e))
        failures := failures + (← require s!"{where_}: accepted without the flag" (withoutFlag == .accepted))
  failures := failures + (← require "30 records of tx_valid.json and 16 of tx_invalid.json have the flag"
    (valid == 30 && invalid == 16 && invalidCases.length == 16))
  -- `script_tests.json`.
  let scriptPath : System.FilePath := "tests/script/corpus/script_tests.jsonl"
  let scriptLines := ((← IO.FS.readFile scriptPath).splitOn "\n").filter (!·.isEmpty)
  let mut ran := 0
  let mut unsupported := 0
  for text in scriptLines do
    let r ← match KnownAnswers.ScriptEval.parseRecord text with
      | .ok r => pure r
      | .error e => throw (IO.userError s!"{scriptPath}: {e}")
    if !hasFlag r.flags ScriptFlags.checkSequenceVerify then continue
    let checker := transactionChecker r.spendTx r.inputIndex.toUInt32 coreVerifier
    let got := verifyScript checker r.flags r.scriptSig r.scriptPubKey
    if unsupportedFlagBits r.flags == 0 then
      ran := ran + 1
      failures := failures + (← require s!"script_tests.json:{r.line}: {r.expected}"
        (scriptTestLines.contains r.line && !r.witness && r.inside &&
          KnownAnswers.ScriptEval.outcomeName (KnownAnswers.ScriptEval.outcomeOf got) == r.expected))
    else
      unsupported := unsupported + 1
      failures := failures + (← require s!"script_tests.json:{r.line}: unsupported for the flag MINIMALDATA"
        (r.line == 2511 && !r.inside && got == .unsupported (.flags ScriptFlags.minimalData)))
  failures := failures + (← require "5 records of script_tests.json with the flag run, and 1 is unsupported"
    (ran == 5 && unsupported == 1))
  return (failures, valid + invalid + ran)

/-! ### Made blocks -/

/-- The transaction that created the spent coin: one output of 0 with the script `script`. It is not a coinbase. -/
def fundingTx (script : List UInt8) : Transaction :=
  { version := 1
    inputs := counted [{ prevout := ⟨Hash256.zero, 0⟩, scriptSig := scriptOf [], sequence := 0xffffffff }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf script }]
    lockTime := 0 }

/-- A transaction with the version `version` and one input: it spends output 0 of `fundingTx script` with an empty `scriptSig` and the sequence `sequence`. -/
def spendTx (script : List UInt8) (version sequence : UInt32) : Transaction :=
  { version
    inputs := counted [{ prevout := ⟨(fundingTx script).txid, 0⟩, scriptSig := scriptOf [], sequence }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [] }]
    lockTime := 0 }

/-- The arguments of a block at height 1 with a coinbase and `spendTx`, on the coin set with the coin of `fundingTx script` at height 0. -/
def blockArgs (script : List UInt8) (version sequence : UInt32) : BlockArgs :=
  ⟨noVerifier, false, false, heightOneContext, CoinSet.empty.addTx (fundingTx script) 0,
    blockOf genesisHash (genesisTime + 60) [coinbaseTx, spendTx script version sequence]⟩

/-- `validateBlockWith` with the revision on the arguments, for an activation. -/
def withActivation (height : Option Nat) (a : BlockArgs) : BlockOutcome ValidateError ValidateError ConnectResult :=
  validateBlockWith ValidateEmbedding.baseline ConnectEmbedding.baseline (blockRevision a.verify) (activationAt height)
    a.fCheckPOW a.fCheckMerkleRoot a.ctx a.coins a.block

/-- The failure of input 0 of transaction 1 with the error `e`, which is not mandatory: Core's `non-mandatory-script-verify-flag`. -/
def notMandatory (e : ScriptError) : ValidateError := .connect (.script 1 0 false e)

/--
A block case: a label, the script of the spent coin, the version of the spending transaction, the sequence of its input, and the expected result of the active revision.
`none` is an acceptance. The baseline accepts every case: without the flag, `0xb2` is `OP_NOP3`, and each script leaves a true item.
-/
structure BlockCase where
  label : String
  script : List UInt8
  version : UInt32
  sequence : UInt32
  active : Option ValidateError

/-- The block cases. `01 nn b2` pushes the operand `nn`, and `OP_CHECKSEQUENCEVERIFY` leaves it on the stack. -/
def blockCases : List BlockCase := [
  -- A height lock of 1 against the sequence 1: met exactly.
  ⟨"operand 1, sequence 1, version 2", [0x01, 0x01, 0xb2], 2, 1, none⟩,
  -- A height lock of 2 against the sequence 1: one short.
  ⟨"operand 2, sequence 1, version 2", [0x01, 0x02, 0xb2], 2, 1, some (notMandatory .unsatisfiedLocktime)⟩,
  -- `CheckSequence` fails for a version below 2 as an unsigned value.
  ⟨"operand 1, sequence 1, version 1", [0x01, 0x01, 0xb2], 1, 1, some (notMandatory .unsatisfiedLocktime)⟩,
  -- Version -1 is `0xffffffff` as an unsigned value, which is at least 2.
  ⟨"operand 1, sequence 1, version -1", [0x01, 0x01, 0xb2], 0xffffffff, 1, none⟩,
  -- Bit 31 of the sequence turns relative lock time off for the input, so `CheckSequence` fails.
  ⟨"operand 1, sequence with bit 31", [0x01, 0x01, 0xb2], 2, 0x80000001, some (notMandatory .unsatisfiedLocktime)⟩,
  -- Bits of the sequence outside the mask `0x0040ffff` do not count: `0x00010001` is 1 under the mask.
  ⟨"operand 1, sequence 0x00010001", [0x01, 0x01, 0xb2], 2, 0x00010001, none⟩,
  ⟨"operand 2, sequence 0x00010001", [0x01, 0x02, 0xb2], 2, 0x00010001, some (notMandatory .unsatisfiedLocktime)⟩,
  -- The operand `00 00 40` is `0x400000`: a time lock of 0. The sequence 1 is a height lock, so the types differ.
  ⟨"time operand, height sequence", [0x03, 0x00, 0x00, 0x40, 0xb2], 2, 1, some (notMandatory .unsatisfiedLocktime)⟩,
  ⟨"time operand, time sequence", [0x03, 0x00, 0x00, 0x40, 0xb2], 2, 0x00400000, none⟩,
  -- The operand `00 00 00 80 00` is `0x80000000`: bit 31 makes the opcode a NOP, also for version 1.
  ⟨"operand with bit 31, version 1", [0x05, 0x00, 0x00, 0x00, 0x80, 0x00, 0xb2], 1, 0, none⟩,
  -- `OP_1NEGATE` pushes -1: a negative operand.
  ⟨"operand -1", [0x4f, 0xb2], 2, 1, some (notMandatory .negativeLocktime)⟩,
  -- A push of six bytes: the operand is longer than five bytes. The item `01 00 00 00 00 00` is true.
  ⟨"operand of six bytes", [0x06, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb2], 2, 1, some (notMandatory .unknownError)⟩,
  -- `OP_1 OP_IF OP_1 OP_ELSE OP_0 OP_CHECKSEQUENCEVERIFY OP_ENDIF`: the opcode is in a branch that does not execute.
  ⟨"opcode in a skipped branch, version 1", [0x51, 0x63, 0x51, 0x67, 0x00, 0xb2, 0x68], 1, 1, none⟩]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let (recordFailures, records) ← checkRecords
  let mut failures := recordFailures
  for c in blockCases do
    let args := blockArgs c.script c.version c.sequence
    failures := failures + (← require s!"{c.label}, baseline" (baselineError (baselineValidate args) == none))
    failures := failures + (← require s!"{c.label}, active" (outcomeIs (revisedValidate true args) c.active))
    failures := failures + (← require s!"{c.label}, inactive" (outcomeIs (revisedValidate false args) none))
    -- The block is at height 1. An activation height of 1 is active there, and a height of 2 is not.
    failures := failures + (← require s!"{c.label}, activation height 1" (outcomeIs (withActivation (some 1) args) c.active))
    failures := failures + (← require s!"{c.label}, activation height 2" (outcomeIs (withActivation (some 2) args) none))
  -- A script that fails without the flag is a mandatory failure with the flag too: `01 01 b2 OP_DROP OP_0` leaves a false item.
  let falseArgs := blockArgs [0x01, 0x01, 0xb2, 0x75, 0x00] 2 1
  let mandatory : ValidateError := .connect (.script 1 0 true .evalFalse)
  failures := failures + (← require "a false result, baseline" (baselineError (baselineValidate falseArgs) == some mandatory))
  failures := failures + (← require "a false result, active" (outcomeIs (revisedValidate true falseArgs) (some mandatory)))
  let total := 5 * blockCases.length + 2
  IO.println s!"Proposals RelativeLockTime opcode: {records} records of Core with the CSV flag (30 tx_valid, 16 tx_invalid, 5 script_tests) and 1 unsupported, {total} block cases, {failures} failures"
  return failures

end KnownAnswers.Proposals.RelativeLockTimeOpcode
