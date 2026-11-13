import DogeLib.Block
import KnownAnswers.Common
import KnownAnswers.Genesis

/-!
## `CheckTransaction`, the legacy count of signature operations and `CheckBlock`

The expected values come from Dogecoin Core's unit tests, its corpus and its chain parameters at the pin.
None of them comes from DogeLib.

- `tx_valid`, `src/test/transaction_tests.cpp` (SOURCES.md D30): the test asserts `CheckTransaction(tx, state)` for every record of `tx_valid.json` (D28).
- `tx_invalid.json` (D29), the records under the comment "Tests for CheckTransaction()".
  Each comment names the rule that its record breaks, and `CheckTransaction` (D106) gives the reject reason of that rule.
  Two comments name `MAX_MONEY`. One record has the amount 2,100,000,000,000,001, and the other has the amounts 2,100,000,000,000,000 and 256.
  The value 2,100,000,000,000,000 is the bound of Bitcoin.
  Dogecoin's `MAX_MONEY` is 10^18 (`src/amount.h`, line 32), so `CheckTransaction` accepts both records here.
  Core's test `tx_invalid` requires only that each record fails `CheckTransaction` or a script check, so it does not fix this result.
  The expected acceptance comes from the amounts and from lines 544 to 548 of D106.
- `GetSigOpCount`, `src/test/sigopcount_tests.cpp`, lines 28 to 64 (D109): the counts with `fAccurate` false of four scripts.
- The mainnet genesis block: `CreateGenesisBlock` and the two assertions on its hash and Merkle root (D9, `src/chainparams.cpp`, lines 18 to 40 and 155 to 161).
  `ConnectBlock` calls `CheckBlock` with both flags true before its special case for the genesis block (`src/validation.cpp`, lines 1804 and 1819 to 1824), so a mainnet node accepts that block with `CheckBlock`.
-/
namespace KnownAnswers.BlockCheck
open DogeLib DogeLib.Block DogeLib.Transaction DogeLib.Serialization
open KnownAnswers.Block (require)
open KnownAnswers.Sha256Cavp (parseHex)

/-- The error of a check, or `none` when the check accepts. -/
def errorOf {ε : Type} : Except ε Unit → Option ε
  | .ok () => none
  | .error e => some e

/-- The error of `checkTransaction`, with the duplicate-input check, on a transaction that is the whole input in the witness-allowed format. The outer `none` means that the reader rejects the input. -/
def checkBytes (bs : List UInt8) : Option (Option CheckTransactionError) :=
  match Transaction.decodeAllowWitnessComplete bs with
  | .ok w => some (errorOf (checkTransaction w.tx true))
  | .error _ => none

/-- The records of a corpus file, each with the last comment before it. -/
def recordsWithComments (text : String) : Except String (Array (String × List UInt8)) := do
  let json ← Lean.Json.parse text
  let rows ← json.getArr?
  let mut comment := ""
  let mut out := #[]
  for row in rows do
    let fields ← row.getArr?
    if fields.size == 1 then
      let text ← fields[0]!.getStr?
      -- This note stands between two comments and their records, and names no rule.
      unless text == "Note the input is just required to make the tester happy" do comment := text
      continue
    if fields.size != 3 then throw s!"record with {fields.size} fields"
    out := out.push (comment, (← parseHex (← fields[1]!.getStr?)).toList)
  return out

/-- The expected result of each record under "Tests for CheckTransaction()", by its comment. -/
def namedInvalid : List (String × Option CheckTransactionError) := [
  ("No outputs", some .voutEmpty),
  ("Negative output", some .voutNegative),
  ("MAX_MONEY + 1 output", none),
  ("MAX_MONEY output + 1 output", none),
  ("Duplicate inputs", some .inputsDuplicate),
  ("Coinbase of size 1", some .coinbaseLength),
  ("Coinbase of size 101", some .coinbaseLength),
  ("Null txin, but without being a coinbase (because there are two inputs)", some .prevoutNull)]

/-- The number of records under each comment. The last comment has two records, with the null outpoint first and second. -/
def expectedCount (name : String) : Nat :=
  if name.startsWith "Null txin" then 2 else 1

/-- A script from its bytes. -/
def script (bs : List UInt8) : Script :=
  ⟨(CountedList.ofList? bs).getD ⟨[], by decide⟩⟩

/-- A push of `n` zero bytes, for `n` below 76. -/
def push (n : Nat) : List UInt8 := n.toUInt8 :: List.replicate n 0

/-- `CheckTransaction` on Core's corpus, Core's four sigop counts, and `CheckBlock` on the genesis block. -/
def check : IO Nat := do
  let mut failures := 0
  let valid ← IO.FS.readFile "tests/transaction/corpus/tx_valid.json"
  match recordsWithComments valid with
  | .error e => failures := failures + (← require s!"tx_valid.json: {e}" false)
  | .ok records =>
    failures := failures + (← require "tx_valid.json: 118 records" (records.size == 118))
    for (_, bs) in records do
      failures := failures + (← require "tx_valid.json: CheckTransaction accepts each record"
        (checkBytes bs == some none))
  let invalid ← IO.FS.readFile "tests/transaction/corpus/tx_invalid.json"
  match recordsWithComments invalid with
  | .error e => failures := failures + (← require s!"tx_invalid.json: {e}" false)
  | .ok records =>
    for (name, expected) in namedInvalid do
      let found := records.filter fun (comment, _) => comment == name
      failures := failures + (← require s!"tx_invalid.json: records for {name}" (found.size == expectedCount name))
      for (_, bs) in found do
        failures := failures + (← require s!"tx_invalid.json: {name}" (checkBytes bs == some expected))
    -- The amounts of the two MAX_MONEY records, read from the decoded outputs.
    let amounts (name : String) : List Int :=
      (records.filter fun (comment, _) => comment == name).toList.flatMap fun (_, bs) =>
        match Transaction.decodeAllowWitnessComplete bs with
        | .ok w => w.tx.outputs.val.map fun o => o.amount.toInt
        | .error _ => []
    failures := failures + (← require "tx_invalid.json: amount of MAX_MONEY + 1 output"
      (amounts "MAX_MONEY + 1 output" == [2100000000000001]))
    failures := failures + (← require "tx_invalid.json: amounts of MAX_MONEY output + 1 output"
      (amounts "MAX_MONEY output + 1 output" == [2100000000000000, 256]))
  -- sigopcount_tests.cpp, GetSigOpCount: the empty script, s1, s2 and a P2SH script, with fAccurate false.
  let s1 := [0x51] ++ push 20 ++ push 20 ++ [0x52, 0xae, 0x63, 0xac, 0x68]
  let s2 := [0x51] ++ push 33 ++ push 33 ++ push 33 ++ [0x53, 0xae]
  let p2sh := [0xa9] ++ push 20 ++ [0x87]
  failures := failures + (← require "sigops: empty script" ((script []).getSigOpCount == 0))
  failures := failures + (← require "sigops: s1" ((script s1).getSigOpCount == 21))
  failures := failures + (← require "sigops: s2" ((script s2).getSigOpCount == 20))
  failures := failures + (← require "sigops: P2SH script" ((script p2sh).getSigOpCount == 0))
  -- The mainnet genesis block.
  match KnownAnswers.Genesis.coinbase, KnownAnswers.Genesis.header 1386325540 99943 0x1e0ffff0 with
  | .ok coinbase, .ok header =>
    let raw := header.toList ++ [0x01] ++ coinbase.toList
    match Block.decodeComplete .allowWitness raw with
    | .error _ => failures := failures + (← require "genesis block: decode" false)
    | .ok b =>
      failures := failures + (← require "genesis block: encodes to its bytes"
        (Block.encode .allowWitness b == raw && Block.encode .base b == raw))
      failures := failures + (← require "genesis block: CheckBlock accepts with both flags"
        (errorOf (checkBlock .mainnet true true b) == none))
      failures := failures + (← require "genesis block: one legacy sigop"
        (legacySigOpCount b.transactions == 1))
  | _, _ => failures := failures + (← require "genesis block: fixture" false)
  if failures == 0 then
    IO.println "block check: 118 valid records, 9 named records, 4 sigop counts and the genesis block agree"
  return failures

end KnownAnswers.BlockCheck

/-- Named checks for the test driver. -/
def KnownAnswers.BlockCheck.checks : List (String × IO Nat) := [
  ("block-check", KnownAnswers.BlockCheck.check)
]
