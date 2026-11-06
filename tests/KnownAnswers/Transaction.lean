import DogeLib.Transaction
import KnownAnswers.Serialization

/-!
## Transactions: the genesis coinbase, and Core's base-mode reader

Known answers for the base serialization of a transaction, its packed codec, Core's base-mode reader `readBase`, the complete reader, and the transaction ID.

The genesis coinbase is the literal of the codec section, which that section checks against the merkle root that Core asserts (SOURCES.md, D9).
Its expected fields are the arguments of `CreateGenesisBlock` in `src/chainparams.cpp` (D9):

- Version 1 and lock time 0.
- One input with the null outpoint (`COutPoint::SetNull`, D4), the scriptSig of the coinbase, and sequence `0xffffffff`.
- One output of `88 * COIN` with the scriptPubKey.

Its transaction ID must be the merkle root, because a block with one transaction has that transaction's ID as its merkle root.

The short inputs are built by hand.
Their expected results come from a reading of `UnserializeTransaction` and the `SerializationOp` methods in `src/primitives/transaction.h` (D4), with `ReadCompactSize` (D1) and `CDataStream::read` (D21).
In base mode Core reads `nVersion`, `vin`, `vout` and `nLockTime` in this order, and stops at the first failure:

- A transaction with no inputs is read as such. In base mode there is no flags byte.
- Counts above `MAX_SIZE` are `tooLarge`, and non-canonical counts are `nonCanonical`, for the inputs, the outputs and both scripts.
- When a script count is non-canonical and the output count after it is too large, the error is `nonCanonical`, the first in read order.
- Input that ends inside the outpoint, or before the lock time, is `truncated`.
- Versions and amounts with the high bit set are read and written again without change. Their signed values are the two's-complement values.
-/

namespace KnownAnswers.Transactions

open DogeLib DogeLib.Serialization DogeLib.Transaction
open DogeLib.Serialization.CompactSize (ReadError)
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Codec (coinbaseHex)
open KnownAnswers.Genesis (ofDisplay merkleRoot)
open KnownAnswers.CountedList (isError)

/-- A list as a counted list. The lists here are short, so the check never fails. -/
def countedOf {α : Type} (l : List α) : CountedList α :=
  match CountedList.ofList? l with
  | some cl => cl
  | none => ⟨[], by simp⟩

/-- A script with these bytes. -/
def script (bs : List UInt8) : Script := ⟨countedOf bs⟩

/-- `n` as `w` little-endian bytes. -/
def le (w : Nat) (n : Nat) : List UInt8 := (List.range w).map fun i => (n >>> (8 * i)).toUInt8

/-- The 36 bytes of an outpoint with hash bytes `1, 2, …, 32` and index 7. -/
def outpointBytes : List UInt8 := (List.range 32).map (fun i => (i + 1).toUInt8) ++ le 4 7

/-- Version 1. -/
def ver : List UInt8 := le 4 1

/-- The count `0x02000001`, one above `MAX_SIZE`. -/
def tooBig : List UInt8 := [0xfe, 0x01, 0x00, 0x00, 0x02]

/-- A transaction with version bits `v`, no inputs, one output of value bits `value` with an empty script, and lock time 0. -/
def noInputs (v : Nat) (value : Nat) : List UInt8 :=
  le 4 v ++ [0x00] ++ [0x01] ++ le 8 value ++ [0x00] ++ le 4 0

/-- The complete base-mode result of the slice reader, with the remainder as bytes. -/
def readSlice (s : ByteSlice) : Except CompactSize.ReadError (Transaction × List UInt8) :=
  (Transaction.readBaseSlice s).map fun (tx, rest) => (tx, rest.toList)

/-- Compare prefix and complete base-mode readers at a nonzero offset, with bytes outside both slice bounds. -/
def sliceAgrees (bs : List UInt8) : Bool :=
  let bytes : ByteArray := ⟨(0xaa :: 0xbb :: bs ++ [0xcc]).toArray⟩
  let s := (ByteSlice.ofByteArray bytes).drop 2 |>.take bs.length
  let complete := match Transaction.decodeBaseCompleteSlice s, Transaction.decodeBaseComplete bs with
    | .error e, .error e' => decide (e = e')
    | .ok a, .ok b => a == b
    | _, _ => false
  complete && match readSlice s, Transaction.readBase bs with
  | .error e, .error e' => decide (e = e')
  | .ok a, .ok b => a == b
  | _, _ => false

/-- Whether `readBase` reads all of `bs` as a transaction that `check` accepts, and the codec writes `bs` again. -/
def readsBack (bs : List UInt8) (check : Transaction → Bool) : Bool :=
  match Transaction.readBase bs with
  | .ok (tx, []) => check tx && Codec.encode tx == bs && sliceAgrees bs
  | _ => false

/-- The checks on the genesis coinbase and on short inputs, each with its name and whether it holds. -/
def cases (coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let c := coinbase.toList
  let root ← ofDisplay merkleRoot
  let scriptSig := (← parseHex "04ffff001d0104084e696e746f6e646f").toList
  let key ← parseHex "040184710fa689ad5023690c80f3a49c8f13f8d45b8c857fbcbc8bc4a8e4d3eb4b10f4d4604fa08dce601aaf0f470216fe1b51850b4acf21b179c45070ac7b03a9"
  let scriptPubKey := [0x41] ++ key.toList ++ [0xac]
  let genesis : Transaction := {
    version := 1
    inputs := countedOf [{ prevout := OutPoint.null, scriptSig := script scriptSig, sequence := 0xffffffff }]
    outputs := countedOf [{ value := 8800000000, scriptPubKey := script scriptPubKey }]
    lockTime := 0 }
  let padded : ByteArray := ⟨#[0xaa, 0xbb, 0xcc]⟩ ++ coinbase
  return [
    -- The genesis coinbase.
    ("generic codec reads the genesis coinbase", Codec.decode c == some (genesis, [])),
    ("generic codec writes the genesis coinbase", Codec.encode genesis == c),
    ("slice reader reads the genesis coinbase at offset 3",
      (readSlice ((ByteSlice.ofByteArray padded).drop 3)).toOption == some (genesis, [])),
    ("slice reader keeps one trailing byte",
      (readSlice (ByteSlice.ofByteArray ⟨(c ++ [0x00]).toArray⟩)).toOption == some (genesis, [0x00])),
    ("slice reader agrees on every truncated genesis prefix",
      (List.range c.length).all fun n => sliceAgrees (c.take n)),
    ("slice reader preserves count errors at every field",
      [ver ++ tooBig, ver ++ [0xfd, 0x01, 0x00],
        ver ++ [1] ++ outpointBytes ++ tooBig,
        ver ++ [1] ++ outpointBytes ++ [0xfd, 0, 0],
        ver ++ [0] ++ tooBig, ver ++ [0, 0xfd, 2, 0],
        ver ++ [0, 1] ++ le 8 0 ++ tooBig,
        ver ++ [0, 1] ++ le 8 0 ++ [0xfd, 0, 0],
        ver ++ [1] ++ outpointBytes ++ [0xfd, 0, 0] ++ le 4 0 ++ tooBig].all sliceAgrees),
    ("readBase reads the genesis coinbase", (Transaction.readBase c).toOption == some (genesis, [])),
    ("complete reader reads the genesis coinbase", (Transaction.decodeBaseComplete c).toOption == some genesis),
    ("packed codec reads the genesis coinbase at offset 3",
      ((PackedCodec.decodeSlice (α := Transaction) ((ByteSlice.ofByteArray padded).drop 3)).map
        fun p => (p.1, p.2.toList)) == some (genesis, [])),
    ("packed codec writes the genesis coinbase", (PackedCodec.encode genesis).toList == c),
    ("txid of the genesis coinbase is the merkle root", genesis.txid.val == root.toList),
    ("txid in display order", genesis.txid.displayBytes == root.toList.reverse),
    ("genesis amount is 88 * COIN", genesis.outputs.val.map (·.amount) == [8800000000]),
    ("complete reader reports one trailing byte",
      match Transaction.decodeBaseComplete (c ++ [0x00]) with
      | .error (.trailingBytes 1) => true
      | _ => false),
    ("readBase keeps one trailing byte", (Transaction.readBase (c ++ [0x00])).toOption == some (genesis, [0x00])),
    ("genesis coinbase without its last byte is truncated", isError (Transaction.readBase (c.take 142)) .truncated),
    -- No inputs, base mode.
    ("a transaction with no inputs is read in base mode",
      readsBack (noInputs 1 0) fun tx => tx.inputs.val.isEmpty && tx.outputs.val.length == 1),
    -- Counts, in read order.
    ("input count above MAX_SIZE is tooLarge", isError (Transaction.readBase (ver ++ tooBig)) .tooLarge),
    ("input count non-canonical", isError (Transaction.readBase (ver ++ [0xfd, 0x01, 0x00])) .nonCanonical),
    ("scriptSig count above MAX_SIZE is tooLarge",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes ++ tooBig)) .tooLarge),
    ("scriptSig count non-canonical",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes ++ [0xfd, 0x00, 0x00])) .nonCanonical),
    ("output count above MAX_SIZE is tooLarge", isError (Transaction.readBase (ver ++ [0x00] ++ tooBig)) .tooLarge),
    ("output count non-canonical",
      isError (Transaction.readBase (ver ++ [0x00] ++ [0xfd, 0x02, 0x00])) .nonCanonical),
    ("scriptPubKey count above MAX_SIZE is tooLarge",
      isError (Transaction.readBase (ver ++ [0x00, 0x01] ++ le 8 0 ++ tooBig)) .tooLarge),
    ("scriptPubKey count non-canonical",
      isError (Transaction.readBase (ver ++ [0x00, 0x01] ++ le 8 0 ++ [0xfd, 0x00, 0x00])) .nonCanonical),
    ("non-canonical scriptSig before a too-large output count is nonCanonical",
      isError (Transaction.readBase
        (ver ++ [0x01] ++ outpointBytes ++ [0xfd, 0x00, 0x00] ++ le 4 0 ++ tooBig)) .nonCanonical),
    ("input that ends inside the outpoint is truncated",
      isError (Transaction.readBase (ver ++ [0x01] ++ outpointBytes.take 20)) .truncated),
    ("missing lock time is truncated", isError (Transaction.readBase ((noInputs 1 0).take 15)) .truncated),
    ("three bytes of lock time is truncated", isError (Transaction.readBase ((noInputs 1 0).take 18)) .truncated),
    -- Signed fields: the bits are kept.
    ("version 0xffffffff is read and written again, signed -1",
      readsBack (noInputs 0xffffffff 0) fun tx => tx.signedVersion == -1),
    ("version 0x80000000 is read and written again, signed -2^31",
      readsBack (noInputs 0x80000000 0) fun tx => tx.signedVersion.toInt == -2147483648),
    ("amount 0xffffffffffffffff is read and written again, signed -1",
      readsBack (noInputs 1 0xffffffffffffffff) fun tx => tx.outputs.val.map (·.amount) == [-1]),
    ("amount 0x8000000000000000 is read and written again, signed -2^63",
      readsBack (noInputs 1 0x8000000000000000) fun tx =>
        tx.outputs.val.map (·.amount.toInt) == [-9223372036854775808])]

/-- Every transaction known answer. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let coinbase ← parseHex coinbaseHex
    if coinbase.size != 143 then throw s!"coinbase literal has {coinbase.size} bytes, expected 143"
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL transactions: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL transactions {name}"
        failures := failures + 1
    IO.println s!"transactions: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.Transactions


/-!
## Transactions: the witness-allowed format

Known answers for `Transaction.readAllowWitness`, the complete reader, the writer and the witness hash.
The format models serialization only.
Core rejects blocks with witness data on main and test at the pin (D9, D36).
The module documentation of `DogeLib.Transaction.Witness` records the separate consensus mechanisms.

The inputs are built by hand.
Their expected results come from a reading of `UnserializeTransaction` and `SerializeTransaction` in `src/primitives/transaction.h`, lines 211 to 272 (D4), with `ReadCompactSize` (D1) and `CDataStream::read` (D21):

- After the version, an input count of zero is followed by a flags byte. Flags zero end the transaction before the lock time, with no outputs.
- With flags that are not zero, Core reads the inputs and the outputs. If bit 0 is set, it reads one stack per input.
- Only then does it reject any other flag bit, before it reads the lock time.
  So a read error in the lists or the stacks comes first, and a missing lock time does not hide the flags error.
- A stack with one empty item counts as witness data. A section of empty stacks does not, and the writer then uses the base form.

The witness hash of the genesis coinbase, which has no witness data, is its transaction ID, the merkle root that Core asserts (D9).
-/

namespace KnownAnswers.Witness

open DogeLib DogeLib.Serialization DogeLib.Transaction
open DogeLib.Serialization.CompactSize (ReadError)
open KnownAnswers.Sha256Cavp (parseHex)
open KnownAnswers.Codec (coinbaseHex)
open KnownAnswers.Genesis (ofDisplay merkleRoot)
open KnownAnswers.Transactions (le outpointBytes ver tooBig)

/-- An input with the outpoint of `outpointBytes`, an empty script and sequence `0xffffffff`. -/
def input0 : List UInt8 := outpointBytes ++ [0x00] ++ le 4 0xffffffff

/-- An output of value 0 with an empty script. -/
def output0 : List UInt8 := le 8 0 ++ [0x00]

/-- A stack with one item of one byte, `ab`. -/
def stack1 : List UInt8 := [0x01, 0x01, 0xab]

/-- Lock time 0. -/
def lock : List UInt8 := le 4 0

/-- The extended form with these flags, one input, one output and these stack bytes, without the lock time. -/
def extended (flags : UInt8) (stacks : List UInt8) : List UInt8 :=
  ver ++ [0x00, flags] ++ [0x01] ++ input0 ++ [0x01] ++ output0 ++ stacks

/-- The base form of the transaction with one input and one output. -/
def base : List UInt8 := ver ++ [0x01] ++ input0 ++ [0x01] ++ output0 ++ lock

/-- Whether the reader fails on `bs` with error `e`. -/
def isError (bs : List UInt8) (e : WitnessReadError) : Bool :=
  match Transaction.readAllowWitness bs with
  | .error e' => e' == e
  | .ok _ => false

/-- Whether the reader reads `bs` as a transaction and remainder that `check` accepts. -/
def reads (bs : List UInt8) (check : WitnessTransaction → List UInt8 → Bool) : Bool :=
  match Transaction.readAllowWitness bs with
  | .ok (w, rest) => check w rest
  | .error _ => false

/-- The checks, each with its name and whether it holds. -/
def cases (coinbase : ByteArray) : Except String (List (String × Bool)) := do
  let root ← ofDisplay merkleRoot
  return [
    -- Zero flags.
    ("zero count, zero flags and a lock time: no inputs, no outputs",
      reads (ver ++ [0x00, 0x00] ++ lock) fun w rest =>
        w.tx.inputs.val.isEmpty && w.tx.outputs.val.isEmpty && w.witnesses.isEmpty && rest.isEmpty),
    ("zero count, zero flags, no lock time: truncated", isError (ver ++ [0x00, 0x00]) (.read .truncated)),
    ("zero count and no flags byte: truncated", isError (ver ++ [0x00]) (.read .truncated)),
    -- Flag bit 0.
    ("flags 01 with one stack: read, witness data, written again",
      reads (extended 0x01 stack1 ++ lock) fun w rest =>
        w.hasWitness && rest.isEmpty && w.encode == extended 0x01 stack1 ++ lock),
    ("flags 01 with zero inputs: no stacks, written in the base form",
      reads (ver ++ [0x00, 0x01, 0x00, 0x01] ++ output0 ++ lock) fun w rest =>
        !w.hasWitness && w.witnesses.isEmpty && rest.isEmpty &&
          w.encode == ver ++ [0x00, 0x01] ++ output0 ++ lock),
    ("a stack with one empty item is witness data",
      reads (extended 0x01 [0x01, 0x00] ++ lock) fun w _ =>
        w.hasWitness && w.encode == extended 0x01 [0x01, 0x00] ++ lock),
    ("a section of empty stacks is read, and written in the base form",
      reads (extended 0x01 [0x00] ++ lock) fun w _ => !w.hasWitness && w.encode == base),
    ("flags 01, lock time missing: truncated", isError (extended 0x01 stack1) (.read .truncated)),
    ("flags 01, stack truncated: truncated", isError (extended 0x01 [0x01, 0x05, 0xab]) (.read .truncated)),
    ("flags 01, stack count non-canonical",
      isError (extended 0x01 [0xfd, 0x01, 0x00, 0x01, 0xab] ++ lock) (.read .nonCanonical)),
    ("flags 01, stack count above MAX_SIZE: tooLarge", isError (extended 0x01 tooBig) (.read .tooLarge)),
    ("flags 01, item length above MAX_SIZE: tooLarge", isError (extended 0x01 ([0x01] ++ tooBig)) (.read .tooLarge)),
    -- Other flag bits.
    ("flags 02, complete: unknownOptionalData", isError (extended 0x02 [] ++ lock) .unknownOptionalData),
    ("flags 02, lock time missing: unknownOptionalData", isError (extended 0x02 []) .unknownOptionalData),
    ("flags 02, outputs truncated: truncated, before the flags",
      isError (ver ++ [0x00, 0x02, 0x01] ++ input0 ++ [0x01] ++ output0.take 4) (.read .truncated)),
    ("flags 03, complete with a stack: unknownOptionalData", isError (extended 0x03 stack1 ++ lock) .unknownOptionalData),
    ("flags 03, a stack, lock time missing: unknownOptionalData", isError (extended 0x03 stack1) .unknownOptionalData),
    ("flags ff, complete with a stack: unknownOptionalData", isError (extended 0xff stack1 ++ lock) .unknownOptionalData),
    ("flags 03, stack truncated: truncated, before the flags",
      isError (extended 0x03 [0x01, 0x05, 0xab]) (.read .truncated)),
    ("flags 03, stack count non-canonical: nonCanonical, before the flags",
      isError (extended 0x03 [0xfd, 0x01, 0x00, 0x01, 0xab] ++ lock) (.read .nonCanonical)),
    ("flags 03, item length above MAX_SIZE: tooLarge, before the flags",
      isError (extended 0x03 ([0x01] ++ tooBig)) (.read .tooLarge)),
    -- Remainders.
    ("one trailing byte: the prefix reader keeps it",
      reads (extended 0x01 stack1 ++ lock ++ [0x00]) fun _ rest => rest == [0x00]),
    ("one trailing byte: the complete reader reports it",
      match Transaction.decodeAllowWitnessComplete (extended 0x01 stack1 ++ lock ++ [0x00]) with
      | .error (.trailingBytes 1) => true
      | _ => false),
    -- The witness hash.
    ("the genesis coinbase has no witness data, and its witness hash is its ID",
      match Transaction.decodeAllowWitnessComplete coinbase.toList with
      | .ok w => !w.hasWitness && w.wtxid.val == root.toList
      | .error _ => false)]

/-- Every known answer of the witness-allowed format. Returns the number of failures. -/
def check : IO Nat := do
  let result := do
    let coinbase ← parseHex coinbaseHex
    cases coinbase
  match result with
  | .error e =>
    IO.eprintln s!"FAIL witness format: {e}"
    return 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL witness format {name}"
        failures := failures + 1
    IO.println s!"witness format: {cs.length} checks, {failures} failures"
    return failures

end KnownAnswers.Witness


/-!
## Core's transaction corpus

Runs the serialized transactions of Core's `src/test/data/tx_valid.json` and `tx_invalid.json` at commit `e0a1c15` (SOURCES.md, D28 and D29), vendored in `tests/transaction/corpus/`, through the compiled base-mode reader and codec.

Core's `transaction_tests.cpp` (D30, lines 151 and 236) reads each one with witness data allowed, and then checks the scripts.
So a record of `tx_invalid.json` is a transaction that Core reads and then rejects for another reason. It is not a parser rejection.
Script validity is not checked here.

A record is in base mode when byte 4 of its transaction, the first byte of the input count, is not `00`.
`UnserializeTransaction` (D4, lines 219 to 230) reads a flags byte only after an empty input list.
So for these records, Core's reading with witness data allowed is the base reading.
The rule reads raw bytes, not DogeLib's reader. The other records use the witness-allowed format.

For each base-mode record, the test checks five things. `readBase` reads the whole transaction, `decodeBaseComplete` accepts it, the codec writes the same bytes again, and the packed codec reads the same transaction.
`readAllowWitness` reads the same transaction, with an empty stack for each input.

For each record in the witness-allowed format, `decodeAllowWitnessComplete` must read the whole transaction, and `WitnessTransaction.encode` must write the same bytes again.
Each of these records has a stack that is not empty, so the writer uses the extended form. The test checks that too.
The format models serialization only.
Core rejects blocks with witness data on main and test at the pin (D9, D36).
The module documentation of `DogeLib.Transaction.Witness` records the separate consensus mechanisms.

Core's harness checks none of these directly. They are DogeLib's checks on Core's bytes, not a comparison with a running Core.
-/

namespace KnownAnswers.TxCorpus

open DogeLib DogeLib.Serialization DogeLib.Transaction
open KnownAnswers.Sha256Cavp (parseHex toHex)

/-- The serialized transactions of the records of a corpus file. Fails on a record of another shape or on bad hexadecimal digits. -/
def parseCorpus (text : String) : Except String (Array (List UInt8)) := do
  let json ← Lean.Json.parse text
  let rows ← json.getArr?
  let mut out := #[]
  for row in rows do
    let fields ← row.getArr?
    if fields.size == 1 then
      let _ ← fields[0]!.getStr?
      continue
    if fields.size != 3 then throw s!"record with {fields.size} fields: {row.compress}"
    let _ ← fields[0]!.getArr?
    let _ ← fields[2]!.getStr?
    out := out.push (← parseHex (← fields[1]!.getStr?)).toList
  return out

/-- Checks one corpus file, which must hold `base` base-mode records and `witness` other records. Returns the number of failures. -/
def checkFile (path : System.FilePath) (base witness : Nat) : IO Nat := do
  let txs ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  let mut nBase := 0
  let mut nWitness := 0
  for bs in txs do
    if !KnownAnswers.Transactions.sliceAgrees bs then
      IO.eprintln s!"FAIL {path}: slice base reader disagrees on {toHex ⟨bs.toArray⟩}"
      failures := failures + 1
    if bs.length < 5 then
      IO.eprintln s!"FAIL {path}: transaction shorter than 5 bytes: {toHex ⟨bs.toArray⟩}"
      failures := failures + 1
    else if bs[4]! == 0x00 then
      nWitness := nWitness + 1
      match Transaction.decodeAllowWitnessComplete bs with
      | .ok w =>
        if !w.hasWitness || w.encode != bs then
          IO.eprintln s!"FAIL {path}: witness record not written again in the extended form: {toHex ⟨bs.toArray⟩}"
          failures := failures + 1
      | .error _ =>
        IO.eprintln s!"FAIL {path}: decodeAllowWitnessComplete does not read the witness record {toHex ⟨bs.toArray⟩}"
        failures := failures + 1
    else
      nBase := nBase + 1
      let read := match Transaction.readBase bs with
        | .ok (tx, []) => some tx
        | _ => none
      match read with
      | none =>
        IO.eprintln s!"FAIL {path}: readBase does not read the whole transaction {toHex ⟨bs.toArray⟩}"
        failures := failures + 1
      | some tx =>
        let complete := match Transaction.decodeBaseComplete bs with
          | .ok tx' => tx' == tx
          | .error _ => false
        let packed := (PackedCodec.decodeSlice (α := Transaction) (ByteSlice.ofByteArray ⟨bs.toArray⟩)).map
          fun p => (p.1, p.2.toList)
        let allowWitness := match Transaction.readAllowWitness bs with
          | .ok (w, []) => w == WitnessTransaction.ofBase tx
          | _ => false
        if !complete || Codec.encode tx != bs || packed != some (tx, []) || !allowWitness then
          IO.eprintln s!"FAIL {path}: complete reader, codec, packed codec or witness-allowed reader disagrees on {toHex ⟨bs.toArray⟩}"
          failures := failures + 1
  if nBase != base || nWitness != witness then
    IO.eprintln s!"FAIL {path}: {nBase} base-mode and {nWitness} witness records, expected {base} and {witness}"
    failures := failures + 1
  IO.println s!"{path}: {nBase} base-mode and {nWitness} witness-format records read and written again, {failures} failures"
  return failures

/-- Both corpus files. Returns the number of failures. -/
def check : IO Nat := do
  let valid ← checkFile "tests/transaction/corpus/tx_valid.json" 91 27
  let invalid ← checkFile "tests/transaction/corpus/tx_invalid.json" 68 12
  return valid + invalid

end KnownAnswers.TxCorpus


/-!
## Legacy signature hash

Two kinds of known answer, both run through the compiled `legacySignatureHash` and `legacyPreimage`.

The first is Core's corpus `src/test/data/sighash.json` at commit `e0a1c15` (SOURCES.md, D26), vendored in `tests/transaction/sighash/`.
Core's `sighash_from_data` reads each transaction with witness data allowed.
Every record's transaction has at least one input, and then that reader reads what the base reader reads (D4, lines 218 to 241).
The test checks that each transaction has an input and is read whole by `decodeBaseComplete`.
The corpus gives digests only, so it does not check preimages.

The second is a set of preimages derived by hand from `CTransactionSignatureSerializer` and `SignatureHash` (D3, lines 1054 to 1246) and `GetOp2` (D24).
Each expected byte string is written out field by field below, not computed with DogeLib's functions.

Both kinds also run through `legacyReferencePlan`, the transformation of `SignatureHashOld` (D2, lines 28 to 88).
The two plans must give the same answers, except on a script that ends in a short push.
There `SignatureHashOld` keeps the whole push, and its expected preimage is derived by hand from `FindAndDelete` (D24, lines 570 to 596).
-/

namespace KnownAnswers.LegacySighash

open DogeLib DogeLib.Serialization DogeLib.Transaction
open KnownAnswers.Sha256Cavp (parseHex toHex)
open KnownAnswers.Transactions (countedOf script le)

/-- One record of the corpus. -/
structure Record where
  tx : List UInt8
  script : List UInt8
  nIn : Int
  hashType : Int
  display : List UInt8

/-- The 32 bits of an `int` value, as Core stores them. -/
def bits32 (i : Int) : UInt32 := (i % 2 ^ 32).toNat.toUInt32

/-- The records of the corpus, after its comment. Fails on a record that is not a comment or a five-field record. -/
def parseCorpus (text : String) : Except String (Array Record) := do
  let json ← Lean.Json.parse text
  let rows ← json.getArr?
  let mut out := #[]
  for row in rows do
    let fields ← row.getArr?
    if fields.size == 1 then continue
    if fields.size != 5 then throw s!"record with {fields.size} fields: {row.compress}"
    out := out.push {
      tx := (← parseHex (← fields[0]!.getStr?)).toList
      script := (← parseHex (← fields[1]!.getStr?)).toList
      nIn := ← fields[2]!.getInt?
      hashType := ← fields[3]!.getInt?
      display := (← parseHex (← fields[4]!.getStr?)).toList }
  return out

/-- Runs every corpus record. Returns the number of failures. -/
def checkCorpus (path : System.FilePath) : IO Nat := do
  let records ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut failures := 0
  let mut fixed := 0
  let mut unparsed := 0
  if records.size != 500 then
    IO.eprintln s!"FAIL {path}: {records.size} records, expected 500"
    failures := failures + 1
  for r in records do
    match Transaction.decodeBaseComplete r.tx, CountedList.ofList? r.script with
    | .ok tx, some sc =>
      if tx.inputs.val.isEmpty || r.nIn < 0 || r.nIn ≥ 2 ^ 32 then
        IO.eprintln s!"FAIL {path}: record outside the tested domain: {toHex ⟨r.tx.toArray⟩}"
        failures := failures + 1
      else
        let plan := legacySignatureHashPlan ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)
        if plan matches .fixedDigest _ then fixed := fixed + 1
        let got := (legacySignatureHash ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)).displayBytes
        if got != r.display then
          IO.eprintln s!"FAIL {path}: nIn {r.nIn}, hashType {r.hashType}: got {toHex ⟨got.toArray⟩}, expected {toHex ⟨r.display.toArray⟩}"
          failures := failures + 1
        -- The transformation reference, SignatureHashOld.
        if !(scanOps r.script).2.isEmpty then unparsed := unparsed + 1
        let ref := (legacyReferencePlan ⟨sc⟩ tx (bits32 r.nIn) (bits32 r.hashType)).digest.displayBytes
        if ref != r.display then
          IO.eprintln s!"FAIL {path} reference: nIn {r.nIn}, hashType {r.hashType}: got {toHex ⟨ref.toArray⟩}, expected {toHex ⟨r.display.toArray⟩}"
          failures := failures + 1
    | _, _ =>
      IO.eprintln s!"FAIL {path}: transaction not read whole: {toHex ⟨r.tx.toArray⟩}"
      failures := failures + 1
  IO.println s!"{path}: {records.size} records, {fixed} with the fixed digest, {unparsed} with a script that does not parse, {failures} failures (production and reference)"
  return failures

/-! ### Mutations of the corpus records

These checks test DogeLib against itself, not against Core.
Each takes a record of Core's `sighash.json`, changes one field of its transaction, and recomputes the production digest.
The expected result, the same digest or a different one, comes from the theorems of `DogeLib.Transaction.Proofs.LegacySighashCommitment` and from the definition, not from Core.
An expected difference assumes that double SHA-256 has no collision on these inputs.
-/

/-- `t` with input `i` changed by `f`. -/
def mapInput (t : Transaction) (i : Nat) (f : TxIn → TxIn) : Transaction :=
  { t with inputs := countedOf (t.inputs.val.modify i f) }

/-- `t` with output `i` changed by `f`. -/
def mapOutput (t : Transaction) (i : Nat) (f : TxOut → TxOut) : Transaction :=
  { t with outputs := countedOf (t.outputs.val.modify i f) }

/-- A script with one more byte, `0x51`, so a different script. -/
def extendScript (s : Script) : Script := script (s.bytes.val ++ [0x51])

/-- The kinds of mutation, each with its name and whether the digest should stay the same. -/
def mutationKinds : List (String × Bool) := [
  ("ALL: lock time changes the digest", false),
  ("ALL: every scriptSig leaves it", true),
  ("ALL|ANYONECANPAY: another input's outpoint leaves it", true),
  ("ALL|ANYONECANPAY: input nIn's sequence changes it", false),
  ("NONE: removing the outputs leaves it", true),
  ("NONE: input nIn's sequence changes it", false),
  ("NONE: another input's sequence leaves it", true),
  ("SINGLE: another output's value leaves it", true),
  ("SINGLE: output nIn's value changes it", false)]

/-- The mutations of one record that apply to it: the index of the kind in `mutationKinds`, and the mutated transaction. -/
def mutations (t : Transaction) (n : Nat) (h : UInt32) : List (Nat × Transaction) :=
  let acp := HashType.anyoneCanPay h
  let none := HashType.isNone h
  let single := HashType.isSingle h
  let other := if n = 0 then 1 else 0
  let nIns := t.inputs.val.length
  let nOuts := t.outputs.val.length
  let allClass := !none && !single
  let bumpSeq := fun (i : TxIn) => { i with sequence := i.sequence + 1 }
  (if allClass && !acp then
    [(0, { t with lockTime := t.lockTime + 1 }),
     (1, { t with inputs := countedOf (t.inputs.val.map fun i => { i with scriptSig := extendScript i.scriptSig }) })]
   else []) ++
  (if allClass && acp then
    (if other < nIns then
      [(2, mapInput t other fun i => { i with prevout := { i.prevout with n := i.prevout.n + 1 } })] else []) ++
    [(3, mapInput t n bumpSeq)]
   else []) ++
  (if none && !acp then
    [(4, { t with outputs := countedOf [] }), (5, mapInput t n bumpSeq)] ++
    (if other < nIns then [(6, mapInput t other bumpSeq)] else [])
   else []) ++
  (if single && !acp && n < nOuts then
    (if other < nOuts then [(7, mapOutput t other fun o => { o with value := o.value + 1 })] else []) ++
    [(8, mapOutput t n fun o => { o with value := o.value + 1 })]
   else [])

/-- Runs every mutation on every corpus record whose plan hashes. Returns the number of failures. -/
def checkMutations (path : System.FilePath) : IO Nat := do
  let records ← match parseCorpus (← IO.FS.readFile path) with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"{path}: {e}")
  let mut counts := Array.replicate mutationKinds.length 0
  let mut failures := 0
  for r in records do
    match Transaction.decodeBaseComplete r.tx, CountedList.ofList? r.script with
    | .ok t, some sc =>
      let n := bits32 r.nIn
      let h := bits32 r.hashType
      if legacySignatureHashPlan ⟨sc⟩ t n h matches .hashBytes _ then
        let d := legacySignatureHash ⟨sc⟩ t n h
        for (k, t') in mutations t n.toNat h do
          let (name, same) := mutationKinds[k]!
          counts := counts.modify k (· + 1)
          if (legacySignatureHash ⟨sc⟩ t' n h == d) != same then
            IO.eprintln s!"FAIL {path} mutation {name}: nIn {r.nIn}, hashType {r.hashType}"
            failures := failures + 1
    | _, _ => pure ()
  for ((name, _), c) in mutationKinds.zip counts.toList do
    if c == 0 then
      IO.eprintln s!"FAIL {path} mutation {name}: no record"
      failures := failures + 1
  let summary := ", ".intercalate ((mutationKinds.zip counts.toList).map fun ((name, _), c) => s!"{name} {c}")
  IO.println s!"{path} mutations (DogeLib against itself): {summary}; {failures} failures"
  return failures

/-! ### Hand-derived preimages -/

/-- The transaction of the hand-derived cases, before its outputs. -/
def txIn0 : TxIn :=
  { prevout := ⟨⟨List.replicate 32 0x11, by simp⟩, 0⟩, scriptSig := script [0x51], sequence := 0xfffffffe }

def txIn1 : TxIn :=
  { prevout := ⟨⟨List.replicate 32 0x22, by simp⟩, 1⟩, scriptSig := script [0x52, 0x53], sequence := 0x01020304 }

def txOut0 : TxOut := { value := 5, scriptPubKey := script [0x76] }

def txOut1 : TxOut := { value := 0x0102, scriptPubKey := script [0xac] }

/-- Version 2, inputs 0 and 1, the given outputs, lock time `0x11223344`. -/
def tx (outs : List TxOut) : Transaction :=
  { version := 2, inputs := countedOf [txIn0, txIn1], outputs := countedOf outs, lockTime := 0x11223344 }

/-! Wire fields of the cases, written out byte by byte. -/

def version : List UInt8 := [0x02, 0x00, 0x00, 0x00]
def lockTime : List UInt8 := [0x44, 0x33, 0x22, 0x11]
def prevout0 : List UInt8 := List.replicate 32 0x11 ++ [0x00, 0x00, 0x00, 0x00]
def prevout1 : List UInt8 := List.replicate 32 0x22 ++ [0x01, 0x00, 0x00, 0x00]
def seq0 : List UInt8 := [0xfe, 0xff, 0xff, 0xff]
def seq1 : List UInt8 := [0x04, 0x03, 0x02, 0x01]
def zeroSeq : List UInt8 := [0x00, 0x00, 0x00, 0x00]
def emptyScript : List UInt8 := [0x00]
def out0 : List UInt8 := [0x05, 0, 0, 0, 0, 0, 0, 0] ++ [0x01, 0x76]
def out1 : List UInt8 := [0x02, 0x01, 0, 0, 0, 0, 0, 0] ++ [0x01, 0xac]
/-- `CTxOut()`: amount −1, empty script. -/
def nullOut : List UInt8 := List.replicate 8 0xff ++ [0x00]

/-- The script code `OP_DUP OP_CODESEPARATOR OP_CHECKSIG`. -/
def codeSep : List UInt8 := [0x76, 0xab, 0xac]
/-- It is written without the separator: count 2, then `76 ac`. -/
def codeSepBytes : List UInt8 := [0x02, 0x76, 0xac]

/-- Whether the production plan hashes exactly `expected`. -/
def hashesProduction (sc : List UInt8) (t : Transaction) (nIn h : UInt32) (expected : List UInt8) : Bool :=
  legacySignatureHashPlan (script sc) t nIn h == .hashBytes expected

/-- Whether the production plan and the transformation reference both hash exactly `expected`. -/
def hashes (sc : List UInt8) (t : Transaction) (nIn h : UInt32) (expected : List UInt8) : Bool :=
  hashesProduction sc t nIn h expected && legacyReferencePlan (script sc) t nIn h == .hashBytes expected

/-- Whether both plans are the fixed digest `one`. -/
def fixedBoth (sc : List UInt8) (t : Transaction) (nIn h : UInt32) : Bool :=
  legacySignatureHashPlan (script sc) t nIn h == .fixedDigest legacyOne &&
    legacyReferencePlan (script sc) t nIn h == .fixedDigest legacyOne

/--
The `FindAndDelete` cases: the script, the pattern, and the script and count that `CScript::FindAndDelete` returns (D24, lines 570 to 596).
Copies are removed only at instruction boundaries, and the bytes of a failed instruction are kept.
-/
def findAndDeleteCases : List (String × List UInt8 × List UInt8 × List UInt8 × Nat) := [
  ("empty pattern changes nothing", [0xab, 0x51], [], [0xab, 0x51], 0),
  ("no copy changes nothing", [0x51, 0x52], [0xab], [0x51, 0x52], 0),
  ("separator instructions are removed", [0x76, 0xab, 0xab, 0xac, 0xab], [0xab], [0x76, 0xac], 3),
  ("0xab inside push data is not an instruction", [0x02, 0xab, 0xab, 0x51], [0xab], [0x02, 0xab, 0xab, 0x51], 0),
  ("0xab after push data is removed", [0x02, 0xab, 0xab, 0xab, 0x51], [0xab], [0x02, 0xab, 0xab, 0x51], 1),
  ("a pattern inside push data is not at a boundary", [0x51, 0x01, 0xab], [0xab], [0x51, 0x01, 0xab], 0),
  ("repeated three-byte copies at one boundary and at a later one",
    [0x02, 0xaa, 0xbb, 0x02, 0xaa, 0xbb, 0x51, 0x02, 0xaa, 0xbb], [0x02, 0xaa, 0xbb], [0x51], 3),
  ("a copy, then a short push: the whole short push is kept",
    [0xab, 0x4c, 0x05, 0xaa], [0xab], [0x4c, 0x05, 0xaa], 1),
  ("a short push alone: unchanged", [0x4c, 0x05, 0xaa], [0xab], [0x4c, 0x05, 0xaa], 0)]

/-- The script-code cases: the script, and its bytes as `SerializeScriptCode` writes them. -/
def scriptCodeCases : List (String × List UInt8 × List UInt8) := [
  ("empty script", [], [0x00]),
  ("separator instruction is removed and not counted", codeSep, codeSepBytes),
  ("separator alone", [0xab], [0x00]),
  ("0xab inside push data is kept", [0x02, 0xab, 0xab, 0xab], [0x03, 0x02, 0xab, 0xab]),
  ("empty PUSHDATA1, then a separator", [0x4c, 0x00, 0xab], [0x02, 0x4c, 0x00]),
  ("whole PUSHDATA4 of one byte", [0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa],
    [0x06, 0x4e, 0x01, 0x00, 0x00, 0x00, 0xaa]),
  -- Short pushes: the count is of the whole script, the bytes stop at GetOp's cursor.
  ("push of 1 with no data stops after the opcode", [0x01], [0x01, 0x01]),
  ("push of 2 with 1 byte stops after the opcode", [0x02, 0xaa], [0x02, 0x02]),
  ("PUSHDATA1 with no length stops after the opcode", [0x4c], [0x01, 0x4c]),
  ("PUSHDATA1 of 5 with 1 byte stops after the length", [0x4c, 0x05, 0xaa], [0x03, 0x4c, 0x05]),
  ("PUSHDATA2 with 1 length byte stops after the opcode", [0x4d, 0x01], [0x02, 0x4d]),
  ("PUSHDATA4 of 2 with 1 byte stops after the length", [0x4e, 0x02, 0x00, 0x00, 0x00, 0xaa],
    [0x06, 0x4e, 0x02, 0x00, 0x00, 0x00]),
  ("separator, then a short PUSHDATA1", [0xab, 0x4c], [0x01, 0x4c])]

/-- The checks on hand-derived preimages, each with its name and whether it holds. -/
def cases : Except String (List (String × Bool)) := do
  let one ← parseHex "0000000000000000000000000000000000000000000000000000000000000001"
  let both := tx [txOut0, txOut1]
  let allOutputs := [0x02] ++ out0 ++ out1
  let inputsWithCode1 (otherSeq : List UInt8) :=
    [0x02] ++ prevout0 ++ emptyScript ++ otherSeq ++ prevout1 ++ codeSepBytes ++ seq1
  let scriptCodeChecks := scriptCodeCases.map fun (name, sc, expected) =>
    (s!"script code: {name}", scriptCodeBytes (script sc) == expected)
  let findAndDeleteChecks := findAndDeleteCases.map fun (name, s, b, out, n) =>
    (s!"FindAndDelete: {name}", findAndDelete s b == (out, n))
  return scriptCodeChecks ++ findAndDeleteChecks ++ [
    ("one displays as 00…01", legacyOne.displayBytes == one.toList),
    ("ALL, nIn 1",
      hashes codeSep both 1 1 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("ALL, nIn 0",
      hashes codeSep both 0 1 (version ++ [0x02] ++ prevout0 ++ codeSepBytes ++ seq0 ++ prevout1 ++ emptyScript ++
        seq1 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("NONE, nIn 1: no outputs, other sequence 0",
      hashes codeSep both 1 2 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x02, 0, 0, 0])),
    ("SINGLE, nIn 1: null output 0, other sequence 0",
      hashes codeSep both 1 3
        (version ++ inputsWithCode1 zeroSeq ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++ [0x03, 0, 0, 0])),
    ("SINGLE, nIn 0: output 0 only",
      hashes codeSep both 0 3
        (version ++ [0x02] ++ prevout0 ++ codeSepBytes ++ seq0 ++ prevout1 ++ emptyScript ++ zeroSeq ++
          [0x01] ++ out0 ++ lockTime ++ [0x03, 0, 0, 0])),
    ("SINGLE|ANYONECANPAY, nIn 1: input 1 alone with its sequence, null output 0",
      hashes codeSep both 1 0x83
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++
          [0x83, 0, 0, 0])),
    ("ALL|ANYONECANPAY, nIn 0: input 0 alone, all outputs",
      hashes codeSep both 0 0x81
        (version ++ [0x01] ++ prevout0 ++ codeSepBytes ++ seq0 ++ allOutputs ++ lockTime ++ [0x81, 0, 0, 0])),
    ("NONE|ANYONECANPAY, nIn 1: input 1 alone with its sequence, no outputs",
      hashes codeSep both 1 0x82
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ [0x00] ++ lockTime ++ [0x82, 0, 0, 0])),
    -- Other raw hash types: low 5 bits other than 2 and 3 serialize as ALL.
    ("hash type 0 serializes as ALL",
      hashes codeSep both 1 0 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x00, 0, 0, 0])),
    ("hash type 4 serializes as ALL",
      hashes codeSep both 1 4 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x04, 0, 0, 0])),
    ("hash type 0x21 serializes as ALL",
      hashes codeSep both 1 0x21 (version ++ inputsWithCode1 seq0 ++ allOutputs ++ lockTime ++ [0x21, 0, 0, 0])),
    ("hash type 0x22 serializes as NONE",
      hashes codeSep both 1 0x22 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x22, 0, 0, 0])),
    ("hash type -1 serializes as ALL|ANYONECANPAY",
      hashes codeSep both 1 (bits32 (-1))
        (version ++ [0x01] ++ prevout1 ++ codeSepBytes ++ seq1 ++ allOutputs ++ lockTime ++ [0xff, 0xff, 0xff, 0xff])),
    ("hash type 0x103 serializes as SINGLE",
      hashes codeSep both 1 0x103
        (version ++ inputsWithCode1 zeroSeq ++ [0x02] ++ nullOut ++ out1 ++ lockTime ++ [0x03, 0x01, 0, 0])),
    -- A short push in the script code.
    ("short PUSHDATA1 in the script code of input 1",
      hashesProduction [0x4c, 0x05, 0xaa] both 1 1
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    -- SignatureHashOld keeps the whole short push, so its plan differs.
    ("reference keeps the whole short PUSHDATA1",
      legacyReferencePlan (script [0x4c, 0x05, 0xaa]) both 1 1 == .hashBytes
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05, 0xaa] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("reference keeps a short push after a separator",
      legacyReferencePlan (script [0xab, 0x4c, 0x05, 0xaa]) both 1 1 == .hashBytes
        (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ [0x03, 0x4c, 0x05, 0xaa] ++ seq1 ++
          allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    -- The signed input's position (`legacyReferencePlan_allOnly_index_eq`).
    -- With an empty script code, every input of the copy has the empty script, so indices 0 and 1 give one preimage.
    ("ALL, empty script code: nIn 0 and nIn 1 hash the same bytes",
      legacySignatureHashPlan (script []) both 0 1 == legacySignatureHashPlan (script []) both 1 1 &&
        hashes [] both 0 1 (version ++ [0x02] ++ prevout0 ++ emptyScript ++ seq0 ++ prevout1 ++ emptyScript ++
          seq1 ++ allOutputs ++ lockTime ++ [0x01, 0, 0, 0])),
    ("ALL, script code 76 ab ac: nIn 0 and nIn 1 hash different bytes",
      legacySignatureHashPlan (script codeSep) both 0 1 != legacySignatureHashPlan (script codeSep) both 1 1),
    -- The fixed digest.
    ("nIn equal to the input count gives one",
      fixedBoth codeSep both 2 1),
    ("nIn 0xffffffff gives one",
      fixedBoth codeSep both 0xffffffff 1),
    ("SINGLE with no output at nIn gives one",
      fixedBoth codeSep (tx [txOut0]) 1 3),
    ("SINGLE|ANYONECANPAY with no output at nIn gives one",
      fixedBoth codeSep (tx [txOut0]) 1 0x83),
    ("ALL with no output at nIn hashes",
      hashes codeSep (tx [txOut0]) 1 1
        (version ++ inputsWithCode1 seq0 ++ [0x01] ++ out0 ++ lockTime ++ [0x01, 0, 0, 0])),
    ("NONE with no outputs hashes",
      hashes codeSep (tx []) 1 2 (version ++ inputsWithCode1 zeroSeq ++ [0x00] ++ lockTime ++ [0x02, 0, 0, 0])),
    ("the digest of the fixed plan is one",
      (legacySignatureHash (script codeSep) both 2 1).val == one.toList.reverse)]

/-- Every legacy signature-hash known answer. Returns the number of failures. -/
def check : IO Nat := do
  let corpus ← checkCorpus "tests/transaction/sighash/sighash.json"
  let corpus := corpus + (← checkMutations "tests/transaction/sighash/sighash.json")
  match cases with
  | .error e =>
    IO.eprintln s!"FAIL legacy sighash: {e}"
    return corpus + 1
  | .ok cs =>
    let mut failures := 0
    for (name, ok) in cs do
      if !ok then
        IO.eprintln s!"FAIL legacy sighash {name}"
        failures := failures + 1
    IO.println s!"legacy sighash: {cs.length} hand-derived checks, {failures} failures"
    return corpus + failures

end KnownAnswers.LegacySighash

/-- Named checks for Transaction known answers, in alphabetical order. -/
def KnownAnswers.Transaction.checks : List (String × IO Nat) := [
  ("sighash", KnownAnswers.LegacySighash.check),
  ("transactions", KnownAnswers.Transactions.check),
  ("txCorpus", KnownAnswers.TxCorpus.check),
  ("witness", KnownAnswers.Witness.check)
]
