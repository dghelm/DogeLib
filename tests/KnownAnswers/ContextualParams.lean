import DogeLib.Block
import DogeLib.Work
import KnownAnswers.Genesis
import KnownAnswers.HeaderPow

/-!
## Contextual parameters and checkpoints

Known answers for `getContextualParams` and `lastCheckpoint` (design record 0006, stage 2), through the compiled code.

Each expected record comes from Dogecoin Core `e0a1c15`, `src/chainparams.cpp` (SOURCES.md, D14), with the line of each value.
The heights on each side of each effective height select the record that Core's `GetConsensus` (lines 494 to 506) returns there.

Ten of the 43 checkpoint hashes are compared with the double SHA-256 of a pure header from an independent source:

- The three genesis headers, which `KnownAnswers.Genesis` derives by hand from `CreateGenesisBlock` and checks against Core's asserted hashes.
- The mainnet header at height 145000 of `tests/work/mainnet-headers/headers.txt`, which predecessor links connect to the other 311 recorded headers.
- The pure headers of the six whole mainnet blocks of `tests/block/auxpow-headers.json`, at heights 371337 to 3000000.

`tests/work/mainnet-headers/README.md` and `tests/block/README.md` record the provenance of the headers.
The hash literals are read with `Work.ArithUint256.targetBytesOfHex`, the model of Core's `uint256S`.

The expected results of `lastCheckpoint` are worked out by hand from `GetLastCheckpoint` (D67, lines 18 to 30) and the `fCheckpointsEnabled` test (D33, line 3093).
-/

namespace KnownAnswers.ContextualParams
open DogeLib DogeLib.Block DogeLib.Serialization
open KnownAnswers.Block (require)

/-- One expected record: the network, the height, the source lines and the three expected fields. -/
structure RecordCase where
  /-- The network. -/
  network : Work.WorkNetwork
  /-- The height that `GetConsensus` receives. -/
  height : UInt32
  /-- The Core record that `GetConsensus` returns, with the lines of D14 that set its fields. -/
  source : String
  /-- The expected `fAllowLegacyBlocks`. -/
  allowLegacyBlocks : Bool
  /-- The expected `BIP65Height`. -/
  bip65Height : Nat
  /-- The expected `BIP66Height`. -/
  bip66Height : Nat

/-- The record cases: the first and last heights of each record of each network, and the greatest UInt32 height. -/
def recordCases : List RecordCase := [
  -- Mainnet: BIP65Height and BIP66Height at lines 86 and 87, fAllowLegacyBlocks true at line 122.
  ⟨.mainnet, 0, "consensus, lines 86, 87, 122", true, 3464751, 1034383⟩,
  ⟨.mainnet, 144999, "consensus, lines 86, 87, 122", true, 3464751, 1034383⟩,
  -- digishieldConsensus: a copy at line 126, effective from 145000 at line 127.
  ⟨.mainnet, 145000, "digishieldConsensus, lines 126, 127", true, 3464751, 1034383⟩,
  ⟨.mainnet, 371336, "digishieldConsensus, lines 126, 127", true, 3464751, 1034383⟩,
  -- auxpowConsensus: a copy at line 134, effective from 371337 at line 135, fAllowLegacyBlocks false at line 136.
  ⟨.mainnet, 371337, "auxpowConsensus, lines 134 to 136", false, 3464751, 1034383⟩,
  ⟨.mainnet, 1034382, "auxpowConsensus, lines 134 to 136", false, 3464751, 1034383⟩,
  ⟨.mainnet, 1034383, "auxpowConsensus, lines 134 to 136", false, 3464751, 1034383⟩,
  ⟨.mainnet, 3464751, "auxpowConsensus, lines 134 to 136", false, 3464751, 1034383⟩,
  ⟨.mainnet, 0xffffffff, "auxpowConsensus, lines 134 to 136", false, 3464751, 1034383⟩,
  -- Testnet: BIP65Height and BIP66Height at lines 246 and 247, fAllowLegacyBlocks true at line 279.
  ⟨.testnet, 0, "consensus, lines 246, 247, 279", true, 1854705, 708658⟩,
  ⟨.testnet, 144999, "consensus, lines 246, 247, 279", true, 1854705, 708658⟩,
  -- digishieldConsensus: a copy at line 282, effective from 145000 at line 283.
  ⟨.testnet, 145000, "digishieldConsensus, lines 282, 283", true, 1854705, 708658⟩,
  ⟨.testnet, 157499, "digishieldConsensus, lines 282, 283", true, 1854705, 708658⟩,
  -- minDifficultyConsensus: a copy at line 291, effective from 157500 at line 292.
  ⟨.testnet, 157500, "minDifficultyConsensus, lines 291, 292", true, 1854705, 708658⟩,
  ⟨.testnet, 158099, "minDifficultyConsensus, lines 291, 292", true, 1854705, 708658⟩,
  -- auxpowConsensus: a copy at line 297, effective from 158100 at line 298, fAllowLegacyBlocks false at line 300.
  ⟨.testnet, 158100, "auxpowConsensus, lines 297, 298, 300", false, 1854705, 708658⟩,
  ⟨.testnet, 0xffffffff, "auxpowConsensus, lines 297, 298, 300", false, 1854705, 708658⟩,
  -- Regtest: BIP65Height and BIP66Height at lines 390 and 391, fAllowLegacyBlocks true at line 419.
  ⟨.regtest, 0, "consensus, lines 390, 391, 419", true, 1351, 1251⟩,
  ⟨.regtest, 9, "consensus, lines 390, 391, 419", true, 1351, 1251⟩,
  -- digishieldConsensus: a copy at line 425, effective from 10 at line 426.
  ⟨.regtest, 10, "digishieldConsensus, lines 425, 426", true, 1351, 1251⟩,
  ⟨.regtest, 19, "digishieldConsensus, lines 425, 426", true, 1351, 1251⟩,
  -- auxpowConsensus: a copy at line 430, fAllowLegacyBlocks false at line 431, effective from 20 at line 432.
  ⟨.regtest, 20, "auxpowConsensus, lines 430 to 432", false, 1351, 1251⟩,
  ⟨.regtest, 0xffffffff, "auxpowConsensus, lines 430 to 432", false, 1351, 1251⟩
]

/-- Every record case. Returns the number of failures. -/
def checkRecords : IO Nat := do
  let mut failures ← require "contextual: 23 record cases" (recordCases.length == 23)
  for c in recordCases do
    let p := getContextualParams c.network c.height
    failures := failures + (← require s!"contextual: {repr c.network} height {c.height}, {c.source}"
      (p.allowLegacyBlocks == c.allowLegacyBlocks && p.bip65Height == c.bip65Height &&
        p.bip66Height == c.bip66Height))
  return failures

/-- The size and the end heights of each table: D9 lines 182 to 204, 342 to 360 and 463. -/
def checkTables : IO Nat := do
  let mut failures := 0
  for (network, size, first, last) in [(Work.WorkNetwork.mainnet, 23, 0, 5050000),
      (.testnet, 19, 0, 5900000), (.regtest, 1, 0, 0)] do
    let hs := checkpointHeights network
    failures := failures + (← require s!"checkpoints: {repr network} has {size} entries, from {first} to {last}"
      (hs.length == size && hs.head? == some first && hs.getLast? == some last))
  return failures

/-- Compare the table hash at `height` with the double SHA-256 of `h`. -/
def expectHash (network : Work.WorkNetwork) (height : Nat) (h : PureBlockHeader) : IO Nat := do
  let entry := (checkpoints network).find? (·.height == height)
  let bytes := entry.bind fun c => (Work.ArithUint256.targetBytesOfHex c.hash).map List.ofFn
  require s!"checkpoints: {repr network} hash at {height}" (bytes == some h.getHash.val)

/-- The genesis header of `KnownAnswers.Genesis`, decoded. -/
def genesisHeader (time nonce bits : UInt32) : IO PureBlockHeader := do
  let bytes ← match KnownAnswers.Genesis.header time nonce bits with
    | .ok b => pure b.toList
    | .error e => throw (IO.userError e)
  let some (h, []) := Codec.decode (α := PureBlockHeader) bytes
    | throw (IO.userError "genesis header is not 80 bytes")
  return h

/-- Ten checkpoint hashes against independent headers. Returns the number of failures. -/
def checkHashes : IO Nat := do
  -- The arguments of CreateGenesisBlock: D9 lines 155, 315 and 446.
  let mut failures ← expectHash .mainnet 0 (← genesisHeader 1386325540 99943 0x1e0ffff0)
  failures := failures + (← expectHash .testnet 0 (← genesisHeader 1391503289 997879 0x1e0ffff0))
  failures := failures + (← expectHash .regtest 0 (← genesisHeader 1296688602 2 0x207fffff))
  let range ← KnownAnswers.HeaderPow.readRangeHeaders
  let some (_, h145000) := range.find? (·.1 == 145000)
    | return failures + (← require "checkpoints: range header 145000" false)
  failures := failures + (← expectHash .mainnet 145000 h145000)
  let auxpow ← KnownAnswers.HeaderPow.readAuxPowHeaders
  failures := failures + (← require "checkpoints: six AuxPoW headers" (auxpow.size == 6))
  for (height, h) in auxpow do
    failures := failures + (← expectHash .mainnet height h.pure)
  return failures

/-- One `lastCheckpoint` case with its expected result. -/
structure LastCase where
  /-- A description of the case. -/
  label : String
  /-- The network. -/
  network : Work.WorkNetwork
  /-- `fCheckpointsEnabled`. -/
  enabled : Bool
  /-- The table heights whose hashes the block index contains, and possibly other heights. -/
  known : List Nat
  /-- The expected height, or `none` for Core's `NULL` or a disabled check. -/
  expected : Option Nat

/-- The `lastCheckpoint` cases. -/
def lastCases : List LastCase := [
  ⟨"no known checkpoint", .mainnet, true, [], none⟩,
  ⟨"disabled, every table height known", .mainnet, false, checkpointHeights .mainnet, none⟩,
  ⟨"disabled, one known", .mainnet, false, [371337], none⟩,
  ⟨"three known, ascending", .mainnet, true, [0, 145000, 371337], some 371337⟩,
  ⟨"three known, out of order", .mainnet, true, [371337, 0, 145000], some 371337⟩,
  -- 371338 and 5050001 are not table keys, so GetLastCheckpoint never looks them up.
  ⟨"a height that is not in the table", .mainnet, true, [371338], none⟩,
  ⟨"genesis and a height above the table", .mainnet, true, [0, 5050001], some 0⟩,
  ⟨"every table height known", .mainnet, true, checkpointHeights .mainnet, some 5050000⟩,
  ⟨"the last two table heights", .mainnet, true, [4303965, 5050000], some 5050000⟩,
  -- 5050000 is a mainnet key, not a testnet key.
  ⟨"a mainnet height on testnet", .testnet, true, [5050000], none⟩,
  ⟨"two testnet heights", .testnet, true, [483173, 1000000], some 1000000⟩,
  ⟨"every testnet height known", .testnet, true, checkpointHeights .testnet, some 5900000⟩,
  ⟨"regtest genesis", .regtest, true, [0], some 0⟩,
  ⟨"regtest, a mainnet height", .regtest, true, [145000], none⟩
]

/-- Every `lastCheckpoint` case. Returns the number of failures. -/
def checkLast : IO Nat := do
  let mut failures := 0
  for c in lastCases do
    let got := lastCheckpoint c.network c.enabled c.known
    failures := failures + (← require s!"lastCheckpoint: {repr c.network}, {c.label}: got {got}, expected {c.expected}"
      (got == c.expected))
  return failures

/-- Every contextual-parameter known answer. Returns the number of failures. -/
def check : IO Nat := do
  let failures := (← checkRecords) + (← checkTables) + (← checkHashes) + (← checkLast)
  if failures == 0 then
    IO.println s!"contextual parameters: {recordCases.length} records, 3 tables, 10 checkpoint hashes, {lastCases.length} lastCheckpoint cases: ok"
  return failures

end KnownAnswers.ContextualParams

/-- Named checks for contextual-parameter known answers, in alphabetical order. -/
def KnownAnswers.ContextualParams.checks : List (String × IO Nat) := [
  ("contextual parameters", KnownAnswers.ContextualParams.check)
]
