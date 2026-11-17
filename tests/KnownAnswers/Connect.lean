import DogeLib.Block
import DogeLib.Script
import KnownAnswers.Common
import KnownAnswers.Genesis

/-!
## The accurate and P2SH counts of signature operations, coinbase maturity, and the genesis block in `ConnectBlock`

The expected values come from Dogecoin Core's unit tests and its chain parameters at the pin.
None of them comes from DogeLib.

- `GetSigOpCount`, `src/test/sigopcount_tests.cpp`, lines 28 to 64 (SOURCES.md D109): the counts with `fAccurate` true of four scripts, and the counts of two `scriptSig` values against a Pay to Script Hash (P2SH) script.
  The test pushes each redeem script with `CScript::operator<<` on a byte vector, which writes the shortest push (D24).
- `nCoinbaseMaturity`, `src/chainparams.cpp`, lines 92 and 131 (D100): 30 in the record of height 0, and 240 in the record of height 145,000, which the record of height 371,337 copies.
- The genesis block: `ConnectBlock` accepts it after `CheckBlock` and changes no coin (`src/validation.cpp`, lines 1804 and 1819 to 1825, D112). A mainnet node accepts that block.
-/
namespace KnownAnswers.Connect
open DogeLib DogeLib.Block DogeLib.Transaction
open KnownAnswers.Block (require)

/-- A push of `n` zero bytes, for `n` below 76. -/
def push (n : Nat) : List UInt8 := n.toUInt8 :: List.replicate n 0

/-- The shortest push of the bytes, for fewer than 256 bytes (D24, `CScript::operator<<`). -/
def pushBytes (bs : List UInt8) : List UInt8 :=
  if bs.length < 76 then bs.length.toUInt8 :: bs else 0x4c :: bs.length.toUInt8 :: bs

/-- Core's accurate and P2SH sigop counts, the two maturity values, and the genesis block in `connectBlock` and `validateBlock`. -/
def check : IO Nat := do
  let mut failures := 0
  -- sigopcount_tests.cpp, GetSigOpCount, with fAccurate true.
  let s1Start := [0x51] ++ push 20 ++ push 20 ++ [0x52, 0xae]
  let s1 := s1Start ++ [0x63, 0xac, 0x68]
  let s2 := [0x51] ++ push 33 ++ push 33 ++ push 33 ++ [0x53, 0xae]
  let p2sh := [0xa9] ++ push 20 ++ [0x87]
  failures := failures + (← require "accurate sigops: empty script" (getSigOpCountAccurate [] == 0))
  failures := failures + (← require "accurate sigops: s1 before OP_IF" (getSigOpCountAccurate s1Start == 2))
  failures := failures + (← require "accurate sigops: s1" (getSigOpCountAccurate s1 == 3))
  failures := failures + (← require "accurate sigops: s2" (getSigOpCountAccurate s2 == 3))
  failures := failures + (← require "accurate sigops: P2SH script" (getSigOpCountAccurate p2sh == 0))
  failures := failures + (← require "P2SH sigops: OP_0 and s1"
    (p2shSigOpCount ([0x00] ++ pushBytes s1) == 3))
  failures := failures + (← require "P2SH sigops: OP_1, two pushes and s2"
    (p2shSigOpCount ([0x51] ++ push 20 ++ push 20 ++ pushBytes s2) == 3))
  -- chainparams.cpp, lines 92 and 131.
  failures := failures + (← require "coinbase maturity: 30 below height 145000"
    (coinbaseMaturity 0 == 30 && coinbaseMaturity 144999 == 30))
  failures := failures + (← require "coinbase maturity: 240 from height 145000"
    (coinbaseMaturity 145000 == 240 && coinbaseMaturity 371337 == 240))
  -- The mainnet genesis block.
  match KnownAnswers.Genesis.coinbase, KnownAnswers.Genesis.header 1386325540 99943 0x1e0ffff0 with
  | .ok coinbase, .ok header =>
    let raw := header.toList ++ [0x01] ++ coinbase.toList
    match Block.decodeComplete .allowWitness raw with
    | .error _ => failures := failures + (← require "genesis block: decode" false)
    | .ok b =>
      let unchanged : Except ConnectBlockError ConnectResult → Bool
        | .ok result => result.changes.isEmpty && result.coins.entries.isEmpty
        | .error _ => false
      failures := failures + (← require "genesis block: ConnectBlock accepts and adds no coin"
        (unchanged (connectBlock Script.coreVerifier false ⟨0, Hash256.zero, none, false⟩ CoinSet.empty b)))
      failures := failures + (← require "genesis block: the five checks accept and add no coin"
        (match validateBlock Script.coreVerifier true true ⟨[], 0, none, false, false, 0, none⟩ CoinSet.empty b with
          | .ok result => result.changes.isEmpty && result.coins.entries.isEmpty
          | .error _ => false))
  | _, _ => failures := failures + (← require "genesis block: fixture" false)
  if failures == 0 then
    IO.println "block connect: 7 sigop counts, 4 maturity values and the genesis block agree"
  return failures

end KnownAnswers.Connect

/-- Named checks for the test driver. -/
def KnownAnswers.Connect.checks : List (String × IO Nat) := [
  ("block-connect", KnownAnswers.Connect.check)
]
