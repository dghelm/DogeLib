import DogeLib.Block
import DogeLib.Block.Proofs.ConnectProperties
import DogeLib.Script
import KnownAnswers.Common
import KnownAnswers.Genesis

/-!
## The accurate and P2SH counts of signature operations, coinbase maturity, the genesis block in `ConnectBlock`, and the total value of the coin set

The expected values come from Dogecoin Core's unit tests and its chain parameters at the pin.
None of them comes from DogeLib.

- `GetSigOpCount`, `src/test/sigopcount_tests.cpp`, lines 28 to 64 (SOURCES.md D109): the counts with `fAccurate` true of four scripts, and the counts of two `scriptSig` values against a Pay to Script Hash (P2SH) script.
  The test pushes each redeem script with `CScript::operator<<` on a byte vector, which writes the shortest push (D24).
- `nCoinbaseMaturity`, `src/chainparams.cpp`, lines 92 and 131 (D100): 30 in the record of height 0, and 240 in the record of height 145,000, which the record of height 371,337 copies.
- The genesis block: `ConnectBlock` accepts it after `CheckBlock` and changes no coin (`src/validation.cpp`, lines 1804 and 1819 to 1825, D114). A mainnet node accepts that block.
- The total value of the coin set (`CoinSet.totalValue`) and the sum of the subsidies (`chainSubsidy`), on a chain of two blocks.
  They are the genesis block, and a block at height 1 that this file builds by hand.
  The subsidy of height 1 on the mainnet genesis hash is 68,416 coins.
  Core's own `GetDogecoinBlockSubsidy` returned that value through the harness (`CORE_VALUES` of `scripts/oracle_subsidy.py`).
  The genesis hash is the value that Core asserts in `src/chainparams.cpp` (D9).
  The expected totals follow from Core's rules by hand.
  `ConnectBlock` accepts a coinbase that pays at most the subsidy (D114, lines 1996 to 2001).
  An output whose script starts with `OP_RETURN` does not enter the set (D113, `src/coins.h`, lines 90 to 96).
  The block at height 1 has no valid proof of work, so the checks run with `fJustCheck`, which skips that test (D114, line 1804).
-/
namespace KnownAnswers.Connect
open DogeLib DogeLib.Block DogeLib.Transaction
open KnownAnswers.Block (require)

/-- A push of `n` zero bytes, for `n` below 76. -/
def push (n : Nat) : List UInt8 := n.toUInt8 :: List.replicate n 0

/-- The shortest push of the bytes, for fewer than 256 bytes (D24, `CScript::operator<<`). -/
def pushBytes (bs : List UInt8) : List UInt8 :=
  if bs.length < 76 then bs.length.toUInt8 :: bs else 0x4c :: bs.length.toUInt8 :: bs

/-- A coinbase transaction with a null outpoint, the `scriptSig` `51 51`, and the given outputs as (amount, script) pairs with scripts below 253 bytes. -/
def coinbaseBytes (outputs : List (UInt64 × List UInt8)) : List UInt8 :=
  (KnownAnswers.Genesis.le32 1).toList ++ [0x01] ++ List.replicate 32 0 ++
    (KnownAnswers.Genesis.le32 0xffffffff).toList ++ [0x02, 0x51, 0x51] ++
    (KnownAnswers.Genesis.le32 0xffffffff).toList ++ [outputs.length.toUInt8] ++
    outputs.flatMap (fun (amount, script) =>
      (KnownAnswers.Genesis.le64 amount).toList ++ [script.length.toUInt8] ++ script) ++
    (KnownAnswers.Genesis.le32 0).toList

/-- A block of version 1 on the previous hash `prev`, with a zero Merkle root and one coinbase transaction. -/
def blockBytes (prev : List UInt8) (outputs : List (UInt64 × List UInt8)) : List UInt8 :=
  (KnownAnswers.Genesis.le32 1).toList ++ prev ++ List.replicate 32 0 ++
    (KnownAnswers.Genesis.le32 1386325541).toList ++ (KnownAnswers.Genesis.le32 0x1e0ffff0).toList ++
    (KnownAnswers.Genesis.le32 0).toList ++ [0x01] ++ coinbaseBytes outputs

/--
The total value and the subsidy sum on the genesis block and one block at height 1.
`genesis` is the decoded genesis block. Returns the number of failures.
-/
def checkTotalValue (genesis : Block) : IO Nat := do
  let mut failures := 0
  -- chainparams.cpp, the asserted mainnet genesis hash (D9), in display order.
  let genesisHash := KnownAnswers.Genesis.ofDisplay "1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
  match genesisHash.toOption.bind (fun h => Hash256.ofBytes? h.toList) with
  | none => failures := failures + (← require "total value: genesis hash fixture" false)
  | some prev =>
    -- CORE_VALUES of scripts/oracle_subsidy.py: 68,416 coins at height 1.
    let subsidy : UInt64 := 68416 * 100000000
    let ctx0 : ConnectContext := ⟨0, Hash256.zero, none, false⟩
    let ctx1 : ConnectContext := ⟨1, prev, none, false⟩
    let run (outputs : List (UInt64 × List UInt8)) : Option (Block × Except ConnectBlockError CoinSet) :=
      match Block.decodeComplete .allowWitness (blockBytes prev.val outputs) with
      | .error _ => none
      | .ok b => some (b, connectChain Script.coreVerifier true CoinSet.empty [(ctx0, genesis), (ctx1, b)])
    failures := failures + (← require "total value: the empty set is worth 0" (CoinSet.empty.totalValue == (0 : Int)))
    -- The coinbase claims the whole subsidy in one spendable output.
    match run [(subsidy, [0x51])] with
    | some (b, .ok final) =>
      failures := failures + (← require "total value: a coinbase that claims the subsidy of height 1"
        (final.totalValue == 6841600000000))
      failures := failures + (← require "total value: the sum of the subsidies of the chain"
        (chainSubsidy genesis 1 [b] == 6841600000000))
      let spent : CoinSet := (b.transactions.head?.map fun tx => final.spend ⟨tx.txid, 0⟩).getD final
      failures := failures + (← require "total value: 0 after the spend of the one coin"
        (spent.totalValue == (0 : Int)))
    | _ => failures := failures + (← require "total value: a coinbase that claims the subsidy of height 1" false)
    -- One koinu more than the subsidy: bad-cb-amount.
    failures := failures + (← require "total value: one koinu above the subsidy is bad-cb-amount"
      (match run [(subsidy + 1, [0x51])] with
        | some (_, .error .coinbaseAmount) => true
        | _ => false))
    -- 5 koinu go to an OP_RETURN output, which does not enter the set.
    failures := failures + (← require "total value: an OP_RETURN output is not in the total"
      (match run [(subsidy - 5, [0x51]), (5, [0x6a])] with
        | some (_, .ok final) => final.totalValue == 6841599999995
        | _ => false))
  return failures

/-- Core's accurate and P2SH sigop counts, the two maturity values, the genesis block in `connectBlock` and `validateBlock`, and the total values of `checkTotalValue`. -/
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
      failures := failures + (← checkTotalValue b)
  | _, _ => failures := failures + (← require "genesis block: fixture" false)
  if failures == 0 then
    IO.println "block connect: 7 sigop counts, 4 maturity values, the genesis block and 6 total values agree"
  return failures

end KnownAnswers.Connect

/-- Named checks for the test driver. -/
def KnownAnswers.Connect.checks : List (String × IO Nat) := [
  ("block-connect", KnownAnswers.Connect.check)
]
