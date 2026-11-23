module

public import Std.Data.TreeMap
public import DogeLib.Transaction.Check
public import DogeLib.Transaction.Txid

/-!
# The coin set

The unspent transaction outputs that `ConnectBlock` reads and changes: Core's `CCoins` and the part of `CCoinsViewCache` that validation uses.

The sources are at the Core pin (SOURCES.md, D113):

- `CCoins`, `src/coins.h`, lines 74 to 243, with `CCoins::Spend`, `src/coins.cpp`, lines 35 to 42.
- `CScript::IsUnspendable`, `src/script/script.h`, lines 635 to 638, with `MAX_SCRIPT_SIZE`, line 31.
- `CCoinsViewCache::AccessCoins`, `HaveInputs`, `GetOutputFor` and `ModifyNewCoins`, `src/coins.cpp`, lines 134 to 162 and 265 to 297.
- `UpdateCoins`, `src/validation.cpp`, lines 1366 to 1390.

## The model

Core keeps one `CCoins` entry for each transaction ID.
The entry has the coinbase flag, the height, and the vector `vout`, where a spent or unspendable output is null.
`TxCoins` is that entry, with `none` for a null output.
`CoinSet` maps a transaction ID to its entry.

| DogeLib | Core |
| --- | --- |
| `isUnspendable` | `CScript::IsUnspendable` |
| `TxCoins.ofTx` | `CCoins::FromTx`, with `ClearUnspendable` |
| `TxCoins.isPruned` | `CCoins::IsPruned` |
| `TxCoins.available` | `CCoins::IsAvailable`, with the output |
| `CoinSet.coin` | `AccessCoins`, then `IsAvailable`, then `vout[n]`: the lookup of `HaveInputs` and `GetOutputFor` |
| `CoinSet.haveUnspent` | `AccessCoins` returns an entry that is not pruned: the BIP30 test |
| `CoinSet.spend` | `ModifyCoins(hash)->Spend(n)` |
| `CoinSet.addTx` | `ModifyNewCoins(hash, coinbase)->FromTx(tx, height)` |

## What the model leaves out

- `CCoins::nVersion`. Validation never reads it.
- `CCoins::Cleanup`, which drops null outputs from the end of `vout`. Every read goes through `IsAvailable` or `IsPruned`, and neither can tell a dropped output from a null one.
- Pruned entries. Core's cache can keep an entry whose outputs are all null. `CoinSet` removes it. Every read treats a pruned entry as an absent one: the BIP30 test is `coins && !coins->IsPruned()`, and `HaveInputs` is `!coins || !coins->IsAvailable(n)`.
- The cache flags `DIRTY` and `FRESH`, and the layers of caches. They decide what a flush writes, not what a read returns.

Core marks a null output with the amount -1 (`CTxOut::SetNull` and `IsNull`, `src/primitives/transaction.h`, lines 157 to 166).
An output that enters the set comes from a transaction that `CheckTransaction` accepted, so its amount is not negative.
A real output is therefore never read as null.

`CoinSet.addTx` replaces the whole entry of the transaction ID, as `FromTx` does.
For a transaction that is not a coinbase, `ModifyNewCoins` throws `std::logic_error` when its cache already holds an entry that is not pruned.
`connectBlock` tests that case before it calls `addTx`.

## The key

The map is a `Std.TreeMap` over natural numbers.
`txidKey` reads the 32 bytes of a transaction ID as a big-endian number.
So the order of the keys is the order of the bytes, which is the order of `uint256::Compare` (`src/uint256.h`).
The oracle's digest of the whole set visits the entries in that order (`docs/oracle.md`).
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction

/-- `MAX_SCRIPT_SIZE` (`src/script/script.h`, line 31, D113). -/
def maxScriptSize : Nat := 10000

/-- `OP_RETURN` (`src/script/script.h`, line 82, D113). -/
def opReturn : UInt8 := 0x6a

/--
Core's `CScript::IsUnspendable` (D113, `src/script/script.h`, lines 635 to 638).
A script is unspendable when its first byte is `OP_RETURN`, or when it has more than `MAX_SCRIPT_SIZE` bytes.
-/
def isUnspendable (s : Script) : Bool :=
  s.bytes.val.head? == some opReturn || s.bytes.val.length > maxScriptSize

/-- One unspent output with the facts of its transaction that validation reads: the output of `GetOutputFor`, and `nHeight` and `fCoinBase` of its `CCoins` entry. -/
structure Coin where
  /-- The output: its amount and its script. -/
  out : TxOut
  /-- The height of the block that has the transaction, `CCoins::nHeight`. -/
  height : Nat
  /-- Whether the transaction is a coinbase, `CCoins::fCoinBase`. -/
  coinbase : Bool
  deriving DecidableEq

/-- The amount of a coin as an integer. -/
def Coin.value (c : Coin) : Int := c.out.amount.toInt

/-- The entry of one transaction ID: Core's `CCoins` (D113, `src/coins.h`, lines 74 to 243), without `nVersion`. -/
structure TxCoins where
  /-- The transaction ID, which is the key of the entry. -/
  txid : Hash256
  /-- Whether the transaction is a coinbase, `fCoinBase`. -/
  coinbase : Bool
  /-- The height of the block that has the transaction, `nHeight`. -/
  height : Nat
  /-- The outputs, `vout`, with `none` for a null output: one that is spent or unspendable. -/
  outputs : List (Option TxOut)
  deriving DecidableEq

/--
Core's `CCoins::FromTx` (D113, `src/coins.h`, lines 90 to 96) for a transaction in a block at `height`.
It copies the outputs, and `ClearUnspendable` makes each unspendable output null.
-/
def TxCoins.ofTx (tx : Transaction) (height : Nat) : TxCoins :=
  ⟨tx.txid, tx.isCoinBase, height,
    tx.outputs.val.map fun o => if isUnspendable o.scriptPubKey then none else some o⟩

/-- Core's `CCoins::IsPruned` (D113, `src/coins.h`, lines 229 to 234): every output is null. -/
def TxCoins.isPruned (c : TxCoins) : Bool := c.outputs.all Option.isNone

/-- The output at index `n` when Core's `CCoins::IsAvailable(n)` holds (D113, `src/coins.h`, lines 223 to 225): the index is inside `vout`, and the output is not null. -/
def TxCoins.available (c : TxCoins) (n : Nat) : Option TxOut := (c.outputs[n]?).join

/-- Core's `CCoins::Spend(n)` (D113, `src/coins.cpp`, lines 35 to 42): the output at index `n` becomes null. An index outside `vout` changes nothing. -/
def TxCoins.spend (c : TxCoins) (n : Nat) : TxCoins := { c with outputs := c.outputs.set n none }

/-- The key of a transaction ID in the coin set: its 32 bytes as a big-endian number. -/
def txidKey (h : Hash256) : Nat := h.val.foldl (fun n b => n * 256 + b.toNat) 0

/-- The coin set: for each transaction ID that has an output that is not null, its `TxCoins` entry. -/
structure CoinSet where
  /-- The entries, under `txidKey` of their transaction IDs. -/
  entries : Std.TreeMap Nat TxCoins

/-- The set with no coin. -/
def CoinSet.empty : CoinSet := ⟨{}⟩

/-- The entry of a transaction ID: Core's `AccessCoins` (D113, `src/coins.cpp`, lines 155 to 162). -/
def CoinSet.accessCoins (s : CoinSet) (txid : Hash256) : Option TxCoins := s.entries[txidKey txid]?

/--
The coin of an outpoint, or `none` when Core's `HaveInputs` test fails for it (D113, `src/coins.cpp`, lines 284 to 297): the transaction ID has no entry, or the output is not available.
The coin has the output that `GetOutputFor` returns (lines 265 to 270).
-/
def CoinSet.coin (s : CoinSet) (o : OutPoint) : Option Coin :=
  match s.accessCoins o.hash with
  | none => none
  | some c => (c.available o.n.toNat).map fun out => ⟨out, c.height, c.coinbase⟩

/-- The BIP30 test of `ConnectBlock` (D101, lines 1880 to 1886): the transaction ID has an entry that is not pruned. -/
def CoinSet.haveUnspent (s : CoinSet) (txid : Hash256) : Bool :=
  match s.accessCoins txid with
  | none => false
  | some c => !c.isPruned

/--
The step of `UpdateCoins` for one input (D113, `src/validation.cpp`, lines 1370 to 1378): the output of the outpoint becomes null.
An entry that becomes pruned leaves the set.
Core asserts that the output is available. Without an entry the set does not change.
-/
def CoinSet.spend (s : CoinSet) (o : OutPoint) : CoinSet :=
  match s.accessCoins o.hash with
  | none => s
  | some c =>
    let c' := c.spend o.n.toNat
    if c'.isPruned then ⟨s.entries.erase (txidKey o.hash)⟩ else ⟨s.entries.insert (txidKey o.hash) c'⟩

/--
The last step of `UpdateCoins` (D113, `src/validation.cpp`, line 1389): the entry of the transaction's ID becomes `TxCoins.ofTx tx height`.
An earlier entry of that ID is replaced.
A transaction whose outputs are all unspendable gets no entry.
-/
def CoinSet.addTx (s : CoinSet) (tx : Transaction) (height : Nat) : CoinSet :=
  let c := TxCoins.ofTx tx height
  if c.isPruned then ⟨s.entries.erase (txidKey c.txid)⟩ else ⟨s.entries.insert (txidKey c.txid) c⟩

/-- The value of an entry: the sum of the amounts of its outputs that are not null, as an integer. -/
def TxCoins.value (c : TxCoins) : Int := ((c.outputs.filterMap id).map fun o => o.amount.toInt).sum

/--
The total value of a coin set: the sum of `TxCoins.value` over its entries, in the integers.

It counts every output that an entry of the set holds.
So it counts each coin that `CoinSet.coin` returns once.
It also counts an output that `CoinSet.coin` cannot return.
Such an output is in an entry whose key is not `txidKey` of a transaction ID, or it has an index of `2^32` or more.
`CoinSet.addTx` stores each entry under `txidKey` of its transaction ID, and no theorem states that a set has only such entries.
The sum has no bound, because the supply of Dogecoin is above `2^63` koinu (design record 0010, section 3).
-/
def CoinSet.totalValue (s : CoinSet) : Int := s.entries.foldl (fun acc _ c => acc + c.value) 0

/-- The coins that a new entry adds, each with its outpoint, in the order of the outputs. `index` is the index of the first output of the list. -/
def createdCoins (txid : Hash256) (height : Nat) (coinbase : Bool) (index : Nat) :
    List (Option TxOut) → List (OutPoint × Coin)
  | [] => []
  | none :: rest => createdCoins txid height coinbase (index + 1) rest
  | some out :: rest =>
    (⟨txid, UInt32.ofNat index⟩, ⟨out, height, coinbase⟩) :: createdCoins txid height coinbase (index + 1) rest

/-- The coins of an entry, each with its outpoint, in the order of the outputs. -/
def TxCoins.coins (c : TxCoins) : List (OutPoint × Coin) :=
  createdCoins c.txid c.height c.coinbase 0 c.outputs

end DogeLib.Block
