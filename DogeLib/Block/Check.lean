module

public import DogeLib.Block.Block
public import DogeLib.Block.Merkle
public import DogeLib.Block.ProofOfWork
public import DogeLib.Transaction.Check
public import DogeLib.Transaction.SigOps

/-!
# `CheckBlock`

Core's `CheckBlock`: the checks of one block that need no context.

The source is `CheckBlock`, `src/validation.cpp`, lines 2939 to 3000, at the Core pin (SOURCES.md, D106).
`checkBlock` follows its statements in order, and returns the first failure.
Each failure is one constructor of `CheckBlockError`, with Core's reject reason, denial-of-service score, reject code and corruption flag.

The parts come from other modules:

- The header check is `checkBlockHeader` (D33), which reports every proof-of-work and AuxPoW failure as `high-hash`.
- The Merkle root and its mutation flag are `blockMerkleRoot` (D42).
- The base size is `Block.baseSize`.
- Each transaction passes through `checkTransaction` with the duplicate-input check, and its signature operations come from `Transaction.getLegacySigOpCount`.

No statement of `CheckBlock` reads a witness stack.
The size test uses the base serialization, and the Merkle root uses transaction IDs.

## The member `fChecked`

Core returns `true` at once when `block.fChecked` is set (line 2943).
It sets that member after a call that passes with both flags true (lines 2996 and 2997).
A new `CBlock` has `fChecked` false, and the reader does not change that member (D108).
So a block that Core reads into a new object has `fChecked` false.
A read into an object that already has the member set keeps it set, and `checkBlock` does not describe a call on that object.
`checkBlock` is the function for a block with `fChecked` false, and it has no state.

## Integer semantics

`nSigOps` is an `unsigned int`, and `nSigOps * WITNESS_SCALE_FACTOR` is computed in that type, modulo `2^32`.
The comparison with the `int64_t` constant `MAX_BLOCK_SIGOPS_COST` then uses the wrapped product.
`checkBlock` reduces the natural-number product modulo `2^32` before the comparison, so it follows Core for every count.
`block.vtx.size()` and the serialized size are `size_t`, and their comparisons with `MAX_BLOCK_BASE_SIZE` are unsigned.

## Source

The adaptation follows Core's statements, with a named error for each `return state.DoS(...)`.
The source is MIT-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/validation.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction

/-- `WITNESS_SCALE_FACTOR` (`src/primitives/transaction.h`, line 17, D106). -/
def witnessScaleFactor : Nat := 4

/-- `MAX_BLOCK_SIGOPS_COST` (`src/consensus/consensus.h`, line 19, D106). -/
def maxBlockSigOpsCost : Nat := 80000

/-- The failures of `CheckBlock`, in source order (D106). -/
inductive CheckBlockError where
  /-- `CheckBlockHeader` fails, for the reason in `e` (line 2948). Core reports each of them as `high-hash`. -/
  | header (e : CheckPowError)
  /-- The Merkle root of the transactions is not `hashMerkleRoot` (line 2956). -/
  | merkleRoot
  /-- The Merkle computation found two equal hashes in an aligned pair, the mutation of CVE-2012-2459 (line 2962). -/
  | duplicateTransactions
  /-- No transactions, more than `MAX_BLOCK_BASE_SIZE` transactions, or a base size above `MAX_BLOCK_BASE_SIZE` bytes (line 2973). -/
  | length
  /-- The first transaction is not a coinbase (line 2977). -/
  | coinbaseMissing
  /-- A transaction after the first is a coinbase (line 2980). -/
  | coinbaseMultiple
  /-- `CheckTransaction` rejects the transaction at `index`, for the reason in `e` (line 2985). -/
  | transaction (index : Nat) (e : CheckTransactionError)
  /-- The legacy signature operations, times `WITNESS_SCALE_FACTOR`, are above `MAX_BLOCK_SIGOPS_COST` (line 2994). -/
  | sigOps
  deriving DecidableEq, Repr

/-- The reject reason that Core's `CValidationState` holds after each failure (D106).
A failed transaction keeps the reason that `CheckTransaction` set (line 2985). -/
def CheckBlockError.rejectReason : CheckBlockError → String
  | .header e => e.rejectReason
  | .merkleRoot => "bad-txnmrklroot"
  | .duplicateTransactions => "bad-txns-duplicate"
  | .length => "bad-blk-length"
  | .coinbaseMissing => "bad-cb-missing"
  | .coinbaseMultiple => "bad-cb-multiple"
  | .transaction _ e => e.rejectReason
  | .sigOps => "bad-blk-sigops"

/-- The denial-of-service score of each failure: 50 for the header (D33, line 2934), the score of `CheckTransaction` for a transaction, and 100 for every other failure.
For a transaction, `CheckBlock` calls `state.Invalid`, which adds 0 to the score that `CheckTransaction` set (D84). -/
def CheckBlockError.dosScore : CheckBlockError → Nat
  | .header _ => 50
  | .transaction _ e => e.dosScore
  | _ => 100

/-- The reject code of each failure: `REJECT_INVALID`, which is `0x10` (D84). A failed transaction keeps the code of `CheckTransaction`. -/
def CheckBlockError.rejectCode : CheckBlockError → Nat
  | .transaction _ e => e.rejectCode
  | _ => 0x10

/-- Core's `CorruptionPossible` after each failure: true for the two Merkle failures, which pass `corruptionIn` true (lines 2956 and 2962), and false for every other failure. -/
def CheckBlockError.corruptionPossible : CheckBlockError → Bool
  | .merkleRoot | .duplicateTransactions => true
  | _ => false

/--
The loop `for (const auto& tx : block.vtx) if (!CheckTransaction(*tx, state, true))` (D106, lines 2983 to 2986), from the transaction at `index`.
The result is the first failure, with the position of its transaction.
-/
def checkTransactions (index : Nat) : List Transaction → Except CheckBlockError Unit
  | [] => .ok ()
  | tx :: rest =>
    match checkTransaction tx true with
    | .error e => .error (.transaction index e)
    | .ok () => checkTransactions (index + 1) rest

/-- The legacy signature operations of the transactions of a block, as a natural number (D106, lines 2988 to 2992). Core's `nSigOps` is this number modulo `2^32`. -/
def legacySigOpCount (txs : List Transaction) : Nat :=
  (txs.map Transaction.getLegacySigOpCount).sum

/--
Core's `CheckBlock` (D106, lines 2939 to 3000) for a block with `fChecked` false, with the first failing check as its error.
Core returns `true` exactly when the result is `.ok ()`.

1. With `fCheckPOW`, `checkBlockHeader network` accepts the header. `CheckBlockHeader` uses the height-zero record of the selected network.
2. With `fCheckMerkleRoot`, the Merkle root of the transaction IDs is `hashMerkleRoot`, and then the mutation flag is clear.
3. The block has a transaction, at most `MAX_BLOCK_BASE_SIZE` transactions, and a base size of at most `MAX_BLOCK_BASE_SIZE` bytes.
4. The first transaction is a coinbase, and no other transaction is one.
5. `checkTransaction` accepts every transaction, with the duplicate-input check.
6. The legacy signature operations, times `WITNESS_SCALE_FACTOR` and modulo `2^32`, are at most `MAX_BLOCK_SIGOPS_COST`.

The checks read the base fields of each transaction, and no witness stack.
-/
def checkBlock (network : Work.WorkNetwork) (fCheckPOW fCheckMerkleRoot : Bool) (b : Block) :
    Except CheckBlockError Unit :=
  let txs := b.transactions
  match (if fCheckPOW then checkBlockHeader network b.header else .ok ()) with
  | .error e => .error (.header e)
  | .ok () =>
    let merkle := blockMerkleRoot txs
    if fCheckMerkleRoot && b.header.pure.hashMerkleRoot != merkle.root then .error .merkleRoot
    else if fCheckMerkleRoot && merkle.mutated then .error .duplicateTransactions
    else if txs.isEmpty || txs.length > maxBlockBaseSize || b.baseSize > maxBlockBaseSize then
      .error .length
    else
      match txs with
      | [] => .error .coinbaseMissing
      | first :: others =>
        if !first.isCoinBase then .error .coinbaseMissing
        else if others.any Transaction.isCoinBase then .error .coinbaseMultiple
        else
          match checkTransactions 0 txs with
          | .error e => .error e
          | .ok () =>
            if legacySigOpCount txs * witnessScaleFactor % 2 ^ 32 > maxBlockSigOpsCost then
              .error .sigOps
            else .ok ()

end DogeLib.Block
