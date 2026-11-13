module

public import DogeLib.Block.AuxPow

/-!
# Blocks

The serialization of Core's `CBlock`: a full header, then the vector of transactions.
The fields and their order follow these sources at the Core pin (SOURCES.md):

- `CBlock::SerializationOp`, `src/primitives/block.h`, lines 87 to 91 (D108).
  It reads or writes the `CBlockHeader` part, then `vtx`.
- The vector reader `Unserialize_impl` and the reader of a `std::shared_ptr<const T>`, `src/serialize.h`, lines 676 to 692 and 801 to 805 (D1).
  The count is a CompactSize within `MAX_SIZE`, and each element is one transaction, read from the stream.
- The full header, `DogeLib.Block.AuxPow` (D41, D54), and the transaction reader and writer (D4).

This module defines the format only.
It checks no field. `checkBlock` of `DogeLib.Block.Check` is Core's `CheckBlock`.

## The read mode

Core reads every transaction of a block with the version of the stream, and that includes the transaction of an AuxPoW payload.
So one `TxReadMode` applies to the header and to every transaction.
Without the bit `SERIALIZE_TRANSACTION_NO_WITNESS`, the reader allows witness data.
That is the mode of Core's network, disk and raw RPC paths at the pin (design record 0004, section 4.6).

Core accepts a block with witness data at this layer.
`ContextualCheckBlock` rejects it later with `unexpected-witness` on main and test (SOURCES.md, D36), and this module does not model that rule.

The writer in base mode drops every witness stack.
Core uses that mode for the size tests of `CheckBlock` and `CheckTransaction`.

## Source

The field names and order come from Dogecoin Core, MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
The prefix reader and the writer are DogeLib's.
Original notice from `src/primitives/block.h`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization
open DogeLib.Transaction
open CompactSize (ReadError)

/--
The raw fields of Core's `CBlock` that its serialization writes (D108): a full header and the transactions.
No field is checked.
The memory-only member `fChecked` is not a field here. `checkBlock` states how it treats that member.
-/
structure Block where
  /-- The `CBlockHeader` part: the pure header and the optional AuxPoW payload. -/
  header : BlockHeader
  /-- `CBlock::vtx`: the transactions, each with the witness stacks that the reader found. -/
  vtx : CountedList WitnessTransaction
  deriving DecidableEq

/-- The base fields of the transactions of a block, in order. -/
def Block.transactions (b : Block) : List Transaction := b.vtx.val.map WitnessTransaction.tx

/-! ## Reader -/

/--
Exactly `n` transactions, each read in `mode` from the remainder of the one before, with the last remainder.
The values read so far are in `acc`, and each step calls itself in tail position.
The result is the first error of a transaction, if there is one.

It models the element loop of `Unserialize_impl` for `std::vector<CTransactionRef>` (D1, lines 676 to 692).
Core grows the vector in steps, which does not change the elements that it reads or the error that it reports.
-/
def readTransactionsLoop (mode : TxReadMode) :
    Nat → List UInt8 → Array WitnessTransaction →
      Except WitnessReadError (List WitnessTransaction × List UInt8)
  | 0, bs, acc => .ok (acc.toList, bs)
  | n + 1, bs, acc =>
    match readTx mode bs with
    | .error e => .error e
    | .ok (tx, rest) => readTransactionsLoop mode n rest (acc.push tx)

/--
Core's read of a block, `CBlock::SerializationOp` for reading (D108), with every transaction read in `mode`.

It reads the full header with `BlockHeader.read mode`.
It reads the count of `vtx` with Core's `ReadCompactSize`, so a count above `MAX_SIZE` is `tooLarge` before any transaction is read.
Then it reads that many transactions.
The result is the first error in this order.
It reads a prefix of the input and returns the remainder.

The last check never fails, because the list has at most `MAX_SIZE` transactions.
If it failed, the result would be `tooLarge`.
-/
def Block.read (mode : TxReadMode) (bs : List UInt8) : Except WitnessReadError (Block × List UInt8) :=
  match BlockHeader.read mode bs with
  | .error e => .error e
  | .ok (header, r1) =>
    match CompactSize.decodeBounded r1 with
    | .error e => .error (.read e)
    | .ok (count, r2) =>
      match readTransactionsLoop mode count.toNat r2 #[] with
      | .error e => .error e
      | .ok (txs, r3) =>
        match CountedList.ofList? txs with
        | none => .error (.read .tooLarge)
        | some vtx => .ok (⟨header, vtx⟩, r3)

/-- The reasons that `Block.decodeComplete` rejects an input. -/
inductive CompleteBlockReadError where
  /-- `Block.read` rejects the input with this error. -/
  | read (e : WitnessReadError)
  /-- The input has this many bytes after the block. -/
  | trailingBytes (count : Nat)
  deriving DecidableEq, Repr

/-- A block that is the whole input: `Block.read mode`, then a check that no bytes remain. -/
def Block.decodeComplete (mode : TxReadMode) (bs : List UInt8) : Except CompleteBlockReadError Block :=
  match Block.read mode bs with
  | .error e => .error (.read e)
  | .ok (b, []) => .ok b
  | .ok (_, rest) => .error (.trailingBytes rest.length)

/-! ## Writer -/

/--
Core's write of a block, `CBlock::SerializationOp` for writing (D108), with every transaction written in `mode`.
It writes the full header, the CompactSize count of `vtx`, and each transaction in order.
-/
def Block.encode (mode : TxReadMode) (b : Block) : List UInt8 :=
  BlockHeader.encode mode b.header ++ CompactSize.encode (UInt64.ofNat b.vtx.val.length) ++
    b.vtx.val.flatMap (encodeTx mode)

/--
The base size of a block: Core's `GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION | SERIALIZE_TRANSACTION_NO_WITNESS)`.
It is the length of the base-mode encoding, which holds no witness data.
The transaction of an AuxPoW payload counts in its base form too, because the flag applies to the whole stream.
-/
def Block.baseSize (b : Block) : Nat := (Block.encode .base b).length

end DogeLib.Block
