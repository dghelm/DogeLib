module

public import DogeLib.Block.Header
public import DogeLib.Transaction.Witness

/-!
# Full block headers and the AuxPoW payload

The serialization of Core's `CBlockHeader`: an 80-byte pure header, then an AuxPoW payload exactly when the AuxPoW flag is set.
The fields and their order follow these sources at the Core pin (SOURCES.md):

- `CBlockHeader::SerializationOp`, `src/primitives/block.h`, lines 37 to 48 (D41).
  It writes the pure header, then the payload when `IsAuxpow` holds.
  On read it creates a payload when the flag is set and clears it otherwise.
- `CMerkleTx::SerializationOp` and `CAuxPow::SerializationOp`, `src/auxpow.h`, lines 80 to 84 and 155 to 160 (D54).
  The payload is the transaction, `hashBlock`, `vMerkleBranch`, `nIndex`, `vChainMerkleBranch`, `nChainIndex` and `parentBlock`, in this order.
- The transaction reader and writer, `src/primitives/transaction.h`, lines 210 to 272 (D4).
  The stream version selects whether the transaction may carry witness data.

This module defines the format only.
It checks no field: `CAuxPow::check` and the proof-of-work check are separate operations.

## The read mode of the transaction

Core reads the embedded transaction with the stream's version.
Without the bit `SERIALIZE_TRANSACTION_NO_WITNESS`, the transaction reader allows witness data.
Design record 0004, section 4.6, shows from the source that the network, disk and raw RPC paths all allow witness data at the pin.
Here the mode is an explicit parameter, `TxReadMode`.
The writer uses the same mode, as Core's writer uses the stream's version.

In the witness-allowed mode, the reader keeps Core's acceptance of an extended encoding whose stacks are all empty.
That encoding and the base encoding read as the same transaction, but they have different lengths.
So the payload of a decoded header does not determine the bytes that the reader consumed.

## Source

The field names and order come from Dogecoin Core, MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
The prefix readers and writers are DogeLib's, built from the readers of `DogeLib.Serialization.Reader`.
Original notice from `src/auxpow.h`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2014 The Bitcoin developers
Copyright (c) 2014-2016 Daniel Kraft
Distributed under the MIT/X11 software license, see the accompanying
file license.txt or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization
open DogeLib.Transaction
open CompactSize (ReadError)

/-- The read mode of a transaction that a full header embeds: with witness data allowed, or base mode only (design record 0004, section 4.6). -/
inductive TxReadMode where
  /-- A stream without `SERIALIZE_TRANSACTION_NO_WITNESS`: Core's network, disk and raw RPC paths at the pin. -/
  | allowWitness
  /-- A stream with `SERIALIZE_TRANSACTION_NO_WITNESS`. -/
  | base
  deriving DecidableEq, Repr

/--
The raw fields of Core's `CAuxPow`, which extends `CMerkleTx` (D54), in serialization order.
No field is checked.
-/
structure AuxPow where
  /-- The parent block's coinbase transaction, `CMerkleTx::tx`, with the witness stacks that the reader found. -/
  tx : WitnessTransaction
  /-- `CMerkleTx::hashBlock`. Core reads it and never checks it. -/
  hashBlock : Hash256
  /-- `CMerkleTx::vMerkleBranch`: the branch from the transaction to the parent's Merkle root. -/
  merkleBranch : CountedList Hash256
  /-- The bits of `CMerkleTx::nIndex`, an `int` in Core. `AuxPow.signedIndex` is the signed value. -/
  index : UInt32
  /-- `CAuxPow::vChainMerkleBranch`: the branch from this chain's block hash to the chain Merkle root. -/
  chainMerkleBranch : CountedList Hash256
  /-- The bits of `CAuxPow::nChainIndex`, an `int` in Core. `AuxPow.signedChainIndex` is the signed value. -/
  chainIndex : UInt32
  /-- `CAuxPow::parentBlock`: the 80-byte pure header of the parent block. -/
  parentBlock : PureBlockHeader

/-- Two payloads are equal when all their fields are equal. -/
instance : DecidableEq AuxPow := fun a b =>
  if h : a.tx = b.tx ∧ a.hashBlock = b.hashBlock ∧ a.merkleBranch = b.merkleBranch ∧ a.index = b.index ∧
      a.chainMerkleBranch = b.chainMerkleBranch ∧ a.chainIndex = b.chainIndex ∧ a.parentBlock = b.parentBlock then
    .isTrue (by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      cases a; cases b; cases h1; cases h2; cases h3; cases h4; cases h5; cases h6; cases h7; rfl)
  else
    .isFalse (by intro e; cases e; exact h ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `nIndex` as Core's signed `int`: the bits of `index` read as a two's-complement `Int32`. -/
def AuxPow.signedIndex (a : AuxPow) : Int32 := a.index.toInt32

/-- `nChainIndex` as Core's signed `int`: the bits of `chainIndex` read as a two's-complement `Int32`. -/
def AuxPow.signedChainIndex (a : AuxPow) : Int32 := a.chainIndex.toInt32

/-- The fields that follow the transaction, in serialization order. -/
abbrev AuxPow.Tail :=
  Hash256 × CountedList Hash256 × UInt32 × CountedList Hash256 × UInt32 × PureBlockHeader

/-- The fields of a payload after its transaction, in serialization order. -/
def AuxPow.tail (a : AuxPow) : AuxPow.Tail :=
  (a.hashBlock, a.merkleBranch, a.index, a.chainMerkleBranch, a.chainIndex, a.parentBlock)

/-- The payload with transaction `tx` and the fields `t` after it. -/
def AuxPow.ofTail (tx : WitnessTransaction) (t : AuxPow.Tail) : AuxPow :=
  ⟨tx, t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩

/--
The raw fields of Core's `CBlockHeader` (D41): a pure header and an optional AuxPoW payload.

The type admits a payload that disagrees with the flag of the pure header.
Core's reader never produces one (`BlockHeader.read_auxpow_isSome`), but Core's in-memory headers can, and `CheckAuxPowProofOfWork` rejects them.
-/
structure BlockHeader where
  /-- The six fields of `CPureBlockHeader`. -/
  pure : PureBlockHeader
  /-- `CBlockHeader::auxpow`: the payload, or `none` for a null pointer. -/
  auxpow : Option AuxPow
  deriving DecidableEq

/-! ## Readers -/

/--
Core's read of the embedded transaction in `mode`.

The witness-allowed mode is `Transaction.readAllowWitness`.
The base mode is `Transaction.readBase`, with an empty stack per input, and its errors are wrapped in `WitnessReadError.read`.
-/
def readTx : TxReadMode → List UInt8 → Except WitnessReadError (WitnessTransaction × List UInt8)
  | .allowWitness, bs => Transaction.readAllowWitness bs
  | .base, bs =>
    match Transaction.readBase bs with
    | .error e => .error (.read e)
    | .ok (tx, rest) => .ok (WitnessTransaction.ofBase tx, rest)

/-- Core's read of a vector of 32-byte hashes: a CompactSize count within `MAX_SIZE`, then the hashes (D1). -/
def readHashes : List UInt8 → Except ReadError (CountedList Hash256 × List UInt8) :=
  CountedList.decodeBounded readFixed

/--
Core's read of the payload fields after the transaction: `hashBlock`, `vMerkleBranch`, `nIndex`, `vChainMerkleBranch`, `nChainIndex` and `parentBlock`, in this order (D54).
The result is the first error in this order.
-/
def AuxPow.readTail : List UInt8 → Except ReadError (AuxPow.Tail × List UInt8) :=
  readPair readFixed (readPair readHashes (readPair readFixed (readPair readHashes (readPair readFixed readFixed))))

/--
Core's read of an AuxPoW payload: the transaction in `mode`, then the fields of `AuxPow.readTail` (D54).
The result is the first error, and the errors of the fields after the transaction are wrapped in `WitnessReadError.read`.
It returns the payload and the remainder.
-/
def AuxPow.read (mode : TxReadMode) (bs : List UInt8) : Except WitnessReadError (AuxPow × List UInt8) :=
  match readTx mode bs with
  | .error e => .error e
  | .ok (tx, rest) =>
    match AuxPow.readTail rest with
    | .error e => .error (.read e)
    | .ok (t, rest') => .ok (AuxPow.ofTail tx t, rest')

/--
Core's read of a full header, `CBlockHeader::SerializationOp` for reading (D41), with the transaction read in `mode`.

It reads the 80-byte pure header.
If the AuxPoW flag (bit 8 of the version) is set, it then reads a payload with `AuxPow.read`.
If the flag is clear, it reads nothing more, and the header has no payload.
It reads a prefix of the input and returns the remainder.
A failure of the pure header is `truncated`, wrapped in `WitnessReadError.read`.
-/
def BlockHeader.read (mode : TxReadMode) (bs : List UInt8) :
    Except WitnessReadError (BlockHeader × List UInt8) :=
  match readFixed (α := PureBlockHeader) bs with
  | .error e => .error (.read e)
  | .ok (pure, rest) =>
    if pure.isAuxpow then
      match AuxPow.read mode rest with
      | .error e => .error e
      | .ok (a, rest') => .ok (⟨pure, some a⟩, rest')
    else .ok (⟨pure, none⟩, rest)

/-- The reasons that `BlockHeader.decodeComplete` rejects an input. -/
inductive CompleteHeaderReadError where
  /-- `BlockHeader.read` rejects the input with this error. -/
  | read (e : WitnessReadError)
  /-- The input has this many bytes after the header. -/
  | trailingBytes (count : Nat)
  deriving DecidableEq, Repr

/-- A full header that is the whole input: `BlockHeader.read mode`, then a check that no bytes remain. -/
def BlockHeader.decodeComplete (mode : TxReadMode) (bs : List UInt8) :
    Except CompleteHeaderReadError BlockHeader :=
  match BlockHeader.read mode bs with
  | .error e => .error (.read e)
  | .ok (h, []) => .ok h
  | .ok (_, rest) => .error (.trailingBytes rest.length)

/-! ## Writers -/

/--
Core's write of the embedded transaction in `mode`.
The witness-allowed mode is `WitnessTransaction.encode`: the extended form when some stack is not empty, else the base form.
The base mode writes the base serialization and drops every stack.
-/
def encodeTx : TxReadMode → WitnessTransaction → List UInt8
  | .allowWitness, w => w.encode
  | .base, w => Codec.encode w.tx

/-- Core's write of an AuxPoW payload (D54): the transaction in `mode`, then the fields after it. -/
def AuxPow.encode (mode : TxReadMode) (a : AuxPow) : List UInt8 :=
  encodeTx mode a.tx ++ Codec.encode a.tail

/--
Core's write of a full header, `CBlockHeader::SerializationOp` for writing (D41), with the transaction written in `mode`.

It writes the 80-byte pure header.
If the AuxPoW flag is set, it then writes the payload.
If the flag is clear, it writes no payload, even if the header has one.
A header with the flag set and no payload is outside Core's domain: Core's writer asserts that the payload exists.
Here that header encodes as its 80 bytes.
-/
def BlockHeader.encode (mode : TxReadMode) (h : BlockHeader) : List UInt8 :=
  Codec.encode h.pure ++
    if h.pure.isAuxpow then (h.auxpow.map (AuxPow.encode mode)).getD [] else []

end DogeLib.Block
