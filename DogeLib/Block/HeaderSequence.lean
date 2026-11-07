module

public import DogeLib.Block.ContextualCheck

/-!
# The block-index model

Stage 1 of design record 0008: a model of the part of Core's block index that `AcceptBlockHeader` reads (SOURCES.md, D33, lines 3205 to 3267).
Core keeps the index in `mapBlockIndex`, a map from block hashes to `CBlockIndex` entries (D69, lines 169 and 170).
Each entry holds the header fields, the height, a predecessor link `pprev` and the status bits `nStatus` (D18).

The model holds the entries in an association list, behind one interface of lookup and insertion (design record 0008, decision 3).
The other definitions read the map only through `HeaderIndex.lookup`.
An entry stores the hash of its predecessor in place of Core's pointer.
An entry without a predecessor above height 0 is an *anchor*: a fixture or a consumer can start the index at a recent block (decision 2).

`WellFormed` states the conditions of design record 0008, section 5.5, that a real index satisfies and an anchor relaxes.
The theorems take it as a hypothesis.

The module also builds the two inputs of `contextualCheckBlockHeader` that come from the index (section 5.4):

- `ancestorView`: the view of a predecessor, from its entry down through the predecessor links.
  It stops after `contextualViewDepth` entries, or at an entry without a predecessor.
- `lastCheckpointInIndex`: Core's `GetLastCheckpoint` over the index (D67, lines 18 to 30), as the height of the entry that it finds.

The step, `acceptBlockHeader`, and the sequence are later stages of the record.
The fields for chain work enter in stage 4.
The theorems are in `DogeLib.Block.Proofs.HeaderSequence`.

## Source

The model follows Core's source, which is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/chain.h`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Work

/--
One entry of the block index: the fields of Core's `CBlockIndex` (D18) that `AcceptBlockHeader` reads, apart from chain work.
`prev` is the hash of the predecessor's entry, where Core holds the pointer `pprev`.
It is `none` for the genesis entry and for an anchor.
-/
structure IndexEntry where
  /-- The 80-byte pure header of the block. Its hash is the key of the entry. -/
  header : PureBlockHeader
  /-- `nHeight`. The genesis block has height 0. -/
  height : Nat
  /-- The key of the predecessor's entry, or `none` for genesis or an anchor. -/
  prev : Option Hash256
  /-- The status bit `BLOCK_FAILED_VALID` of `nStatus` (D18, line 146). -/
  failedValid : Bool
  /-- The status bit `BLOCK_FAILED_CHILD` of `nStatus` (D18, line 147). -/
  failedChild : Bool
  /-- `IsValid(BLOCK_VALID_SCRIPTS)` without the failure bits: the validity level is at least `BLOCK_VALID_SCRIPTS` (D18, line 136). -/
  scriptsValid : Bool
  deriving DecidableEq

/-- The fields of an entry that a work view reads: `nHeight`, `nTime` and `nBits`. -/
def IndexEntry.toBlockIndex (entry : IndexEntry) : BlockIndex :=
  ⟨entry.height, entry.header.nTime, entry.header.nBits⟩

/--
The state of the block index that `AcceptBlockHeader` reads.
`entries` holds Core's `mapBlockIndex` as an association list from block hashes to entries.
`failedBlocks` holds the members of Core's `gFailedBlocks` (D33, line 180), in the order in which step 6 of the record visits them.
-/
structure HeaderIndex where
  /-- The entries, keyed by block hash. The first pair with a key shadows every later pair with that key, and `insert` adds pairs at the head. -/
  entries : List (Hash256 × IndexEntry)
  /-- The hashes of the members of `gFailedBlocks`, in visit order. -/
  failedBlocks : List Hash256
  deriving DecidableEq

/-- The entry under a hash, as `mapBlockIndex.find` gives it, or `none` when the index has no such entry.
The first pair with the key in `entries` wins. -/
def HeaderIndex.lookup (index : HeaderIndex) (hash : Hash256) : Option IndexEntry :=
  index.entries.lookup hash

/-- The index with `entry` under `hash`. The new pair goes to the head of the list, so it shadows an earlier entry with the same key.
The failed list does not change. -/
def HeaderIndex.insert (index : HeaderIndex) (hash : Hash256) (entry : IndexEntry) : HeaderIndex :=
  { index with entries := (hash, entry) :: index.entries }

/--
The hash that Core's `uint256S` reads from a literal (D22, lines 151 to 156), in internal byte order.
`uint256S` calls `SetHex`, which `Work.ArithUint256.targetBytesOfHex` transcribes for exactly 64 digits after `0x`.
Its byte `i` is byte `i` of the hash, so the last two digits give byte 0.
Every other format gives `none`.
-/
def hash256OfHex? (hex : String) : Option Hash256 :=
  (ArithUint256.targetBytesOfHex hex).map fun bytes => ⟨List.ofFn bytes, List.length_ofFn⟩

/-- The literal that each network asserts as its genesis hash, `hashGenesisBlock` (D9, lines 160, 320 and 450). -/
def genesisHashHex : WorkNetwork → String
  | .mainnet => "0x1a91e3dace36e2be3bf030a65679fe821aa1d6ef92e7c9902eb318182c355691"
  | .testnet => "0xbb0a78264637406b6360aad926284d544d7049f45189db5664f3c4d07350559e"
  | .regtest => "0x3d2160a3b5dc4a9d62e7e66a295f70313ac808440ef7400d6c0772171ce973a5"

/-- The genesis hash of a network in internal byte order, read from `genesisHashHex` with `hash256OfHex?`. -/
def genesisHash? (network : WorkNetwork) : Option Hash256 :=
  hash256OfHex? (genesisHashHex network)

/-- The hash of a checkpoint in internal byte order, read from its `uint256S` literal with `hash256OfHex?`. -/
def Checkpoint.blockHash? (checkpoint : Checkpoint) : Option Hash256 :=
  hash256OfHex? checkpoint.hash

/--
The conditions of design record 0008, section 5.5, on an index of a network.
Core's index satisfies them, except that an anchor has no predecessor above height 0.
Each condition reads the index only through `HeaderIndex.lookup`.
-/
structure WellFormed (network : WorkNetwork) (index : HeaderIndex) : Prop where
  /-- Each key is the hash of the pure header of its entry. -/
  keyHash : ∀ hash entry, index.lookup hash = some entry → entry.header.getHash = hash
  /-- If an entry has a predecessor hash, the header's `hashPrevBlock` equals it, and the index has an entry under it.
  The entry's height is that entry's height plus one (D33, lines 2773 to 2778). -/
  prevLink : ∀ hash entry prev, index.lookup hash = some entry → entry.prev = some prev →
    entry.header.hashPrevBlock = prev ∧
      ∃ parent, index.lookup prev = some parent ∧ entry.height = parent.height + 1
  /-- An entry at height 0 without a predecessor is the genesis entry: its key is the network's genesis hash.
  Every other entry without a predecessor is an anchor. -/
  genesis : ∀ hash entry, index.lookup hash = some entry → entry.prev = none → entry.height = 0 →
    genesisHash? network = some hash
  /-- Each height is below 2147483647, as `validateWorkView` requires. -/
  heightBound : ∀ hash entry, index.lookup hash = some entry → entry.height < 2147483647
  /-- Each member of the failed list has an entry with `BLOCK_FAILED_VALID`, as Core asserts (D33, line 3244). -/
  failedListed : ∀ hash ∈ index.failedBlocks, ∃ entry, index.lookup hash = some entry ∧ entry.failedValid = true

/--
The walk of the predecessor links from `entry`, with at most `fuel` entries, newest first.
Each entry becomes its `toBlockIndex`.
The walk stops when the fuel runs out, at an entry without a predecessor, or at a predecessor hash that the index lacks.
A well-formed index never lacks a predecessor hash.
-/
def ancestorWalk (index : HeaderIndex) : Nat → IndexEntry → List BlockIndex
  | 0, _ => []
  | fuel + 1, entry =>
    entry.toBlockIndex ::
      match entry.prev.bind index.lookup with
      | some parent => ancestorWalk index fuel parent
      | none => []

/--
The view of design record 0008, section 5.4, for the predecessor's entry `prev`.
The walk collects `prev` and its ancestors, newest first, and stops after `contextualViewDepth network prev.toBlockIndex` entries or at an entry without a predecessor.
`contextualCheckBlockHeader` takes this list as its view.
-/
def ancestorView (network : WorkNetwork) (index : HeaderIndex) (prev : IndexEntry) : List BlockIndex :=
  ancestorWalk index (contextualViewDepth network prev.toBlockIndex) prev

/--
The whole chain of predecessors of `prev` in the index, newest first: the walk with `prev.height + 1` entries of fuel.
In a well-formed index, each step lowers the height by one.
So the walk ends at an entry without a predecessor before the fuel runs out.
When that entry has height 0, the chain is the chain of `pprev` links that Core walks.
-/
def ancestorChain (index : HeaderIndex) (prev : IndexEntry) : List BlockIndex :=
  ancestorWalk index (prev.height + 1) prev

/--
Core's `GetLastCheckpoint` over the index (D67, lines 18 to 30), with the test of `fCheckpointsEnabled` in `ContextualCheckBlockHeader` (D33, lines 3093 to 3100).
With `checkpointsEnabled` false, the result is `none`, and check 4 does not run.
Otherwise the search walks the network's checkpoint table from the greatest height down.
It returns the height of the index entry of the first table hash that the index has.
The result is `none` when the index has none of them.
The result is the entry's own `nHeight`, which check 4 compares (D33, line 3098), not the key of the table.
-/
def lastCheckpointInIndex (network : WorkNetwork) (checkpointsEnabled : Bool) (index : HeaderIndex) :
    Option Nat :=
  if checkpointsEnabled then
    (checkpoints network).reverse.findSome? fun checkpoint =>
      (checkpoint.blockHash?.bind index.lookup).map IndexEntry.height
  else none

/-- The table heights of a network whose checkpoint hashes the index has, in table order.
It is the known list that `lastCheckpoint` of design record 0006 takes. -/
def checkpointHeightsInIndex (network : WorkNetwork) (index : HeaderIndex) : List Nat :=
  ((checkpoints network).filter fun checkpoint =>
    (checkpoint.blockHash?.bind index.lookup).isSome).map Checkpoint.height

end DogeLib.Block
