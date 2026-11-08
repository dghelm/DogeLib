module

public import DogeLib.Block.ContextualCheck
public import DogeLib.Block.ProofOfWork
public import DogeLib.Work.ChainWork

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
The theorems take it as a hypothesis, and `checkWellFormed` is its executable form.

The module also builds the two inputs of `contextualCheckBlockHeader` that come from the index (section 5.4):

- `ancestorView`: the view of a predecessor, from its entry down through the predecessor links.
  It stops after `contextualViewDepth` entries, or at an entry without a predecessor.
- `lastCheckpointInIndex`: Core's `GetLastCheckpoint` over the index (D67, lines 18 to 30), as the height of the entry that it finds.

Stage 2 adds one step, `acceptBlockHeader`: Core's `AcceptBlockHeader` (D33, lines 3205 to 3267) on the model.
The step runs the seven steps of design record 0008, section 3.1, in Core's order:

1. A known hash returns its entry, or `duplicate` when the entry has a failure flag.
2. `checkBlockHeader`, Core's `CheckBlockHeader` with `fCheckPOW` true.
3. The index must have the predecessor.
4. The predecessor must have no failure flag.
5. `contextualCheckBlockHeader` on the view and the last checkpoint that the index gives.
6. Unless the predecessor has `scriptsValid`, no member of the failed list may be an ancestor of the predecessor.
   A failure marks the entries from the predecessor down to that member with `failedChild`, and then rejects.
7. `addToBlockIndex`, the index part of Core's `AddToBlockIndex` (D33, lines 2755 to 2788).

The genesis hash skips steps 1 to 6.
Between steps 4 and 5, the adapter error `heightOutOfRange` excludes a candidate at height 2147483647 (decision 17).

Stage 3 adds the sequence, `processNewBlockHeaders`: Core's `ProcessNewBlockHeaders` (D33, lines 3270 to 3286) on the model.
It tests `checkWellFormed`, then runs the step on each header in order and stops at the first error.
`composeSequence` combines the results of two lists (section 7.2).

Stage 4 adds chain work (decision 8, option W2).
Each entry holds Core's `nChainWork` in `chainWork`.
`addToBlockIndex` sets it to the predecessor's chain work plus `Work.blockProof` of the header's `nBits`, modulo 2^256, or to `blockProof` alone without a predecessor (D33, line 2780).
An anchor holds a chain work that the caller supplies.
The model has no best header: it omits `pindexBestHeader` (lines 2782 and 2783).
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
One entry of the block index: the fields of Core's `CBlockIndex` (D18) that `AcceptBlockHeader` reads, and the chain work that `AddToBlockIndex` writes.
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
  /-- `nChainWork`: the work of the chain up to and including this block, modulo 2^256 (D18, line 183).
  `addToBlockIndex` sets it for a new entry. The caller supplies it for an anchor. -/
  chainWork : ArithUint256
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
The conditions of `WellFormed` on one entry under `hash`: the key, the predecessor link, the genesis condition and the height bound.
-/
def wellFormedEntry (network : WorkNetwork) (index : HeaderIndex) (hash : Hash256) (entry : IndexEntry) :
    Bool :=
  entry.header.getHash == hash &&
    (match entry.prev with
      | some prev =>
        entry.header.hashPrevBlock == prev &&
          (index.lookup prev).any fun parent => entry.height == parent.height + 1
      | none => entry.height != 0 || genesisHash? network == some hash) &&
    decide (entry.height < 2147483647)

/--
The executable form of `WellFormed` (`checkWellFormed_iff`).
It tests `wellFormedEntry` on each pair of the list that `HeaderIndex.lookup` finds, and skips each pair that an earlier pair with the same key shadows.
It also tests that each member of the failed list has an entry with `failedValid`.
The sequence of design record 0008, stage 3, runs it before the first header, and returns `HeaderAdapterError.notWellFormed` when it fails.
-/
def checkWellFormed (network : WorkNetwork) (index : HeaderIndex) : Bool :=
  index.entries.all (fun pair => index.lookup pair.1 != some pair.2 || wellFormedEntry network index pair.1 pair.2) &&
    index.failedBlocks.all fun hash => (index.lookup hash).any (·.failedValid)

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

/-! ## One step: `AcceptBlockHeader` -/

/--
The inputs of a step that do not come from the index (design record 0008, section 7.1).
`adjustedTime` is one value for the whole call (decision 6).
`checkpointsEnabled` is Core's `fCheckpointsEnabled` (D69).
-/
structure HeaderContext where
  /-- The network, which selects the genesis hash, the proof-of-work record and the contextual records. -/
  network : WorkNetwork
  /-- `GetAdjustedTime()`, which Core passes to `ContextualCheckBlockHeader` (D33, line 3238). -/
  adjustedTime : Int64
  /-- `fCheckpointsEnabled`, which decides whether check 4 of the contextual check runs. -/
  checkpointsEnabled : Bool

/-- The failure flags of an entry: `nStatus & BLOCK_FAILED_MASK` is not zero (D18, lines 146 to 148). -/
def IndexEntry.isFailed (entry : IndexEntry) : Bool := entry.failedValid || entry.failedChild

/-- Core's `REJECT_INVALID`, `0x10` (D84, line 13). -/
def rejectInvalid : Nat := 0x10

/-- Core's `REJECT_OBSOLETE`, `0x11` (D84, line 14). -/
def rejectObsolete : Nat := 0x11

/-- Core's `REJECT_CHECKPOINT`, `0x43` (D84, line 19). -/
def rejectCheckpoint : Nat := 0x43

/--
The denial-of-service score of a rejection of `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
Checks 1 to 4 use `state.DoS(100, …)`, and checks 5 to 7 use `state.Invalid`, which adds 0 (D84, lines 35 to 53).
An adapter error has no Core score, and the value is 0.
-/
def ContextualHeaderError.dosScore : ContextualHeaderError → Nat
  | .lateLegacyBlock | .earlyAuxpowBlock | .badDiffbits | .badForkPriorToCheckpoint => 100
  | .timeTooOld | .timeTooNew | .badVersion _ => 0
  | .emptyView | .invalidView _ | .shortView | .nextWork _ | .adjustedTimeOutOfRange => 0

/--
The reject code of a rejection of `ContextualHeaderError` (D33, lines 3066 to 3119).
Check 4 uses `REJECT_CHECKPOINT`, check 7 uses `REJECT_OBSOLETE`, and the other checks use `REJECT_INVALID`.
An adapter error has no Core code, and the value is 0.
-/
def ContextualHeaderError.rejectCode : ContextualHeaderError → Nat
  | .lateLegacyBlock | .earlyAuxpowBlock | .badDiffbits | .timeTooOld | .timeTooNew => rejectInvalid
  | .badForkPriorToCheckpoint => rejectCheckpoint
  | .badVersion _ => rejectObsolete
  | .emptyView | .invalidView _ | .shortView | .nextWork _ | .adjustedTimeOutOfRange => 0

/--
A Core rejection of one step: one constructor for each rejection of design record 0008, section 3.1.
Steps 3, 4 and 6 have the same reject reason, `bad-prevblk`, so the reason alone does not identify the step (item 8).
-/
inductive HeaderRejection where
  /-- Step 1: the hash is known, and its entry has a failure flag: `duplicate` (D33, lines 3214 to 3222). -/
  | duplicate
  /-- Step 2: `CheckBlockHeader` fails: `high-hash` (D33, lines 3224 and 3225). -/
  | highHash (error : CheckPowError)
  /-- Step 3: the index has no entry under `hashPrevBlock`: `bad-prevblk` (D33, lines 3229 to 3231). -/
  | prevBlockNotFound
  /-- Step 4: the predecessor has a failure flag: `bad-prevblk` (D33, lines 3233 and 3234). -/
  | prevBlockInvalid
  /-- Step 5: `ContextualCheckBlockHeader` rejects (D33, lines 3238 and 3239).
  The step holds only Core rejections here, never an adapter error of the contextual check. -/
  | contextual (error : ContextualHeaderError)
  /-- Step 6: the member `failed` of the failed list is an ancestor of the predecessor: `bad-prevblk` (D33, lines 3241 to 3256). -/
  | failedAncestor (failed : Hash256)
  deriving DecidableEq, Repr

/-- Core's reject reason for each rejection (D33, lines 3220, 3231, 3234 and 3253, and line 2934 for `high-hash`).
The reason of step 5 is the reason of the contextual check. -/
def HeaderRejection.rejectReason : HeaderRejection → String
  | .duplicate => "duplicate"
  | .highHash error => error.rejectReason
  | .prevBlockNotFound | .prevBlockInvalid | .failedAncestor _ => "bad-prevblk"
  | .contextual error => error.rejectReason.getD ""

/-- Core's denial-of-service score for each rejection: 0, 50, 10, 100, the score of the contextual check, and 100.
`state.Invalid` adds 0, and `state.DoS(n, …)` adds `n` (D84, lines 35 to 53). -/
def HeaderRejection.dosScore : HeaderRejection → Nat
  | .duplicate => 0
  | .highHash _ => 50
  | .prevBlockNotFound => 10
  | .prevBlockInvalid => 100
  | .contextual error => error.dosScore
  | .failedAncestor _ => 100

/-- Core's reject code for each rejection: 0 for `duplicate` and step 3, which use the default code, and `REJECT_INVALID` for steps 2, 4 and 6.
The code of step 5 is the code of the contextual check. -/
def HeaderRejection.rejectCode : HeaderRejection → Nat
  | .duplicate | .prevBlockNotFound => 0
  | .highHash _ | .prevBlockInvalid | .failedAncestor _ => rejectInvalid
  | .contextual error => error.rejectCode

/--
An input outside the domain of a step (design record 0008, section 7.1). An adapter error is not a Core verdict.
-/
inductive HeaderAdapterError where
  /-- The index fails `WellFormed`, as `checkWellFormed` tests it. The sequence of stage 3 checks this before the first header. The step does not produce it. -/
  | notWellFormed
  /-- `contextualCheckBlockHeader` returns this adapter error, for example `shortView` or `nextWork` below an anchor. -/
  | contextual (error : ContextualHeaderError)
  /-- The adjusted time is above `maxAdjustedTime`, where Core's sum `nAdjustedTime + 7200` overflows. -/
  | adjustedTimeOutOfRange
  /-- The predecessor is at height 2147483646 or above, so the candidate would be at height 2147483647 or above (decision 17). -/
  | heightOutOfRange
  deriving DecidableEq, Repr

/-- The error of a step: a Core rejection, or an adapter error for an input outside the domain. -/
inductive HeaderStepError where
  /-- A Core rejection. -/
  | rejection (rejection : HeaderRejection)
  /-- An adapter error. -/
  | adapter (error : HeaderAdapterError)
  deriving DecidableEq, Repr

/-- The error of step 5 for an error of the contextual check.
A Core rejection becomes `HeaderRejection.contextual`, and an adapter error stays an adapter error. -/
def HeaderStepError.ofContextual : ContextualHeaderError → HeaderStepError
  | .adjustedTimeOutOfRange => .adapter .adjustedTimeOutOfRange
  | error => if error.isRejection then .rejection (.contextual error) else .adapter (.contextual error)

/--
Step 5 (D33, lines 3238 and 3239): `contextualCheckBlockHeader` with the inputs that design record 0008, section 5.4, builds from the index.
The view is `ancestorView` of the predecessor's entry, and the last checkpoint is `lastCheckpointInIndex` over the whole index.
-/
def contextualCheckInIndex (ctx : HeaderContext) (index : HeaderIndex) (header : PureBlockHeader)
    (prev : IndexEntry) : Except ContextualHeaderError Unit :=
  contextualCheckBlockHeader ctx.network header (ancestorView ctx.network index prev) ctx.adjustedTime
    (lastCheckpointInIndex ctx.network ctx.checkpointsEnabled index)

/--
Core's `CBlockIndex::GetAncestor` (D35, lines 113 to 137), as the key of the ancestor's entry.
The walk starts at `entry` under the key `hash` and follows the predecessor links, with at most `fuel` entries.
It returns the key of the entry at `height`.
The result is `none` when `height` is above the entry's height, or when the walk ends first.
The walk ends at an entry without a predecessor, at a missing predecessor, or when the fuel runs out.

An anchor above `height` ends the walk, where Core would fail its assertion on `pprev` (design record 0008, section 5.3).
Core's skip pointers only shorten the walk, so they do not change the result.
-/
def ancestorHashAt (index : HeaderIndex) : Nat → Hash256 → IndexEntry → Nat → Option Hash256
  | 0, _, _, _ => none
  | fuel + 1, hash, entry, height =>
    if entry.height = height then some hash
    else if entry.height < height then none
    else
      match entry.prev with
      | some prev =>
        match index.lookup prev with
        | some parent => ancestorHashAt index fuel prev parent height
        | none => none
      | none => none

/--
The test of step 6 for one member of the failed list (D33, line 3243): `pindexPrev->GetAncestor(failedit->nHeight) == failedit`.
The predecessor's entry `prev` is under the key `prevHash`.
The walk has `prev.height + 1` entries of fuel, enough to reach height 0.
A member without an entry is no ancestor. A well-formed index has an entry for each member.
-/
def isAncestorInIndex (index : HeaderIndex) (prevHash : Hash256) (prev : IndexEntry) (member : Hash256) :
    Bool :=
  match index.lookup member with
  | some entry => ancestorHashAt index (prev.height + 1) prevHash prev entry.height == some member
  | none => false

/--
The search of step 6 (D33, lines 3242 and 3243): the first member of the failed list that is an ancestor of the predecessor.
The search visits the list in its order, where Core visits `gFailedBlocks` in address order (design record 0008, decision 5).
The verdict does not depend on that order (`failedAncestor_verdict_perm`).
-/
def failedAncestor? (index : HeaderIndex) (prevHash : Hash256) (prev : IndexEntry) : Option Hash256 :=
  index.failedBlocks.find? (isAncestorInIndex index prevHash prev)

/--
The keys that the loop of step 6 marks (D33, lines 3245 to 3250).
They are the entries from `entry` under `hash` down the predecessor links, up to the entry under `member` and without it.
The walk has at most `fuel` entries, and it also stops at an entry without a predecessor or at a missing predecessor.
-/
def failedChildPath (index : HeaderIndex) : Nat → Hash256 → IndexEntry → Hash256 → List Hash256
  | 0, _, _, _ => []
  | fuel + 1, hash, entry, member =>
    if hash = member then []
    else
      hash ::
        match entry.prev with
        | some prev =>
          match index.lookup prev with
          | some parent => failedChildPath index fuel prev parent member
          | none => []
        | none => []

/--
The marks of step 6: each key of `hashes` that the index has gets its entry with `failedChild` set, as `nStatus |= BLOCK_FAILED_CHILD` (D33, line 3247).
Each mark is an insertion of the changed entry, which shadows the earlier one.
Every other field and the failed list stay unchanged.
-/
def markFailedChild (index : HeaderIndex) (hashes : List Hash256) : HeaderIndex :=
  hashes.foldl (fun acc hash =>
    match acc.lookup hash with
    | some entry => acc.insert hash { entry with failedChild := true }
    | none => acc) index

/--
The index part of Core's `AddToBlockIndex` (D33, lines 2755 to 2788), without `nTimeMax`, `pindexBestHeader` and the dirty set.

If the index has the hash of the header, the index does not change (lines 2757 to 2761).
Otherwise the function inserts a new entry under the hash.
If the index has `hashPrevBlock`, the entry gets that predecessor and the predecessor's height plus one (lines 2772 to 2778).
Otherwise it has no predecessor and height 0.

The entry's chain work is the predecessor's chain work plus `blockProof` of the header's `nBits`, modulo 2^256.
Without a predecessor it is `blockProof` alone, as Core adds the proof to 0 (line 2780).
The entry has no failure flag and the validity level `BLOCK_VALID_TREE`, so `scriptsValid` is false (line 2781).

Core searches for `hashPrevBlock` after it inserts the new entry (line 2772).
The function searches the index before the insertion.
The two differ only for a header whose `hashPrevBlock` is its own hash, a fixed point of double SHA-256.
Core links that entry to itself at height 1, and the function inserts it with no predecessor at height 0.
Design record 0008, section 13.1, accepts this difference, because a self-link would break `WellFormed`.
-/
def addToBlockIndex (index : HeaderIndex) (header : PureBlockHeader) : HeaderIndex :=
  let hash := header.getHash
  match index.lookup hash with
  | some _ => index
  | none =>
    match index.lookup header.hashPrevBlock with
    | some parent =>
      index.insert hash ⟨header, parent.height + 1, some header.hashPrevBlock, false, false, false,
        parent.chainWork + blockProof header.nBits⟩
    | none => index.insert hash ⟨header, 0, none, false, false, false, blockProof header.nBits⟩

/-- The height bound of decision 17: a predecessor at height 2147483646 or above gives `heightOutOfRange`. -/
def maxPrevHeight : Nat := 2147483646

/--
Core's `AcceptBlockHeader` (D33, lines 3205 to 3267) on the block-index model, design record 0008, section 3.1.
It returns the index after the step and, on acceptance, the hash of the header's entry.

For the genesis hash of the network, the step skips steps 1 to 6 and runs `addToBlockIndex`.
If the index lacks the genesis hash but has a predecessor at `maxPrevHeight` or above, it returns `heightOutOfRange` (decision 17).

For any other hash, the step runs steps 1 to 7 in order and returns at the first failure.
The adapter error `heightOutOfRange` comes after step 4 and before step 5.
A rejection of step 6 returns the index with the marks of `markFailedChild`.
Every other error returns the input index.
The step never checks `WellFormed`: the sequence of stage 3 checks it before the first header.
-/
def acceptBlockHeader (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader) :
    HeaderIndex × Except HeaderStepError Hash256 :=
  let hash := header.pure.getHash
  if genesisHash? ctx.network = some hash then
    match index.lookup hash with
    | some _ => (index, .ok hash)
    | none =>
      match index.lookup header.pure.hashPrevBlock with
      | some parent =>
        if maxPrevHeight ≤ parent.height then (index, .error (.adapter .heightOutOfRange))
        else (addToBlockIndex index header.pure, .ok hash)
      | none => (addToBlockIndex index header.pure, .ok hash)
  else
    match index.lookup hash with
    | some entry =>
      if entry.isFailed then (index, .error (.rejection .duplicate)) else (index, .ok hash)
    | none =>
      match checkBlockHeader ctx.network header with
      | .error error => (index, .error (.rejection (.highHash error)))
      | .ok () =>
        match index.lookup header.pure.hashPrevBlock with
        | none => (index, .error (.rejection .prevBlockNotFound))
        | some prev =>
          if prev.isFailed then (index, .error (.rejection .prevBlockInvalid))
          else if maxPrevHeight ≤ prev.height then (index, .error (.adapter .heightOutOfRange))
          else
            match contextualCheckInIndex ctx index header.pure prev with
            | .error error => (index, .error (.ofContextual error))
            | .ok () =>
              match (if prev.scriptsValid then none
                  else failedAncestor? index header.pure.hashPrevBlock prev) with
              | some failed =>
                (markFailedChild index
                    (failedChildPath index (prev.height + 1) header.pure.hashPrevBlock prev failed),
                  .error (.rejection (.failedAncestor failed)))
              | none => (addToBlockIndex index header.pure, .ok hash)

/-! ## The sequence: `ProcessNewBlockHeaders` -/

/--
The error of a sequence (design record 0008, section 7.2): the error of one step, with the position of its header in the list.
Positions start at 0.
The adapter error `notWellFormed` comes before the first header, at position 0, also for an empty list.
-/
structure HeaderSequenceError where
  /-- The position of the failing header in the list, or 0 for `notWellFormed`. -/
  position : Nat
  /-- The error of the step at that position, or the adapter error `notWellFormed`. -/
  error : HeaderStepError
  deriving DecidableEq, Repr

/--
The result of a sequence: the index after the last step that ran, and the outcome.
On success, the outcome is the hash of the last header, or `none` for an empty list, where Core leaves `ppindex` unchanged.
-/
abbrev HeaderSequenceResult := HeaderIndex × Except HeaderSequenceError (Option Hash256)

/--
The loop of Core's `ProcessNewBlockHeaders` (D33, lines 3274 to 3282): `acceptBlockHeader` on each header in order.
`position` is the position of the first header of `headers` in the whole list, and `last` is the result so far.
The loop stops at the first error, and returns the index of that step with the error at its position.
-/
def processSteps (ctx : HeaderContext) :
    Nat → HeaderIndex → Option Hash256 → List BlockHeader → HeaderSequenceResult
  | _, index, last, [] => (index, .ok last)
  | position, index, _, header :: rest =>
    match acceptBlockHeader ctx index header with
    | (index', .error error) => (index', .error ⟨position, error⟩)
    | (index', .ok hash) => processSteps ctx (position + 1) index' (some hash) rest

/--
Core's `ProcessNewBlockHeaders` (D33, lines 3270 to 3286) on the block-index model, design record 0008, section 3.3.
The function first tests `checkWellFormed`, and returns the adapter error `notWellFormed` at position 0 when the index fails it (section 5.5).
It then calls `acceptBlockHeader` on each header in order, with one context for the whole call (decision 6), and stops at the first error.
The result holds the index after the last step that ran.
So the entries that earlier headers added stay in the index, and a rejection of step 6 keeps its marks.
On success, the result holds the hash of the last header, or `none` for an empty list.

The function does not require that a header links to the header before it.
Each header needs only a predecessor in the index, which an earlier header of the call can supply, so one call can extend several branches.
The peer checks of the `headers` message, such as its limit of 2000 headers and its test of continuity, are outside the function (D74, decision 10).
`NotifyHeaderTip` (line 3284) changes no state that the model holds.
-/
def processNewBlockHeaders (ctx : HeaderContext) (index : HeaderIndex) (headers : List BlockHeader) :
    HeaderSequenceResult :=
  if checkWellFormed ctx.network index then processSteps ctx 0 index none headers
  else (index, .error ⟨0, .adapter .notWellFormed⟩)

/--
The composition of two sequence results, design record 0008, section 7.2.
`n` is the length of the list of the first result, and `second` is the result of the next list from the index of `first`.
If `first` is an error, the composition is `first`.
Otherwise the index is the index of `second`, and an error of `second` has its position increased by `n`.
A success of `second` with `none`, from an empty list, keeps the last hash of `first`.
`process_append` shows that processing `xs ++ ys` gives the composition of the results of `xs` and `ys`.
-/
def composeSequence (n : Nat) (first second : HeaderSequenceResult) : HeaderSequenceResult :=
  match first.2 with
  | .error _ => first
  | .ok last =>
    (second.1, match second.2 with
      | .error error => .error { error with position := error.position + n }
      | .ok none => .ok last
      | .ok (some hash) => .ok (some hash))

end DogeLib.Block
