module

public import DogeLib.Block.AuxPow
public import DogeLib.Block.Merkle

/-!
# The AuxPoW check

Core's `CAuxPow::check` and its two helpers, `CheckMerkleBranch` and `getExpectedIndex`.
The source is `src/auxpow.cpp` at the Core pin (SOURCES.md, D55, which design record 0004 cites as C5 and C6):

- `CAuxPow::check`, lines 80 to 161.
- `CAuxPow::getExpectedIndex`, lines 163 to 187.
- `CAuxPow::CheckMerkleBranch`, lines 189 to 206.

`check` tests that an AuxPoW payload links a merge-mined block hash to the parent block.
It does not test the parent's proof of work, and it reads only `fStrictChainId` of the parameter record.
The theorems are in `DogeLib.Block.Proofs.AuxPowCheck`.

## Signed integers

Core's `nIndex`, `nChainIndex` and chain IDs are `int`.
`GetChainId` and `CheckMerkleBranch` shift such a value right, which C++11 leaves implementation-defined for a negative value.
Here both shifts are the arithmetic shift of `Int32`, as GCC and Clang implement it.
That choice affects only a negative chain ID and the chain root of a negative `nChainIndex`.
`check` rejects every negative `nChainIndex` at its last test (`AuxPow.check_ok_chainIndex_lt`).

## Source

The adaptation follows Core's statements in order, with a named error for each `return error(...)`.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/auxpow.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2014 The Bitcoin developers
Copyright (c) 2011 Vince Durham
Copyright (c) 2014-2016 Daniel Kraft
Distributed under the MIT/X11 software license, see the accompanying
file license.txt or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/-- Core's `GetChainId` (D10, lines 110 to 113): the signed version shifted right by 16 bits, with the arithmetic shift. -/
def PureBlockHeader.chainId (h : PureBlockHeader) : Int32 := h.signedVersion >>> 16

/--
Core's `CAuxPow::CheckMerkleBranch` (D55, lines 189 to 206).

An index of −1 gives the zero hash.
Otherwise each branch hash is combined with the running hash by `merklePair`, Core's `Hash` of two 32-byte ranges.
If the low bit of the index is set, the branch hash is on the left.
Otherwise the running hash is on the left.
The index then shifts right by one bit, with the arithmetic shift of a signed `int`.
-/
def checkMerkleBranch (hash : Hash256) (branch : List Hash256) (index : Int32) : Hash256 :=
  if index = -1 then Hash256.zero else go hash branch index
where
  /-- The fold of `CheckMerkleBranch` after the test for −1. -/
  go (hash : Hash256) : List Hash256 → Int32 → Hash256
    | [], _ => hash
    | b :: bs, i => go (if i &&& 1 != 0 then merklePair b hash else merklePair hash b) bs (i >>> 1)

/--
Core's `CAuxPow::getExpectedIndex` (D55, lines 163 to 187): the slot of a chain in the chain Merkle tree.

The computation is unsigned 32-bit arithmetic, modulo 2^32.
The chain ID is converted modulo 2^32, so a negative chain ID wraps.
The result is the remainder modulo `2 ^ h`.
Core returns it as an `int`.
For `h` at most 30 it is below 2^30 (`getExpectedIndex_lt`), so the value is the same.

`check` calls it only with `h` at most 30.
For `h` of 32 or more, the shift here is taken modulo 32, while Core's shift would be undefined.
-/
def getExpectedIndex (nonce : UInt32) (chainId : Int32) (h : Nat) : UInt32 :=
  let rand := nonce * 1103515245 + 12345
  let rand := rand + chainId.toUInt32
  let rand := rand * 1103515245 + 12345
  rand % ((1 : UInt32) <<< h.toUInt32)

/-- The first offset at which `needle` occurs in `hay`, as Core's `std::search` finds it, or `none` if it does not occur. -/
def findSubseq? (needle hay : List UInt8) : Option Nat :=
  go hay 0
where
  /-- The search from offset `i`, where `rest` is `hay` without its first `i` bytes. -/
  go : List UInt8 → Nat → Option Nat
    | rest, i =>
      if needle.isPrefixOf rest then some i
      else match rest with
        | [] => none
        | _ :: rest' => go rest' (i + 1)

/-- The merged-mining marker `pchMergedMiningHeader`, `fa be 6d 6d` (D54, line 24). -/
def mergedMiningMarker : List UInt8 := [0xfa, 0xbe, 0x6d, 0x6d]

/-- The reason that `AuxPow.check` rejects a payload: one constructor for each `return error(...)` of D55, in source order. -/
inductive AuxPowCheckError where
  /-- `nIndex` is not zero: "AuxPow is not a generate" (line 85). -/
  | notCoinbase
  /-- With `fStrictChainId`, the parent has the chain ID of the merge-mined block (line 88). -/
  | parentHasChainId
  /-- The chain Merkle branch has more than 30 hashes (line 91). -/
  | chainBranchTooLong
  /-- The coinbase branch does not lead to the parent's `hashMerkleRoot` (line 102). -/
  | merkleRootIncorrect
  /-- The coinbase transaction has no inputs (line 106). -/
  | noInputs
  /-- The chain root, in display order, does not occur in the first input's script (line 120). -/
  | missingChainRoot
  /-- The marker occurs again after its first occurrence (line 127). -/
  | multipleMarkers
  /-- The first chain root does not start right after the first marker (line 129). -/
  | markerNotBeforeRoot
  /-- Without a marker, the first chain root starts after byte offset 20 (line 137). -/
  | rootTooLate
  /-- Fewer than eight bytes follow the first chain root (line 145). -/
  | missingSizeAndNonce
  /-- The size word is not `2 ^ h` for a chain branch of `h` hashes (line 152). -/
  | sizeMismatch
  /-- `nChainIndex` is not the expected index of the nonce and the chain ID (line 158). -/
  | wrongIndex
  deriving DecidableEq, Repr

/--
The search of the coinbase script in `CAuxPow::check` (D55, lines 108 to 156).
`root` is the chain root in display order.

It finds the first occurrences of the marker and of `root`, and `root` must occur.
If the marker occurs, no second marker may start after the first byte of the first marker.
The first `root` must then start right after the first marker.
If the marker does not occur, the first `root` must start at an offset of at most 20.

Eight bytes must follow the first `root`.
The result is the two little-endian words that they encode: the size and the nonce.
The caller compares them.
-/
def searchChainRoot (script root : List UInt8) : Except AuxPowCheckError (UInt32 × UInt32) :=
  match findSubseq? root script with
  | none => .error .missingChainRoot
  | some pc =>
    let headOk : Except AuxPowCheckError Unit :=
      match findSubseq? mergedMiningMarker script with
      | some head =>
        if (findSubseq? mergedMiningMarker (script.drop (head + 1))).isSome then .error .multipleMarkers
        else if head + mergedMiningMarker.length ≠ pc then .error .markerNotBeforeRoot
        else .ok ()
      | none => if pc > 20 then .error .rootTooLate else .ok ()
    match headOk with
    | .error e => .error e
    | .ok () =>
      match Codec.decode (α := UInt32 × UInt32) (script.drop (pc + root.length)) with
      | none => .error .missingSizeAndNonce
      | some (words, _) => .ok words

/--
Core's `CAuxPow::check` (D55, lines 80 to 161), with the first failing test as its error.

`hashAuxBlock` is the hash of the merge-mined block and `chainId` is its chain ID.
`strictChainId` is `fStrictChainId` of the parameter record, the only field that `check` reads.
The tests run in Core's order:

1. `nIndex` is zero.
2. With `strictChainId`, the parent's chain ID differs from `chainId`.
3. The chain branch has at most 30 hashes.
4. The coinbase branch at index zero leads from the transaction ID to the parent's `hashMerkleRoot`.
5. The transaction has an input.
6. `searchChainRoot` accepts the first input's script, with the chain root of `hashAuxBlock` reversed to display order.
7. The size word is `2 ^ h`, where `h` is the chain branch length.
8. `nChainIndex` equals `getExpectedIndex` of the nonce word, `chainId` and `h`.

Core computes the chain root before test 4, but that computation cannot fail.
The transaction ID excludes witness data, as `CTransaction::GetHash` does.

Test 4 of Core reads the cached `GetHash` of the coinbase transaction (D55, line 100).
A default-constructed `CAuxPow` holds `CTransaction()`, whose cache is zero, and `Transaction.txid` gives the computed digest instead.
So `check` and Core can report different errors for that object, which is outside the domain of `check`.
Core computes the cache when it decodes a payload, so only an object that a caller builds in memory has the zero cache.
-/
def AuxPow.check (a : AuxPow) (hashAuxBlock : Hash256) (chainId : Int32) (strictChainId : Bool) :
    Except AuxPowCheckError Unit :=
  if a.index ≠ 0 then .error .notCoinbase
  else if strictChainId && a.parentBlock.chainId == chainId then .error .parentHasChainId
  else if a.chainMerkleBranch.val.length > 30 then .error .chainBranchTooLong
  else
    let rootHash := checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex
    if checkMerkleBranch a.tx.tx.txid a.merkleBranch.val a.signedIndex ≠ a.parentBlock.hashMerkleRoot then
      .error .merkleRootIncorrect
    else
      match a.tx.tx.inputs.val with
      | [] => .error .noInputs
      | input :: _ =>
        match searchChainRoot input.scriptSig.bytes.val rootHash.displayBytes with
        | .error e => .error e
        | .ok (size, nonce) =>
          let h := a.chainMerkleBranch.val.length
          if size ≠ (1 : UInt32) <<< h.toUInt32 then .error .sizeMismatch
          else if a.chainIndex ≠ getExpectedIndex nonce chainId h then .error .wrongIndex
          else .ok ()

end DogeLib.Block
