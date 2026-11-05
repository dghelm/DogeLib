module

public import DogeLib.Transaction.Txid

/-!
# Transaction Merkle roots

The root uses the pair hashing and odd-level duplication of Core's `ComputeMerkleRoot`.
The source is `src/consensus/merkle.cpp` at the Dogecoin pin in SOURCES.md.
Core checks equal complete subtrees during its leaf pass, but never checks its final padding sweep.
`merkleMutated` therefore recurses over complete pairs only, without synthetic padding.
Source review connects these definitions to Core, without an all-input equivalence theorem to C++.

The compatibility domain has fewer than 2^32 leaves, before Core's count and shift limits.
The Lean definitions are total on all finite lists, without a resource bound.
No collision resistance or transaction validity assumption enters these computations.

The adaptation replaces Core's stack with level recursion and separates the root from mutation detection.
The source is MIT-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/consensus/merkle.cpp`:

Copyright (c) 2015-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block

/-- Double SHA-256 of two internal-order 32-byte hashes, left then right (Core's `CHash256`). -/
def merklePair (left right : Hash256) : Hash256 :=
  Transaction.digestToHash256 (Cryptography.Hash.Sha256d.hash (left.val ++ right.val).toByteArray)

/-- One Merkle level, with the last hash duplicated when the level has odd length. -/
def merkleLevel : List Hash256 → List Hash256
  | [] => []
  | [a] => [merklePair a a]
  | a :: b :: rest => merklePair a b :: merkleLevel rest

/-- One level of complete subtree pairs, without padding an unpaired final subtree. -/
def merkleCompleteLevel : List Hash256 → List Hash256
  | a :: b :: rest => merklePair a b :: merkleCompleteLevel rest
  | _ => []

/-- Whether this level has equal hashes in an aligned pair, without counting padding. -/
def merkleEqualPair : List Hash256 → Bool
  | a :: b :: rest => decide (a = b) || merkleEqualPair rest
  | _ => false

/-- The padded level never has more entries than its input. -/
theorem merkleLevel_length_le (xs : List Hash256) : (merkleLevel xs).length ≤ xs.length := by
  match xs with
  | [] => simp [merkleLevel]
  | [a] => simp [merkleLevel]
  | a :: b :: rest =>
    have := merkleLevel_length_le rest
    simp only [merkleLevel, List.length_cons]
    omega

/-- The complete level never has more entries than its input. -/
theorem merkleCompleteLevel_length_le (xs : List Hash256) :
    (merkleCompleteLevel xs).length ≤ xs.length := by
  match xs with
  | [] => simp [merkleCompleteLevel]
  | [a] => simp [merkleCompleteLevel]
  | a :: b :: rest =>
    have := merkleCompleteLevel_length_le rest
    simp only [merkleCompleteLevel, List.length_cons]
    omega

/-- The Merkle root, with zero for no leaves and the leaf itself for one leaf. -/
def merkleRoot (xs : List Hash256) : Hash256 :=
  match xs with
  | [] => Hash256.zero
  | [a] => a
  | a :: b :: rest => merkleRoot (merklePair a b :: merkleLevel rest)
termination_by xs.length
decreasing_by
  have := merkleLevel_length_le rest
  simp only [List.length_cons]
  omega

/-- Equal aligned complete subtrees at any level set the mutation flag.
Synthetic nodes from odd-level padding do not enter this computation. -/
def merkleMutated (xs : List Hash256) : Bool :=
  match xs with
  | [] => false
  | [_] => false
  | a :: b :: rest =>
    merkleEqualPair (a :: b :: rest) ||
      merkleMutated (merklePair a b :: merkleCompleteLevel rest)
termination_by xs.length
decreasing_by
  have := merkleCompleteLevel_length_le rest
  simp only [List.length_cons]
  omega

/-- A root and mutation flag, corresponding to Core's output value and `mutated` argument. -/
structure MerkleResult where
  /-- The Merkle root in internal byte order. -/
  root : Hash256
  /-- Equal aligned complete subtrees, without padding comparisons. -/
  mutated : Bool
  deriving DecidableEq

/-- Compute the Merkle root and the complete-subtree mutation flag. -/
def computeMerkleRoot (leaves : List Hash256) : MerkleResult :=
  ⟨merkleRoot leaves, merkleMutated leaves⟩

/-- Core's `BlockMerkleRoot`: use base transaction IDs, without witness commitments or block validation. -/
def blockMerkleRoot (transactions : List Transaction.Transaction) : MerkleResult :=
  computeMerkleRoot (transactions.map Transaction.Transaction.txid)

end DogeLib.Block
