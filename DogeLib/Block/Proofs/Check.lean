module

public import DogeLib.Block.Check
public import DogeLib.Block.Proofs.Merkle
public import DogeLib.Block.Proofs.MerkleLeafList
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of `checkBlock`

`checkBlock_rejects_merkleDuplication`: with the Merkle check, `checkBlock` rejects every block that comes from an accepted block by the duplication of CVE-2012-2459.

The two blocks have the same header, and so the same `hashMerkleRoot`.
`MerkleDuplication.root_eq_and_mutated` shows that the two transaction lists have the same Merkle root.
So a check of the root alone would accept both blocks.
The theorem shows that the mutation flag separates them, with the reject reason `bad-txns-duplicate`.

The theorem is about the Lean definitions.
It assumes nothing about SHA-256.
It does not cover a block whose list has the root of another list for a different cause, such as a hash collision.

`checkBlock_transactions_eq_of_merkleRoot_eq` covers every other list.
Let `checkBlock` accept a block with the Merkle check.
Let a list start with a coinbase, have the root of the header and not set the mutation flag.
Then the list is the transaction list of the block.

The theorem has two other cases, which `DogeLib.Block.Proofs.MerkleLeafList` defines.
One is a collision between two inputs of the two trees.
The other is a coinbase whose serialization is the 64 bytes of two nodes of the other tree.
`checkBlock_transactions_unique` states the same for two accepted blocks with one `hashMerkleRoot`.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction

/--
Let `checkBlock` accept the block `b` with the Merkle check, for any network and any `fCheckPOW`.
Let `b'` have the header of `b`, and let its transaction IDs be a `MerkleDuplication` of the transaction IDs of `b`.
Then `checkBlock` rejects `b'` with `duplicateTransactions`, whose reject reason is `bad-txns-duplicate`.

For example, `b` has the transactions `[cb, t1, t2]`, and `b'` has `[cb, t1, t2, t2]`.
Both lists have the Merkle root in the shared header, so `b'` passes the root comparison, and the mutation flag rejects it.
The hypothesis `MerkleDuplication` covers each duplication of a trailing subtree and each sequence of them.
-/
@[theorem_tag property]
theorem checkBlock_rejects_merkleDuplication (network : Work.WorkNetwork) (fCheckPOW : Bool)
    (b b' : Block) (hheader : b'.header = b.header)
    (hdup : MerkleDuplication (b.transactions.map Transaction.txid)
      (b'.transactions.map Transaction.txid))
    (hok : checkBlock network fCheckPOW true b = .ok ()) :
    checkBlock network fCheckPOW true b' = .error .duplicateTransactions := by
  obtain ⟨hroot, hmut⟩ := hdup.root_eq_and_mutated
  have hhead : (if fCheckPOW then checkBlockHeader network b.header else .ok ()) = .ok () := by
    unfold checkBlock at hok
    split at hok
    · cases hok
    · assumption
  have hmr : b.header.pure.hashMerkleRoot = merkleRoot (b.transactions.map Transaction.txid) := by
    unfold checkBlock at hok
    simp only [hhead, Bool.true_and, blockMerkleRoot, computeMerkleRoot] at hok
    by_cases hne : b.header.pure.hashMerkleRoot = merkleRoot (b.transactions.map Transaction.txid)
    · exact hne
    · simp [hne] at hok
  unfold checkBlock
  simp only [hheader, hhead, Bool.true_and, blockMerkleRoot, computeMerkleRoot, hroot, hmut, hmr,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

/--
Let `checkBlock` accept the block `b` with the Merkle check, for any network and any `fCheckPOW`.
Then the transaction list of `b` starts with a coinbase and does not set the mutation flag.
The Merkle root of the list is `hashMerkleRoot` of the header.
Core's `CheckBlock` makes these three tests at D106, lines 2951 to 2962, 2976 and 2977.
-/
theorem checkBlock_ok_merkle (network : Work.WorkNetwork) (fCheckPOW : Bool) (b : Block)
    (hok : checkBlock network fCheckPOW true b = .ok ()) :
    ∃ c rest, b.transactions = c :: rest ∧ c.isCoinBase = true ∧
      (blockMerkleRoot b.transactions).root = b.header.pure.hashMerkleRoot ∧
      (blockMerkleRoot b.transactions).mutated = false := by
  unfold checkBlock at hok
  split at hok
  · cases hok
  · simp only [Bool.true_and] at hok
    split at hok
    · cases hok
    · rename_i hroot
      split at hok
      · cases hok
      · rename_i hmut
        split at hok
        · cases hok
        · split at hok
          · cases hok
          · rename_i first others heq
            split at hok
            · cases hok
            · rename_i hcb
              refine ⟨first, others, heq, by simpa using hcb, ?_, by simpa using hmut⟩
              simpa using (Eq.symm (by simpa using hroot))

/--
A supplied transaction list for an accepted block.
Let `checkBlock` accept the block `b` with the Merkle check, for any network and any `fCheckPOW`.
Let `cy :: ys` be a list of transactions with these properties:

- `cy` is a coinbase (`Transaction.isCoinBase`).
- The Merkle root of the list is `hashMerkleRoot` of the header of `b`.
- The list does not set the mutation flag.

Then one of these holds:

1. `cy :: ys` is the transaction list of `b`.
2. `MerkleCollision (cy :: ys) b.transactions`: two different inputs of the two trees have the same double SHA-256 digest.
3. `CoinbaseAtInnerNode` for one list and the other.
   The serialization of one coinbase is the 64 bytes of two nodes of the other tree.

A verifier that holds only the header of `b` can make the three tests on a list from any source.
The theorem then says what a list that passes can be.
Statements 2 and 3 name inputs of the two trees, as `transactions_eq_of_merkleRoot_eq` explains.
Without the coinbase test, `blockMerkleRoot_inner_transaction` gives another list with the same root.
The theorem is about the Lean definitions, and it assumes no property of SHA-256.
-/
@[theorem_tag property]
theorem checkBlock_transactions_eq_of_merkleRoot_eq (network : Work.WorkNetwork) (fCheckPOW : Bool)
    (b : Block) (cy : Transaction) (ys : List Transaction)
    (hok : checkBlock network fCheckPOW true b = .ok ())
    (hcy : cy.isCoinBase = true)
    (hroot : (blockMerkleRoot (cy :: ys)).root = b.header.pure.hashMerkleRoot)
    (hmy : (blockMerkleRoot (cy :: ys)).mutated = false) :
    cy :: ys = b.transactions ∨ MerkleCollision (cy :: ys) b.transactions ∨
      CoinbaseAtInnerNode (cy :: ys) b.transactions ∨
      CoinbaseAtInnerNode b.transactions (cy :: ys) := by
  obtain ⟨c, rest, heq, hc, hr, hm⟩ := checkBlock_ok_merkle network fCheckPOW b hok
  rw [heq] at hr hm ⊢
  exact transactions_eq_of_merkleRoot_eq cy c ys rest hcy hc (hroot.trans hr.symm) hmy hm

/--
Let `checkBlock` accept the blocks `b` and `b'` with the Merkle check, each for any network and any `fCheckPOW`.
Let their headers have the same `hashMerkleRoot`.
Then the two blocks have the same transaction list, or `MerkleCollision` holds for the two lists, or `CoinbaseAtInnerNode` holds for one list and the other.
-/
@[theorem_tag property]
theorem checkBlock_transactions_unique (network network' : Work.WorkNetwork)
    (fCheckPOW fCheckPOW' : Bool) (b b' : Block)
    (hroot : b'.header.pure.hashMerkleRoot = b.header.pure.hashMerkleRoot)
    (hok : checkBlock network fCheckPOW true b = .ok ())
    (hok' : checkBlock network' fCheckPOW' true b' = .ok ()) :
    b'.transactions = b.transactions ∨ MerkleCollision b'.transactions b.transactions ∨
      CoinbaseAtInnerNode b'.transactions b.transactions ∨
      CoinbaseAtInnerNode b.transactions b'.transactions := by
  obtain ⟨c, rest, heq, hc, hr, hm⟩ := checkBlock_ok_merkle network' fCheckPOW' b' hok'
  rw [heq] at hr hm ⊢
  exact checkBlock_transactions_eq_of_merkleRoot_eq network fCheckPOW b c rest hok hc
    (hr.trans hroot) hm

end DogeLib.Block
