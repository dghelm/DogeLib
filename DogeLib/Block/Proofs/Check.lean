module

public import DogeLib.Block.Check
public import DogeLib.Block.Proofs.Merkle
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

end DogeLib.Block
