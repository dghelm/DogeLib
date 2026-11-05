module

public import DogeLib.Block.Merkle
public import DogeLib.Transaction.Proofs.Txid

/-!
# Merkle structural properties

These properties concern the Lean definitions on every finite leaf list.
They do not establish collision resistance or an all-input equivalence to Core's C++ implementation.
-/

@[expose] public section
namespace DogeLib.Block

/-- No leaves give the zero root and no mutation. -/
theorem computeMerkleRoot_nil : computeMerkleRoot [] = ⟨Hash256.zero, false⟩ := by
  simp [computeMerkleRoot, merkleRoot, merkleMutated]

/-- For every leaf, a singleton gives that leaf as root and no mutation. -/
theorem computeMerkleRoot_singleton (a : Hash256) : computeMerkleRoot [a] = ⟨a, false⟩ := by
  simp [computeMerkleRoot, merkleRoot, merkleMutated]

/-- For every odd level, explicit duplication of its final leaf leaves the next level unchanged. -/
theorem merkleLevel_duplicate_last (pre : List Hash256) (last : Hash256)
    (even : pre.length % 2 = 0) :
    merkleLevel (pre ++ [last]) = merkleLevel (pre ++ [last, last]) := by
  match pre with
  | [] => rfl
  | [a] => simp at even
  | a :: b :: rest =>
    simp only [List.length_cons] at even
    have hr : rest.length % 2 = 0 := by omega
    simpa only [List.cons_append, merkleLevel] using
      congrArg (List.cons (merklePair a b)) (merkleLevel_duplicate_last rest last hr)

/-- An equal aligned leaf pair sets this level's flag, after any even-length prefix. -/
theorem merkleEqualPair_of_equal (pre rest : List Hash256) (a : Hash256)
    (even : pre.length % 2 = 0) : merkleEqualPair (pre ++ a :: a :: rest) = true := by
  match pre with
  | [] => simp [merkleEqualPair]
  | [b] => simp at even
  | b :: c :: tail =>
    simp only [List.length_cons] at even
    have ht : tail.length % 2 = 0 := by omega
    simp [merkleEqualPair, merkleEqualPair_of_equal tail rest a ht]

/-- Any equal aligned leaf pair sets the complete-subtree mutation flag. -/
theorem merkleMutated_of_equal (pre rest : List Hash256) (a : Hash256)
    (even : pre.length % 2 = 0) : merkleMutated (pre ++ a :: a :: rest) = true := by
  have hp := merkleEqualPair_of_equal pre rest a even
  cases hs : pre ++ a :: a :: rest with
  | nil => simp [hs, merkleEqualPair] at hp
  | cons x xs =>
    cases xs with
    | nil => simp [hs, merkleEqualPair] at hp
    | cons y tail => simp [merkleMutated, hs ▸ hp]

/-- For every level, mutation means an equal aligned pair here or mutation among complete parent subtrees. -/
theorem merkleMutated_iff (xs : List Hash256) :
    merkleMutated xs = true ↔ merkleEqualPair xs = true ∨
      merkleMutated (merkleCompleteLevel xs) = true := by
  match xs with
  | [] => simp [merkleMutated, merkleEqualPair, merkleCompleteLevel]
  | [a] => simp [merkleMutated, merkleEqualPair, merkleCompleteLevel]
  | a :: b :: rest => simp [merkleMutated, merkleCompleteLevel]

/-- Equal complete subtrees at the parent level imply mutation at the current level. -/
theorem merkleMutated_of_completeLevel (xs : List Hash256)
    (h : merkleMutated (merkleCompleteLevel xs) = true) : merkleMutated xs = true :=
  (merkleMutated_iff xs).mpr (Or.inr h)

/-- Every pair hash contains exactly the double SHA-256 digest of its 64 input bytes. -/
theorem merklePair_val (a b : Hash256) :
    (merklePair a b).val = (Cryptography.Hash.Sha256d.hash (a.val ++ b.val).toByteArray).toList :=
  Transaction.digestToHash256_val _ (Cryptography.Hash.Sha256d.size_hash _)

end DogeLib.Block
