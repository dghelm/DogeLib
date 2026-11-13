module

public import DogeLib.Block.Merkle
public import DogeLib.Transaction.Proofs.Txid
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Merkle structural properties

These properties concern the Lean definitions on every finite leaf list.
They do not establish collision resistance or an all-input equivalence to Core's C++ implementation.

`MerkleDuplication.root_eq_and_mutated` covers the mutation of CVE-2012-2459 in every shape: one or more duplications of a trailing subtree keep the root and set the mutation flag.
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

/--
For every nonempty even-length prefix `pre` and leaf `last`: the leaves `pre ++ [last, last]` have the Merkle root of `pre ++ [last]`, and they set the mutation flag.
For example, `[A, B, C, C]` has the root of `[A, B, C]`, with no hash collision.
The theorem states the duplicate-leaf shape of CVE-2012-2459, which the comment at the top of Core's `src/consensus/merkle.cpp` describes (D42).
The theorem is about the Lean definitions. It does not state what a block validator does with the flag.
-/
theorem computeMerkleRoot_duplicate_last (pre : List Hash256) (last : Hash256) (ne : pre ≠ [])
    (even : pre.length % 2 = 0) :
    computeMerkleRoot (pre ++ [last, last]) = ⟨(computeMerkleRoot (pre ++ [last])).root, true⟩ := by
  match pre with
  | [] => exact absurd rfl ne
  | [a] => simp at even
  | a :: b :: rest =>
    simp only [List.length_cons] at even
    have hr : rest.length % 2 = 0 := by omega
    have hm := merkleMutated_of_equal (a :: b :: rest) [] last (by simp; omega)
    simp only [List.cons_append] at hm ⊢
    simp only [computeMerkleRoot, hm]
    rw [merkleRoot, merkleRoot, merkleLevel_duplicate_last rest last hr]

/-- Every pair hash contains exactly the double SHA-256 digest of its 64 input bytes. -/
theorem merklePair_val (a b : Hash256) :
    (merklePair a b).val = (Cryptography.Hash.Sha256d.hash (a.val ++ b.val).toByteArray).toList :=
  Transaction.digestToHash256_val _ (Cryptography.Hash.Sha256d.size_hash _)

/-! ## Duplication of a trailing subtree (CVE-2012-2459) -/

/-- A list of at least two hashes has the root of its next level. -/
theorem merkleRoot_eq_merkleLevel (xs : List Hash256) (h : 2 ≤ xs.length) :
    merkleRoot xs = merkleRoot (merkleLevel xs) := by
  match xs with
  | [] => simp at h
  | [a] => simp at h
  | a :: b :: rest => rw [merkleRoot, merkleLevel]

/-- The next level of `xs ++ ys` is the next level of each part, when `xs` has even length. -/
theorem merkleLevel_append (xs ys : List Hash256) (even : xs.length % 2 = 0) :
    merkleLevel (xs ++ ys) = merkleLevel xs ++ merkleLevel ys := by
  match xs with
  | [] => rfl
  | [a] => simp at even
  | a :: b :: rest =>
    simp only [List.length_cons] at even
    have hr : rest.length % 2 = 0 := by omega
    simp only [List.cons_append, merkleLevel, merkleLevel_append rest ys hr]

/-- The next level of a list of even length has half its entries. -/
theorem merkleLevel_length (xs : List Hash256) (even : xs.length % 2 = 0) :
    (merkleLevel xs).length = xs.length / 2 := by
  match xs with
  | [] => rfl
  | [a] => simp at even
  | a :: b :: rest =>
    simp only [List.length_cons] at even
    have hr : rest.length % 2 = 0 := by omega
    simp only [merkleLevel, List.length_cons, merkleLevel_length rest hr]
    omega

/-- The next level of a list without its first `m` entries, for even `m`, is the next level without its first `m / 2` entries. -/
theorem merkleLevel_drop (xs : List Hash256) (m : Nat) (even : m % 2 = 0) :
    merkleLevel (xs.drop m) = (merkleLevel xs).drop (m / 2) := by
  match m, xs with
  | 0, xs => simp
  | 1, _ => simp at even
  | m + 2, [] => simp [merkleLevel]
  | m + 2, [a] =>
    have : (m + 2) / 2 = m / 2 + 1 := by omega
    simp [merkleLevel, this]
  | m + 2, a :: b :: rest =>
    have hm : m % 2 = 0 := by omega
    have : (m + 2) / 2 = m / 2 + 1 := by omega
    simp only [List.drop_succ_cons, merkleLevel, this, merkleLevel_drop rest m hm]

/-- On a list of even length, the level of complete pairs is the padded level: no entry needs padding. -/
theorem merkleCompleteLevel_eq_merkleLevel (xs : List Hash256) (even : xs.length % 2 = 0) :
    merkleCompleteLevel xs = merkleLevel xs := by
  match xs with
  | [] => rfl
  | [a] => simp at even
  | a :: b :: rest =>
    simp only [List.length_cons] at even
    have hr : rest.length % 2 = 0 := by omega
    simp only [merkleCompleteLevel, merkleLevel, merkleCompleteLevel_eq_merkleLevel rest hr]

/--
One duplication of a trailing subtree.
Let `xs` have `2^k * c` hashes, with `c` odd and at least 3, and let `ys` be `xs` followed by a copy of its last `2^k` hashes.
Then `ys` has the Merkle root of `xs`, and `ys` sets the mutation flag.

At level `k` the tree of `xs` has `c` nodes, an odd number, so the root computation pairs the last node with itself.
The copy in `ys` makes that pair explicit.
`c = 1` is excluded: the one node at level `k` is the root, and the computation does not pair it.
-/
theorem merkle_duplicate_subtree (k : Nat) : ∀ (c : Nat) (xs : List Hash256),
    xs.length = 2 ^ k * c → c % 2 = 1 → 3 ≤ c →
    merkleRoot (xs ++ xs.drop (xs.length - 2 ^ k)) = merkleRoot xs ∧
      merkleMutated (xs ++ xs.drop (xs.length - 2 ^ k)) = true := by
  induction k with
  | zero =>
    intro c xs hlen hodd hc
    simp only [Nat.pow_zero, Nat.one_mul] at hlen
    have hne : xs ≠ [] := by intro h; simp [h] at hlen; omega
    obtain ⟨pre, last, rfl⟩ : ∃ pre last, xs = pre ++ [last] :=
      ⟨xs.dropLast, xs.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    have hpre : pre ≠ [] := by intro h; simp [h] at hlen; omega
    have heven : pre.length % 2 = 0 := by omega
    have hdrop : (pre ++ [last]).drop ((pre ++ [last]).length - 2 ^ 0) = [last] := by simp
    rw [hdrop, List.append_assoc]
    have h := computeMerkleRoot_duplicate_last pre last hpre heven
    simp only [computeMerkleRoot, MerkleResult.mk.injEq] at h
    exact h
  | succ k ih =>
    intro c xs hlen hodd hc
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    rw [Nat.pow_succ] at hlen ⊢
    generalize 2 ^ k = p at hlen hp ih ⊢
    have hlen' : xs.length = 2 * (p * c) := by rw [hlen]; ac_rfl
    have hpc : 3 * p ≤ p * c := by rw [Nat.mul_comm 3 p]; exact Nat.mul_le_mul_left p hc
    have hxs : xs.length % 2 = 0 := by omega
    have htail : (xs.drop (xs.length - p * 2)).length % 2 = 0 := by simp only [List.length_drop]; omega
    have hys : (xs ++ xs.drop (xs.length - p * 2)).length % 2 = 0 := by
      simp only [List.length_append]; omega
    have hzlen : (merkleLevel xs).length = p * c := by rw [merkleLevel_length xs hxs]; omega
    have hlevel : merkleLevel (xs ++ xs.drop (xs.length - p * 2)) =
        merkleLevel xs ++ (merkleLevel xs).drop ((merkleLevel xs).length - p) := by
      rw [merkleLevel_append xs _ hxs, merkleLevel_drop xs _ (by omega), hzlen]
      congr 2
      omega
    obtain ⟨hroot, hmut⟩ := ih c (merkleLevel xs) hzlen hodd hc
    constructor
    · rw [merkleRoot_eq_merkleLevel _ (by simp only [List.length_append]; omega), hlevel, hroot,
        ← merkleRoot_eq_merkleLevel xs (by omega)]
    · apply merkleMutated_of_completeLevel
      rw [merkleCompleteLevel_eq_merkleLevel _ hys, hlevel]
      exact hmut

/--
`MerkleDuplication xs ys`: `ys` comes from `xs` by one or more duplications of a trailing subtree, the mutation of CVE-2012-2459.
One step appends a copy of the last `2^k` hashes of a list of `2^k * c` hashes, for an odd `c` of at least 3.
For example, `[A, B, C]` gives `[A, B, C, C]`, and `[A, B, C, D, E, F]` gives `[A, B, C, D, E, F, E, F]`.
A step from `[A, B, C, D, E]` to six hashes and a step from six to eight give `[A, B, C, D, E, E, E, E]`.
-/
inductive MerkleDuplication : List Hash256 → List Hash256 → Prop where
  /-- One duplication of the last `2^k` hashes. -/
  | step (k c : Nat) (xs : List Hash256) (hlen : xs.length = 2 ^ k * c) (hodd : c % 2 = 1)
      (hc : 3 ≤ c) : MerkleDuplication xs (xs ++ xs.drop (xs.length - 2 ^ k))
  /-- A duplication of a duplication. -/
  | trans {xs ys zs : List Hash256} : MerkleDuplication xs ys → MerkleDuplication ys zs →
      MerkleDuplication xs zs

/--
For all hash lists `xs` and `ys` with `MerkleDuplication xs ys`: `ys` has the Merkle root of `xs`, and `ys` sets the mutation flag.
So the root alone does not tell the two lists apart, and the flag marks the longer one.
The theorem is about `merkleRoot` and `merkleMutated`. It assumes nothing about the hash function.
It does not say that every list with the root of `xs` is a duplication of `xs`.
-/
@[theorem_tag property]
theorem MerkleDuplication.root_eq_and_mutated {xs ys : List Hash256} (h : MerkleDuplication xs ys) :
    merkleRoot ys = merkleRoot xs ∧ merkleMutated ys = true := by
  induction h with
  | step k c xs hlen hodd hc => exact merkle_duplicate_subtree k c xs hlen hodd hc
  | trans _ _ ih1 ih2 => exact ⟨ih2.1.trans ih1.1, ih2.2⟩

end DogeLib.Block
