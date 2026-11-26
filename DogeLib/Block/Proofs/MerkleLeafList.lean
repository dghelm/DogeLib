module

public import DogeLib.Block.Proofs.Merkle
public import DogeLib.Transaction.Check
public import DogeLib.Transaction.Proofs.Serialization
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# A transaction list with the Merkle root of a block

A block header holds the Merkle root of the transaction IDs of the block.
The root does not hold the number of transactions or the depth of the tree.
A transaction ID and an inner node are both a double SHA-256 digest, with no mark that tells them apart.
So the root alone does not fix the list of transactions.
This module states which further tests fix it.

## The two known ambiguities

- *Duplication (CVE-2012-2459).* `[A, B, C, C]` has the root of `[A, B, C]`.
  `MerkleDuplication.root_eq_and_mutated` of `DogeLib.Block.Proofs.Merkle` states it, and the mutation flag marks the longer list.
- *A transaction of 64 bytes at an inner node (CVE-2017-12842).* An inner node is the digest of the 64 bytes of its two children.
  If those 64 bytes are also the base serialization of a transaction `t`, the ID of `t` is that inner node.
  Then the list `[t]` has the root of the two children.
  `blockMerkleRoot_inner_transaction` states it, with no assumption about the hash.

## The result

`transactions_eq_of_merkleRoot_eq` takes two lists of transactions.
Each list starts with a coinbase, the two lists have the same Merkle root, and neither sets the mutation flag.
Then one of three statements holds:

1. The two lists are equal.
2. `MerkleCollision`: two different byte strings that the two trees hash have the same double SHA-256 digest.
3. `CoinbaseAtInnerNode`: the serialization of one coinbase is the 64 bytes of two nodes of the other tree.

Statements 2 and 3 are about the two lists.
A statement that some two byte strings collide, with no relation to the lists, would hold for every hash with a fixed output length.
So each statement names its byte strings among the inputs of the two trees (`MerkleInput`).
The inputs are the serializations of the transactions, and the 64 bytes of two nodes of one level.
Both statements are false for lists of one transaction (`not_merkleCollision_singleton`, `not_encodesInnerNode_singleton`).

The third statement is not a collision.
It names one 64-byte string, the serialization of a coinbase, and two nodes `l` and `r` of the other tree with that serialization as `l ++ r`.
Then the digest `l` ends with the byte 1 and 27 zero bytes.
The digest `r` starts with 5 zero bytes and 4 bytes `0xff`.
The serialization does not exclude this case, because a coinbase of 64 bytes is well formed.
To leave the statement out, the theorem would need a further assumption about SHA-256.

`transactions_eq_or_encodesInnerNode` is the same theorem without the coinbase hypotheses.
Its third statement is `EncodesInnerNode`, with no condition on digests, and it holds for the lists of `blockMerkleRoot_inner_transaction`.

The proofs assume no property of SHA-256.

## The argument

`merkleRoot_eq_cases` compares the two trees from the root down.
Two nodes with the same digest have the same two children, or their 64-byte inputs are a collision (`merklePair_eq_or_collision`).
So two levels with the same next level are equal, or the longer one ends with an equal aligned pair (`merkleLevel_eq_cases`).
The comparison ends when one tree has no further level.
If both end together, the lists of leaves are equal.
If not, the leaves of one list are a level of inner nodes of the other.

An equal aligned pair in a padded level gives the mutation flag or a collision (`merkleMutated_of_paddedPair`).
`merkleMutated` reads complete subtrees only, and a padded level has at most one node above them, its last one.
The proof follows that one node from level to level.

Each lemma takes a predicate `S` on byte strings and a proof that `S` holds for the node pairs that it compares (`LevelPairsIn`).
Its collision is then a `Sha256dCollisionIn S`, two byte strings of `S`.
The lemmas compare only nodes of levels below a root, so the inputs stay in the two trees.

A coinbase has one input with the null outpoint, so bytes 4 to 40 of its serialization are fixed (`isCoinBase_encode_pattern`).
If the ID of the coinbase is an inner node with the children `l` and `r`, then the serialization is `l ++ r` or a collision.
In the first case the digests `l` and `r` hold the fixed bytes (`encodesInnerNode_coinbase_pattern`).

The module adds no definition to the specification.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction DogeLib.Serialization
open DogeLib.Cryptography.Hash

/-! ## Collisions among named inputs -/

/--
Two different byte strings `p` and `q` that both satisfy `S` have the same double SHA-256 digest.

`S` names the byte strings that count.
Without `S` the statement would hold for every hash with a fixed output length, because more inputs exist than digests.
So a theorem with this alternative states it for a finite set `S` that it builds from its inputs.
DogeLib does not assume that the statement is false for any `S`.
-/
def Sha256dCollisionIn (S : List UInt8 → Prop) : Prop :=
  ∃ p q : List UInt8, S p ∧ S q ∧ p ≠ q ∧
    Sha256d.hash p.toByteArray = Sha256d.hash q.toByteArray

/-- A collision among the byte strings of `S` is a collision among those of every `S'` that holds on `S`. -/
theorem Sha256dCollisionIn.mono {S S' : List UInt8 → Prop} (h : Sha256dCollisionIn S)
    (hS : ∀ p, S p → S' p) : Sha256dCollisionIn S' := by
  obtain ⟨p, q, hp, hq, hne, he⟩ := h
  exact ⟨p, q, hS p hp, hS q hq, hne, he⟩

/-- Two byte arrays with the same list of bytes are equal. -/
theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  rw [ByteArray.toList_eq_data_toList, ByteArray.toList_eq_data_toList] at h
  cases a
  cases b
  simp_all

/-- For all byte lists `x` and `y` of `S` whose double SHA-256 digests are equal: `x = y`, or the two lists are a `Sha256dCollisionIn S`. -/
theorem sha256d_eq_or_collision {S : List UInt8 → Prop} {x y : List UInt8} (hx : S x) (hy : S y)
    (h : (Sha256d.hash x.toByteArray).toList = (Sha256d.hash y.toByteArray).toList) :
    x = y ∨ Sha256dCollisionIn S := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr ⟨x, y, hx, hy, hxy, byteArray_eq_of_toList_eq h⟩

/--
Let `merklePair a b = merklePair c d`, and let the two 64-byte inputs satisfy `S`.
Then `a = c` and `b = d`, or the two inputs are a `Sha256dCollisionIn S`.
-/
theorem merklePair_eq_or_collision {S : List UInt8 → Prop} {a b c d : Hash256}
    (h : merklePair a b = merklePair c d) (h1 : S (a.val ++ b.val)) (h2 : S (c.val ++ d.val)) :
    (a = c ∧ b = d) ∨ Sha256dCollisionIn S := by
  have hv := congrArg Subtype.val h
  rw [merklePair_val, merklePair_val] at hv
  rcases sha256d_eq_or_collision h1 h2 hv with heq | hc
  · have := List.append_inj heq (by simp)
    exact Or.inl ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  · exact Or.inr hc

/-! ## Levels -/

/-- The list after `k` applications of `merkleLevel`: the padded level `k` of the tree over `xs`. -/
def merkleLevels : Nat → List Hash256 → List Hash256
  | 0, xs => xs
  | k + 1, xs => merkleLevels k (merkleLevel xs)

/-- Level `k + 1` is the next level of level `k`. -/
theorem merkleLevels_succ (k : Nat) (xs : List Hash256) :
    merkleLevels (k + 1) xs = merkleLevel (merkleLevels k xs) := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    show merkleLevels (k + 1) (merkleLevel xs) = _
    rw [ih]
    rfl

/-- If level `k` has at least two entries, so has each level below it. -/
theorem merkleLevels_two_le {k : Nat} {xs : List Hash256} (h : 2 ≤ (merkleLevels k xs).length) :
    ∀ j, j ≤ k → 2 ≤ (merkleLevels j xs).length := by
  induction k with
  | zero =>
    intro j hj
    have : j = 0 := by omega
    subst this
    exact h
  | succ k ih =>
    intro j hj
    by_cases hjk : j = k + 1
    · subst hjk
      exact h
    · refine ih ?_ j (by omega)
      have := merkleLevel_length_le (merkleLevels k xs)
      rw [← merkleLevels_succ] at this
      omega

/--
The 64 bytes `l ++ r` of two nodes `l` and `r` of one level of the tree over `hs`.
The level has at least two nodes.
Such a level is below the root, so the tree has finitely many such byte strings.
The input of each inner node of the tree is one of them.
The predicate also holds for two nodes of one level that the tree does not pair.
-/
def MerkleNodeInput (hs : List Hash256) (p : List UInt8) : Prop :=
  ∃ k l r, 2 ≤ (merkleLevels k hs).length ∧ l ∈ merkleLevels k hs ∧ r ∈ merkleLevels k hs ∧
    p = l.val ++ r.val

/-- `S` holds for the 64 bytes of each two nodes of each level of `xs` that has at least two nodes. -/
def LevelPairsIn (S : List UInt8 → Prop) (xs : List Hash256) : Prop :=
  ∀ k, 2 ≤ (merkleLevels k xs).length → ∀ l ∈ merkleLevels k xs, ∀ r ∈ merkleLevels k xs,
    S (l.val ++ r.val)

/-- `LevelPairsIn` passes from a list to its next level. -/
theorem LevelPairsIn.level {S : List UInt8 → Prop} {xs : List Hash256} (h : LevelPairsIn S xs) :
    LevelPairsIn S (merkleLevel xs) := fun k => h (k + 1)

/-- `MerkleNodeInput hs` holds for the pairs of each level of `hs`. -/
theorem levelPairsIn_merkleNodeInput (hs : List Hash256) : LevelPairsIn (MerkleNodeInput hs) hs :=
  fun k h2 l hl r hr => ⟨k, l, r, h2, hl, hr, rfl⟩

/-- A padded level of `xs` has an equal aligned pair. The pair can hold the node that padding made. -/
def MerklePaddedPair (xs : List Hash256) : Prop :=
  ∃ k, merkleEqualPair (merkleLevels k xs) = true

/--
Let the hash lists `xs` and `ys` have the same next level.
Let `S` hold for the 64 bytes of each two entries of `xs`, and of each two entries of `ys`.
Then `xs = ys`, or there is a `Sha256dCollisionIn S`, or one of the two lists has an equal aligned pair.
The last case occurs when one list has an odd length and the other has one more hash, a copy of the last one.
-/
theorem merkleLevel_eq_cases {S : List UInt8 → Prop} : ∀ (xs ys : List Hash256),
    (∀ l ∈ xs, ∀ r ∈ xs, S (l.val ++ r.val)) → (∀ l ∈ ys, ∀ r ∈ ys, S (l.val ++ r.val)) →
    merkleLevel xs = merkleLevel ys →
    xs = ys ∨ Sha256dCollisionIn S ∨ merkleEqualPair xs = true ∨ merkleEqualPair ys = true
  | [], [], _, _, _ => Or.inl rfl
  | [], [_], _, _, h => by simp [merkleLevel] at h
  | [], _ :: _ :: _, _, _, h => by simp [merkleLevel] at h
  | [_], [], _, _, h => by simp [merkleLevel] at h
  | _ :: _ :: _, [], _, _, h => by simp [merkleLevel] at h
  | [a], [b], hx, hy, h => by
    simp only [merkleLevel, List.cons.injEq, and_true] at h
    rcases merklePair_eq_or_collision h (hx a (by simp) a (by simp)) (hy b (by simp) b (by simp))
      with ⟨rfl, _⟩ | hc
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
  | [a], b :: b' :: rest, hx, hy, h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 (hx a (by simp) a (by simp))
      (hy b (by simp) b' (by simp)) with ⟨h1, h2⟩ | hc
    · exact Or.inr (Or.inr (Or.inr (by simp [merkleEqualPair, ← h1, ← h2])))
    · exact Or.inr (Or.inl hc)
  | a :: a' :: rest, [b], hx, hy, h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 (hx a (by simp) a' (by simp))
      (hy b (by simp) b (by simp)) with ⟨h1, h2⟩ | hc
    · exact Or.inr (Or.inr (Or.inl (by simp [merkleEqualPair, h1, h2])))
    · exact Or.inr (Or.inl hc)
  | a :: a' :: rest, b :: b' :: rest', hx, hy, h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 (hx a (by simp) a' (by simp))
      (hy b (by simp) b' (by simp)) with ⟨rfl, rfl⟩ | hc
    · rcases merkleLevel_eq_cases rest rest'
          (fun l hl r hr => hx l (by simp [hl]) r (by simp [hr]))
          (fun l hl r hr => hy l (by simp [hl]) r (by simp [hr])) h.2 with rfl | hc | he | he
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl (by simp [merkleEqualPair, he])))
      · exact Or.inr (Or.inr (Or.inr (by simp [merkleEqualPair, he])))
    · exact Or.inr (Or.inl hc)

/--
For every nonempty hash list, some level `k` is the one-entry list of the Merkle root.
Each level below `k` has at least two entries.
-/
theorem exists_merkleLevels_eq_root (xs : List Hash256) (h : xs ≠ []) :
    ∃ k, merkleLevels k xs = [merkleRoot xs] ∧ ∀ j, j < k → 2 ≤ (merkleLevels j xs).length := by
  induction xs using merkleRoot.induct with
  | case1 => exact absurd rfl h
  | case2 a => exact ⟨0, by simp [merkleLevels, merkleRoot], by omega⟩
  | case3 a b rest ih =>
    obtain ⟨k, hk, hlt⟩ := ih (by simp)
    refine ⟨k + 1, by rw [merkleRoot]; exact hk, ?_⟩
    intro j hj
    cases j with
    | zero => simp [merkleLevels]
    | succ j => exact hlt j (by omega)

/--
Let `xs` and `ys` be nonempty hash lists with the same Merkle root, and let `S` hold for the node pairs of both trees (`LevelPairsIn`).
Then one of these holds:

- There is a `Sha256dCollisionIn S`.
- A padded level of `xs` or of `ys` has an equal aligned pair.
- `xs` is level `k` of `ys`, or `ys` is level `k` of `xs`, and each level below `k` has at least two entries.
  Level 0 of a list is the list, so this case includes `xs = ys`.

The theorem assumes nothing about the hash function.
-/
theorem merkleRoot_eq_cases {S : List UInt8 → Prop} (xs ys : List Hash256) (hx : xs ≠ [])
    (hy : ys ≠ []) (hSx : LevelPairsIn S xs) (hSy : LevelPairsIn S ys)
    (h : merkleRoot xs = merkleRoot ys) :
    Sha256dCollisionIn S ∨ MerklePaddedPair xs ∨ MerklePaddedPair ys ∨
      (∃ k, xs = merkleLevels k ys ∧ ∀ j, j < k → 2 ≤ (merkleLevels j ys).length) ∨
      (∃ k, ys = merkleLevels k xs ∧ ∀ j, j < k → 2 ≤ (merkleLevels j xs).length) := by
  induction xs using merkleRoot.induct generalizing ys with
  | case1 => exact absurd rfl hx
  | case2 a =>
    obtain ⟨k, hk, hlt⟩ := exists_merkleLevels_eq_root ys hy
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ?_, hlt⟩)))
    rw [hk, ← h, merkleRoot]
  | case3 a b rest ih =>
    match ys, hy, hSy, h with
    | [c], _, _, h =>
      obtain ⟨k, hk, hlt⟩ := exists_merkleLevels_eq_root (a :: b :: rest) (by simp)
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨k, ?_, hlt⟩)))
      rw [hk, h, merkleRoot]
    | c :: d :: rest', _, hSy, h =>
      have h' : merkleRoot (merklePair a b :: merkleLevel rest) =
          merkleRoot (merklePair c d :: merkleLevel rest') := by
        rw [merkleRoot, merkleRoot] at h
        exact h
      have step : ∀ (A B : List Hash256) (k : Nat), 2 ≤ A.length → 2 ≤ B.length →
          LevelPairsIn S A → LevelPairsIn S B →
          merkleLevel A = merkleLevels k (merkleLevel B) →
          (∀ j, j < k → 2 ≤ (merkleLevels j (merkleLevel B)).length) →
          Sha256dCollisionIn S ∨ merkleEqualPair A = true ∨ MerklePaddedPair B ∨
            (A = merkleLevels k B ∧ ∀ j, j < k → 2 ≤ (merkleLevels j B).length) := by
        intro A B k hA hB hSA hSB hk hlt
        have hL : 2 ≤ (merkleLevels k B).length := by
          cases k with
          | zero => exact hB
          | succ k' => exact hlt k' (Nat.lt_succ_self _)
        have hk' : merkleLevel A = merkleLevel (merkleLevels k B) := by
          rw [← merkleLevels_succ]
          exact hk
        rcases merkleLevel_eq_cases A (merkleLevels k B) (hSA 0 hA) (hSB k hL) hk' with
          e | hc | he | he
        · refine Or.inr (Or.inr (Or.inr ⟨e, ?_⟩))
          intro j hj
          cases j with
          | zero => exact hB
          | succ j => exact hlt j (by omega)
        · exact Or.inl hc
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (Or.inl ⟨k, he⟩))
      rcases ih _ (by simp) (by simp [merkleLevel]) hSx.level hSy.level h' with
        hc | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk, hlt⟩ | ⟨k, hk, hlt⟩
      · exact Or.inl hc
      · exact Or.inr (Or.inl ⟨k + 1, hk⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k + 1, hk⟩))
      · rcases step (a :: b :: rest) (c :: d :: rest') k (by simp) (by simp) hSx hSy hk hlt with
          hc | he | hp | he
        · exact Or.inl hc
        · exact Or.inr (Or.inl ⟨0, he⟩)
        · exact Or.inr (Or.inr (Or.inl hp))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, he⟩)))
      · rcases step (c :: d :: rest') (a :: b :: rest) k (by simp) (by simp) hSy hSx hk hlt with
          hc | he | hp | he
        · exact Or.inl hc
        · exact Or.inr (Or.inr (Or.inl ⟨0, he⟩))
        · exact Or.inr (Or.inl hp)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, he⟩)))

/-! ## An equal pair in a padded level -/

/-- Each entry of the level of complete pairs is `merklePair a b` for an aligned pair `a`, `b` of the list, which has at least two entries. If `a = b`, the list has an equal aligned pair. -/
theorem mem_merkleCompleteLevel : ∀ (xs : List Hash256) (c : Hash256), c ∈ merkleCompleteLevel xs →
    ∃ a b, c = merklePair a b ∧ a ∈ xs ∧ b ∈ xs ∧ 2 ≤ xs.length ∧
      (a = b → merkleEqualPair xs = true)
  | [], c, h => by simp [merkleCompleteLevel] at h
  | [_], c, h => by simp [merkleCompleteLevel] at h
  | a :: b :: rest, c, h => by
    simp only [merkleCompleteLevel, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, b, rfl, by simp, by simp, by simp, fun e => by simp [merkleEqualPair, e]⟩
    · obtain ⟨x, y, hc, hx, hy, _, he⟩ := mem_merkleCompleteLevel rest c h
      exact ⟨x, y, hc, by simp [hx], by simp [hy], by simp,
        fun e => by simp [merkleEqualPair, he e]⟩

/-- The padded level is the level of complete pairs, or that level and one more node `merklePair e e` for an entry `e`. -/
theorem merkleLevel_eq_complete : ∀ xs : List Hash256,
    merkleLevel xs = merkleCompleteLevel xs ∨
      ∃ e ∈ xs, merkleLevel xs = merkleCompleteLevel xs ++ [merklePair e e]
  | [] => Or.inl rfl
  | [a] => Or.inr ⟨a, by simp, rfl⟩
  | a :: b :: rest => by
    rcases merkleLevel_eq_complete rest with h | ⟨e, he, h⟩
    · exact Or.inl (by simp [merkleLevel, merkleCompleteLevel, h])
    · exact Or.inr ⟨e, by simp [he], by simp [merkleLevel, merkleCompleteLevel, h]⟩

/--
The padded level of `xs ++ [z]` is the level of complete pairs of `xs` and one more node.
That node is `merklePair e z` for an entry `e` of `xs`, or `merklePair z z`.
-/
theorem merkleLevel_append_singleton : ∀ (xs : List Hash256) (z : Hash256),
    ∃ z', merkleLevel (xs ++ [z]) = merkleCompleteLevel xs ++ [z'] ∧
      ((∃ e ∈ xs, z' = merklePair e z) ∨ z' = merklePair z z)
  | [], z => ⟨merklePair z z, rfl, Or.inr rfl⟩
  | [a], z => ⟨merklePair a z, rfl, Or.inl ⟨a, by simp, rfl⟩⟩
  | a :: b :: rest, z => by
    obtain ⟨z', hl, hz⟩ := merkleLevel_append_singleton rest z
    refine ⟨z', by simp [merkleLevel, merkleCompleteLevel, hl], ?_⟩
    rcases hz with ⟨e, he, hz⟩ | hz
    · exact Or.inl ⟨e, by simp [he], hz⟩
    · exact Or.inr hz

/-- If `xs ++ [z]` has an equal aligned pair, then `xs` has one, or `z` is an entry of `xs`. -/
theorem merkleEqualPair_append_singleton : ∀ (xs : List Hash256) (z : Hash256),
    merkleEqualPair (xs ++ [z]) = true → merkleEqualPair xs = true ∨ z ∈ xs
  | [], z, h => by simp [merkleEqualPair] at h
  | [a], z, h => by
    simp only [List.cons_append, List.nil_append, merkleEqualPair, Bool.or_false,
      decide_eq_true_eq] at h
    exact Or.inr (by simp [h])
  | a :: b :: rest, z, h => by
    simp only [List.cons_append, merkleEqualPair, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact Or.inl (by simp [merkleEqualPair, h])
    · rcases merkleEqualPair_append_singleton rest z h with h | h
      · exact Or.inl (by simp [merkleEqualPair, h])
      · exact Or.inr (by simp [h])

/--
One level of the argument of `merkleMutated_of_levels_equalPair`.
`C` holds the complete nodes of a level, and `t` is the node above an incomplete subtree, when the level has one.
`S` holds for the 64 bytes of each two nodes of the level, when `C` has at least two nodes.
If no complete node equals `t`, apart from the cases `M` and `Sha256dCollisionIn S`, then the same holds one level up.
-/
theorem merkleLevel_tail_step {S : List UInt8 → Prop} (M : Prop) (C : List Hash256)
    (t : Option Hash256) (hM : merkleMutated C = true → M)
    (hP : 2 ≤ C.length → ∀ l ∈ C ++ t.toList, ∀ r ∈ C ++ t.toList, S (l.val ++ r.val))
    (hinv : ∀ z, t = some z → z ∈ C → M ∨ Sha256dCollisionIn S) :
    ∃ t' : Option Hash256, merkleLevel (C ++ t.toList) = merkleCompleteLevel C ++ t'.toList ∧
      ∀ z', t' = some z' → z' ∈ merkleCompleteLevel C → M ∨ Sha256dCollisionIn S := by
  have hE : merkleEqualPair C = true → M := fun h => hM ((merkleMutated_iff C).mpr (Or.inl h))
  cases t with
  | none =>
    rcases merkleLevel_eq_complete C with h | ⟨e, hmemE, h⟩
    · exact ⟨none, by simpa using h, by simp⟩
    · refine ⟨some (merklePair e e), by simpa using h, ?_⟩
      intro z' hz' hmem
      cases hz'
      obtain ⟨a, b, hab, ha, hb, h2, heq⟩ := mem_merkleCompleteLevel C _ hmem
      rcases merklePair_eq_or_collision hab
          (hP h2 e (by simp [hmemE]) e (by simp [hmemE]))
          (hP h2 a (by simp [ha]) b (by simp [hb])) with ⟨h1, h2'⟩ | hc
      · exact Or.inl (hE (heq (h1.symm.trans h2')))
      · exact Or.inr hc
  | some z =>
    obtain ⟨z', hl, hz⟩ := merkleLevel_append_singleton C z
    refine ⟨some z', by simpa using hl, ?_⟩
    intro w hw hmem
    cases hw
    obtain ⟨a, b, hab, ha, hb, h2, _⟩ := mem_merkleCompleteLevel C _ hmem
    have hSab := hP h2 a (by simp [ha]) b (by simp [hb])
    rcases hz with ⟨e, hmemE, rfl⟩ | rfl
    · rcases merklePair_eq_or_collision hab (hP h2 e (by simp [hmemE]) z (by simp)) hSab with
        ⟨_, h2'⟩ | hc
      · exact hinv z rfl (h2' ▸ hb)
      · exact Or.inr hc
    · rcases merklePair_eq_or_collision hab (hP h2 z (by simp) z (by simp)) hSab with
        ⟨h1, _⟩ | hc
      · exact hinv z rfl (h1 ▸ ha)
      · exact Or.inr hc

/--
Let `C` be a hash list and `t` an optional further hash.
Let `S` hold for the node pairs of the tree over `C` followed by `t`.
Let no entry of `C` equal `t`, apart from the cases `M` and `Sha256dCollisionIn S`.
Let `M` hold when `C` sets the mutation flag.
If level `k` of `C` followed by `t` has an equal aligned pair, then `M` holds or there is a `Sha256dCollisionIn S`.
-/
theorem merkleMutated_of_levels_equalPair {S : List UInt8 → Prop} (k : Nat) :
    ∀ (M : Prop) (C : List Hash256) (t : Option Hash256),
      (merkleMutated C = true → M) → LevelPairsIn S (C ++ t.toList) →
      (∀ z, t = some z → z ∈ C → M ∨ Sha256dCollisionIn S) →
      merkleEqualPair (merkleLevels k (C ++ t.toList)) = true → M ∨ Sha256dCollisionIn S := by
  induction k with
  | zero =>
    intro M C t hM _ hinv h
    cases t with
    | none =>
      exact Or.inl (hM ((merkleMutated_iff C).mpr (Or.inl (by simpa [merkleLevels] using h))))
    | some z =>
      rcases merkleEqualPair_append_singleton C z (by simpa [merkleLevels] using h) with h | h
      · exact Or.inl (hM ((merkleMutated_iff C).mpr (Or.inl h)))
      · exact hinv z rfl h
  | succ k ih =>
    intro M C t hM hS hinv h
    obtain ⟨t', hl, hinv'⟩ := merkleLevel_tail_step M C t hM
      (fun h2 => hS 0 (by simp only [merkleLevels, List.length_append]; omega)) hinv
    have hS' : LevelPairsIn S (merkleCompleteLevel C ++ t'.toList) := by
      rw [← hl]
      exact hS.level
    rw [merkleLevels, hl] at h
    exact ih M (merkleCompleteLevel C) t'
      (fun hm => hM (merkleMutated_of_completeLevel C hm)) hS' hinv' h

/--
Let a padded level of the hash list `xs` have an equal aligned pair.
Let `S` hold for the node pairs of the tree over `xs`.
Then `xs` sets the mutation flag, or there is a `Sha256dCollisionIn S`.
`merkleMutated` compares complete subtrees only, so the theorem covers the pair that holds a padded node.
For example, in `[A, B, C]` the padded level 1 is `[AB, CC]`.
If `AB = CC`, then `A = B = C` and the leaves `A`, `B` set the flag, or the inputs of `AB` and `CC` are a collision.
-/
theorem merkleMutated_of_paddedPair {S : List UInt8 → Prop} (xs : List Hash256)
    (hS : LevelPairsIn S xs) (h : MerklePaddedPair xs) :
    merkleMutated xs = true ∨ Sha256dCollisionIn S := by
  obtain ⟨k, hk⟩ := h
  exact merkleMutated_of_levels_equalPair k _ xs none id (by simpa using hS) (by simp)
    (by simpa using hk)

/--
Let `xs` and `ys` be nonempty hash lists with the same Merkle root, and let neither set the mutation flag.
Let `S` hold for the node pairs of both trees.
Then there is a `Sha256dCollisionIn S`, or `xs` is level `k` of `ys`, or `ys` is level `k` of `xs`.
In the last two cases each level below `k` has at least two entries.
-/
theorem merkleRoot_eq_levels_of {S : List UInt8 → Prop} (xs ys : List Hash256) (hx : xs ≠ [])
    (hy : ys ≠ []) (hSx : LevelPairsIn S xs) (hSy : LevelPairsIn S ys)
    (h : merkleRoot xs = merkleRoot ys) (hmx : merkleMutated xs = false)
    (hmy : merkleMutated ys = false) :
    Sha256dCollisionIn S ∨
      (∃ k, xs = merkleLevels k ys ∧ ∀ j, j < k → 2 ≤ (merkleLevels j ys).length) ∨
      (∃ k, ys = merkleLevels k xs ∧ ∀ j, j < k → 2 ≤ (merkleLevels j xs).length) := by
  rcases merkleRoot_eq_cases xs ys hx hy hSx hSy h with hc | hp | hp | hl | hl
  · exact Or.inl hc
  · rcases merkleMutated_of_paddedPair xs hSx hp with hm | hc
    · rw [hmx] at hm; cases hm
    · exact Or.inl hc
  · rcases merkleMutated_of_paddedPair ys hSy hp with hm | hc
    · rw [hmy] at hm; cases hm
    · exact Or.inl hc
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hl)

/--
Let `xs` and `ys` be nonempty hash lists with the same Merkle root, and let neither set the mutation flag.
Then one of these holds:

- Two different node inputs of the two trees have the same double SHA-256 digest.
  Each is `MerkleNodeInput xs` or `MerkleNodeInput ys`: the 64 bytes of two nodes of one level of one of the trees.
- `xs` is a level of `ys`, or `ys` is a level of `xs`. Level 0 of a list is the list, so this case includes `xs = ys`.

For example, `[merklePair a b]` and `[a, b]` have the same root, and the first list is level 1 of the second.
The theorem assumes nothing about the hash function.
-/
@[theorem_tag property]
theorem merkleRoot_eq_levels (xs ys : List Hash256) (hx : xs ≠ []) (hy : ys ≠ [])
    (h : merkleRoot xs = merkleRoot ys) (hmx : merkleMutated xs = false)
    (hmy : merkleMutated ys = false) :
    Sha256dCollisionIn (fun p => MerkleNodeInput xs p ∨ MerkleNodeInput ys p) ∨
      (∃ k, xs = merkleLevels k ys) ∨ (∃ k, ys = merkleLevels k xs) := by
  rcases merkleRoot_eq_levels_of (S := fun p => MerkleNodeInput xs p ∨ MerkleNodeInput ys p) xs ys hx hy
      (fun k h2 l hl r hr => Or.inl (levelPairsIn_merkleNodeInput xs k h2 l hl r hr))
      (fun k h2 l hl r hr => Or.inr (levelPairsIn_merkleNodeInput ys k h2 l hl r hr))
      h hmx hmy with hc | ⟨k, hk, _⟩ | ⟨k, hk, _⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨k, hk⟩)
  · exact Or.inr (Or.inr ⟨k, hk⟩)

/-! ## Transactions at the leaves -/

/--
A byte string that the tree over the transactions `ts` hashes:

- the base serialization of a transaction of `ts`, whose digest is a leaf, or
- a `MerkleNodeInput` of the transaction IDs: the 64 bytes of two nodes of one level below the root.

A list of `n` transactions has at most `n` of the first kind and fewer than `4 * n * n` of the second.
-/
def MerkleInput (ts : List Transaction) (p : List UInt8) : Prop :=
  (∃ t ∈ ts, p = Codec.encode t) ∨ MerkleNodeInput (ts.map Transaction.txid) p

/--
Two different byte strings, each a `MerkleInput` of `xs` or of `ys`, have the same double SHA-256 digest.

The statement is about the two trees.
It names two byte strings that the trees hash, such as the serializations of two transactions or the inputs of two inner nodes.
It is false for many lists, for example when both lists hold one transaction (`not_merkleCollision_singleton`).
DogeLib does not assume that it is false for all lists.
-/
def MerkleCollision (xs ys : List Transaction) : Prop :=
  Sha256dCollisionIn (fun p => MerkleInput xs p ∨ MerkleInput ys p)

/--
The base serialization of the transaction `t` is the 64 bytes `l ++ r`.
`l` and `r` are two nodes of one level of the tree over `ts`.
The level has at least two nodes, so it is below the root.
Then the ID of `t` is `merklePair l r`, the value of an inner node above `l` and `r` (`txid_eq_merklePair_of_encode`).
`blockMerkleRoot_inner_transaction` gives transactions with this property.
-/
def EncodesInnerNode (t : Transaction) (ts : List Transaction) : Prop :=
  ∃ k l r, 2 ≤ (merkleLevels k (ts.map Transaction.txid)).length ∧
    l ∈ merkleLevels k (ts.map Transaction.txid) ∧ r ∈ merkleLevels k (ts.map Transaction.txid) ∧
    Codec.encode t = l.val ++ r.val

/-- The first entry of a padded level is `merklePair l r` for two entries `l` and `r` of the list below. -/
theorem merkleLevel_head {xs : List Hash256} {c : Hash256} {tl : List Hash256}
    (h : merkleLevel xs = c :: tl) : ∃ l r, c = merklePair l r ∧ l ∈ xs ∧ r ∈ xs := by
  match xs, h with
  | [a], h =>
    simp only [merkleLevel, List.cons.injEq] at h
    exact ⟨a, a, h.1.symm, by simp, by simp⟩
  | a :: b :: rest, h =>
    simp only [merkleLevel, List.cons.injEq] at h
    exact ⟨a, b, h.1.symm, by simp, by simp⟩

/-- Every entry of a padded level is `merklePair a b` for two entries `a` and `b` of the list below. -/
theorem mem_merkleLevel : ∀ (xs : List Hash256) (c : Hash256), c ∈ merkleLevel xs →
    ∃ a b, c = merklePair a b ∧ a ∈ xs ∧ b ∈ xs
  | [], c, h => by simp [merkleLevel] at h
  | [a], c, h => by
    simp only [merkleLevel, List.mem_singleton] at h
    exact ⟨a, a, h, by simp, by simp⟩
  | a :: b :: rest, c, h => by
    simp only [merkleLevel, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, b, h, by simp, by simp⟩
    · obtain ⟨x, y, hc, hx, hy⟩ := mem_merkleLevel rest c h
      exact ⟨x, y, hc, by simp [hx], by simp [hy]⟩

/--
Let level `k` of the tree over `ts` have at least two nodes.
Then each node of that level is the double SHA-256 digest of a `MerkleInput` of `ts`.
-/
theorem merkleLevels_node_digest (ts : List Transaction) (k : Nat)
    (h2 : 2 ≤ (merkleLevels k (ts.map Transaction.txid)).length) :
    ∀ c ∈ merkleLevels k (ts.map Transaction.txid),
      ∃ p, MerkleInput ts p ∧ c.val = (Sha256d.hash p.toByteArray).toList := by
  intro c hc
  cases k with
  | zero =>
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hc
    exact ⟨Codec.encode t, Or.inl ⟨t, ht, rfl⟩, t.txid_val⟩
  | succ k =>
    rw [merkleLevels_succ] at hc
    obtain ⟨a, b, rfl, ha, hb⟩ := mem_merkleLevel _ c hc
    exact ⟨a.val ++ b.val,
      Or.inr ⟨k, a, b, merkleLevels_two_le h2 k (Nat.le_succ k), ha, hb, rfl⟩, merklePair_val a b⟩

/-- For all transactions `a` and `b` with the same ID, whose base serializations satisfy `S`: `a = b`, or the two serializations are a `Sha256dCollisionIn S`. -/
theorem txid_eq_or_collision {S : List UInt8 → Prop} {a b : Transaction}
    (ha : S (Codec.encode a)) (hb : S (Codec.encode b)) (h : a.txid = b.txid) :
    a = b ∨ Sha256dCollisionIn S := by
  have hv := congrArg Subtype.val h
  rw [Transaction.txid_val, Transaction.txid_val] at hv
  rcases sha256d_eq_or_collision ha hb hv with heq | hc
  · exact Or.inl (encode_injective heq)
  · exact Or.inr hc

/-- For all transaction lists with the same list of IDs, whose base serializations satisfy `S`: the lists are equal, or there is a `Sha256dCollisionIn S`. -/
theorem map_txid_eq_or_collision {S : List UInt8 → Prop} : ∀ (xs ys : List Transaction),
    (∀ x ∈ xs, S (Codec.encode x)) → (∀ y ∈ ys, S (Codec.encode y)) →
    xs.map Transaction.txid = ys.map Transaction.txid → xs = ys ∨ Sha256dCollisionIn S
  | [], [], _, _, _ => Or.inl rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, y :: ys, hx, hy, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases txid_eq_or_collision (hx x (by simp)) (hy y (by simp)) h.1 with rfl | hc
    · rcases map_txid_eq_or_collision xs ys (fun t ht => hx t (by simp [ht]))
          (fun t ht => hy t (by simp [ht])) h.2 with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr hc
    · exact Or.inr hc

/--
Let the ID of a transaction `t` be `merklePair l r`, and let `S` hold for the base serialization of `t` and for the 64 bytes `l ++ r`.
Then the serialization is `l ++ r`, or the serialization and those 64 bytes are a `Sha256dCollisionIn S`.
-/
theorem txid_eq_merklePair_cases {S : List UInt8 → Prop} {t : Transaction} {l r : Hash256}
    (ht : S (Codec.encode t)) (hlr : S (l.val ++ r.val)) (h : t.txid = merklePair l r) :
    Codec.encode t = l.val ++ r.val ∨ Sha256dCollisionIn S := by
  have hv := congrArg Subtype.val h
  rw [Transaction.txid_val, merklePair_val] at hv
  exact sha256d_eq_or_collision ht hlr hv

/--
The converse, with no assumption about the hash: a transaction whose base serialization is the 64 bytes `l ++ r` has the ID `merklePair l r`.
So the ID of such a transaction is also the inner node above `l` and `r`.
-/
theorem txid_eq_merklePair_of_encode {t : Transaction} {l r : Hash256}
    (h : Codec.encode t = l.val ++ r.val) : t.txid = merklePair l r := by
  apply Subtype.ext
  rw [Transaction.txid_val, merklePair_val, h]

/--
Bytes 4 to 40 of the base serialization of a coinbase, 37 bytes.

```text
01            the input count, one byte of CompactSize
00 (32 times) the hash of the null outpoint
ff ff ff ff   the index of the null outpoint
```
-/
def coinbasePattern : List UInt8 := 1 :: (List.replicate 32 0 ++ List.replicate 4 0xff)

/--
For every coinbase `t`, in the sense of Core's `CTransaction::IsCoinBase`, bytes 4 to 40 of the base serialization are `coinbasePattern`.
The 4 bytes before them are the version.
-/
theorem isCoinBase_encode_pattern {t : Transaction} (h : t.isCoinBase = true) :
    ((Codec.encode t).drop 4).take 37 = coinbasePattern := by
  obtain ⟨version, ⟨inputs, hin⟩, outputs, lockTime⟩ := t
  unfold Transaction.isCoinBase at h
  match inputs, hin, h with
  | [i], hin, h =>
    obtain ⟨⟨hash, n⟩, scriptSig, sequence⟩ := i
    simp only [OutPoint.isNull, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hv : (Codec.encode version).length = 4 := encodeBitVecLE_length 4 _
    have hn : Codec.encode (4294967295 : UInt32) = List.replicate 4 0xff := by decide
    have he : Codec.encode ({ version := version, inputs := ⟨[{ prevout := { hash := Hash256.zero, n := 4294967295 }, scriptSig := scriptSig, sequence := sequence }], hin⟩, outputs := outputs, lockTime := lockTime } : Transaction) =
        Codec.encode version ++ (coinbasePattern ++ (Codec.encode scriptSig ++ Codec.encode sequence ++
          (Codec.encode outputs ++ Codec.encode lockTime))) := by
      show Codec.encode version ++ ((CompactSize.encode (UInt64.ofNat 1) ++
        (((Hash256.zero.val ++ Codec.encode (4294967295 : UInt32)) ++
          (Codec.encode scriptSig ++ Codec.encode sequence)) ++ [])) ++
          (Codec.encode outputs ++ Codec.encode lockTime)) = _
      rw [hn]
      have hc : CompactSize.encode (UInt64.ofNat 1) = [1] := by decide
      rw [hc]
      simp [coinbasePattern, Hash256.zero]
    rw [he, List.drop_left' hv, List.take_left' (by simp [coinbasePattern])]

/--
A coinbase at an inner node gives two digests with fixed bytes.
Let `c` be a coinbase with `EncodesInnerNode c ts`.
Then two `MerkleInput` byte strings `p` and `q` of `ts` have digests that, one after the other, hold `coinbasePattern` in bytes 4 to 40.

```text
digest of p   4 bytes of any value, 01, then 27 zero bytes
digest of q   5 zero bytes, ff ff ff ff, then 23 bytes of any value
```

This statement is a condition on the digests of two inputs of the tree, not a collision.
It fixes 37 bytes of the 64, which are 296 bits.
-/
theorem encodesInnerNode_coinbase_pattern {c : Transaction} {ts : List Transaction}
    (hc : c.isCoinBase = true) (h : EncodesInnerNode c ts) :
    ∃ p q, MerkleInput ts p ∧ MerkleInput ts q ∧
      (((Sha256d.hash p.toByteArray).toList ++ (Sha256d.hash q.toByteArray).toList).drop 4).take 37 =
        coinbasePattern := by
  obtain ⟨k, l, r, h2, hl, hr, he⟩ := h
  obtain ⟨p, hp, hpv⟩ := merkleLevels_node_digest ts k h2 l hl
  obtain ⟨q, hq, hqv⟩ := merkleLevels_node_digest ts k h2 r hr
  refine ⟨p, q, hp, hq, ?_⟩
  rw [← hpv, ← hqv, ← he]
  exact isCoinBase_encode_pattern hc

/-! ## The result -/

/--
Let the hash list `c.txid :: rest` be level `k + 1` of the tree over the transactions `ts`, where level `k` has at least two nodes.
Let `S` hold for the base serialization of `c` and for the node pairs of that tree.
Then there is a `Sha256dCollisionIn S`, or `EncodesInnerNode c ts`.
-/
theorem txid_at_level_cases {S : List UInt8 → Prop} (c : Transaction) (rest : List Hash256)
    (k : Nat) (ts : List Transaction) (hc : S (Codec.encode c))
    (hS : LevelPairsIn S (ts.map Transaction.txid))
    (h2 : 2 ≤ (merkleLevels k (ts.map Transaction.txid)).length)
    (h : c.txid :: rest = merkleLevels (k + 1) (ts.map Transaction.txid)) :
    Sha256dCollisionIn S ∨ EncodesInnerNode c ts := by
  rw [merkleLevels_succ] at h
  obtain ⟨l, r, hlr, hl, hr⟩ := merkleLevel_head h.symm
  rcases txid_eq_merklePair_cases hc (hS k h2 l hl r hr) hlr with he | hcoll
  · exact Or.inr ⟨k, l, r, h2, hl, hr, he⟩
  · exact Or.inl hcoll

/--
Two transaction lists with the same Merkle root, with no coinbase hypothesis.
Let `cx :: xs` and `cy :: ys` have the same Merkle root, and let neither set the mutation flag.
Then one of these holds:

1. `cx :: xs = cy :: ys`.
2. `MerkleCollision (cx :: xs) (cy :: ys)`.
3. `EncodesInnerNode cx (cy :: ys)` or `EncodesInnerNode cy (cx :: xs)`.
   The serialization of the first transaction of one list is the 64 bytes of two nodes of the other tree.

Statement 3 holds for some unequal lists, with no collision: `blockMerkleRoot_inner_transaction` and `encodesInnerNode_of_encode` give them.
So the theorem cannot conclude statement 1 or 2 alone.
`transactions_eq_of_merkleRoot_eq` adds the hypothesis that both first transactions are coinbases.
-/
@[theorem_tag property]
theorem transactions_eq_or_encodesInnerNode (cx cy : Transaction) (xs ys : List Transaction)
    (hroot : (blockMerkleRoot (cx :: xs)).root = (blockMerkleRoot (cy :: ys)).root)
    (hmx : (blockMerkleRoot (cx :: xs)).mutated = false)
    (hmy : (blockMerkleRoot (cy :: ys)).mutated = false) :
    cx :: xs = cy :: ys ∨ MerkleCollision (cx :: xs) (cy :: ys) ∨
      EncodesInnerNode cx (cy :: ys) ∨ EncodesInnerNode cy (cx :: xs) := by
  simp only [blockMerkleRoot, computeMerkleRoot] at hroot hmx hmy
  have hSx : LevelPairsIn (fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p)
      ((cx :: xs).map Transaction.txid) :=
    fun k h2 l hl r hr => Or.inl (Or.inr ⟨k, l, r, h2, hl, hr, rfl⟩)
  have hSy : LevelPairsIn (fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p)
      ((cy :: ys).map Transaction.txid) :=
    fun k h2 l hl r hr => Or.inr (Or.inr ⟨k, l, r, h2, hl, hr, rfl⟩)
  have hEx : ∀ t ∈ cx :: xs,
      MerkleInput (cx :: xs) (Codec.encode t) ∨ MerkleInput (cy :: ys) (Codec.encode t) :=
    fun t ht => Or.inl (Or.inl ⟨t, ht, rfl⟩)
  have hEy : ∀ t ∈ cy :: ys,
      MerkleInput (cx :: xs) (Codec.encode t) ∨ MerkleInput (cy :: ys) (Codec.encode t) :=
    fun t ht => Or.inr (Or.inl ⟨t, ht, rfl⟩)
  rcases merkleRoot_eq_levels_of (S := fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p) _ _ (by simp) (by simp) hSx hSy hroot hmx hmy with
    hc | ⟨k, hk, hlt⟩ | ⟨k, hk, hlt⟩
  · exact Or.inr (Or.inl hc)
  · cases k with
    | zero =>
      rcases map_txid_eq_or_collision (S := fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p) _ _ hEx hEy hk with e | hc
      · exact Or.inl e
      · exact Or.inr (Or.inl hc)
    | succ k =>
      have hk' : cx.txid :: xs.map Transaction.txid = _ := hk
      rcases txid_at_level_cases (S := fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p) cx _ k _ (hEx cx (by simp)) hSy (hlt k (Nat.lt_succ_self k)) hk'
        with hc | he
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl he))
  · cases k with
    | zero =>
      rcases map_txid_eq_or_collision (S := fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p) _ _ hEy hEx hk with e | hc
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl hc)
    | succ k =>
      have hk' : cy.txid :: ys.map Transaction.txid = _ := hk
      rcases txid_at_level_cases (S := fun p => MerkleInput (cx :: xs) p ∨ MerkleInput (cy :: ys) p) cy _ k _ (hEy cy (by simp)) hSx (hlt k (Nat.lt_succ_self k)) hk'
        with hc | he
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inr he))

/--
The digests of two inputs of the tree over `ts`, one after the other, hold `coinbasePattern` in bytes 4 to 40.
`encodesInnerNode_coinbase_pattern` describes the bytes.
The statement is a condition on two digests of this tree, not a collision.
-/
def MerkleCoinbasePattern (ts : List Transaction) : Prop :=
  ∃ p q, MerkleInput ts p ∧ MerkleInput ts q ∧
    (((Sha256d.hash p.toByteArray).toList ++ (Sha256d.hash q.toByteArray).toList).drop 4).take 37 =
      coinbasePattern

/--
The first transaction `c` of `ts` is a coinbase whose base serialization is the 64 bytes of two nodes of the tree over `us`.

```text
serialization of c = l ++ r      l and r are two nodes of one level of the tree over us
l = digest of p                  4 bytes of any value, 01, then 27 zero bytes
r = digest of q                  5 zero bytes, ff ff ff ff, then 23 bytes of any value
```

The statement has three parts: `c` is a coinbase, `EncodesInnerNode c us`, and `MerkleCoinbasePattern us`.
The third part follows from the first two (`encodesInnerNode_coinbase_pattern`), and the definition keeps it to state the digests.
`p` and `q` are inputs of the tree over `us`: serializations of its transactions, or the 64 bytes of two of its nodes.

The statement is not a collision, because it names one 64-byte string and no second string with the same digest.
It fixes 37 bytes of two digests of the tree over `us`, which are 296 bits.
It is false when `us` holds one transaction (`not_encodesInnerNode_singleton`).
DogeLib does not assume that it is false for all lists.
-/
def CoinbaseAtInnerNode (ts us : List Transaction) : Prop :=
  ∃ c, ts.head? = some c ∧ c.isCoinBase = true ∧ EncodesInnerNode c us ∧ MerkleCoinbasePattern us

/--
Let `cx :: xs` and `cy :: ys` be two lists of transactions, with these hypotheses:

- `cx` and `cy` are coinbases, in the sense of Core's `CTransaction::IsCoinBase`: one input, with the null outpoint.
- The two lists have the same Merkle root (`blockMerkleRoot`, over the transaction IDs).
- Neither list sets the mutation flag.

Then one of these holds:

1. `cx :: xs = cy :: ys`, as lists of transactions.
2. `MerkleCollision (cx :: xs) (cy :: ys)`: two different byte strings that the two trees hash have the same double SHA-256 digest.
   Each is the serialization of a transaction of one list, or the 64 bytes of two nodes of one level.
3. `CoinbaseAtInnerNode` for one list and the other.
   The serialization of one coinbase is the 64 bytes of two nodes of the other tree.
   Then one digest of that tree ends with the byte 1 and 27 zero bytes.
   Another digest starts with 5 zero bytes and `ff ff ff ff`.

Statement 3 is not a collision.
It occurs when one tree has more levels than the other.
The coinbase of the lower tree is then an inner node of the higher tree.
A coinbase of 64 bytes is well formed, so the serialization does not exclude it.

Statements 2 and 3 name byte strings of the two trees, and the proof builds them from the two lists.
Each statement is false for lists of one transaction (`not_merkleCollision_singleton`, `not_encodesInnerNode_singleton`).
So the conclusion is not a statement about SHA-256 alone.

The theorem is about the Lean definitions, and it assumes no property of SHA-256.
A caller that reads the lists from bytes gets each `Transaction` from a reader, such as `Transaction.readBase`.
The equality is then an equality of the values that the reader returned.
-/
@[theorem_tag property]
theorem transactions_eq_of_merkleRoot_eq (cx cy : Transaction) (xs ys : List Transaction)
    (hcx : cx.isCoinBase = true) (hcy : cy.isCoinBase = true)
    (hroot : (blockMerkleRoot (cx :: xs)).root = (blockMerkleRoot (cy :: ys)).root)
    (hmx : (blockMerkleRoot (cx :: xs)).mutated = false)
    (hmy : (blockMerkleRoot (cy :: ys)).mutated = false) :
    cx :: xs = cy :: ys ∨ MerkleCollision (cx :: xs) (cy :: ys) ∨
      CoinbaseAtInnerNode (cx :: xs) (cy :: ys) ∨ CoinbaseAtInnerNode (cy :: ys) (cx :: xs) := by
  rcases transactions_eq_or_encodesInnerNode cx cy xs ys hroot hmx hmy with e | hc | he | he
  · exact Or.inl e
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inl
      ⟨cx, rfl, hcx, he, encodesInnerNode_coinbase_pattern hcx he⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨cy, rfl, hcy, he, encodesInnerNode_coinbase_pattern hcy he⟩))

/-! ## The transaction of 64 bytes -/

/-- If the base serialization of `t` is the ID of `a` followed by the ID of `b`, then `EncodesInnerNode t [a, b]`. -/
theorem encodesInnerNode_of_encode (t a b : Transaction)
    (h : Codec.encode t = a.txid.val ++ b.txid.val) : EncodesInnerNode t [a, b] :=
  ⟨0, a.txid, b.txid, by simp [merkleLevels], by simp [merkleLevels], by simp [merkleLevels], h⟩

/--
A transaction at an inner node, with no assumption about the hash.
Let the base serialization of `t` be the 64 bytes of the IDs of `a` and `b`, one after the other.
Then the one-entry list `[t]` has the Merkle root of `[a, b]`, and `[t]` does not set the mutation flag.
`[a, b]` sets the flag exactly when the two IDs are equal.

So two different lists have one root, and the flag marks neither when the IDs differ.
The pair is in case 3 of `transactions_eq_or_encodesInnerNode`, by `encodesInnerNode_of_encode`.
The known answer `merkleInnerTransaction` of `lake test` gives made transactions `t`, `a` and `b` with this hypothesis, where `a` is a coinbase and `t` is not.
-/
@[theorem_tag property]
theorem blockMerkleRoot_inner_transaction (t a b : Transaction)
    (h : Codec.encode t = a.txid.val ++ b.txid.val) :
    (blockMerkleRoot [t]).root = (blockMerkleRoot [a, b]).root ∧
      (blockMerkleRoot [t]).mutated = false ∧
      ((blockMerkleRoot [a, b]).mutated = false ↔ a.txid ≠ b.txid) := by
  have ht := txid_eq_merklePair_of_encode h
  have hs : ∀ x : Hash256, merkleRoot [x] = x ∧ merkleMutated [x] = false := by
    intro x
    have := computeMerkleRoot_singleton x
    simpa only [computeMerkleRoot, MerkleResult.mk.injEq] using this
  have hr : merkleRoot [a.txid, b.txid] = merklePair a.txid b.txid := by
    rw [merkleRoot]
    exact (hs _).1
  have hm : merkleMutated [a.txid, b.txid] = true ↔ a.txid = b.txid := by
    rw [merkleMutated_iff]
    simp [merkleEqualPair, merkleCompleteLevel, (hs _).2]
  refine ⟨?_, (hs _).2, ?_⟩
  · show merkleRoot [t.txid] = merkleRoot [a.txid, b.txid]
    rw [hr, (hs _).1, ht]
  · show merkleMutated [a.txid, b.txid] = false ↔ _
    rw [Ne, ← hm]
    simp

/-! ## The alternatives depend on the lists -/

/-- Every level of a one-entry list has one entry. -/
theorem merkleLevels_singleton_length (k : Nat) : ∀ a : Hash256, (merkleLevels k [a]).length = 1 := by
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih => exact fun a => ih (merklePair a a)

/-- A tree with one leaf has no node input: no level has two nodes. -/
theorem not_merkleNodeInput_singleton (a : Hash256) (p : List UInt8) : ¬ MerkleNodeInput [a] p := by
  rintro ⟨k, _, _, h2, _⟩
  rw [merkleLevels_singleton_length] at h2
  omega

/--
For every transaction `c`, `MerkleCollision [c] [c]` is false.
The two trees hash one byte string, the serialization of `c`, so no two different inputs exist.
So `MerkleCollision` is a statement about its lists, and it does not hold for all lists.
-/
theorem not_merkleCollision_singleton (c : Transaction) : ¬ MerkleCollision [c] [c] := by
  have key : ∀ p, (MerkleInput [c] p ∨ MerkleInput [c] p) → p = Codec.encode c := by
    intro p hp
    have hp' : MerkleInput [c] p := hp.elim id id
    rcases hp' with ⟨t, ht, rfl⟩ | hn
    · rw [List.mem_singleton.mp ht]
    · exact absurd hn (not_merkleNodeInput_singleton _ _)
  rintro ⟨p, q, hp, hq, hne, _⟩
  exact hne ((key p hp).trans (key q hq).symm)

/--
For all transactions `t` and `c`, `EncodesInnerNode t [c]` is false: a tree with one leaf has no level with two nodes.
So `CoinbaseAtInnerNode ts [c]` is false for every list `ts`.
-/
theorem not_encodesInnerNode_singleton (t c : Transaction) : ¬ EncodesInnerNode t [c] := by
  rintro ⟨k, _, _, h2, _⟩
  have := merkleLevels_singleton_length k c.txid
  simp only [List.map_cons, List.map_nil] at h2
  omega

end DogeLib.Block
