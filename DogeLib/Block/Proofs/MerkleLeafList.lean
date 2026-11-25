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
2. `Sha256dCollision`: two different byte strings have the same double SHA-256 digest.
3. `Sha256dCoinbasePattern`: two byte strings have digests that, one after the other, hold the start of a coinbase.

The third statement is not a collision.
It is a condition on two digests.
The first digest ends with the byte 1 and 27 zero bytes.
The second digest starts with 5 zero bytes and 4 bytes `0xff`.

The third statement occurs when the 64-byte serialization of a coinbase is the input of an inner node of the other tree.
The serialization does not exclude this case, because a coinbase of 64 bytes is well formed.
The case has one 64-byte string and no second one, so it gives no collision.
To leave the statement out, the theorem would need a further assumption about SHA-256.

The proofs assume no property of SHA-256.
Each of statements 2 and 3 names byte strings that the proof builds from the two lists.

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

A coinbase has one input with the null outpoint, so bytes 4 to 40 of its serialization are fixed (`isCoinBase_encode_pattern`).
If the ID of the coinbase is an inner node with the children `l` and `r`, then the serialization is `l ++ r` or a collision.
In the first case the digests `l` and `r` hold the fixed bytes.

The module adds no definition to the specification.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction DogeLib.Serialization
open DogeLib.Cryptography.Hash

/-! ## The two alternatives about double SHA-256 -/

/--
Two different byte strings `p` and `q` have the same double SHA-256 digest.
A theorem with this alternative builds `p` and `q` from its inputs.
DogeLib does not assume that the statement is false.
-/
def Sha256dCollision : Prop :=
  ∃ p q : ByteArray, p ≠ q ∧ Sha256d.hash p = Sha256d.hash q

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
Two byte strings `p` and `q` whose double SHA-256 digests, one after the other, hold `coinbasePattern` in bytes 4 to 40.

```text
digest of p   4 bytes of any value, 01, then 27 zero bytes
digest of q   5 zero bytes, ff ff ff ff, then 23 bytes of any value
```

This statement is a condition on two digests, not a collision: `p` and `q` can be any byte strings.
It fixes 37 bytes of the 64, which are 296 bits.
DogeLib does not assume that the statement is false.
-/
def Sha256dCoinbasePattern : Prop :=
  ∃ p q : ByteArray,
    (((Sha256d.hash p).toList ++ (Sha256d.hash q).toList).drop 4).take 37 = coinbasePattern

/-- Two byte arrays with the same list of bytes are equal. -/
theorem byteArray_eq_of_toList_eq {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  rw [ByteArray.toList_eq_data_toList, ByteArray.toList_eq_data_toList] at h
  cases a
  cases b
  simp_all

/-- For all byte lists `x` and `y` whose double SHA-256 digests are equal: `x = y`, or the two lists are a `Sha256dCollision`. -/
theorem sha256d_eq_or_collision {x y : List UInt8}
    (h : (Sha256d.hash x.toByteArray).toList = (Sha256d.hash y.toByteArray).toList) :
    x = y ∨ Sha256dCollision := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · refine Or.inr ⟨x.toByteArray, y.toByteArray, fun he => hxy ?_, byteArray_eq_of_toList_eq h⟩
    have := congrArg ByteArray.toList he
    simpa using this

/-- For all hashes: if `merklePair a b = merklePair c d`, then `a = c` and `b = d`, or the two 64-byte inputs are a `Sha256dCollision`. -/
theorem merklePair_eq_or_collision {a b c d : Hash256} (h : merklePair a b = merklePair c d) :
    (a = c ∧ b = d) ∨ Sha256dCollision := by
  have hv := congrArg Subtype.val h
  rw [merklePair_val, merklePair_val] at hv
  rcases sha256d_eq_or_collision hv with heq | hc
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

/-- A padded level of `xs` has an equal aligned pair. The pair can hold the node that padding made. -/
def MerklePaddedPair (xs : List Hash256) : Prop :=
  ∃ k, merkleEqualPair (merkleLevels k xs) = true

/--
Let the hash lists `xs` and `ys` have the same next level.
Then `xs = ys`, or there is a `Sha256dCollision`, or one of the two lists has an equal aligned pair.
The last case occurs when one list has an odd length and the other has one more hash, a copy of the last one.
-/
theorem merkleLevel_eq_cases : ∀ (xs ys : List Hash256), merkleLevel xs = merkleLevel ys →
    xs = ys ∨ Sha256dCollision ∨ merkleEqualPair xs = true ∨ merkleEqualPair ys = true
  | [], [], _ => Or.inl rfl
  | [], [_], h => by simp [merkleLevel] at h
  | [], _ :: _ :: _, h => by simp [merkleLevel] at h
  | [_], [], h => by simp [merkleLevel] at h
  | _ :: _ :: _, [], h => by simp [merkleLevel] at h
  | [a], [b], h => by
    simp only [merkleLevel, List.cons.injEq, and_true] at h
    rcases merklePair_eq_or_collision h with ⟨rfl, _⟩ | hc
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
  | [a], b :: b' :: rest, h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 with ⟨h1, h2⟩ | hc
    · exact Or.inr (Or.inr (Or.inr (by simp [merkleEqualPair, ← h1, ← h2])))
    · exact Or.inr (Or.inl hc)
  | a :: a' :: rest, [b], h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 with ⟨h1, h2⟩ | hc
    · exact Or.inr (Or.inr (Or.inl (by simp [merkleEqualPair, h1, h2])))
    · exact Or.inr (Or.inl hc)
  | a :: a' :: rest, b :: b' :: rest', h => by
    simp only [merkleLevel, List.cons.injEq] at h
    rcases merklePair_eq_or_collision h.1 with ⟨rfl, rfl⟩ | hc
    · rcases merkleLevel_eq_cases rest rest' h.2 with rfl | hc | he | he
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr (Or.inl (by simp [merkleEqualPair, he])))
      · exact Or.inr (Or.inr (Or.inr (by simp [merkleEqualPair, he])))
    · exact Or.inr (Or.inl hc)

/-- For every nonempty hash list, some level is the one-entry list of the Merkle root. -/
theorem exists_merkleLevels_eq_root (xs : List Hash256) (h : xs ≠ []) :
    ∃ k, merkleLevels k xs = [merkleRoot xs] := by
  induction xs using merkleRoot.induct with
  | case1 => exact absurd rfl h
  | case2 a => exact ⟨0, by simp [merkleLevels, merkleRoot]⟩
  | case3 a b rest ih =>
    obtain ⟨k, hk⟩ := ih (by simp)
    exact ⟨k + 1, by rw [merkleRoot]; exact hk⟩

/--
For all nonempty hash lists `xs` and `ys` with the same Merkle root, one of these holds:

- There is a `Sha256dCollision`.
- A padded level of `xs` or of `ys` has an equal aligned pair.
- `xs` is a level of `ys`, or `ys` is a level of `xs`. Level 0 of a list is the list, so this case includes `xs = ys`.

The theorem assumes nothing about the hash function.
-/
theorem merkleRoot_eq_cases (xs ys : List Hash256) (hx : xs ≠ []) (hy : ys ≠ [])
    (h : merkleRoot xs = merkleRoot ys) :
    Sha256dCollision ∨ MerklePaddedPair xs ∨ MerklePaddedPair ys ∨
      (∃ k, xs = merkleLevels k ys) ∨ (∃ k, ys = merkleLevels k xs) := by
  induction xs using merkleRoot.induct generalizing ys with
  | case1 => exact absurd rfl hx
  | case2 a =>
    obtain ⟨k, hk⟩ := exists_merkleLevels_eq_root ys hy
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨k, ?_⟩)))
    rw [hk, ← h, merkleRoot]
  | case3 a b rest ih =>
    match ys, hy, h with
    | [c], _, h =>
      obtain ⟨k, hk⟩ := exists_merkleLevels_eq_root (a :: b :: rest) (by simp)
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨k, ?_⟩)))
      rw [hk, h, merkleRoot]
    | c :: d :: rest', _, h =>
      have h' : merkleRoot (merklePair a b :: merkleLevel rest) =
          merkleRoot (merklePair c d :: merkleLevel rest') := by
        rw [merkleRoot, merkleRoot] at h
        exact h
      rcases ih _ (by simp) (by simp) h' with hc | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inl hc
      · exact Or.inr (Or.inl ⟨k + 1, hk⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨k + 1, hk⟩))
      · have hk' : merkleLevel (a :: b :: rest) =
            merkleLevel (merkleLevels k (c :: d :: rest')) := by
          rw [← merkleLevels_succ]
          exact hk
        rcases merkleLevel_eq_cases _ _ hk' with e | hc | he | he
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, e⟩)))
        · exact Or.inl hc
        · exact Or.inr (Or.inl ⟨0, he⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨k, he⟩))
      · have hk' : merkleLevel (c :: d :: rest') =
            merkleLevel (merkleLevels k (a :: b :: rest)) := by
          rw [← merkleLevels_succ]
          exact hk
        rcases merkleLevel_eq_cases _ _ hk' with e | hc | he | he
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k, e⟩)))
        · exact Or.inl hc
        · exact Or.inr (Or.inr (Or.inl ⟨0, he⟩))
        · exact Or.inr (Or.inl ⟨k, he⟩)

/-! ## An equal pair in a padded level -/

/-- Each entry of the level of complete pairs is `merklePair a b` for an aligned pair `a`, `b` of the list. If `a = b`, the list has an equal aligned pair. -/
theorem mem_merkleCompleteLevel : ∀ (xs : List Hash256) (c : Hash256), c ∈ merkleCompleteLevel xs →
    ∃ a b, c = merklePair a b ∧ a ∈ xs ∧ b ∈ xs ∧ (a = b → merkleEqualPair xs = true)
  | [], c, h => by simp [merkleCompleteLevel] at h
  | [_], c, h => by simp [merkleCompleteLevel] at h
  | a :: b :: rest, c, h => by
    simp only [merkleCompleteLevel, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, b, rfl, by simp, by simp, fun e => by simp [merkleEqualPair, e]⟩
    · obtain ⟨x, y, hc, hx, hy, he⟩ := mem_merkleCompleteLevel rest c h
      exact ⟨x, y, hc, by simp [hx], by simp [hy], fun e => by simp [merkleEqualPair, he e]⟩

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
If no complete node equals `t`, apart from the cases `M` and `Sha256dCollision`, then the same holds one level up.
-/
theorem merkleLevel_tail_step (M : Prop) (C : List Hash256) (t : Option Hash256)
    (hM : merkleMutated C = true → M)
    (hinv : ∀ z, t = some z → z ∈ C → M ∨ Sha256dCollision) :
    ∃ t' : Option Hash256, merkleLevel (C ++ t.toList) = merkleCompleteLevel C ++ t'.toList ∧
      ∀ z', t' = some z' → z' ∈ merkleCompleteLevel C → M ∨ Sha256dCollision := by
  have hE : merkleEqualPair C = true → M := fun h => hM ((merkleMutated_iff C).mpr (Or.inl h))
  cases t with
  | none =>
    rcases merkleLevel_eq_complete C with h | ⟨e, _, h⟩
    · exact ⟨none, by simpa using h, by simp⟩
    · refine ⟨some (merklePair e e), by simpa using h, ?_⟩
      intro z' hz' hmem
      cases hz'
      obtain ⟨a, b, hab, _, _, heq⟩ := mem_merkleCompleteLevel C _ hmem
      rcases merklePair_eq_or_collision hab with ⟨h1, h2⟩ | hc
      · exact Or.inl (hE (heq (h1.symm.trans h2)))
      · exact Or.inr hc
  | some z =>
    obtain ⟨z', hl, hz⟩ := merkleLevel_append_singleton C z
    refine ⟨some z', by simpa using hl, ?_⟩
    intro w hw hmem
    cases hw
    obtain ⟨a, b, hab, ha, hb, _⟩ := mem_merkleCompleteLevel C _ hmem
    rcases hz with ⟨e, _, rfl⟩ | rfl
    · rcases merklePair_eq_or_collision hab with ⟨_, h2⟩ | hc
      · exact hinv z rfl (h2 ▸ hb)
      · exact Or.inr hc
    · rcases merklePair_eq_or_collision hab with ⟨h1, _⟩ | hc
      · exact hinv z rfl (h1 ▸ ha)
      · exact Or.inr hc

/--
Let `C` be a hash list and `t` an optional further hash.
Let no entry of `C` equal `t`, apart from the cases `M` and `Sha256dCollision`.
Let `M` hold when `C` sets the mutation flag.
If level `k` of `C` followed by `t` has an equal aligned pair, then `M` holds or there is a `Sha256dCollision`.
-/
theorem merkleMutated_of_levels_equalPair (k : Nat) :
    ∀ (M : Prop) (C : List Hash256) (t : Option Hash256),
      (merkleMutated C = true → M) → (∀ z, t = some z → z ∈ C → M ∨ Sha256dCollision) →
      merkleEqualPair (merkleLevels k (C ++ t.toList)) = true → M ∨ Sha256dCollision := by
  induction k with
  | zero =>
    intro M C t hM hinv h
    cases t with
    | none =>
      exact Or.inl (hM ((merkleMutated_iff C).mpr (Or.inl (by simpa [merkleLevels] using h))))
    | some z =>
      rcases merkleEqualPair_append_singleton C z (by simpa [merkleLevels] using h) with h | h
      · exact Or.inl (hM ((merkleMutated_iff C).mpr (Or.inl h)))
      · exact hinv z rfl h
  | succ k ih =>
    intro M C t hM hinv h
    obtain ⟨t', hl, hinv'⟩ := merkleLevel_tail_step M C t hM hinv
    rw [merkleLevels, hl] at h
    exact ih M (merkleCompleteLevel C) t'
      (fun hm => hM (merkleMutated_of_completeLevel C hm)) hinv' h

/--
Let a padded level of the hash list `xs` have an equal aligned pair.
Then `xs` sets the mutation flag, or there is a `Sha256dCollision`.
`merkleMutated` compares complete subtrees only, so the theorem covers the pair that holds a padded node.
For example, in `[A, B, C]` the padded level 1 is `[AB, CC]`.
If `AB = CC`, then `A = B = C` and the leaves `A`, `B` set the flag, or the inputs of `AB` and `CC` are a collision.
-/
theorem merkleMutated_of_paddedPair (xs : List Hash256) (h : MerklePaddedPair xs) :
    merkleMutated xs = true ∨ Sha256dCollision := by
  obtain ⟨k, hk⟩ := h
  exact merkleMutated_of_levels_equalPair k _ xs none id (by simp) (by simpa using hk)

/--
Let `xs` and `ys` be nonempty hash lists with the same Merkle root, and let neither set the mutation flag.
Then there is a `Sha256dCollision`, or `xs` is a level of `ys`, or `ys` is a level of `xs`.
Level 0 of a list is the list, so the last two cases include `xs = ys`.
For example, `[merklePair a b]` and `[a, b]` have the same root, and the first list is level 1 of the second.
The theorem assumes nothing about the hash function.
-/
@[theorem_tag property]
theorem merkleRoot_eq_levels (xs ys : List Hash256) (hx : xs ≠ []) (hy : ys ≠ [])
    (h : merkleRoot xs = merkleRoot ys) (hmx : merkleMutated xs = false)
    (hmy : merkleMutated ys = false) :
    Sha256dCollision ∨ (∃ k, xs = merkleLevels k ys) ∨ (∃ k, ys = merkleLevels k xs) := by
  rcases merkleRoot_eq_cases xs ys hx hy h with hc | hp | hp | hl | hl
  · exact Or.inl hc
  · rcases merkleMutated_of_paddedPair xs hp with hm | hc
    · rw [hmx] at hm; cases hm
    · exact Or.inl hc
  · rcases merkleMutated_of_paddedPair ys hp with hm | hc
    · rw [hmy] at hm; cases hm
    · exact Or.inl hc
  · exact Or.inr (Or.inl hl)
  · exact Or.inr (Or.inr hl)

/-! ## Digests in the tree -/

/-- The hash holds the double SHA-256 digest of some byte string. -/
def IsSha256d (h : Hash256) : Prop := ∃ p : ByteArray, h.val = (Sha256d.hash p).toList

/-- Every transaction ID is a double SHA-256 digest. -/
theorem isSha256d_txid (t : Transaction) : IsSha256d t.txid := ⟨_, t.txid_val⟩

/-- Every pair hash is a double SHA-256 digest. -/
theorem isSha256d_merklePair (a b : Hash256) : IsSha256d (merklePair a b) := ⟨_, merklePair_val a b⟩

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

/-- Every entry of a padded level is a pair hash. -/
theorem mem_merkleLevel : ∀ (xs : List Hash256) (c : Hash256), c ∈ merkleLevel xs →
    ∃ a b, c = merklePair a b
  | [], c, h => by simp [merkleLevel] at h
  | [a], c, h => by
    simp only [merkleLevel, List.mem_singleton] at h
    exact ⟨a, a, h⟩
  | a :: b :: rest, c, h => by
    simp only [merkleLevel, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨a, b, h⟩
    · exact mem_merkleLevel rest c h

/-- If every entry of `xs` is a double SHA-256 digest, so is every entry of each level of `xs`. -/
theorem isSha256d_merkleLevels (k : Nat) : ∀ (xs : List Hash256), (∀ x ∈ xs, IsSha256d x) →
    ∀ c ∈ merkleLevels k xs, IsSha256d c := by
  induction k with
  | zero => exact fun xs h => h
  | succ k ih =>
    intro xs _
    refine ih (merkleLevel xs) ?_
    intro x hx
    obtain ⟨a, b, rfl⟩ := mem_merkleLevel xs x hx
    exact isSha256d_merklePair a b

/-! ## Transactions at the leaves -/

/-- For all transactions `a` and `b` with the same ID: `a = b`, or their base serializations are a `Sha256dCollision`. -/
theorem txid_eq_or_collision {a b : Transaction} (h : a.txid = b.txid) :
    a = b ∨ Sha256dCollision := by
  have hv := congrArg Subtype.val h
  rw [Transaction.txid_val, Transaction.txid_val] at hv
  rcases sha256d_eq_or_collision hv with heq | hc
  · exact Or.inl (encode_injective heq)
  · exact Or.inr hc

/-- For all transaction lists with the same list of IDs: the lists are equal, or there is a `Sha256dCollision`. -/
theorem map_txid_eq_or_collision : ∀ (xs ys : List Transaction),
    xs.map Transaction.txid = ys.map Transaction.txid → xs = ys ∨ Sha256dCollision
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases txid_eq_or_collision h.1 with rfl | hc
    · rcases map_txid_eq_or_collision xs ys h.2 with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr hc
    · exact Or.inr hc

/--
Let the ID of a transaction `t` be `merklePair l r`, for hashes `l` and `r`.
Then the base serialization of `t` is the 64 bytes `l ++ r`, or the serialization and those 64 bytes are a `Sha256dCollision`.
-/
theorem txid_eq_merklePair_cases {t : Transaction} {l r : Hash256} (h : t.txid = merklePair l r) :
    Codec.encode t = l.val ++ r.val ∨ Sha256dCollision := by
  have hv := congrArg Subtype.val h
  rw [Transaction.txid_val, merklePair_val] at hv
  exact sha256d_eq_or_collision hv

/--
The converse, with no assumption about the hash: a transaction whose base serialization is the 64 bytes `l ++ r` has the ID `merklePair l r`.
So the ID of such a transaction is also the inner node above `l` and `r`.
-/
theorem txid_eq_merklePair_of_encode {t : Transaction} {l r : Hash256}
    (h : Codec.encode t = l.val ++ r.val) : t.txid = merklePair l r := by
  apply Subtype.ext
  rw [Transaction.txid_val, merklePair_val, h]

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

/-! ## The result -/

/--
Let the hash list `c.txid :: rest` be level `k + 1` of a list `ys` of double SHA-256 digests, for a coinbase `c`.
Then the ID of `c` is an inner node of the tree over `ys`, and there is a `Sha256dCollision` or a `Sha256dCoinbasePattern`.
The pattern holds the digests of the two children of that node.
-/
theorem coinbase_inner_cases (c : Transaction) (rest : List Hash256) (k : Nat) (ys : List Hash256)
    (hc : c.isCoinBase = true) (hys : ∀ y ∈ ys, IsSha256d y)
    (h : c.txid :: rest = merkleLevels (k + 1) ys) : Sha256dCollision ∨ Sha256dCoinbasePattern := by
  rw [merkleLevels_succ] at h
  obtain ⟨l, r, hlr, hl, hr⟩ := merkleLevel_head h.symm
  obtain ⟨p, hp⟩ := isSha256d_merkleLevels k ys hys l hl
  obtain ⟨q, hq⟩ := isSha256d_merkleLevels k ys hys r hr
  rcases txid_eq_merklePair_cases hlr with he | hcoll
  · refine Or.inr ⟨p, q, ?_⟩
    rw [← hp, ← hq, ← he]
    exact isCoinBase_encode_pattern hc
  · exact Or.inl hcoll

/--
Let `cx :: xs` and `cy :: ys` be two lists of transactions, with these hypotheses:

- `cx` and `cy` are coinbases, in the sense of Core's `CTransaction::IsCoinBase`: one input, with the null outpoint.
- The two lists have the same Merkle root (`blockMerkleRoot`, over the transaction IDs).
- Neither list sets the mutation flag.

Then one of these holds:

1. `cx :: xs = cy :: ys`, as lists of transactions.
2. `Sha256dCollision`: two different byte strings with the same double SHA-256 digest.
   The proof takes them from two serializations, from the inputs of two inner nodes, or from one of each.
3. `Sha256dCoinbasePattern`: two byte strings whose digests are the two halves of the 64-byte serialization of `cx` or of `cy`.
   This statement is not a collision.
   It says that one digest ends with 27 zero bytes.
   The next digest starts with 5 zero bytes and `ff ff ff ff`.
   It occurs when one tree has more levels than the other.
   The coinbase of the lower tree is then an inner node of the higher tree.
   A coinbase of 64 bytes is well formed, so the serialization does not exclude the case.

The theorem needs each hypothesis.
Without the mutation flags, `[A, B, C]` and `[A, B, C, C]` are a counterexample (`MerkleDuplication.root_eq_and_mutated`).
Without a coinbase hypothesis, a transaction of 64 bytes gives a counterexample (`blockMerkleRoot_inner_transaction`).

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
    cx :: xs = cy :: ys ∨ Sha256dCollision ∨ Sha256dCoinbasePattern := by
  simp only [blockMerkleRoot, computeMerkleRoot] at hroot hmx hmy
  have hd : ∀ (ts : List Transaction), ∀ x ∈ ts.map Transaction.txid, IsSha256d x := by
    intro ts x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
    exact isSha256d_txid t
  rcases merkleRoot_eq_levels _ _ (by simp) (by simp) hroot hmx hmy with hc | ⟨k, hk⟩ | ⟨k, hk⟩
  · exact Or.inr (Or.inl hc)
  · cases k with
    | zero =>
      rcases map_txid_eq_or_collision _ _ hk with e | hc
      · exact Or.inl e
      · exact Or.inr (Or.inl hc)
    | succ k =>
      have hk' : cx.txid :: xs.map Transaction.txid = _ := hk
      exact Or.inr (coinbase_inner_cases cx _ k _ hcx (hd _) hk')
  · cases k with
    | zero =>
      rcases map_txid_eq_or_collision _ _ hk with e | hc
      · exact Or.inl e.symm
      · exact Or.inr (Or.inl hc)
    | succ k =>
      have hk' : cy.txid :: ys.map Transaction.txid = _ := hk
      exact Or.inr (coinbase_inner_cases cy _ k _ hcy (hd _) hk')

/--
A transaction at an inner node, with no assumption about the hash.
Let the base serialization of `t` be the 64 bytes of the IDs of `a` and `b`, one after the other.
Then the one-entry list `[t]` has the Merkle root of `[a, b]`, and `[t]` does not set the mutation flag.
`[a, b]` sets the flag exactly when the two IDs are equal.

So two different lists have one root, and the flag marks neither when the IDs differ.
`transactions_eq_of_merkleRoot_eq` shows that `t` and `a` are not both coinbases, apart from its statements 2 and 3.
The known answer `merkleInnerTransaction` of `lake test` gives made transactions `t`, `a` and `b` with this hypothesis.
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

end DogeLib.Block
