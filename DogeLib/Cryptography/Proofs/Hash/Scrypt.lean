module

public import DogeLib.Cryptography.Proofs.Hash.ScryptSpec

/-!
# Properties of the scrypt model

Adapted from pyca/verified-garbage `lean/VerifiedGarbage/Proof/Scrypt/BlockMix.lean`
and the length lemmas of `Proof/Scrypt/RoMix.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes imports, namespaces and documentation, and spells `Byte` as `BitVec 8`.
The sequential-fill definitions and proofs follow the sketch in `docs/assessments/0004-crypto-reuse.md`.

`blockMix` in the order an implementation computes it: `Y[i]` from the
previous one (`yAt`), and the output as the blocks `Y[0], Y[2], …` followed by
`Y[1], Y[3], …`.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Scrypt

open Spec
open Pbkdf2.Spec (xorBytes)

variable (b : List (BitVec 8)) (r : Nat)

/-- `Y[i]`. -/
def yAt : Nat → List (BitVec 8)
  | 0 => salsa (xorBytes (blk b (2 * r - 1)) (blk b 0))
  | i + 1 => salsa (xorBytes (yAt i) (blk b (i + 1)))

/-- `X` before step `i` of scryptBlockMix's step 2. -/
def xBefore : Nat → List (BitVec 8)
  | 0 => blk b (2 * r - 1)
  | i + 1 => yAt b r i

/-- For every block index, `Y[i]` is Salsa20/8 of the previous state XOR the input block. -/
theorem yAt_eq (i : Nat) : yAt b r i = salsa (xorBytes (xBefore b r i) (blk b i)) := by
  cases i <;> rfl

/-- Before step `i + 1`, the state is `Y[i]`, for every index. -/
theorem xBefore_succ (i : Nat) : xBefore b r (i + 1) = yAt b r i := rfl

/-- For any start and count, the loop from its indexed state returns the corresponding `Y` blocks. -/
theorem blockMixYs_range' (n : Nat) : ∀ s,
    blockMixYs b (xBefore b r s) (List.range' s n) = (List.range' s n).map (yAt b r) := by
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, blockMixYs]
    rw [← yAt_eq, ← xBefore_succ, ih (s + 1)]

/-- For every count, the loop from the final input block returns the indexed `Y` blocks. -/
theorem blockMixYs_range (n : Nat) :
    blockMixYs b (blk b (2 * r - 1)) (List.range n) = (List.range n).map (yAt b r) := by
  rw [List.range_eq_range']
  exact blockMixYs_range' b r n 0

/-- Pointwise equal list functions on the members of a list give equal concatenations. -/
theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- For every byte list and natural block parameter, BlockMix concatenates even-indexed `Y[i]` blocks followed by odd-indexed blocks. -/
theorem blockMix_eq : blockMix r b =
    ((List.range r).flatMap fun i => yAt b r (2 * i)) ++
      ((List.range r).flatMap fun i => yAt b r (2 * i + 1)) := by
  simp only [blockMix, blockMixYs_range]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]; rfl

/-- Concatenating constant-length lists multiplies their length by the number of members. -/
theorem length_flatMap_const {α β : Type} (l : List α) {f : α → List β} {n : Nat}
    (h : ∀ a, (f a).length = n) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, h, ih, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- Serializing sixteen 32-bit words returns exactly 64 bytes. -/
theorem serialize_length (x : Vector Word 16) : (serialize x).length = 64 := by
  rw [serialize, length_flatMap_const _ (n := 4) fun _ => rfl]; simp

/-- For every byte list, Salsa20/8 returns exactly 64 bytes. -/
theorem salsa_length (t : List (BitVec 8)) : (salsa t).length = 64 := serialize_length _

/-- For every input, block parameter and index, `Y[i]` has 64 bytes. -/
theorem yAt_length (i : Nat) : (yAt b r i).length = 64 := by
  rw [yAt_eq]; exact salsa_length _

/-- BlockMix returns `128 * r` bytes for every input of that length. -/
theorem blockMix_length {r : Nat} {b : List (BitVec 8)} (_h : b.length = 128 * r) :
    (blockMix r b).length = 128 * r := by
  rw [blockMix_eq, List.length_append, length_flatMap_const _ fun _ => yAt_length _ _ _,
    length_flatMap_const _ fun _ => yAt_length _ _ _, List.length_range]
  omega

/-- Repeated BlockMix preserves the length of every `128 * r`-byte input, for every count. -/
theorem repeat_blockMix_length {r : Nat} {b : List (BitVec 8)} (h : b.length = 128 * r) (i : Nat) :
    (Nat.repeat (blockMix r) i b).length = 128 * r := by
  induction i with
  | zero => exact h
  | succ i ih => exact blockMix_length ih

/-- For any step function and count, iteration can take its first step before the remaining steps. -/
theorem repeat_succ' {α : Type} (f : α → α) :
    ∀ (i : Nat) (x : α), Nat.repeat f (i + 1) x = Nat.repeat f i (f x)
  | 0, _ => rfl
  | i + 1, x => by
    show f (Nat.repeat f (i + 1) x) = f (Nat.repeat f i (f x))
    rw [repeat_succ' f i x]

/-- Store the state, then apply `f`, for `n` steps, extending an existing array.
This sequential fill supports the implementation bridge for `powHash_eq_spec`. -/
def fillLoop {α : Type} (f : α → α) : Nat → α → Array α → Array α × α
  | 0, x, v => (v, x)
  | n + 1, x, v => fillLoop f n (f x) (v.push x)

/-- For any step function, initial state, array and count, sequential fill appends all iterates
and returns the final iterate.
This theorem is the representation-independent fill bridge for `powHash_eq_spec`. -/
theorem fillLoop_eq {α : Type} (f : α → α) : ∀ (n : Nat) (x : α) (v : Array α),
    fillLoop f n x v =
      ((v.toList ++ (List.range n).map fun i => Nat.repeat f i x).toArray, Nat.repeat f n x)
  | 0, x, v => by simp [fillLoop, Nat.repeat]
  | n + 1, x, v => by
    rw [fillLoop, fillLoop_eq f n (f x) (v.push x), repeat_succ']
    simp only [Array.toList_push, List.append_assoc, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.singleton_append, Nat.repeat]
    congr 3
    exact congrArg (x :: ·) (List.map_congr_left fun i _ => (repeat_succ' f i x).symm)

/-- For every BlockMix parameter, count and byte list, sequential fill from an empty array
returns the reference ROMix blocks and its final state. -/
theorem fill_eq_spec (r N : Nat) (b : List (BitVec 8)) :
    fillLoop (blockMix r) N b #[] =
      (((List.range N).map fun i => Nat.repeat (blockMix r) i b).toArray,
        Nat.repeat (blockMix r) N b) := by
  rw [fillLoop_eq]
  simp

end DogeLib.Cryptography.Hash.Scrypt
