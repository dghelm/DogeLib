module

public import DogeLib.Block.Subsidy
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the block subsidy

The theorems are about the definitions of `DogeLib.Block.Subsidy` (design record 0010, stage 0010a).

- `uniformInt_preimages`: for the two mainnet ranges, the bucket sizes of Boost's distribution, the words that give each value, and the words that the distribution rejects.
- `Mt19937.output_seed_10000`: output number 10,000 of the generator with the default seed 5489 is 4123659995.

`Mt19937.output_seed_10000` is a kernel computation.
The kernel evaluates the array updates of `Mt19937.seed` and `Mt19937.twist` slowly: about 37 seconds for one seed and 15 seconds for one twist.
So the module defines an evaluator on lists, proves that it agrees with the definitions for every seed (`Mt19937.output_seed_eq`), and evaluates that.

No theorem here says that `uniformInt` returns a value with a given fuel, or that a subsidy has a given distribution.
-/

@[expose] public section
namespace DogeLib.Block

/-! ## The distribution -/

/--
For every range `maxValue ≥ 1` with a positive bucket size, every word and every `value`:
`uniformIntAccept` returns `value` exactly when `1 ≤ value ≤ maxValue` and the word lies in the interval `[(value - 1) * bucket, value * bucket)`.
-/
theorem uniformIntAccept_eq_some_iff (maxValue : Nat) (word : UInt32) (value : Nat)
    (hmax : 1 ≤ maxValue) (hbucket : 0 < uniformIntBucket maxValue) :
    uniformIntAccept maxValue word = some value ↔
      1 ≤ value ∧ value ≤ maxValue ∧ (value - 1) * uniformIntBucket maxValue ≤ word.toNat ∧
        word.toNat < value * uniformIntBucket maxValue := by
  simp only [uniformIntAccept]
  generalize uniformIntBucket maxValue = bucket at hbucket ⊢
  generalize hq : word.toNat / bucket = q
  have hle : value - 1 ≤ q ↔ (value - 1) * bucket ≤ word.toNat := hq ▸ Nat.le_div_iff_mul_le hbucket
  have hlt : q < value ↔ word.toNat < value * bucket := hq ▸ Nat.div_lt_iff_lt_mul hbucket
  split
  · simp only [Option.some.injEq]
    constructor
    · intro h
      exact ⟨by omega, by omega, hle.mp (by omega), hlt.mp (by omega)⟩
    · rintro ⟨h1, _, h3, h4⟩
      have := hle.mpr h3
      have := hlt.mpr h4
      omega
  · simp only [reduceCtorEq, false_iff]
    rintro ⟨h1, h2, _, h4⟩
    have := hlt.mpr h4
    omega

/--
For every range `maxValue ≥ 1` with a positive bucket size and every word:
`uniformIntAccept` rejects the word exactly when the word is at least `maxValue * bucket`.
-/
theorem uniformIntAccept_eq_none_iff (maxValue : Nat) (word : UInt32)
    (hmax : 1 ≤ maxValue) (hbucket : 0 < uniformIntBucket maxValue) :
    uniformIntAccept maxValue word = none ↔ maxValue * uniformIntBucket maxValue ≤ word.toNat := by
  simp only [uniformIntAccept]
  generalize uniformIntBucket maxValue = bucket at hbucket ⊢
  generalize hq : word.toNat / bucket = q
  have hle : maxValue ≤ q ↔ maxValue * bucket ≤ word.toNat := hq ▸ Nat.le_div_iff_mul_le hbucket
  split
  · simp only [reduceCtorEq, false_iff]; omega
  · simp only [true_iff]; omega

/--
Boost's draw on the two mainnet ranges, `maxReward = 999999` and `maxReward = 499999`.

1. The bucket size is 4,294 for 999,999 and 8,589 for 499,999.
2. For both ranges, `maxReward * bucket ≤ 2^32`.
3. For both ranges and every `value`, a 32-bit word gives `value` exactly when `1 ≤ value ≤ maxReward` and the word lies in `[(value - 1) * bucket, value * bucket)`.
   With part 2, that interval lies below `2^32`. So each value from 1 to `maxReward` has exactly `bucket` accepted words.
4. For both ranges, the draw rejects a word exactly when the word is at least `maxReward * bucket`.

The statement is about one word, `uniformIntAccept`. It does not say how many words `uniformInt` reads.
A draw by remainder, or another bucket size, does not satisfy part 3.
-/
@[theorem_tag property]
theorem uniformInt_preimages :
    uniformIntBucket 999999 = 4294 ∧ uniformIntBucket 499999 = 8589 ∧
      ∀ maxReward, maxReward = 999999 ∨ maxReward = 499999 →
        maxReward * uniformIntBucket maxReward ≤ 2 ^ 32 ∧
        (∀ (value : Nat) (word : UInt32), uniformIntAccept maxReward word = some value ↔
          1 ≤ value ∧ value ≤ maxReward ∧ (value - 1) * uniformIntBucket maxReward ≤ word.toNat ∧
            word.toNat < value * uniformIntBucket maxReward) ∧
        (∀ word : UInt32, uniformIntAccept maxReward word = none ↔
          maxReward * uniformIntBucket maxReward ≤ word.toNat) := by
  have h1 : uniformIntBucket 999999 = 4294 := by decide
  have h2 : uniformIntBucket 499999 = 8589 := by decide
  refine ⟨h1, h2, ?_⟩
  rintro maxReward (rfl | rfl)
  · exact ⟨by rw [h1]; decide,
      fun value word => uniformIntAccept_eq_some_iff _ word value (by decide) (by rw [h1]; decide),
      fun word => uniformIntAccept_eq_none_iff _ word (by decide) (by rw [h1]; decide)⟩
  · exact ⟨by rw [h2]; decide,
      fun value word => uniformIntAccept_eq_some_iff _ word value (by decide) (by rw [h2]; decide),
      fun word => uniformIntAccept_eq_none_iff _ word (by decide) (by rw [h2]; decide)⟩

/-! ## The generator -/

namespace Mt19937

/-- An invariant that holds at the start of `Nat.fold`, and that every step keeps, holds at its end. -/
theorem fold_induction {α : Type} (P : Nat → α → Prop) :
    ∀ (n : Nat) (f : (i : Nat) → i < n → α → α) (init : α), P 0 init →
      (∀ i h a, P i a → P (i + 1) (f i h a)) → P n (Nat.fold n f init)
  | 0, _, _, h0, _ => by simpa using h0
  | n + 1, f, init, h0, hs => by
    rw [Nat.fold_succ]
    exact hs n _ _ (fold_induction P n _ init h0 fun i h a ha => hs i _ a ha)

/-- The `count` words that the loop of `seed` writes after the word `prev` at index `k`. -/
def seedWords : (count k : Nat) → (prev : UInt32) → List UInt32
  | 0, _, _ => []
  | count + 1, k, prev =>
    let word := (1812433253 : UInt32) * (prev ^^^ (prev >>> 30)) + (k + 1).toUInt32
    word :: seedWords count (k + 1) word

/-- `normalizeState` on the list of the 624 words. -/
def normalizeList (l : List UInt32) : List UInt32 :=
  let y0 := l.getD 396 0 ^^^ l.getD 623 0
  let y0 := if y0 &&& upperMask != 0 then ((y0 ^^^ a) <<< 1) ||| 1 else y0 <<< 1
  let l := l.set 0 ((l.getD 0 0 &&& upperMask) ||| (y0 &&& lowerMask))
  if l.all (· == 0) then l.set 0 upperMask else l

/--
`twist` on lists, without an array update.
`rest` holds the words that the pass has not replaced, and `doneRev` holds the new words, newest first.
One step replaces the head of `rest`.
It reads the next word from `rest`, or the first new word at the last step.
It reads the word 397 places on from `rest`, or the new word 227 places back.
-/
def twistList : (rest doneRev : List UInt32) → List UInt32
  | [], doneRev => doneRev.reverse
  | cur :: rest, doneRev =>
    let next := rest.headD (doneRev.getLastD 0)
    let y := (cur &&& upperMask) ||| (next &&& lowerMask)
    twistList rest
      ((rest[396]?.getD (doneRev.getD 226 0) ^^^ (y >>> 1) ^^^ ((next &&& 1) * a)) :: doneRev)

/-- `count` passes of `twistList`. -/
def twistsList : (count : Nat) → List UInt32 → List UInt32
  | 0, l => l
  | count + 1, l => twistsList count (twistList l [])

/-- `count` calls of `twist`. -/
def twists : (count : Nat) → Vector UInt32 624 → Vector UInt32 624
  | 0, x => x
  | count + 1, x => twists count (twist x)

/-- For every list `l` and index `n` below its length, the first `n + 1` elements of `l.set n v` are the first `n` elements of `l`, then `v`. -/
private theorem take_succ_set {α : Type} (l : List α) (n : Nat) (v : α) (h : n < l.length) :
    (l.set n v).take (n + 1) = l.take n ++ [v] := by
  induction l generalizing n with
  | nil => simp at h
  | cons head tail ih => cases n with
    | zero => simp
    | succ n => simpa using ih n (by simpa using h)

/-- For every list `l` and index `n` below its length, `l.set n v` holds `v` at index `n`. -/
private theorem getD_set_self {α : Type} (l : List α) (n : Nat) (v d : α) (h : n < l.length) :
    (l.set n v).getD n d = v := by
  simp [List.getD_eq_getElem?_getD, h]

/-- For every 624-word vector and every index below 624, the word at the index is the element of the list at that index. -/
theorem getElem_eq_getD (x : Vector UInt32 624) (i : Nat) (h : i < 624) :
    x[i] = x.toList.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `seedWords` with a count of zero is the empty list. -/
theorem seedWords_zero (k : Nat) (prev : UInt32) : seedWords 0 k prev = [] := rfl

/--
For every seed, the loop of `seed` leaves the words `value :: seedWords 623 0 value`.
The statement is about the words before `normalizeState`.
-/
theorem seedLoop_toList (value : UInt32) :
    (Nat.fold 623 (fun k _ (x : Vector UInt32 624) =>
      x.set (k + 1) ((1812433253 : UInt32) * (x[k] ^^^ (x[k] >>> 30)) + (k + 1).toUInt32))
      ((Vector.replicate 624 0).set 0 value)).toList = value :: seedWords 623 0 value := by
  have key := fold_induction (α := Vector UInt32 624)
    (fun k x => k ≤ 623 → x.toList.take (k + 1) ++ seedWords (623 - k) k (x.toList.getD k 0) =
      value :: seedWords 623 0 value)
    623 (fun k _ (x : Vector UInt32 624) =>
      x.set (k + 1) ((1812433253 : UInt32) * (x[k] ^^^ (x[k] >>> 30)) + (k + 1).toUInt32))
    ((Vector.replicate 624 0).set 0 value) ?init ?step (Nat.le_refl _)
  · rw [Nat.sub_self, seedWords_zero, List.append_nil, List.take_of_length_le (Nat.le_of_eq Vector.length_toList)] at key
    exact key
  · intro _
    have h0 : ((Vector.replicate 624 (0 : UInt32)).set 0 value).toList = value :: List.replicate 623 0 := by
      rw [Vector.toList_set, Vector.toList_replicate]; rfl
    rw [h0]; rfl
  · intro i h x ih _
    have ih := ih (by omega)
    have hlen : i + 1 < x.toList.length := by rw [Vector.length_toList]; omega
    rw [Vector.toList_set, take_succ_set _ _ _ hlen, getD_set_self _ _ _ _ hlen, ← ih,
      show 623 - i = (623 - (i + 1)) + 1 by omega, seedWords, getElem_eq_getD x i (by omega)]
    simp only [List.append_assoc, List.singleton_append]

/-- For every 624-word vector, `normalizeList` on its list gives the list of `normalizeState`. -/
theorem normalizeState_toList (x : Vector UInt32 624) :
    (normalizeState x).toList = normalizeList x.toList := by
  unfold normalizeState normalizeList
  simp only [getElem_eq_getD x 396 (by decide), getElem_eq_getD x 623 (by decide),
    getElem_eq_getD x 0 (by decide), Vector.toList_set]
  rw [apply_ite Vector.toList]
  simp only [Vector.toList_set]

/--
For every list `l` of 624 words and every step `j < 624` of a pass, the next word that `twistList` reads is `l[(j + 1) % 624]`.
Here `l` is the whole array at step `j`: the first `j` words are new, and the others are not yet replaced.
-/
theorem twistNext_eq (l : List UInt32) (hl : l.length = 624) (j : Nat) (hj : j < 624) :
    (l.drop (j + 1)).headD ((l.take j).reverse.getLastD 0) = l.getD ((j + 1) % 624) 0 := by
  by_cases h : j + 1 < 624
  · rw [Nat.mod_eq_of_lt h]
    simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD, hl, h]
  · have hj : j = 623 := by omega
    subst hj
    simp [List.drop_of_length_le, hl, List.getLastD_eq_getLast?, List.getLast?_reverse,
      List.getD_eq_getElem?_getD, List.head?_eq_getElem?]

/--
For every list `l` of 624 words and every step `j < 624` of a pass, the far word that `twistList` reads is `l[(j + 397) % 624]`.
Here `l` is the whole array at step `j`, as in `twistNext_eq`.
-/
theorem twistFar_eq (l : List UInt32) (hl : l.length = 624) (j : Nat) (hj : j < 624) :
    ((l.drop (j + 1))[396]?).getD ((l.take j).reverse.getD 226 0) =
      l.getD ((j + 397) % 624) 0 := by
  by_cases h : j + 397 < 624
  · rw [Nat.mod_eq_of_lt h]
    simp [List.getElem?_drop, List.getD_eq_getElem?_getD, hl, h, show j + 1 + 396 = j + 397 by omega]
  · rw [show (j + 397) % 624 = j - 227 by omega]
    simp [List.getElem?_drop, List.getD_eq_getElem?_getD, hl, h, show j + 1 + 396 = j + 397 by omega]
    rw [List.getElem?_reverse (by rw [List.length_take, hl]; omega), List.length_take, hl,
      List.getElem?_take_of_lt (by omega), show min j 624 - 1 - 226 = j - 227 by omega]

/-- For every 624-word vector, `twistList` on its list, with no new words yet, gives the list of `twist`. -/
theorem twist_toList (x : Vector UInt32 624) : (twist x).toList = twistList x.toList [] := by
  have key := fold_induction (α := Vector UInt32 624)
    (fun j y => twistList (y.toList.drop j) (y.toList.take j).reverse = twistList x.toList [])
    624 (fun j _ (x : Vector UInt32 624) =>
      let next := x[(j + 1) % 624]'(Nat.mod_lt _ (by decide))
      let y := (x[j] &&& upperMask) ||| (next &&& lowerMask)
      x.set j (x[(j + 397) % 624]'(Nat.mod_lt _ (by decide)) ^^^ (y >>> 1) ^^^ ((next &&& 1) * a)))
    x rfl ?step
  · rw [List.drop_of_length_le (Nat.le_of_eq Vector.length_toList),
      List.take_of_length_le (Nat.le_of_eq Vector.length_toList), twistList, List.reverse_reverse] at key
    exact key
  · intro j h y ih
    have hl : y.toList.length = 624 := Vector.length_toList
    have hj : j < y.toList.length := by omega
    rw [← ih, Vector.toList_set, List.drop_set_of_lt (by omega), take_succ_set _ _ _ hj,
      List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.drop_eq_getElem_cons hj, twistList]
    simp only [twistNext_eq _ hl j h, twistFar_eq _ hl j h,
      getElem_eq_getD y _ (Nat.mod_lt _ (by decide)), getElem_eq_getD y j h,
      show y.toList.getD j 0 = y.toList[j] by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]]

/-- For every count and every 624-word vector, `twistsList` on its list gives the list of `twists`. -/
theorem twists_toList (count : Nat) (x : Vector UInt32 624) :
    (twists count x).toList = twistsList count x.toList := by
  induction count generalizing x with
  | zero => rfl
  | succ count ih => rw [twists, twistsList, ih, twist_toList]

/-- Two generator states with the same result of `next` have the same outputs. -/
theorem output_congr_next (g g' : Mt19937) (h : g.next = g'.next) (k : Nat) :
    g.output k = g'.output k := by
  cases k <;> simp only [output, h]

/-- At position 624, `next` gives the result that it gives at position 0 of the twisted words. -/
theorem next_twist (x : Vector UInt32 624) (h : 624 ≤ 624) :
    (⟨x, 624, h⟩ : Mt19937).next = (⟨twist x, 0, Nat.zero_le _⟩ : Mt19937).next := by
  simp [next]

/-- For a state at position `i` and every `k` with `i + k < 624`, output `k + 1` is the tempered word at index `i + k`. No twist occurs. -/
theorem output_of_lt (x : Vector UInt32 624) (k i : Nat) (h : i ≤ 624) (hk : i + k < 624) :
    (⟨x, i, h⟩ : Mt19937).output k = temper x[i + k] := by
  induction k generalizing i with
  | zero => simp [output, next, show i < 624 by omega]
  | succ k ih =>
    rw [output]
    simp only [next, show i < 624 by omega, dite_true]
    rw [ih (i + 1) (by omega) (by omega)]
    congr 2; omega

/--
For a state at position `i` and every `k` with `624 ≤ i + k`, output `k + 1` is output `i + k - 624 + 1` of the same words at position 624.
The outputs before it only move the position.
-/
theorem output_skip (x : Vector UInt32 624) (k i : Nat) (h : i ≤ 624) (hk : 624 ≤ i + k) :
    (⟨x, i, h⟩ : Mt19937).output k = (⟨x, 624, Nat.le_refl _⟩ : Mt19937).output (i + k - 624) := by
  induction k generalizing i with
  | zero =>
    have hi : i = 624 := by omega
    subst hi
    rw [show 624 + 0 - 624 = 0 by omega]
  | succ k ih =>
    by_cases hi : i < 624
    · rw [output]
      simp only [next, hi, dite_true]
      rw [ih (i + 1) (by omega) (by omega), show i + 1 + k - 624 = i + (k + 1) - 624 by omega]
    · have hi : i = 624 := by omega
      subst hi
      rw [show 624 + (k + 1) - 624 = k + 1 by omega]

/-- For words at position 624, every `q` and every `r < 624`: output `624 * q + r + 1` is the tempered word at index `r` after `q + 1` twists. -/
theorem output_twists (x : Vector UInt32 624) (q r : Nat) (hr : r < 624) :
    (⟨x, 624, Nat.le_refl _⟩ : Mt19937).output (624 * q + r) = temper (twists (q + 1) x)[r] := by
  induction q generalizing x with
  | zero =>
    rw [output_congr_next _ _ (next_twist x _), Nat.mul_zero, Nat.zero_add,
      output_of_lt _ _ _ _ (by omega)]
    simp [twists]
  | succ q ih =>
    rw [output_congr_next _ _ (next_twist x _), output_skip _ _ _ _ (by omega),
      show 0 + (624 * (q + 1) + r) - 624 = 624 * q + r by omega, ih]
    rfl

/--
For every seed, every `q` and every `r < 624`: output `624 * q + r + 1` of `seed value` is the tempered word at index `r` of the list evaluator.
The evaluator seeds with `seedWords`, normalizes with `normalizeList` and twists `q + 1` times with `twistList`.
So the evaluator computes the same outputs as `seed`, `twist` and `next`.
-/
@[theorem_tag model_agreement]
theorem output_seed_eq (value : UInt32) (q r : Nat) (hr : r < 624) :
    (seed value).output (624 * q + r) =
      temper ((twistsList (q + 1) (normalizeList (value :: seedWords 623 0 value))).getD r 0) := by
  rw [seed, output_twists _ _ _ hr, getElem_eq_getD _ _ hr, twists_toList, normalizeState_toList,
    seedLoop_toList]

/--
Output number 10,000 of `boost::mt19937` with the default seed 5489 (B1, line 89) is 4123659995.
The C++11 draft N3337, 26.5.5 [rand.predef], paragraph 3, requires this value of `std::mt19937`.
The kernel computes it through the list evaluator of `output_seed_eq`, in about 45 seconds.
-/
@[theorem_tag witness]
theorem output_seed_10000 : (seed 5489).output 9999 = 4123659995 := by
  rw [show 9999 = 624 * 16 + 15 from rfl, output_seed_eq _ _ _ (by decide)]
  decide +kernel

end Mt19937

end DogeLib.Block
