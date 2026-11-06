module

public import DogeLib.Cryptography.Hash.Scrypt
public import DogeLib.Cryptography.Proofs.Hash.Scrypt
public import DogeLib.Cryptography.Proofs.Hash.Pbkdf2

/-!
# Dogecoin's scrypt executable equals the RFC 7914 model

`powHash_eq_spec` proves that `scrypt_1024_1_1_256` equals the list model `Spec.scrypt` for every 80-byte input.
The model runs with N = 1024, r = 1, p = 1 and 32 output bytes, and the input is both password and salt.
`powHash_eq_fips` restates the same digest with the FIPS 180-4 SHA-256 model inside HMAC.

The proof crosses the representation once per component:

- `toModel` maps a word state to the model's 128 bytes, each word little-endian.
- `doubleRound_toBitVec` relates Core's statement order to the RFC order of `Spec.doubleRound`.
  Steps on disjoint words commute (`step_comm`), and a directed rewrite sorts Core's interleaved
  quarter-rounds into the RFC order.
- `blockMix_toModel` commutes the executable BlockMix with the model's `blockMix 1`.
- `fill_flat` relates the flat scratchpad to `fillLoop`, so `fillLoop_eq` gives the model's reference fill.
- `index_eq` and `integerify_toModel` show that `32 * (X[16] & 1023)` is 32 times Integerify modulo 1024.
- `flat_getElem!_lo` and `flat_getElem!_hi` show that each `!` read of the scratchpad is in bounds.
  So the default value of those reads is never used.

No theorem here evaluates a scrypt digest.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Scrypt

open Spec (Word)
open Hmac.Spec (toBytes)

/-! ## Words and steps -/

/-- The words of a vector as 32-bit bit vectors. -/
def bv (x : Vector UInt32 16) : Vector Word 16 := x.map UInt32.toBitVec

/-- For a rotation amount strictly between 0 and 32, `rotl` is `BitVec.rotateLeft`. -/
theorem rotl_toBitVec (a : UInt32) (n : UInt32) (h0 : 0 < n.toNat) (h : n.toNat < 32) :
    (rotl a n).toBitVec = a.toBitVec.rotateLeft n.toNat := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [rotl, BitVec.getLsbD_rotateLeft, BitVec.getLsbD_or, UInt32.toBitVec_shiftLeft,
    UInt32.toBitVec_shiftRight, UInt32.toBitVec_or, UInt32.toBitVec_sub]
  simp
  have e1 : n.toNat % 32 = n.toNat := Nat.mod_eq_of_lt h
  have e2 : (4294967296 - n.toNat) % 32 = 32 - n.toNat := by omega
  rw [e1, e2]
  by_cases hin : i < n.toNat
  · simp [hin, Nat.add_comm]
  · simp [hin, hi, BitVec.getLsbD_of_ge a.toBitVec (32 - n.toNat + i) (by omega)]

/-- For a rotation amount strictly between 0 and 32, one executable step is the model's `step`. -/
theorem step_toBitVec (x : Vector UInt32 16) (i j k : Fin 16) (n : UInt32)
    (h0 : 0 < n.toNat) (h : n.toNat < 32) :
    bv (step x i j k n) = Spec.step (bv x) i j k n.toNat := by
  simp only [bv, step, Spec.step, Vector.map_set, Fin.getElem_fin, Vector.getElem_map,
    UInt32.toBitVec_xor, UInt32.toBitVec_add, rotl_toBitVec _ _ h0 h]

/-- Two model steps commute when neither writes a word that the other reads or writes. -/
theorem step_comm (x : Vector Word 16) (i j k i' j' k' : Fin 16) (n n' : Nat)
    (h1 : i ≠ i') (h2 : i ≠ j') (h3 : i ≠ k') (h4 : i' ≠ j) (h5 : i' ≠ k) :
    Spec.step (Spec.step x i j k n) i' j' k' n' = Spec.step (Spec.step x i' j' k' n') i j k n := by
  have n1 := Fin.val_ne_of_ne h1; have n2 := Fin.val_ne_of_ne h2; have n3 := Fin.val_ne_of_ne h3
  have n4 := Fin.val_ne_of_ne h4; have n5 := Fin.val_ne_of_ne h5
  simp only [Spec.step, Fin.getElem_fin, Vector.getElem_set, n1, Ne.symm n1, n2, n3, n4, n5, ite_false]
  exact Vector.set_comm _ _ n1

/-- `step_comm`, oriented to move a step of a lower column (`i % 4`) before a step of a higher one.
The `+ 0` keeps `simp` from treating the statement as a permutation lemma. -/
theorem step_sort_column (x : Vector Word 16) (i j k i' j' k' : Fin 16) (n n' : Nat)
    (_order : i'.val % 4 < i.val % 4)
    (h1 : i ≠ i') (h2 : i ≠ j') (h3 : i ≠ k') (h4 : i' ≠ j) (h5 : i' ≠ k) :
    Spec.step (Spec.step x i j k n) i' j' k' n' = Spec.step (Spec.step x i' j' k' n') i j k (n + 0) :=
  step_comm x i j k i' j' k' n n' h1 h2 h3 h4 h5

/-- `step_comm`, oriented to move a step of a lower row (`i / 4`) before a step of a higher one. -/
theorem step_sort_row (x : Vector Word 16) (i j k i' j' k' : Fin 16) (n n' : Nat)
    (_order : i'.val / 4 < i.val / 4)
    (h1 : i ≠ i') (h2 : i ≠ j') (h3 : i ≠ k') (h4 : i' ≠ j) (h5 : i' ≠ k) :
    Spec.step (Spec.step x i j k n) i' j' k' n' = Spec.step (Spec.step x i' j' k' n') i j k (n + 0) :=
  step_comm x i j k i' j' k' n n' h1 h2 h3 h4 h5

/-- The column statements of `xor_salsa8`, over bit vectors, in Core's order. -/
def columnsCore (x : Vector Word 16) : Vector Word 16 :=
  let x := Spec.step x  4  0 12  7; let x := Spec.step x  9  5  1  7
  let x := Spec.step x 14 10  6  7; let x := Spec.step x  3 15 11  7
  let x := Spec.step x  8  4  0  9; let x := Spec.step x 13  9  5  9
  let x := Spec.step x  2 14 10  9; let x := Spec.step x  7  3 15  9
  let x := Spec.step x 12  8  4 13; let x := Spec.step x  1 13  9 13
  let x := Spec.step x  6  2 14 13; let x := Spec.step x 11  7  3 13
  let x := Spec.step x  0 12  8 18; let x := Spec.step x  5  1 13 18
  let x := Spec.step x 10  6  2 18
  Spec.step x 15 11  7 18

/-- The row statements of `xor_salsa8`, over bit vectors, in Core's order. -/
def rowsCore (x : Vector Word 16) : Vector Word 16 :=
  let x := Spec.step x  1  0  3  7; let x := Spec.step x  6  5  4  7
  let x := Spec.step x 11 10  9  7; let x := Spec.step x 12 15 14  7
  let x := Spec.step x  2  1  0  9; let x := Spec.step x  7  6  5  9
  let x := Spec.step x  8 11 10  9; let x := Spec.step x 13 12 15  9
  let x := Spec.step x  3  2  1 13; let x := Spec.step x  4  7  6 13
  let x := Spec.step x  9  8 11 13; let x := Spec.step x 14 13 12 13
  let x := Spec.step x  0  3  2 18; let x := Spec.step x  5  4  7 18
  let x := Spec.step x 10  9  8 18
  Spec.step x 15 14 13 18

/-- The executable double round, read as bit vectors, is Core's column statements then Core's row statements. -/
theorem doubleRound_toBitVec_core (x : Vector UInt32 16) :
    bv (doubleRound x) = rowsCore (columnsCore (bv x)) := by
  simp only [doubleRound, rowsCore, columnsCore]
  simp (disch := decide) only [step_toBitVec, UInt32.reduceToNat]

/-- The column statements of `Spec.doubleRound`, one quarter-round at a time. -/
def columnsRfc (x : Vector Word 16) : Vector Word 16 :=
  let x := Spec.step x  4  0 12  7; let x := Spec.step x  8  4  0  9
  let x := Spec.step x 12  8  4 13; let x := Spec.step x  0 12  8 18
  let x := Spec.step x  9  5  1  7; let x := Spec.step x 13  9  5  9
  let x := Spec.step x  1 13  9 13; let x := Spec.step x  5  1 13 18
  let x := Spec.step x 14 10  6  7; let x := Spec.step x  2 14 10  9
  let x := Spec.step x  6  2 14 13; let x := Spec.step x 10  6  2 18
  let x := Spec.step x  3 15 11  7; let x := Spec.step x  7  3 15  9
  let x := Spec.step x 11  7  3 13
  Spec.step x 15 11  7 18

/-- The row statements of `Spec.doubleRound`, one quarter-round at a time. -/
def rowsRfc (x : Vector Word 16) : Vector Word 16 :=
  let x := Spec.step x  1  0  3  7; let x := Spec.step x  2  1  0  9
  let x := Spec.step x  3  2  1 13; let x := Spec.step x  0  3  2 18
  let x := Spec.step x  6  5  4  7; let x := Spec.step x  7  6  5  9
  let x := Spec.step x  4  7  6 13; let x := Spec.step x  5  4  7 18
  let x := Spec.step x 11 10  9  7; let x := Spec.step x  8 11 10  9
  let x := Spec.step x  9  8 11 13; let x := Spec.step x 10  9  8 18
  let x := Spec.step x 12 15 14  7; let x := Spec.step x 13 12 15  9
  let x := Spec.step x 14 13 12 13
  Spec.step x 15 14 13 18

/-- For every state, Core's column statements equal the RFC's column quarter-rounds. -/
theorem columnsCore_eq (x : Vector Word 16) : columnsCore x = columnsRfc x := by
  simp only [columnsCore, columnsRfc]
  simp (disch := decide) only [step_sort_column, Nat.add_zero]

/-- For every state, Core's row statements equal the RFC's row quarter-rounds. -/
theorem rowsCore_eq (x : Vector Word 16) : rowsCore x = rowsRfc x := by
  simp only [rowsCore, rowsRfc]
  simp (disch := decide) only [step_sort_row, Nat.add_zero]

/-- For every state, Core's statement order gives the RFC 7914 §3 double round. -/
theorem rowsCore_columnsCore (x : Vector Word 16) :
    rowsCore (columnsCore x) = Spec.doubleRound x := by
  rw [columnsCore_eq, rowsCore_eq]
  rfl

/-- For every state, the executable double round in Core's order equals the model's double round. -/
theorem doubleRound_toBitVec (x : Vector UInt32 16) :
    bv (doubleRound x) = Spec.doubleRound (bv x) := by
  rw [doubleRound_toBitVec_core, rowsCore_columnsCore]

/-! ## Bytes of words -/

/-- The four bytes of a word, least significant first, as `Spec.serialize` writes them. -/
def wordBytes (w : Word) : List (BitVec 8) :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- `Spec.serialize` concatenates the bytes of each word in order. -/
theorem serialize_eq (x : Vector Word 16) : Spec.serialize x = x.toList.flatMap wordBytes := rfl

/-- In a concatenation of chunks of length `c`, position `c * j + r` with `r < c` is position `r` of chunk `j`. -/
theorem getElem?_flatMap_chunk {α β : Type} (g : α → List β) (c : Nat) (hg : ∀ a, (g a).length = c) :
    ∀ (l : List α) (j r : Nat) (hj : j < l.length), r < c →
      (l.flatMap g)[c * j + r]? = (g l[j])[r]?
  | [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a :: l, 0, r, _, hr => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getElem?_append_left (by rw [hg]; exact hr)]
  | a :: l, j + 1, r, hj, hr => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [List.getElem?_append_right (by rw [hg]; exact Nat.le_trans (Nat.le_mul_of_pos_right c (by omega)) (Nat.le_add_right _ _)),
      hg, show c * (j + 1) + r - c = c * j + r by rw [Nat.mul_succ]; omega]
    exact getElem?_flatMap_chunk g c hg l j r (by simp at hj; omega) hr

/-- The four bytes of a word, most significant first, concatenate to the word. -/
theorem wordBytes_concat (w : Word) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h24 : i < 24 <;>
    first
    | omega
    | (simp (disch := omega) [h8]
       all_goals (repeat' split) <;> (try intro) <;> first | omega | (congr 1 <;> omega))

/-- For every word index below 16, reading a serialized vector returns its word. -/
theorem wordLE_serialize (x : Vector Word 16) (j : Nat) (hj : j < 16) :
    Spec.wordLE (Spec.serialize x) j = x[j] := by
  have hl : j < x.toList.length := by simpa using hj
  have hg : ∀ w, (wordBytes w).length = 4 := fun _ => rfl
  have h0 := getElem?_flatMap_chunk wordBytes 4 hg x.toList j 0 hl (by decide)
  rw [Nat.add_zero] at h0
  simp only [Spec.wordLE, serialize_eq, List.getD_eq_getElem?_getD, h0,
    getElem?_flatMap_chunk wordBytes 4 hg x.toList j _ hl (by decide : 3 < 4),
    getElem?_flatMap_chunk wordBytes 4 hg x.toList j _ hl (by decide : 2 < 4),
    getElem?_flatMap_chunk wordBytes 4 hg x.toList j _ hl (by decide : 1 < 4)]
  simp only [wordBytes, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Vector.getElem_toList]
  exact wordBytes_concat _

/-- For every vector, reading the words of its serialization returns the vector. -/
theorem ofFn_wordLE_serialize (x : Vector Word 16) :
    Vector.ofFn (fun j : Fin 16 => Spec.wordLE (Spec.serialize x) j.val) = x := by
  ext j hj
  simp [wordLE_serialize x j hj]

/-! ## Salsa20/8 and BlockMix -/

/-- Wordwise XOR of two vectors of words. -/
def xorWords (a b : Vector Word 16) : Vector Word 16 := Vector.zipWith (· ^^^ ·) a b

/-- Wordwise XOR is commutative. -/
theorem xorWords_comm (a b : Vector Word 16) : xorWords a b = xorWords b a := by
  ext i hi
  simp [xorWords, BitVec.xor_comm]

/-- Bytewise XOR of the bytes of two words is the bytes of their XOR. -/
theorem wordBytes_xor (a b : Word) :
    List.zipWith (· ^^^ ·) (wordBytes a) (wordBytes b) = wordBytes (a ^^^ b) := by
  simp only [wordBytes, List.zipWith_cons_cons, List.zipWith_nil_left, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> simp [hi]

/-- For equal lengths, bytewise XOR of serialized words is the serialization of their wordwise XOR. -/
theorem zipWith_flatMap_wordBytes : ∀ (l₁ l₂ : List Word), l₁.length = l₂.length →
    List.zipWith (· ^^^ ·) (l₁.flatMap wordBytes) (l₂.flatMap wordBytes) =
      (List.zipWith (· ^^^ ·) l₁ l₂).flatMap wordBytes
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.flatMap_cons, List.zipWith_cons_cons]
    rw [List.zipWith_append (by rfl : (wordBytes a).length = (wordBytes b).length), wordBytes_xor,
      zipWith_flatMap_wordBytes l₁ l₂ (by simpa using h)]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- For all word vectors, bytewise XOR of their serializations is the serialization of their XOR. -/
theorem xorBytes_serialize (a b : Vector Word 16) :
    Pbkdf2.Spec.xorBytes (Spec.serialize a) (Spec.serialize b) = Spec.serialize (xorWords a b) := by
  simp only [Pbkdf2.Spec.xorBytes, serialize_eq, xorWords, Vector.toList_zipWith]
  exact zipWith_flatMap_wordBytes _ _ (by simp)

/-- For every vector, Salsa20/8 of its serialization is the serialization of the Salsa20/8 core. -/
theorem salsa_serialize (v : Vector Word 16) : Spec.salsa (Spec.serialize v) = Spec.serialize (Spec.core v) := by
  simp only [Spec.salsa, ofFn_wordLE_serialize]

/-- Iterated executable double rounds, read as bit vectors, are iterated model double rounds. -/
theorem repeat_doubleRound_toBitVec (n : Nat) (x : Vector UInt32 16) :
    bv (Nat.repeat doubleRound n x) = Nat.repeat Spec.doubleRound n (bv x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, doubleRound_toBitVec, ih]

/-- For all word vectors, `xor_salsa8(B, Bx)` is the Salsa20/8 core of `B xor Bx`.
Core adds the rounds' output to the input, and the RFC adds the input to the output.
Addition commutes, so the results agree. -/
theorem xorSalsa8_toBitVec (b bx : Vector UInt32 16) :
    bv (xorSalsa8 b bx) = Spec.core (xorWords (bv b) (bv bx)) := by
  have hy : bv (Vector.zipWith (· ^^^ ·) b bx) = xorWords (bv b) (bv bx) := by
    ext i hi
    simp [bv, xorWords]
  simp only [xorSalsa8, Spec.core, ← hy, ← repeat_doubleRound_toBitVec]
  ext i hi
  simp [bv, BitVec.add_comm]

/-- The model bytes of a state: `X[0..15]` then `X[16..31]`, each word little-endian.
`le32enc` writes these 128 bytes from `X`. -/
def toModel (x : State) : List (BitVec 8) := Spec.serialize (bv x.1) ++ Spec.serialize (bv x.2)

/-- The model state has 128 bytes. -/
theorem toModel_length (x : State) : (toModel x).length = 128 := by
  simp [toModel, serialize_length]

/-- Block 0 of a model state is the serialization of `X[0..15]`. -/
theorem blk_toModel_zero (x : State) : Spec.blk (toModel x) 0 = Spec.serialize (bv x.1) := by
  simp [Spec.blk, toModel, serialize_length]

/-- Block 1 of a model state is the serialization of `X[16..31]`. -/
theorem blk_toModel_one (x : State) : Spec.blk (toModel x) 1 = Spec.serialize (bv x.2) := by
  simp [Spec.blk, toModel, serialize_length]
  exact List.take_of_length_le (by rw [serialize_length]; exact Nat.le_refl _)

/-- **Commutation.** For every state, the executable BlockMix followed by `toModel` equals
`toModel` followed by the model's scryptBlockMix with `r = 1`. -/
theorem blockMix_toModel (x : State) : toModel (blockMix x) = Spec.blockMix 1 (toModel x) := by
  rw [blockMix_eq]
  simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.mul_zero,
    Nat.zero_add]
  have e0 : yAt (toModel x) 1 0 = Spec.serialize (bv (xorSalsa8 x.1 x.2)) := by
    simp only [yAt, show 2 * 1 - 1 = 1 from rfl, blk_toModel_zero, blk_toModel_one, xorBytes_serialize,
      salsa_serialize, xorSalsa8_toBitVec, xorWords_comm (bv x.2)]
  have e1 : yAt (toModel x) 1 1 = Spec.serialize (bv (xorSalsa8 x.2 (xorSalsa8 x.1 x.2))) := by
    show Spec.salsa (Pbkdf2.Spec.xorBytes (yAt (toModel x) 1 0) (Spec.blk (toModel x) 1)) = _
    rw [e0, blk_toModel_one, xorBytes_serialize, salsa_serialize, xorWords_comm]
    simp only [xorSalsa8_toBitVec]
  rw [e0, e1]
  rfl

/-- For every count and state, iterated BlockMix commutes with `toModel`. -/
theorem repeat_blockMix_toModel (n : Nat) (x : State) :
    toModel (Nat.repeat blockMix n x) = Nat.repeat (Spec.blockMix 1) n (toModel x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, blockMix_toModel, ih]

/-! ## The scratchpad -/

/-- The 32 words of a state, `X[0..31]`. -/
def words (x : State) : List UInt32 := x.1.toList ++ x.2.toList

/-- States stored one after another, 32 words each, so that `V[32 * i + k]` is word `k` of state `i`. -/
def flat (w : List State) : Array UInt32 := (w.flatMap words).toArray

/-- **Flattening.** The flat first loop stores the words of the states that `fillLoop` stores whole.
It also returns the same final state. This holds for every count, state and list of stored states. -/
theorem fill_flat : ∀ (n : Nat) (x : State) (w : List State),
    fill n x (flat w) =
      (flat (fillLoop blockMix n x w.toArray).1.toList, (fillLoop blockMix n x w.toArray).2)
  | 0, x, w => by simp [fill, fillLoop]
  | n + 1, x, w => by
    have hv : flat w ++ x.1.toArray ++ x.2.toArray = flat (w ++ [x]) := by
      simp [flat, words, List.flatMap_append, Array.append_assoc]
      rfl
    rw [fill, hv, fill_flat n, fillLoop, List.push_toArray]

/-- Each state has 32 words. -/
theorem words_length (x : State) : (words x).length = 32 := by simp [words]

/-- For a stored state `j` and `k < 16`, `V[32 * j + k]` is `X[k]` of that state. -/
theorem flat_getElem!_lo (w : List State) (j k : Nat) (hj : j < w.length) (hk : k < 16) :
    (flat w)[32 * j + k]! = (w[j]).1[k] := by
  have h := getElem?_flatMap_chunk words 32 words_length w j k hj (by omega)
  simp only [flat, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, h, words]
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- For a stored state `j` and `k < 16`, `V[32 * j + 16 + k]` is `X[16 + k]` of that state. -/
theorem flat_getElem!_hi (w : List State) (j k : Nat) (hj : j < w.length) (hk : k < 16) :
    (flat w)[32 * j + 16 + k]! = (w[j]).2[k] := by
  have h := getElem?_flatMap_chunk words 32 words_length w j (16 + k) hj (by omega)
  simp only [flat, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, Nat.add_assoc, h, words]
  rw [List.getElem?_append_right (by simp)]
  simp [hk]

/-! ## Integerify -/

/-- `32 * (w & 1023)` in 32-bit arithmetic is 32 times `w` modulo 1024, without overflow. -/
theorem index_eq (w : UInt32) : ((32 : UInt32) * (w &&& 1023)).toNat = 32 * (w.toNat % 1024) := by
  rw [UInt32.toNat_mul, UInt32.toNat_and, show (1023 : UInt32).toNat = 2 ^ 10 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt w.toNat (show 0 < 2 ^ 10 by decide)
  simp only [UInt32.reduceToNat]
  omega

/-- The little-endian value of a concatenation. -/
theorem leNat_append (a b : List (BitVec 8)) :
    Spec.leNat (a ++ b) = Spec.leNat a + 256 ^ a.length * Spec.leNat b := by
  induction a with
  | nil => simp [Spec.leNat]
  | cons c a ih =>
    simp only [Spec.leNat, List.cons_append, List.foldr_cons, List.length_cons] at *
    rw [ih, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_comm (256 ^ a.length) 256, Nat.mul_assoc]

/-- The little-endian value of the four bytes of a word is the word. -/
theorem leNat_wordBytes (w : Word) : Spec.leNat (wordBytes w) = w.toNat := by
  simp only [wordBytes, Spec.leNat, List.foldr_cons, List.foldr_nil, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- **Integerify for r = 1.** Integerify of a model state, modulo 1024, is word `X[16]` modulo 1024. -/
theorem integerify_toModel (x : State) : Spec.integerify 1 (toModel x) % 1024 = x.2[0].toNat % 1024 := by
  simp only [Spec.integerify, show 2 * 1 - 1 = 1 from rfl, blk_toModel_one, serialize_eq]
  have hl : (bv x.2).toList = (bv x.2).toList[0]'(by simp) :: (bv x.2).toList.drop 1 := by
    rw [List.getElem_cons_drop]; rfl
  rw [hl, List.flatMap_cons, leNat_append, leNat_wordBytes]
  simp only [Vector.getElem_toList, bv, Vector.getElem_map, UInt32.toNat_toBitVec,
    show (wordBytes _).length = 4 from rfl]
  omega

/-! ## The second loop -/

/-- Wordwise XOR of two states. -/
def xorState (x y : State) : State := (Vector.zipWith (· ^^^ ·) x.1 y.1, Vector.zipWith (· ^^^ ·) x.2 y.2)

/-- Bit-vector reading commutes with wordwise XOR. -/
theorem bv_xor (a b : Vector UInt32 16) : bv (Vector.zipWith (· ^^^ ·) a b) = xorWords (bv a) (bv b) := by
  ext i hi
  simp [bv, xorWords]

/-- For all states, bytewise XOR of their model bytes is the model bytes of their XOR. -/
theorem xorBytes_toModel (x y : State) :
    Pbkdf2.Spec.xorBytes (toModel x) (toModel y) = toModel (xorState x y) := by
  simp only [toModel, xorState, Pbkdf2.Spec.xorBytes, bv_xor]
  rw [List.zipWith_append (by simp [serialize_length]), ← xorBytes_serialize, ← xorBytes_serialize]
  rfl

/-- One iteration of the model's step 3, first component. -/
theorem mixLoop_succ_fst (v : List (List (BitVec 8))) (n : Nat) (x : List (BitVec 8)) :
    (Spec.mixLoop 1 1024 v (n + 1) x).1 =
      (Spec.mixLoop 1 1024 v n
        (Spec.blockMix 1 (Pbkdf2.Spec.xorBytes x (v.getD (Spec.integerify 1 x % 1024) [])))).1 := by
  simp only [Spec.mixLoop]

/-- The executable second loop over the flat scratchpad equals the model's step 3 over the stored blocks.
This holds for 1024 stored states, every count and every state.
Every `!` read is in bounds, by `flat_getElem!_lo` and `flat_getElem!_hi`. -/
theorem mix_toModel (w : List State) (hw : w.length = 1024) : ∀ (n : Nat) (x : State),
    toModel (mix (flat w) n x) = (Spec.mixLoop 1 1024 (w.map toModel) n (toModel x)).1
  | 0, x => rfl
  | n + 1, x => by
    have hidx : x.2[0].toNat % 1024 < w.length := by rw [hw]; exact Nat.mod_lt _ (by decide)
    have hx : (Vector.ofFn fun k : Fin 16 =>
          x.1[k] ^^^ (flat w)[((32 : UInt32) * (x.2[0] &&& 1023)).toNat + k.val]!,
        Vector.ofFn fun k : Fin 16 =>
          x.2[k] ^^^ (flat w)[((32 : UInt32) * (x.2[0] &&& 1023)).toNat + 16 + k.val]!) =
        xorState x w[x.2[0].toNat % 1024] := by
      simp only [index_eq, xorState]
      refine Prod.ext ?_ ?_ <;> ext k hk
      · simp [flat_getElem!_lo w _ k hidx hk]
      · simp [flat_getElem!_hi w _ k hidx hk]
    rw [mixLoop_succ_fst, integerify_toModel, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hidx, Option.map_some, Option.getD_some, xorBytes_toModel,
      ← blockMix_toModel, ← mix_toModel w hw n, ← hx]
    rfl

/-! ## ROMix -/

/-- For every state, both executable loops equal the model's scryptROMix with `r = 1` and `N = 1024`.
The first loop reaches the model's reference fill through `fill_flat` and `fillLoop_eq`. -/
theorem roMix_toModel (x : State) : toModel (roMix x) = Spec.roMix 1 1024 (toModel x) := by
  have hf := fill_flat 1024 x []
  rw [fillLoop_eq] at hf
  simp only [List.nil_append] at hf
  have he : Array.emptyWithCapacity (α := UInt32) 32768 = flat [] := Array.emptyWithCapacity_eq
  unfold roMix
  rw [he, hf]
  show toModel (mix _ 1024 _) = _
  rw [mix_toModel _ (by rw [List.length_map, List.length_range]), List.map_map,
    repeat_blockMix_toModel]
  have hv : (toModel ∘ fun i => Nat.repeat blockMix i x) = fun i => Nat.repeat (Spec.blockMix 1) i (toModel x) :=
    funext fun i => repeat_blockMix_toModel i x
  rw [hv]
  rfl

/-! ## `le32dec` and `le32enc` -/

/-- Four bytes ORed into place, least significant first, are their concatenation, most significant first. -/
theorem bytes_toUInt32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toBitVec =
      b3.toBitVec ++ b2.toBitVec ++ b1.toBitVec ++ b0.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append]
  simp
  by_cases h8 : i < 8 <;> by_cases h16 : i < 16 <;> by_cases h24 : i < 24 <;>
    first
    | omega
    | simp (disch := omega) [h8, h16, h24, hi, BitVec.getLsbD_of_ge, show i - 8 < 8 ↔ i < 16 by omega,
        show i - 16 < 8 ↔ i < 24 by omega, Nat.sub_sub,
        show i - 8 < 32 by omega, show i - 16 < 32 by omega, show i - 24 < 32 by omega]

/-- `le32enc` writes the bytes of the word that `Spec.serialize` writes. -/
theorem le32enc_toBitVec (w : UInt32) : (le32enc w).map UInt8.toBitVec = wordBytes w.toBitVec := by
  simp only [le32enc, wordBytes, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> simp

/-- Byte `r < 4` of a concatenation of four bytes, most significant first, is the `r`th from the end. -/
theorem wordBytes_append (a3 a2 a1 a0 : BitVec 8) :
    wordBytes (a3 ++ a2 ++ a1 ++ a0) = [a0, a1, a2, a3] := by
  simp only [wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, show 16 + i - 8 = 8 + i by omega,
      show 24 + i - 8 = 16 + i by omega, show 8 + i - 8 = i by omega,
      show ¬ 8 + i < 8 by omega, show ¬ 16 + i < 8 by omega, show ¬ 24 + i < 8 by omega] <;>
    simp [hi]

/-- Words whose bytes are four consecutive bytes of `t`, least significant first, serialize to `t`. -/
theorem flatMap_wordBytes_eq (l : List Word) (t : List (BitVec 8)) (hl : t.length = 4 * l.length)
    (h : ∀ (i : Nat) (hi : i < l.length),
      l[i] = t[4 * i + 3]'(by omega) ++ t[4 * i + 2]'(by omega) ++ t[4 * i + 1]'(by omega) ++ t[4 * i]'(by omega)) :
    l.flatMap wordBytes = t := by
  apply List.ext_getElem?
  intro m
  by_cases hm : m < t.length
  · have hj : m / 4 < l.length := by omega
    have hr : m % 4 < 4 := Nat.mod_lt _ (by decide)
    have e := getElem?_flatMap_chunk wordBytes 4 (fun _ => rfl) l (m / 4) (m % 4) hj hr
    rw [Nat.div_add_mod] at e
    rw [e, h _ hj, wordBytes_append, List.getElem?_eq_getElem hm]
    have : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases this with h0 | h0 | h0 | h0 <;> simp only [h0] <;> simp <;> congr 1 <;> omega
  · have := length_flatMap_const l (f := wordBytes) (n := 4) (fun _ => rfl)
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Bit-vector reading of a byte array, at every index in range. -/
theorem toBytes_getElem (b : ByteArray) (i : Nat) (hi : i < (toBytes b).length) :
    (toBytes b)[i] = (b[i]'(by simpa using hi)).toBitVec := by
  simp [Hmac.Spec.toBytes]
  rfl

/-- **Representation.** For 128 bytes, the model bytes of the decoded state are the bytes. -/
theorem decode_toModel (b : ByteArray) (hb : b.size = 128) : toModel (decode b) = toBytes b := by
  simp only [toModel, serialize_eq, ← List.flatMap_append]
  refine flatMap_wordBytes_eq _ _ (by simp [hb]) ?_
  · intro i hi
    have hi : i < 32 := by simpa using hi
    have hb' : ∀ k (hk : k < 128), b[k]! = b[k]'(by omega) := fun k hk => getElem!_pos b k (by omega)
    simp only [toBytes_getElem]
    by_cases h16 : i < 16
    · rw [List.getElem_append_left (by simpa using h16)]
      simp only [decode, bv, Vector.getElem_toList, Vector.getElem_map, Vector.getElem_ofFn, le32dec,
        bytes_toUInt32, hb' _ (show 4 * i < 128 by omega), hb' _ (show 4 * i + 1 < 128 by omega),
        hb' _ (show 4 * i + 2 < 128 by omega), hb' _ (show 4 * i + 3 < 128 by omega)]
    · rw [List.getElem_append_right (by simpa using h16)]
      simp only [decode, bv, Vector.getElem_toList, Vector.getElem_map, Vector.getElem_ofFn, le32dec,
        bytes_toUInt32, Vector.length_toList]
      rw [hb' _ (by omega), hb' _ (by omega), hb' _ (by omega), hb' _ (by omega)]
      simp only [show 64 + 4 * (i - 16) = 4 * i by omega]

/-- **Representation.** The bytes that `le32enc` writes are the model bytes of the state. -/
theorem encode_toBytes (x : State) : toBytes (encode x) = toModel x := by
  simp only [encode, Hmac.Spec.toBytes, toModel, serialize_eq, bv]
  simp [List.map_flatMap, le32enc_toBitVec, Vector.toList_map, List.flatMap_map, List.flatMap_append]

/-! ## PBKDF2 and the digest -/

/-- With one iteration, the first `k` PBKDF2 blocks have `32 * k` bytes. -/
theorem blocks_size (pw s : ByteArray) : ∀ k, (Pbkdf2.blocks pw s 1 k).size = 32 * k
  | 0 => by simp [Pbkdf2.blocks]
  | k + 1 => by
    have ih := blocks_size pw s k
    simp only [Pbkdf2.blocks, Nat.fold_succ, ByteArray.size_append] at *
    rw [ih]
    simp [Pbkdf2.block, Pbkdf2.iterate, Hmac.hmac_size, Nat.mul_succ]

/-- With one iteration, PBKDF2 returns `some` of exactly `n` bytes for every admitted length `n`. -/
theorem pbkdf2_some (pw s : ByteArray) (n : Nat) (hn : n ≤ (2 ^ 32 - 1) * 32) :
    ∃ b, Pbkdf2.pbkdf2 pw s 1 n = some b ∧ b.size = n := by
  refine ⟨(Pbkdf2.blocks pw s 1 ((n + 32 - 1) / 32)).extract 0 n, by simp only [Pbkdf2.pbkdf2, show ¬ ((2 ^ 32 - 1) * 32 < n) by omega, ↓reduceIte], ?_⟩
  rw [ByteArray.size_extract, blocks_size]
  omega

/-- For an array of exactly `n` bytes, `prefixBytes` returns all of them. -/
theorem prefixBytes_val (b : ByteArray) (n : Nat) (hb : b.size = n) : (prefixBytes b n).val = b.data.toList := by
  apply List.ext_getElem (by rw [prefixBytes, List.length_ofFn, Array.length_toList]; exact hb.symm)
  intro i h1 h2
  simp only [prefixBytes, List.getElem_ofFn, Array.getElem_toList]
  rw [Array.length_toList] at h2
  rw [getElem!_pos b i h2]
  rfl

/-- `le32enc` writes 128 bytes. -/
theorem encode_size (x : State) : (encode x).size = 128 := by
  have h := congrArg List.length (encode_toBytes x)
  rwa [Hmac.toBytes_length, toModel_length] at h

/-- For 128 bytes, encoding the result of both loops on the decoded state is scryptROMix of the bytes. -/
theorem roMix_bytes (b : ByteArray) (hb : b.size = 128) :
    toBytes (encode (roMix (decode b))) = Spec.roMix 1 1024 (toBytes b) := by
  rw [encode_toBytes, roMix_toModel, decode_toModel b hb]

/-- The executable as its three stages: PBKDF2 to 128 bytes, both loops, and PBKDF2 to 32 bytes,
each stage over byte arrays. -/
theorem scrypt_1024_1_1_256_eq (input : Bytes 80) :
    ∃ b d, Pbkdf2.pbkdf2 input.val.toByteArray input.val.toByteArray 1 128 = some b ∧ b.size = 128 ∧
      Pbkdf2.pbkdf2 input.val.toByteArray (encode (roMix (decode b))) 1 32 = some d ∧
      (scrypt_1024_1_1_256 input).val.map UInt8.toBitVec = toBytes d := by
  obtain ⟨b, hb, hbs⟩ := pbkdf2_some input.val.toByteArray input.val.toByteArray 128 (by decide)
  obtain ⟨d, hd, hds⟩ := pbkdf2_some input.val.toByteArray (encode (roMix (decode b))) 32 (by decide)
  refine ⟨b, d, hb, hbs, hd, ?_⟩
  simp only [scrypt_1024_1_1_256, hb, hd, Option.getD_some, prefixBytes_val d 32 hds]
  rfl

/-- The 80 input bytes, as the model's password and salt. -/
theorem toBytes_input (input : Bytes 80) :
    toBytes input.val.toByteArray = input.val.map UInt8.toBitVec := by
  simp [Hmac.Spec.toBytes]

/--
**`powHash_eq_spec`.** For every 80-byte input, Dogecoin's scrypt executable equals the RFC 7914 model.
The model runs with N = 1024, r = 1, p = 1 and 32 output bytes, and the input is both password and salt.
The executable follows Core's `scrypt_1024_1_1_256_sp_generic`: its word order, its statement order in
`xor_salsa8`, its index `32 * (X[16] & 1023)` and its flat scratchpad.

The model's HMAC uses DogeLib's executable SHA-256. `powHash_eq_fips` uses the FIPS 180-4 model.
The input type admits no other length.
-/
theorem powHash_eq_spec (input : Bytes 80) :
    Spec.scrypt (input.val.map UInt8.toBitVec) (input.val.map UInt8.toBitVec) 1024 1 1 32 =
      some ((scrypt_1024_1_1_256 input).val.map UInt8.toBitVec) := by
  obtain ⟨b, d, hb, hbs, hd, hout⟩ := scrypt_1024_1_1_256_eq input
  have e1 := Pbkdf2.pbkdf2_eq_spec input.val.toByteArray input.val.toByteArray 1 128
  have e2 := Pbkdf2.pbkdf2_eq_spec input.val.toByteArray (encode (roMix (decode b))) 1 32
  rw [hb, Option.map_some, toBytes_input] at e1
  rw [hd, Option.map_some, toBytes_input, roMix_bytes b hbs] at e2
  rw [hout, Spec.scrypt]
  simp only [show Spec.valid 1024 1 1 32 by decide, ↓reduceIte, show 1 * 128 * 1 = 128 from rfl, ← e1]
  have hlen : (toBytes b).take 128 = toBytes b := List.take_of_length_le (by simp [hbs])
  simp only [Option.bind_eq_bind, Option.bind_some, List.range_one, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.mul_zero, List.drop_zero, hlen, ← e2]

/--
**`powHash_eq_fips`.** For every 80-byte input `P`, the executable digest equals RFC 7914 scrypt as three steps.
The steps are `B = PBKDF2(P, P, 1, 128)`, then `PBKDF2(P, scryptROMix(1, B, 1024), 1, 32)`.
Both PBKDF2 steps use HMAC over the FIPS 180-4 SHA-256 model.
`Spec.scrypt` runs exactly these steps with N = 1024, r = 1, p = 1 and 32 output bytes.
-/
theorem powHash_eq_fips (input : Bytes 80) :
    (Pbkdf2.Spec.pbkdf2 (Hmac.Spec.hmac Hmac.Spec.fipsSha256 (input.val.map UInt8.toBitVec)) 32
        (input.val.map UInt8.toBitVec) 1 128).bind
      (fun b => Pbkdf2.Spec.pbkdf2 (Hmac.Spec.hmac Hmac.Spec.fipsSha256 (input.val.map UInt8.toBitVec)) 32
        (Spec.roMix 1 1024 b) 1 32) =
      some ((scrypt_1024_1_1_256 input).val.map UInt8.toBitVec) := by
  obtain ⟨b, d, hb, hbs, hd, hout⟩ := scrypt_1024_1_1_256_eq input
  have hsize : input.val.toByteArray.size = 80 := by simp [input.property]
  have e1 := Pbkdf2.pbkdf2_eq_fips input.val.toByteArray input.val.toByteArray 1 128
    (by rw [hsize]; decide) (by rw [hsize]; decide)
  have e2 := Pbkdf2.pbkdf2_eq_fips input.val.toByteArray (encode (roMix (decode b))) 1 32
    (by rw [hsize]; decide) (by rw [encode_size]; decide)
  rw [hb, Option.map_some, toBytes_input] at e1
  rw [hd, Option.map_some, toBytes_input, roMix_bytes b hbs] at e2
  rw [hout, ← e1, Option.bind_some, ← e2]

end DogeLib.Cryptography.Hash.Scrypt
