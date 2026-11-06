module

public import DogeLib.Block.AuxPowCheck
public import DogeLib.Serialization.Proofs.Codec

/-!
# Properties of the AuxPoW check

The theorems characterize `getExpectedIndex`, `checkMerkleBranch`, the script search and `AuxPow.check` (design record 0004, section 8).

- `getExpectedIndex_eq`: the closed form over natural numbers, for `h < 32`.
- `getExpectedIndex_lt`: the result is below `2 ^ h`, for `h < 32`.
- `getExpectedIndex_mod64`: the same steps modulo 2^64 give the same result, for `h ≤ 32`.
- `checkMerkleBranch_neg_one` and `checkMerkleBranch_eq_fold`: the zero hash for index −1, and otherwise a left fold that takes the side from the index bits.
- `findSubseq?_eq_some_iff` and `findSubseq?_eq_none_iff`: the search returns the first occurrence.
- `searchChainRoot_eq_ok_iff`: the conditions on the first occurrences of the marker and the root, and the two words after the root.
- `AuxPow.check_eq_ok_iff`: `check` accepts exactly when each of its tests passes.
- `AuxPow.check_ok_binding`: what an accepted payload says about the hashes and the script bytes.
- `AuxPow.check_ok_chainIndex_lt`: an accepted `nChainIndex` is not negative and is below `2 ^ h`.

The theorems state equalities of computed hashes.
None of them says that a different header or transaction cannot give the same hashes.
That claim needs collision resistance of double SHA-256, which DogeLib does not model.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Serialization

/-! ## `getExpectedIndex` -/

/-- A chain ID converted to `uint32_t` is the chain ID modulo 2^32. -/
theorem Int32.toNat_toUInt32_eq_emod (c : Int32) : c.toUInt32.toNat = (c.toInt % 2 ^ 32).toNat := by
  have h1 : c.toInt = Int.bmod c.toBitVec.toNat (2 ^ 32) := BitVec.toInt_eq_toNat_bmod _
  have h2 : c.toBitVec.toNat < 2 ^ 32 := c.toBitVec.isLt
  rw [h1, show ((2 : Int) ^ 32) = ((2 ^ 32 : Nat) : Int) by norm_cast, Int.bmod_emod]
  have : ((c.toBitVec.toNat : Int) % ((2 ^ 32 : Nat) : Int)) = c.toBitVec.toNat :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [this]; rfl

/-- For `h < 32`, `1 <<< h` in `UInt32` is `2 ^ h`. -/
theorem UInt32.one_shiftLeft_toNat (h : Nat) (hh : h < 32) : ((1 : UInt32) <<< h.toUInt32).toNat = 2 ^ h := by
  simp [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hh, Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by decide) hh

/--
For every nonce and chain ID, and every `h < 32`, `getExpectedIndex` equals a closed form over natural numbers.
The form takes two steps of the linear congruential generator modulo 2^32, and adds the chain ID modulo 2^32 between them.
The result is the remainder of that value modulo `2 ^ h`.
-/
theorem getExpectedIndex_eq (nonce : UInt32) (chainId : Int32) (h : Nat) (hh : h < 32) :
    (getExpectedIndex nonce chainId h).toNat =
      ((((nonce.toNat * 1103515245 + 12345) % 2 ^ 32 + (chainId.toInt % 2 ^ 32).toNat) % 2 ^ 32
        * 1103515245 + 12345) % 2 ^ 32) % 2 ^ h := by
  simp only [getExpectedIndex, UInt32.toNat_mod, UInt32.one_shiftLeft_toNat h hh, UInt32.toNat_add,
    UInt32.toNat_mul, Int32.toNat_toUInt32_eq_emod]
  have a : UInt32.toNat 1103515245 = 1103515245 := rfl
  have b : UInt32.toNat 12345 = 12345 := rfl
  rw [a, b]
  apply congrArg (· % 2 ^ h)
  generalize nonce.toNat = N
  generalize chainId.toInt = C
  omega

/-- For every nonce and chain ID, and every `h < 32`, `getExpectedIndex` is below `2 ^ h`. `check` calls it only with `h ≤ 30`. -/
theorem getExpectedIndex_lt (nonce : UInt32) (chainId : Int32) (h : Nat) (hh : h < 32) :
    (getExpectedIndex nonce chainId h).toNat < 2 ^ h := by
  rw [getExpectedIndex_eq nonce chainId h hh]
  exact Nat.mod_lt _ (Nat.two_pow_pos h)

/--
For every nonce and chain ID, and every `h ≤ 32`, the steps of `getExpectedIndex_eq` modulo 2^64 give the same remainder modulo `2 ^ h`.
That computation takes the chain ID modulo 2^64.
The theorem proves the claim of Core's comment that a 64-bit computation agrees (D55, lines 173 to 179).
-/
theorem getExpectedIndex_mod64 (nonce : UInt32) (chainId : Int32) (h : Nat) (hh : h ≤ 32) :
    ((((nonce.toNat * 1103515245 + 12345) % 2 ^ 64 + (chainId.toInt % 2 ^ 64).toNat) % 2 ^ 64
        * 1103515245 + 12345) % 2 ^ 64) % 2 ^ h =
      ((((nonce.toNat * 1103515245 + 12345) % 2 ^ 32 + (chainId.toInt % 2 ^ 32).toNat) % 2 ^ 32
        * 1103515245 + 12345) % 2 ^ 32) % 2 ^ h := by
  have hd : 2 ^ h ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hh
  have key : ((((nonce.toNat * 1103515245 + 12345) % 2 ^ 64 + (chainId.toInt % 2 ^ 64).toNat) % 2 ^ 64
        * 1103515245 + 12345) % 2 ^ 64) % 2 ^ 32 =
      ((((nonce.toNat * 1103515245 + 12345) % 2 ^ 32 + (chainId.toInt % 2 ^ 32).toNat) % 2 ^ 32
        * 1103515245 + 12345) % 2 ^ 32) := by
    generalize nonce.toNat = N
    generalize chainId.toInt = C
    omega
  rw [← Nat.mod_mod_of_dvd _ hd, key]

/-! ## `checkMerkleBranch` -/

/-- The low-bit test of `checkMerkleBranch` reads bit 0 of the index. -/
theorem Int32.and_one_ne_zero (x : Int32) : (x &&& 1 != 0) = x.toBitVec.getLsbD 0 := by
  have h1 : (x &&& 1 != 0) = decide ((x.toBitVec &&& 1#32).toNat ≠ 0) := by
    rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    rw [← Int32.toBitVec_inj, BitVec.toNat_eq]; rfl
  rw [h1, BitVec.toNat_and, BitVec.getLsbD, Nat.testBit_zero]
  have : (1#32).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one x.toBitVec.toNat with h | h <;> simp [h]

/--
The side bit of step `k` of `checkMerkleBranch`: bit `k` of the index, or its sign bit (bit 31) for `k ≥ 31`.
The arithmetic shift copies the sign bit, so after 31 shifts every step reads the sign bit.
-/
def branchBit (index : Int32) (k : Nat) : Bool := index.toBitVec.getLsbD (min k 31)

/-- The fold of `checkMerkleBranch` over the branch hashes and their step numbers, from step `k`. -/
def branchFold (index : Int32) (hash : Hash256) (branch : List Hash256) (k : Nat) : Hash256 :=
  (branch.zipIdx k).foldl
    (fun acc p => if branchBit index p.2 then merklePair p.1 acc else merklePair acc p.1) hash

private theorem bit_sshiftRight (index : Int32) (k : Nat) :
    (Int32.ofBitVec (index.toBitVec.sshiftRight k)).toBitVec.getLsbD 0 = branchBit index k := by
  simp only [Int32.toBitVec_ofBitVec, BitVec.getLsbD_sshiftRight, branchBit]
  by_cases hk : k < 32
  · simp [hk, Nat.min_eq_left (by omega : k ≤ 31)]
  · simp [hk, Nat.min_eq_right (by omega : 31 ≤ k), BitVec.msb_eq_getLsbD_last]

private theorem shiftRight_one (x : Int32) : (x >>> 1).toBitVec = x.toBitVec.sshiftRight 1 := by
  simp only [Int32.toBitVec_shiftRight, BitVec.sshiftRight_eq']
  rfl

private theorem go_eq_branchFold (index : Int32) (acc : Hash256) (bs : List Hash256) (k : Nat) :
    checkMerkleBranch.go acc bs (Int32.ofBitVec (index.toBitVec.sshiftRight k)) = branchFold index acc bs k := by
  induction bs generalizing acc k with
  | nil => rfl
  | cons b bs ih =>
    simp only [checkMerkleBranch.go, branchFold, List.zipIdx_cons, List.foldl_cons, Int32.and_one_ne_zero,
      bit_sshiftRight]
    have : Int32.ofBitVec (index.toBitVec.sshiftRight k) >>> 1 =
        Int32.ofBitVec (index.toBitVec.sshiftRight (k + 1)) := by
      apply Int32.toBitVec_inj.mp
      rw [shiftRight_one, Int32.toBitVec_ofBitVec, Int32.toBitVec_ofBitVec, BitVec.sshiftRight_add]
    rw [this, ih]
    rfl

/-- For every hash and branch, index −1 gives the zero hash (D55, lines 194 to 195). -/
theorem checkMerkleBranch_neg_one (hash : Hash256) (branch : List Hash256) :
    checkMerkleBranch hash branch (-1) = Hash256.zero := by
  simp [checkMerkleBranch]

/--
For every hash, branch and index other than −1, `checkMerkleBranch` is a left fold over the branch.
At step `k`, the branch hash goes on the left exactly when `branchBit index k` is set, and the running hash goes on the left otherwise.
-/
theorem checkMerkleBranch_eq_fold (hash : Hash256) (branch : List Hash256) (index : Int32) (hi : index ≠ -1) :
    checkMerkleBranch hash branch index = branchFold index hash branch 0 := by
  have : index = Int32.ofBitVec (index.toBitVec.sshiftRight 0) := by
    apply Int32.toBitVec_inj.mp; simp
  simp only [checkMerkleBranch, hi, ite_false]
  conv => lhs; rw [this]
  exact go_eq_branchFold index hash branch 0

/-- For every hash and branch, index zero keeps the running hash on the left at every step: the coinbase branch of `check` (D55, line 100). -/
theorem checkMerkleBranch_zero (hash : Hash256) (branch : List Hash256) :
    checkMerkleBranch hash branch 0 = branch.foldl merklePair hash := by
  rw [checkMerkleBranch_eq_fold _ _ _ (by decide)]
  unfold branchFold
  have hf : (fun (acc : Hash256) (p : Hash256 × Nat) =>
      if branchBit 0 p.2 then merklePair p.1 acc else merklePair acc p.1) =
      fun acc p => merklePair acc p.1 := by
    funext acc p; simp [branchBit]
  rw [hf]
  generalize 0 = k
  induction branch generalizing hash k with
  | nil => rfl
  | cons b bs ih => simp only [List.zipIdx_cons, List.foldl_cons]; exact ih _ _

/-! ## The search -/

private theorem findSubseq?_go_eq_some_iff (needle rest : List UInt8) (k i : Nat) :
    findSubseq?.go needle rest k = some i ↔
      ∃ d, i = k + d ∧ needle <+: rest.drop d ∧ ∀ e < d, ¬ needle <+: rest.drop e := by
  induction rest generalizing k with
  | nil =>
    by_cases hp : needle <+: []
    · simp only [findSubseq?.go, List.isPrefixOf_iff_prefix.mpr hp, ite_true, Option.some.injEq]
      constructor
      · intro h; exact ⟨0, by omega, by simpa using hp, by intro e he; omega⟩
      · rintro ⟨d, rfl, -, hmin⟩
        cases d with
        | zero => rfl
        | succ d => exact absurd (by simpa using hp) (hmin 0 (by omega))
    · have hb : needle.isPrefixOf [] = false := by
        rw [Bool.eq_false_iff]; intro h; exact hp (List.isPrefixOf_iff_prefix.mp h)
      simp only [findSubseq?.go, hb, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
      rintro ⟨d, -, hd, -⟩
      exact hp (by simpa using hd)
  | cons b r ih =>
    by_cases hp : needle <+: b :: r
    · simp only [findSubseq?.go, List.isPrefixOf_iff_prefix.mpr hp, ite_true, Option.some.injEq]
      constructor
      · intro h; exact ⟨0, by omega, by simpa using hp, by intro e he; omega⟩
      · rintro ⟨d, rfl, -, hmin⟩
        cases d with
        | zero => rfl
        | succ d => exact absurd (by simpa using hp) (hmin 0 (by omega))
    · have hb : needle.isPrefixOf (b :: r) = false := by
        rw [Bool.eq_false_iff]; intro h; exact hp (List.isPrefixOf_iff_prefix.mp h)
      simp only [findSubseq?.go, hb, Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · rintro ⟨d, rfl, hd, hmin⟩
        refine ⟨d + 1, by omega, by simpa using hd, ?_⟩
        intro e he
        cases e with
        | zero => simpa using hp
        | succ e => simpa using hmin e (by omega)
      · rintro ⟨d, rfl, hd, hmin⟩
        cases d with
        | zero => exact absurd (by simpa using hd) hp
        | succ d =>
          refine ⟨d, by omega, by simpa using hd, ?_⟩
          intro e he
          simpa using hmin (e + 1) (by omega)

/-- For all needles and inputs, the search returns `i` exactly when the needle occurs at offset `i` and at no smaller offset. -/
theorem findSubseq?_eq_some_iff (needle hay : List UInt8) (i : Nat) :
    findSubseq? needle hay = some i ↔ needle <+: hay.drop i ∧ ∀ j < i, ¬ needle <+: hay.drop j := by
  rw [findSubseq?, findSubseq?_go_eq_some_iff]
  constructor
  · rintro ⟨d, rfl, hd, hmin⟩; exact ⟨by simpa using hd, by simpa using hmin⟩
  · rintro ⟨hd, hmin⟩; exact ⟨i, by omega, hd, hmin⟩

private theorem findSubseq?_go_eq_none_iff (needle rest : List UInt8) (k : Nat) :
    findSubseq?.go needle rest k = none ↔ ∀ d, ¬ needle <+: rest.drop d := by
  induction rest generalizing k with
  | nil =>
    by_cases hp : needle <+: []
    · simp only [findSubseq?.go, List.isPrefixOf_iff_prefix.mpr hp, ite_true, reduceCtorEq, false_iff]
      intro h; exact h 0 hp
    · have hb : needle.isPrefixOf [] = false := by
        rw [Bool.eq_false_iff]; intro h; exact hp (List.isPrefixOf_iff_prefix.mp h)
      simp only [findSubseq?.go, hb, Bool.false_eq_true, ite_false, true_iff]
      intro d; simpa using hp
  | cons b r ih =>
    by_cases hp : needle <+: b :: r
    · simp only [findSubseq?.go, List.isPrefixOf_iff_prefix.mpr hp, ite_true, reduceCtorEq, false_iff]
      intro h; exact h 0 hp
    · have hb : needle.isPrefixOf (b :: r) = false := by
        rw [Bool.eq_false_iff]; intro h; exact hp (List.isPrefixOf_iff_prefix.mp h)
      simp only [findSubseq?.go, hb, Bool.false_eq_true, ite_false]
      rw [ih]
      constructor
      · intro h d
        cases d with
        | zero => simpa using hp
        | succ d => simpa using h d
      · intro h d; simpa using h (d + 1)

/-- For all needles and inputs, the search returns `none` exactly when the needle occurs at no offset. -/
theorem findSubseq?_eq_none_iff (needle hay : List UInt8) :
    findSubseq? needle hay = none ↔ ∀ j, ¬ needle <+: hay.drop j := by
  rw [findSubseq?, findSubseq?_go_eq_none_iff]

/--
The marker condition of `searchChainRoot` for a first root occurrence at `pc` (D55, lines 122 to 138).
If the marker occurs first at `head`, it occurs nowhere in the script after its first byte, and `pc = head + 4`.
If the marker does not occur, `pc ≤ 20`.
-/
def MarkerCondition (script : List UInt8) (pc : Nat) : Prop :=
  match findSubseq? mergedMiningMarker script with
  | some head => findSubseq? mergedMiningMarker (script.drop (head + 1)) = none ∧ pc = head + 4
  | none => pc ≤ 20

/--
For every script and root, `searchChainRoot` returns the words `size` and `nonce` exactly when these hold:

- The first occurrence of `root` in the script is at offset `pc`.
- `MarkerCondition script pc` holds.
- The bytes after that occurrence start with the little-endian encodings of `size` and then `nonce`.
-/
theorem searchChainRoot_eq_ok_iff (script root : List UInt8) (size nonce : UInt32) :
    searchChainRoot script root = .ok (size, nonce) ↔
      ∃ pc, findSubseq? root script = some pc ∧ MarkerCondition script pc ∧
        ∃ rest, script.drop (pc + root.length) = Codec.encode size ++ Codec.encode nonce ++ rest := by
  unfold searchChainRoot MarkerCondition
  cases hr : findSubseq? root script with
  | none => simp
  | some pc =>
    simp only [Option.some.injEq, exists_eq_left']
    cases hm : findSubseq? mergedMiningMarker script with
    | none =>
      by_cases h20 : pc > 20
      · simp only [h20, ite_true, reduceCtorEq, false_iff, not_and]; intro h; omega
      · simp only [h20, ite_false, Nat.le_of_not_gt h20, true_and]
        exact decodeWords_iff _ size nonce
    | some head =>
      by_cases h2 : (findSubseq? mergedMiningMarker (script.drop (head + 1))).isSome
      · simp only [h2, ite_true, reduceCtorEq, false_iff, not_and]
        intro h; simp [h] at h2
      · have h2' : findSubseq? mergedMiningMarker (script.drop (head + 1)) = none := by
          simpa using h2
        simp only [h2', Option.isSome_none, Bool.false_eq_true, ite_false, true_and]
        have hl : mergedMiningMarker.length = 4 := rfl
        rw [hl]
        by_cases hp : pc = head + 4
        · subst hp
          simp only [ne_eq, not_true_eq_false, ite_false, true_and]
          exact decodeWords_iff _ size nonce
        · have hp' : head + 4 ≠ pc := fun h => hp h.symm
          simp only [hp', ne_eq, not_false_eq_true, ite_true, reduceCtorEq, hp, false_and]
where
  decodeWords_iff (bs : List UInt8) (size nonce : UInt32) :
      (match Codec.decode (α := UInt32 × UInt32) bs with
        | none => (Except.error .missingSizeAndNonce : Except AuxPowCheckError (UInt32 × UInt32))
        | some (words, _) => .ok words) = .ok (size, nonce) ↔
      ∃ rest, bs = Codec.encode size ++ Codec.encode nonce ++ rest := by
    constructor
    · intro h
      cases hd : Codec.decode (α := UInt32 × UInt32) bs with
      | none => simp [hd] at h
      | some p =>
        obtain ⟨words, rest⟩ := p
        simp only [hd, Except.ok.injEq] at h
        subst h
        exact ⟨rest, by rw [LawfulCodec.decode_canonical bs _ rest hd]; simp [Codec.encode]⟩
    · rintro ⟨rest, rfl⟩
      have : Codec.encode size ++ Codec.encode nonce ++ rest = Codec.encode (size, nonce) ++ rest := by
        simp [Codec.encode]
      rw [this, LawfulCodec.decode_encode]

/-! ## `check` -/

/--
For every payload, block hash, chain ID and value of `fStrictChainId`, `check` accepts exactly when each of its tests passes.
`h` is the length of the chain branch.

- `nIndex` is zero.
- With `strictChainId`, the parent's chain ID is not `chainId`.
- The chain branch has at most 30 hashes.
- The coinbase branch at index zero leads from the transaction ID to the parent's `hashMerkleRoot`.
- The transaction has a first input, and `searchChainRoot` returns `size` and `nonce` for its script and the chain root in display order.
- `size` is `2 ^ h`, and `nChainIndex` is `getExpectedIndex nonce chainId h`.
-/
theorem AuxPow.check_eq_ok_iff (a : AuxPow) (hashAuxBlock : Hash256) (chainId : Int32) (strictChainId : Bool) :
    a.check hashAuxBlock chainId strictChainId = .ok () ↔
      a.index = 0 ∧ (strictChainId = true → a.parentBlock.chainId ≠ chainId) ∧
      a.chainMerkleBranch.val.length ≤ 30 ∧
      checkMerkleBranch a.tx.tx.txid a.merkleBranch.val 0 = a.parentBlock.hashMerkleRoot ∧
      ∃ input inputs size nonce, a.tx.tx.inputs.val = input :: inputs ∧
        searchChainRoot input.scriptSig.bytes.val
          (checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex).displayBytes = .ok (size, nonce) ∧
        size = (1 : UInt32) <<< a.chainMerkleBranch.val.length.toUInt32 ∧
        a.chainIndex = getExpectedIndex nonce chainId a.chainMerkleBranch.val.length := by
  unfold AuxPow.check
  by_cases h1' : a.index ≠ 0
  · rw [ite_eq_left h1']; simp only [reduceCtorEq, false_iff, not_and]; intro h; exact absurd h h1'
  rw [ite_eq_right h1']
  have h1 : a.index = 0 := Classical.not_not.mp h1'
  have hs : a.signedIndex = 0 := by simp [AuxPow.signedIndex, h1]
  rw [hs]
  simp only [h1, true_and]
  by_cases h2 : (strictChainId && a.parentBlock.chainId == chainId) = true
  · rw [ite_eq_left h2]; simp only [reduceCtorEq, false_iff, not_and]
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    intro h; exact absurd h2.2 (h h2.1)
  rw [ite_eq_right h2]
  have h2' : strictChainId = true → a.parentBlock.chainId ≠ chainId := by
    intro hs he; simp [hs, he] at h2
  rw [and_iff_right h2']
  by_cases h3 : a.chainMerkleBranch.val.length > 30
  · rw [ite_eq_left h3]; simp only [reduceCtorEq, false_iff, not_and]; intro h; omega
  rw [ite_eq_right h3]
  simp only [Nat.le_of_not_gt h3, true_and]
  by_cases h4' : checkMerkleBranch a.tx.tx.txid a.merkleBranch.val 0 ≠ a.parentBlock.hashMerkleRoot
  · rw [ite_eq_left h4']; simp only [reduceCtorEq, false_iff, not_and]; intro h; exact absurd h h4'
  rw [ite_eq_right h4']
  have h4 := Classical.not_not.mp h4'
  simp only [h4, true_and]
  cases hin : a.tx.tx.inputs.val with
  | nil => simp
  | cons input inputs =>
    simp only [List.cons.injEq]
    cases hsr : searchChainRoot input.scriptSig.bytes.val
        (checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex).displayBytes with
    | error e =>
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro i is s n ⟨hi, _⟩ h; subst hi; rw [hsr] at h; cases h
    | ok words =>
      obtain ⟨size, nonce⟩ := words
      constructor
      · intro h
        dsimp only at h
        by_cases h7' : size ≠ (1 : UInt32) <<< a.chainMerkleBranch.val.length.toUInt32
        · rw [ite_eq_left h7'] at h; simp at h
        rw [ite_eq_right h7'] at h
        by_cases h8' : a.chainIndex ≠ getExpectedIndex nonce chainId a.chainMerkleBranch.val.length
        · rw [ite_eq_left h8'] at h; simp at h
        have h7 := Classical.not_not.mp h7'
        have h8 := Classical.not_not.mp h8'
        exact ⟨input, inputs, size, nonce, ⟨rfl, rfl⟩, hsr, h7, h8⟩
      · rintro ⟨i, is, s, n, ⟨rfl, rfl⟩, hs', h7, h8⟩
        rw [hsr] at hs'
        simp only [Except.ok.injEq, Prod.mk.injEq] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        dsimp only
        rw [ite_eq_right (Classical.not_not.mpr h7), ite_eq_right (Classical.not_not.mpr h8)]

/--
What an accepted payload says, for every payload, block hash, chain ID and value of `fStrictChainId`.
`h` is the length of the chain branch, and `root` is the chain root `checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex`.

- `nIndex` is zero, and the parent's `hashMerkleRoot` is the left fold of the transaction ID along the coinbase branch.
- The chain branch has at most 30 hashes.
- The first input's script contains `root` with its bytes reversed, first at an offset `pc` that satisfies `MarkerCondition`.
- The eight bytes after that occurrence encode `2 ^ h` and a nonce, little-endian, and `nChainIndex` is `getExpectedIndex` of that nonce, `chainId` and `h`.

The statement is about computed hashes only: it makes no claim that other inputs cannot give the same hashes.
-/
theorem AuxPow.check_ok_binding (a : AuxPow) (hashAuxBlock : Hash256) (chainId : Int32) (strictChainId : Bool)
    (hok : a.check hashAuxBlock chainId strictChainId = .ok ()) :
    a.index = 0 ∧ a.merkleBranch.val.foldl merklePair a.tx.tx.txid = a.parentBlock.hashMerkleRoot ∧
      a.chainMerkleBranch.val.length ≤ 30 ∧
      ∃ input inputs pc nonce rest, a.tx.tx.inputs.val = input :: inputs ∧
        findSubseq? (checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex).val.reverse
          input.scriptSig.bytes.val = some pc ∧
        MarkerCondition input.scriptSig.bytes.val pc ∧
        input.scriptSig.bytes.val.drop (pc + 32) =
          Codec.encode ((1 : UInt32) <<< a.chainMerkleBranch.val.length.toUInt32) ++ Codec.encode nonce ++ rest ∧
        a.chainIndex = getExpectedIndex nonce chainId a.chainMerkleBranch.val.length := by
  obtain ⟨h1, -, h3, h4, input, inputs, size, nonce, hin, hsr, rfl, h8⟩ :=
    (AuxPow.check_eq_ok_iff a hashAuxBlock chainId strictChainId).mp hok
  rw [checkMerkleBranch_zero] at h4
  obtain ⟨pc, hpc, hmc, rest, hrest⟩ := (searchChainRoot_eq_ok_iff _ _ _ _).mp hsr
  have hl := (checkMerkleBranch hashAuxBlock a.chainMerkleBranch.val a.signedChainIndex).property
  simp only [Hash256.displayBytes, List.length_reverse] at hpc hrest
  rw [hl] at hrest
  exact ⟨h1, h4, h3, input, inputs, pc, nonce, rest, hin, hpc, hmc, hrest, h8⟩

/--
For every accepted payload, `nChainIndex` is below `2 ^ h`, where `h ≤ 30` is the chain branch length.
So its signed value `nChainIndex` is not negative, and a negative `nChainIndex`, with its zero or shifted root, is always rejected.
-/
theorem AuxPow.check_ok_chainIndex_lt (a : AuxPow) (hashAuxBlock : Hash256) (chainId : Int32) (strictChainId : Bool)
    (hok : a.check hashAuxBlock chainId strictChainId = .ok ()) :
    a.chainIndex.toNat < 2 ^ a.chainMerkleBranch.val.length ∧ 0 ≤ a.signedChainIndex := by
  obtain ⟨-, -, h3, -, -, -, -, nonce, -, -, -, h8⟩ :=
    (AuxPow.check_eq_ok_iff a hashAuxBlock chainId strictChainId).mp hok
  have hlt : a.chainIndex.toNat < 2 ^ a.chainMerkleBranch.val.length := by
    rw [h8]; exact getExpectedIndex_lt _ _ _ (by omega)
  refine ⟨hlt, ?_⟩
  have h30 : 2 ^ a.chainMerkleBranch.val.length ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) h3
  have : a.chainIndex.toNat < 2 ^ 31 := by omega
  rw [AuxPow.signedChainIndex, Int32.le_iff_toInt_le]
  have e : a.chainIndex.toInt32.toInt = a.chainIndex.toBitVec.toInt := rfl
  have e2 : a.chainIndex.toBitVec.toNat = a.chainIndex.toNat := rfl
  rw [e, BitVec.toInt_eq_toNat_of_lt (by rw [e2]; omega)]
  simp

end DogeLib.Block
