module

public import DogeLib.Script.Signature

/-!
# Proofs: `Script.Signature`

## The checkers

- `baseChecker_checkSig`: Core's `BaseSignatureChecker` fails every signature check.
- `transactionChecker_invalidKey`: a public key that fails `isValidPubKey` gives `some false`, for every verifier.
- `transactionChecker_emptySig`: with a valid key, an empty signature gives `some false`, for every verifier.
- `transactionChecker_verify`: otherwise the result is exactly `verify` on the signature without its last byte, the key and `legacySignatureHash` with that byte zero-extended as the hash type.
- `transactionChecker_verify_congr`: two verifiers that agree on that one request give the same result.
- `baseChecker_checkLockTime`, `baseChecker_checkSequence`: `BaseSignatureChecker` fails every lock-time and sequence check.
- `transactionChecker_checkLockTime`, `transactionChecker_checkSequence`: for an input in range, the checks are `lockTimeSatisfied` and `sequenceSatisfied` on its sequence, for every verifier.
  `transactionChecker_checkLockTime_none`, `transactionChecker_checkSequence_none`: for an index outside the inputs, both give `none`.
- `lockTimeSatisfied_iff`, `sequenceSatisfied_iff`: the conditions of Core's `CheckLockTime` and `CheckSequence`, with the constants written out.

## The matching loop of `OP_CHECKMULTISIG`

`OrderedMatch R sigs keys` says that the signatures can be paired, in order, with a subsequence of the keys under `R`.
A subsequence keeps the order of the keys, so the matched key positions strictly increase.

- `greedyMatch`: Core's loop over a Boolean relation, with its early exit. `greedyMatchNoExit`: the same loop without the early exit.
- `greedyMatchNoExit_iff`, `greedyMatch_iff`: the greedy loop succeeds exactly when an ordered match exists.
- `greedyMatch_eq_noExit`: the early exit does not change the result.
- `multisigLoop_ok`: when every check on the pairs of the two lists returns `R`, `multisigLoop` returns `greedyMatch R`.
- `orderedMatch_reverse`: reversing both lists keeps an ordered match, so the property holds in stack order and in push order alike.

These theorems are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-! ## The checkers -/

/-- For every signature, public key and script code: `baseChecker` returns `some false`. -/
theorem baseChecker_checkSig (sig key code : List UInt8) : baseChecker.checkSig sig key code = some false := rfl

/-- For every operand: `baseChecker` fails the lock-time check. -/
theorem baseChecker_checkLockTime (n : Int) : baseChecker.checkLockTime n = some false := rfl

/-- For every operand: `baseChecker` fails the sequence check. -/
theorem baseChecker_checkSequence (n : Int) : baseChecker.checkSequence n = some false := rfl

/-- For every transaction, verifier and operand, and every index `nIn` that selects input `i`: the lock-time check is `lockTimeSatisfied` on the transaction's lock time and the sequence of `i`. -/
theorem transactionChecker_checkLockTime {tx : Transaction} {nIn : UInt32} {i : TxIn} (verify : SignatureVerifier)
    (h : tx.inputs.val[nIn.toNat]? = some i) (n : Int) :
    (transactionChecker tx nIn verify).checkLockTime n = some (lockTimeSatisfied tx.lockTime i.sequence n) := by
  simp [transactionChecker, h]

/-- For every transaction, verifier and operand, and every index `nIn` that selects input `i`: the sequence check is `sequenceSatisfied` on the version bits and the sequence of `i`. -/
theorem transactionChecker_checkSequence {tx : Transaction} {nIn : UInt32} {i : TxIn} (verify : SignatureVerifier)
    (h : tx.inputs.val[nIn.toNat]? = some i) (n : Int) :
    (transactionChecker tx nIn verify).checkSequence n = some (sequenceSatisfied tx.version i.sequence n) := by
  simp [transactionChecker, h]

/-- For every transaction, verifier and operand, and every index outside the inputs: the lock-time check is unavailable. -/
theorem transactionChecker_checkLockTime_none {tx : Transaction} {nIn : UInt32} (verify : SignatureVerifier)
    (h : tx.inputs.val.length ≤ nIn.toNat) (n : Int) : (transactionChecker tx nIn verify).checkLockTime n = none := by
  simp [transactionChecker, h]

/-- For every transaction, verifier and operand, and every index outside the inputs: the sequence check is unavailable. -/
theorem transactionChecker_checkSequence_none {tx : Transaction} {nIn : UInt32} (verify : SignatureVerifier)
    (h : tx.inputs.val.length ≤ nIn.toNat) (n : Int) : (transactionChecker tx nIn verify).checkSequence n = none := by
  simp [transactionChecker, h]

/--
For every lock time, sequence and operand `n`: `lockTimeSatisfied` holds exactly when `n` and the lock time lie on the same side of 500,000,000, `n` is at most the lock time, and the sequence is not `0xffffffff`.
-/
theorem lockTimeSatisfied_iff (lockTime sequence : UInt32) (n : Int) :
    lockTimeSatisfied lockTime sequence n = true ↔
      ((lockTime.toNat < 500000000 ∧ n < 500000000) ∨ (500000000 ≤ lockTime.toNat ∧ 500000000 ≤ n)) ∧
        n ≤ lockTime.toNat ∧ sequence ≠ 0xffffffff := by
  unfold lockTimeSatisfied lockTimeThreshold sequenceFinal
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, and_assoc]
  rfl

/--
For every version, sequence and operand `n`, with the masked values `m s = s &&& 0x40ffff`:
`sequenceSatisfied` holds exactly when the version is at least 2, bit 31 of the sequence is clear, `m n` and `m sequence` are both below `0x400000` or both at least `0x400000`, and `m n` is at most `m sequence`.
The operand is masked as `n.toNat`.
-/
theorem sequenceSatisfied_iff (version sequence : UInt32) (n : Int) :
    sequenceSatisfied version sequence n = true ↔
      2 ≤ version.toNat ∧ sequence.toNat &&& 0x80000000 = 0 ∧
        ((sequence.toNat &&& 0x40ffff < 0x400000 ∧ n.toNat &&& 0x40ffff < 0x400000) ∨
          (0x400000 ≤ sequence.toNat &&& 0x40ffff ∧ 0x400000 ≤ n.toNat &&& 0x40ffff)) ∧
        n.toNat &&& 0x40ffff ≤ sequence.toNat &&& 0x40ffff := by
  have hm : sequenceLockTimeTypeFlag ||| sequenceLockTimeMask = 0x40ffff := by decide
  unfold sequenceSatisfied
  dsimp only
  rw [hm]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]
  simp only [sequenceLockTimeTypeFlag, sequenceLockTimeDisableFlag]

/-- For every transaction, input index, verifier, signature and script code, and every public key that fails `isValidPubKey`: the check returns `some false`. -/
theorem transactionChecker_invalidKey (tx : Transaction) (nIn : UInt32) (verify : SignatureVerifier)
    (sig code : List UInt8) {key : List UInt8} (hk : isValidPubKey key = false) :
    (transactionChecker tx nIn verify).checkSig sig key code = some false := by
  simp [transactionChecker, hk]

/-- For every transaction, input index, verifier and script code, and every public key that passes `isValidPubKey`: the empty signature gives `some false`. -/
theorem transactionChecker_emptySig (tx : Transaction) (nIn : UInt32) (verify : SignatureVerifier)
    (code : List UInt8) {key : List UInt8} (hk : isValidPubKey key = true) :
    (transactionChecker tx nIn verify).checkSig [] key code = some false := by
  simp [transactionChecker, hk]

/--
For every transaction, input index, verifier, signature bytes `sig`, last byte `hashType`, and script code `code` shorter than 2^64 bytes, and every public key that passes `isValidPubKey`:
the check of `sig ++ [hashType]` is `verify sig key d`, where `d` is `legacySignatureHash` of `code` with the hash type `hashType` zero-extended to 32 bits.
-/
theorem transactionChecker_verify (tx : Transaction) (nIn : UInt32) (verify : SignatureVerifier)
    (sig : List UInt8) (hashType : UInt8) {key code : List UInt8} (hk : isValidPubKey key = true)
    (hc : code.length < 2 ^ 64) :
    (transactionChecker tx nIn verify).checkSig (sig ++ [hashType]) key code =
      verify sig key (legacySignatureHash ⟨⟨code, hc⟩⟩ tx nIn hashType.toUInt32) := by
  simp [transactionChecker, hk, hc]

/--
For every transaction, input index, signature, public key and script code shorter than 2^64 bytes, and all verifiers `v` and `w`:
if `v` and `w` agree on the request of `transactionChecker_verify`, or the signature is empty, or the key fails `isValidPubKey`, then the two checkers agree.
So `transactionChecker` consults its verifier only on that one request.
-/
theorem transactionChecker_verify_congr (tx : Transaction) (nIn : UInt32) {v w : SignatureVerifier}
    {sig key code : List UInt8} (hc : code.length < 2 ^ 64)
    (h : ∀ s hashType, sig = s ++ [hashType] → isValidPubKey key = true →
      v s key (legacySignatureHash ⟨⟨code, hc⟩⟩ tx nIn hashType.toUInt32) =
        w s key (legacySignatureHash ⟨⟨code, hc⟩⟩ tx nIn hashType.toUInt32)) :
    (transactionChecker tx nIn v).checkSig sig key code = (transactionChecker tx nIn w).checkSig sig key code := by
  cases hk : isValidPubKey key
  · rw [transactionChecker_invalidKey _ _ _ _ _ hk, transactionChecker_invalidKey _ _ _ _ _ hk]
  · rcases List.eq_nil_or_concat sig with hs | ⟨s, b, hs⟩
    · subst hs; rw [transactionChecker_emptySig _ _ _ _ hk, transactionChecker_emptySig _ _ _ _ hk]
    · subst hs
      rw [List.concat_eq_append, transactionChecker_verify _ _ _ _ _ hk hc, transactionChecker_verify _ _ _ _ _ hk hc]
      exact h s b (List.concat_eq_append ..) hk

/-! ## Ordered matching -/

/-- The loop of `multisigLoop` with a Boolean relation `R` as its check: Core's greedy matching with its early exit. -/
def greedyMatch {α β : Type} (R : α → β → Bool) : List α → List β → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    let rest := if R a b then as else a :: as
    if bs.length < rest.length then false else greedyMatch R rest bs

/-- Greedy matching without the early exit: it moves to the next key until the signatures or the keys run out. -/
def greedyMatchNoExit {α β : Type} (R : α → β → Bool) : List α → List β → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if R a b then greedyMatchNoExit R as bs else greedyMatchNoExit R (a :: as) bs

/-- The two lists have the same length, and `R` holds for each pair of items at the same position. -/
def PairsMatch {α β : Type} (R : α → β → Bool) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b = true ∧ PairsMatch R as bs
  | _, _ => False

/-- The signatures `sigs` pair in order with a subsequence `ks` of `keys`: `R` holds for each signature and its key. -/
def OrderedMatch {α β : Type} (R : α → β → Bool) (sigs : List α) (keys : List β) : Prop :=
  ∃ ks, ks.Sublist keys ∧ PairsMatch R sigs ks

/-- For all lists that pair under `R`: they have the same length. -/
theorem PairsMatch.length_eq {α β : Type} {R : α → β → Bool} :
    ∀ {as : List α} {bs : List β}, PairsMatch R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [PairsMatch.length_eq h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- For all lists whose first parts have the same length: the concatenations pair exactly when both parts pair. -/
theorem pairsMatch_append {α β : Type} {R : α → β → Bool} :
    ∀ {as₁ as₂ : List α} {bs₁ bs₂ : List β}, as₁.length = bs₁.length →
      (PairsMatch R (as₁ ++ as₂) (bs₁ ++ bs₂) ↔ PairsMatch R as₁ bs₁ ∧ PairsMatch R as₂ bs₂)
  | [], _, [], _, _ => by simp [PairsMatch]
  | a :: as₁, _, b :: bs₁, _, h => by
    simp only [List.cons_append, PairsMatch, pairsMatch_append (by simpa using h), and_assoc]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

/-- For all lists: their reversals pair exactly when they pair. -/
theorem pairsMatch_reverse {α β : Type} {R : α → β → Bool} :
    ∀ {as : List α} {bs : List β}, PairsMatch R as.reverse bs.reverse ↔ PairsMatch R as bs
  | [], [] => Iff.rfl
  | a :: as, b :: bs => by
    have hl : as.reverse.length = bs.reverse.length ↔ as.length = bs.length := by simp
    by_cases h : as.length = bs.length
    · simp only [List.reverse_cons, pairsMatch_append (hl.mpr h), pairsMatch_reverse, PairsMatch, and_true]
      exact and_comm
    · constructor
      · intro hm; have := hm.length_eq; simp at this; omega
      · intro hm; have := hm.length_eq; simp at this; omega
  | [], b :: bs => by
    simp only [List.reverse_nil, List.reverse_cons, PairsMatch, iff_false]
    intro hm; have := hm.length_eq; simp at this
  | a :: as, [] => by
    simp only [List.reverse_nil, List.reverse_cons, PairsMatch, iff_false]
    intro hm; have := hm.length_eq; simp at this

/-- A sublist whose head is `c` of a list with head `b`: the tail lies in the tail. -/
theorem tail_sublist_of_cons {β : Type} {c b : β} {ks bs : List β} (h : (c :: ks).Sublist (b :: bs)) :
    ks.Sublist bs := by
  cases h with
  | cons _ h => exact (List.sublist_cons_self c ks).trans h
  | cons_cons _ h => exact h

/-- For every relation and all lists: greedy matching without the early exit succeeds exactly when an ordered match exists. -/
theorem greedyMatchNoExit_iff {α β : Type} (R : α → β → Bool) (sigs : List α) (keys : List β) :
    greedyMatchNoExit R sigs keys = true ↔ OrderedMatch R sigs keys := by
  induction keys generalizing sigs with
  | nil =>
    cases sigs with
    | nil => simp only [greedyMatchNoExit, true_iff]; exact ⟨[], List.Sublist.slnil, trivial⟩
    | cons a as =>
      simp only [greedyMatchNoExit, OrderedMatch, Bool.false_eq_true, false_iff, not_exists, not_and]
      intro ks hks hf
      rw [List.sublist_nil.mp hks] at hf
      exact hf
  | cons b bs ih =>
    cases sigs with
    | nil => simp only [greedyMatchNoExit, true_iff]; exact ⟨[], List.nil_sublist _, trivial⟩
    | cons a as =>
      simp only [greedyMatchNoExit]
      split
      · rename_i hab
        rw [ih]
        constructor
        · rintro ⟨ks, hks, hf⟩
          exact ⟨b :: ks, hks.cons_cons b, hab, hf⟩
        · rintro ⟨ks, hks, hf⟩
          match ks, hks, hf with
          | _ :: _, hks, ⟨_, hf⟩ => exact ⟨_, tail_sublist_of_cons hks, hf⟩
      · rename_i hab
        rw [ih]
        constructor
        · rintro ⟨ks, hks, hf⟩
          exact ⟨ks, hks.cons b, hf⟩
        · rintro ⟨ks, hks, hf⟩
          match ks, hks, hf with
          | _ :: _, .cons _ h, hf => exact ⟨_, h, hf⟩
          | _ :: _, .cons_cons _ _, ⟨hc, _⟩ => exact absurd hc hab

/-- For every ordered match: there are at most as many signatures as keys. -/
theorem orderedMatch_length {α β : Type} {R : α → β → Bool} {sigs : List α} {keys : List β}
    (h : OrderedMatch R sigs keys) : sigs.length ≤ keys.length := by
  obtain ⟨ks, hks, hf⟩ := h
  rw [hf.length_eq]; exact hks.length_le

/-- For all lists with fewer keys than signatures: greedy matching without the early exit fails. -/
theorem greedyMatchNoExit_short {α β : Type} (R : α → β → Bool) {sigs : List α} {keys : List β}
    (h : keys.length < sigs.length) : greedyMatchNoExit R sigs keys = false := by
  cases hg : greedyMatchNoExit R sigs keys
  · rfl
  · have := orderedMatch_length ((greedyMatchNoExit_iff R sigs keys).mp hg); omega

/-- For every relation and all lists: the early exit does not change the result of greedy matching. -/
theorem greedyMatch_eq_noExit {α β : Type} (R : α → β → Bool) (sigs : List α) (keys : List β) :
    greedyMatch R sigs keys = greedyMatchNoExit R sigs keys := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> rfl
  | cons b bs ih =>
    cases sigs with
    | nil => rfl
    | cons a as =>
      have hstep : greedyMatchNoExit R (a :: as) (b :: bs) =
          greedyMatchNoExit R (if R a b then as else a :: as) bs := by
        simp only [greedyMatchNoExit]; split <;> simp_all
      rw [hstep]
      generalize hr : (if R a b = true then as else a :: as) = rest
      have : greedyMatch R (a :: as) (b :: bs) = if bs.length < rest.length then false else greedyMatch R rest bs := by
        rw [← hr]; rfl
      rw [this]
      split
      · rename_i h; exact (greedyMatchNoExit_short R h).symm
      · exact ih _

/--
For every relation and all lists: Core's greedy matching succeeds exactly when the signatures can be paired, in order, with a subsequence of the keys.
This is the greedy-equals-existence property of `OP_CHECKMULTISIG`.
-/
theorem greedyMatch_iff {α β : Type} (R : α → β → Bool) (sigs : List α) (keys : List β) :
    greedyMatch R sigs keys = true ↔ OrderedMatch R sigs keys := by
  rw [greedyMatch_eq_noExit, greedyMatchNoExit_iff]

/--
For every check function, relation and lists: if `check a b` returns `.ok (R a b)` for every signature `a` and key `b` of the lists, `multisigLoop` returns `greedyMatch R`.
The hypothesis covers every pair, which is stronger than Core needs: the loop visits only some pairs, and an error or unavailable result on an unvisited pair does not matter.
-/
theorem multisigLoop_ok {α β ε : Type} {check : α → β → Except ε Bool} {R : α → β → Bool}
    {sigs : List α} {keys : List β} (h : ∀ a ∈ sigs, ∀ b ∈ keys, check a b = .ok (R a b)) :
    multisigLoop check sigs keys = .ok (greedyMatch R sigs keys) := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> rfl
  | cons b bs ih =>
    cases sigs with
    | nil => rfl
    | cons a as =>
      have hrest : ∀ x ∈ (if R a b = true then as else a :: as), x ∈ a :: as := by
        intro x hx; split at hx
        · exact List.mem_cons_of_mem a hx
        · exact hx
      generalize hr : (if R a b = true then as else a :: as) = rest at hrest
      have e1 : multisigLoop check (a :: as) (b :: bs) =
          if bs.length < rest.length then .ok false else multisigLoop check rest bs := by
        rw [← hr]; simp only [multisigLoop, h a (by simp) b (by simp)]
      have e2 : greedyMatch R (a :: as) (b :: bs) = if bs.length < rest.length then false else greedyMatch R rest bs := by
        rw [← hr]; rfl
      rw [e1, e2]
      split
      · rfl
      · exact ih fun x hx y hy => h x (hrest x hx) y (List.mem_cons_of_mem b hy)

/-- For every relation and all lists: the reversed signatures match the reversed keys exactly when the signatures match the keys. -/
theorem orderedMatch_reverse {α β : Type} {R : α → β → Bool} {sigs : List α} {keys : List β} :
    OrderedMatch R sigs.reverse keys.reverse ↔ OrderedMatch R sigs keys := by
  constructor
  · rintro ⟨ks, hks, hf⟩
    refine ⟨ks.reverse, ?_, ?_⟩
    · simpa using hks.reverse
    · rw [← pairsMatch_reverse]; simpa using hf
  · rintro ⟨ks, hks, hf⟩
    exact ⟨ks.reverse, hks.reverse, pairsMatch_reverse.mpr hf⟩

end DogeLib.Script
