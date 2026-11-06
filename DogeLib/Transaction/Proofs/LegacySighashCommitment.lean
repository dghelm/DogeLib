module

public import DogeLib.Transaction.Proofs.LegacySighashReference
public import DogeLib.Transaction.Proofs.Serialization

/-!
# Proofs: what a legacy ALL digest commits to

Design record 0003, section 7, leaves the restriction to SIGHASH_ALL without ANYONECANPAY to the hypotheses of a later bridge property.
This module states what such a hash type commits to, for the legacy signature hash of `Transaction.LegacySighash`.

## The committed fields

`HashType.IsAllOnly h` holds when the ANYONECANPAY bit of `h` is clear and its low five bits are neither NONE (2) nor SINGLE (3), as Core's serializer tests them.
`legacyAllFields tx` is the version, each input's outpoint and sequence in order, the outputs and the lock time.
It leaves out every scriptSig: the serializer writes the empty script, or the script code for input `nIn`, in their place.

## The theorems

- `legacyReferencePlan_allOnly_commits`: two transformation plans for the same script code, input index and `IsAllOnly` hash type, with the index in range, are equal only if the two transactions have equal `legacyAllFields`. It needs no other hypothesis.
- `legacySignatureHashPlan_allOnly_commits`: the same for the production plan. It also needs the hypotheses of `legacySignatureHashPlan_eq_reference` for both transactions: a fully parsed script code, and fewer than 2^32 inputs and outputs.
- `legacySignatureHashPlan_eq_of_allFields`, `legacyReferencePlan_eq_of_allFields`: the converse, with no hypothesis beyond `IsAllOnly`.
- `legacyReferencePlan_eq_iff_allFields`, `legacySignatureHashPlan_eq_iff_allFields`: the two directions together.
- `legacySignatureHash_eq_of_allFields`: equal committed fields give equal digests.
- `legacyReferencePlan_allOnly_index_eq`: when the script code of the copy is not empty, equal plans also have the same input index.
- `legacySignatureHashPlan_eq_of_anyoneCanPay`, `legacySignatureHashPlan_eq_of_none`, `legacySignatureHashPlan_eq_of_single`: the weaker modes. Agreement on fewer fields already gives equal plans, and three corollaries name a field that each mode leaves out.

## What the theorems do not say

The forward theorems are about plans, so about the bytes that are hashed. They need no assumption about double SHA-256.
No theorem here goes from equal digests to equal fields. That would need collision resistance of double SHA-256, which DogeLib does not assume.

These are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-! ## Definitions -/

/--
The hash type is ALL without ANYONECANPAY, as Core's serializer tests it (D3, lines 1054 to 1143).
"Only" means that the ANYONECANPAY bit `0x80` is clear.
The low five bits, `nHashType & 0x1f`, are neither NONE (2) nor SINGLE (3).
So the class includes the undefined low values: `0x01`, `0x00`, `0x04`, `0x21` and `0x101` are members, and `0x81`, `0x02`, `0x03` and `0x22` are not.
Under `SCRIPT_VERIFY_STRICTENC`, the signature encoding check rejects undefined hash types, so the only member that a signature can then carry is `0x01`.
-/
def HashType.IsAllOnly (h : UInt32) : Prop :=
  HashType.anyoneCanPay h = false ∧ HashType.isNone h = false ∧ HashType.isSingle h = false

instance (h : UInt32) : Decidable (HashType.IsAllOnly h) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The fields of an input that a legacy digest can commit to: its outpoint and its sequence. Not its scriptSig. -/
def TxIn.signedFields (i : TxIn) : OutPoint × UInt32 := (i.prevout, i.sequence)

/--
The fields that a legacy digest with an `IsAllOnly` hash type commits to:
the version, each input's outpoint and sequence in order, so also the number of inputs, the outputs, and the lock time.
No scriptSig is among them.
-/
def legacyAllFields (tx : Transaction) : UInt32 × List (OutPoint × UInt32) × List TxOut × UInt32 :=
  (tx.version, tx.inputs.val.map TxIn.signedFields, tx.outputs.val, tx.lockTime)

/--
For all transactions `tx` and `tx'`, `legacyAllFields` agree exactly when these agree: the version, the lock time, the number of inputs, each input's outpoint and sequence, and the outputs.
-/
theorem legacyAllFields_eq_iff (tx tx' : Transaction) :
    legacyAllFields tx = legacyAllFields tx' ↔
      tx.version = tx'.version ∧ tx.lockTime = tx'.lockTime ∧
        tx.inputs.val.length = tx'.inputs.val.length ∧
        (∀ (i : Nat) (h : i < tx.inputs.val.length) (h' : i < tx'.inputs.val.length),
          tx.inputs.val[i].prevout = tx'.inputs.val[i].prevout ∧
            tx.inputs.val[i].sequence = tx'.inputs.val[i].sequence) ∧
        tx.outputs = tx'.outputs := by
  constructor
  · intro heq
    simp only [legacyAllFields, Prod.mk.injEq] at heq
    obtain ⟨hv, hi, ho, hl⟩ := heq
    have hlen : tx.inputs.val.length = tx'.inputs.val.length := by
      simpa using congrArg List.length hi
    refine ⟨hv, hl, hlen, fun i h h' => ?_, Subtype.ext ho⟩
    have := congrArg (·[i]?) hi
    simp only [List.getElem?_map, List.getElem?_eq_getElem h, List.getElem?_eq_getElem h',
      Option.map_some, Option.some.injEq, TxIn.signedFields, Prod.mk.injEq] at this
    exact this
  · rintro ⟨hv, hl, hlen, hi, ho⟩
    simp only [legacyAllFields, Prod.mk.injEq, hv, hl, ho, true_and, and_true]
    apply List.ext_getElem (by simpa using hlen)
    intro i h1 h2
    simp only [List.length_map] at h1 h2
    obtain ⟨hp, hs⟩ := hi i h1 h2
    simp [TxIn.signedFields, hp, hs]

/-! ## The serializer reads no scriptSig -/

/-- For all lists of equal length whose elements agree index by index under `g`, their `mapIdx g` agree. -/
theorem mapIdx_eq_of_getElem {α β : Type} {g : Nat → α → β} {l l' : List α} (hlen : l.length = l'.length)
    (h : ∀ (i : Nat) (h : i < l.length) (h' : i < l'.length), g i l[i] = g i l'[i]) :
    l.mapIdx g = l'.mapIdx g := by
  apply List.ext_getElem (by simpa using hlen)
  intro i h1 h2
  simp only [List.length_mapIdx] at h1 h2
  simp only [List.getElem_mapIdx]
  exact h i h1 h2

/-- For every script code, index, flag and position: two inputs with the same outpoint and sequence are written the same. -/
theorem legacyInputBytes_congr (sc : Script) (n : Nat) (z : Bool) (i : Nat) {x y : TxIn}
    (hp : x.prevout = y.prevout) (hs : i = n ∨ z = false → x.sequence = y.sequence) :
    legacyInputBytes sc n z i x = legacyInputBytes sc n z i y := by
  unfold legacyInputBytes
  by_cases hi : i = n
  · simp [hi, hp, hs (Or.inl hi)]
  · cases z
    · simp [hi, hp, hs (Or.inr rfl)]
    · simp [hi, hp]

/--
For every script code, index and pair of transactions with the same input outpoints, without ANYONECANPAY:
the inputs are written the same when the sequences agree, at every index if `z` is false, at index `nIn` if `z` is true.
-/
theorem legacyInputsBytes_congr (sc : Script) (tx tx' : Transaction) (nIn : UInt32) (z : Bool)
    (hp : tx.inputs.val.map (·.prevout) = tx'.inputs.val.map (·.prevout))
    (hs : ∀ (i : Nat) (h : i < tx.inputs.val.length) (h' : i < tx'.inputs.val.length),
      i = nIn.toNat ∨ z = false → tx.inputs.val[i].sequence = tx'.inputs.val[i].sequence) :
    legacyInputsBytes sc tx nIn false z = legacyInputsBytes sc tx' nIn false z := by
  have hlen : tx.inputs.val.length = tx'.inputs.val.length := by simpa using congrArg List.length hp
  unfold legacyInputsBytes
  simp only [Bool.false_eq_true, ↓reduceIte, hlen]
  congr 2
  apply mapIdx_eq_of_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.length_take] at h1 h2
  have hi1 : i < tx.inputs.val.length := by omega
  have hi2 : i < tx'.inputs.val.length := by omega
  simp only [List.getElem_take]
  apply legacyInputBytes_congr
  · have := congrArg (·[i]?) hp
    simpa [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using this
  · exact hs i hi1 hi2

/--
For every script code and pair of transactions, with ANYONECANPAY:
the inputs are written the same when input `nIn` has the same outpoint and sequence in both, or is missing from both.
-/
theorem legacyInputsBytes_anyoneCanPay_congr (sc : Script) (tx tx' : Transaction) (nIn : UInt32) (z : Bool)
    (hi : (tx.inputs.val[nIn.toNat]?).map TxIn.signedFields = (tx'.inputs.val[nIn.toNat]?).map TxIn.signedFields) :
    legacyInputsBytes sc tx nIn true z = legacyInputsBytes sc tx' nIn true z := by
  unfold legacyInputsBytes
  simp only [↓reduceIte]
  congr 1
  by_cases h1 : nIn.toNat < tx.inputs.val.length
  · by_cases h2 : nIn.toNat < tx'.inputs.val.length
    · rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2]
      simp only [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.map_some,
        Option.some.injEq, TxIn.signedFields, Prod.mk.injEq] at hi
      simp only [List.take_succ_cons, List.take_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact legacyInputBytes_congr sc _ _ _ hi.1 (fun _ => hi.2)
    · simp [List.getElem?_eq_getElem h1, List.getElem?_eq_none (Nat.le_of_not_lt h2)] at hi
  · have hn : tx.inputs.val[nIn.toNat]? = none := List.getElem?_eq_none (Nat.le_of_not_lt h1)
    rw [hn] at hi
    have h2 : tx'.inputs.val.length ≤ nIn.toNat := by
      cases h : tx'.inputs.val[nIn.toNat]? with
      | none => exact List.getElem?_eq_none_iff.mp h
      | some _ => simp [h] at hi
    rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt h1), List.drop_eq_nil_of_le h2]

/-- For every pair of transactions, without NONE: the outputs are written the same when SINGLE does not hold and the outputs are equal. -/
theorem legacyOutputsBytes_all_congr (tx tx' : Transaction) (nIn : UInt32)
    (ho : tx.outputs.val = tx'.outputs.val) :
    legacyOutputsBytes tx nIn false false = legacyOutputsBytes tx' nIn false false := by
  simp [legacyOutputsBytes, ho]

/-- For every pair of transactions: with SINGLE, the outputs are written the same when output `nIn` is the same in both, provided both have it. -/
theorem legacyOutputsBytes_single_congr (tx tx' : Transaction) (nIn : UInt32)
    (h1 : nIn.toNat < tx.outputs.val.length) (h2 : nIn.toNat < tx'.outputs.val.length)
    (ho : tx.outputs.val[nIn.toNat] = tx'.outputs.val[nIn.toNat]) :
    legacyOutputsBytes tx nIn false true = legacyOutputsBytes tx' nIn false true := by
  unfold legacyOutputsBytes
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 2
  apply mapIdx_eq_of_getElem (by simp; omega)
  intro i hi1 hi2
  simp only [List.length_take] at hi1 hi2
  by_cases hi : i = nIn.toNat
  · subst hi
    simp [ho]
  · simp [hi]

/-! ## The converse: equal committed fields give equal plans -/

/--
For every script code, input index and `IsAllOnly` hash type: two transactions with equal `legacyAllFields` have equal production plans.
There is no other hypothesis. The production serializer reads no scriptSig, and with this hash type it reads only these fields.
The equality also covers an input index out of range, where both plans are the fixed digest `one`.
-/
theorem legacySignatureHashPlan_eq_of_allFields (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hf : legacyAllFields tx = legacyAllFields tx') :
    legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h := by
  obtain ⟨hacp, hnone, hsingle⟩ := hh
  obtain ⟨hv, hl, hlen, hi, ho⟩ := (legacyAllFields_eq_iff tx tx').mp hf
  have hp : tx.inputs.val.map (·.prevout) = tx'.inputs.val.map (·.prevout) := by
    apply List.ext_getElem (by simpa using hlen)
    intro i h1 h2
    simp only [List.length_map] at h1 h2
    simp [(hi i h1 h2).1]
  unfold legacySignatureHashPlan
  simp only [hlen, hsingle, Bool.false_eq_true, false_and, ↓reduceIte]
  split
  · rfl
  · congr 1
    unfold legacyPreimage legacyBody
    rw [hacp, hnone, hsingle, hv, hl, legacyOutputsBytes_all_congr tx tx' n (congrArg Subtype.val ho)]
    simp only [Bool.or_self]
    rw [legacyInputsBytes_congr sc tx tx' n false hp (fun i h1 h2 _ => (hi i h1 h2).2)]

/-- For every list of inputs, index and script: without the zero-sequence step, the copy's inputs are the outpoints and sequences of the inputs, with the script `code` at index `n` and the empty script elsewhere. -/
theorem referenceSequencedInputs_false_eq (code : Script) (l : List TxIn) (n : Nat) :
    referenceSequencedInputs code l n false =
      (l.map TxIn.signedFields).mapIdx fun i p => ⟨p.1, if i = n then code else Script.empty, p.2⟩ := by
  unfold referenceSequencedInputs
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, List.getElem_map, List.getElem_modify, List.getElem_mapIdx,
    TxIn.signedFields]
  by_cases hi : n = i
  · simp [hi]
  · simp [hi, Ne.symm hi]

/-- For every list of inputs, index and script: the copy's inputs without the zero-sequence step have the same outpoints and sequences. -/
theorem referenceSequencedInputs_signedFields (code : Script) (l : List TxIn) (n : Nat) :
    (referenceSequencedInputs code l n false).map TxIn.signedFields = l.map TxIn.signedFields := by
  rw [referenceSequencedInputs_false_eq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [TxIn.signedFields]

/-- For every `IsAllOnly` hash type, the copy's inputs are the inputs with the scripts replaced. -/
theorem referenceTransaction_inputs_allOnly (sc : Script) (tx : Transaction) (n : Nat) {h : UInt32}
    (hh : HashType.IsAllOnly h) :
    (referenceTransaction sc tx n h).inputs.val =
      referenceSequencedInputs (referenceScriptCode sc) tx.inputs.val n false := by
  obtain ⟨hacp, hnone, hsingle⟩ := hh
  simp [referenceTransaction, CountedList.ofLengthLe, referenceInputs, hacp, hnone, hsingle]

/-- For every `IsAllOnly` hash type, the copy's outputs are the outputs. -/
theorem referenceTransaction_outputs_allOnly (sc : Script) (tx : Transaction) (n : Nat) {h : UInt32}
    (hh : HashType.IsAllOnly h) :
    (referenceTransaction sc tx n h).outputs.val = tx.outputs.val := by
  obtain ⟨_, hnone, hsingle⟩ := hh
  simp [referenceTransaction, CountedList.ofLengthLe, referenceOutputs, hnone, hsingle]

/-- For every script code, input index and `IsAllOnly` hash type: two transactions with equal `legacyAllFields` have equal copies. -/
theorem referenceTransaction_eq_of_allFields (sc : Script) (tx tx' : Transaction) (n : Nat) {h : UInt32}
    (hh : HashType.IsAllOnly h) (hf : legacyAllFields tx = legacyAllFields tx') :
    referenceTransaction sc tx n h = referenceTransaction sc tx' n h := by
  simp only [legacyAllFields, Prod.mk.injEq] at hf
  obtain ⟨hv, hi, ho, hl⟩ := hf
  have hin := referenceTransaction_inputs_allOnly sc tx n hh
  have hin' := referenceTransaction_inputs_allOnly sc tx' n hh
  have hout := referenceTransaction_outputs_allOnly sc tx n hh
  have hout' := referenceTransaction_outputs_allOnly sc tx' n hh
  rw [referenceSequencedInputs_false_eq] at hin hin'
  have e : ∀ t : Transaction, t = ⟨t.version, t.inputs, t.outputs, t.lockTime⟩ := fun _ => rfl
  rw [e (referenceTransaction sc tx n h), e (referenceTransaction sc tx' n h)]
  congr 1 <;> first
    | exact hv
    | exact hl
    | exact Subtype.ext (by rw [hin, hin', hi])
    | exact Subtype.ext (by rw [hout, hout', ho])

/--
For every script code, input index and `IsAllOnly` hash type: two transactions with equal `legacyAllFields` have equal transformation plans.
There is no other hypothesis.
-/
theorem legacyReferencePlan_eq_of_allFields (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hf : legacyAllFields tx = legacyAllFields tx') :
    legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n h := by
  have hlen : tx.inputs.val.length = tx'.inputs.val.length := by
    simpa [legacyAllFields] using congrArg (fun f => f.2.1.length) hf
  have hsingle := hh.2.2
  unfold legacyReferencePlan
  simp only [hlen, hsingle, Bool.false_eq_true, false_and, ↓reduceIte]
  split
  · rfl
  · rw [referenceTransaction_eq_of_allFields sc tx tx' n.toNat hh hf]

/-! ## Forward: equal plans give equal committed fields -/

/-- For every script code, input index and `IsAllOnly` hash type: two transactions with equal copies have equal `legacyAllFields`. -/
theorem legacyAllFields_eq_of_referenceTransaction_eq (sc : Script) (tx tx' : Transaction) (n : Nat) {h : UInt32}
    (hh : HashType.IsAllOnly h) (heq : referenceTransaction sc tx n h = referenceTransaction sc tx' n h) :
    legacyAllFields tx = legacyAllFields tx' := by
  have hin := congrArg (fun t => t.inputs.val.map TxIn.signedFields) heq
  have hout := congrArg (fun t => t.outputs.val) heq
  simp only [referenceTransaction_inputs_allOnly sc _ n hh, referenceSequencedInputs_signedFields,
    referenceTransaction_outputs_allOnly sc _ n hh] at hin hout
  have hv : tx.version = tx'.version := by
    simpa [referenceTransaction] using congrArg Transaction.version heq
  have hl : tx.lockTime = tx'.lockTime := by
    simpa [referenceTransaction] using congrArg Transaction.lockTime heq
  simp only [legacyAllFields, hv, hl, hin, hout]

/-- For every script code and `IsAllOnly` hash type, and an input index in range: the transformation plan hashes the copy, then the hash type. -/
theorem legacyReferencePlan_eq_hashBytes_of_allOnly (sc : Script) (tx : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hn : n.toNat < tx.inputs.val.length) :
    legacyReferencePlan sc tx n h =
      .hashBytes (Codec.encode (referenceTransaction sc tx n.toNat h) ++ Codec.encode h) := by
  unfold legacyReferencePlan
  simp [Nat.not_le_of_lt hn, hh.2.2]

/-- For every script code, input index and `IsAllOnly` hash type: when the transformation plan hashes bytes for `tx`, a transformation plan equal to it also has its index in range. -/
theorem lt_of_legacyReferencePlan_eq (sc : Script) (tx tx' : Transaction) (n n' h : UInt32)
    (hh : HashType.IsAllOnly h) (hn : n.toNat < tx.inputs.val.length)
    (heq : legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n' h) :
    n'.toNat < tx'.inputs.val.length := by
  rw [legacyReferencePlan_eq_hashBytes_of_allOnly sc tx n h hh hn] at heq
  apply Nat.lt_of_not_le
  intro hc
  unfold legacyReferencePlan at heq
  simp [hc] at heq

/-- For every script code, input indices and `IsAllOnly` hash type, with the first index in range: equal transformation plans have equal copies. -/
theorem referenceTransaction_eq_of_legacyReferencePlan_eq (sc : Script) (tx tx' : Transaction) (n n' h : UInt32)
    (hh : HashType.IsAllOnly h) (hn : n.toNat < tx.inputs.val.length)
    (heq : legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n' h) :
    referenceTransaction sc tx n.toNat h = referenceTransaction sc tx' n'.toNat h := by
  have hn' := lt_of_legacyReferencePlan_eq sc tx tx' n n' h hh hn heq
  rw [legacyReferencePlan_eq_hashBytes_of_allOnly sc tx n h hh hn,
    legacyReferencePlan_eq_hashBytes_of_allOnly sc tx' n' h hh hn'] at heq
  exact encode_injective (List.append_cancel_right (LegacyHashPlan.hashBytes.inj heq))

/--
**Commitment, transformation reference.**
Take a script code, an input index `n` and an `IsAllOnly` hash type `h`, and two transactions `tx` and `tx'`, with `n` an input index of `tx`.
If their transformation plans are equal, then `legacyAllFields tx = legacyAllFields tx'`:
the version, the lock time, the number of inputs, each input's outpoint and sequence, and the outputs agree.
No other hypothesis is needed.
The hypothesis on `n` is needed: when `n` is not an input index of either transaction, both plans are the fixed digest `one`.
-/
theorem legacyReferencePlan_allOnly_commits (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hn : n.toNat < tx.inputs.val.length)
    (heq : legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n h) :
    legacyAllFields tx = legacyAllFields tx' :=
  legacyAllFields_eq_of_referenceTransaction_eq sc tx tx' n.toNat hh
    (referenceTransaction_eq_of_legacyReferencePlan_eq sc tx tx' n n h hh hn heq)

/--
**Commitment, production plan.**
Take a script code whose instructions all parse, an input index `n` and an `IsAllOnly` hash type `h`.
Take two transactions with fewer than 2^32 inputs and fewer than 2^32 outputs each, with `n` an input index of `tx`.
If their production plans are equal, then `legacyAllFields tx = legacyAllFields tx'`.

The parse and count hypotheses are those of `legacySignatureHashPlan_eq_reference`, for both transactions.
The count hypotheses are needed: Core writes the counts modulo 2^32, and only that many inputs or outputs.
-/
theorem legacySignatureHashPlan_allOnly_commits (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hParse : (scanOps sc.bytes.val).2 = [])
    (hIn : tx.inputs.val.length < 2 ^ 32) (hOut : tx.outputs.val.length < 2 ^ 32)
    (hIn' : tx'.inputs.val.length < 2 ^ 32) (hOut' : tx'.outputs.val.length < 2 ^ 32)
    (hn : n.toNat < tx.inputs.val.length)
    (heq : legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h) :
    legacyAllFields tx = legacyAllFields tx' := by
  rw [legacySignatureHashPlan_eq_reference sc tx n h hParse hIn hOut,
    legacySignatureHashPlan_eq_reference sc tx' n h hParse hIn' hOut'] at heq
  exact legacyReferencePlan_allOnly_commits sc tx tx' n h hh hn heq

/-- Under the hypotheses of `legacyReferencePlan_allOnly_commits` without the equality: the transformation plans are equal exactly when `legacyAllFields` are. -/
theorem legacyReferencePlan_eq_iff_allFields (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hn : n.toNat < tx.inputs.val.length) :
    legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n h ↔ legacyAllFields tx = legacyAllFields tx' :=
  ⟨legacyReferencePlan_allOnly_commits sc tx tx' n h hh hn, legacyReferencePlan_eq_of_allFields sc tx tx' n h hh⟩

/-- Under the hypotheses of `legacySignatureHashPlan_allOnly_commits` without the equality: the production plans are equal exactly when `legacyAllFields` are. -/
theorem legacySignatureHashPlan_eq_iff_allFields (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hParse : (scanOps sc.bytes.val).2 = [])
    (hIn : tx.inputs.val.length < 2 ^ 32) (hOut : tx.outputs.val.length < 2 ^ 32)
    (hIn' : tx'.inputs.val.length < 2 ^ 32) (hOut' : tx'.outputs.val.length < 2 ^ 32)
    (hn : n.toNat < tx.inputs.val.length) :
    legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h ↔
      legacyAllFields tx = legacyAllFields tx' :=
  ⟨legacySignatureHashPlan_allOnly_commits sc tx tx' n h hh hParse hIn hOut hIn' hOut' hn,
    legacySignatureHashPlan_eq_of_allFields sc tx tx' n h hh⟩

/--
**Digest.** For every script code, input index and `IsAllOnly` hash type: two transactions with equal `legacyAllFields` have equal digests.
The converse at the level of digests is not proved. It would need collision resistance of double SHA-256, which DogeLib does not assume.
-/
theorem legacySignatureHash_eq_of_allFields (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hh : HashType.IsAllOnly h) (hf : legacyAllFields tx = legacyAllFields tx') :
    legacySignatureHash sc tx n h = legacySignatureHash sc tx' n h := by
  rw [legacySignatureHash, legacySignatureHash, legacySignatureHashPlan_eq_of_allFields sc tx tx' n h hh hf]

/-! ## The signed input's position -/

/--
**Position.** Take a script code whose copy `referenceScriptCode sc` is not empty, an `IsAllOnly` hash type, and input indices `n` and `n'`, with `n` an input index of `tx`.
If the transformation plans of `tx` at `n` and `tx'` at `n'` are equal, then `n = n'` and `legacyAllFields tx = legacyAllFields tx'`.

The copy gives input `n` the script code and every other input the empty script, so the position of the script code is the index.
The hypothesis on the script code is needed. When the script code is empty, or holds only `OP_CODESEPARATOR` instructions, every input of the copy has the empty script.
Then a transaction with two inputs has the same plan at index 0 and at index 1. A known answer in `tests/KnownAnswers.lean` shows such a case.
-/
theorem legacyReferencePlan_allOnly_index_eq (sc : Script) (tx tx' : Transaction) (n n' h : UInt32)
    (hh : HashType.IsAllOnly h) (hcode : (referenceScriptCode sc).bytes.val ≠ [])
    (hn : n.toNat < tx.inputs.val.length)
    (heq : legacyReferencePlan sc tx n h = legacyReferencePlan sc tx' n' h) :
    n = n' ∧ legacyAllFields tx = legacyAllFields tx' := by
  have ht := referenceTransaction_eq_of_legacyReferencePlan_eq sc tx tx' n n' h hh hn heq
  have hin := congrArg (fun t => t.inputs.val) ht
  simp only [referenceTransaction_inputs_allOnly sc _ _ hh, referenceSequencedInputs_false_eq] at hin
  have hlen : tx.inputs.val.length = tx'.inputs.val.length := by simpa using congrArg List.length hin
  have hnn : n.toNat = n'.toNat := by
    have hs := congrArg (fun l => (l[n.toNat]?).map TxIn.scriptSig) hin
    simp only [List.getElem?_mapIdx, List.getElem?_map, List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem (hlen ▸ hn), Option.map_some, Option.some.injEq, ↓reduceIte] at hs
    by_cases hne : n.toNat = n'.toNat
    · exact hne
    · simp only [hne, ↓reduceIte] at hs
      exact absurd (by rw [hs]; rfl) hcode
  have hn_eq : n = n' := UInt32.toNat_inj.mp hnn
  subst hn_eq
  exact ⟨rfl, legacyAllFields_eq_of_referenceTransaction_eq sc tx tx' _ hh ht⟩

/-! ## The weaker modes -/

/-- NONE and SINGLE exclude each other: the low five bits cannot be both 2 and 3. -/
theorem HashType.isSingle_eq_false_of_isNone {h : UInt32} (hn : HashType.isNone h = true) :
    HashType.isSingle h = false := by
  simp only [HashType.isNone, HashType.isSingle, sighashNone, sighashSingle, beq_iff_eq] at hn ⊢
  simp [hn]

/-- NONE and SINGLE exclude each other. -/
theorem HashType.isNone_eq_false_of_isSingle {h : UInt32} (hs : HashType.isSingle h = true) :
    HashType.isNone h = false := by
  cases hn : HashType.isNone h
  · rfl
  · rw [HashType.isSingle_eq_false_of_isNone hn] at hs
    cases hs

/--
**ALL with ANYONECANPAY.** For every script code, input index and hash type with the ANYONECANPAY bit and neither NONE nor SINGLE:
two transactions have equal production plans when they agree on the version, the lock time, the outputs, and the outpoint and sequence of input `n`.
Input `n` may be missing from both. The other inputs, and the number of inputs, are not committed.
-/
theorem legacySignatureHashPlan_eq_of_anyoneCanPay (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = true) (hnone : HashType.isNone h = false)
    (hsingle : HashType.isSingle h = false)
    (hv : tx.version = tx'.version) (hl : tx.lockTime = tx'.lockTime) (ho : tx.outputs.val = tx'.outputs.val)
    (hi : (tx.inputs.val[n.toNat]?).map TxIn.signedFields = (tx'.inputs.val[n.toNat]?).map TxIn.signedFields) :
    legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h := by
  have hle : tx.inputs.val.length ≤ n.toNat ↔ tx'.inputs.val.length ≤ n.toNat := by
    rw [← List.getElem?_eq_none_iff, ← List.getElem?_eq_none_iff, ← Option.map_eq_none_iff (f := TxIn.signedFields),
      hi, Option.map_eq_none_iff]
  unfold legacySignatureHashPlan
  simp only [hle, hsingle, Bool.false_eq_true, false_and, ↓reduceIte]
  split
  · rfl
  · congr 1
    unfold legacyPreimage legacyBody
    rw [hacp, hnone, hsingle, hv, hl, legacyOutputsBytes_all_congr tx tx' n ho,
      legacyInputsBytes_anyoneCanPay_congr sc tx tx' n _ hi]

/--
**NONE without ANYONECANPAY.** For every script code, input index and hash type that is NONE without the ANYONECANPAY bit:
two transactions have equal production plans when they agree on the version, the lock time, every input's outpoint, and the sequence of input `n`.
The outputs and the other inputs' sequences are not committed.
-/
theorem legacySignatureHashPlan_eq_of_none (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = false) (hnone : HashType.isNone h = true)
    (hv : tx.version = tx'.version) (hl : tx.lockTime = tx'.lockTime)
    (hp : tx.inputs.val.map (·.prevout) = tx'.inputs.val.map (·.prevout))
    (hs : (tx.inputs.val[n.toNat]?).map (·.sequence) = (tx'.inputs.val[n.toNat]?).map (·.sequence)) :
    legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h := by
  have hsingle := HashType.isSingle_eq_false_of_isNone hnone
  have hlen : tx.inputs.val.length = tx'.inputs.val.length := by simpa using congrArg List.length hp
  unfold legacySignatureHashPlan
  simp only [hlen, hsingle, Bool.false_eq_true, false_and, ↓reduceIte]
  split
  · rfl
  · congr 1
    unfold legacyPreimage legacyBody
    rw [hacp, hnone, hsingle, hv, hl]
    have hout : legacyOutputsBytes tx n true false = legacyOutputsBytes tx' n true false := rfl
    rw [hout, legacyInputsBytes_congr sc tx tx' n _ hp]
    intro i h1 h2 hi
    simp only [Bool.false_or, Bool.true_eq_false, or_false] at hi
    subst hi
    simpa [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using hs

/--
**SINGLE without ANYONECANPAY.** For every script code, input index and hash type that is SINGLE without the ANYONECANPAY bit:
two transactions have equal production plans when they agree on the version, the lock time, every input's outpoint, the sequence of input `n`, and output `n`.
Output `n` may be missing from both. Then both plans are the fixed digest `one`.
The other outputs, beyond their number being more than `n`, and the other inputs' sequences are not committed.
-/
theorem legacySignatureHashPlan_eq_of_single (sc : Script) (tx tx' : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = false) (hsingle : HashType.isSingle h = true)
    (hv : tx.version = tx'.version) (hl : tx.lockTime = tx'.lockTime)
    (hp : tx.inputs.val.map (·.prevout) = tx'.inputs.val.map (·.prevout))
    (hs : (tx.inputs.val[n.toNat]?).map (·.sequence) = (tx'.inputs.val[n.toNat]?).map (·.sequence))
    (ho : tx.outputs.val[n.toNat]? = tx'.outputs.val[n.toNat]?) :
    legacySignatureHashPlan sc tx n h = legacySignatureHashPlan sc tx' n h := by
  have hnone := HashType.isNone_eq_false_of_isSingle hsingle
  have hlen : tx.inputs.val.length = tx'.inputs.val.length := by simpa using congrArg List.length hp
  have hle : tx.outputs.val.length ≤ n.toNat ↔ tx'.outputs.val.length ≤ n.toNat := by
    rw [← List.getElem?_eq_none_iff, ← List.getElem?_eq_none_iff, ho]
  unfold legacySignatureHashPlan
  simp only [hlen, hsingle, hle, true_and]
  split
  · rfl
  · split
    · rfl
    · rename_i h2
      have h1 : n.toNat < tx.outputs.val.length := Nat.lt_of_not_le fun hc => h2 (hle.mp hc)
      have h1' : n.toNat < tx'.outputs.val.length := by omega
      congr 1
      unfold legacyPreimage legacyBody
      rw [hacp, hnone, hsingle, hv, hl,
        legacyOutputsBytes_single_congr tx tx' n h1 h1' (by
          simpa [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h1'] using ho),
        legacyInputsBytes_congr sc tx tx' n _ hp]
      intro i hi1 hi2 hi
      simp only [Bool.or_false, Bool.true_eq_false, or_false] at hi
      subst hi
      simpa [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] using hs

/-- With ALL and ANYONECANPAY, replacing an input other than input `n` leaves the production plan unchanged. -/
theorem legacySignatureHashPlan_anyoneCanPay_set_other (sc : Script) (tx : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = true) (hnone : HashType.isNone h = false)
    (hsingle : HashType.isSingle h = false) (i : Nat) (hi : i ≠ n.toNat) (x : TxIn) :
    legacySignatureHashPlan sc { tx with inputs := ⟨tx.inputs.val.set i x, by simpa using tx.inputs.property⟩ } n h =
      legacySignatureHashPlan sc tx n h :=
  legacySignatureHashPlan_eq_of_anyoneCanPay sc _ tx n h hacp hnone hsingle rfl rfl rfl
    (by simp only [List.getElem?_set_ne hi])

/-- With NONE and without ANYONECANPAY, replacing the outputs leaves the production plan unchanged. -/
theorem legacySignatureHashPlan_none_outputs (sc : Script) (tx : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = false) (hnone : HashType.isNone h = true) (outs : CountedList TxOut) :
    legacySignatureHashPlan sc { tx with outputs := outs } n h = legacySignatureHashPlan sc tx n h :=
  legacySignatureHashPlan_eq_of_none sc _ tx n h hacp hnone rfl rfl rfl rfl

/-- With SINGLE and without ANYONECANPAY, replacing an output other than output `n` leaves the production plan unchanged. -/
theorem legacySignatureHashPlan_single_set_other_output (sc : Script) (tx : Transaction) (n h : UInt32)
    (hacp : HashType.anyoneCanPay h = false) (hsingle : HashType.isSingle h = true) (i : Nat) (hi : i ≠ n.toNat)
    (y : TxOut) :
    legacySignatureHashPlan sc
        { tx with outputs := ⟨tx.outputs.val.set i y, by simpa using tx.outputs.property⟩ } n h =
      legacySignatureHashPlan sc tx n h :=
  legacySignatureHashPlan_eq_of_single sc _ tx n h hacp hsingle rfl rfl rfl rfl
    (by simp only [List.getElem?_set_ne hi])

end DogeLib.Transaction
