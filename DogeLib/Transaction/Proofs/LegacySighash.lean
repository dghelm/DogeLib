module

public import DogeLib.Serialization.Proofs.CountedList
public import DogeLib.Transaction.LegacySighash
public import DogeLib.Transaction.Proofs.Txid

/-!
# Proofs: `Transaction.LegacySighash`

- `legacySignatureHashPlan_eq_fixedDigest_iff` and `legacySignatureHashPlan_eq_hashBytes`: the plan is the fixed digest `legacyOne` exactly when `nIn` is not an input index, or the hash type is SINGLE and `nIn` is not an output index. Otherwise the plan hashes `legacyPreimage`.
- `legacyPreimage_eq`: the preimage is a body that depends on the hash type only through its three flags, then the 4 bytes of the hash type.
- `HashType.flags_eq_of_and`: two hash types that agree on the bits `0x9f` have the same flags.
- `readOp_stop_prefix` and `readOp_stop_nil`: the bytes that a failing `readOp` call passes.
  `readOp_op_append`, for a call that reads an instruction, is in the specification module, with `readOp_rest_length`, because `findAndDelete` needs it to terminate.
- `scanOps_prefix` and `scanOps_eq_of_complete`: the bytes of the instructions that `scanOps` reads, then the bytes of its failing call, start the script. When no instruction parse failed, the instructions' bytes are the whole script.
- `scriptCodeBytes_eq_encode`: when no instruction parse failed and no instruction is `OP_CODESEPARATOR`, the script code is written as its ordinary encoding.
- `LegacyHashPlan.digest_fixedDigest` and `LegacyHashPlan.digest_hashBytes_val`: the digest of each kind of plan.
- `readOp_cons_eq`: one uniform form of `readOp` on a nonempty script, in terms of `lengthFieldWidth` and `pushSize`.
- `readOp_eq_op_iff`: `readOp` reads an instruction exactly when the bytes start with an opcode, its length field and its data.
- `readOp_eq_stop_iff`: `readOp` stops exactly on a short push or on the empty script.
- `readPush_eq_op_iff` and `readPush_eq_stop_iff`: the two results of `readPush`.

These are statements about the definitions. They do not say that the definitions match Core. The known answers in `tests/KnownAnswers/Transaction.lean` compare them with Core's corpus and with preimages derived from Core's source.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-! ## The plan -/

/--
For every script code, transaction, input index and hash type, the plan is the fixed digest `legacyOne` if and only if `nIn` is at least the number of inputs, or the hash type is SINGLE and `nIn` is at least the number of outputs.
-/
theorem legacySignatureHashPlan_eq_fixedDigest_iff (sc : Script) (tx : Transaction) (nIn h : UInt32) :
    legacySignatureHashPlan sc tx nIn h = .fixedDigest legacyOne ↔
      tx.inputs.val.length ≤ nIn.toNat ∨
        (HashType.isSingle h = true ∧ tx.outputs.val.length ≤ nIn.toNat) := by
  unfold legacySignatureHashPlan
  by_cases h1 : tx.inputs.val.length ≤ nIn.toNat
  · simp [h1]
  · by_cases h2 : HashType.isSingle h = true ∧ tx.outputs.val.length ≤ nIn.toNat
    · simp [h1, h2]
    · simp only [h1, ↓reduceIte, h2, false_or, iff_false]
      intro heq
      cases heq

/--
For every script code, transaction, input index and hash type: if `nIn` is an input index, and also an output index when the hash type is SINGLE, then the plan hashes `legacyPreimage`.
-/
theorem legacySignatureHashPlan_eq_hashBytes (sc : Script) (tx : Transaction) (nIn h : UInt32)
    (hIn : nIn.toNat < tx.inputs.val.length)
    (hOut : HashType.isSingle h = true → nIn.toNat < tx.outputs.val.length) :
    legacySignatureHashPlan sc tx nIn h = .hashBytes (legacyPreimage sc tx nIn h) := by
  unfold legacySignatureHashPlan
  have h1 : ¬ tx.inputs.val.length ≤ nIn.toNat := by omega
  have h2 : ¬ (HashType.isSingle h = true ∧ tx.outputs.val.length ≤ nIn.toNat) := by
    intro ⟨hs, hle⟩
    have := hOut hs
    omega
  simp only [h1, ↓reduceIte, h2]

/-! ## The hash type -/

/--
For every script code, transaction, input index and hash type `h`, the preimage is the body for the three flags of `h`, then the 4 little-endian bytes of `h`.
So two hash types with the same flags give preimages that differ at most in their last 4 bytes.
-/
theorem legacyPreimage_eq (sc : Script) (tx : Transaction) (nIn h : UInt32) :
    legacyPreimage sc tx nIn h =
      legacyBody sc tx nIn (HashType.anyoneCanPay h) (HashType.isNone h) (HashType.isSingle h) ++
        Codec.encode h :=
  rfl

/-- For all hash types `h` and `h'` with `h &&& 0x9f = h' &&& 0x9f`, the ANYONECANPAY, NONE and SINGLE flags of `h` and `h'` are equal. -/
theorem HashType.flags_eq_of_and {h h' : UInt32} (heq : h &&& 0x9f = h' &&& 0x9f) :
    HashType.anyoneCanPay h = HashType.anyoneCanPay h' ∧ HashType.isNone h = HashType.isNone h' ∧
      HashType.isSingle h = HashType.isSingle h' := by
  have hm : ∀ (m : UInt32), m &&& 0x9f = m → ∀ x : UInt32, x &&& m = (x &&& 0x9f) &&& m := by
    intro m hm x
    rw [UInt32.and_assoc, UInt32.and_comm 0x9f m, hm]
  have h80 := hm 0x80 (by decide)
  have h1f := hm 0x1f (by decide)
  simp only [HashType.anyoneCanPay, HashType.isNone, HashType.isSingle, sighashAnyoneCanPay]
  rw [h80 h, h80 h', h1f h, h1f h', heq]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Script instructions -/

/-- For all bytes: if `readPush` stops, it stops after `header`. -/
theorem readPush_stop {opcode : UInt8} {header r p : List UInt8} {size : Nat}
    (h : readPush opcode header size r = .stop p) : p = header := by
  unfold readPush at h
  split at h
  · cases h; rfl
  · cases h

/-- For all bytes `bs`: if `readOp` stops, the bytes it passed start `bs`. -/
theorem readOp_stop_prefix {bs p : List UInt8} (h : readOp bs = .stop p) : p <+: bs := by
  match bs with
  | [] => simp [readOp] at h; subst h; exact List.nil_prefix
  | op :: t =>
    simp only [readOp] at h
    split at h
    · rw [readPush_stop h]; exact List.prefix_cons_inj op |>.mpr List.nil_prefix
    · split at h
      · split at h
        · rw [readPush_stop h]; simp_all
        · cases h; exact List.prefix_cons_inj op |>.mpr List.nil_prefix
      · split at h
        · split at h
          · rw [readPush_stop h]; simp_all
          · cases h; exact List.prefix_cons_inj op |>.mpr List.nil_prefix
        · split at h
          · split at h
            · rw [readPush_stop h]; simp_all
            · cases h; exact List.prefix_cons_inj op |>.mpr List.nil_prefix
          · cases h

/-- For all bytes `bs`: `readOp` stops having passed no bytes only on the empty script. A call that fails on a short push passes at least its opcode. -/
theorem readOp_stop_nil {bs : List UInt8} (h : readOp bs = .stop []) : bs = [] := by
  match bs with
  | [] => rfl
  | op :: t =>
    exfalso
    simp only [readOp] at h
    split at h
    · cases readPush_stop h
    · split at h
      · split at h
        · cases readPush_stop h
        · cases h
      · split at h
        · split at h
          · cases readPush_stop h
          · cases h
        · split at h
          · split at h
            · cases readPush_stop h
            · cases h
          · cases h

/-- For all bytes `bs`, the bytes of the instructions that `scanOps` reads, then the bytes that its failing call passed, start `bs`. -/
theorem scanOps_prefix (bs : List UInt8) :
    (scanOps bs).1.flatMap (·.2) ++ (scanOps bs).2 <+: bs := by
  rw [scanOps]
  split
  · rename_i p hp
    simpa using readOp_stop_prefix hp
  · rename_i o b r hr
    have := scanOps_prefix r
    simp only [List.flatMap_cons, List.append_assoc]
    rw [← readOp_op_append hr]
    exact (List.prefix_append_right_inj b).mpr this
termination_by bs.length
decreasing_by exact readOp_rest_length ‹_›

/-- For all bytes `bs`: if no instruction parse failed, the bytes of the instructions that `scanOps` reads are `bs`. -/
theorem scanOps_eq_of_complete (bs : List UInt8) (h : (scanOps bs).2 = []) :
    (scanOps bs).1.flatMap (·.2) = bs := by
  rw [scanOps] at h ⊢
  split
  · rename_i p hp
    rw [hp] at h
    simp only at h
    subst h
    simp [readOp_stop_nil hp]
  · rename_i o b r hr
    rw [hr] at h
    simp only at h ⊢
    rw [List.flatMap_cons, scanOps_eq_of_complete r h, readOp_op_append hr]
termination_by bs.length
decreasing_by exact readOp_rest_length ‹_›

/-- For every script: when no instruction parse failed and no instruction is `OP_CODESEPARATOR`, `scriptCodeBytes` is the ordinary encoding of the script, its CompactSize count and then its bytes. -/
theorem scriptCodeBytes_eq_encode (sc : Script) (hc : (scanOps sc.bytes.val).2 = [])
    (hs : ∀ o ∈ (scanOps sc.bytes.val).1, o.1 ≠ opCodeSeparator) :
    scriptCodeBytes sc = Codec.encode sc := by
  have hkeep : (scanOps sc.bytes.val).1.filter (fun o => o.1 != opCodeSeparator) =
      (scanOps sc.bytes.val).1 :=
    List.filter_eq_self.mpr fun o ho => by simpa using hs o ho
  have hdrop : (scanOps sc.bytes.val).1.filter (fun o => o.1 == opCodeSeparator) = [] :=
    List.filter_eq_nil_iff.mpr fun o ho => by simpa using hs o ho
  change _ = CountedList.encode sc.bytes
  simp only [scriptCodeBytes, CountedList.encode, hkeep, hdrop, List.length_nil, Nat.sub_zero, hc,
    List.append_nil, scanOps_eq_of_complete _ hc, CountedList.encodeElems_uint8]

/-! ## The digest -/

/-- For every 256-bit value `d`, the digest of `fixedDigest d` is `d`. -/
theorem LegacyHashPlan.digest_fixedDigest (d : Hash256) : (LegacyHashPlan.fixedDigest d).digest = d := rfl

/-- For all bytes `p`, the bytes of the digest of `hashBytes p` are the double SHA-256 of `p`. -/
theorem LegacyHashPlan.digest_hashBytes_val (p : List UInt8) :
    (LegacyHashPlan.hashBytes p).digest.val = (Cryptography.Hash.Sha256d.hash p.toByteArray).toList :=
  digestToHash256_val _ (Cryptography.Hash.Sha256d.size_hash _)

/-! ## Characterization of `readOp`

These theorems state `readOp` in terms of `lengthFieldWidth` and `pushSize`, without its nested cases.
`DogeLib.Script.Proofs.Instruction` uses them for the cursor reader of the Script interpreter.
-/

/-- For every decidable condition `c` that fails, `if c then a else b` is `b`. -/
private theorem ite_neg_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- For every decidable condition `c` that holds, `if c then a else b` is `a`. -/
private theorem ite_pos_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-! ## Opcode classes -/

/-- For every opcode above `OP_PUSHDATA4`, the length field has width 0. -/
theorem lengthFieldWidth_of_gt {op : UInt8} (h : 0x4e < op) : lengthFieldWidth op = 0 := by
  have h1 : op ≠ 0x4c := by rintro rfl; exact absurd h (by decide)
  have h2 : op ≠ 0x4d := by rintro rfl; exact absurd h (by decide)
  have h3 : op ≠ 0x4e := by rintro rfl; exact absurd h (by decide)
  simp [lengthFieldWidth, h1, h2, h3]

/-- For every direct push opcode, below `OP_PUSHDATA1`, the length field has width 0. -/
theorem lengthFieldWidth_of_lt {op : UInt8} (h : op < 0x4c) : lengthFieldWidth op = 0 := by
  have h1 : op ≠ 0x4c := by rintro rfl; exact absurd h (by decide)
  have h2 : op ≠ 0x4d := by rintro rfl; exact absurd h (by decide)
  have h3 : op ≠ 0x4e := by rintro rfl; exact absurd h (by decide)
  simp [lengthFieldWidth, h1, h2, h3]

/-- For every opcode above `OP_PUSHDATA4` and every length field, the data size is 0. -/
theorem pushSize_of_gt {op : UInt8} (h : 0x4e < op) (lf : List UInt8) : pushSize op lf = 0 := by
  have h1 : ¬ op < 0x4c := fun h' => absurd (UInt8.lt_trans h' (UInt8.lt_trans (by decide) h))
    (UInt8.lt_irrefl _)
  have h2 : ¬ op ≤ 0x4e := fun h' => absurd (UInt8.lt_of_lt_of_le h h') (UInt8.lt_irrefl _)
  simp [pushSize, h1, h2]

/-! ## `readPush` -/

/-- For all inputs: `readPush` reads an instruction if and only if `size` bytes follow, and then the instruction is `header` and those bytes. -/
theorem readPush_eq_op_iff {opcode o : UInt8} {header r b rest : List UInt8} {size : Nat} :
    readPush opcode header size r = .op o b rest ↔
      size ≤ r.length ∧ o = opcode ∧ b = header ++ r.take size ∧ rest = r.drop size := by
  unfold readPush
  split
  · simp only [reduceCtorEq, false_iff]
    omega
  · constructor
    · intro h; cases h; exact ⟨by omega, rfl, rfl, rfl⟩
    · rintro ⟨-, rfl, rfl, rfl⟩; rfl

/-- For all inputs: `readPush` stops if and only if fewer than `size` bytes follow, and then it passes `header`. -/
theorem readPush_eq_stop_iff {opcode : UInt8} {header r p : List UInt8} {size : Nat} :
    readPush opcode header size r = .stop p ↔ r.length < size ∧ p = header := by
  unfold readPush
  split
  · constructor
    · intro h; cases h; exact ⟨by omega, rfl⟩
    · rintro ⟨-, rfl⟩; rfl
  · simp only [reduceCtorEq, false_iff]
    omega

/-! ## A uniform form of `readOp` -/

/--
For every opcode `op` and bytes `t`, `readOp (op :: t)` in one form for all opcodes.
A push opcode reads a length field of `lengthFieldWidth op` bytes and then `pushSize op` bytes of data.
It stops after the opcode when the length field is short.
Every other opcode is one byte.
-/
theorem readOp_cons_eq (op : UInt8) (t : List UInt8) :
    readOp (op :: t) =
      if op ≤ 0x4e then
        if t.length < lengthFieldWidth op then .stop [op]
        else readPush op (op :: t.take (lengthFieldWidth op))
          (pushSize op (t.take (lengthFieldWidth op))) (t.drop (lengthFieldWidth op))
      else .op op [op] t := by
  by_cases hlt : op < 0x4c
  · have hle : op ≤ 0x4e := UInt8.le_of_lt (UInt8.lt_trans hlt (by decide))
    simp [readOp, hlt, hle, lengthFieldWidth_of_lt hlt, pushSize]
  · by_cases h4c : op = 0x4c
    · subst h4c
      cases t with
      | nil => rfl
      | cons b r => simp [readOp, lengthFieldWidth, pushSize, leValue]
    · by_cases h4d : op = 0x4d
      · subst h4d
        match t with
        | [] => rfl
        | [_] => rfl
        | b0 :: b1 :: r => simp [readOp, lengthFieldWidth, pushSize, leValue]; omega
      · by_cases h4e : op = 0x4e
        · subst h4e
          match t with
          | [] => rfl
          | [_] => rfl
          | [_, _] => rfl
          | [_, _, _] => rfl
          | b0 :: b1 :: b2 :: b3 :: r =>
            simp [readOp, lengthFieldWidth, pushSize, leValue]
            split
            · omega
            · congr 1; omega
        · have hgt : 0x4e < op := by
            have : ¬ op.toNat < 0x4c := fun h => hlt (UInt8.lt_iff_toNat_lt.mpr h)
            have h1 : op.toNat ≠ 0x4c := fun h => h4c (UInt8.toNat_inj.mp h)
            have h2 : op.toNat ≠ 0x4d := fun h => h4d (UInt8.toNat_inj.mp h)
            have h3 : op.toNat ≠ 0x4e := fun h => h4e (UInt8.toNat_inj.mp h)
            exact UInt8.lt_iff_toNat_lt.mpr (by simp; omega)
          have hnle : ¬ op ≤ 0x4e := fun h => absurd (UInt8.lt_of_lt_of_le hgt h) (UInt8.lt_irrefl _)
          simp [readOp, hlt, h4c, h4d, h4e, hnle]

/-- For every byte that is not at most `OP_PUSHDATA4`, the byte is above it. -/
private theorem gt_of_not_le {op : UInt8} (h : ¬ op ≤ 0x4e) : 0x4e < op :=
  UInt8.lt_iff_toNat_lt.mpr (by
    have : ¬ op.toNat ≤ (0x4e : UInt8).toNat := fun h' => h (UInt8.le_iff_toNat_le.mpr h')
    omega)

/-! ## `readOp` against the instruction encoding -/

/--
For all bytes `bs`, `o`, `b` and `r`: `readOp bs` returns `.op o b r` if and only if two conditions hold.
The bytes `bs` are `b ++ r`, and `b` is `o :: lf ++ data`.
The length field `lf` has the width that `o` requires, and `data` has the size that `o` and `lf` give.
-/
theorem readOp_eq_op_iff {bs : List UInt8} {o : UInt8} {b r : List UInt8} :
    readOp bs = .op o b r ↔
      ∃ lf data, lf.length = lengthFieldWidth o ∧ data.length = pushSize o lf ∧
        b = o :: lf ++ data ∧ bs = b ++ r := by
  constructor
  · intro h
    match bs with
    | [] => simp [readOp] at h
    | op :: t =>
      rw [readOp_cons_eq] at h
      split at h
      · split at h
        · cases h
        · rename_i hw
          obtain ⟨hn, rfl, rfl, rfl⟩ := readPush_eq_op_iff.mp h
          refine ⟨t.take (lengthFieldWidth o),
            (t.drop (lengthFieldWidth o)).take (pushSize o (t.take (lengthFieldWidth o))),
            ?_, ?_, rfl, ?_⟩
          · simp only [List.length_take]; omega
          · simp only [List.length_take]; omega
          · simp only [List.cons_append, List.append_assoc]
            rw [List.take_append_drop, List.take_append_drop]
      · rename_i hle
        cases h
        have hgt := gt_of_not_le hle
        exact ⟨[], [], by simp [lengthFieldWidth_of_gt hgt], by simp [pushSize_of_gt hgt],
          rfl, rfl⟩
  · rintro ⟨lf, data, hlf, hdata, rfl, rfl⟩
    rw [List.cons_append, List.cons_append, readOp_cons_eq]
    by_cases hle : o ≤ 0x4e
    · simp only [hle, ↓reduceIte, ← hlf, List.append_assoc, List.take_left, List.drop_left,
        List.length_append]
      rw [ite_neg_eq (by omega)]
      exact readPush_eq_op_iff.mpr ⟨by simp; omega, rfl, by simp [← hdata],
        by simp [← hdata]⟩
    · have hgt := gt_of_not_le hle
      have hl : lf = [] := List.eq_nil_of_length_eq_zero (by rw [hlf, lengthFieldWidth_of_gt hgt])
      have hd : data = [] := List.eq_nil_of_length_eq_zero (by rw [hdata, pushSize_of_gt hgt])
      subst hl hd
      simp [hle]

/--
For all bytes `bs` and `p`: `readOp bs` returns `.stop p` if and only if one of two cases holds.
Either `bs` and `p` are empty, or `bs` starts with a push opcode `op` whose length field or data is short.
When the length field is short, `p` is the opcode. When the data is short, `p` is the opcode and the length field.
-/
theorem readOp_eq_stop_iff {bs p : List UInt8} :
    readOp bs = .stop p ↔
      (bs = [] ∧ p = []) ∨
      ∃ op t, bs = op :: t ∧ op ≤ 0x4e ∧
        ((t.length < lengthFieldWidth op ∧ p = [op]) ∨
         (lengthFieldWidth op ≤ t.length ∧
           (t.drop (lengthFieldWidth op)).length < pushSize op (t.take (lengthFieldWidth op)) ∧
           p = op :: t.take (lengthFieldWidth op))) := by
  match bs with
  | [] => simp [readOp, eq_comm]
  | op :: t =>
    rw [readOp_cons_eq]
    simp only [reduceCtorEq, false_and, List.cons.injEq, false_or]
    constructor
    · intro h
      refine ⟨op, t, ⟨rfl, rfl⟩, ?_⟩
      split at h
      · rename_i hle
        refine ⟨hle, ?_⟩
        split at h
        · cases h; exact Or.inl ⟨by omega, rfl⟩
        · obtain ⟨hn, rfl⟩ := readPush_eq_stop_iff.mp h
          exact Or.inr ⟨by omega, hn, rfl⟩
      · cases h
    · rintro ⟨op', t', ⟨rfl, rfl⟩, hle, h⟩
      simp only [hle, ↓reduceIte]
      rcases h with ⟨hw, rfl⟩ | ⟨hw, hn, rfl⟩
      · rw [ite_pos_eq hw]
      · rw [ite_neg_eq (by omega)]
        exact readPush_eq_stop_iff.mpr ⟨hn, rfl⟩


end DogeLib.Transaction
