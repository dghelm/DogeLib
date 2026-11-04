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

These are statements about the definitions. They do not say that the definitions match Core. The known answers in `tests/KnownAnswers.lean` compare them with Core's corpus and with preimages derived from Core's source.
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

end DogeLib.Transaction
