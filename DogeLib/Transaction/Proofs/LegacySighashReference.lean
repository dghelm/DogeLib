module

public import DogeLib.Transaction.LegacySighashReference
public import DogeLib.Transaction.Proofs.LegacySighash

/-!
# Proofs: `Transaction.LegacySighashReference`

The main theorem, `legacySignatureHashPlan_eq_reference`, says that the production plan and the transformation plan are equal, under three hypotheses:

- No instruction of the script code fails to parse: `(scanOps sc.bytes.val).2 = []`.
- The transaction has fewer than 2^32 inputs.
- The transaction has fewer than 2^32 outputs.

`legacySignatureHash_eq_reference` gives the equality of the digests.
The equality holds for every input index and every hash type, including the two cases with the fixed digest.

The supporting results:

- `findAndDelete_separator`: for a script whose instructions all parse, removing `OP_CODESEPARATOR` keeps the bytes of the other instructions, and counts the separators.
- `encode_referenceScriptCode`: then the encoding of the script code of the copy is `scriptCodeBytes`.
- `encode_referenceInputs` and `encode_referenceOutputs`: the encodings of the inputs and outputs of the copy are the bytes that the serializer writes.

The hypothesis on the script code is needed. `legacyPlans_differ_shortPush` shows a script, `4c 05 aa`, on which the two plans differ.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-! ## Encodings of the structures -/

/-- For every input, its encoding is its outpoint, its script and its sequence. -/
theorem TxIn.encode_eq (i : TxIn) :
    Codec.encode i = Codec.encode i.prevout ++ (Codec.encode i.scriptSig ++ Codec.encode i.sequence) := rfl

/-- For every transaction, its encoding is its version, inputs, outputs and lock time. -/
theorem Transaction.encode_eq (tx : Transaction) :
    Codec.encode tx = Codec.encode tx.version ++ (CountedList.encode tx.inputs ++
      (CountedList.encode tx.outputs ++ Codec.encode tx.lockTime)) := rfl

/-- For every script, its encoding is its CompactSize length, then its bytes. -/
theorem Script.encode_eq (s : Script) :
    Codec.encode s = CompactSize.encode (UInt64.ofNat s.bytes.val.length) ++ s.bytes.val := by
  change CountedList.encode s.bytes = _
  rw [CountedList.encode, CountedList.encodeElems_uint8]

/-- For every list, the elements' encodings, one after the other, are the flattened list of encodings. -/
theorem CountedList.encodeElems_eq_flatten {α : Type} [Codec α] (l : List α) :
    CountedList.encodeElems l = (l.map Codec.encode).flatten := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [CountedList.encodeElems, ih]

/-! ## One step of each loop -/

/-- `readOp` reads `OP_CODESEPARATOR` as a one-byte instruction. -/
theorem readOp_separator (t : List UInt8) :
    readOp (opCodeSeparator :: t) = .op opCodeSeparator [opCodeSeparator] t := rfl

/-- For all bytes: the opcode of an instruction that `readOp` reads is the first byte. -/
theorem readOp_cons_opcode {x o : UInt8} {t b r : List UInt8} (h : readOp (x :: t) = .op o b r) : o = x := by
  have push : ∀ (hd : List UInt8) (n : Nat) (t' : List UInt8), readPush x hd n t' = .op o b r → o = x := by
    intro hd n t' h
    unfold readPush at h
    split at h
    · cases h
    · cases h; rfl
  simp only [readOp] at h
  split at h
  · exact push _ _ _ h
  · split at h
    · split at h
      · exact push _ _ _ h
      · cases h
    · split at h
      · split at h
        · exact push _ _ _ h
        · cases h
      · split at h
        · split at h
          · exact push _ _ _ h
          · cases h
        · cases h; rfl

/-- `scanOps` after an instruction. -/
theorem scanOps_of_op {bs : List UInt8} {o : UInt8} {b r : List UInt8} (h : readOp bs = .op o b r) :
    scanOps bs = ((o, b) :: (scanOps r).1, (scanOps r).2) := by
  rw [scanOps]
  split
  · rename_i p h'
    rw [h] at h'; cases h'
  · rename_i o' b' r' h'
    rw [h] at h'; cases h'; rfl

/-- `scanOps` after a failing call. -/
theorem scanOps_of_stop {bs p : List UInt8} (h : readOp bs = .stop p) : scanOps bs = ([], p) := by
  rw [scanOps]
  split
  · rename_i p' h'
    rw [h] at h'; cases h'; rfl
  · rename_i o' b' r' h'
    rw [h] at h'; cases h'

/-- `dropMatches` on the empty input. -/
theorem dropMatches_nil (b : List UInt8) : dropMatches b [] = ([], 0) := by
  rw [dropMatches]
  split
  · rename_i h
    exact absurd (List.isPrefixOf_iff_prefix.mp h.2) (by simpa using h.1)
  · rfl

/-- `dropMatches` with the pattern `OP_CODESEPARATOR`, when the input starts with it. -/
theorem dropMatches_separator_cons (t : List UInt8) :
    dropMatches [opCodeSeparator] (opCodeSeparator :: t) =
      ((dropMatches [opCodeSeparator] t).1, (dropMatches [opCodeSeparator] t).2 + 1) := by
  rw [dropMatches]
  split
  · rfl
  · rename_i h
    exact absurd ⟨by simp, by simp⟩ h

/-- `dropMatches` with the pattern `OP_CODESEPARATOR`, when the input starts with another byte. -/
theorem dropMatches_separator_of_ne {x : UInt8} (t : List UInt8) (hx : x ≠ opCodeSeparator) :
    dropMatches [opCodeSeparator] (x :: t) = (x :: t, 0) := by
  rw [dropMatches]
  split
  · rename_i h
    have := h.2
    simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at this
    exact absurd this.1.symm hx
  · rfl

/-- `findAndDeleteLoop` when the call after the matches reads an instruction. -/
theorem findAndDeleteLoop_of_op {b rest : List UInt8} {o : UInt8} {bytes r : List UInt8}
    (h : readOp (dropMatches b rest).1 = .op o bytes r) :
    findAndDeleteLoop b rest = (bytes ++ (findAndDeleteLoop b r).1, (dropMatches b rest).2 + (findAndDeleteLoop b r).2) := by
  rw [findAndDeleteLoop]
  split
  · rename_i o' b' r' h'
    rw [h] at h'; cases h'; rfl
  · rename_i p' h'
    rw [h] at h'; cases h'

/-- `findAndDeleteLoop` when the call after the matches fails. -/
theorem findAndDeleteLoop_of_stop {b rest p : List UInt8} (h : readOp (dropMatches b rest).1 = .stop p) :
    findAndDeleteLoop b rest = dropMatches b rest := by
  rw [findAndDeleteLoop]
  split
  · rename_i o' b' r' h'
    rw [h] at h'; cases h'
  · rfl

/-- A leading `OP_CODESEPARATOR` adds one to the count of `findAndDeleteLoop` and changes nothing else. -/
theorem findAndDeleteLoop_separator_cons (t : List UInt8) :
    findAndDeleteLoop [opCodeSeparator] (opCodeSeparator :: t) =
      ((findAndDeleteLoop [opCodeSeparator] t).1, (findAndDeleteLoop [opCodeSeparator] t).2 + 1) := by
  have hd := dropMatches_separator_cons t
  cases hr : readOp (dropMatches [opCodeSeparator] t).1 with
  | op o bytes r =>
    have h1 : readOp (dropMatches [opCodeSeparator] (opCodeSeparator :: t)).1 = .op o bytes r := by
      rw [hd]; exact hr
    rw [findAndDeleteLoop_of_op h1, findAndDeleteLoop_of_op hr, hd]
    simp only [Prod.mk.injEq, true_and]
    omega
  | stop p =>
    have h1 : readOp (dropMatches [opCodeSeparator] (opCodeSeparator :: t)).1 = .stop p := by
      rw [hd]; exact hr
    rw [findAndDeleteLoop_of_stop h1, findAndDeleteLoop_of_stop hr, hd]

/-! ## Removing the separators -/

/-- The bytes of the instructions other than `OP_CODESEPARATOR`. -/
abbrev keptBytes (ops : List (UInt8 × List UInt8)) : List UInt8 :=
  (ops.filter fun o => o.1 != opCodeSeparator).flatMap (·.2)

/-- The number of `OP_CODESEPARATOR` instructions. -/
abbrev separatorCount (ops : List (UInt8 × List UInt8)) : Nat :=
  (ops.filter fun o => o.1 == opCodeSeparator).length

/-- For every script whose instructions all parse, the loop of `FindAndDelete(OP_CODESEPARATOR)` keeps the bytes of the other instructions and counts the separator instructions. -/
theorem findAndDeleteLoop_separator (s : List UInt8) (h : (scanOps s).2 = []) :
    findAndDeleteLoop [opCodeSeparator] s = (keptBytes (scanOps s).1, separatorCount (scanOps s).1) := by
  match s with
  | [] =>
    have hs : readOp (dropMatches [opCodeSeparator] []).1 = .stop [] := by rw [dropMatches_nil]; rfl
    rw [findAndDeleteLoop_of_stop hs, dropMatches_nil, scanOps_of_stop (p := []) rfl]
    rfl
  | x :: t =>
    by_cases hx : x = opCodeSeparator
    · subst hx
      rw [scanOps_of_op (readOp_separator t)] at h ⊢
      rw [findAndDeleteLoop_separator_cons, findAndDeleteLoop_separator t h]
      simp [keptBytes, separatorCount]
    · cases hr : readOp (x :: t) with
      | op o b r =>
        have ho : o = x := readOp_cons_opcode hr
        rw [scanOps_of_op hr] at h ⊢
        have h1 : readOp (dropMatches [opCodeSeparator] (x :: t)).1 = .op o b r := by
          rw [dropMatches_separator_of_ne t hx]; exact hr
        rw [findAndDeleteLoop_of_op h1, dropMatches_separator_of_ne t hx, findAndDeleteLoop_separator r h]
        subst ho
        simp [keptBytes, separatorCount, hx]
      | stop p =>
        rw [scanOps_of_stop hr] at h
        simp only at h
        subst h
        exact absurd (readOp_stop_nil hr) (by simp)
termination_by s.length
decreasing_by
  all_goals first
    | exact readOp_rest_length hr
    | simp

/-- For every script whose instructions all parse, the kept bytes and the separators together have the length of the script. -/
theorem keptBytes_length_add (s : List UInt8) (h : (scanOps s).2 = []) :
    (keptBytes (scanOps s).1).length + separatorCount (scanOps s).1 = s.length := by
  match s with
  | [] =>
    rw [scanOps_of_stop (p := []) rfl]
    rfl
  | x :: t =>
    by_cases hx : x = opCodeSeparator
    · subst hx
      rw [scanOps_of_op (readOp_separator t)] at h ⊢
      have := keptBytes_length_add t h
      simp only [keptBytes, separatorCount] at this ⊢
      simp only [List.filter_cons, bne_self_eq_false, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
        List.length_cons]
      omega
    · cases hr : readOp (x :: t) with
      | op o b r =>
        have ho : o = x := readOp_cons_opcode hr
        rw [scanOps_of_op hr] at h ⊢
        have := keptBytes_length_add r h
        have happ := congrArg List.length (readOp_op_append hr)
        subst ho
        simp only [List.length_append, List.length_cons] at happ
        simp [keptBytes, separatorCount, hx] at this ⊢
        omega
      | stop p =>
        rw [scanOps_of_stop hr] at h
        simp only at h
        subst h
        exact absurd (readOp_stop_nil hr) (by simp)
termination_by s.length
decreasing_by
  all_goals first
    | exact readOp_rest_length hr
    | simp

/-- For every script whose instructions all parse, `FindAndDelete(OP_CODESEPARATOR)` keeps the bytes of the instructions other than `OP_CODESEPARATOR`. -/
theorem findAndDelete_separator (s : List UInt8) (h : (scanOps s).2 = []) :
    (findAndDelete s [opCodeSeparator]).1 = keptBytes (scanOps s).1 := by
  unfold findAndDelete
  simp only [List.cons_ne_nil, ↓reduceIte, findAndDeleteLoop_separator s h]
  split
  · rename_i h0
    have hlen := keptBytes_length_add s h
    have hall : (scanOps s).1.filter (fun o => o.1 != opCodeSeparator) = (scanOps s).1 := by
      rw [List.filter_eq_self]
      intro o ho
      have : o ∉ (scanOps s).1.filter (fun o => o.1 == opCodeSeparator) := by
        rw [List.length_eq_zero_iff] at h0
        simp [h0]
      simp only [List.mem_filter, beq_iff_eq, not_and] at this
      simpa using this ho
    simp only [keptBytes, hall]
    exact (scanOps_eq_of_complete s h).symm
  · rfl

/-- For every script code whose instructions all parse, the encoding of the script code of the copy is `scriptCodeBytes`. -/
theorem encode_referenceScriptCode (sc : Script) (h : (scanOps sc.bytes.val).2 = []) :
    Codec.encode (referenceScriptCode sc) = scriptCodeBytes sc := by
  rw [Script.encode_eq]
  have hk : (referenceScriptCode sc).bytes.val = keptBytes (scanOps sc.bytes.val).1 :=
    findAndDelete_separator _ h
  have hlen := keptBytes_length_add _ h
  rw [hk]
  simp only [scriptCodeBytes, h, List.append_nil]
  congr 3
  simp only [keptBytes, separatorCount] at hlen ⊢
  omega

/-! ## Inputs and outputs -/

/-- For every counted list, its encoding is the CompactSize length of the list, then the encodings of its elements. -/
theorem CountedList.encode_eq_flatten {α : Type} [Codec α] (c : CountedList α) :
    CountedList.encode c = CompactSize.encode (UInt64.ofNat c.val.length) ++ (c.val.map Codec.encode).flatten := by
  rw [CountedList.encode, CountedList.encodeElems_eq_flatten]

/--
Hypothesis: every instruction of the script code parses.
Then for every list of inputs, index `n` and flag `z`, the copy's inputs before the ANYONECANPAY step encode as `legacyInputBytes`.
-/
theorem referenceSequencedInputs_map_encode (sc : Script) (hParse : (scanOps sc.bytes.val).2 = [])
    (inputs : List TxIn) (n : Nat) (z : Bool) :
    (referenceSequencedInputs (referenceScriptCode sc) inputs n z).map Codec.encode =
      inputs.mapIdx (legacyInputBytes sc n z) := by
  have hcode := encode_referenceScriptCode sc hParse
  apply List.ext_getElem
  · unfold referenceSequencedInputs
    split <;> simp
  · intro i h1 h2
    simp only [List.length_mapIdx] at h2
    simp only [List.getElem_map, List.getElem_mapIdx]
    unfold referenceSequencedInputs legacyInputBytes
    by_cases hi : i = n
    · subst hi
      cases z <;> simp [TxIn.encode_eq, hcode]
    · have hn : n ≠ i := fun h => hi h.symm
      cases z <;> simp [TxIn.encode_eq, hi, hn]

/-- For every nonempty list, setting its first element to `x` and keeping one element gives `[x]`. -/
theorem take_one_set_zero {α : Type} {l : List α} (x : α) (h : l ≠ []) : (l.set 0 x).take 1 = [x] := by
  cases l with
  | nil => exact absurd rfl h
  | cons y ys => rfl

/--
Hypotheses: every instruction of the script code parses, and the transaction has fewer than 2^32 inputs.
Then for every input index `nIn` and both flags, the inputs of the copy encode as `legacyInputsBytes`.
-/
theorem encode_referenceInputs (sc : Script) (hParse : (scanOps sc.bytes.val).2 = []) (tx : Transaction)
    (nIn : UInt32) (z a : Bool) (hLen : tx.inputs.val.length < 2 ^ 32)
    (hn : nIn.toNat < tx.inputs.val.length) :
    CountedList.encode (CountedList.ofLengthLe
        (referenceInputs (referenceScriptCode sc) tx.inputs.val nIn.toNat z a) tx.inputs
        (referenceInputs_length_le _ _ _ _ _)) =
      legacyInputsBytes sc tx nIn a z := by
  have hmap := referenceSequencedInputs_map_encode sc hParse tx.inputs.val nIn.toNat z
  have hslen : (referenceSequencedInputs (referenceScriptCode sc) tx.inputs.val nIn.toNat z).length =
      tx.inputs.val.length := by
    have := congrArg List.length hmap
    simpa using this
  rw [CountedList.encode_eq_flatten]
  unfold legacyInputsBytes referenceInputs CountedList.ofLengthLe
  cases a with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, hmap, hslen, Nat.mod_eq_of_lt hLen, List.take_length]
  | true =>
    simp only [↓reduceIte]
    have hget := congrArg (·[nIn.toNat]?) hmap
    simp only [List.getElem?_map, List.getElem?_mapIdx] at hget
    rw [List.getElem?_eq_getElem (by omega)] at hget ⊢
    rw [List.getElem?_eq_getElem hn] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have hne : 0 < (referenceSequencedInputs (referenceScriptCode sc) tx.inputs.val nIn.toNat z).length := by
      omega
    have hdrop : (tx.inputs.val.drop nIn.toNat).take 1 = [tx.inputs.val[nIn.toNat]] := by
      rw [List.drop_eq_getElem_cons hn]; rfl
    simp only [hdrop, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [take_one_set_zero _ (List.ne_nil_of_length_pos hne)]
    simp only [List.length_singleton, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, hget]
    rfl

/--
Hypotheses: the transaction has fewer than 2^32 outputs, and `nIn` is an output index when `single` holds.
Then for both flags, the outputs of the copy encode as `legacyOutputsBytes`.
-/
theorem encode_referenceOutputs (tx : Transaction) (nIn : UInt32) (none single : Bool)
    (hLen : tx.outputs.val.length < 2 ^ 32) (hSingle : single = true → nIn.toNat < tx.outputs.val.length) :
    CountedList.encode (CountedList.ofLengthLe
        (referenceOutputs tx.outputs.val nIn.toNat none single) tx.outputs
        (referenceOutputs_length_le _ _ _ _)) =
      legacyOutputsBytes tx nIn none single := by
  rw [CountedList.encode_eq_flatten]
  unfold legacyOutputsBytes referenceOutputs CountedList.ofLengthLe
  cases none with
  | true => rfl
  | false =>
    cases single with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.mod_eq_of_lt hLen, List.take_length,
        CountedList.encodeElems_eq_flatten]
    | true =>
      have hn := hSingle rfl
      have hmod : (nIn.toNat + 1) % 2 ^ 32 = nIn.toNat + 1 := Nat.mod_eq_of_lt (by omega)
      have htl : (tx.outputs.val.take (nIn.toNat + 1)).length = nIn.toNat + 1 := by
        simp only [List.length_take]; omega
      simp only [Bool.false_eq_true, ↓reduceIte, hmod, List.length_mapIdx, htl]
      congr 2
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.length_map, List.length_mapIdx, htl] at h1
        simp only [List.getElem_map, List.getElem_mapIdx]
        by_cases hi : i = nIn.toNat
        · subst hi; simp
        · have : i < nIn.toNat := by omega
          simp [this, hi]

/-! ## The plans -/

/--
Hypotheses: every instruction of the script code parses, and the transaction has fewer than 2^32 inputs and fewer than 2^32 outputs.
Then for every input index and every hash type, the production plan equals the plan of the transformation reference.
-/
theorem legacySignatureHashPlan_eq_reference (sc : Script) (tx : Transaction) (nIn h : UInt32)
    (hParse : (scanOps sc.bytes.val).2 = []) (hIn : tx.inputs.val.length < 2 ^ 32)
    (hOut : tx.outputs.val.length < 2 ^ 32) :
    legacySignatureHashPlan sc tx nIn h = legacyReferencePlan sc tx nIn h := by
  unfold legacySignatureHashPlan legacyReferencePlan
  split
  · rfl
  · rename_i h1
    split
    · rfl
    · rename_i h2
      congr 1
      rw [legacyPreimage_eq, Transaction.encode_eq]
      unfold legacyBody referenceTransaction
      simp only [List.append_assoc]
      rw [encode_referenceInputs sc hParse tx nIn _ _ hIn (by omega),
        encode_referenceOutputs tx nIn _ _ hOut (fun hs => by
          have := h2
          simp only [hs, true_and, Nat.not_le] at this
          exact this)]

/-- Under the hypotheses of `legacySignatureHashPlan_eq_reference`, the two digests are equal. -/
theorem legacySignatureHash_eq_reference (sc : Script) (tx : Transaction) (nIn h : UInt32)
    (hParse : (scanOps sc.bytes.val).2 = []) (hIn : tx.inputs.val.length < 2 ^ 32)
    (hOut : tx.outputs.val.length < 2 ^ 32) :
    legacySignatureHash sc tx nIn h = (legacyReferencePlan sc tx nIn h).digest := by
  rw [legacySignatureHash, legacySignatureHashPlan_eq_reference sc tx nIn h hParse hIn hOut]

/-! ## A script on which the definitions differ -/

/-- The script `4c 05 aa`: `OP_PUSHDATA1` of 5 bytes, with only 1 byte of data. -/
def shortPushScript : Script := ⟨⟨[0x4c, 0x05, 0xaa], by decide⟩⟩

/--
On the script `4c 05 aa`, the serializer writes `03 4c 05`: the count of the whole script, then the bytes up to the cursor of the failed `GetOp`.
The transformation keeps the whole script, so its encoding is `03 4c 05 aa`.
So the hypothesis `hParse` of `legacySignatureHashPlan_eq_reference` cannot be dropped.
-/
theorem legacyPlans_differ_shortPush :
    scriptCodeBytes shortPushScript = [0x03, 0x4c, 0x05] ∧
      Codec.encode (referenceScriptCode shortPushScript) = [0x03, 0x4c, 0x05, 0xaa] := by
  have hstop : readOp [0x4c, 0x05, 0xaa] = .stop [0x4c, 0x05] := rfl
  have hscan : scanOps [0x4c, 0x05, 0xaa] = ([], [0x4c, 0x05]) := scanOps_of_stop hstop
  have hloop : findAndDeleteLoop [opCodeSeparator] [0x4c, 0x05, 0xaa] = ([0x4c, 0x05, 0xaa], 0) := by
    have hd := dropMatches_separator_of_ne [0x05, 0xaa] (x := 0x4c) (by decide)
    rw [findAndDeleteLoop_of_stop (p := [0x4c, 0x05]) (by rw [hd]; exact hstop), hd]
  constructor
  · simp only [scriptCodeBytes, shortPushScript, hscan]
    rfl
  · rw [Script.encode_eq]
    simp only [referenceScriptCode, CountedList.ofLengthLe, shortPushScript, findAndDelete, hloop]
    rfl

end DogeLib.Transaction
