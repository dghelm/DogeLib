module

public import DogeLib.Script.SignatureCode
public import DogeLib.Script.Proofs.Instruction
public import DogeLib.Transaction.Proofs.LegacySighashReference
public import DogeLib.Transaction.Proofs.ScanOps

/-!
# Proofs: `Script.SignatureCode`

Push encodings, Core's visited deletion boundaries and effective script code.
The traversal describes boundaries after preceding deletions, rather than boundaries of the original input.
A single pass can create a match across retained pieces, so the result need not be free of matches.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-- For every width and number, a push length field has exactly that width. -/
theorem pushLengthBytes_length (w n : Nat) : (pushLengthBytes w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [pushLengthBytes, ih]

/-- For a number below `256^w`, its `w` push length bytes have that little-endian value. -/
theorem leValue_pushLengthBytes (w n : Nat) (h : n < 256 ^ w) :
    leValue (pushLengthBytes w n) = n := by
  induction w generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    subst n
    rfl
  | succ w ih =>
    have hn : n / 256 < 256 ^ w := by rw [Nat.pow_succ] at h; omega
    simp only [pushLengthBytes, leValue, Nat.toUInt8, UInt8.toNat_ofNat',
      Nat.reducePow, ih _ hn]
    omega

/-- Every payload shorter than 2^32 bytes has a push header with the required width and exact payload size. -/
theorem pushHeader_encoding (data : List UInt8) (h : data.length < 2^32) :
    ∃ o lf, pushHeader data.length = o :: lf ∧ InstructionEncoding o lf data := by
  unfold pushHeader
  split
  · rename_i hn
    have hv : data.length.toUInt8.toNat = data.length := by
      simp [Nat.toUInt8, Nat.mod_eq_of_lt (show data.length < 256 by omega)]
    have ho : data.length.toUInt8 < (0x4c : UInt8) := by
      change data.length.toUInt8.toNat < 76
      omega
    exact ⟨_, [], rfl, by
      simp [InstructionEncoding, lengthFieldWidth_of_lt ho, pushSize, ho, hv]⟩
  · split
    · rename_i hn
      refine ⟨0x4c, pushLengthBytes 1 data.length, rfl, ?_⟩
      constructor
      · simp [pushLengthBytes_length, lengthFieldWidth]
      · simp [pushSize, leValue_pushLengthBytes 1 data.length (by omega)]
    · split
      · rename_i hn
        refine ⟨0x4d, pushLengthBytes 2 data.length, rfl, ?_⟩
        constructor
        · simp [pushLengthBytes_length, lengthFieldWidth]
        · simp [pushSize, leValue_pushLengthBytes 2 data.length (by omega)]
      · refine ⟨0x4e, pushLengthBytes 4 data.length, rfl, ?_⟩
        constructor
        · simp [pushLengthBytes_length, lengthFieldWidth]
        · simp [pushSize, leValue_pushLengthBytes 4 data.length (by simpa using h)]

/--
For every payload shorter than 2^32 bytes and every tail, the reader consumes its push encoding as one instruction.
It pushes exactly the payload and leaves the tail unread.
-/
theorem readInstruction_pushEncoding (data tail : List UInt8) (h : data.length < 2^32) :
    readInstruction (pushEncoding data ++ tail) 0 =
      .instruction ⟨(pushEncoding data).head!, pushEncoding data, data,
        (pushEncoding data).length⟩ := by
  obtain ⟨o, lf, hh, he⟩ := pushHeader_encoding data h
  have hb : pushEncoding data = o :: lf ++ data := by simp [pushEncoding, hh]
  have hhead : (pushEncoding data).head! = o := by rw [hb]; rfl
  apply readInstruction_eq_instruction_iff.mpr
  exact ⟨lf, tail, by simpa [hhead] using he, by simpa [hhead] using hb,
    by simp, by simp⟩

/-- For every script, an empty deletion pattern leaves its bytes and returns zero. -/
theorem findAndDelete_empty (s : List UInt8) : Transaction.findAndDelete s [] = (s, 0) := by
  simp [Transaction.findAndDelete]

/--
For all patterns and inputs, the inner loop removes a prefix consisting of exactly its reported number of pattern copies.
-/
theorem dropMatches_decomposition (b s : List UInt8) :
    s = (List.replicate (dropMatches b s).2 b).flatten ++ (dropMatches b s).1 := by
  rw [dropMatches]
  split
  · rename_i h
    have ih := dropMatches_decomposition b (s.drop b.length)
    have hp := List.isPrefixOf_iff_prefix.mp h.2
    obtain ⟨t, ht⟩ := hp
    have hs : s = b ++ s.drop b.length := by rw [← ht]; simp
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
    rw [← ih, ← hs]
  · simp
termination_by s.length
decreasing_by
  have hle := (List.isPrefixOf_iff_prefix.mp ‹_ ∧ _›.2).length_le
  have hpos := List.length_pos_iff.mpr ‹_ ∧ _›.1
  simp only [List.length_drop]
  omega

/-- For a nonempty pattern, no copy starts at the cursor after the inner deletion loop. -/
theorem dropMatches_exhausted (b s : List UInt8) (hb : b ≠ []) :
    b.isPrefixOf (dropMatches b s).1 = false := by
  rw [dropMatches]
  split
  · exact dropMatches_exhausted b (s.drop b.length) hb
  · rename_i h
    simp only
    cases hp : b.isPrefixOf s
    · rfl
    · exact False.elim (h ⟨hb, hp⟩)
termination_by s.length
decreasing_by
  have hle := (List.isPrefixOf_iff_prefix.mp ‹_ ∧ _›.2).length_le
  have hpos := List.length_pos_iff.mpr hb
  simp only [List.length_drop]
  omega

/--
Core's traversal of the remaining input `s` produces bytes `out` and deletion count `count`.
At each cursor it removes leading copies, then retains one whole instruction without searching its interior.
A failed read retains the entire suffix after the leading deletions, including unread bytes.
The next cursor belongs to the remaining input after earlier deletions.
-/
inductive DeletionTraversal (b : List UInt8) : List UInt8 → List UInt8 → Nat → Prop where
  /-- A failed read preserves the whole suffix after leading deletions. -/
  | stop {s p : List UInt8} :
      readOp (dropMatches b s).1 = .stop p →
      DeletionTraversal b s (dropMatches b s).1 (dropMatches b s).2
  /-- A successful read retains one instruction, then continues at its end. -/
  | step {s bytes rest out : List UInt8} {o : UInt8} {count : Nat} :
      readOp (dropMatches b s).1 = .op o bytes rest →
      DeletionTraversal b rest out count →
      DeletionTraversal b s (bytes ++ out) ((dropMatches b s).2 + count)

/-- For all patterns and inputs, the deletion loop follows `DeletionTraversal`, including the count and malformed suffix. -/
theorem findAndDeleteLoop_traversal (b s : List UInt8) :
    DeletionTraversal b s (findAndDeleteLoop b s).1 (findAndDeleteLoop b s).2 := by
  cases hr : readOp (dropMatches b s).1 with
  | stop p => rw [findAndDeleteLoop_of_stop hr]; exact .stop hr
  | op o bytes rest =>
    rw [findAndDeleteLoop_of_op hr]
    exact .step hr (findAndDeleteLoop_traversal b rest)
termination_by s.length
decreasing_by
  have := readOp_rest_length ‹_›
  have := dropMatches_length_le b s
  omega

/-- For every traversal with zero deletions, the output equals the entire input. -/
theorem DeletionTraversal.zero {b s out : List UInt8} {count : Nat}
    (h : DeletionTraversal b s out count) (hc : count = 0) : out = s := by
  induction h with
  | @stop s p hr =>
    have hd := dropMatches_decomposition b s
    rw [hc] at hd
    simpa using hd.symm
  | @step s bytes rest out o count hr ht ih =>
    have hd0 : (dropMatches b s).2 = 0 := by omega
    have hc0 : count = 0 := by omega
    have hd := dropMatches_decomposition b s
    rw [hd0] at hd
    simpa only [List.replicate_zero, List.flatten_nil, List.nil_append] using
      (show bytes ++ out = s from (by rw [ih hc0, readOp_op_append hr]; simpa using hd.symm))

/-- For every script, an empty pattern leaves the loop's bytes unchanged and returns zero. -/
theorem findAndDeleteLoop_empty (s : List UInt8) : findAndDeleteLoop [] s = (s, 0) := by
  have hd : dropMatches [] s = (s, 0) := by rw [dropMatches]; simp
  cases hr : readOp s with
  | stop p => rw [findAndDeleteLoop_of_stop (by simpa [hd] using hr), hd]
  | op o bytes rest =>
    rw [findAndDeleteLoop_of_op (by simpa [hd] using hr), findAndDeleteLoop_empty rest, hd]
    simp [readOp_op_append hr]
termination_by s.length
decreasing_by exact readOp_rest_length ‹_›

/-- For all scripts and patterns, Core's unchanged-input shortcut has the same result as its traversal loop. -/
theorem findAndDelete_eq_loop (s b : List UInt8) :
    Transaction.findAndDelete s b = findAndDeleteLoop b s := by
  unfold Transaction.findAndDelete
  split
  · rename_i hb
    subst b
    exact (findAndDeleteLoop_empty s).symm
  · dsimp only
    split
    · rename_i hc
      have hz := (findAndDeleteLoop_traversal b s).zero hc
      exact Prod.ext hz.symm hc.symm
    · rfl

/-- For all scripts and patterns, `findAndDelete` follows Core's traversal and returns its exact deletion count. -/
theorem findAndDelete_traversal (s b : List UInt8) :
    DeletionTraversal b s (Transaction.findAndDelete s b).1 (Transaction.findAndDelete s b).2 := by
  rw [findAndDelete_eq_loop]
  exact findAndDeleteLoop_traversal b s

/-- For every failed read after leading deletions, the loop keeps every remaining byte and reports only those deletions. -/
theorem findAndDeleteLoop_malformed {b s p : List UInt8}
    (h : readOp (dropMatches b s).1 = .stop p) :
    findAndDeleteLoop b s = dropMatches b s := findAndDeleteLoop_of_stop h

/-- With no signatures, effective script code is the exact suffix from the supplied separator cursor. -/
theorem effectiveScriptCode_nil (s : List UInt8) (pc : Nat) :
    effectiveScriptCode s pc [] = s.drop pc := rfl

/-- With one signature, effective script code deletes its complete push encoding from the selected suffix. -/
theorem effectiveScriptCode_single (s sig : List UInt8) (pc : Nat) :
    effectiveScriptCode s pc [sig] = (Transaction.findAndDelete (s.drop pc) (pushEncoding sig)).1 := rfl

/-- For any two signature lists, preparation for their concatenation runs the first list before the second. -/
theorem effectiveScriptCode_append (s : List UInt8) (pc : Nat) (a b : List (List UInt8)) :
    effectiveScriptCode s pc (a ++ b) = effectiveScriptCode (effectiveScriptCode s pc a) 0 b := by
  simp [effectiveScriptCode, List.foldl_append]

/-! ## Complete parses -/

/-- For every payload shorter than 2^32 bytes, `readOp` reads its push encoding as one instruction, with the first byte as the opcode and nothing after it. -/
theorem readOp_pushEncoding (data : List UInt8) (h : data.length < 2 ^ 32) :
    readOp (pushEncoding data) = .op (pushEncoding data).head! (pushEncoding data) [] := by
  obtain ⟨o, lf, hh, he⟩ := pushHeader_encoding data h
  have hb : pushEncoding data = o :: lf ++ data := by simp [pushEncoding, hh]
  have hhead : (pushEncoding data).head! = o := by rw [hb]; rfl
  rw [hhead]
  exact readOp_eq_op_iff.mpr ⟨lf, data, he.1, he.2, hb, by simp⟩

/-- For every payload shorter than 2^32 bytes, its push encoding parses completely. -/
theorem scanOps_pushEncoding (data : List UInt8) (h : data.length < 2 ^ 32) :
    (scanOps (pushEncoding data)).2 = [] :=
  scanOps_bytes (readOp_pushEncoding data h)

/-- For every payload, its push encoding is longer than the payload. -/
theorem length_lt_pushEncoding (data : List UInt8) : data.length < (pushEncoding data).length := by
  have : 0 < (pushHeader data.length).length := by
    unfold pushHeader
    split
    · simp
    · split
      · simp
      · split <;> simp
  simp only [pushEncoding, List.length_append]
  omega

/--
For every script of at most 2^32 bytes, cursor `pc` whose suffix parses completely, and signature list `sigs`: the effective script code parses completely.
The suffix parses completely when the script does and `pc` is at an instruction boundary (`Transaction.scanOps_drop`).
No hypothesis on the signatures is needed.
A push of a signature of 2^32 bytes or more is longer than the script code, so it never matches.
-/
theorem effectiveScriptCode_scanOps (script : List UInt8) (pc : Nat) (sigs : List (List UInt8))
    (h : (scanOps (script.drop pc)).2 = []) (hlen : script.length ≤ 2 ^ 32) :
    (scanOps (effectiveScriptCode script pc sigs)).2 = [] := by
  unfold effectiveScriptCode
  suffices ∀ code : List UInt8, (scanOps code).2 = [] → code.length ≤ 2 ^ 32 →
      (scanOps (sigs.foldl (fun code sig => (Transaction.findAndDelete code (pushEncoding sig)).1) code)).2 = [] from
    this _ h (by simp only [List.length_drop]; omega)
  induction sigs with
  | nil => intro code hc _; exact hc
  | cons sig sigs ih =>
    intro code hc hl
    refine ih _ (findAndDelete_scanOps hc ?_) (Nat.le_trans (findAndDelete_length_le _ _) hl)
    by_cases hs : sig.length < 2 ^ 32
    · exact .inl (scanOps_pushEncoding sig hs)
    · have := length_lt_pushEncoding sig
      exact .inr (by omega)

end DogeLib.Script
