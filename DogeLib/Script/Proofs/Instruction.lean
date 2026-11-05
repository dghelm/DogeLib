module

public import DogeLib.Script.Instruction
import DogeLib.Transaction.Proofs.LegacySighash

/-! Byte-consumption and cursor properties of the Script reader. -/

public section

namespace DogeLib.Script

/-- Every successful underlying read gives the same instruction bytes and next cursor. -/
theorem readInstruction_of_op {script : List UInt8} {cursor : Nat} {opcode : UInt8}
    {bytes rest : List UInt8} (hc : cursor ≤ script.length)
    (h : Transaction.readOp (script.drop cursor) = .op opcode bytes rest) :
    readInstruction script cursor = .instruction
      ⟨opcode, bytes, pushedBytes opcode bytes, cursor + bytes.length⟩ := by
  simp [readInstruction, hc, h]

/-- A failed underlying read on a nonempty suffix preserves the exact failure cursor. -/
theorem readInstruction_of_stop {script passed : List UInt8} {cursor : Nat}
    (hc : cursor ≤ script.length)
    (h : Transaction.readOp (script.drop cursor) = .stop passed)
    (hne : script.drop cursor ≠ []) :
    readInstruction script cursor = .truncatedPush (cursor + passed.length) := by
  simp [readInstruction, hc, h, hne]

private theorem instruction_parts {script : List UInt8} {cursor : Nat} {i : Instruction}
    (h : readInstruction script cursor = .instruction i) :
    ∃ opcode bytes rest, cursor ≤ script.length ∧
      Transaction.readOp (script.drop cursor) = .op opcode bytes rest ∧
      i = ⟨opcode, bytes, pushedBytes opcode bytes, cursor + bytes.length⟩ := by
  unfold readInstruction at h
  split at h
  next hc =>
    split at h
    next opcode bytes rest hr => exact ⟨opcode, bytes, rest, hc, hr, by cases h; rfl⟩
    next => split at h <;> cases h
  next => cases h

/-- Every successful read advances the cursor and stays within the script. -/
theorem instruction_cursor {script : List UInt8} {cursor : Nat} {i : Instruction}
    (h : readInstruction script cursor = .instruction i) :
    cursor < i.nextCursor ∧ i.nextCursor ≤ script.length := by
  obtain ⟨o, b, r, hc, hr, rfl⟩ := instruction_parts h
  have ha := congrArg List.length (Transaction.readOp_op_append hr)
  have hl := Transaction.readOp_rest_length hr
  simp only [List.length_append, List.length_drop] at ha hl
  simp only
  omega

/-- Successful instruction bytes followed by the unread suffix reconstruct the input suffix. -/
theorem instruction_consumption {script : List UInt8} {cursor : Nat} {i : Instruction}
    (h : readInstruction script cursor = .instruction i) :
    i.bytes ++ script.drop i.nextCursor = script.drop cursor := by
  obtain ⟨o, b, r, hc, hr, rfl⟩ := instruction_parts h
  have ha := Transaction.readOp_op_append hr
  have hd := congrArg (List.drop b.length) ha
  simp only [List.drop_left] at hd
  have he : script.drop (cursor + b.length) = r := by
    simpa [List.drop_drop, Nat.add_comm] using hd.symm
  change b ++ script.drop (cursor + b.length) = script.drop cursor
  rw [he]
  exact ha

/-- Every truncated push advances the failure cursor and stays within the script. -/
theorem truncated_cursor {script : List UInt8} {cursor next : Nat}
    (h : readInstruction script cursor = .truncatedPush next) :
    cursor < next ∧ next ≤ script.length := by
  unfold readInstruction at h
  split at h
  next hc =>
    split at h
    next => cases h
    next passed hr =>
      split at h
      next => cases h
      next hn =>
        cases h
        have hp := Transaction.readOp_stop_prefix hr
        have hl := hp.length_le
        have hpos : 0 < passed.length := by
          by_cases hz : passed = []
          · subst passed
            exact False.elim (hn (Transaction.readOp_stop_nil hr))
          · have := List.length_pos_iff.mpr hz
            omega
        simp only [List.length_drop] at hl
        omega
  next => cases h

/-- End-of-script occurs exactly at the input length, for every byte list and cursor. -/
theorem readInstruction_end_iff (script : List UInt8) (cursor : Nat) :
    readInstruction script cursor = .endOfScript ↔ cursor = script.length := by
  constructor
  · intro h
    unfold readInstruction at h
    split at h
    next hc =>
      split at h
      next => cases h
      next =>
        split at h
        next hn => have := congrArg List.length hn; simp at this; omega
        next => cases h
    next => cases h
  · rintro rfl
    simp [readInstruction, Transaction.readOp]

/-- For every suffix and offset, the complete instructions form an exact prefix of that suffix. -/
theorem readInstructionsFrom_prefix (bs : List UInt8) (cursor : Nat) :
    ∃ suffix, ((readInstructionsFrom bs cursor).1.flatMap Instruction.bytes) ++ suffix = bs := by
  rw [readInstructionsFrom]
  split
  next o b r hr =>
    obtain ⟨suffix, hs⟩ := readInstructionsFrom_prefix r (cursor + b.length)
    refine ⟨suffix, ?_⟩
    simpa [List.flatMap_cons, List.append_assoc, hs] using Transaction.readOp_op_append hr
  next => exact ⟨bs, rfl⟩
termination_by bs.length
decreasing_by exact Transaction.readOp_rest_length ‹_›

/-- If iteration reaches the end, its instruction bytes reconstruct the whole input suffix. -/
theorem readInstructionsFrom_complete (bs : List UInt8) (cursor : Nat)
    (h : (readInstructionsFrom bs cursor).2 = .endOfScript) :
    (readInstructionsFrom bs cursor).1.flatMap Instruction.bytes = bs := by
  rw [readInstructionsFrom] at h ⊢
  split at *
  next o b r hr =>
    have ht := readInstructionsFrom_complete r (cursor + b.length) h
    simpa [List.flatMap_cons, ht] using Transaction.readOp_op_append hr
  next passed hr =>
    split at h
    next he => simp [he]
    next => cases h
termination_by bs.length
decreasing_by exact Transaction.readOp_rest_length ‹_›

end DogeLib.Script
