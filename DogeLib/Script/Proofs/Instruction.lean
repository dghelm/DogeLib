module

public import DogeLib.Script.Instruction
public import DogeLib.Transaction.Proofs.LegacySighash

/-!
# Proofs: `Script.Instruction`

- `readInstruction_eq_instruction_iff_readOp` and `readInstruction_eq_fail_iff_readOp`: `readInstruction` succeeds and fails exactly where `readOp` does, with the same opcode and bytes.
- `readInstruction_eq_instruction_iff`: soundness and completeness against `InstructionEncoding`, an encoding relation stated without the reader.
- `readInstruction_consumes` and `readInstruction_nonpush`: the cursor moves forward by the bytes of the instruction and stays within the script.
- `readInstruction_atEnd_iff` and `readInstruction_truncated_iff`: the failures and the cursor that each leaves, as `GetOp2` leaves it.
- `IsBoundary.le_length` and `IsBoundary.not_inside`: boundaries lie within the script, and none lies inside an instruction that starts at a boundary.

These theorems are statements about the definitions. They do not say that the definitions match Core.
The known answers in `tests/KnownAnswers.lean` compare `readInstruction` with cases from Core's `script_tests.json` and with cases derived from `GetOp2`.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-! ## The encoding relation -/

/--
`op :: lengthField ++ data` is one whole instruction as `GetOp2` reads it (D24, lines 502 to 552).
The length field has the width that the opcode requires, and the data has the size that the opcode and the length field give.
For an opcode above `OP_PUSHDATA4`, the width and the size are 0, so the instruction is the opcode alone.
-/
def InstructionEncoding (op : UInt8) (lengthField data : List UInt8) : Prop :=
  lengthField.length = lengthFieldWidth op ∧ data.length = pushSize op lengthField

/-- For every decidable condition `c` that fails, `if c then a else b` is `b`. -/
private theorem ite_neg_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- For every decidable condition `c` that holds, `if c then a else b` is `a`. -/
private theorem ite_pos_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-- For every opcode `o` and bytes `lf` and `data`: the instruction bytes `o :: lf ++ data` without the opcode and the `lf.length` bytes after it are `data`. -/
private theorem drop_header (o : UInt8) (lf data : List UInt8) :
    (o :: lf ++ data).drop (1 + lf.length) = data := by
  rw [Nat.add_comm, List.cons_append, List.drop_succ_cons, List.drop_left]

/-! ## `readInstruction` and `readOp` -/

/--
For every script `s`, cursor `pc` and instruction `i`: `readInstruction s pc` reads `i` exactly when `readOp` reads the opcode and bytes of `i`.
`readOp` reads the bytes from `pc`.
The pushed bytes of `i` are its bytes after the opcode and the length field.
The next cursor of `i` is `pc` plus the number of its bytes.
-/
theorem readInstruction_eq_instruction_iff_readOp {s : List UInt8} {pc : Nat} {i : Instruction} :
    readInstruction s pc = .instruction i ↔
      ∃ r, readOp (s.drop pc) = .op i.opcode i.bytes r ∧
        i.pushed = i.bytes.drop (1 + lengthFieldWidth i.opcode) ∧ i.next = pc + i.bytes.length := by
  unfold readInstruction
  split
  · rename_i o b r h
    rw [h]
    constructor
    · intro hi; cases hi; exact ⟨r, rfl, rfl, rfl⟩
    · rintro ⟨r', h', hp, hn⟩
      cases h'
      cases i
      simp_all
  · rename_i h
    rw [h]
    simp
  · rename_i o lf h
    rw [h]
    simp

/-- For every script `s` and cursor `pc`: `readInstruction s pc` fails if and only if `readOp` on the bytes from `pc` stops. -/
theorem readInstruction_eq_fail_iff_readOp {s : List UInt8} {pc : Nat} :
    (∀ i, readInstruction s pc ≠ .instruction i) ↔ ∃ p, readOp (s.drop pc) = .stop p := by
  constructor
  · intro h
    match hr : readOp (s.drop pc) with
    | .stop p => exact ⟨p, rfl⟩
    | .op o b r =>
      exact absurd (readInstruction_eq_instruction_iff_readOp.mpr ⟨r, hr, rfl, rfl⟩)
        (h ⟨o, b, b.drop (1 + lengthFieldWidth o), pc + b.length⟩)
  · rintro ⟨p, hp⟩ i hi
    obtain ⟨r, hr, -⟩ := readInstruction_eq_instruction_iff_readOp.mp hi
    rw [hp] at hr
    cases hr

/-! ## Soundness and completeness -/

/--
For every script `s`, cursor `pc` and instruction `i`: `readInstruction s pc` reads `i` exactly when two conditions hold.
The bytes from `pc` start with the bytes of `i`, and those bytes are an instruction encoding `i.opcode :: lengthField ++ i.pushed`.
The next cursor is `pc` plus the number of bytes of `i`.
So the reader keeps the exact bytes of every push, including a nonminimal one.
-/
theorem readInstruction_eq_instruction_iff {s : List UInt8} {pc : Nat} {i : Instruction} :
    readInstruction s pc = .instruction i ↔
      ∃ lengthField rest, InstructionEncoding i.opcode lengthField i.pushed ∧
        i.bytes = i.opcode :: lengthField ++ i.pushed ∧
        s.drop pc = i.bytes ++ rest ∧ i.next = pc + i.bytes.length := by
  rw [readInstruction_eq_instruction_iff_readOp]
  constructor
  · rintro ⟨r, hr, hp, hn⟩
    obtain ⟨lf, data, hlf, hdl, hb, hs⟩ := readOp_eq_op_iff.mp hr
    have henc : InstructionEncoding i.opcode lf data := ⟨hlf, hdl⟩
    have hdata : i.pushed = data := by rw [hp, hb, ← henc.1, drop_header]
    rw [hdata]
    exact ⟨lf, r, henc, hb, hs, hn⟩
  · rintro ⟨lf, rest, henc, hb, hs, hn⟩
    refine ⟨rest, readOp_eq_op_iff.mpr ⟨lf, i.pushed, henc.1, henc.2, hb, hs⟩, ?_, hn⟩
    rw [hb, ← henc.1, drop_header]

/-! ## Consumption and the cursor -/

/--
For every script `s`, cursor `pc` and instruction `i` that `readInstruction s pc` reads, the next cursor is after `pc` and at most the length of `s`.
The bytes from `pc` are the bytes of `i` and then the bytes from the next cursor.
-/
theorem readInstruction_consumes {s : List UInt8} {pc : Nat} {i : Instruction}
    (h : readInstruction s pc = .instruction i) :
    pc < i.next ∧ i.next ≤ s.length ∧ s.drop pc = i.bytes ++ s.drop i.next := by
  obtain ⟨lf, rest, -, hb, hs, hn⟩ := readInstruction_eq_instruction_iff.mp h
  have hlen := congrArg List.length hs
  simp only [List.length_drop, List.length_append] at hlen
  have hbl : 0 < i.bytes.length := by rw [hb]; simp
  have hrest : s.drop i.next = rest := by
    rw [hn, ← List.drop_drop, hs, List.drop_left]
  refine ⟨by omega, by omega, by rw [hrest, hs]⟩

/-- For every instruction `i` that `readInstruction s pc` reads with an opcode above `OP_PUSHDATA4`: `i` is one byte, pushes nothing, and moves the cursor by one. -/
theorem readInstruction_nonpush {s : List UInt8} {pc : Nat} {i : Instruction}
    (h : readInstruction s pc = .instruction i) (hop : 0x4e < i.opcode) :
    i.bytes = [i.opcode] ∧ i.pushed = [] ∧ i.next = pc + 1 := by
  obtain ⟨lf, rest, ⟨hlf, hdata⟩, hb, -, hn⟩ := readInstruction_eq_instruction_iff.mp h
  have hl : lf = [] := List.eq_nil_of_length_eq_zero (by rw [hlf, lengthFieldWidth_of_gt hop])
  have hd : i.pushed = [] :=
    List.eq_nil_of_length_eq_zero (by rw [hdata, pushSize_of_gt hop])
  rw [hl, hd] at hb
  exact ⟨hb, hd, by rw [hn, hb]; rfl⟩

/-- For every script `s` and cursor `pc`: `readInstruction s pc` reports the end of the script if and only if `pc` is at or after the end. -/
theorem readInstruction_atEnd_iff {s : List UInt8} {pc : Nat} :
    readInstruction s pc = .atEnd ↔ s.length ≤ pc := by
  unfold readInstruction
  split
  · rename_i o b r h
    simp only [reduceCtorEq, false_iff, Nat.not_le]
    apply Nat.lt_of_not_le
    intro hle
    rw [List.drop_eq_nil_of_le hle] at h
    simp [readOp] at h
  · rename_i h
    simpa using readOp_stop_nil h
  · rename_i o lf h
    simp only [reduceCtorEq, false_iff, Nat.not_le]
    apply Nat.lt_of_not_le
    intro hle
    rw [List.drop_eq_nil_of_le hle] at h
    simp [readOp] at h

/-- For every script `s` and cursor `pc`: the bytes from `pc` are `op :: t` exactly when `op` is at index `pc`, and `t` is the rest. -/
private theorem drop_eq_cons_iff {s t : List UInt8} {pc : Nat} {op : UInt8} :
    s.drop pc = op :: t ↔ s[pc]? = some op ∧ s.drop (pc + 1) = t := by
  induction s generalizing pc with
  | nil => simp
  | cons a s ih =>
    cases pc with
    | zero => simp
    | succ pc => simpa using ih

/--
For every script `s` and cursor `pc`: `readInstruction` fails on a short push of `op` exactly when `readOp` stops after `op` and `lf`.
The part and the cursor of the failure follow from `lf`.
-/
theorem readInstruction_eq_truncated_iff_readOp {s : List UInt8} {pc c : Nat} {op : UInt8}
    {part : ShortPart} :
    readInstruction s pc = .truncated op part c ↔
      ∃ lf, readOp (s.drop pc) = .stop (op :: lf) ∧
        part = (if lf.length = lengthFieldWidth op then .payload else .lengthField) ∧
        c = pc + 1 + lf.length := by
  unfold readInstruction
  split
  · rename_i o b r h
    rw [h]; simp
  · rename_i h
    rw [h]; simp
  · rename_i o lf h
    rw [h]
    simp only [ReadResult.truncated.injEq, OpRead.stop.injEq, List.cons.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨lf, ⟨rfl, rfl⟩, rfl, rfl⟩
    · rintro ⟨lf', ⟨rfl, rfl⟩, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩

/--
For every script `s` and cursor `pc`: `readInstruction s pc` returns `.truncated op part c` exactly when two conditions hold.
The byte `op` at index `pc` is a push opcode, and one of two cases holds.

- The length field is short: fewer than `lengthFieldWidth op` bytes follow the opcode, and `c` is the cursor after the opcode.
- The data is short: the whole length field follows the opcode, and fewer than `pushSize` bytes follow it. Then `c` is the cursor after the length field.

A direct push has a length field of width 0, so a short direct push is the second case, with `c = pc + 1`.
`GetOp2` (D24, lines 502 to 552) leaves `pc` at these cursors when it returns false.
-/
theorem readInstruction_truncated_iff {s : List UInt8} {pc c : Nat} {op : UInt8} {part : ShortPart} :
    readInstruction s pc = .truncated op part c ↔
      s[pc]? = some op ∧ op ≤ 0x4e ∧
      ((part = .lengthField ∧ s.length < pc + 1 + lengthFieldWidth op ∧ c = pc + 1) ∨
       (part = .payload ∧ pc + 1 + lengthFieldWidth op ≤ s.length ∧
          s.length < pc + 1 + lengthFieldWidth op +
            pushSize op ((s.drop (pc + 1)).take (lengthFieldWidth op)) ∧
          c = pc + 1 + lengthFieldWidth op)) := by
  rw [readInstruction_eq_truncated_iff_readOp]
  constructor
  · rintro ⟨lf, hr, hpart, hc⟩
    rcases readOp_eq_stop_iff.mp hr with ⟨-, h⟩ | ⟨op', t, hs, hle, h⟩
    · cases h
    · obtain ⟨hget, ht⟩ := drop_eq_cons_iff.mp hs
      subst ht
      have hlen : (s.drop (pc + 1)).length = s.length - (pc + 1) := List.length_drop
      have hpc : pc < s.length := (List.getElem?_eq_some_iff.mp hget).1
      rcases h with ⟨hw, hp⟩ | ⟨hw, hn, hp⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hp
        refine ⟨hget, hle, Or.inl ⟨?_, by omega, by simpa using hc⟩⟩
        rw [hpart, ite_neg_eq (by simp; omega)]
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hp
        have htl : ((s.drop (pc + 1)).take (lengthFieldWidth op)).length = lengthFieldWidth op := by
          simp only [List.length_take]; omega
        simp only [List.length_drop] at hn
        refine ⟨hget, hle, Or.inr ⟨?_, by omega, by omega, by rw [hc, htl]⟩⟩
        rw [hpart, ite_pos_eq htl]
  · rintro ⟨hget, hle, h⟩
    have hs : s.drop pc = op :: s.drop (pc + 1) := drop_eq_cons_iff.mpr ⟨hget, rfl⟩
    have hlen : (s.drop (pc + 1)).length = s.length - (pc + 1) := List.length_drop
    have hpc : pc < s.length := (List.getElem?_eq_some_iff.mp hget).1
    rcases h with ⟨rfl, hw, rfl⟩ | ⟨rfl, hw, hn, rfl⟩
    · refine ⟨[], ?_, ?_, rfl⟩
      · rw [hs]
        exact readOp_eq_stop_iff.mpr
          (Or.inr ⟨op, s.drop (pc + 1), rfl, hle, Or.inl ⟨by omega, rfl⟩⟩)
      · rw [ite_neg_eq (by simp; omega)]
    · have htl : ((s.drop (pc + 1)).take (lengthFieldWidth op)).length = lengthFieldWidth op := by
        simp only [List.length_take]; omega
      refine ⟨(s.drop (pc + 1)).take (lengthFieldWidth op), ?_, by rw [ite_pos_eq htl], by rw [htl]⟩
      rw [hs]
      refine readOp_eq_stop_iff.mpr (Or.inr ⟨op, s.drop (pc + 1), rfl, hle, Or.inr ⟨by omega, ?_, rfl⟩⟩)
      simp only [List.length_drop]
      omega

/-! ## Instruction boundaries -/

/-- For every script `s` and boundary `pc` of `s`: `pc` is at most the length of `s`. -/
theorem IsBoundary.le_length {s : List UInt8} {pc : Nat} (h : IsBoundary s pc) : pc ≤ s.length := by
  induction h with
  | start => exact Nat.zero_le _
  | step _ hread _ => exact (readInstruction_consumes hread).2.1

/-- For every script `s` and cursor `pc`: `readInstruction` reads at most one instruction at `pc`. -/
theorem readInstruction_instruction_unique {s : List UInt8} {pc : Nat} {i j : Instruction}
    (hi : readInstruction s pc = .instruction i) (hj : readInstruction s pc = .instruction j) :
    i = j := by
  rw [hi] at hj
  cases hj
  rfl

/-- For every script `s` and boundaries `a ≤ b` of `s`: `a = b`, or an instruction starts at `a` and ends at or before `b`. -/
theorem IsBoundary.eq_or_next_le {s : List UInt8} {a b : Nat} (hb : IsBoundary s b) :
    IsBoundary s a → a ≤ b →
      a = b ∨ ∃ i, readInstruction s a = .instruction i ∧ i.next ≤ b := by
  induction hb generalizing a with
  | start =>
    intro _ hle
    exact Or.inl (Nat.le_zero.mp hle)
  | @step b' i hb' hread ih =>
    intro ha hle
    have hcons := readInstruction_consumes hread
    by_cases hab : a ≤ b'
    · rcases ih ha hab with rfl | ⟨j, hj, hjn⟩
      · exact Or.inr ⟨i, hread, Nat.le_refl _⟩
      · exact Or.inr ⟨j, hj, by omega⟩
    · -- A boundary after `b'` is at or after the end of the instruction at `b'`.
      have key : ∀ {a'}, IsBoundary s a' → b' < a' → i.next ≤ a' := by
        intro a' ha'
        induction ha' with
        | start => intro h; omega
        | @step c j hc hreadc ihc =>
          intro hlt
          have hconsc := readInstruction_consumes hreadc
          by_cases hcb : b' < c
          · exact Nat.le_trans (ihc hcb) (Nat.le_of_lt hconsc.1)
          · rcases ih hc (by omega) with rfl | ⟨j', hj', hj'n⟩
            · rw [readInstruction_instruction_unique hread hreadc]
              exact Nat.le_refl _
            · rw [readInstruction_instruction_unique hreadc hj'] at hlt
              omega
      exact Or.inl (Nat.le_antisymm hle (key ha (by omega)))

/--
Let `pc` and `k` be boundaries of a script `s`, and let `i` be the instruction at `pc`.
Then `k` is at or before `pc`, or at or after the end of `i`.
So no boundary lies inside an instruction that starts at a boundary.
A loop of `GetOp2` calls from `begin()` never reads a byte of a length field or of pushed data as an opcode.
An example is a byte `0xab` (`OP_CODESEPARATOR`) inside a push.
-/
theorem IsBoundary.not_inside {s : List UInt8} {pc k : Nat} {i : Instruction}
    (hpc : IsBoundary s pc) (h : readInstruction s pc = .instruction i) (hk : IsBoundary s k) :
    k ≤ pc ∨ i.next ≤ k := by
  by_cases hle : k ≤ pc
  · exact Or.inl hle
  · rcases hk.eq_or_next_le hpc (by omega) with rfl | ⟨j, hj, hjn⟩
    · omega
    · rw [readInstruction_instruction_unique h hj]
      exact Or.inr hjn

/-! ## Examples

These examples check the reader in the kernel on three short scripts.
The known answers in `tests/KnownAnswers.lean` check the compiled code on more cases.
-/

-- `OP_CODESEPARATOR` (`0xab`) as pushed data, then as an instruction at cursor 2.
example : readInstruction [0x01, 0xab, 0xab] 0 = .instruction ⟨0x01, [0x01, 0xab], [0xab], 2⟩ := by
  decide
example : readInstruction [0x01, 0xab, 0xab] 2 = .instruction ⟨0xab, [0xab], [], 3⟩ := by decide

-- `OP_PUSHDATA2` with one byte of its length field: the cursor stops after the opcode.
example : readInstruction [0x4d, 0x01] 0 = .truncated 0x4d .lengthField 1 := by decide

-- `OP_PUSHDATA1` that declares one byte and has none: the cursor stops after the length field.
example : readInstruction [0x4c, 0x01] 0 = .truncated 0x4c .payload 2 := by decide

end DogeLib.Script
