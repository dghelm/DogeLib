module

public import DogeLib.Script.Instruction
public import DogeLib.Transaction.Proofs.LegacySighash

/-!
# Proofs: `Script.Instruction`

- `readOp_cons_eq`: one uniform form of `Transaction.readOp` on a nonempty script, in terms of `lengthFieldWidth` and `pushSize`.
- `readOp_eq_op_iff`: `readOp` reads an instruction exactly when the bytes start with a whole instruction encoding.
- `readOp_eq_stop_iff`: `readOp` stops exactly on a short push or on the empty script.
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

/-- For every decidable condition `c` that fails, `if c then a else b` is `b`. -/
theorem ite_neg_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- For every decidable condition `c` that holds, `if c then a else b` is `a`. -/
theorem ite_pos_eq {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

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
theorem gt_of_not_le {op : UInt8} (h : ¬ op ≤ 0x4e) : 0x4e < op :=
  UInt8.lt_iff_toNat_lt.mpr (by
    have : ¬ op.toNat ≤ (0x4e : UInt8).toNat := fun h' => h (UInt8.le_iff_toNat_le.mpr h')
    omega)

/-- For every opcode `o` and bytes `lf` and `data`: the instruction bytes `o :: lf ++ data` without the opcode and the `lf.length` bytes after it are `data`. -/
theorem drop_header (o : UInt8) (lf data : List UInt8) :
    (o :: lf ++ data).drop (1 + lf.length) = data := by
  rw [Nat.add_comm, List.cons_append, List.drop_succ_cons, List.drop_left]

/-! ## `readOp` against the encoding relation -/

/--
For all bytes `bs`, `o`, `b` and `r`: `readOp bs` returns `.op o b r` if and only if two conditions hold.
The bytes `bs` are `b ++ r`, and `b` is an instruction encoding `o :: lf ++ data`.
-/
theorem readOp_eq_op_iff {bs : List UInt8} {o : UInt8} {b r : List UInt8} :
    readOp bs = .op o b r ↔
      ∃ lf data, InstructionEncoding o lf data ∧ b = o :: lf ++ data ∧ bs = b ++ r := by
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
            ⟨?_, ?_⟩, rfl, ?_⟩
          · simp only [List.length_take]; omega
          · simp only [List.length_take]; omega
          · simp only [List.cons_append, List.append_assoc]
            rw [List.take_append_drop, List.take_append_drop]
      · rename_i hle
        cases h
        have hgt := gt_of_not_le hle
        exact ⟨[], [], ⟨by simp [lengthFieldWidth_of_gt hgt], by simp [pushSize_of_gt hgt]⟩,
          rfl, rfl⟩
  · rintro ⟨lf, data, ⟨hlf, hdata⟩, rfl, rfl⟩
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
    obtain ⟨lf, data, henc, hb, hs⟩ := readOp_eq_op_iff.mp hr
    have hdata : i.pushed = data := by rw [hp, hb, ← henc.1, drop_header]
    rw [hdata]
    exact ⟨lf, r, henc, hb, hs, hn⟩
  · rintro ⟨lf, rest, henc, hb, hs, hn⟩
    refine ⟨rest, readOp_eq_op_iff.mpr ⟨lf, i.pushed, henc, hb, hs⟩, ?_, hn⟩
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
theorem drop_eq_cons_iff {s t : List UInt8} {pc : Nat} {op : UInt8} :
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
