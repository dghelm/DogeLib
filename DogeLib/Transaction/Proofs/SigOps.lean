module

public import DogeLib.Transaction.SigOps
public import DogeLib.Transaction.Proofs.ScanOps
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the legacy count of signature operations

- `nextOp_view`: the linear reader `nextOp` reads the opcode, the data and the rest that `readOp` reads, and fails exactly where `readOp` fails.
- `foldOps_eq`: `foldOps` folds over the opcodes of the instructions of `scanOps`, in order.
- `Script.getSigOpCount_eq_scanOps`: the count is the sum of `opcodeSigOps` over the instructions of `scanOps`.
- `Script.getSigOpCount_le` bounds the count of a script by 20 times its length.
  Core counts in `unsigned int`, and the bound shows when that type holds the count without a wrap.
-/

@[expose] public section

namespace DogeLib.Transaction

/-- For every `n` and all bytes `bs`: `dropExact n bs` is `none` when `bs` has fewer than `n` bytes, and otherwise `bs` without its first `n` bytes. -/
theorem dropExact_eq : ∀ (n : Nat) (bs : List UInt8),
    dropExact n bs = if bs.length < n then none else some (bs.drop n)
  | 0, bs => by simp [dropExact]
  | n + 1, [] => by simp [dropExact]
  | n + 1, b :: bs => by
    rw [dropExact, dropExact_eq n bs]
    simp

/-- The next instruction that one call of `readOp` reads: its opcode, its data after the length field, and the bytes after it. A failed read gives `none`. -/
def OpRead.view : OpRead → Option (UInt8 × List UInt8 × List UInt8)
  | .op o b r => some (o, b.drop (1 + lengthFieldWidth o), r)
  | .stop _ => none

/-- The opcode, the data and the bytes after an instruction that `nextOp` reads. -/
def OpStep.view (s : OpStep) : UInt8 × List UInt8 × List UInt8 := (s.opcode, s.data, s.rest)

/-- For every push after a header of `1 + lengthFieldWidth op` bytes, `pushStep` and `readPush` agree. They give the same opcode, data and rest, and fail on the same bytes. -/
theorem pushStep_view (op : UInt8) (hd : List UInt8) (n : Nat) (r : List UInt8)
    (hh : hd.length = 1 + lengthFieldWidth op) :
    (pushStep op n r).map OpStep.view = (readPush op hd n r).view := by
  unfold pushStep readPush
  rw [dropExact_eq]
  by_cases h : r.length < n
  · simp [h, OpRead.view]
  · simp [h, OpRead.view, OpStep.view, OpStep.data, ← hh]

/--
For all bytes `bs`: `nextOp bs` reads the instruction that `readOp bs` reads.
Both give the same opcode, the same data and the same bytes after the instruction, and `nextOp` gives `none` exactly when `readOp` stops.
-/
theorem nextOp_view (bs : List UInt8) : (nextOp bs).map OpStep.view = (readOp bs).view := by
  match bs with
  | [] => rfl
  | op :: t =>
    simp only [nextOp, readOp]
    split
    · rename_i h
      exact pushStep_view _ _ _ _ (by simp [lengthFieldWidth_of_lt h])
    · split
      · rename_i h
        subst h
        match t with
        | b :: r' => exact pushStep_view _ _ _ _ (by simp [lengthFieldWidth])
        | [] => rfl
      · split
        · rename_i h
          subst h
          match t with
          | b0 :: b1 :: r' => exact pushStep_view _ _ _ _ (by simp [lengthFieldWidth])
          | [] => rfl
          | [_] => rfl
        · split
          · rename_i h
            subst h
            match t with
            | b0 :: b1 :: b2 :: b3 :: r' => exact pushStep_view _ _ _ _ (by simp [lengthFieldWidth])
            | [] => rfl
            | [_] => rfl
            | [_, _] => rfl
            | [_, _, _] => rfl
          · rename_i h1 h2 h3 h4
            have hgt : 0x4e < op := by
              simp only [UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj] at h1 h2 h3 h4 ⊢
              simp at h1 h2 h3 h4 ⊢
              omega
            simp [OpRead.view, OpStep.view, OpStep.data, lengthFieldWidth_of_gt hgt]

/-- For every step `f`, start value and script: `foldOps` is the left fold of `f` over the opcodes of `scanOps bs`. -/
theorem foldOps_eq {β : Type} (f : β → UInt8 → β) (acc : β) (bs : List UInt8) :
    foldOps f acc bs = ((scanOps bs).1.map Prod.fst).foldl f acc := by
  have hv := nextOp_view bs
  rw [foldOps]
  split
  · rename_i h
    rw [h] at hv
    cases hr : readOp bs with
    | op o b r => rw [hr] at hv; simp [OpRead.view] at hv
    | stop p => rw [scanOps_of_stop hr]; rfl
  · rename_i s h
    rw [h] at hv
    cases hr : readOp bs with
    | stop p => rw [hr] at hv; simp [OpRead.view] at hv
    | op o b r =>
      rw [hr] at hv
      simp only [Option.map_some, OpStep.view, OpRead.view, Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨ho, -, hrest⟩ := hv
      rw [scanOps_of_op hr, foldOps_eq f _ s.rest, hrest, ho]
      simp
termination_by bs.length
decreasing_by exact nextOp_rest_length ‹_›

/-- The left fold that adds `g` of each element to `acc` gives `acc` plus the sum of `g` over the list. -/
theorem foldl_add_eq_sum (g : UInt8 → Nat) : ∀ (l : List UInt8) (acc : Nat),
    l.foldl (fun n o => n + g o) acc = acc + (l.map g).sum
  | [], acc => by simp
  | o :: l, acc => by
    rw [List.foldl_cons, foldl_add_eq_sum g l]
    simp; omega

/--
For every script, `Script.getSigOpCount` is the sum of `opcodeSigOps` over the instructions that `scanOps` reads.
-/
theorem Script.getSigOpCount_eq_scanOps (s : Script) :
    s.getSigOpCount = (((scanOps s.bytes.val).1.map fun o => opcodeSigOps o.1)).sum := by
  rw [Script.getSigOpCount, foldOps_eq, foldl_add_eq_sum]
  simp [List.map_map]
  rfl

/-- One opcode adds at most `MAX_PUBKEYS_PER_MULTISIG = 20` signature operations. -/
theorem opcodeSigOps_le (opcode : UInt8) : opcodeSigOps opcode ≤ 20 := by
  unfold opcodeSigOps maxPubkeysPerMultisig
  split
  · omega
  · split <;> omega

/-- The instructions that `scanOps` reads from `bs` add at most 20 signature operations for each byte of `bs`. -/
theorem scanOps_sigOps_le (bs : List UInt8) :
    (((scanOps bs).1.map fun o => opcodeSigOps o.1)).sum ≤ 20 * bs.length := by
  rw [scanOps]
  split
  · simp
  · rename_i o b r h
    have hlt := readOp_rest_length h
    have ih := scanOps_sigOps_le r
    have ho := opcodeSigOps_le o
    simp only [List.map_cons, List.sum_cons]
    omega
termination_by bs.length
decreasing_by exact readOp_rest_length ‹_›

/--
For every script, `Script.getSigOpCount` is at most 20 times the number of its bytes.
Each instruction has at least one byte and adds at most 20.
So a script of fewer than `2^32 / 20` bytes, about 214 million, has a count below `2^32`, and Core's `unsigned int` holds it without a wrap.
-/
@[theorem_tag property]
theorem Script.getSigOpCount_le (s : Script) : s.getSigOpCount ≤ 20 * s.bytes.val.length := by
  rw [Script.getSigOpCount_eq_scanOps]
  exact scanOps_sigOps_le s.bytes.val

end DogeLib.Transaction
