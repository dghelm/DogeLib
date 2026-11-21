module

public import DogeLib.Block.SigOpCost
public import DogeLib.Transaction.Proofs.SigOps

/-!
# Proofs: the linear readers of the signature-operation cost

`getSigOpCountAccurate` and `p2shSigOpCount` read scripts with the linear reader `nextOp` (issue #149).
This module proves each equal to its reference expression with `scanOps` or `lastPushFrom`.

- `getSigOpCountAccurate_eq_scanOps`: the accurate count is `accurateSigOps` over the opcodes of `scanOps`.
- `lastPushFrom_eq_lastPushLoop`: from every cursor, `lastPushLoop` on the bytes after the cursor gives the result of `lastPushFrom`.
- `p2shSigOpCount_eq_lastPushFrom`: the count of a P2SH input is the accurate count of the data that `lastPushFrom` gives, and 0 when it gives none.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script

/-- For every list of opcodes, opcode `last` and count `acc`: the left fold of `accurateStep` from `(last, acc)` ends with the count `acc + accurateSigOps last l`. -/
theorem foldl_accurateStep : ∀ (l : List UInt8) (last : UInt8) (acc : Nat),
    (l.foldl accurateStep (last, acc)).2 = acc + accurateSigOps last l
  | [], _, _ => by simp [accurateSigOps]
  | o :: l, last, acc => by
    rw [List.foldl_cons, accurateStep, foldl_accurateStep l]
    simp only [accurateSigOps]; omega

/--
For every script, `getSigOpCountAccurate` is `accurateSigOps` from `OP_INVALIDOPCODE` over the opcodes of the instructions that `scanOps` reads.
-/
theorem getSigOpCountAccurate_eq_scanOps (script : List UInt8) :
    getSigOpCountAccurate script = accurateSigOps opInvalidOpcode ((scanOps script).1.map Prod.fst) := by
  rw [getSigOpCountAccurate, foldOps_eq, foldl_accurateStep]
  simp

/-- For all bytes `bs` with no instruction for `nextOp`: `lastPushLoop` gives `data` at the end of the script and `none` otherwise. -/
theorem lastPushLoop_of_none {bs data : List UInt8} (h : nextOp bs = none) :
    lastPushLoop bs data = if bs.isEmpty then some data else none := by
  rw [lastPushLoop]; split
  · rfl
  · rename_i h'; rw [h] at h'; cases h'

/-- For all bytes `bs` whose next instruction is `s`: `lastPushLoop` gives `none` for an opcode above `OP_16`. Otherwise it goes on after `s` with its data. -/
theorem lastPushLoop_of_some {bs data : List UInt8} {s : OpStep} (h : nextOp bs = some s) :
    lastPushLoop bs data = if s.opcode > op16 then none else lastPushLoop s.rest s.data := by
  rw [lastPushLoop]; split
  · rename_i h'; rw [h] at h'; cases h'
  · rename_i s' h'; rw [h] at h'; cases h'; rfl

/--
For every script, cursor `pc` and data `data`: `lastPushFrom script pc data` is `lastPushLoop` on the bytes of `script` after `pc`, with the same data.
The two loops read the same instructions and give the same result.
-/
theorem lastPushFrom_eq_lastPushLoop (script : List UInt8) (pc : Nat) (data : List UInt8) :
    lastPushFrom script pc data = lastPushLoop (script.drop pc) data := by
  have hv := nextOp_view (script.drop pc)
  rw [lastPushFrom]
  split
  · -- At the end of the script.
    rename_i hri
    unfold readInstruction at hri
    split at hri
    · cases hri
    · rename_i hr
      have hd : script.drop pc = [] := by
        rcases readOp_eq_stop_iff.mp hr with ⟨h, -⟩ | ⟨_, _, _, _, h | h⟩
        · exact h
        · exact absurd h.2 (by simp)
        · exact absurd h.2.2 (by simp)
      rw [lastPushLoop_of_none (by rw [hd]; rfl), hd]; rfl
    · cases hri
  · -- A failed read.
    rename_i hri
    unfold readInstruction at hri
    split at hri
    · cases hri
    · cases hri
    · rename_i o lf hr
      rw [hr] at hv
      have hne : (script.drop pc).isEmpty = false := by
        cases h : script.drop pc with
        | nil => rw [h] at hr; simp [readOp] at hr
        | cons _ _ => rfl
      cases h : nextOp (script.drop pc) with
      | none => rw [lastPushLoop_of_none h, hne]; rfl
      | some s => rw [h] at hv; simp [OpRead.view] at hv
  · -- An instruction.
    rename_i i hri
    unfold readInstruction at hri
    split at hri
    · rename_i o b r hr
      cases hri
      rw [hr] at hv
      have happ := readOp_op_append hr
      obtain ⟨s, hn⟩ : ∃ s, nextOp (script.drop pc) = some s := by
        cases h : nextOp (script.drop pc) with
        | none => rw [h] at hv; simp [OpRead.view] at hv
        | some s => exact ⟨s, rfl⟩
      rw [hn] at hv
      simp only [Option.map_some, OpStep.view, OpRead.view, Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨ho, hdata, hrest⟩ := hv
      have hd : script.drop (pc + b.length) = s.rest := by
        rw [← List.drop_drop, ← happ, hrest]; simp
      rw [lastPushLoop_of_some hn, ho, hdata]
      split
      · rfl
      · rw [lastPushFrom_eq_lastPushLoop script (pc + b.length), hd]
    · cases hri
    · cases hri
termination_by script.length - pc
decreasing_by
  have := readInstruction_progress ‹_›
  simp only at this
  omega

/--
For every `scriptSig`, `p2shSigOpCount` is 0 when `lastPushFrom scriptSig 0 []` gives `none`, and otherwise the accurate count of the redeem script that it gives.
-/
theorem p2shSigOpCount_eq_lastPushFrom (scriptSig : List UInt8) :
    p2shSigOpCount scriptSig =
      match lastPushFrom scriptSig 0 [] with
      | none => 0
      | some redeem => getSigOpCountAccurate redeem := by
  rw [lastPushFrom_eq_lastPushLoop, List.drop_zero]
  rfl

end DogeLib.Block
