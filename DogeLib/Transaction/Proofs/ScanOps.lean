module

public import DogeLib.Transaction.Proofs.LegacySighashReference

/-!
# Proofs: complete parses of script code

`legacySignatureHashPlan_eq_reference` needs script code whose instructions all parse: `(scanOps s).2 = []`.
This module proves that the property survives the operations that build script code.

- `readOp_append`: an instruction that `readOp` reads stays the same when bytes follow it.
- `scanOps_append`, `scanOps_append_snd`: after a fully parsed head, the parse of a concatenation is the parse of the tail.
- `scanOps_drop`: a cursor at an instruction boundary of a fully parsed script leaves a fully parsed suffix.
- `findAndDelete_scanOps`: `FindAndDelete` keeps a fully parsed script fully parsed, when the pattern parses or is longer than the script.

The hypothesis on the pattern is needed.
The script `02 4c 01` parses as one push, and the pattern `02` matches at its start.
The bytes that remain, `4c 01`, are a short `OP_PUSHDATA1`.
-/

@[expose] public section

namespace DogeLib.Transaction

/-- For all bytes `bs` and `t`: if `readOp` reads an instruction from `bs`, it reads the same instruction from `bs ++ t`, and `t` follows the rest. -/
theorem readOp_append {bs : List UInt8} {o : UInt8} {b r : List UInt8} (h : readOp bs = .op o b r)
    (t : List UInt8) : readOp (bs ++ t) = .op o b (r ++ t) := by
  obtain ⟨lf, data, h1, h2, h3, rfl⟩ := readOp_eq_op_iff.mp h
  exact readOp_eq_op_iff.mpr ⟨lf, data, h1, h2, h3, by simp⟩

/-- For all bytes `bs`: the bytes of an instruction that `readOp` reads are that instruction alone. -/
theorem readOp_bytes {bs : List UInt8} {o : UInt8} {b r : List UInt8} (h : readOp bs = .op o b r) :
    readOp b = .op o b [] := by
  obtain ⟨lf, data, h1, h2, h3, -⟩ := readOp_eq_op_iff.mp h
  exact readOp_eq_op_iff.mpr ⟨lf, data, h1, h2, h3, by simp⟩

/-- The empty script parses completely. -/
theorem scanOps_nil : scanOps [] = ([], []) := scanOps_of_stop (p := []) rfl

/-- For all bytes `bs`: the bytes of an instruction that `readOp` reads parse completely. -/
theorem scanOps_bytes {bs : List UInt8} {o : UInt8} {b r : List UInt8} (h : readOp bs = .op o b r) :
    (scanOps b).2 = [] := by
  rw [scanOps_of_op (readOp_bytes h), scanOps_nil]

/-- For every opcode above `OP_PUSHDATA4`, the one-byte script of that opcode parses completely. -/
theorem scanOps_opcode {op : UInt8} (h : 0x4e < op) : (scanOps [op]).2 = [] :=
  scanOps_bytes (bs := [op]) (o := op) (r := [])
    (readOp_eq_op_iff.mpr ⟨[], [], by simp [lengthFieldWidth_of_gt h], by simp [pushSize_of_gt h], rfl, rfl⟩)

/-- For every fully parsed script `a` and all bytes `t`: the instructions of `a ++ t` are those of `a`, then those of `t`, and the unparsed bytes are those of `t`. -/
theorem scanOps_append (a : List UInt8) (ha : (scanOps a).2 = []) (t : List UInt8) :
    scanOps (a ++ t) = ((scanOps a).1 ++ (scanOps t).1, (scanOps t).2) := by
  cases hr : readOp a with
  | stop p =>
    rw [scanOps_of_stop hr] at ha ⊢
    dsimp only at ha
    subst ha
    rw [readOp_stop_nil hr]
    simp
  | op o b r =>
    rw [scanOps_of_op hr] at ha ⊢
    dsimp only at ha
    rw [scanOps_of_op (readOp_append hr t), scanOps_append r ha t]
    simp
termination_by a.length
decreasing_by exact readOp_rest_length hr

/-- For every fully parsed script `a` and all bytes `t`: `a ++ t` parses completely exactly when `t` does. -/
theorem scanOps_append_snd {a : List UInt8} (ha : (scanOps a).2 = []) (t : List UInt8) :
    (scanOps (a ++ t)).2 = (scanOps t).2 := by
  rw [scanOps_append a ha t]

/--
For every fully parsed script `s` and cursor `pc` at an instruction boundary, the suffix from `pc` parses completely.
The cursor is at an instruction boundary when the first `pc` bytes parse completely.
-/
theorem scanOps_drop {s : List UInt8} {pc : Nat} (hs : (scanOps s).2 = []) (hpc : (scanOps (s.take pc)).2 = []) :
    (scanOps (s.drop pc)).2 = [] := by
  rw [← scanOps_append_snd hpc, List.take_append_drop]
  exact hs

/-- For every fully parsed `rest`, and a pattern that parses or is longer than `rest`: the bytes after the leading copies of the pattern parse completely. -/
theorem dropMatches_scanOps (b rest : List UInt8) (hr : (scanOps rest).2 = [])
    (hb : (scanOps b).2 = [] ∨ rest.length < b.length) : (scanOps (dropMatches b rest).1).2 = [] := by
  rw [dropMatches]
  split
  · rename_i h
    obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp h.2
    have hdrop : rest.drop b.length = t := by rw [← ht]; simp
    have hpos := List.length_pos_iff.mpr h.1
    rcases hb with hb | hb
    · have ht' : (scanOps t).2 = [] := by rw [← ht, scanOps_append_snd hb] at hr; exact hr
      exact dropMatches_scanOps b (rest.drop b.length) (by rw [hdrop]; exact ht') (Or.inl hb)
    · have := congrArg List.length ht
      simp only [List.length_append] at this
      omega
  · exact hr
termination_by rest.length
decreasing_by
  rw [hdrop, ← ht, List.length_append]
  omega

/-- For every fully parsed `rest`, and a pattern that parses or is longer than `rest`: the output of the deletion loop parses completely. -/
theorem findAndDeleteLoop_scanOps (b rest : List UInt8) (hr : (scanOps rest).2 = [])
    (hb : (scanOps b).2 = [] ∨ rest.length < b.length) : (scanOps (findAndDeleteLoop b rest).1).2 = [] := by
  have hd := dropMatches_scanOps b rest hr hb
  have hdl := dropMatches_length_le b rest
  cases h : readOp (dropMatches b rest).1 with
  | op o bytes r =>
    rw [findAndDeleteLoop_of_op h]
    have hr' : (scanOps r).2 = [] := by rw [scanOps_of_op h] at hd; exact hd
    have hrl := readOp_rest_length h
    rw [scanOps_append_snd (scanOps_bytes h)]
    exact findAndDeleteLoop_scanOps b r hr' (hb.imp_right fun hlt => by omega)
  | stop p =>
    rw [findAndDeleteLoop_of_stop h]
    exact hd
termination_by rest.length
decreasing_by
  have := readOp_rest_length h
  omega

/--
For every fully parsed script `s`, and every pattern `b` that parses completely or is longer than `s`:
the script that `FindAndDelete` returns parses completely.
-/
theorem findAndDelete_scanOps {s b : List UInt8} (hs : (scanOps s).2 = [])
    (hb : (scanOps b).2 = [] ∨ s.length < b.length) : (scanOps (findAndDelete s b).1).2 = [] := by
  unfold findAndDelete
  split
  · exact hs
  · dsimp only
    split
    · exact hs
    · exact findAndDeleteLoop_scanOps b s hs hb

end DogeLib.Transaction
