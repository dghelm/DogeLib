module

public import DogeLib.Block.ContextualBody
public import DogeLib.Proposals.Framework.Block

/-!
# Proofs: the lock-time cutoff of `ContextualCheckBlock`

Facts about the baseline definitions `isFinalTx`, `checkFinality` and `contextualCheckBlockBody` of `DogeLib.Block.ContextualBody`.
Extension E3 of design record 0012 lets a revision set the lock-time arguments of `contextualCheckBlockBody`.
These theorems say how its result depends on those arguments.
They are rule-level: each is about one call of a baseline function, for every block and height.

`contextualCheckBlockBody` reads `csvActive` and the median time past only through the lock-time cutoff (`contextualCheckBlockBody_eq_of_cutoff`).
The cutoff is `lockTimeCutoff`: the median time past with `csvActive` true, and the time of the block otherwise.

- `isFinalTx_mono`: a transaction that is final at a cutoff is final at every later cutoff. A target of design record 0012, section 9.2.
- `checkFinality_mono`, `contextualCheckBlockBody_cutoff_mono`: the same for the finality loop and for the body. A body that accepts at a cutoff accepts at every later cutoff.
- `contextualCheckBlockBody_csv_restricts`: let the median time past be at most the time of the block. A body that accepts with `csvActive` true accepts with `csvActive` false. A target of design record 0012, section 9.2.
- `CutoffUntouched` and `contextualCheckBlockBody_eq_of_untouched`: take two cutoffs, and a block in which no transaction has a time lock time between them with an input that is not final. The body gives one result at both.

Core enforces the hypothesis of `contextualCheckBlockBody_csv_restricts` in `ContextualCheckBlockHeader`, with the reason `time-too-old` (SOURCES.md, D33, line 3104).
`validateBlock` runs that check first, so no block-level theorem assumes it.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Block DogeLib.Transaction

/--
The target `isFinalTx_mono` of design record 0012, section 9.2.
For every transaction and height: if `isFinalTx` holds at the cutoff `t`, and `t ≤ t'`, it holds at the cutoff `t'`.
-/
theorem isFinalTx_mono {tx : Transaction} {height : Nat} {t t' : Int} (h : isFinalTx tx height t = true)
    (hle : t ≤ t') : isFinalTx tx height t' = true := by
  unfold isFinalTx at h ⊢
  split
  · rfl
  · rename_i hz
    rw [ite_eq_right hz] at h
    by_cases hth : tx.lockTime.toNat < lockTimeThreshold
    · simpa only [hth, ↓reduceIte] using h
    · simp only [hth, ↓reduceIte] at h ⊢
      split at h
      · rename_i hlt
        rw [ite_eq_left (by omega)]
      · split
        · rfl
        · exact h

/-- If the finality loop accepts a list of transactions at the cutoff `t`, and `t ≤ t'`, it accepts the list at the cutoff `t'`. -/
theorem checkFinality_mono {height : Nat} {t t' : Int} (hle : t ≤ t') :
    ∀ {txs : List Transaction}, checkFinality height t txs = .ok () → checkFinality height t' txs = .ok ()
  | [], _ => rfl
  | tx :: rest, h => by
    unfold checkFinality at h ⊢
    split at h
    · rename_i hf
      rw [ite_eq_left (isFinalTx_mono hf hle)]
      exact checkFinality_mono hle h
    · cases h

/-- `contextualCheckBlockBody` reads its lock-time arguments only through the cutoff: two pairs of arguments with one `lockTimeCutoff` give one result. -/
theorem contextualCheckBlockBody_eq_of_cutoff {height : Nat} {args args' : Bool × Int} {segwitActive : Bool}
    {b : Block} (h : lockTimeCutoff args b = lockTimeCutoff args' b) :
    contextualCheckBlockBody height args.2 args.1 segwitActive b =
      contextualCheckBlockBody height args'.2 args'.1 segwitActive b := by
  unfold lockTimeCutoff at h
  unfold contextualCheckBlockBody
  simp only [h]

/--
If `contextualCheckBlockBody` accepts a block with the lock-time arguments `args`, and the cutoff of `args` is at most the cutoff of `args'`, it accepts the block with `args'`.
For every height, SegWit state and block. The cutoff is `lockTimeCutoff`.
-/
theorem contextualCheckBlockBody_cutoff_mono {height : Nat} {args args' : Bool × Int} {segwitActive : Bool}
    {b : Block} (hle : lockTimeCutoff args b ≤ lockTimeCutoff args' b)
    (h : contextualCheckBlockBody height args.2 args.1 segwitActive b = .ok ()) :
    contextualCheckBlockBody height args'.2 args'.1 segwitActive b = .ok () := by
  unfold lockTimeCutoff at hle
  unfold contextualCheckBlockBody at h ⊢
  simp only at h ⊢
  cases hf : checkFinality height (if args.1 = true then args.2 else (b.header.pure.nTime.toNat : Int))
      b.transactions with
  | error e => simp [hf] at h
  | ok u =>
    cases u
    rw [hf] at h
    rw [checkFinality_mono hle hf]
    exact h

/--
The target `contextualCheckBlockBody_csv_restricts` of design record 0012, section 9.2.
Let the median time past `m` be at most the time of the block.
If `contextualCheckBlockBody` accepts the block with `csvActive` true and `m`, it accepts the block with `csvActive` false.
The height, the SegWit state and the block are equal in both calls, and the second call reads no median time past, so it takes any value `m'`.
-/
theorem contextualCheckBlockBody_csv_restricts {height : Nat} {m m' : Int} {segwitActive : Bool} {b : Block}
    (hm : m ≤ (b.header.pure.nTime.toNat : Int))
    (h : contextualCheckBlockBody height m true segwitActive b = .ok ()) :
    contextualCheckBlockBody height m' false segwitActive b = .ok () :=
  contextualCheckBlockBody_cutoff_mono (args := (true, m)) (args' := (false, m'))
    (by simpa [lockTimeCutoff] using hm) h

/--
No transaction of the list separates the cutoffs `t` and `t'`.
A transaction separates them under two conditions.
Its lock time is a time (at least `LOCKTIME_THRESHOLD`) from the lower cutoff to below the higher one.
One of its inputs has a sequence other than `SEQUENCE_FINAL`.
The statement is for `t ≤ t'`.
-/
def CutoffUntouched (t t' : Int) (txs : List Transaction) : Prop :=
  ∀ tx ∈ txs, lockTimeThreshold ≤ tx.lockTime.toNat → t ≤ (tx.lockTime.toNat : Int) →
    (tx.lockTime.toNat : Int) < t' → tx.inputs.val.all (fun i => i.sequence == contextualSequenceFinal) = true

/-- For `t ≤ t'`: a transaction that does not separate the two cutoffs is final at both or at neither. -/
theorem isFinalTx_eq_of_untouched {tx : Transaction} {height : Nat} {t t' : Int}
    (h : lockTimeThreshold ≤ tx.lockTime.toNat → t ≤ (tx.lockTime.toNat : Int) → (tx.lockTime.toNat : Int) < t' →
      tx.inputs.val.all (fun i => i.sequence == contextualSequenceFinal) = true) (hle : t ≤ t') :
    isFinalTx tx height t = isFinalTx tx height t' := by
  unfold isFinalTx
  split
  · rfl
  · by_cases hth : tx.lockTime.toNat < lockTimeThreshold
    · simp only [hth, ↓reduceIte]
    · simp only [hth, ↓reduceIte]
      by_cases h1 : (tx.lockTime.toNat : Int) < t
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : (tx.lockTime.toNat : Int) < t'
        · rw [ite_eq_left h2]
          exact h (by omega) (by omega) h2
        · rw [ite_eq_right h2]

/-- For `t ≤ t'`: on a list with `CutoffUntouched t t'`, the finality loop gives one result at both cutoffs. -/
theorem checkFinality_eq_of_untouched {height : Nat} {t t' : Int} (hle : t ≤ t') :
    ∀ {txs : List Transaction}, CutoffUntouched t t' txs → checkFinality height t txs = checkFinality height t' txs
  | [], _ => rfl
  | tx :: rest, h => by
    unfold checkFinality
    rw [isFinalTx_eq_of_untouched (h tx (by simp)) hle,
      checkFinality_eq_of_untouched hle (fun x hx => h x (by simp [hx]))]

/--
Take two pairs of lock-time arguments whose cutoffs are `t ≤ t'`, and a block with `CutoffUntouched t t'` on its transactions.
Then `contextualCheckBlockBody` gives one result for both pairs: the same acceptance, rejection or adapter error.
For every height and SegWit state.
-/
theorem contextualCheckBlockBody_eq_of_untouched {height : Nat} {args args' : Bool × Int} {segwitActive : Bool}
    {b : Block} (hle : lockTimeCutoff args b ≤ lockTimeCutoff args' b)
    (h : CutoffUntouched (lockTimeCutoff args b) (lockTimeCutoff args' b) b.transactions) :
    contextualCheckBlockBody height args.2 args.1 segwitActive b =
      contextualCheckBlockBody height args'.2 args'.1 segwitActive b := by
  unfold lockTimeCutoff at hle h
  unfold contextualCheckBlockBody
  simp only
  rw [checkFinality_eq_of_untouched hle h]

end DogeLib.Proposals.Framework
