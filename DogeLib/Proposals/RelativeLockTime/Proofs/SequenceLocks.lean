module

public import DogeLib.Work.Proofs.MedianTimePast
public import DogeLib.Proposals.RelativeLockTime

/-!
# Proofs: the sequence locks of `Proposals.RelativeLockTime`

The rule-level theorems of design record 0012, section 9.2, for the rule of BIP 68.
Each theorem is about `sequenceLocks` for one transaction, on a supplied view and supplied coins.
None is a claim about a block, a chain or the network.

- `sequenceLocks_inactive`: with `active` false, or with a version below 2 as an unsigned value, the test accepts every transaction.
- `sequenceLocks_empty_view`: the test accepts on an empty view.
- `medianTimePast_range`: a median time past of a view is a 32-bit value that is not negative.
- `LockMet`: the lock of one input is met.
- `sequenceLocks_iff`: the characterization. For a version of at least 2 and a result that is not outside the model, the test accepts exactly when the view is empty, or the view has a median time past and each input meets its lock.
- `sequenceLocks_iff_of_view`: the same on a view that is not empty, where the test accepts exactly when each input meets its lock.
- `sequenceLocks_fits`: each sum of `CalculateSequenceLocks` fits its C++ type.
- `sequenceLocks_of_disabled`: a transaction whose inputs all have bit 31 set passes, when the view gives a median time past.
- `sequenceLocks_height_lock`, `sequenceLocks_time_lock`: the height lock and the time lock of one input of an accepted transaction.

## Hypotheses and where Core enforces them

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The result is not outside the model. | `sequenceLocks_iff` | The three reasons are limits of the specification (design record 0012, section 6.3). Core has no such result. |
| `calculateSequenceLocks` or `inputLock` has a result. | `sequenceLocks_fits`, `inputLock_fits` | Not a rule. A result implies that each coin height with a lock is below `2^31 - 65535`, because `inputLock` returns `heightOutOfDomain` for a larger height. So neither theorem has a separate hypothesis on the heights. |
| A block time is a 32-bit value. | `sequenceLocks_fits` | The type of `nTime`. |
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/--
The target `sequenceLocks_inactive` of design record 0012, section 9.2.
With `active` false, or with a version below 2 as an unsigned 32-bit value, `sequenceLocks` accepts.
For every view, height, index, transaction and list of coins.
-/
theorem sequenceLocks_inactive {active : Bool} {tx : Transaction} (h : active = false ∨ tx.version.toNat < 2)
    (view : List BlockIndex) (height index : Nat) (coins : List Coin) :
    sequenceLocks active view height index tx coins = .ok () := by
  unfold sequenceLocks sequenceLocksWith
  rcases h with h | h
  · simp [h]
  · simp [h]

/-- On an empty view, `sequenceLocks` accepts: a block without a predecessor is not applicable. For every `active`, height, index, transaction and list of coins. -/
theorem sequenceLocks_empty_view (active : Bool) (height index : Nat) (tx : Transaction) (coins : List Coin) :
    sequenceLocks active [] height index tx coins = .ok () := by
  unfold sequenceLocks sequenceLocksWith
  split <;> rfl

/-- A median time past that `Work.medianTimePast` returns is the time of a view entry, so it is not negative and it is below `2^32`. -/
theorem medianTimePast_range {view : List BlockIndex} {m : Int} (h : medianTimePast view = .ok m) :
    0 ≤ m ∧ m < 2 ^ 32 := by
  cases view with
  | nil => cases h
  | cons last rest =>
    obtain ⟨entry, -, htime⟩ := medianTimePast_mem last rest m h
    rw [← htime]
    unfold BlockIndex.getBlockTime
    have := entry.nTime.toNat_lt
    omega

/--
The lock of one input is met, for a block at `height` whose predecessor has the median time past `median`.
`sequence` is the sequence of the input, and `c` is the height of the coin that it spends.
An input with bit 31 set has no lock.
With bit 22 clear, the lock is `c + n ≤ height`, where `n` is the low 16 bits of the sequence.
With bit 22 set, the ancestor of the time lock has a median time past `t` (`ancestorMedianTimePast`), and the lock is `t + 512 * n ≤ median`.
-/
def LockMet (view : List BlockIndex) (height : Nat) (median : Int) (sequence : UInt32) (c : Nat) : Prop :=
  sequence.toNat &&& sequenceLockTimeDisableFlag = 0 →
    (sequence.toNat &&& sequenceLockTimeTypeFlag = 0 → c + (sequence.toNat &&& sequenceLockTimeMask) ≤ height) ∧
      (sequence.toNat &&& sequenceLockTimeTypeFlag ≠ 0 → ∃ t, ancestorMedianTimePast view height c = .ok t ∧
        t + 512 * ((sequence.toNat &&& sequenceLockTimeMask : Nat) : Int) ≤ median)

/-- The low 16 bits of a sequence are at most 65,535. -/
theorem sequence_mask_le (sequence : UInt32) : sequence.toNat &&& sequenceLockTimeMask ≤ 65535 :=
  Nat.and_le_right

/-- A shift by the granularity of a time lock is a product with 512. -/
theorem shift_granularity (n : Nat) : ((n <<< sequenceLockTimeGranularity : Nat) : Int) = 512 * (n : Int) := by
  simp only [sequenceLockTimeGranularity, Nat.shiftLeft_eq]
  omega

/--
The lock of one input, when `inputLock` has a result: the result passes its comparison exactly when the lock is met.
A height lock compares its last invalid height with `height`, and a time lock compares its last invalid time with `median`.
-/
theorem inputLock_met_iff {view : List BlockIndex} {height : Nat} {median : Int} {sequence : UInt32} {c : Nat}
    {lock : InputLock} (h : inputLock view height sequence c = .ok lock) :
    LockMet view height median sequence c ↔
      match lock with
      | .none => True
      | .height last => last < (height : Int)
      | .time last => last < median := by
  unfold inputLock at h
  unfold LockMet
  split at h
  · rename_i hd
    cases h
    simp [hd]
  · rename_i hd
    have hd' : sequence.toNat &&& sequenceLockTimeDisableFlag = 0 := by simpa using hd
    split at h
    · cases h
    · split at h
      · rename_i ht
        split at h
        · cases h
        · split at h
          · cases h
          · rename_i t hanc
            cases h
            simp only [hd', ht, hanc, forall_const, false_implies, true_and, ne_eq,
              not_false_eq_true, Except.ok.injEq, exists_eq_left', shift_granularity]
            omega
      · rename_i ht
        have ht' : sequence.toNat &&& sequenceLockTimeTypeFlag = 0 := by simpa using ht
        cases h
        simp only [hd', ht', forall_const, ne_eq, not_true_eq_false, false_implies, and_true]
        omega

/--
The pair of `calculateSequenceLocks` passes `evaluateSequenceLocks` exactly when the pair at the start passes and each input of the list meets its lock.
-/
theorem calculateSequenceLocks_evaluate_iff {view : List BlockIndex} {height : Nat} {median : Int} :
    ∀ {l : List (TxIn × Coin)} {start pair : Int × Int}, calculateSequenceLocks view height l start = .ok pair →
      (evaluateSequenceLocks height median pair = true ↔
        evaluateSequenceLocks height median start = true ∧
          ∀ p ∈ l, LockMet view height median p.1.sequence p.2.height)
  | [], start, pair, h => by
    simp only [calculateSequenceLocks, Except.ok.injEq] at h
    subst h
    simp
  | (input, coin) :: rest, start, pair, h => by
    unfold calculateSequenceLocks at h
    cases hl : inputLock view height input.sequence coin.height with
    | error r => simp [hl] at h
    | ok lock =>
      have hmet := inputLock_met_iff (median := median) hl
      cases lock with
      | none =>
        simp only [hl] at h
        rw [calculateSequenceLocks_evaluate_iff h]
        simp only [List.mem_cons, forall_eq_or_imp, hmet, true_and]
      | height last =>
        simp only [hl] at h
        rw [calculateSequenceLocks_evaluate_iff h]
        simp only [List.mem_cons, forall_eq_or_imp, hmet, evaluateSequenceLocks, Bool.and_eq_true,
          decide_eq_true_eq, Int.max_lt]
        exact ⟨fun ⟨⟨⟨a, l⟩, b⟩, r⟩ => ⟨⟨a, b⟩, l, r⟩, fun ⟨⟨a, b⟩, l, r⟩ => ⟨⟨⟨a, l⟩, b⟩, r⟩⟩
      | time last =>
        simp only [hl] at h
        rw [calculateSequenceLocks_evaluate_iff h]
        simp only [List.mem_cons, forall_eq_or_imp, hmet, evaluateSequenceLocks, Bool.and_eq_true,
          decide_eq_true_eq, Int.max_lt]
        exact ⟨fun ⟨⟨a, b, l⟩, r⟩ => ⟨⟨a, b⟩, l, r⟩, fun ⟨⟨a, b⟩, l, r⟩ => ⟨⟨a, b, l⟩, r⟩⟩

/--
The characterization of sequence locks on a view that is not empty.
Take `active` true, a view that is not empty, and a transaction whose version is at least 2 as an unsigned value.
Let the result of `sequenceLocks` not be outside the model.
Then the view has a median time past `median`, and `sequenceLocks` accepts exactly when each input meets its lock (`LockMet`).
Each input is paired with the coin at its position in `coins`.
With bit 31 set an input has no lock. With bit 22 clear the lock is `c + n ≤ height`. With bit 22 set it is `t + 512 * n ≤ median`.
For every height, index and list of coins.
-/
theorem sequenceLocks_iff_of_view {view : List BlockIndex} (hview : view ≠ []) {tx : Transaction} (hv : 2 ≤ tx.version.toNat)
    {height index : Nat} {coins : List Coin}
    (hs : ∀ r, sequenceLocks true view height index tx coins ≠ .unsupported r) :
    ∃ median, medianTimePast view = .ok median ∧
      (sequenceLocks true view height index tx coins = .ok () ↔
        ∀ p ∈ tx.inputs.val.zip coins, LockMet view height median p.1.sequence p.2.height) := by
  unfold sequenceLocks sequenceLocksWith at hs ⊢
  have hv' : ¬ tx.version.toNat < 2 := by omega
  cases view with
  | nil => exact absurd rfl hview
  | cons prev rest =>
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq, hv', ↓reduceIte] at hs ⊢
    split at hs
    · exact absurd rfl (hs _)
    · rename_i hh
      have hh' : prev.nHeight + 1 = height := by simpa using hh
      simp only [hh', ne_eq, not_true_eq_false, ↓reduceIte] at hs ⊢
      cases hmed : medianTimePast (prev :: rest) with
      | error e =>
        rw [hmed] at hs
        exact absurd rfl (hs _)
      | ok median =>
        rw [hmed] at hs
        refine ⟨median, rfl, ?_⟩
        simp only
        cases hcalc : calculateSequenceLocks (prev :: rest) height (tx.inputs.val.zip coins) (-1, -1) with
        | error r =>
          rw [hcalc] at hs
          exact absurd rfl (hs _)
        | ok pair =>
          have hiff := calculateSequenceLocks_evaluate_iff (median := median) hcalc
          have hstart : evaluateSequenceLocks height median (-1, -1) = true := by
            have := (medianTimePast_range hmed).1
            simp only [evaluateSequenceLocks, Bool.and_eq_true, decide_eq_true_eq]
            omega
          simp only [hstart, true_and] at hiff
          rw [← hiff]
          cases he : evaluateSequenceLocks height median pair <;> simp [he]

/--
The target `sequenceLocks_iff` of design record 0012, section 9.2: the characterization of sequence locks.
Take `active` true, and a transaction whose version is at least 2 as an unsigned value.
Let the result of `sequenceLocks` not be outside the model.
Then `sequenceLocks` accepts exactly when one of two conditions holds.
The view is empty: the block has no predecessor, and the rule does not apply to it (design record 0012, section 5).
Or the view has a median time past `median`, and each input meets its lock (`LockMet`), with the coin at its position in `coins`.
With bit 31 set an input has no lock. With bit 22 clear the lock is `c + n ≤ height`. With bit 22 set it is `t + 512 * n ≤ median`.
The statement has no hypothesis on the view. For every view, height, index and list of coins.
-/
theorem sequenceLocks_iff {view : List BlockIndex} {tx : Transaction} (hv : 2 ≤ tx.version.toNat)
    {height index : Nat} {coins : List Coin}
    (hs : ∀ r, sequenceLocks true view height index tx coins ≠ .unsupported r) :
    sequenceLocks true view height index tx coins = .ok () ↔
      view = [] ∨ ∃ median, medianTimePast view = .ok median ∧
        ∀ p ∈ tx.inputs.val.zip coins, LockMet view height median p.1.sequence p.2.height := by
  cases view with
  | nil => simp [sequenceLocks_empty_view]
  | cons prev rest =>
    obtain ⟨median, hmed, hiff⟩ := sequenceLocks_iff_of_view (List.cons_ne_nil prev rest) hv hs
    constructor
    · intro h
      exact .inr ⟨median, hmed, hiff.mp h⟩
    · rintro (h | ⟨m, hm, hall⟩)
      · cases h
      · rw [hmed] at hm
        cases hm
        exact hiff.mpr hall

/-! ## The sums of Core -/

/-- Core's `int`: a 32-bit signed value. -/
def FitsInt (x : Int) : Prop := -2 ^ 31 ≤ x ∧ x < 2 ^ 31

/-- Core's `int64_t`: a 64-bit signed value. -/
def FitsInt64 (x : Int) : Prop := -2 ^ 63 ≤ x ∧ x < 2 ^ 63

/--
The sums of one input fit their C++ types.
When `inputLock` has a result for a coin at the height `c`, the height `c` and the height `c - 1` of line 348 fit `int`.
The last invalid height of a height lock fits `int`, with the sum `c + n` before the subtraction of 1.
The last invalid time of a time lock fits `int64_t`, with the sum `t + 512 * n` before the subtraction of 1.
-/
theorem inputLock_fits {view : List BlockIndex} {height : Nat} {sequence : UInt32} {c : Nat} {lock : InputLock}
    (h : inputLock view height sequence c = .ok lock) :
    match lock with
    | .none => True
    | .height last => FitsInt c ∧ FitsInt (last + 1) ∧ FitsInt last
    | .time last => FitsInt c ∧ FitsInt ((c : Int) - 1) ∧ FitsInt64 (last + 1) ∧ FitsInt64 last := by
  unfold inputLock at h
  have hn := sequence_mask_le sequence
  split at h
  · cases h
    trivial
  · split at h
    · cases h
    · rename_i hc
      have hc' : c < 2 ^ 31 - 65535 := by simpa [coinHeightBound] using hc
      split at h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i t hanc
            cases h
            have ht := medianTimePast_range hanc
            simp only [FitsInt, FitsInt64, shift_granularity]
            omega
      · cases h
        simp only [FitsInt]
        omega

/--
Each pair of `calculateSequenceLocks` fits its C++ types: when the pair at the start fits `int` and `int64_t`, so does the result.
-/
theorem calculateSequenceLocks_fits {view : List BlockIndex} {height : Nat} :
    ∀ {l : List (TxIn × Coin)} {start pair : Int × Int}, calculateSequenceLocks view height l start = .ok pair →
      FitsInt start.1 → FitsInt64 start.2 → FitsInt pair.1 ∧ FitsInt64 pair.2
  | [], start, pair, h, h1, h2 => by
    simp only [calculateSequenceLocks, Except.ok.injEq] at h
    subst h
    exact ⟨h1, h2⟩
  | (input, coin) :: rest, start, pair, h, h1, h2 => by
    unfold calculateSequenceLocks at h
    cases hl : inputLock view height input.sequence coin.height with
    | error r => simp [hl] at h
    | ok lock =>
      have hfit := inputLock_fits hl
      cases lock with
      | none =>
        simp only [hl] at h
        exact calculateSequenceLocks_fits h h1 h2
      | height last =>
        simp only [hl] at h
        refine calculateSequenceLocks_fits h ?_ h2
        simp only [FitsInt] at h1 hfit ⊢
        omega
      | time last =>
        simp only [hl] at h
        refine calculateSequenceLocks_fits h h1 ?_
        simp only [FitsInt64] at h2 hfit ⊢
        omega

/--
The target `sequenceLocks_fits` of design record 0012, section 9.2.
Take a transaction for which `calculateSequenceLocks` has a result from Core's start (-1, -1).
Then `nMinHeight` fits `int` and `nMinTime` fits `int64_t`, after every input.
`inputLock_fits` gives the same for each term of the two maxima, and for the sums before the subtraction of 1.

Its one hypothesis is that `calculateSequenceLocks` has a result. It has no separate hypothesis on the heights or the times.
`inputLock` returns `heightOutOfDomain` for a coin height of at least `2^31 - 65535`, so a result implies the height bound of design record 0012, section 7.2.
A median time past is the time of a view entry, which is a 32-bit value.
The height of the block is an argument of `EvaluateSequenceLocks` alone, and enters no sum.
-/
theorem sequenceLocks_fits {view : List BlockIndex} {height : Nat} {l : List (TxIn × Coin)} {pair : Int × Int}
    (h : calculateSequenceLocks view height l (-1, -1) = .ok pair) : FitsInt pair.1 ∧ FitsInt64 pair.2 :=
  calculateSequenceLocks_fits h (by simp only [FitsInt]; omega) (by simp only [FitsInt64]; omega)

/-! ## Transactions without a lock, and one height lock -/

/-- With every sequence of the list at bit 31 set, `calculateSequenceLocks` returns the pair at the start. -/
theorem calculateSequenceLocks_of_disabled {view : List BlockIndex} {height : Nat} :
    ∀ {l : List (TxIn × Coin)} {start : Int × Int},
      (∀ p ∈ l, p.1.sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0) →
        calculateSequenceLocks view height l start = .ok start
  | [], _, _ => rfl
  | (input, coin) :: rest, start, h => by
    have h0 : input.sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0 := h (input, coin) (List.Mem.head _)
    unfold calculateSequenceLocks
    simp only [inputLock, h0, ne_eq, not_false_eq_true, ↓reduceIte]
    exact calculateSequenceLocks_of_disabled fun p hp => h p (List.mem_cons_of_mem _ hp)

/--
A transaction without a lock passes.
Take a view whose first entry is at the height below `height`, and which has a median time past.
Let every input of the transaction have a sequence with bit 31 set.
Then `sequenceLocks` accepts, for every `active`, index and list of coins.
-/
theorem sequenceLocks_of_disabled {prev : BlockIndex} {rest : List BlockIndex} {height : Nat} {median : Int}
    (hheight : prev.nHeight + 1 = height) (hmed : medianTimePast (prev :: rest) = .ok median) {tx : Transaction}
    (hd : ∀ input ∈ tx.inputs.val, input.sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0) (active : Bool)
    (index : Nat) (coins : List Coin) :
    sequenceLocks active (prev :: rest) height index tx coins = .ok () := by
  unfold sequenceLocks sequenceLocksWith
  split
  · rfl
  · simp only [hheight, ne_eq, not_true_eq_false, ↓reduceIte, hmed]
    rw [calculateSequenceLocks_of_disabled fun p hp => hd p.1 (List.of_mem_zip hp).1]
    have := (medianTimePast_range hmed).1
    have hstart : evaluateSequenceLocks height median (-1, -1) = true := by
      simp only [evaluateSequenceLocks, Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp [hstart]

/--
The height lock of one input of an accepted transaction.
Take `active` true, a view that is not empty, and a transaction with a version of at least 2 that `sequenceLocks` accepts.
Let the input at position `j` have a sequence with bits 31 and 22 clear, and let `coin` be the coin at position `j`.
Then the height of the coin plus the low 16 bits of the sequence is at most the height of the block.
-/
theorem sequenceLocks_height_lock {view : List BlockIndex} (hview : view ≠ []) {tx : Transaction}
    (hv : 2 ≤ tx.version.toNat) {height index : Nat} {coins : List Coin}
    (hok : sequenceLocks true view height index tx coins = .ok ()) {j : Nat} {input : TxIn} {coin : Coin}
    (hin : tx.inputs.val[j]? = some input) (hcoin : coins[j]? = some coin)
    (hd : input.sequence.toNat &&& sequenceLockTimeDisableFlag = 0)
    (ht : input.sequence.toNat &&& sequenceLockTimeTypeFlag = 0) :
    coin.height + (input.sequence.toNat &&& sequenceLockTimeMask) ≤ height := by
  obtain ⟨median, -, hiff⟩ := sequenceLocks_iff_of_view hview hv (index := index) (height := height) (coins := coins)
    (fun r hr => by rw [hok] at hr; cases hr)
  have hmem : (input, coin) ∈ tx.inputs.val.zip coins := by
    apply List.mem_of_getElem? (i := j)
    simp [List.getElem?_zip_eq_some, hin, hcoin]
  exact ((hiff.mp hok) (input, coin) hmem hd).1 ht

/--
The time lock of one input of an accepted transaction.
Take `active` true, a view that is not empty, and a transaction with a version of at least 2 that `sequenceLocks` accepts.
Let the input at position `j` have a sequence with bit 31 clear and bit 22 set, and let `coin` be the coin at position `j`.
Then the view has a median time past `median`, and the ancestor of the coin has a median time past `t` (`ancestorMedianTimePast`).
`t` plus 512 times the low 16 bits of the sequence is at most `median`.
-/
theorem sequenceLocks_time_lock {view : List BlockIndex} (hview : view ≠ []) {tx : Transaction}
    (hv : 2 ≤ tx.version.toNat) {height index : Nat} {coins : List Coin}
    (hok : sequenceLocks true view height index tx coins = .ok ()) {j : Nat} {input : TxIn} {coin : Coin}
    (hin : tx.inputs.val[j]? = some input) (hcoin : coins[j]? = some coin)
    (hd : input.sequence.toNat &&& sequenceLockTimeDisableFlag = 0)
    (ht : input.sequence.toNat &&& sequenceLockTimeTypeFlag ≠ 0) :
    ∃ median t, medianTimePast view = .ok median ∧ ancestorMedianTimePast view height coin.height = .ok t ∧
      t + 512 * ((input.sequence.toNat &&& sequenceLockTimeMask : Nat) : Int) ≤ median := by
  obtain ⟨median, hmed, hiff⟩ := sequenceLocks_iff_of_view hview hv (index := index) (height := height)
    (coins := coins) (fun r hr => by rw [hok] at hr; cases hr)
  have hmem : (input, coin) ∈ tx.inputs.val.zip coins := by
    apply List.mem_of_getElem? (i := j)
    simp [List.getElem?_zip_eq_some, hin, hcoin]
  obtain ⟨t, hanc, hle⟩ := ((hiff.mp hok) (input, coin) hmem hd).2 ht
  exact ⟨median, t, hmed, hanc, hle⟩

end DogeLib.Proposals.RelativeLockTime
