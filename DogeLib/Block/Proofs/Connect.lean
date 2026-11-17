module

public import DogeLib.Block.Connect
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of `checkTxInputs` and `connectBlock`

The arithmetic domain of design record 0010, section 3, and the unreachable reasons of its section 5.

- `checkTxInputs_ne_feeNegative` and `checkTxInputs_ne_feeOutOfRange`: `checkTxInputs` never returns the two fee failures, whose reasons are `bad-txns-fee-negative` and `bad-txns-fee-outofrange`.
- `connectBlock_ne_feeNegative` and `connectBlock_ne_feeOutOfRange`: so `connectBlock` never rejects a block with either reason.
- `connect_fits`: `connectBlock` never returns `outOfDomain` when every coin of the set has an amount from 0 to `MAX_MONEY`, and the coins that the block's inputs spend, plus `MAX_MONEY` and the subsidy, are below `2^63`.

The theorems are about the Lean definitions.
`outOfDomain` marks the sums where Core's `int64_t` arithmetic would be undefined.
So `connect_fits` gives a condition under which the Lean result describes a Core execution with no signed overflow in those sums.
It does not prove that Core's compiled code computes the same sums.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script

/-! ## `checkTxInputs` -/

/-- The loop over the inputs returns only its own three errors. -/
theorem checkInputValues_error {spendHeight : Nat} : ∀ {coins : List Coin} {acc : Int} {e : CheckTxInputsError},
    checkInputValues spendHeight acc coins = .error e →
      e = .prematureSpendOfCoinbase ∨ e = .outOfDomain ∨ e = .inputValuesOutOfRange
  | [], _, _, h => by simp [checkInputValues] at h
  | c :: rest, acc, e, h => by
    unfold checkInputValues at h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · split at h
        · cases h; simp
        · exact checkInputValues_error h

/-- When the loop over the inputs accepts, its result is the starting sum plus the amounts of the coins. -/
theorem checkInputValues_ok_sum {spendHeight : Nat} : ∀ {coins : List Coin} {acc total : Int},
    checkInputValues spendHeight acc coins = .ok total → total = acc + (coins.map Coin.value).sum
  | [], acc, total, h => by simp [checkInputValues] at h; simp [h]
  | c :: rest, acc, total, h => by
    unfold checkInputValues at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · have := checkInputValues_ok_sum h
          simp only [List.map_cons, List.sum_cons]
          omega

/-- When the loop over the inputs accepts from a sum in `MoneyRange`, its result is in `MoneyRange`. -/
theorem checkInputValues_ok_range {spendHeight : Nat} : ∀ {coins : List Coin} {acc total : Int},
    0 ≤ acc → acc ≤ maxMoney → checkInputValues spendHeight acc coins = .ok total →
      0 ≤ total ∧ total ≤ maxMoney
  | [], acc, total, h0, h1, h => by
    simp [checkInputValues] at h
    subst h
    exact ⟨h0, h1⟩
  | c :: rest, acc, total, _, _, h => by
    unfold checkInputValues at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hrange
          simp [moneyRange] at hrange
          exact checkInputValues_ok_range (by omega) (by omega) h

/--
`checkTxInputs` never returns `feeNegative`, whose reject reason is `bad-txns-fee-negative`.
The statement before Core's test returns when the coins are worth less than the outputs (D112, lines 1447 to 1454).
-/
@[theorem_tag property]
theorem checkTxInputs_ne_feeNegative (spendHeight : Nat) (coins : List Coin) (valueOut : Int) :
    checkTxInputs spendHeight coins valueOut ≠ .error .feeNegative := by
  unfold checkTxInputs
  split
  · rename_i e he
    intro h
    cases h
    rcases checkInputValues_error he with h | h | h <;> cases h
  · split
    · simp
    · split
      · omega
      · split <;> simp

/--
For an output total that is not negative, `checkTxInputs` never returns `feeOutOfRange`, whose reject reason is `bad-txns-fee-outofrange`.
The fee is at most the sum of the coins, which the loop over the inputs keeps at most `MAX_MONEY` (D112, lines 1441 to 1457).
`CheckTransaction` gives the hypothesis for every transaction of a block that `CheckBlock` accepted.
-/
@[theorem_tag property]
theorem checkTxInputs_ne_feeOutOfRange (spendHeight : Nat) (coins : List Coin) (valueOut : Int)
    (hvalue : 0 ≤ valueOut) : checkTxInputs spendHeight coins valueOut ≠ .error .feeOutOfRange := by
  unfold checkTxInputs
  split
  · rename_i e he
    intro h
    cases h
    rcases checkInputValues_error he with h | h | h <;> cases h
  · rename_i total htotal
    have hrange := checkInputValues_ok_range (by omega) (by simp [maxMoney]) htotal
    split
    · simp
    · split
      · simp
      · split
        · rename_i hfee
          simp [moneyRange] at hfee
          omega
        · simp

/-- The loop over the inputs never leaves the `int64_t` range when it starts in `MoneyRange` and every coin has an amount in `MoneyRange`. -/
theorem checkInputValues_ne_outOfDomain {spendHeight : Nat} : ∀ {coins : List Coin} {acc : Int},
    (∀ c ∈ coins, 0 ≤ c.value ∧ c.value ≤ maxMoney) → 0 ≤ acc → acc ≤ maxMoney →
      checkInputValues spendHeight acc coins ≠ .error .outOfDomain
  | [], _, _, _, _ => by simp [checkInputValues]
  | c :: rest, acc, hcoins, h0, h1 => by
    have hc := hcoins c (by simp)
    unfold checkInputValues
    split
    · simp
    · split
      · rename_i hdomain
        simp [inInt64Range, maxMoney] at hdomain hc h1
        omega
      · split
        · simp
        · rename_i hrange
          simp [moneyRange] at hrange
          exact checkInputValues_ne_outOfDomain (fun c hmem => hcoins c (by simp [hmem])) (by omega) (by omega)

/-- `checkTxInputs` never returns `outOfDomain` when every coin has an amount in `MoneyRange`. -/
theorem checkTxInputs_ne_outOfDomain (spendHeight : Nat) (coins : List Coin) (valueOut : Int)
    (hcoins : ∀ c ∈ coins, 0 ≤ c.value ∧ c.value ≤ maxMoney) :
    checkTxInputs spendHeight coins valueOut ≠ .error .outOfDomain := by
  unfold checkTxInputs
  split
  · rename_i e he
    intro h
    cases h
    exact checkInputValues_ne_outOfDomain hcoins (by omega) (by simp [maxMoney]) he
  · split
    · simp
    · split
      · simp
      · split <;> simp

/-! ## The arithmetic domain of `connectBlock` -/

/-- Every output that the coin set holds has an amount from 0 to `MAX_MONEY`. -/
def CoinSet.ValuesInRange (s : CoinSet) : Prop :=
  ∀ (key : Nat) (entry : TxCoins) (out : TxOut), s.entries[key]? = some entry → some out ∈ entry.outputs →
    0 ≤ out.amount.toInt ∧ out.amount.toInt ≤ maxMoney

/-- The amounts of the coins that the inputs name in the set `s`. An input without a coin counts 0. -/
def inputValue (s : CoinSet) : List TxIn → Int
  | [] => 0
  | input :: rest =>
    (match s.coin input.prevout with
      | some c => c.value
      | none => 0) + inputValue s rest

/-- The change of `UpdateCoins` for one transaction at `height`, with no check: the coins of its inputs leave the set, unless it is a coinbase, and its outputs enter. -/
def applyTransaction (s : CoinSet) (height : Nat) (tx : Transaction) : CoinSet :=
  (if tx.isCoinBase then s else spendInputs s tx.inputs.val).addTx tx height

/--
The amounts of the coins that all input occurrences of the transactions spend, from the set `s`.
Each transaction that is not a coinbase is valued against the set just before it, so a coin that an earlier transaction of the list created counts.
The sum is defined whether or not `connectBlock` accepts the transactions.
-/
def spentValue (s : CoinSet) (height : Nat) : List Transaction → Int
  | [] => 0
  | tx :: rest =>
    (if tx.isCoinBase then 0 else inputValue s tx.inputs.val) +
      spentValue (applyTransaction s height tx) height rest

/-- The subsidy that `connectBlock` adds, or 0 when the subsidy has no value. -/
def subsidyValue (height : Nat) (prevHash : Hash256) : Nat :=
  match getDogecoinBlockSubsidy subsidyFuel height prevHash with
  | .ok subsidy => subsidy
  | .error _ => 0

/-- A coin of a set with amounts in range has an amount in range. -/
theorem CoinSet.coin_range {s : CoinSet} (hs : s.ValuesInRange) {o : OutPoint} {c : Coin}
    (h : s.coin o = some c) : 0 ≤ c.value ∧ c.value ≤ maxMoney := by
  unfold CoinSet.coin CoinSet.accessCoins at h
  split at h
  · cases h
  · rename_i entry hentry
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨out, hout, rfl⟩ := h
    have hmem : some out ∈ entry.outputs := by
      unfold TxCoins.available at hout
      rw [Option.join_eq_some_iff] at hout
      exact List.mem_of_getElem? hout
    exact hs _ entry out hentry hmem

/-- A spend keeps the amounts in range. -/
theorem CoinSet.spend_range {s : CoinSet} (hs : s.ValuesInRange) (o : OutPoint) :
    (s.spend o).ValuesInRange := by
  unfold CoinSet.spend CoinSet.accessCoins
  split
  · exact hs
  · rename_i entry hentry
    intro key e out hkey hmem
    by_cases hp : (entry.spend o.n.toNat).isPruned
    · simp only [hp, ↓reduceIte, Std.TreeMap.getElem?_erase] at hkey
      split at hkey
      · cases hkey
      · exact hs key e out hkey hmem
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getElem?_insert] at hkey
      split at hkey
      · cases hkey
        rcases List.mem_or_eq_of_mem_set hmem with h | h
        · exact hs _ entry out hentry h
        · cases h
      · exact hs key e out hkey hmem

/-- The spends of a list of inputs keep the amounts in range. -/
theorem spendInputs_range : ∀ {inputs : List TxIn} {s : CoinSet}, s.ValuesInRange →
    (spendInputs s inputs).ValuesInRange
  | [], _, hs => hs
  | input :: rest, _, hs => spendInputs_range (inputs := rest) (CoinSet.spend_range hs input.prevout)

/-- A new entry keeps the amounts in range when the transaction's outputs are in range. -/
theorem CoinSet.addTx_range {s : CoinSet} (hs : s.ValuesInRange) (tx : Transaction) (height : Nat)
    (htx : ∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) :
    (s.addTx tx height).ValuesInRange := by
  unfold CoinSet.addTx
  intro key e out hkey hmem
  by_cases hp : (TxCoins.ofTx tx height).isPruned
  · simp only [hp, ↓reduceIte, Std.TreeMap.getElem?_erase] at hkey
    split at hkey
    · cases hkey
    · exact hs key e out hkey hmem
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getElem?_insert] at hkey
    split at hkey
    · cases hkey
      simp only [TxCoins.ofTx, List.mem_map] at hmem
      obtain ⟨o, ho, heq⟩ := hmem
      split at heq
      · cases heq
      · cases heq
        exact htx _ ho
    · exact hs key e out hkey hmem

/-- The unchecked change of one transaction keeps the amounts in range. -/
theorem applyTransaction_range {s : CoinSet} (hs : s.ValuesInRange) (height : Nat) (tx : Transaction)
    (htx : ∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) :
    (applyTransaction s height tx).ValuesInRange := by
  unfold applyTransaction
  split
  · exact CoinSet.addTx_range hs tx height htx
  · exact CoinSet.addTx_range (spendInputs_range hs) tx height htx

/-- The amounts that the inputs name in a set with amounts in range are not negative. -/
theorem inputValue_nonneg {s : CoinSet} (hs : s.ValuesInRange) : ∀ (inputs : List TxIn), 0 ≤ inputValue s inputs
  | [] => by simp [inputValue]
  | input :: rest => by
    have ih := inputValue_nonneg hs rest
    unfold inputValue
    split
    · rename_i c hc
      have := (CoinSet.coin_range hs hc).1
      omega
    · omega

/-- The amounts that a list of transactions spends are not negative, from a set with amounts in range and for outputs in range. -/
theorem spentValue_nonneg (height : Nat) : ∀ {txs : List Transaction} {s : CoinSet}, s.ValuesInRange →
    (∀ tx ∈ txs, ∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) →
      0 ≤ spentValue s height txs
  | [], _, _, _ => by simp [spentValue]
  | tx :: rest, s, hs, htxs => by
    have ih := spentValue_nonneg height (txs := rest)
      (applyTransaction_range hs height tx (htxs tx (by simp))) (fun t ht => htxs t (by simp [ht]))
    have := inputValue_nonneg hs tx.inputs.val
    unfold spentValue
    split <;> omega

/-- The coins that `lookupInputs` finds are coins of the set, and their amounts add up to `inputValue`. -/
theorem lookupInputs_some {s : CoinSet} : ∀ {inputs : List TxIn} {coins : List Coin},
    lookupInputs s inputs = some coins →
      (∀ c ∈ coins, ∃ o, s.coin o = some c) ∧ (coins.map Coin.value).sum = inputValue s inputs
  | [], coins, h => by
    simp only [lookupInputs, Option.some.injEq] at h
    subst h
    simp [inputValue]
  | input :: rest, coins, h => by
    unfold lookupInputs at h
    split at h
    · cases h
    · rename_i c hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, rfl⟩ := h
      obtain ⟨hmem, hsum⟩ := lookupInputs_some htail
      refine ⟨?_, ?_⟩
      · intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨_, hc⟩
        · exact hmem c' hc'
      · simp [inputValue, hc, hsum]

/-- A sum of amounts that are not negative is not negative. -/
theorem sum_values_nonneg : ∀ {coins : List Coin}, (∀ c ∈ coins, 0 ≤ c.value) → 0 ≤ (coins.map Coin.value).sum
  | [], _ => by simp
  | c :: rest, h => by
    have := h c (by simp)
    have := sum_values_nonneg (coins := rest) (fun c hc => h c (by simp [hc]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- `getValueIn` has a value when the amounts are not negative and the whole sum is in the `int64_t` range. -/
theorem getValueIn_some : ∀ {coins : List Coin} {acc : Int}, (∀ c ∈ coins, 0 ≤ c.value) →
    -9223372036854775808 ≤ acc → acc + (coins.map Coin.value).sum ≤ 9223372036854775807 →
      getValueIn acc coins = some (acc + (coins.map Coin.value).sum)
  | [], acc, _, _, _ => by simp [getValueIn]
  | c :: rest, acc, hpos, hlo, hhi => by
    have hc := hpos c (by simp)
    have hrest := sum_values_nonneg (coins := rest) (fun c h => hpos c (by simp [h]))
    simp only [List.map_cons, List.sum_cons] at hhi ⊢
    unfold getValueIn
    have hin : inInt64Range (acc + c.value) = true := by
      simp only [inInt64Range, Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp only [hin, ↓reduceIte]
    rw [getValueIn_some (fun c h => hpos c (by simp [h])) (by omega) (by omega)]
    congr 1
    omega

/-- When `checkOutputs` accepts from a sum in `MoneyRange`, every amount is in `MoneyRange`, and so is the final sum. -/
theorem checkOutputs_ok_range : ∀ {outs : List TxOut} {acc : Int}, 0 ≤ acc → acc ≤ maxMoney →
    checkOutputs acc outs = .ok () →
      (∀ o ∈ outs, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) ∧
        0 ≤ (outs.map fun o => o.amount.toInt).sum ∧ acc + (outs.map fun o => o.amount.toInt).sum ≤ maxMoney
  | [], acc, h0, h1, _ => by simp; omega
  | o :: rest, acc, h0, h1, h => by
    unfold checkOutputs at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · obtain ⟨hmem, hsum0, hsum1⟩ := checkOutputs_ok_range (outs := rest) (by omega) (by omega) h
          refine ⟨?_, ?_, ?_⟩
          · intro o' ho'
            simp only [List.mem_cons] at ho'
            rcases ho' with rfl | ho'
            · omega
            · exact hmem o' ho'
          · simp only [List.map_cons, List.sum_cons]
            omega
          · simp only [List.map_cons, List.sum_cons]
            omega

/-- A transaction that `checkTransaction` accepts has every output amount in `MoneyRange`, and an output total in `MoneyRange`. -/
theorem checkTransaction_ok_range {tx : Transaction} {duplicates : Bool}
    (h : checkTransaction tx duplicates = .ok ()) :
    (∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) ∧
      0 ≤ tx.valueOut ∧ tx.valueOut ≤ maxMoney := by
  have hout : checkOutputs 0 tx.outputs.val = .ok () := by
    unfold checkTransaction at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · assumption
  obtain ⟨hmem, h0, h1⟩ := checkOutputs_ok_range (by omega) (by simp [maxMoney]) hout
  exact ⟨hmem, h0, by simpa [Transaction.valueOut] using h1⟩

/-- When the loop of `CheckBlock` accepts a list, `checkTransaction` accepts each member. -/
theorem checkTransactions_ok : ∀ {txs : List Transaction} {index : Nat}, checkTransactions index txs = .ok () →
    ∀ tx ∈ txs, checkTransaction tx true = .ok ()
  | [], _, _ => by simp
  | t :: rest, index, h => by
    unfold checkTransactions at h
    split at h
    · cases h
    · rename_i ht
      intro tx htx
      simp only [List.mem_cons] at htx
      rcases htx with rfl | htx
      · exact ht
      · exact checkTransactions_ok h tx htx

/-- A block that `checkBlock` accepts has transactions that `checkTransaction` accepts. -/
theorem checkBlock_ok_transactions {network : Work.WorkNetwork} {fCheckPOW fCheckMerkleRoot : Bool} {b : Block}
    (h : checkBlock network fCheckPOW fCheckMerkleRoot b = .ok ()) :
    ∀ tx ∈ b.transactions, checkTransaction tx true = .ok () := by
  have hloop : checkTransactions 0 b.transactions = .ok () := by
    unfold checkBlock at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · assumption
  exact checkTransactions_ok hloop

/-- The script check of one input never returns `outOfDomain`. -/
theorem checkInputScript_ne_outOfDomain (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (input : Nat) (coin : Coin) :
    checkInputScript verify flags txIndex tx input coin ≠ .error .outOfDomain := by
  unfold checkInputScript
  repeat' split
  all_goals simp

/-- The script loop never returns `outOfDomain`. -/
theorem checkInputScripts_ne_outOfDomain (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) : ∀ (coins : List Coin) (input : Nat),
    checkInputScripts verify flags txIndex tx input coins ≠ .error .outOfDomain
  | [], _ => by simp [checkInputScripts]
  | coin :: rest, input => by
    unfold checkInputScripts
    split
    · rename_i e he
      intro h
      cases h
      exact checkInputScript_ne_outOfDomain verify flags txIndex tx input coin he
    · exact checkInputScripts_ne_outOfDomain verify flags txIndex tx rest (input + 1)

/-- `checkInputs` never returns `outOfDomain` when every coin has an amount in `MoneyRange`. -/
theorem checkInputs_ne_outOfDomain (verify : SignatureVerifier) (height : Nat) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (coins : List Coin) (hcoins : ∀ c ∈ coins, 0 ≤ c.value ∧ c.value ≤ maxMoney) :
    checkInputs verify height flags txIndex tx coins ≠ .error .outOfDomain := by
  unfold checkInputs
  split
  · rename_i he
    exact absurd he (checkTxInputs_ne_outOfDomain height coins tx.valueOut hcoins)
  · rename_i e hne he
    intro h
    cases h
  · exact checkInputScripts_ne_outOfDomain verify flags txIndex tx coins 0

/-- When `checkInputs` accepts, the coins are worth at least the outputs. -/
theorem checkInputs_ok_value {verify : SignatureVerifier} {height : Nat} {flags : UInt32} {txIndex : Nat}
    {tx : Transaction} {coins : List Coin} (h : checkInputs verify height flags txIndex tx coins = .ok ()) :
    tx.valueOut ≤ (coins.map Coin.value).sum := by
  unfold checkInputs at h
  split at h
  · cases h
  · cases h
  · rename_i hok
    unfold checkTxInputs at hok
    split at hok
    · cases hok
    · rename_i total htotal
      have := checkInputValues_ok_sum htotal
      split at hok
      · cases hok
      · omega

/--
One pass of the transaction loop inside the `int64_t` range.
When the set has amounts in range, the transaction passed `checkTransaction`, `nFees` is not negative, and `nFees` plus the coins of the transaction is in the `int64_t` range, the pass does not return `outOfDomain`.
When it accepts, the new set is `applyTransaction`, and the new `nFees` is not negative and at most the old one plus the coins of the transaction.
-/
theorem connectTransaction_fits (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) (index : Nat)
    {st : ConnectState} {tx : Transaction} (hs : st.coins.ValuesInRange)
    (htx : (∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt ∧ o.amount.toInt ≤ maxMoney) ∧
      0 ≤ tx.valueOut ∧ tx.valueOut ≤ maxMoney)
    (hfees : 0 ≤ st.fees)
    (hbound : st.fees + (if tx.isCoinBase then 0 else inputValue st.coins tx.inputs.val) ≤ 9223372036854775807) :
    connectTransaction verify ctx flags index st tx ≠ .error .outOfDomain ∧
      ∀ st', connectTransaction verify ctx flags index st tx = .ok st' →
        st'.coins = applyTransaction st.coins ctx.height tx ∧ 0 ≤ st'.fees ∧
          st'.fees ≤ st.fees + (if tx.isCoinBase then 0 else inputValue st.coins tx.inputs.val) := by
  by_cases hcb : tx.isCoinBase
  · simp only [connectTransaction, hcb, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    split
    · exact ⟨by simp, by simp⟩
    · refine ⟨by simp, ?_⟩
      intro st' h
      cases h
      simp [applyTransaction, hcb, hfees]
  · simp only [hcb, Bool.false_eq_true, ↓reduceIte] at hbound
    simp only [connectTransaction, hcb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
    cases hl : lookupInputs st.coins tx.inputs.val with
    | none => exact ⟨by simp, by simp⟩
    | some coins =>
      obtain ⟨hmem, hsum⟩ := lookupInputs_some hl
      have hrange : ∀ c ∈ coins, 0 ≤ c.value ∧ c.value ≤ maxMoney := fun c hc => by
        obtain ⟨o, ho⟩ := hmem c hc
        exact CoinSet.coin_range hs ho
      rw [← hsum] at hbound
      have hnonneg := sum_values_nonneg (coins := coins) (fun c hc => (hrange c hc).1)
      have hvalue : getValueIn 0 coins = some ((coins.map Coin.value).sum) := by
        have := getValueIn_some (coins := coins) (acc := 0) (fun c hc => (hrange c hc).1) (by omega) (by omega)
        simpa using this
      have hmax : maxMoney = 1000000000000000000 := rfl
      have hfee : addFee st.fees coins tx.valueOut =
          some (st.fees + ((coins.map Coin.value).sum - tx.valueOut)) := by
        have h1 : inInt64Range ((coins.map Coin.value).sum - tx.valueOut) = true := by
          simp only [inInt64Range, Bool.and_eq_true, decide_eq_true_eq]
          omega
        have h2 : inInt64Range (st.fees + ((coins.map Coin.value).sum - tx.valueOut)) = true := by
          simp only [inInt64Range, Bool.and_eq_true, decide_eq_true_eq]
          omega
        simp [addFee, hvalue, h1, h2]
      simp only [hfee]
      split
      · exact ⟨by simp, by simp⟩
      · split
        · rename_i e he
          refine ⟨?_, by simp⟩
          intro h
          cases h
          exact checkInputs_ne_outOfDomain verify ctx.height flags index tx coins hrange he
        · rename_i hok
          have hv := checkInputs_ok_value hok
          split
          · exact ⟨by simp, by simp⟩
          · refine ⟨by simp, ?_⟩
            intro st' h
            cases h
            refine ⟨by simp [applyTransaction, hcb], ?_, ?_⟩ <;> simp only <;> omega

/--
The transaction loop inside the `int64_t` range.
When the set has amounts in range, every transaction passed `checkTransaction`, `nFees` is not negative, and `nFees` plus the coins that the transactions spend is in the `int64_t` range, the loop does not return `outOfDomain`.
When it accepts, the final `nFees` is not negative and at most the first one plus those coins.
-/
theorem connectTransactions_fits (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) :
    ∀ {txs : List Transaction} {index : Nat} {st : ConnectState}, st.coins.ValuesInRange →
      (∀ tx ∈ txs, checkTransaction tx true = .ok ()) → 0 ≤ st.fees →
      st.fees + spentValue st.coins ctx.height txs ≤ 9223372036854775807 →
        connectTransactions verify ctx flags index st txs ≠ .error .outOfDomain ∧
          ∀ st', connectTransactions verify ctx flags index st txs = .ok st' →
            0 ≤ st'.fees ∧ st'.fees ≤ st.fees + spentValue st.coins ctx.height txs
  | [], _, st, _, _, hfees, _ => by
    refine ⟨by simp [connectTransactions], ?_⟩
    intro st' h
    simp only [connectTransactions, Except.ok.injEq] at h
    subst h
    simp [spentValue, hfees]
  | tx :: rest, index, st, hs, htxs, hfees, hbound => by
    have htx := checkTransaction_ok_range (htxs tx (by simp))
    have hrest := spentValue_nonneg ctx.height (txs := rest) (applyTransaction_range hs ctx.height tx htx.1)
      (fun t ht => (checkTransaction_ok_range (htxs t (by simp [ht]))).1)
    unfold spentValue at hbound
    obtain ⟨hne, hok⟩ := connectTransaction_fits verify ctx flags index hs htx hfees (by omega)
    unfold connectTransactions
    split
    · rename_i e he
      refine ⟨?_, by simp⟩
      intro h
      cases h
      exact hne he
    · rename_i st1 h1
      obtain ⟨hcoins, hf0, hf1⟩ := hok st1 h1
      have ih := connectTransactions_fits verify ctx flags (txs := rest) (index := index + 1) (st := st1)
        (hcoins ▸ applyTransaction_range hs ctx.height tx htx.1) (fun t ht => htxs t (by simp [ht])) hf0
        (by rw [hcoins]; omega)
      refine ⟨ih.1, fun st' h => ?_⟩
      obtain ⟨h0, h1'⟩ := ih.2 st' h
      rw [hcoins] at h1'
      unfold spentValue
      exact ⟨h0, by omega⟩

/--
`connectBlock` never returns `outOfDomain` under the two hypotheses of design record 0010, section 3.

1. Every output that the coin set holds has an amount from 0 to `MAX_MONEY` (`CoinSet.ValuesInRange`).
2. The amounts of the coins that all input occurrences of the block spend (`spentValue`), plus `MAX_MONEY` and the subsidy, are below `2^63`.

`spentValue` values each transaction against the set just before it, so it counts a coin that an earlier transaction of the block created.
It is defined for every block, so the bound also covers a block that `connectBlock` rejects.
`subsidyValue` is the subsidy, or 0 when the subsidy has no value. In that case `connectBlock` returns `subsidy`, not `outOfDomain`.

The theorem holds for every verifier, both values of `fJustCheck` and every context.
Its sums are those where Core adds `int64_t` values with no earlier range check: `GetValueIn`, the fee added to `nFees`, the subsidy added to `nFees`, and the sum of `CheckTxInputs`.
-/
@[theorem_tag property]
theorem connect_fits (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext) (s : CoinSet)
    (b : Block) (hcoins : s.ValuesInRange)
    (hsum : spentValue s ctx.height b.transactions + maxMoney + (subsidyValue ctx.height ctx.prevHash : Int) <
      2 ^ 63) :
    connectBlock verify fJustCheck ctx s b ≠ .error .outOfDomain := by
  have hmax : maxMoney = 1000000000000000000 := rfl
  have hpow : (2 : Int) ^ 63 = 9223372036854775808 := by decide
  rw [hpow, hmax] at hsum
  unfold connectBlock
  split
  · simp
  · rename_i hcheck
    have htxs := checkBlock_ok_transactions hcheck
    split
    · simp
    · simp only
      split
      · simp
      · split
        · simp
        · have hloop := connectTransactions_fits verify ctx (connectScriptFlags ctx.height)
            (txs := b.transactions) (index := 0) (st := ⟨s, 0, 0, []⟩) hcoins htxs (by simp)
            (by simp only [Int.zero_add]; omega)
          split
          · rename_i e he
            intro h
            cases h
            exact hloop.1 he
          · rename_i st hst
            obtain ⟨h0, h1⟩ := hloop.2 st hst
            simp only [Int.zero_add] at h1
            split
            · simp
            · rename_i subsidy hsub
              have hvalue : subsidyValue ctx.height ctx.prevHash = subsidy := by simp [subsidyValue, hsub]
              rw [hvalue] at hsum
              split
              · rename_i hdomain
                simp only [inInt64Range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hdomain
                omega
              · repeat' split
                all_goals simp

/-! ## The fee reasons inside `connectBlock` -/

/-- The script check of one input returns no `txInputs` error. -/
theorem checkInputScript_ne_txInputs (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (input : Nat) (coin : Coin) (index : Nat) (e : CheckTxInputsError) :
    checkInputScript verify flags txIndex tx input coin ≠ .error (.txInputs index e) := by
  unfold checkInputScript
  repeat' split
  all_goals simp

/-- The script loop returns no `txInputs` error. -/
theorem checkInputScripts_ne_txInputs (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (index : Nat) (e : CheckTxInputsError) : ∀ (coins : List Coin) (input : Nat),
    checkInputScripts verify flags txIndex tx input coins ≠ .error (.txInputs index e)
  | [], _ => by simp [checkInputScripts]
  | coin :: rest, input => by
    unfold checkInputScripts
    split
    · rename_i e' he
      intro h
      cases h
      exact checkInputScript_ne_txInputs verify flags txIndex tx input coin index e he
    · exact checkInputScripts_ne_txInputs verify flags txIndex tx index e rest (input + 1)

/-- A `txInputs` error of `checkInputs` is the error of `checkTxInputs` on the same coins. -/
theorem checkInputs_txInputs {verify : SignatureVerifier} {height : Nat} {flags : UInt32} {txIndex index : Nat}
    {tx : Transaction} {coins : List Coin} {e : CheckTxInputsError}
    (h : checkInputs verify height flags txIndex tx coins = .error (.txInputs index e)) :
    checkTxInputs height coins tx.valueOut = .error e := by
  unfold checkInputs at h
  split at h
  · cases h
  · rename_i e' _ he
    cases h
    exact he
  · exact absurd h (checkInputScripts_ne_txInputs verify flags txIndex tx index e coins 0)

/-- A `txInputs` error of one pass of the transaction loop is the error of `checkTxInputs` on some coins. -/
theorem connectTransaction_txInputs {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32}
    {index j : Nat} {st : ConnectState} {tx : Transaction} {e : CheckTxInputsError}
    (h : connectTransaction verify ctx flags index st tx = .error (.txInputs j e)) :
    ∃ coins, checkTxInputs ctx.height coins tx.valueOut = .error e := by
  unfold connectTransaction at h
  split at h
  · cases h
  · rename_i coins _
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i e' he
          cases h
          split at he
          · cases he
          · exact ⟨coins, checkInputs_txInputs he⟩
        · revert h
          repeat' split
          all_goals (intro h; cases h)

/-- A `txInputs` error of the transaction loop is the error of `checkTxInputs` for a transaction of the list. -/
theorem connectTransactions_txInputs {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32}
    {j : Nat} {e : CheckTxInputsError} : ∀ {txs : List Transaction} {index : Nat} {st : ConnectState},
    connectTransactions verify ctx flags index st txs = .error (.txInputs j e) →
      ∃ tx ∈ txs, ∃ coins, checkTxInputs ctx.height coins tx.valueOut = .error e
  | [], _, _, h => by simp [connectTransactions] at h
  | tx :: rest, index, st, h => by
    unfold connectTransactions at h
    split at h
    · rename_i e' he
      cases h
      exact ⟨tx, by simp, connectTransaction_txInputs he⟩
    · obtain ⟨t, ht, hcoins⟩ := connectTransactions_txInputs h
      exact ⟨t, by simp [ht], hcoins⟩

/-- A `txInputs` error of `connectBlock` is the error of `checkTxInputs` for a transaction that `checkTransaction` accepted. -/
theorem connectBlock_txInputs {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext}
    {s : CoinSet} {b : Block} {j : Nat} {e : CheckTxInputsError}
    (h : connectBlock verify fJustCheck ctx s b = .error (.txInputs j e)) :
    ∃ tx, checkTransaction tx true = .ok () ∧ ∃ coins, checkTxInputs ctx.height coins tx.valueOut = .error e := by
  unfold connectBlock at h
  split at h
  · cases h
  · rename_i hcheck
    have htxs := checkBlock_ok_transactions hcheck
    split at h
    · cases h
    · simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · rename_i e' he
            cases h
            obtain ⟨tx, htx, hcoins⟩ := connectTransactions_txInputs he
            exact ⟨tx, htxs tx htx, hcoins⟩
          · split at h
            · cases h
            · split at h
              · cases h
              · revert h
                repeat' split
                all_goals (intro h; cases h)

/--
`connectBlock` never rejects a block with `bad-txns-fee-negative`.
The theorem holds for every verifier, flag, context, coin set and block.
-/
@[theorem_tag property]
theorem connectBlock_ne_feeNegative (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) (index : Nat) :
    connectBlock verify fJustCheck ctx s b ≠ .error (.txInputs index .feeNegative) := by
  intro h
  obtain ⟨tx, _, coins, hcoins⟩ := connectBlock_txInputs h
  exact checkTxInputs_ne_feeNegative ctx.height coins tx.valueOut hcoins

/--
`connectBlock` never rejects a block with `bad-txns-fee-outofrange`.
`connectBlock` runs `checkBlock` first, so every transaction that reaches `checkTxInputs` has an output total that is not negative.
The theorem holds for every verifier, flag, context, coin set and block.
-/
@[theorem_tag property]
theorem connectBlock_ne_feeOutOfRange (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) (index : Nat) :
    connectBlock verify fJustCheck ctx s b ≠ .error (.txInputs index .feeOutOfRange) := by
  intro h
  obtain ⟨tx, htx, coins, hcoins⟩ := connectBlock_txInputs h
  exact checkTxInputs_ne_feeOutOfRange ctx.height coins tx.valueOut (checkTransaction_ok_range htx).2.1 hcoins

end DogeLib.Block
