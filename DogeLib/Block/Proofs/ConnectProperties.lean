module

public import DogeLib.Block.Proofs.Connect
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of block connection

The three properties of design record 0010, section 6, for `connectBlock`:

- `connect_spends_available`: in an accepted block, each input of a transaction that is not a coinbase has a coin in the set just before its transaction. The spends of the transaction remove that coin, and no transaction names one outpoint twice.
- `connect_value_bound`: an accepted block adds at most its subsidy to the total value of a coin set with amounts in range.
- `chain_issuance_bound`: take a chain from the mainnet genesis block that `connectBlock` accepts block by block from the empty set. Its total value is at most the sum of the subsidies.

`connect_valuesInRange` is the invariant of the last two: an accepted block keeps every amount of the set from 0 to `MAX_MONEY`.
`connectChain_issuance_bound` is the chain bound for any supplied contexts.

## The hypotheses

Design record 0010 states the targets for a coin set with amounts in range, a successful subsidy and the arithmetic domain of its section 3.
The theorems take acceptance, `connectBlock … = .ok r`, as their hypothesis.
`connectBlock_ok` derives the last two conditions from acceptance, for a block without the genesis hash.
The subsidy has a value, and the result is not `outOfDomain`, so each sum that the run tested was in the `int64_t` range.
Acceptance does not give the sufficient bound of `connect_fits`.
So only `CoinSet.ValuesInRange` stays as a separate hypothesis, and only the value bounds need it.

`connect_spends_available` excludes a block with the hash of the mainnet genesis block.
`connectBlock` accepts such a block after `checkBlock` and before the transaction loop, as Core does (D114, lines 1821 to 1825).
`connectBlock_genesis` states that result.

## What the theorems do not say

The theorems are about the Lean definitions.
They do not show that Core's compiled code has these properties.
The comparison of `block.validate` with Core, and the source review, connect the definitions to Core (SOUNDNESS.md).

The value bounds are upper bounds.
No theorem here says that a coin of the set can be spent, or that the total equals an amount.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script

/-! ## Definitions -/

/-- The value of an entry: the sum of the amounts of its outputs that are not null, as an integer. -/
def TxCoins.value (c : TxCoins) : Int := ((c.outputs.filterMap id).map fun o => o.amount.toInt).sum

/-- The value of an optional entry: `TxCoins.value` of the entry, or 0 without an entry. -/
def entryValue : Option TxCoins → Int
  | none => 0
  | some c => c.value

/--
The coin set just before the transaction at `index`: the set `s` after the unchecked changes (`applyTransaction`) of the transactions before that index.
A coin that an earlier transaction of the list created is in this set, unless a transaction between them spent it.
-/
def coinsBefore (s : CoinSet) (height : Nat) (txs : List Transaction) (index : Nat) : CoinSet :=
  (txs.take index).foldl (fun s tx => applyTransaction s height tx) s

/-- The sum of the output totals of the coinbase transactions of a list. -/
def coinbaseValueOut (txs : List Transaction) : Int :=
  ((txs.filter Transaction.isCoinBase).map Transaction.valueOut).sum

/--
`connectBlock` on a list of blocks in order, each with its own context, from the coin set `s`.
The result is the set after the last block, or the first failure.
The set after each block is the set before the next one.
-/
def connectChain (verify : SignatureVerifier) (fJustCheck : Bool) (s : CoinSet) :
    List (ConnectContext × Block) → Except ConnectBlockError CoinSet
  | [] => .ok s
  | (ctx, b) :: rest =>
    match connectBlock verify fJustCheck ctx s b with
    | .error e => .error e
    | .ok r => connectChain verify fJustCheck r.coins rest

/--
The contexts of a list of blocks are those of a chain after the block `prev`.
The first block has the height `height`, and each next block has the next height.
The previous hash of each context is the hash of the block before it.
-/
def ChainLinked (prev : Block) (height : Nat) : List (ConnectContext × Block) → Prop
  | [] => True
  | (ctx, b) :: rest =>
    ctx.height = height ∧ ctx.prevHash = prev.header.pure.getHash ∧ ChainLinked b (height + 1) rest

/--
The sum of the subsidies of a list of blocks that follow the block `prev`, with the first block at `height`.
Each subsidy is `subsidyValue` of the block's height and the hash of the block before it.
-/
def chainSubsidy (prev : Block) (height : Nat) : List Block → Int
  | [] => 0
  | b :: rest => (subsidyValue height prev.header.pure.getHash : Int) + chainSubsidy b (height + 1) rest

/-! ## The coin set as a map
This section is the only part of the module that reads `CoinSet.entries`.
It has the definition of `CoinSet.totalValue` and the lemmas that depend on the map.
The later sections use the set through seven of its statements:
`CoinSet.totalValue_empty`, `CoinSet.empty_valuesInRange`, `CoinSet.entryValue_nonneg`, `CoinSet.totalValue_spend`, `CoinSet.totalValue_addTx`, `CoinSet.coin_spend_self` and `CoinSet.coin_spend_of_ne`.
A change of the representation of `CoinSet` needs new proofs of these statements, and of no later theorem.
-/

/--
The total value of a coin set: the sum of `TxCoins.value` over its entries, in the integers.

It counts every output that an entry of the set holds.
So it counts each coin that `CoinSet.coin` returns once.
It also counts an output that `CoinSet.coin` cannot return.
Such an output is in an entry whose key is not `txidKey` of a transaction ID, or it has an index of `2^32` or more.
`CoinSet.addTx` stores each entry under `txidKey` of its transaction ID, and no theorem states that a set has only such entries.
The sum has no bound, because the supply of Dogecoin is above `2^63` koinu (design record 0010, section 3).
-/
def CoinSet.totalValue (s : CoinSet) : Int := s.entries.foldl (fun acc _ c => acc + c.value) 0

/-- A left fold that adds the entry values equals the start value plus the sum of the values. -/
private theorem foldl_add_value : ∀ (l : List (Nat × TxCoins)) (acc : Int),
    l.foldl (fun a b => a + b.2.value) acc = acc + (l.map fun p => p.2.value).sum
  | [], acc => by simp
  | p :: rest, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_value rest]; omega

/-- The total value is the sum of the entry values over the list of the entries. -/
theorem CoinSet.totalValue_eq (s : CoinSet) :
    s.totalValue = (s.entries.toList.map fun p => p.2.value).sum := by
  unfold CoinSet.totalValue
  rw [Std.TreeMap.foldl_eq_foldl_toList, foldl_add_value]; omega

/-- A filter that removes one key changes nothing when no member has that key. -/
private theorem sum_filter_ne_of_forall : ∀ (l : List (Nat × TxCoins)) (k : Nat), (∀ p ∈ l, p.1 ≠ k) →
    l.filter (fun p => p.1 != k) = l
  | l, k, h => by
    rw [List.filter_eq_self]
    intro p hp
    simpa using h p hp

/-- In a list with pairwise different keys, the sum of the values is the value at one key plus the sum over the other keys. -/
private theorem sum_split_key : ∀ (l : List (Nat × TxCoins)) (k : Nat) (v : TxCoins),
    l.Pairwise (fun a b => a.1 ≠ b.1) → (k, v) ∈ l →
    (l.map fun p => p.2.value).sum = v.value + ((l.filter fun p => p.1 != k).map fun p => p.2.value).sum
  | [], _, _, _, h => by simp at h
  | p :: rest, k, v, hp, hmem => by
    rw [List.pairwise_cons] at hp
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · have : rest.filter (fun p => p.1 != k) = rest :=
        sum_filter_ne_of_forall rest k (fun q hq => fun h => hp.1 q hq h.symm)
      simp [this]
    · have hne : p.1 ≠ k := fun h => hp.1 (k, v) hmem h
      have ih := sum_split_key rest k v hp.2 hmem
      simp only [List.map_cons, List.sum_cons, List.filter_cons, bne_iff_ne, ne_eq, hne, not_false_eq_true,
        ↓reduceIte]
      omega

/-- Two integer lists with the same members, in any order, have the same sum. -/
private theorem perm_sum_eq {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => omega

/-- The entries of a map have pairwise different keys. -/
private theorem toList_pairwise (m : Std.TreeMap Nat TxCoins) : m.toList.Pairwise (fun a b => a.1 ≠ b.1) :=
  (Std.TreeMap.distinct_keys_toList (t := m)).imp fun h heq => h (Nat.compare_eq_eq.mpr heq)

/-- The list of the entries of a map has no member twice. -/
private theorem toList_nodup (m : Std.TreeMap Nat TxCoins) : m.toList.Nodup :=
  (toList_pairwise m).imp fun h heq => h (by rw [heq])

/-- The sum of the entry values of a map is the value at one key plus the sum over the other keys. -/
private theorem sum_eq_entryValue_add (m : Std.TreeMap Nat TxCoins) (k : Nat) :
    (m.toList.map fun p => p.2.value).sum =
      entryValue m[k]? + ((m.toList.filter fun p => p.1 != k).map fun p => p.2.value).sum := by
  cases h : m[k]? with
  | none =>
    rw [sum_filter_ne_of_forall]
    · simp [entryValue]
    · intro p hp heq
      have : m[p.1]? = some p.2 := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
      rw [heq, h] at this
      cases this
  | some v =>
    exact sum_split_key _ k v (toList_pairwise m) (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr h)

/--
Two maps that agree at every key except `k` have totals that differ by the difference of their values at `k`.
The lemmas for `CoinSet.spend` and `CoinSet.addTx` both follow from this statement.
-/
private theorem total_of_agree (m m' : Std.TreeMap Nat TxCoins) (k : Nat) (h : ∀ a, a ≠ k → m'[a]? = m[a]?) :
    (m'.toList.map fun p => p.2.value).sum - entryValue m'[k]? =
      (m.toList.map fun p => p.2.value).sum - entryValue m[k]? := by
  rw [sum_eq_entryValue_add m k, sum_eq_entryValue_add m' k]
  have hperm : (m'.toList.filter fun p => p.1 != k).Perm (m.toList.filter fun p => p.1 != k) := by
    rw [List.perm_ext_iff_of_nodup ((toList_nodup m').filter _) ((toList_nodup m).filter _)]
    intro p
    simp only [List.mem_filter, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨hp, hne⟩
      have := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
      rw [h _ hne] at this
      exact ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr this, hne⟩
    · rintro ⟨hp, hne⟩
      have := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
      rw [← h _ hne] at this
      exact ⟨Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr this, hne⟩
  have := perm_sum_eq (hperm.map fun p => p.2.value)
  omega

/-- The fold of `txidKey` gives equal results only for equal start values and equal byte lists, when the lists have one length. -/
private theorem txidKey_fold_inj : ∀ (l₁ l₂ : List UInt8) (a₁ a₂ : Nat), l₁.length = l₂.length →
    l₁.foldl (fun n b => n * 256 + b.toNat) a₁ = l₂.foldl (fun n b => n * 256 + b.toNat) a₂ →
      a₁ = a₂ ∧ l₁ = l₂
  | [], [], _, _, _, h => by simpa using h
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | b₁ :: r₁, b₂ :: r₂, a₁, a₂, hl, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨ha, hr⟩ := txidKey_fold_inj r₁ r₂ _ _ (by simpa using hl) h
    have h1 := b₁.toNat_lt
    have h2 := b₂.toNat_lt
    have : a₁ = a₂ ∧ b₁.toNat = b₂.toNat := by omega
    exact ⟨this.1, by rw [UInt8.toNat_inj.mp this.2, hr]⟩

/-- `txidKey` gives different keys to different transaction IDs. -/
theorem txidKey_inj {h₁ h₂ : Hash256} (h : txidKey h₁ = txidKey h₂) : h₁ = h₂ :=
  Subtype.ext (txidKey_fold_inj _ _ 0 0 (by rw [h₁.property, h₂.property]) h).2

/-- The empty set has the total value 0. -/
theorem CoinSet.totalValue_empty : CoinSet.empty.totalValue = 0 := by
  have : (CoinSet.empty.entries).toList = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro p hp
    have := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    simp [CoinSet.empty] at this
  rw [CoinSet.totalValue_eq, this]; rfl

/-- The empty set has amounts in range, because it has no output. -/
theorem CoinSet.empty_valuesInRange : CoinSet.empty.ValuesInRange := by
  intro key entry out h
  simp [CoinSet.empty] at h

/--
The entry of each key after `CoinSet.spend`.
At the key of the outpoint's transaction ID, the entry is the spent entry, or nothing when that entry is pruned or absent.
Every other key keeps its entry.
-/
theorem CoinSet.entries_spend (s : CoinSet) (o : OutPoint) (a : Nat) :
    (s.spend o).entries[a]? =
      if a = txidKey o.hash then
        (match s.entries[txidKey o.hash]? with
          | none => none
          | some c => if (c.spend o.n.toNat).isPruned then none else some (c.spend o.n.toNat))
      else s.entries[a]? := by
  unfold CoinSet.spend CoinSet.accessCoins
  split
  · rename_i h
    split
    · rename_i ha; rw [ha, h]
    · rfl
  · rename_i c h
    by_cases hp : (c.spend o.n.toNat).isPruned
    · simp only [hp, ↓reduceIte, Std.TreeMap.getElem?_erase, Nat.compare_eq_eq]
      by_cases ha : a = txidKey o.hash
      · simp [ha, h, hp]
      · simp [ha, Ne.symm ha]
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getElem?_insert, Nat.compare_eq_eq]
      by_cases ha : a = txidKey o.hash
      · simp [ha, h, hp]
      · simp [ha, Ne.symm ha]

/--
The entry of each key after `CoinSet.addTx`.
At the key of the transaction's ID, the entry is `TxCoins.ofTx`, or nothing when that entry is pruned.
Every other key keeps its entry.
-/
theorem CoinSet.entries_addTx (s : CoinSet) (tx : Transaction) (height : Nat) (a : Nat) :
    (s.addTx tx height).entries[a]? =
      if a = txidKey tx.txid then
        (if (TxCoins.ofTx tx height).isPruned then none else some (TxCoins.ofTx tx height))
      else s.entries[a]? := by
  unfold CoinSet.addTx
  have htx : (TxCoins.ofTx tx height).txid = tx.txid := rfl
  by_cases hp : (TxCoins.ofTx tx height).isPruned
  · simp only [hp, ↓reduceIte, Std.TreeMap.getElem?_erase, Nat.compare_eq_eq, htx]
    by_cases ha : a = txidKey tx.txid
    · simp [ha]
    · simp [ha, Ne.symm ha]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.getElem?_insert, Nat.compare_eq_eq, htx]
    by_cases ha : a = txidKey tx.txid
    · simp [ha]
    · simp [ha, Ne.symm ha]

/-- A list of outputs that are all null has the value 0. -/
private theorem outputs_value_nil_of_all_none : ∀ (l : List (Option TxOut)), l.all Option.isNone = true →
    ((l.filterMap id).map fun o => o.amount.toInt).sum = 0
  | [], _ => rfl
  | none :: rest, h => by
    simp only [List.all_cons, Option.isNone_none, Bool.true_and] at h
    simpa using outputs_value_nil_of_all_none rest h
  | some _ :: _, h => by simp at h

/-- A pruned entry has the value 0. -/
theorem TxCoins.value_of_isPruned {c : TxCoins} (h : c.isPruned = true) : c.value = 0 :=
  outputs_value_nil_of_all_none c.outputs h

/-- When the output at an index becomes null, the value of the list drops by the amount of that output, if it was not null. -/
private theorem outputs_value_set : ∀ (l : List (Option TxOut)) (n : Nat),
    (((l.set n none).filterMap id).map fun o => o.amount.toInt).sum =
      ((l.filterMap id).map fun o => o.amount.toInt).sum -
        (match (l[n]?).join with | some out => out.amount.toInt | none => 0)
  | [], _ => by simp
  | x :: rest, 0 => by cases x <;> simp <;> omega
  | x :: rest, n + 1 => by
    have ih := outputs_value_set rest n
    cases x <;> simp only [List.set_cons_succ, List.filterMap_cons, id, List.map_cons, List.sum_cons,
      List.getElem?_cons_succ] <;> omega

/-- `TxCoins.spend` lowers the value of an entry by the amount of the output at the index, when that output is available. -/
theorem TxCoins.value_spend (c : TxCoins) (n : Nat) :
    (c.spend n).value = c.value - (match c.available n with | some out => out.amount.toInt | none => 0) :=
  outputs_value_set c.outputs n

/-- A list of outputs has a value that is not negative when no output of the list has a negative amount. -/
private theorem outputs_value_nonneg : ∀ (l : List (Option TxOut)), (∀ out, some out ∈ l → 0 ≤ out.amount.toInt) →
    0 ≤ ((l.filterMap id).map fun o => o.amount.toInt).sum
  | [], _ => by simp
  | none :: rest, h => by
    simpa using outputs_value_nonneg rest (fun out ho => h out (by simp [ho]))
  | some o :: rest, h => by
    have := outputs_value_nonneg rest (fun out ho => h out (by simp [ho]))
    have := h o (by simp)
    simp only [List.filterMap_cons, id, List.map_cons, List.sum_cons]
    omega

/-- In a set with amounts in range, the entry of each transaction ID has a value that is not negative. -/
theorem CoinSet.entryValue_nonneg {s : CoinSet} (hs : s.ValuesInRange) (txid : Hash256) :
    0 ≤ entryValue (s.accessCoins txid) := by
  unfold CoinSet.accessCoins
  cases h : s.entries[txidKey txid]? with
  | none => simp [entryValue]
  | some c => exact outputs_value_nonneg c.outputs (fun out ho => (hs _ c out h ho).1)

/--
`CoinSet.spend` lowers the total value by the amount of the coin of the outpoint.
Without a coin at the outpoint, the total value does not change.
-/
theorem CoinSet.totalValue_spend (s : CoinSet) (o : OutPoint) :
    (s.spend o).totalValue = s.totalValue - (match s.coin o with | some c => c.value | none => 0) := by
  have h := total_of_agree s.entries (s.spend o).entries (txidKey o.hash)
    (fun a ha => by rw [CoinSet.entries_spend]; simp [ha])
  rw [← CoinSet.totalValue_eq, ← CoinSet.totalValue_eq, CoinSet.entries_spend] at h
  simp only [↓reduceIte] at h
  unfold CoinSet.coin CoinSet.accessCoins
  cases hc : s.entries[txidKey o.hash]? with
  | none => simp only [hc] at h ⊢; omega
  | some c =>
    simp only [hc] at h ⊢
    have hv := TxCoins.value_spend c o.n.toNat
    have hval : entryValue (if (c.spend o.n.toNat).isPruned then none else some (c.spend o.n.toNat)) =
        (c.spend o.n.toNat).value := by
      split
      · rename_i hp; simp [entryValue, TxCoins.value_of_isPruned hp]
      · rfl
    rw [hval] at h
    simp only [entryValue] at h
    cases ha : c.available o.n.toNat with
    | none => simp only [ha, Option.map_none] at hv ⊢; omega
    | some out => simp only [ha, Option.map_some, Coin.value] at hv ⊢; omega

/--
`CoinSet.addTx` changes the total value by the value of the new entry less the value of the entry that it replaces.
The replaced entry is the earlier entry of the same transaction ID, if there is one.
-/
theorem CoinSet.totalValue_addTx (s : CoinSet) (tx : Transaction) (height : Nat) :
    (s.addTx tx height).totalValue =
      s.totalValue - entryValue (s.accessCoins tx.txid) + (TxCoins.ofTx tx height).value := by
  have h := total_of_agree s.entries (s.addTx tx height).entries (txidKey tx.txid)
    (fun a ha => by rw [CoinSet.entries_addTx]; simp [ha])
  rw [← CoinSet.totalValue_eq, ← CoinSet.totalValue_eq, CoinSet.entries_addTx] at h
  simp only [↓reduceIte] at h
  have hval : entryValue (if (TxCoins.ofTx tx height).isPruned then none else some (TxCoins.ofTx tx height)) =
      (TxCoins.ofTx tx height).value := by
    split
    · rename_i hp; simp [entryValue, TxCoins.value_of_isPruned hp]
    · rfl
  rw [hval] at h
  unfold CoinSet.accessCoins
  omega

/-- After `CoinSet.spend`, the outpoint has no coin. -/
theorem CoinSet.coin_spend_self (s : CoinSet) (o : OutPoint) : (s.spend o).coin o = none := by
  unfold CoinSet.coin CoinSet.accessCoins
  rw [CoinSet.entries_spend]
  simp only [↓reduceIte]
  cases hc : s.entries[txidKey o.hash]? with
  | none => rfl
  | some c =>
    simp only
    split
    · rfl
    · rename_i c' hc'
      split at hc'
      · cases hc'
      · cases hc'
        simp [TxCoins.available, TxCoins.spend, List.getElem?_set]
        split <;> simp

/-- `CoinSet.spend` changes the coin of no other outpoint. -/
theorem CoinSet.coin_spend_of_ne (s : CoinSet) {o o' : OutPoint} (hne : o' ≠ o) :
    (s.spend o).coin o' = s.coin o' := by
  unfold CoinSet.coin CoinSet.accessCoins
  rw [CoinSet.entries_spend]
  by_cases hh : o'.hash = o.hash
  · have hn : o.n.toNat ≠ o'.n.toNat := by
      intro h
      apply hne
      cases o; cases o'
      simp only [OutPoint.mk.injEq]
      exact ⟨hh, (UInt32.toNat_inj.mp h).symm⟩
    simp only [hh, ↓reduceIte]
    cases hc : s.entries[txidKey o.hash]? with
    | none => rfl
    | some c =>
      simp only
      have hav : (c.spend o.n.toNat).available o'.n.toNat = c.available o'.n.toNat := by
        simp [TxCoins.available, TxCoins.spend, hn]
      split
      · rename_i hp
        split at hp
        · rename_i hpr
          have : (c.spend o.n.toNat).available o'.n.toNat = none := by
            unfold TxCoins.isPruned at hpr
            unfold TxCoins.available
            cases hg : (c.spend o.n.toNat).outputs[o'.n.toNat]? with
            | none => rfl
            | some x =>
              have := List.all_eq_true.mp hpr x (List.mem_of_getElem? hg)
              cases x <;> simp_all
          rw [← hav, this]; rfl
        · cases hp
      · rename_i c' hp
        split at hp
        · cases hp
        · cases hp
          rw [hav]; rfl
  · have : txidKey o'.hash ≠ txidKey o.hash := fun h => hh (txidKey_inj h)
    simp [this]

/-! ## Inputs and spends -/

/-- When `hasDuplicate` is false, the outpoints of the list are pairwise different. -/
theorem nodup_of_hasDuplicate : ∀ {l : List OutPoint}, hasDuplicate l = false → l.Nodup
  | [], _ => List.nodup_nil
  | o :: rest, h => by
    simp only [hasDuplicate, Bool.or_eq_false_iff] at h
    rw [List.nodup_cons]
    exact ⟨by simpa using h.1, nodup_of_hasDuplicate h.2⟩

/-- A transaction that `checkTransaction` accepts with the duplicate-input check has pairwise different outpoints in its inputs. -/
theorem checkTransaction_ok_nodup {tx : Transaction} (h : checkTransaction tx true = .ok ()) :
    (tx.inputs.val.map TxIn.prevout).Nodup := by
  apply nodup_of_hasDuplicate
  unfold checkTransaction at h
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
          · rename_i hd
            simpa using hd

/-- When `lookupInputs` succeeds, every input of the list has a coin in the set. -/
theorem lookupInputs_some_coin {s : CoinSet} : ∀ {inputs : List TxIn} {coins : List Coin},
    lookupInputs s inputs = some coins → ∀ input ∈ inputs, ∃ c, s.coin input.prevout = some c
  | [], _, _ => by simp
  | i :: rest, coins, h => by
    unfold lookupInputs at h
    split at h
    · cases h
    · rename_i c hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, _⟩ := h
      intro input hin
      simp only [List.mem_cons] at hin
      rcases hin with rfl | hin
      · exact ⟨c, hc⟩
      · exact lookupInputs_some_coin htail input hin

/-- An outpoint with no coin has no coin after `CoinSet.spend` of any outpoint. -/
theorem CoinSet.coin_spend_none (s : CoinSet) (o : OutPoint) {o' : OutPoint} (h : s.coin o' = none) :
    (s.spend o).coin o' = none := by
  by_cases hne : o' = o
  · rw [hne]; exact s.coin_spend_self o
  · rw [s.coin_spend_of_ne hne]; exact h

/-- An outpoint with no coin has no coin after `spendInputs`. -/
theorem spendInputs_coin_none : ∀ {inputs : List TxIn} {s : CoinSet} {o : OutPoint}, s.coin o = none →
    (spendInputs s inputs).coin o = none
  | [], _, _, h => h
  | i :: rest, s, _, h => spendInputs_coin_none (inputs := rest) (s.coin_spend_none i.prevout h)

/-- After `spendInputs`, the outpoint of each input of the list has no coin. -/
theorem spendInputs_coin_of_mem : ∀ {inputs : List TxIn} {s : CoinSet} {input : TxIn}, input ∈ inputs →
    (spendInputs s inputs).coin input.prevout = none
  | i :: rest, s, input, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact spendInputs_coin_none (inputs := rest) (s.coin_spend_self _)
    · exact spendInputs_coin_of_mem (inputs := rest) h

/-- `lookupInputs` gives the same result after a spend of an outpoint that no input of the list names. -/
theorem lookupInputs_spend {s : CoinSet} {o : OutPoint} : ∀ {inputs : List TxIn},
    (∀ i ∈ inputs, i.prevout ≠ o) → lookupInputs (s.spend o) inputs = lookupInputs s inputs
  | [], _ => rfl
  | i :: rest, h => by
    unfold lookupInputs
    rw [s.coin_spend_of_ne (h i (by simp)), lookupInputs_spend (inputs := rest) (fun j hj => h j (by simp [hj]))]

/--
`spendInputs` lowers the total value by the amounts of the coins of the inputs.
The hypotheses are that the outpoints of the inputs are pairwise different, and that `lookupInputs` finds the coins in the set.
-/
theorem totalValue_spendInputs : ∀ {inputs : List TxIn} {s : CoinSet} {coins : List Coin},
    (inputs.map TxIn.prevout).Nodup → lookupInputs s inputs = some coins →
      (spendInputs s inputs).totalValue = s.totalValue - (coins.map Coin.value).sum
  | [], s, coins, _, h => by
    simp only [lookupInputs, Option.some.injEq] at h
    subst h
    simp [spendInputs]
  | i :: rest, s, coins, hnd, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    unfold lookupInputs at h
    split at h
    · cases h
    · rename_i c hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, rfl⟩ := h
      have hrest : lookupInputs (s.spend i.prevout) rest = some tail := by
        rw [lookupInputs_spend (fun j hj heq => hnd.1 j hj heq)]; exact htail
      have ih := totalValue_spendInputs (inputs := rest) hnd.2 hrest
      have hs := s.totalValue_spend i.prevout
      rw [hc] at hs
      simp only at hs
      simp only [spendInputs, List.map_cons, List.sum_cons]
      omega

/-! ## The transaction loop -/

/-- When `getValueIn` has a value, the value is the start value plus the amounts of the coins. -/
theorem getValueIn_eq : ∀ {coins : List Coin} {acc total : Int}, getValueIn acc coins = some total →
    total = acc + (coins.map Coin.value).sum
  | [], acc, total, h => by simp [getValueIn] at h; simp [h]
  | c :: rest, acc, total, h => by
    unfold getValueIn at h
    split at h
    · have := getValueIn_eq h
      simp only [List.map_cons, List.sum_cons]; omega
    · cases h

/-- When `addFee` has a value, the value is `nFees` plus the amounts of the coins less the output total. -/
theorem addFee_eq {nFees : Int} {coins : List Coin} {valueOut fees : Int}
    (h : addFee nFees coins valueOut = some fees) :
    fees = nFees + ((coins.map Coin.value).sum - valueOut) := by
  unfold addFee at h
  split at h
  · cases h
  · rename_i total ht
    have := getValueIn_eq ht
    split at h
    · cases h; omega
    · cases h

/--
The effect of one pass of the transaction loop that accepts.
The new set is `applyTransaction` of the old set.
A coinbase leaves `nFees` as it is.
For any other transaction, `lookupInputs` finds the coins of all its inputs in the old set.
`nFees` then grows by their amounts less the output total.
-/
theorem connectTransaction_ok {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32} {index : Nat}
    {st st' : ConnectState} {tx : Transaction} (h : connectTransaction verify ctx flags index st tx = .ok st') :
    st'.coins = applyTransaction st.coins ctx.height tx ∧
      (tx.isCoinBase = true → st'.fees = st.fees) ∧
      (tx.isCoinBase = false → ∃ coins, lookupInputs st.coins tx.inputs.val = some coins ∧
        st'.fees = st.fees + ((coins.map Coin.value).sum - tx.valueOut)) := by
  by_cases hcb : tx.isCoinBase
  · simp only [connectTransaction, hcb, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.false_eq_true] at h
    split at h
    · cases h
    · cases h
      simp [applyTransaction, hcb]
  · simp only [connectTransaction, hcb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at h
    cases hl : lookupInputs st.coins tx.inputs.val with
    | none => simp [hl] at h
    | some coins =>
      simp only [hl] at h
      split at h
      · cases h
      · cases hf : addFee st.fees coins tx.valueOut with
        | none => simp [hf] at h
        | some fees =>
          simp only [hf] at h
          split at h
          · cases h
          · split at h
            · cases h
            · cases h
              exact ⟨by simp [applyTransaction, hcb], by simp [hcb], fun _ => ⟨coins, rfl, addFee_eq hf⟩⟩

/-- The outputs that `TxCoins.ofTx` keeps are worth at most all the outputs, when no output has a negative amount. -/
private theorem ofTx_outputs_value_le : ∀ (outs : List TxOut), (∀ o ∈ outs, 0 ≤ o.amount.toInt) →
    (((outs.map fun o => if isUnspendable o.scriptPubKey then none else some o).filterMap id).map
      fun o => o.amount.toInt).sum ≤ (outs.map fun o => o.amount.toInt).sum
  | [], _ => by simp
  | o :: rest, h => by
    have ih := ofTx_outputs_value_le rest (fun x hx => h x (by simp [hx]))
    have := h o (by simp)
    simp only [List.map_cons, List.filterMap_cons, List.sum_cons]
    split
    · rename_i heq
      split at heq
      · omega
      · cases heq
    · rename_i b heq
      split at heq
      · cases heq
      · simp only [id, Option.some.injEq] at heq
        subst heq
        simp only [List.map_cons, List.sum_cons]; omega

/-- The entry of a transaction is worth at most the output total of the transaction, when no output has a negative amount. -/
theorem TxCoins.ofTx_value_le (tx : Transaction) (height : Nat) (h : ∀ o ∈ tx.outputs.val, 0 ≤ o.amount.toInt) :
    (TxCoins.ofTx tx height).value ≤ tx.valueOut :=
  ofTx_outputs_value_le tx.outputs.val h

/--
The value accounts of one pass of the transaction loop that accepts.
The hypotheses are a set with amounts in range and a transaction that `checkTransaction` accepted.
The new set has amounts in range.
The total value plus `nFees` does not grow, except by the output total of a coinbase.
-/
theorem connectTransaction_value {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32} {index : Nat}
    {st st' : ConnectState} {tx : Transaction} (hs : st.coins.ValuesInRange)
    (htx : checkTransaction tx true = .ok ())
    (h : connectTransaction verify ctx flags index st tx = .ok st') :
    st'.coins.ValuesInRange ∧
      st'.coins.totalValue + st'.fees ≤
        st.coins.totalValue + st.fees + (if tx.isCoinBase then tx.valueOut else 0) := by
  obtain ⟨hcoins, hcbfees, hfees⟩ := connectTransaction_ok h
  have hrange := checkTransaction_ok_range htx
  refine ⟨hcoins ▸ applyTransaction_range hs ctx.height tx hrange.1, ?_⟩
  have hle := TxCoins.ofTx_value_le tx ctx.height (fun o ho => (hrange.1 o ho).1)
  rw [hcoins]
  unfold applyTransaction
  by_cases hcb : tx.isCoinBase
  · have hadd := st.coins.totalValue_addTx tx ctx.height
    have := CoinSet.entryValue_nonneg hs tx.txid
    have := hcbfees hcb
    simp only [hcb, ↓reduceIte]
    omega
  · simp only [Bool.not_eq_true] at hcb
    obtain ⟨coins, hl, hf⟩ := hfees hcb
    have hadd := (spendInputs st.coins tx.inputs.val).totalValue_addTx tx ctx.height
    have := CoinSet.entryValue_nonneg (spendInputs_range (inputs := tx.inputs.val) hs) tx.txid
    have := totalValue_spendInputs (checkTransaction_ok_nodup htx) hl
    simp only [hcb, Bool.false_eq_true, ↓reduceIte]
    omega

/--
The value accounts of the transaction loop when it accepts.
The hypotheses are a set with amounts in range and transactions that `checkTransaction` accepted.
The final set has amounts in range.
The total value plus `nFees` grows by at most the output totals of the coinbase transactions.
-/
theorem connectTransactions_value {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32} :
    ∀ {txs : List Transaction} {index : Nat} {st st' : ConnectState}, st.coins.ValuesInRange →
      (∀ tx ∈ txs, checkTransaction tx true = .ok ()) →
      connectTransactions verify ctx flags index st txs = .ok st' →
        st'.coins.ValuesInRange ∧
          st'.coins.totalValue + st'.fees ≤ st.coins.totalValue + st.fees + coinbaseValueOut txs
  | [], _, st, st', hs, _, h => by
    simp only [connectTransactions, Except.ok.injEq] at h
    subst h
    exact ⟨hs, by simp [coinbaseValueOut]⟩
  | tx :: rest, index, st, st', hs, htxs, h => by
    unfold connectTransactions at h
    split at h
    · cases h
    · rename_i st1 h1
      obtain ⟨hs1, hv1⟩ := connectTransaction_value hs (htxs tx (by simp)) h1
      obtain ⟨hs', hv'⟩ := connectTransactions_value (txs := rest) hs1 (fun t ht => htxs t (by simp [ht])) h
      refine ⟨hs', ?_⟩
      have : coinbaseValueOut (tx :: rest) = (if tx.isCoinBase then tx.valueOut else 0) + coinbaseValueOut rest := by
        unfold coinbaseValueOut
        by_cases hcb : tx.isCoinBase <;> simp [hcb]
      omega

/--
The sets of the transaction loop when it accepts.
The final set is `coinsBefore` at the end of the list.
For each transaction that is not a coinbase, `lookupInputs` finds the coins of all its inputs in `coinsBefore` at its index.
-/
theorem connectTransactions_inputs {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32} :
    ∀ {txs : List Transaction} {index : Nat} {st st' : ConnectState},
      connectTransactions verify ctx flags index st txs = .ok st' →
        st'.coins = coinsBefore st.coins ctx.height txs txs.length ∧
          ∀ (i : Nat) (tx : Transaction), txs[i]? = some tx → tx.isCoinBase = false →
            ∃ coins, lookupInputs (coinsBefore st.coins ctx.height txs i) tx.inputs.val = some coins
  | [], _, st, st', h => by
    simp only [connectTransactions, Except.ok.injEq] at h
    subst h
    simp [coinsBefore]
  | t :: rest, index, st, st', h => by
    unfold connectTransactions at h
    split at h
    · cases h
    · rename_i st1 h1
      obtain ⟨hcoins, _, hfees⟩ := connectTransaction_ok h1
      obtain ⟨hfinal, hrest⟩ := connectTransactions_inputs (txs := rest) h
      rw [hcoins] at hfinal hrest
      refine ⟨by simpa [coinsBefore] using hfinal, ?_⟩
      intro i tx hi hcb
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        obtain ⟨coins, hl, _⟩ := hfees hcb
        exact ⟨coins, by simpa [coinsBefore] using hl⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi
        simpa [coinsBefore] using hrest j tx hi hcb

/-! ## `connectBlock` -/

/-- A block that `checkBlock` accepts has a first transaction that is a coinbase, and no other coinbase. -/
theorem checkBlock_ok_coinbase {network : Work.WorkNetwork} {fCheckPOW fCheckMerkleRoot : Bool} {b : Block}
    (h : checkBlock network fCheckPOW fCheckMerkleRoot b = .ok ()) :
    ∃ first others, b.transactions = first :: others ∧ first.isCoinBase = true ∧
      others.any Transaction.isCoinBase = false := by
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
          · rename_i first others heq
            split at h
            · cases h
            · rename_i hfirst
              split at h
              · cases h
              · rename_i hothers
                exact ⟨first, others, heq, by simpa using hfirst, by simpa using hothers⟩

/--
The facts that an accepted `connectBlock` supplies.
`checkBlock` accepted the block, and one of two cases holds.

1. The header has the hash of the mainnet genesis block, and the result is the unchanged set with no change.
2. The header has another hash. The transaction loop accepted from the set `s` with `nFees` 0. The subsidy has a value. `nFees` plus the subsidy is in the `int64_t` range. The first transaction pays at most `nFees` plus the subsidy. The new set is the set of the loop.

So in case 2 acceptance supplies a successful subsidy.
The result is also not `outOfDomain`, so each sum that the run tested was in the `int64_t` range.
Acceptance does not supply the bound of `connect_fits`, which is a sufficient condition and not a necessary one.
-/
theorem connectBlock_ok {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext} {s : CoinSet}
    {b : Block} {r : ConnectResult} (h : connectBlock verify fJustCheck ctx s b = .ok r) :
    checkBlock .mainnet (!fJustCheck) (!fJustCheck) b = .ok () ∧
      ((some b.header.pure.getHash = genesisHash? .mainnet ∧ r = ⟨s, []⟩) ∨
        (some b.header.pure.getHash ≠ genesisHash? .mainnet ∧ ∃ (st : ConnectState) (subsidy : Nat),
          connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions = .ok st ∧
          getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash = .ok subsidy ∧
          inInt64Range (st.fees + (subsidy : Int)) = true ∧
          (match b.transactions with | [] => 0 | coinbase :: _ => coinbase.valueOut) ≤ st.fees + (subsidy : Int) ∧
          r.coins = st.coins)) := by
  unfold connectBlock at h
  split at h
  · cases h
  · rename_i hcheck
    refine ⟨hcheck, ?_⟩
    split at h
    · rename_i hg
      cases h
      exact .inl ⟨by simpa using hg, rfl⟩
    · rename_i hg
      simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i st hst
            split at h
            · cases h
            · rename_i subsidy hsub
              split at h
              · cases h
              · rename_i hdom
                cases htx : b.transactions with
                | nil =>
                  rw [htx] at h
                  simp only at h
                  split at h
                  · cases h
                  · cases h
                    exact .inr ⟨by simpa using hg, st, subsidy, htx ▸ hst, hsub, by simpa using hdom,
                      by simp only; omega, rfl⟩
                | cons first others =>
                  rw [htx] at h
                  simp only at h
                  split at h
                  · cases h
                  · cases h
                    exact .inr ⟨by simpa using hg, st, subsidy, htx ▸ hst, hsub, by simpa using hdom,
                      by simp only; omega, rfl⟩

/--
`connectBlock` accepts a block with the hash of the mainnet genesis block without a change: the result is the set `s` and no change.
The definition follows Core's own special case (D114, lines 1821 to 1825), which returns after `CheckBlock` accepts and before the transaction loop.
-/
theorem connectBlock_genesis {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext} {s : CoinSet}
    {b : Block} {r : ConnectResult} (h : connectBlock verify fJustCheck ctx s b = .ok r)
    (hg : some b.header.pure.getHash = genesisHash? .mainnet) : r = ⟨s, []⟩ := by
  rcases (connectBlock_ok h).2 with ⟨_, hr⟩ | ⟨hne, _⟩
  · exact hr
  · exact absurd hg hne

/-- When `connectBlock` accepts a block whose hash is not the genesis hash, the subsidy has a value, and `subsidyValue` is that value. -/
theorem connectBlock_ok_subsidy {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext}
    {s : CoinSet} {b : Block} {r : ConnectResult} (h : connectBlock verify fJustCheck ctx s b = .ok r)
    (hg : some b.header.pure.getHash ≠ genesisHash? .mainnet) :
    getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash = .ok (subsidyValue ctx.height ctx.prevHash) := by
  rcases (connectBlock_ok h).2 with ⟨heq, _⟩ | ⟨_, st, subsidy, _, hsub, _⟩
  · exact absurd heq hg
  · simp [subsidyValue, hsub]

/--
When `connectBlock` accepts a block whose hash is not the genesis hash, the new set is `coinsBefore` at the end of the block's transactions.
So the sets of `connect_spends_available` are the sets of the accepted run.
-/
theorem connectBlock_ok_coins {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext} {s : CoinSet}
    {b : Block} {r : ConnectResult} (h : connectBlock verify fJustCheck ctx s b = .ok r)
    (hg : some b.header.pure.getHash ≠ genesisHash? .mainnet) :
    r.coins = coinsBefore s ctx.height b.transactions b.transactions.length := by
  rcases (connectBlock_ok h).2 with ⟨heq, _⟩ | ⟨_, st, subsidy, hst, _, _, _, hr⟩
  · exact absurd heq hg
  · rw [hr]; exact (connectTransactions_inputs hst).1

/--
Each input of an accepted block spends a coin that is present, and each transaction spends each coin at most once (design record 0010, section 6).

Suppose that `connectBlock` accepts the block `b` on the coin set `s`.
Suppose also that the hash of `b` is not the hash of the mainnet genesis block.
Let `tx` be the transaction at `index`, and suppose that it is not a coinbase.
Let `before` be `coinsBefore` at `index`: the set just before `tx`, which has the coins that earlier transactions of the block created.
Then:

1. The outpoints of the inputs of `tx` are pairwise different.
2. Every input of `tx` has a coin in `before`.
3. After the spends of `tx` (`spendInputs before`), no input of `tx` has a coin.

The theorem holds for every verifier, both values of `fJustCheck` and every context.
It needs no hypothesis on the amounts of the set.
`connectBlock_ok_coins` shows that the last of these sets is the new set of the result.

The genesis hypothesis matches Core's own special case in `ConnectBlock` (D114, lines 1821 to 1825).
For a block with the genesis hash, `connectBlock` returns after `checkBlock` and does not run the transaction loop.
`connectBlock_genesis` states its result.

The statement is about coins as created, not about outpoints.
Conclusion 3 is about the set after the spends of `tx` and before its outputs enter.
A later transaction with the same ID can create another coin at an outpoint that was spent.
That can occur when every coin of the earlier entry is spent, or for a coinbase with BIP30 skipped.
The theorem does not exclude a spend of the later coin.
-/
@[theorem_tag property]
theorem connect_spends_available (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) (r : ConnectResult) (h : connectBlock verify fJustCheck ctx s b = .ok r)
    (hg : some b.header.pure.getHash ≠ genesisHash? .mainnet)
    (index : Nat) (tx : Transaction) (htx : b.transactions[index]? = some tx) (hcb : tx.isCoinBase = false) :
    (tx.inputs.val.map TxIn.prevout).Nodup ∧
      ∀ input ∈ tx.inputs.val,
        (∃ c, (coinsBefore s ctx.height b.transactions index).coin input.prevout = some c) ∧
          (spendInputs (coinsBefore s ctx.height b.transactions index) tx.inputs.val).coin input.prevout = none := by
  obtain ⟨hcheck, hcases⟩ := connectBlock_ok h
  rcases hcases with ⟨heq, _⟩ | ⟨_, st, subsidy, hst, _⟩
  · exact absurd heq hg
  · obtain ⟨coins, hl⟩ := (connectTransactions_inputs hst).2 index tx htx hcb
    refine ⟨checkTransaction_ok_nodup (checkBlock_ok_transactions hcheck tx (List.mem_of_getElem? htx)), ?_⟩
    intro input hin
    exact ⟨lookupInputs_some_coin hl input hin, spendInputs_coin_of_mem hin⟩

/--
An accepted block keeps the amounts in range, and adds at most the subsidy to the total value.
`connect_valuesInRange` and `connect_value_bound` state the two parts.
-/
theorem connect_value {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext}
    {s : CoinSet} {b : Block} {r : ConnectResult} (hcoins : s.ValuesInRange)
    (h : connectBlock verify fJustCheck ctx s b = .ok r) :
    r.coins.ValuesInRange ∧
      r.coins.totalValue ≤ s.totalValue + (subsidyValue ctx.height ctx.prevHash : Int) := by
  obtain ⟨hcheck, hcases⟩ := connectBlock_ok h
  rcases hcases with ⟨_, hr⟩ | ⟨_, st, subsidy, hst, hsub, _, hcb, hr⟩
  · subst hr
    exact ⟨hcoins, by simp only; omega⟩
  · obtain ⟨hrange, hvalue⟩ := connectTransactions_value hcoins (checkBlock_ok_transactions hcheck) hst
    rw [hr]
    refine ⟨hrange, ?_⟩
    obtain ⟨first, others, heq, hfirst, hothers⟩ := checkBlock_ok_coinbase hcheck
    have hsum : coinbaseValueOut b.transactions = first.valueOut := by
      have : others.filter Transaction.isCoinBase = [] := by
        rw [List.filter_eq_nil_iff]
        intro t ht
        have := List.any_eq_false.mp hothers t ht
        simpa using this
      simp [coinbaseValueOut, heq, hfirst, this]
    have hv : subsidyValue ctx.height ctx.prevHash = subsidy := by simp [subsidyValue, hsub]
    rw [heq] at hcb
    simp only at hcb hvalue
    rw [hsum] at hvalue
    rw [hv]
    omega

/--
When `connectBlock` accepts a block on a set with amounts in range (`CoinSet.ValuesInRange`), the new set has amounts in range.
The theorem holds for every verifier, both values of `fJustCheck`, every context and every block.
-/
@[theorem_tag property]
theorem connect_valuesInRange (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) (r : ConnectResult) (hcoins : s.ValuesInRange)
    (h : connectBlock verify fJustCheck ctx s b = .ok r) : r.coins.ValuesInRange :=
  (connect_value hcoins h).1

/--
An accepted block adds at most its subsidy to the total value of the coin set (design record 0010, section 6).

Suppose that every output of the set `s` has an amount from 0 to `MAX_MONEY` (`CoinSet.ValuesInRange`), and that `connectBlock` accepts the block `b` on `s`.
Then `CoinSet.totalValue` of the new set is at most that of `s` plus `subsidyValue`.

`subsidyValue` is the subsidy of the context's height and previous hash.
Take a block whose hash is not the genesis hash.
Acceptance then shows that the subsidy has a value and that the result is not `outOfDomain` (`connectBlock_ok`).
For a block with the genesis hash, the set does not change.

The fees cancel: each fee leaves the set with the inputs, and the coinbase can claim it.
The bound is an upper bound only.
A coinbase can claim less, an unspendable output does not enter the set, and a replaced entry leaves it.
The proof uses the hypothesis on `s` only for the lower bound 0 of the amounts.
The theorem holds for every verifier, both values of `fJustCheck` and every context.
-/
@[theorem_tag property]
theorem connect_value_bound (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext)
    (s : CoinSet) (b : Block) (r : ConnectResult) (hcoins : s.ValuesInRange)
    (h : connectBlock verify fJustCheck ctx s b = .ok r) :
    r.coins.totalValue ≤ s.totalValue + (subsidyValue ctx.height ctx.prevHash : Int) :=
  (connect_value hcoins h).2

/-! ## A chain of blocks -/

/--
The value bound for a list of blocks with any supplied contexts.

Suppose that the set `s` has amounts in range, and that `connectChain` accepts every block of the list from `s`.
Then the final set has amounts in range.
Its total value is at most that of `s` plus the sum of `subsidyValue` over the supplied contexts.

The contexts are not related to the blocks or to each other here: a height can repeat.
`chain_issuance_bound` is the statement for the contexts of a chain.
-/
@[theorem_tag property]
theorem connectChain_issuance_bound (verify : SignatureVerifier) (fJustCheck : Bool) :
    ∀ (chain : List (ConnectContext × Block)) (s final : CoinSet), s.ValuesInRange →
      connectChain verify fJustCheck s chain = .ok final →
        final.ValuesInRange ∧
          final.totalValue ≤
            s.totalValue + (chain.map fun p => (subsidyValue p.1.height p.1.prevHash : Int)).sum
  | [], s, final, hs, h => by
    simp only [connectChain, Except.ok.injEq] at h
    subst h
    exact ⟨hs, by simp⟩
  | (ctx, b) :: rest, s, final, hs, h => by
    unfold connectChain at h
    split at h
    · cases h
    · rename_i r hr
      obtain ⟨hrange, hv⟩ := connect_value hs hr
      obtain ⟨hfinal, hv'⟩ := connectChain_issuance_bound verify fJustCheck rest r.coins final hrange h
      refine ⟨hfinal, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega

/-- For the contexts of a chain (`ChainLinked`), the sum of `subsidyValue` over the contexts is `chainSubsidy` of the blocks. -/
theorem chainSubsidy_eq : ∀ (chain : List (ConnectContext × Block)) (prev : Block) (height : Nat),
    ChainLinked prev height chain →
      (chain.map fun p => (subsidyValue p.1.height p.1.prevHash : Int)).sum =
        chainSubsidy prev height (chain.map Prod.snd)
  | [], _, _, _ => rfl
  | (ctx, b) :: rest, prev, height, h => by
    obtain ⟨hh, hp, hrest⟩ := h
    simp only [List.map_cons, List.sum_cons, chainSubsidy]
    rw [chainSubsidy_eq rest b (height + 1) hrest, hh, hp]

/--
The coins of a chain from the mainnet genesis block are worth at most the sum of the subsidies of its blocks (design record 0010, section 6).

Let `genesis` be a block with the hash of the mainnet genesis block, and let `chain` be the blocks after it with their contexts.
Suppose that the contexts are those of a chain (`ChainLinked genesis 1`).
So the heights are 1, 2 and so on, and each previous hash is the hash of the block before.
Suppose that `connectChain` accepts `genesis` and then every block of `chain`, from the empty set.
Then the total value of the final set is at most `chainSubsidy`: the sum of the subsidies at the heights from 1.

The genesis block adds no coin, so its subsidy is not in the sum, and its context is free.
The other fields of the contexts, `bip34Ancestor` and `csvActive`, are also free.
The sum is in the integers, with no `int64_t` bound.
The bound is an upper bound only: a coinbase can claim less, and unspendable and replaced outputs leave the set.

The theorem is about `connectBlock` block by block.
It says nothing about the header checks, about proof of work, or about which chain a node selects.
It holds for every verifier and both values of `fJustCheck`.
-/
@[theorem_tag property]
theorem chain_issuance_bound (verify : SignatureVerifier) (fJustCheck : Bool) (ctx₀ : ConnectContext)
    (genesis : Block) (chain : List (ConnectContext × Block)) (final : CoinSet)
    (hgenesis : some genesis.header.pure.getHash = genesisHash? .mainnet)
    (hlinked : ChainLinked genesis 1 chain)
    (h : connectChain verify fJustCheck .empty ((ctx₀, genesis) :: chain) = .ok final) :
    final.totalValue ≤ chainSubsidy genesis 1 (chain.map Prod.snd) := by
  unfold connectChain at h
  split at h
  · cases h
  · rename_i r hr
    rw [connectBlock_genesis hr hgenesis] at h
    have := (connectChain_issuance_bound verify fJustCheck chain .empty final CoinSet.empty_valuesInRange h).2
    rw [CoinSet.totalValue_empty, chainSubsidy_eq chain genesis 1 hlinked] at this
    omega

end DogeLib.Block
