module

public import DogeLib.Block.Proofs.ConnectProperties
public import DogeLib.Block.Validate
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Block validation on a restricted coin set

`validateBlock` reads and changes the coin set only at the transaction IDs that the block names (design record 0011, section 3.3).
Those IDs are the ID of each transaction of the block, and the ID in the outpoint of each input.

- `validateBlock_agree`: two coin sets with equal entries at a set of keys give the same error, or accept with the same coin changes and with new sets that again have equal entries at those keys. The set of keys must hold the key of every ID that the block names.
- `validateBlock_frame`: an accepted block changes no entry whose key is not the key of an ID that the block names.
- `validateBlock_restrict`: the two statements for a set `s` and its restriction `s.restrict keep`, which is the target of design record 0011, decision 2.

## Keys

A coin set stores the entry of a transaction ID under `txidKey` of that ID.
The statements are about keys: `keep` is a predicate on keys, and `CoinSet.restrict` keeps the entries whose key satisfies it.
`txidKey_inj` shows that different IDs have different keys.
So a set of IDs and the set of their keys determine each other.

The design record expected a hypothesis that each entry of the set is under the key of its own ID.
The statements need no such hypothesis, because the restriction selects an entry by its key, and `validateBlock` reads no `TxCoins.txid` field of an entry.

## What the theorems do not say

The theorems are about `validateBlock` on one block.
`validateBlock_agree` keeps its own hypothesis on the coin sets, so it applies again to the next block of a range, when `keep` holds the keys of that block too.
No theorem here is about a list of blocks, about the oracle's adapter, or about the file of a snapshot.
The oracle reads a snapshot and merges the entries of a run into a digest in `IO` code, which no theorem covers (SOUNDNESS.md, B4).
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script

/-! ## Definitions -/

/-- The entries of `s` whose key satisfies `keep`: the set `s|T` of design record 0011, section 3.3, where `keep` holds for the keys of `T`. -/
def CoinSet.restrict (s : CoinSet) (keep : Nat → Bool) : CoinSet := ⟨s.entries.filter fun k _ => keep k⟩

/-- The sets `s` and `r` have equal entries at every key that satisfies `keep`. -/
def CoinSet.AgreeOn (keep : Nat → Bool) (s r : CoinSet) : Prop :=
  ∀ k, keep k = true → r.entries[k]? = s.entries[k]?

/--
`keep` holds for the key of every transaction ID that the transactions name: the ID of each transaction, and the ID in the outpoint of each input.
The inputs include the one input of a coinbase, whose outpoint has the null ID.
-/
def NamesWithin (keep : Nat → Bool) (txs : List Transaction) : Prop :=
  ∀ tx ∈ txs, keep (txidKey tx.txid) = true ∧ ∀ input ∈ tx.inputs.val, keep (txidKey input.prevout.hash) = true

/-- No transaction names the key `k`: `k` is not the key of the ID of a transaction, or of the ID in the outpoint of an input. -/
def NotNamed (k : Nat) (txs : List Transaction) : Prop :=
  ∀ tx ∈ txs, k ≠ txidKey tx.txid ∧ ∀ input ∈ tx.inputs.val, k ≠ txidKey input.prevout.hash

/-- Two results of one check have the same outcome: the same error, or two values that `R` relates. -/
def SameOutcome {ε α : Type} (R : α → α → Prop) : Except ε α → Except ε α → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok a' => R a a'
  | _, _ => False

/-- Two states of the transaction loop have equal fees, costs and changes, and their coin sets have equal entries at the keys of `keep`. -/
def ConnectState.AgreeOn (keep : Nat → Bool) (st st' : ConnectState) : Prop :=
  st'.fees = st.fees ∧ st'.sigOpsCost = st.sigOpsCost ∧ st'.changes = st.changes ∧
    CoinSet.AgreeOn keep st.coins st'.coins

/-- Two results of an accepted block have equal changes, and their coin sets have equal entries at the keys of `keep`. -/
def ConnectResult.AgreeOn (keep : Nat → Bool) (r r' : ConnectResult) : Prop :=
  r'.changes = r.changes ∧ CoinSet.AgreeOn keep r.coins r'.coins

/-- An accepted result on both sides has the same outcome when `R` relates the two values. -/
theorem SameOutcome.ok {ε α : Type} {R : α → α → Prop} {a a' : α} (h : R a a') :
    SameOutcome (ε := ε) R (.ok a) (.ok a') := h

/-- A test that fails with one error on both sides keeps the same outcome. -/
theorem SameOutcome.ite {ε α : Type} {R : α → α → Prop} {c : Prop} [Decidable c] {e : ε} {x y : Except ε α}
    (h : SameOutcome R x y) : SameOutcome R (if c then .error e else x) (if c then .error e else y) := by
  split
  · rfl
  · exact h

/-! ## The coin set -/

/-- The entry of each key in a restricted set: the entry of the set when `keep` holds for the key, and nothing otherwise. -/
theorem CoinSet.entries_restrict (s : CoinSet) (keep : Nat → Bool) (k : Nat) :
    (s.restrict keep).entries[k]? = if keep k then s.entries[k]? else none := by
  unfold CoinSet.restrict
  rw [Std.TreeMap.getElem?_filter']
  cases keep k <;> cases s.entries[k]? <;> simp

/-- A set and its restriction have equal entries at the keys of `keep`. -/
theorem CoinSet.agreeOn_restrict (s : CoinSet) (keep : Nat → Bool) : CoinSet.AgreeOn keep s (s.restrict keep) := by
  intro k hk
  rw [CoinSet.entries_restrict, hk]; rfl

/-- Two sets with equal entries at the key of an outpoint's ID have the same coin for that outpoint. -/
theorem agreeOn_coin {keep : Nat → Bool} {s r : CoinSet} (h : CoinSet.AgreeOn keep s r) {o : OutPoint}
    (ho : keep (txidKey o.hash) = true) : r.coin o = s.coin o := by
  unfold CoinSet.coin CoinSet.accessCoins
  rw [h _ ho]

/-- Two sets with equal entries at the key of an ID give the same result of the BIP30 test for that ID. -/
theorem agreeOn_haveUnspent {keep : Nat → Bool} {s r : CoinSet} (h : CoinSet.AgreeOn keep s r) {txid : Hash256}
    (ht : keep (txidKey txid) = true) : r.haveUnspent txid = s.haveUnspent txid := by
  unfold CoinSet.haveUnspent CoinSet.accessCoins
  rw [h _ ht]

/-- One spend keeps equal entries at the keys of `keep`. -/
theorem agreeOn_spend {keep : Nat → Bool} {s r : CoinSet} (h : CoinSet.AgreeOn keep s r) (o : OutPoint) :
    CoinSet.AgreeOn keep (s.spend o) (r.spend o) := by
  intro k hk
  rw [CoinSet.entries_spend, CoinSet.entries_spend]
  by_cases hko : k = txidKey o.hash
  · subst hko
    simp only [↓reduceIte]
    rw [h _ hk]
  · simp only [hko, ↓reduceIte]
    exact h k hk

/-- A new entry keeps equal entries at the keys of `keep`. -/
theorem agreeOn_addTx {keep : Nat → Bool} {s r : CoinSet} (h : CoinSet.AgreeOn keep s r) (tx : Transaction)
    (height : Nat) : CoinSet.AgreeOn keep (s.addTx tx height) (r.addTx tx height) := by
  intro k hk
  rw [CoinSet.entries_addTx, CoinSet.entries_addTx]
  split
  · rfl
  · exact h k hk

/-- The spends of a list of inputs keep equal entries at the keys of `keep`. -/
theorem agreeOn_spendInputs {keep : Nat → Bool} : ∀ (inputs : List TxIn) {s r : CoinSet},
    CoinSet.AgreeOn keep s r → CoinSet.AgreeOn keep (spendInputs s inputs) (spendInputs r inputs)
  | [], _, _, h => by simpa [spendInputs] using h
  | input :: rest, _, _, h => by
    simpa [spendInputs] using agreeOn_spendInputs rest (agreeOn_spend h input.prevout)

/-- Two sets with equal entries at the keys of the inputs' IDs give the same coins for the inputs. -/
theorem agreeOn_lookupInputs {keep : Nat → Bool} {s r : CoinSet} (h : CoinSet.AgreeOn keep s r) :
    ∀ (inputs : List TxIn), (∀ input ∈ inputs, keep (txidKey input.prevout.hash) = true) →
      lookupInputs r inputs = lookupInputs s inputs
  | [], _ => by simp [lookupInputs]
  | input :: rest, hin => by
    simp only [lookupInputs]
    rw [agreeOn_coin h (hin input (by simp)), agreeOn_lookupInputs h rest (fun i hi => hin i (by simp [hi]))]

/-- One spend changes no entry at a key other than the key of the outpoint's ID. -/
theorem spendInputs_entries_of_ne : ∀ (inputs : List TxIn) (s : CoinSet) (k : Nat),
    (∀ input ∈ inputs, k ≠ txidKey input.prevout.hash) → (spendInputs s inputs).entries[k]? = s.entries[k]?
  | [], _, _, _ => by simp [spendInputs]
  | input :: rest, s, k, h => by
    simp only [spendInputs]
    rw [spendInputs_entries_of_ne rest _ k (fun i hi => h i (by simp [hi])), CoinSet.entries_spend]
    simp [h input (by simp)]

/-- The unchecked change of one transaction changes no entry at a key that the transaction does not name. -/
theorem applyTransaction_entries_of_ne (s : CoinSet) (height : Nat) (tx : Transaction) (k : Nat)
    (hid : k ≠ txidKey tx.txid) (hin : ∀ input ∈ tx.inputs.val, k ≠ txidKey input.prevout.hash) :
    (applyTransaction s height tx).entries[k]? = s.entries[k]? := by
  unfold applyTransaction
  rw [CoinSet.entries_addTx]
  simp only [hid, ↓reduceIte]
  split
  · rfl
  · exact spendInputs_entries_of_ne _ _ _ hin

/-- The unchecked changes of a list of transactions change no entry at a key that no transaction names. -/
theorem foldl_applyTransaction_entries_of_ne (height : Nat) (k : Nat) : ∀ (txs : List Transaction) (s : CoinSet),
    NotNamed k txs → (txs.foldl (fun s tx => applyTransaction s height tx) s).entries[k]? = s.entries[k]?
  | [], _, _ => by simp
  | tx :: rest, s, h => by
    simp only [List.foldl_cons]
    rw [foldl_applyTransaction_entries_of_ne height k rest _ (fun t ht => h t (by simp [ht])),
      applyTransaction_entries_of_ne s height tx k (h tx (by simp)).1 (h tx (by simp)).2]

/-! ## The transaction loop -/

/-- One pass of the transaction loop has the same outcome on two states that agree at the keys of `keep`, when `keep` holds the keys that the transaction names. -/
theorem connectTransaction_agree {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32} {index : Nat}
    {keep : Nat → Bool} {st st' : ConnectState} {tx : Transaction} (h : st.AgreeOn keep st')
    (hid : keep (txidKey tx.txid) = true)
    (hin : ∀ input ∈ tx.inputs.val, keep (txidKey input.prevout.hash) = true) :
    SameOutcome (ConnectState.AgreeOn keep) (connectTransaction verify ctx flags index st tx)
      (connectTransaction verify ctx flags index st' tx) := by
  obtain ⟨c, fees, cost, changes⟩ := st
  obtain ⟨c', fees', cost', changes'⟩ := st'
  obtain ⟨hf, hc, hch, hco⟩ := h
  simp only at hf hc hch hco
  subst hf hc hch
  have hlook : lookupInputs c' tx.inputs.val = lookupInputs c tx.inputs.val := agreeOn_lookupInputs hco _ hin
  have hspent : CoinSet.AgreeOn keep (if tx.isCoinBase = true then c else spendInputs c tx.inputs.val)
      (if tx.isCoinBase = true then c' else spendInputs c' tx.inputs.val) := by
    split
    · exact hco
    · exact agreeOn_spendInputs _ hco
  have hhave := agreeOn_haveUnspent hspent hid
  unfold connectTransaction
  simp only [hlook]
  split
  · simp [SameOutcome]
  · split
    · simp [SameOutcome]
    · split
      · simp [SameOutcome]
      · split
        · simp [SameOutcome]
        · simp only [hhave]
          exact SameOutcome.ite (SameOutcome.ok ⟨rfl, rfl, rfl, agreeOn_addTx hspent tx ctx.height⟩)

/-- The transaction loop has the same outcome on two states that agree at the keys of `keep`, when `keep` holds the keys that the transactions name. -/
theorem connectTransactions_agree {verify : SignatureVerifier} {ctx : ConnectContext} {flags : UInt32}
    {keep : Nat → Bool} : ∀ (txs : List Transaction) {index : Nat} {st st' : ConnectState},
    st.AgreeOn keep st' → NamesWithin keep txs →
      SameOutcome (ConnectState.AgreeOn keep) (connectTransactions verify ctx flags index st txs)
        (connectTransactions verify ctx flags index st' txs)
  | [], _, _, _, h, _ => by simpa [connectTransactions, SameOutcome] using h
  | tx :: rest, index, st, st', h, hn => by
    have h1 := connectTransaction_agree (verify := verify) (ctx := ctx) (flags := flags) (index := index) h
      (hn tx (by simp)).1 (hn tx (by simp)).2
    unfold connectTransactions
    cases ha : connectTransaction verify ctx flags index st tx with
    | error e =>
      cases hb : connectTransaction verify ctx flags index st' tx with
      | error e' => rw [ha, hb] at h1; simpa [SameOutcome] using h1
      | ok b => rw [ha, hb] at h1; exact absurd h1 (by simp [SameOutcome])
    | ok a =>
      cases hb : connectTransaction verify ctx flags index st' tx with
      | error e' => rw [ha, hb] at h1; exact absurd h1 (by simp [SameOutcome])
      | ok b =>
        rw [ha, hb] at h1
        exact connectTransactions_agree rest (by simpa [SameOutcome] using h1) (fun t ht => hn t (by simp [ht]))

/-! ## `connectBlock` and `validateBlock` -/

/-- `connectBlock` has the same outcome on two coin sets that agree at the keys of `keep`, when `keep` holds the keys that the block names. -/
theorem connectBlock_agree {verify : SignatureVerifier} {fJustCheck : Bool} {ctx : ConnectContext} {keep : Nat → Bool}
    {s r : CoinSet} {b : Block} (h : CoinSet.AgreeOn keep s r) (hn : NamesWithin keep b.transactions) :
    SameOutcome (ConnectResult.AgreeOn keep) (connectBlock verify fJustCheck ctx s b)
      (connectBlock verify fJustCheck ctx r b) := by
  have hany : (b.transactions.any fun tx => r.haveUnspent tx.txid) =
      (b.transactions.any fun tx => s.haveUnspent tx.txid) := by
    have : ∀ (txs : List Transaction), (∀ tx ∈ txs, keep (txidKey tx.txid) = true) →
        (txs.any fun tx => r.haveUnspent tx.txid) = (txs.any fun tx => s.haveUnspent tx.txid) := by
      intro txs
      induction txs with
      | nil => intro _; rfl
      | cons tx rest ih =>
        intro hk
        simp only [List.any_cons]
        rw [agreeOn_haveUnspent h (hk tx (by simp)), ih (fun t ht => hk t (by simp [ht]))]
    exact this _ (fun tx ht => (hn tx ht).1)
  have hloop := connectTransactions_agree (verify := verify) (ctx := ctx) (flags := connectScriptFlags ctx.height)
    (index := 0) b.transactions (st := ⟨s, 0, 0, []⟩) (st' := ⟨r, 0, 0, []⟩) ⟨rfl, rfl, rfl, h⟩ hn
  unfold connectBlock
  simp only [hany]
  split
  · simp [SameOutcome]
  · split
    · exact ⟨rfl, h⟩
    · split
      · simp [SameOutcome]
      · split
        · simp [SameOutcome]
        · cases ha : connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions with
          | error e =>
            cases hb : connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨r, 0, 0, []⟩ b.transactions with
            | error e' => rw [ha, hb] at hloop; simpa [SameOutcome] using hloop
            | ok st' => rw [ha, hb] at hloop; exact absurd hloop (by simp [SameOutcome])
          | ok st =>
            cases hb : connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨r, 0, 0, []⟩ b.transactions with
            | error e' => rw [ha, hb] at hloop; exact absurd hloop (by simp [SameOutcome])
            | ok st' =>
              rw [ha, hb] at hloop
              obtain ⟨hf, _, hch, hco⟩ := hloop
              simp only [hf, hch]
              split
              · simp [SameOutcome]
              · exact SameOutcome.ite (SameOutcome.ite (SameOutcome.ok ⟨rfl, hco⟩))

/--
`validateBlock` with the hash of the genesis block as the parameter `g`.
`validateBlock` is this function at `genesisHash? .mainnet` (`validateBlock_eq_at`).

The definition exists for the proofs of this module alone.
A proof that unfolds `validateBlock` makes the kernel compare its body with a term.
The kernel then evaluates the first test of the body, and with it the hash of the genesis block from its hexadecimal string, which takes minutes.
With the hash as a variable, that evaluation stops at once.
The body applies the matchers of `validateBlock` by name, so that the two bodies are equal term by term and the kernel compares them without evaluation.
-/
def validateBlockAt (g : Option Hash256) (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool)
    (ctx : ValidateContext) (s : CoinSet) (b : Block) : Except ValidateError ConnectResult :=
  have genesis := some b.header.pure.getHash == g
  validateBlock.match_9 (fun _ => Except ValidateError ConnectResult)
    (if genesis || !fCheckPOW then .ok () else checkBlockHeader .mainnet b.header)
    (fun e => .error (.header e)) fun _ =>
    validateBlock.match_7 (fun _ => Except ValidateError ConnectResult)
      (if genesis then .ok () else
        contextualCheckBlockHeader .mainnet b.header.pure ctx.view ctx.adjustedTime ctx.lastCheckpointHeight)
      (fun e => .error (.contextualHeader e)) fun _ =>
      validateBlock.match_5 (fun _ => Except ValidateError ConnectResult)
        (checkBlock .mainnet fCheckPOW fCheckMerkleRoot b)
        (fun e => .error (.checkBlock e)) fun _ =>
        validateBlock.match_3 (fun _ => Except ValidateError ConnectResult)
          (contextualCheckBlockBody ctx.height ctx.prevMedianTimePast ctx.csvActive ctx.segwitActive b)
          (fun e => .error (.contextualBody e)) fun _ =>
          validateBlock.match_1 (fun _ => Except ValidateError ConnectResult)
            (connectBlock verify true
              ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ s b)
            (fun e => .error (.connect e)) fun result => .ok result

/-- `validateBlock` is `validateBlockAt` at the hash of the mainnet genesis block. -/
theorem validateBlock_eq_at : @validateBlock = @validateBlockAt (genesisHash? .mainnet) := Eq.refl _

/-- An accepted `validateBlockAt` is an accepted `connectBlock` on the same coin set, with the same result. -/
theorem validateBlockAt_ok_connect {g : Option Hash256} {verify : SignatureVerifier}
    {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockAt g verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    connectBlock verify true ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ s b = .ok r := by
  unfold validateBlockAt at h
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
          · rename_i result hres
            cases h
            exact hres

/-- An accepted `validateBlock` is an accepted `connectBlock` on the same coin set, with the same result. -/
theorem validateBlock_ok_connect {verify : SignatureVerifier} {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext}
    {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r) :
    connectBlock verify true ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ s b = .ok r := by
  rw [validateBlock_eq_at] at h
  exact validateBlockAt_ok_connect h

/-- `validateBlockAt` has the same outcome on two coin sets with equal entries at the keys of `keep`, when `keep` holds the keys that the block names. -/
theorem validateBlockAt_agree {g : Option Hash256} {verify : SignatureVerifier} {fCheckPOW fCheckMerkleRoot : Bool}
    {ctx : ValidateContext} {keep : Nat → Bool} {s r : CoinSet} {b : Block} (h : CoinSet.AgreeOn keep s r)
    (hn : NamesWithin keep b.transactions) :
    SameOutcome (ConnectResult.AgreeOn keep) (validateBlockAt g verify fCheckPOW fCheckMerkleRoot ctx s b)
      (validateBlockAt g verify fCheckPOW fCheckMerkleRoot ctx r b) := by
  have hconnect := connectBlock_agree (verify := verify) (fJustCheck := true)
    (ctx := ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩) h hn
  unfold validateBlockAt
  simp only
  split
  · simp [SameOutcome]
  · split
    · simp [SameOutcome]
    · split
      · simp [SameOutcome]
      · split
        · simp [SameOutcome]
        · revert hconnect
          cases connectBlock verify true ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ s b <;>
            cases connectBlock verify true ⟨ctx.height, b.header.pure.hashPrevBlock, ctx.bip34Ancestor, ctx.csvActive⟩ r b <;>
            simp [SameOutcome]

/--
`validateBlock` has the same outcome on two coin sets with equal entries at the keys of `keep`.

Suppose that `keep` holds for the key of every transaction ID that the block `b` names (`NamesWithin`).
Suppose that the coin sets `s` and `r` have equal entries at every key of `keep`.
Then `validateBlock` returns the same error on both sets, or it accepts the block on both.
When it accepts, the two results have the same coin changes, and the two new sets again have equal entries at every key of `keep`.

The theorem holds for every verifier, both flags and every context.
The conclusion repeats the hypothesis on the coin sets, so the theorem applies again to the next block, when `keep` also holds the keys of that block.
-/
@[theorem_tag property]
theorem validateBlock_agree (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (keep : Nat → Bool) (s r : CoinSet) (b : Block) (h : CoinSet.AgreeOn keep s r)
    (hn : NamesWithin keep b.transactions) :
    SameOutcome (ConnectResult.AgreeOn keep) (validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b)
      (validateBlock verify fCheckPOW fCheckMerkleRoot ctx r b) := by
  rw [validateBlock_eq_at]
  exact validateBlockAt_agree h hn

/--
An accepted block changes no entry of the coin set at a key that the block does not name.

Suppose that `validateBlock` accepts the block `b` on the coin set `s`, with the result `r`.
Suppose that `k` is not the key of the ID of a transaction of `b`, and not the key of the ID in the outpoint of an input of `b` (`NotNamed`).
Then the new set has at `k` the entry that `s` has at `k`, or no entry when `s` has none.
-/
@[theorem_tag property]
theorem validateBlock_frame (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (s : CoinSet) (b : Block) (r : ConnectResult)
    (h : validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b = .ok r) (k : Nat) (hk : NotNamed k b.transactions) :
    r.coins.entries[k]? = s.entries[k]? := by
  have hc := validateBlock_ok_connect h
  by_cases hg : some b.header.pure.getHash = genesisHash? .mainnet
  · rw [connectBlock_genesis hc hg]
  · rw [connectBlock_ok_coins hc hg]
    unfold coinsBefore
    rw [List.take_length]
    exact foldl_applyTransaction_entries_of_ne _ k _ s hk

/--
`validateBlock` on a coin set and on its restriction to the transaction IDs that the block names (design record 0011, section 3.3 and decision 2).

Suppose that `keep` holds for the key of every transaction ID that the block `b` names (`NamesWithin`): the ID of each transaction, and the ID in the outpoint of each input.
`s.restrict keep` has the entries of `s` whose key satisfies `keep`.
Then `validateBlock` returns the same error on `s` and on `s.restrict keep`, or it accepts the block on both.
When it accepts, with the result `r` on `s` and the result `r'` on the restriction:

1. The two results have the same coin changes.
2. The new sets have equal entries at every key that satisfies `keep`.
3. The new set of the restriction has no entry at a key that does not satisfy `keep`.
4. The new set of `s` has the entries of `s` at every key that does not satisfy `keep`.

So the new set of `s` is determined by `r'.coins` at the keys of `keep` and by `s` at the other keys.
The theorem holds for every verifier, both flags and every context, and it has no hypothesis on `s`.
The module documentation says why the statement is about keys.
-/
@[theorem_tag property]
theorem validateBlock_restrict (verify : SignatureVerifier) (fCheckPOW fCheckMerkleRoot : Bool) (ctx : ValidateContext)
    (keep : Nat → Bool) (s : CoinSet) (b : Block) (hn : NamesWithin keep b.transactions) :
    match validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b,
      validateBlock verify fCheckPOW fCheckMerkleRoot ctx (s.restrict keep) b with
    | .error e, .error e' => e = e'
    | .ok r, .ok r' =>
      r'.changes = r.changes ∧
        (∀ k, keep k = true → r'.coins.entries[k]? = r.coins.entries[k]?) ∧
        (∀ k, keep k = false → r'.coins.entries[k]? = none) ∧
        (∀ k, keep k = false → r.coins.entries[k]? = s.entries[k]?)
    | _, _ => False := by
  have hagree := validateBlock_agree verify fCheckPOW fCheckMerkleRoot ctx keep s (s.restrict keep) b
    (s.agreeOn_restrict keep) hn
  have hnot : ∀ k, keep k = false → NotNamed k b.transactions := by
    intro k hk tx ht
    refine ⟨fun heq => ?_, fun input hi heq => ?_⟩
    · rw [heq, (hn tx ht).1] at hk; cases hk
    · rw [heq, (hn tx ht).2 input hi] at hk; cases hk
  cases ha : validateBlock verify fCheckPOW fCheckMerkleRoot ctx s b with
  | error e =>
    cases hb : validateBlock verify fCheckPOW fCheckMerkleRoot ctx (s.restrict keep) b with
    | error e' => rw [ha, hb] at hagree; simpa [SameOutcome] using hagree
    | ok r' => rw [ha, hb] at hagree; exact absurd hagree (by simp [SameOutcome])
  | ok r =>
    cases hb : validateBlock verify fCheckPOW fCheckMerkleRoot ctx (s.restrict keep) b with
    | error e' => rw [ha, hb] at hagree; exact absurd hagree (by simp [SameOutcome])
    | ok r' =>
      rw [ha, hb] at hagree
      obtain ⟨hch, hco⟩ := hagree
      refine ⟨hch, hco, fun k hk => ?_, fun k hk => ?_⟩
      · rw [validateBlock_frame verify fCheckPOW fCheckMerkleRoot ctx _ b r' hb k (hnot k hk),
          CoinSet.entries_restrict, hk]; rfl
      · exact validateBlock_frame verify fCheckPOW fCheckMerkleRoot ctx s b r ha k (hnot k hk)

end DogeLib.Block
