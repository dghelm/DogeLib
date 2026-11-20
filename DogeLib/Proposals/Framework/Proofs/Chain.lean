module

public import DogeLib.Proposals.Framework.Proofs.Block

/-!
# Proofs: a list of blocks, and what an accepted block ran

Two additions to the block level of a proposed revision (design record 0012, section 9.1).

## A list of blocks

`connectChainWith` runs `connectBlockWith` on a list of blocks in order, as `connectChain` runs `connectBlock`.
Each entry has its own revision, value of `active` and context, so a revision can read a view that differs from block to block.

- `connectChainWith_restricts`: the target of design record 0012, section 9.1. If each entry meets conditions 1 and 2 of section 6.4, a list that `connectChainWith` accepts is accepted by `connectChain`, with the same final coin set.

The statement covers connection alone. `connectChain` runs no body check, so it has no part for a lock-time cutoff.
It is block-level: it is about a supplied list of blocks and contexts on a supplied coin set, and it is not a claim about the network.

## What an accepted block ran

- `connectTransactionsWith_ok_inv`, `connectBlockWith_ok_inv`: in a block that `connectBlockWith` accepts, each transaction that is not a coinbase found its coins, passed the transaction test and passed the script loop.
- `checkInputScriptsWith_ok_inv`: in a script loop that accepts, the spend check accepted each input.

A coin of a transaction is the coin of its outpoint in the set just before the transaction (`coinsBefore`).
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Block DogeLib.Transaction DogeLib.Script DogeLib.Work

variable {ε υ ρ μ : Type}

/-! ## What an accepted block ran -/

/-- If `checkInputScriptWith` accepts an input, the input has a context, and the spend check accepts it under the flags. -/
theorem checkInputScriptWith_ok_inv {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ} {flags : UInt32}
    {txIndex : Nat} {tx : Transaction} {input : Nat} {coin : Coin}
    (h : checkInputScriptWith E spend flags txIndex tx input coin = .ok ()) :
    ∃ ictx, inputContext? tx input = some ictx ∧ spend ictx coin.out.scriptPubKey flags = .accepted := by
  unfold checkInputScriptWith at h
  cases hic : inputContext? tx input with
  | none => simp [hic, ConnectEmbedding.ofError_ne_ok] at h
  | some ctx =>
    simp only [hic] at h
    refine ⟨ctx, rfl, ?_⟩
    cases hs : spend ctx coin.out.scriptPubKey flags with
    | accepted => rfl
    | unsupported u => simp [hs] at h
    | rejected e =>
      simp only [hs] at h
      split at h
      · split at h <;> cases h
      · cases h

/-- If the script loop from input `input` accepts, the spend check accepted the input at each position `input + j`, with the coin at position `j`. -/
theorem checkInputScriptsWith_ok_inv {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ} {flags : UInt32}
    {txIndex : Nat} {tx : Transaction} :
    ∀ {coins : List Coin} {input : Nat}, checkInputScriptsWith E spend flags txIndex tx input coins = .ok () →
      ∀ j coin, coins[j]? = some coin →
        ∃ ictx, inputContext? tx (input + j) = some ictx ∧ spend ictx coin.out.scriptPubKey flags = .accepted
  | [], _, _, j, coin, hj => by simp at hj
  | c :: rest, input, h, j, coin, hj => by
    unfold checkInputScriptsWith at h
    cases h1 : checkInputScriptWith E spend flags txIndex tx input c with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok u =>
      simp only [h1] at h
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        exact checkInputScriptWith_ok_inv h1
      | succ k =>
        simp only [List.getElem?_cons_succ] at hj
        obtain ⟨ictx, hic, hacc⟩ := checkInputScriptsWith_ok_inv h k coin hj
        exact ⟨ictx, by rw [← hic]; congr 1; omega, hacc⟩

/--
If `connectTransactionWith` accepts a transaction that is not a coinbase, `lookupInputs` found its coins in the set before it, the transaction test accepted it with those coins, and the script loop accepted it.
-/
theorem connectTransactionWith_ok_inv {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ} {test : TxTest ρ μ}
    {ctx : ConnectContext} {flags : UInt32} {index : Nat} {st st' : ConnectState} {tx : Transaction}
    (h : connectTransactionWith E spend test ctx flags index st tx = .ok st') (hcb : tx.isCoinBase = false) :
    ∃ coins, lookupInputs st.coins tx.inputs.val = some coins ∧ test index tx coins = .ok () ∧
      checkInputScriptsWith E spend flags index tx 0 coins = .ok () := by
  unfold connectTransactionWith connectFoundWith at h
  simp only [hcb, Bool.false_eq_true, ↓reduceIte] at h
  cases hl : lookupInputs st.coins tx.inputs.val with
  | none =>
    simp only [hl] at h
    exact absurd h (E.ofError_ne_ok _ _)
  | some coins =>
    simp only [hl] at h
    refine ⟨coins, rfl, ?_⟩
    cases h0 : test index tx coins with
    | rejected e => simp [h0] at h
    | unsupported u => simp [h0] at h
    | ok u0 =>
      simp only [h0] at h
      refine ⟨rfl, ?_⟩
      obtain ⟨_, h⟩ := ConnectEmbedding.ite_ofError_ok h
      cases hf : addFee st.fees coins tx.valueOut with
      | none =>
        simp only [hf] at h
        exact absurd h (E.ofError_ne_ok _ _)
      | some fees =>
        simp only [hf] at h
        cases h1 : checkInputsWith E spend ctx.height flags index tx coins with
        | rejected e => simp [h1] at h
        | unsupported u => simp [h1] at h
        | ok u =>
          unfold checkInputsWith at h1
          cases hc : checkTxInputs ctx.height coins tx.valueOut with
          | error e =>
            simp only [hc] at h1
            split at h1 <;> first | exact absurd h1 (E.ofError_ne_ok _ _) | simp_all
          | ok u2 =>
            simpa only [hc] using h1

/--
If the transaction loop accepts a list, each transaction of the list that is not a coinbase found its coins in the set just before it (`coinsBefore`), passed the transaction test with those coins, and passed the script loop.
-/
theorem connectTransactionsWith_ok_inv {E : ConnectEmbedding ε υ ρ μ} {spend : SpendCheck ε υ} {test : TxTest ρ μ}
    {ctx : ConnectContext} {flags : UInt32} :
    ∀ {txs : List Transaction} {index : Nat} {st st' : ConnectState},
      connectTransactionsWith E spend test ctx flags index st txs = .ok st' →
      ∀ i tx, txs[i]? = some tx → tx.isCoinBase = false →
        ∃ coins, lookupInputs (coinsBefore st.coins ctx.height txs i) tx.inputs.val = some coins ∧
          test (index + i) tx coins = .ok () ∧ checkInputScriptsWith E spend flags (index + i) tx 0 coins = .ok ()
  | [], _, _, _, _, i, tx, hi, _ => by simp at hi
  | t :: rest, index, st, st', h, i, tx, hi, hcb => by
    unfold connectTransactionsWith at h
    cases h1 : connectTransactionWith E spend test ctx flags index st t with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok st1 =>
      simp only [h1] at h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        simpa [coinsBefore] using connectTransactionWith_ok_inv h1 hcb
      | succ k =>
        simp only [List.getElem?_cons_succ] at hi
        obtain ⟨coins, hl, ht, hs⟩ := connectTransactionsWith_ok_inv h k tx hi hcb
        have hidx : index + 1 + k = index + (k + 1) := by omega
        rw [hidx] at ht hs
        exact ⟨coins, by simpa [coinsBefore, connectTransactionWith_ok_coins h1] using hl, ht, hs⟩

/--
Take a block that `connectBlockWith` accepts, whose header does not have the hash of the mainnet genesis block.
Then each transaction of the block that is not a coinbase found its coins in the set just before it (`coinsBefore`).
The transaction test of the revision accepted it with those coins, and the script loop accepted it with the spend check and the script flags of the revision.
-/
theorem connectBlockWith_ok_inv {E : ConnectEmbedding ε υ ρ μ} {rev : BlockRevision ε υ ρ μ} {active fJustCheck : Bool}
    {ctx : ConnectContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : connectBlockWith E rev active fJustCheck ctx s b = .ok r)
    (hg : (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = false) :
    ∀ i tx, b.transactions[i]? = some tx → tx.isCoinBase = false →
      ∃ coins, lookupInputs (coinsBefore s ctx.height b.transactions i) tx.inputs.val = some coins ∧
        rev.txTest active ctx.height i tx coins = .ok () ∧
          checkInputScriptsWith E (rev.spend active) (rev.scriptFlags active ctx.height) i tx 0 coins = .ok () := by
  unfold connectBlockWith at h
  cases hcb : checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | error e =>
    simp only [hcb] at h
    exact absurd h (E.ofError_ne_ok _ _)
  | ok u =>
    simp only [hcb, hg, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨_, h⟩ := ConnectEmbedding.ite_ofError_ok h
    obtain ⟨_, h⟩ := ConnectEmbedding.ite_ofError_ok h
    cases h1 : connectTransactionsWith E (rev.spend active) (rev.txTest active ctx.height) ctx
        (rev.scriptFlags active ctx.height) 0 ⟨s, 0, 0, []⟩ b.transactions with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok st =>
      intro i tx hi hcbtx
      simpa using connectTransactionsWith_ok_inv h1 i tx hi hcbtx

/-! ## A list of blocks -/

/--
`connectBlockWith` on a list of blocks in order, from the coin set `s`, as `connectChain` runs `connectBlock`.
Each entry holds the revision, the value of `active`, the context and the block.
The result is the set after the last block, or the first rejection or result outside the model.
The set after each block is the set before the next one.
-/
def connectChainWith (E : ConnectEmbedding ε υ ρ μ) (fJustCheck : Bool) (s : CoinSet) :
    List (BlockRevision ε υ ρ μ × Bool × ConnectContext × Block) → BlockOutcome ρ μ CoinSet
  | [] => .ok s
  | (rev, active, ctx, b) :: rest =>
    match connectBlockWith E rev active fJustCheck ctx s b with
    | .rejected e => .rejected e
    | .unsupported u => .unsupported u
    | .ok r => connectChainWith E fJustCheck r.coins rest

/--
The target `connectChainWith_restricts` of design record 0012, section 9.1. Block-level, for connection alone.
Take a list of blocks, each with its revision, its value of `active` and its context.
Let each entry meet conditions 1 and 2 of design record 0012, section 6.4, at the height of its context:

1. If the spend check of the revision accepts an input under the script flags of the revision, `verifyLegacySpend` accepts it under `connectScriptFlags`.
2. The script flags of the revision and `connectScriptFlags` agree on `SCRIPT_VERIFY_P2SH`.

The baseline has no transaction test, so every transaction test meets condition 3.
If `connectChainWith` accepts the list from a coin set, `connectChain` accepts the blocks with their contexts from that set, to the same final set.
For every embedding, verifier, flag `fJustCheck` and coin set.

The statement needs no hypothesis on `csvActive` of a context: with that field true, `connectBlockWith` accepts no block that reaches the test of the field, and neither does `connectBlock`.
`connectChain` runs no body check, so the statement has no part for a lock-time cutoff.
-/
theorem connectChainWith_restricts {E : ConnectEmbedding ε υ ρ μ} {verify : SignatureVerifier} {fJustCheck : Bool} :
    ∀ {l : List (BlockRevision ε υ ρ μ × Bool × ConnectContext × Block)} {s final : CoinSet},
      (∀ entry ∈ l,
        (∀ ictx spk, entry.1.spend entry.2.1 ictx spk (entry.1.scriptFlags entry.2.1 entry.2.2.1.height) = .accepted →
          verifyLegacySpend ictx spk (connectScriptFlags entry.2.2.1.height) verify = .accepted) ∧
        hasFlag (entry.1.scriptFlags entry.2.1 entry.2.2.1.height) ScriptFlags.p2sh =
          hasFlag (connectScriptFlags entry.2.2.1.height) ScriptFlags.p2sh) →
      connectChainWith E fJustCheck s l = .ok final →
        connectChain verify fJustCheck s (l.map fun entry => (entry.2.2.1, entry.2.2.2)) = .ok final
  | [], s, final, _, h => by
    simp only [connectChainWith, BlockOutcome.ok.injEq] at h
    subst h
    rfl
  | (rev, active, ctx, b) :: rest, s, final, hall, h => by
    unfold connectChainWith at h
    cases h1 : connectBlockWith E rev active fJustCheck ctx s b with
    | rejected e => simp [h1] at h
    | unsupported u => simp [h1] at h
    | ok r =>
      simp only [h1] at h
      obtain ⟨hspend, hp2sh⟩ := hall (rev, active, ctx, b) (List.Mem.head _)
      have hb := connectBlockWith_restricts (verify := verify) hspend hp2sh h1
      simp only [List.map_cons, connectChain, hb]
      exact connectChainWith_restricts (fun entry hmem => hall entry (List.mem_cons_of_mem _ hmem)) h

end DogeLib.Proposals.Framework
