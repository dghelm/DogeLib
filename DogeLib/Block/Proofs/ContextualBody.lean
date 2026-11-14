module

public import DogeLib.Block.ContextualBody
public import DogeLib.Block.Proofs.VersionBits
import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the body of `ContextualCheckBlock`

The arguments of design record 0010, section 4, exit condition 3, for the reject reasons that `block.validate` cannot reach:

- `segwit_never_active`: on a valid mainnet chain the SegWit state is never `ACTIVE`, a corollary of `csv_never_lockedIn` for the SegWit deployment.
  Core guards `bad-witness-nonce-size` and `bad-witness-merkle-match` with an active SegWit state (D110, lines 3161 to 3181), so neither reason is reachable on mainnet.
  This module's body returns the adapter error `segwitActive` on an active SegWit state and never those two reasons.
- `contextualBody_badBlkWeight_unreachable_after_checkBlock`: after `CheckBlock` accepts a block, the body's weight check cannot fire, so `block.validate` does not reach `bad-blk-weight`.

The weight argument holds under the hypothesis that the AuxPoW payload transaction has no witness data.
That hypothesis excludes some real mainnet blocks: pull request #152 found that the AuxPoW parent coinbase of blocks 6,455,642, 6,456,071 and 6,456,247 carries witness data that Core accepts.
The theorem does not cover a block whose AuxPoW payload transaction has witness data.
-/

public section
namespace DogeLib.Block
open DogeLib.Transaction

/-- The AuxPoW payload transaction of a block, if present, has no witness data. -/
def Block.payloadNoWitness (b : Block) : Prop :=
  ∀ a, b.header.auxpow = some a → a.tx.hasWitness = false

/-- A transaction with no witness data writes the same bytes in both modes. -/
theorem encodeTx_eq_of_noWitness (w : WitnessTransaction) (h : w.hasWitness = false) :
    encodeTx .allowWitness w = encodeTx .base w := by
  simp [encodeTx, WitnessTransaction.encode, h]

/-- A list of transactions with no witness data writes the same bytes in both modes. -/
theorem flatMap_encodeTx_eq (l : List WitnessTransaction) (h : ∀ w ∈ l, w.hasWitness = false) :
    l.flatMap (encodeTx .allowWitness) = l.flatMap (encodeTx .base) := by
  induction l with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons]
    rw [encodeTx_eq_of_noWitness w (h w (List.mem_cons_self ..)),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- A full header whose payload transaction has no witness data writes the same bytes in both modes. -/
theorem blockHeader_encode_eq_of_noWitness (h : BlockHeader)
    (hp : ∀ a, h.auxpow = some a → a.tx.hasWitness = false) :
    BlockHeader.encode .allowWitness h = BlockHeader.encode .base h := by
  simp only [BlockHeader.encode]
  cases ha : h.auxpow with
  | none => simp
  | some a =>
    cases hx : h.pure.isAuxpow with
    | false => simp
    | true =>
      simp only [Option.map_some, Option.getD_some, AuxPow.encode, reduceIte]
      rw [encodeTx_eq_of_noWitness a.tx (hp a ha)]

/-- A block with no witness data anywhere writes the same bytes in both modes. -/
theorem block_encode_eq_of_noWitness (b : Block) (hv : ∀ w ∈ b.vtx.val, w.hasWitness = false)
    (hp : b.payloadNoWitness) : Block.encode .allowWitness b = Block.encode .base b := by
  unfold Block.encode
  rw [blockHeader_encode_eq_of_noWitness b.header hp, flatMap_encodeTx_eq b.vtx.val hv]

/-- A block with no witness data has weight four times its base size. -/
theorem weight_eq_of_noWitness (b : Block) (hv : ∀ w ∈ b.vtx.val, w.hasWitness = false)
    (hp : b.payloadNoWitness) : Block.weight b = 4 * Block.baseSize b := by
  unfold Block.weight Block.fullSize Block.baseSize
  rw [block_encode_eq_of_noWitness b hv hp]
  omega

/-- `CheckBlock` accepts only a block whose base size is at most `MAX_BLOCK_BASE_SIZE` (D106, line 2972). -/
theorem checkBlock_baseSize_le (network : Work.WorkNetwork) (pow merkle : Bool) (b : Block)
    (h : checkBlock network pow merkle b = .ok ()) : b.baseSize ≤ maxBlockBaseSize := by
  simp only [checkBlock] at h
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  split at h
  · exact absurd h (by simp)
  rename_i hlen
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hlen
  omega

/-- `checkFinality` never rejects with `bad-blk-weight`. -/
theorem checkFinality_ne_badBlk (height : Nat) (cutoff : Int) (txs : List Transaction) :
    checkFinality height cutoff txs ≠ .error .badBlkWeight := by
  induction txs with
  | nil => simp [checkFinality]
  | cons tx rest ih =>
    simp only [checkFinality]
    split
    · exact ih
    · simp

/--
After `CheckBlock` accepts a block, the body of `ContextualCheckBlock` cannot reject it with `bad-blk-weight`, under the hypothesis that the AuxPoW payload transaction has no witness data.
So `block.validate`, which runs `CheckBlock` before the body, does not reach `bad-blk-weight`.

The theorem does not cover a block whose AuxPoW payload transaction has witness data.
-/
@[theorem_tag property]
theorem contextualBody_badBlkWeight_unreachable_after_checkBlock (network : Work.WorkNetwork)
    (pow merkle : Bool) (b : Block) (hcb : checkBlock network pow merkle b = .ok ())
    (hp : b.payloadNoWitness) (height : Nat) (prevMtp : Int) (csvActive segwitActive : Bool) :
    contextualCheckBlockBody height prevMtp csvActive segwitActive b ≠ .error .badBlkWeight := by
  intro hbad
  have hbase := checkBlock_baseSize_le network pow merkle b hcb
  simp only [contextualCheckBlockBody] at hbad
  split at hbad
  · -- Finality rejected with nonFinal, never badBlkWeight.
    rename_i e heq
    have : e = ContextualBodyError.badBlkWeight := by injection hbad
    exact checkFinality_ne_badBlk height _ b.transactions (this ▸ heq)
  -- Coinbase present.
  split at hbad
  · exact absurd hbad (by simp)
  split at hbad
  · exact absurd hbad (by simp)
  -- The BIP34 check.
  split at hbad
  · exact absurd hbad (by simp)
  -- The SegWit check.
  split at hbad
  · exact absurd hbad (by simp)
  -- The witness check: its else branch has no witness in any transaction.
  split at hbad
  · exact absurd hbad (by simp)
  -- The weight check: the weight is bounded, so this branch cannot have fired.
  rename_i hnw
  rw [Bool.not_eq_true] at hnw
  have hv : ∀ w ∈ b.vtx.val, w.hasWitness = false := by
    simp only [WitnessTransaction.anyWitness, List.any_eq_false] at hnw
    intro w hw; simpa using hnw w hw
  have hle : Block.weight b ≤ maxBlockWeight := by
    rw [weight_eq_of_noWitness b hv hp]
    simp only [maxBlockWeight, maxBlockBaseSize] at *; omega
  rw [ite_eq_right (by omega)] at hbad
  exact absurd hbad (by simp)

/--
On a header chain from the mainnet genesis in which every header passed `checkBlockHeader`, the SegWit state is never `ACTIVE`.
Core guards the witness-commitment checks with an active SegWit state, so `bad-witness-nonce-size` and `bad-witness-merkle-match` are unreachable on mainnet.
-/
@[theorem_tag property]
theorem segwit_never_active (chain : List BlockHeader)
    (hpass : ∀ bh ∈ chain, checkBlockHeader .mainnet bh = .ok ()) :
    versionBitsStateFull segwitDeployment ruleChangeActivationThreshold
      (chain.map (fun bh => (⟨bh.pure.nVersion, bh.pure.nTime⟩ : VbEntry))) ≠ .active :=
  (csv_never_lockedIn chain hpass segwitDeployment).ne_active

end DogeLib.Block
