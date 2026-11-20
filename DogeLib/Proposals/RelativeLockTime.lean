module

public import DogeLib.Proposals.Framework.Block
public import DogeLib.Work.MedianTimePast

/-!
# `Proposals.RelativeLockTime`

A proposed revision of the Dogecoin block rules: the three rules that Bitcoin deployed together under the name CSV.
Design record 0012 sets the contract.

| Rule | Document | Content |
| --- | --- | --- |
| BIP 113 | SOURCES.md, P3 | The lock-time test of a block compares with the median time past of its predecessor. |
| BIP 112 | SOURCES.md, P2 | The opcode `OP_CHECKSEQUENCEVERIFY` replaces `OP_NOP3`. |
| BIP 68 | SOURCES.md, P1 | The sequence of an input can state a relative lock time. |

Discussion 3509 of `dogecoin/dogecoin` proposed their activation for Dogecoin (SOURCES.md, P4).
The baseline is the specification of Dogecoin Core at the pin in SOURCES.md, where the version-bits deployment of these rules cannot activate on mainnet (`csv_never_lockedIn`).
DogeLib is a specification library. This module does not argue for or against the activation of the rules.

## Coverage of this module

**The revision is partial. It has the rule of BIP 113 alone.**
The rules of BIP 112 and BIP 68 are stages 2 and 3 of design record 0012, and this module does not state them.
With `active` true, the script flags and the transaction test of `blockRevision` are still those of the baseline.
So a result of this module is not the result of the three rules together.

## The rule of BIP 113

Core's `ContextualCheckBlock` selects the lock-time cutoff of `IsFinalTx` (SOURCES.md, D110, lines 3127 to 3140).
Without an active CSV state the cutoff is the time of the block.
With an active state it is the median time past of the predecessor.

The baseline `contextualCheckBlockBody` has both branches, and takes the state and the median as arguments.
The revision defines no second copy of the check. Through extension E3 of the block layer, `lockTimeArgs` passes `csvActive` true and the median time past of the view (design record 0012, decision 9).
The median is `Work.medianTimePast` of the view of the context: the view that `contextualCheckBlockHeader` reads, and not the separate field `prevMedianTimePast`.

## Where the rule applies

A block is *applicable* under two conditions (design record 0012, section 5).
Its view of the predecessor is not empty.
The hash of its own header is not the hash of the mainnet genesis block.
The revised rule applies only when `active` is true and the block is applicable.
For every other block, `lockTimeArgs` gives the arguments of the baseline.

`validateBlock` runs no header check on a header with the genesis hash.
So no check gives the order between the median time past and the time of the block, which the restriction theorem needs.

## A view without a median

`Work.medianTimePast` returns an adapter error for a view that is invalid or too short.
`lockTimeArgs` then gives the arguments of the baseline.
`validateBlockWithActive` never reads that case: `contextualCheckBlockHeader` computes the same median first, and returns the adapter error (`lockTimeArgs_of_headerPassed` in `Proofs.Cutoff`).
A caller that runs `contextualBodyWith` alone must check the median itself.

## Differences from the BIPs

Where a BIP and the pinned code differ, the definition follows the code (design record 0012, section 2.3):

- BIP 113 states a version-bits deployment with Bitcoin's parameters. The revision has an activation height, through `Activation`.
- BIP 68 chose its time unit of 512 seconds for a block interval of 600 seconds. The pinned code keeps that unit. This item concerns stage 3.

## Labels

The theorems of `DogeLib.Proposals.RelativeLockTime.Proofs` are rule-level or block-level.
A block-level theorem is about `validateBlock` for one block on a supplied coin set and view.
It is not a claim about a chain or about the network, and it says nothing about fork choice, convergence or liveness.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Work DogeLib.Proposals.Framework

/--
Whether the revised rules apply to the block `b` in the context `ctx` (design record 0012, section 5).
The view of the predecessor is not empty, and the hash of the header is not the hash of the mainnet genesis block.
-/
def applicable (ctx : ValidateContext) (b : Block) : Bool :=
  !ctx.view.isEmpty && !(some b.header.pure.getHash == genesisHash? .mainnet)

/--
The lock-time arguments of `contextualCheckBlockBody` under the revision (extension E3).
With `active` true on an applicable block: `csvActive` true, and the median time past of the view.
Otherwise the arguments of the baseline. A view without a median also gives the arguments of the baseline, and the module documentation says why no block-level result reads that case.
-/
def lockTimeArgs (active : Bool) (ctx : ValidateContext) (b : Block) : Bool × Int :=
  if active && applicable ctx b then
    match medianTimePast ctx.view with
    | .ok median => (true, median)
    | .error _ => baselineLockTimeArgs ctx
  else baselineLockTimeArgs ctx

/--
The revision at the block level, with the verifier `verify`.
Its lock-time arguments are `lockTimeArgs`.
Its spend check, its script flags and its transaction test are those of the baseline: the revision is partial, and has the rule of BIP 113 alone.
-/
def blockRevision {ρ μ : Type} (verify : SignatureVerifier) : BlockRevision ScriptError Unsupported ρ μ where
  spend := fun _ => baselineSpendCheck id id verify
  lockTimeArgs := lockTimeArgs

/--
The context of one block-level check: the verifier, the two flags of `CheckBlock`, the view and the times, the coin set after the predecessor and the block.
-/
structure BlockArgs where
  /-- The elliptic-curve check. -/
  verify : SignatureVerifier
  /-- `fCheckPOW` of `CheckBlock`. -/
  fCheckPOW : Bool
  /-- `fCheckMerkleRoot` of `CheckBlock`. -/
  fCheckMerkleRoot : Bool
  /-- The view, the times and the version-bits states. -/
  ctx : ValidateContext
  /-- The coin set after the predecessor. -/
  coins : CoinSet
  /-- The block. -/
  block : Block

/-- The baseline: `validateBlock` on the arguments. -/
def baselineValidate (a : BlockArgs) : Except ValidateError ConnectResult :=
  validateBlock a.verify a.fCheckPOW a.fCheckMerkleRoot a.ctx a.coins a.block

/--
The revision: `validateBlockWithActive` with `blockRevision`, for the value `active`, with the baseline error types.
A rejection and an unsupported result both hold a `ValidateError`.
-/
def revisedValidate (active : Bool) (a : BlockArgs) : BlockOutcome ValidateError ValidateError ConnectResult :=
  validateBlockWithActive ValidateEmbedding.baseline ConnectEmbedding.baseline (blockRevision a.verify) active
    a.fCheckPOW a.fCheckMerkleRoot a.ctx a.coins a.block

/--
The rule of BIP 113 runs on the block.
The block is applicable, and one of its transactions has a time lock time and an input whose sequence is not `SEQUENCE_FINAL`.
For such a transaction, `isFinalTx` compares the lock time with the cutoff.
-/
def RunsCutoff (a : BlockArgs) : Prop :=
  applicable a.ctx a.block = true ∧
    ∃ tx ∈ a.block.transactions, Block.lockTimeThreshold ≤ tx.lockTime.toNat ∧
      tx.inputs.val.all (fun i => i.sequence == contextualSequenceFinal) = false

end DogeLib.Proposals.RelativeLockTime
