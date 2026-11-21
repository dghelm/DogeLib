module

public import DogeLib.Proposals.RelativeLockTime.SequenceLocks

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

The revision has the three rules.
`blockRevision` sets the lock-time arguments (BIP 113), the script flags (BIP 112) and the transaction test (BIP 68) of the block layer.

## The rule of BIP 113

Core's `ContextualCheckBlock` selects the lock-time cutoff of `IsFinalTx` (SOURCES.md, D110, lines 3127 to 3140).
Without an active CSV state the cutoff is the time of the block.
With an active state it is the median time past of the predecessor.

The baseline `contextualCheckBlockBody` has both branches, and takes the state and the median as arguments.
The revision defines no second copy of the check. Through extension E3 of the block layer, `lockTimeArgs` passes `csvActive` true and the median time past of the view (design record 0012, decision 9).
The median is `Work.medianTimePast` of the view of the context: the view that `contextualCheckBlockHeader` reads, and not the separate field `prevMedianTimePast`.

## The rule of BIP 112

Core's `ConnectBlock` adds `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` to the script flags of a block exactly when the CSV state is active (SOURCES.md, D114, lines 1906 to 1911).
With the flag, opcode `0xb2` is `OP_CHECKSEQUENCEVERIFY`. Without it, the opcode is `OP_NOP3` (SOURCES.md, D3, lines 392 to 427).

The baseline `Script.execOpcode` has both branches, and `Script.checkSequenceStep` and `Script.sequenceSatisfied` state the opcode.
The revision defines no second copy of the opcode. Through extension E1 of the block layer, `scriptFlags` adds the flag to `connectScriptFlags` when `active` is true.
The spend check of the revision is the baseline `verifyLegacySpend`.

The flag is in `standardNotMandatoryVerifyFlags`.
So the second script check of `checkInputScriptWith` runs without it, and a spend that fails through the opcode alone gets the class of Core's `non-mandatory-script-verify-flag` (SOURCES.md, D101, lines 1488 to 1512).

`ConnectBlock` at the pin sets neither `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS` nor `SCRIPT_VERIFY_MINIMALDATA`, so the opcode has the consensus form of design record 0012, section 3.2.

## The rule of BIP 68

Core's `ConnectBlock` runs `SequenceLocks` on each transaction that is not a coinbase, with `LOCKTIME_VERIFY_SEQUENCE` exactly when the CSV state is active (SOURCES.md, D114, lines 1906 to 1911 and 1948 to 1959).
The baseline has no definition of that test, because the state is never active on mainnet.
`DogeLib.Proposals.RelativeLockTime.SequenceLocks` defines it as `sequenceLocks`, and states its three results outside the model.
Through extension E2 of the block layer, `txTest` runs it.

The test reads ancestor times of the view, and the transaction test of the block layer has no view argument.
So `blockRevision` takes the view of the predecessor as an argument, and `revisedValidate` passes the view of its context.
Every theorem that does not read the test holds for every view argument.

## Results

The revision adds one rejection and three results outside the model to those of `ConnectBlock` (extension E4).
The outcome types are sums, with the baseline values under `Sum.inl`:

| Type | Value |
| --- | --- |
| `ConnectRejection` | `ConnectBlockError ⊕ RevisionError` |
| `ConnectReason` | `ConnectBlockError ⊕ Reason` |
| `ValidateRejection` | `ValidateError ⊕ RevisionError` |
| `ValidateReason` | `ValidateError ⊕ Reason` |

`connectEmbedding` and `validateEmbedding` map the baseline results into them.

## Where the rules apply

A block is *applicable* under two conditions (design record 0012, section 5).
Its view of the predecessor is not empty.
The hash of its own header is not the hash of the mainnet genesis block.

`lockTimeArgs` gives the revised arguments only when `active` is true and the block is applicable.
For every other block it gives the arguments of the baseline.
`validateBlock` runs no header check on a header with the genesis hash.
So no check gives the order between the median time past and the time of the block, which the restriction theorem needs.

`scriptFlags` takes `active` and the height, and does not read the block.
`sequenceLocks` accepts on an empty view, and does not read the hash of the block.
`validateBlockWithActive` still gives the embedded result of `validateBlock` on a block that is not applicable (`relativeLockTime_eq_of_not_applicable` in `Proofs.Block`).
`connectBlockWith` connects no transaction of a block with the genesis hash, and the contextual header check fails on an empty view.

## A view without a median

`Work.medianTimePast` returns an adapter error for a view that is invalid or too short.
`lockTimeArgs` then gives the arguments of the baseline.
`validateBlockWithActive` never reads that case: `contextualCheckBlockHeader` computes the same median first, and returns the adapter error (`lockTimeArgs_of_headerPassed` in `Proofs.Block`).
A caller that runs `contextualBodyWith` alone must check the median itself.

## Differences from the BIPs

Where a BIP and the pinned code differ, the definition follows the code (design record 0012, section 2.3):

- BIP 112 and BIP 113 state a version-bits deployment with Bitcoin's parameters. The revision has an activation height, through `Activation`.
- BIP 68 chose its time unit of 512 seconds for a block interval of 600 seconds. The pinned code keeps that unit, and Dogecoin's interval is 60 seconds.
- The BIPs state no result outside the model. `sequenceLocks` has three, for an input that Core's `int` arithmetic or the supplied view does not cover.

## Labels

The theorems of `DogeLib.Proposals.RelativeLockTime.Proofs` are rule-level, Script-local or block-level.
A Script-local theorem is about one input and its scripts.
A block-level theorem is about `validateBlock` or `connectBlock` for one block on a supplied coin set and view, or about a list of blocks through `connectChain`.
It is not a claim about the network, and it says nothing about fork choice, convergence or liveness.
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

/-- Opcode `0xb2`: `OP_NOP3` without the CSV flag, and `OP_CHECKSEQUENCEVERIFY` with it. -/
def csvOpcode : UInt8 := 0xb2

/-- The opcode set of the rule of BIP 112: `0xb2` alone. -/
def isCsvOpcode (op : UInt8) : Bool := op == csvOpcode

/-- The flag set `f` with `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` added. -/
def withCsvFlag (f : UInt32) : UInt32 := f ||| ScriptFlags.checkSequenceVerify

/--
The script flags of a block under the revision (extension E1).
With `active` true: `connectScriptFlags` at the height with `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` added, as Core's `ConnectBlock` sets them with an active CSV state (SOURCES.md, D114, lines 1906 to 1911).
Otherwise `connectScriptFlags` at the height.
-/
def scriptFlags (active : Bool) (height : Nat) : UInt32 :=
  if active then withCsvFlag (connectScriptFlags height) else connectScriptFlags height

/-- The rejections of `connectBlockWith` under the revision: those of `ConnectBlock`, or a failure of the sequence locks. -/
abbrev ConnectRejection : Type := ConnectBlockError ⊕ RevisionError

/-- The results outside the model of `connectBlockWith` under the revision: those of `ConnectBlock`, or a reason of the sequence locks. -/
abbrev ConnectReason : Type := ConnectBlockError ⊕ Reason

/-- The rejections of `validateBlockWithActive` under the revision. -/
abbrev ValidateRejection : Type := ValidateError ⊕ RevisionError

/-- The results outside the model of `validateBlockWithActive` under the revision. -/
abbrev ValidateReason : Type := ValidateError ⊕ Reason

/-- The embedding of the results of `ConnectBlock` into the outcome types of the revision: each baseline value under `Sum.inl`. -/
def connectEmbedding : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason :=
  ⟨.inl, .inl, fun tx input mandatory e => .inl (.script tx input mandatory e), fun u => .inl (.scriptUnsupported u)⟩

/-- The embedding of the results of `validateBlock` into the outcome types of the revision. A result of `connectBlockWith` keeps its side of the sum, and a baseline value goes under `ValidateError.connect`. -/
def validateEmbedding : ValidateEmbedding ConnectRejection ConnectReason ValidateRejection ValidateReason :=
  ⟨.inl, .inl, Sum.map .connect id, Sum.map .connect id⟩

/--
The transaction test of the revision (extension E2): `sequenceLocks` on the view `view`, with its error and its reasons under `Sum.inr`.
-/
def txTest (active : Bool) (view : List BlockIndex) (height : Nat) : TxTest ConnectRejection ConnectReason :=
  fun index tx coins => (sequenceLocks active view height index tx coins).map .inr .inr

/--
The revision at the block level, with the verifier `verify` and the view `view` of the predecessor.
Its lock-time arguments are `lockTimeArgs` (BIP 113), its script flags are `scriptFlags` (BIP 112), and its transaction test is `sequenceLocks` on `view` (BIP 68).
Its spend check is that of the baseline.
`view` is the view that the transaction test reads, and a caller passes the view of the context of the block.
-/
def blockRevision (verify : SignatureVerifier) (view : List BlockIndex) :
    BlockRevision ScriptError Unsupported ConnectRejection ConnectReason where
  spend := fun _ => baselineSpendCheck id id verify
  scriptFlags := scriptFlags
  txTest := fun active height => txTest active view height
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
The revision: `validateBlockWithActive` with `blockRevision` on the view of the context, for the value `active`.
A rejection is a `ValidateError` of the baseline or a `RevisionError`. A result outside the model is a `ValidateError` or a `Reason`.
-/
def revisedValidate (active : Bool) (a : BlockArgs) : BlockOutcome ValidateRejection ValidateReason ConnectResult :=
  validateBlockWithActive validateEmbedding connectEmbedding (blockRevision a.verify a.ctx.view) active
    a.fCheckPOW a.fCheckMerkleRoot a.ctx a.coins a.block

/-- The embedded result of a baseline `validateBlock` call in the outcome types of the revision. -/
def embedBaseline (r : Except ValidateError ConnectResult) : BlockOutcome ValidateRejection ValidateReason ConnectResult :=
  validateEmbedding.ofBaseline connectEmbedding id id r

/--
The rule of BIP 113 runs on the block.
The block is applicable, and one of its transactions has a time lock time and an input whose sequence is not `SEQUENCE_FINAL`.
For such a transaction, `isFinalTx` compares the lock time with the cutoff.
-/
def RunsCutoff (a : BlockArgs) : Prop :=
  applicable a.ctx a.block = true ∧
    ∃ tx ∈ a.block.transactions, Block.lockTimeThreshold ≤ tx.lockTime.toNat ∧
      tx.inputs.val.all (fun i => i.sequence == contextualSequenceFinal) = false

/--
The scripts of the characterization `csv_accepted_iff`: a push of the bytes `b`, then opcode `0xb2`, then the script `S`.
The push opcode is the length of `b`: `OP_0` for the empty list, and a direct push for 1 to 75 bytes.
-/
def operandScript (b S : List UInt8) : List UInt8 := (b.length.toUInt8 :: b) ++ csvOpcode :: S

/--
The rule of BIP 112 runs on the block.
The block is applicable.
A transaction of the block that is not a coinbase has an input that spends a coin of the coin set.
The script of the coin is `operandScript b S` for an operand `b` of at most 5 bytes.
The operand is not negative and has bit 31 clear.
So `OP_CHECKSEQUENCEVERIFY` at the top level of that script compares it with the sequence of the input.
-/
def RunsOpcode (a : BlockArgs) : Prop :=
  applicable a.ctx a.block = true ∧
    ∃ tx ∈ a.block.transactions, tx.isCoinBase = false ∧ ∃ input ∈ tx.inputs.val, ∃ c,
      a.coins.coin input.prevout = some c ∧ ∃ b S, b.length ≤ 5 ∧
        c.out.scriptPubKey.bytes.val = operandScript b S ∧ 0 ≤ ScriptNum.value b ∧
          (ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag = 0

/--
The rule of BIP 68 runs on the block.
The block is applicable.
A transaction of the block that is not a coinbase has a version of at least 2, as an unsigned value.
One of its inputs has a sequence with bits 31 and 22 clear and with low 16 bits of at least 1: a height lock of at least one block.
-/
def RunsSequenceLock (a : BlockArgs) : Prop :=
  applicable a.ctx a.block = true ∧
    ∃ tx ∈ a.block.transactions, tx.isCoinBase = false ∧ 2 ≤ tx.version.toNat ∧ ∃ input ∈ tx.inputs.val,
      input.sequence.toNat &&& sequenceLockTimeDisableFlag = 0 ∧
        input.sequence.toNat &&& sequenceLockTimeTypeFlag = 0 ∧ 1 ≤ input.sequence.toNat &&& sequenceLockTimeMask

end DogeLib.Proposals.RelativeLockTime
