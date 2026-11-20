import DogeLib.Proposals

/-!
## Proposals: the proposed revision `RelativeLockTime`, the lock-time cutoff

`RelativeLockTime` is the revision of design record 0012. It is partial: it has the rules of BIP 113 and BIP 112.
`KnownAnswers.Proposals.RelativeLockTimeOpcode` has the cases of BIP 112.
These cases run `contextualBodyWith`, `validateBlockWithActive` and `validateBlockWith` with the revision through the compiled code.

Each expected result is derived by hand, never computed by DogeLib, from two sources:

- BIP 113 (SOURCES.md, P3): a transaction with a time lock time `T` is final in a block when `T` is below the median time past of the block's predecessor.
- Core's code of the rule at the pin (SOURCES.md, D110): `IsFinalTx` (`src/validation.cpp`, lines 258 to 269) and the cutoff of `ContextualCheckBlock` (lines 3127 to 3140).

The baseline cutoff is the time of the block. A transaction is final when its lock time is 0 or below the cutoff, or when every input has the sequence `SEQUENCE_FINAL`.
The median of n times, for n at most 11, is the sorted time at index n / 2 (D18, `src/chain.h`, lines 286 to 298).

The cases cover the three cutoff boundaries of design record 0012, section 10.1: a lock time equal to the median cutoff, one below it, and equal to the block time.
They run at two levels:

- The body check alone, at height 5,000 on a made view of eleven entries with the times `t0`, `t0 - 60`, ..., `t0 - 600`. The median is `t0 - 300`, and the block time is `t0 + 60`.
- The whole of `validateBlock`, for a made block at height 1 on the mainnet genesis block. The view is the genesis block alone, so the median is its time, 1,386,325,540. The block time is 60 seconds later. The block has no proof of work and a zero Merkle root, so both flags of `CheckBlock` are false.

Other cases show where the rule does not apply: with `active` false, with a final sequence, on a block without a predecessor, and below an activation height.
-/

namespace KnownAnswers.Proposals.RelativeLockTime

open DogeLib DogeLib.Block DogeLib.Work DogeLib.Transaction DogeLib.Script
open DogeLib.Proposals.Framework DogeLib.Proposals.RelativeLockTime

/-- Check a condition and report its label on failure. Returns the number of failures. -/
def require (label : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.eprintln s!"FAIL RelativeLockTime: {label}"
  return 1

/-- A script from its bytes. The scripts of this module are short. -/
def scriptOf (bytes : List UInt8) : Transaction.Script :=
  if h : bytes.length < 2 ^ 64 then ⟨⟨bytes, h⟩⟩ else ⟨⟨[], by decide⟩⟩

/-- A list as a counted list. The lists of this module are short. -/
def counted {α : Type} (l : List α) : Serialization.CountedList α :=
  if h : l.length < 2 ^ 64 then ⟨l, h⟩ else ⟨[], by simp⟩

/-- A coinbase with the `scriptSig` `51 51`, the sequence 0xffffffff, one output of 0 and no lock time. -/
def coinbaseTx : Transaction :=
  { version := 1
    inputs := counted [{ prevout := OutPoint.null, scriptSig := scriptOf [0x51, 0x51], sequence := 0xffffffff }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [] }]
    lockTime := 0 }

/-- A coinbase as `coinbaseTx`, with the sequence `sequence` and the lock time `lockTime`. -/
def lockedCoinbase (lockTime sequence : UInt32) : Transaction :=
  { coinbaseTx with
    inputs := counted [{ prevout := OutPoint.null, scriptSig := scriptOf [0x51, 0x51], sequence }]
    lockTime }

/-- A transaction with one input of the sequence `sequence`, one output of 0 and the lock time `lockTime`. -/
def lockedTx (lockTime sequence : UInt32) : Transaction :=
  { version := 1
    inputs := counted [{ prevout := ⟨Hash256.zero, 0⟩, scriptSig := scriptOf [], sequence }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [] }]
    lockTime }

/-- A transaction of a block, without witness data. -/
def plain (tx : Transaction) : WitnessTransaction :=
  ⟨tx, tx.inputs.val.map fun _ => WitnessStack.empty, by simp⟩

/-- A block with the time `time`, the previous hash `prev`, the `nBits` of the genesis block and the transactions `txs`. -/
def blockOf (prev : Hash256) (time : UInt32) (txs : List Transaction) : Block :=
  { header := ⟨⟨1, prev, Hash256.zero, time, 0x1e0ffff0, 0⟩, none⟩, vtx := counted (txs.map plain) }

/-! ### The body check alone -/

/-- The newest time of the made view. -/
def t0 : UInt32 := 1400000000

/-- The median time past of the made view: the sorted time at index 5 of `t0`, `t0 - 60`, ..., `t0 - 600`. -/
def median : UInt32 := 1399999700

/-- The time of the made block. -/
def blockTime : UInt32 := 1400000060

/-- The made view: heights 4,999 down to 4,989, with the times `t0 - 60 * i`. -/
def madeView : List BlockIndex := (List.range 11).map fun i => ⟨4999 - i, t0 - 60 * UInt32.ofNat i, 0x1e0ffff0⟩

/-- A context with the view `view`, and no active version-bits state. -/
def contextOf (view : List BlockIndex) (adjustedTime : Int64) : ValidateContext :=
  { view, adjustedTime, lastCheckpointHeight := none, csvActive := false, segwitActive := false,
    prevMedianTimePast := 0, bip34Ancestor := none }

/-- An unavailable verifier. No block of this module has a script that calls it. -/
def noVerifier : SignatureVerifier := fun _ _ _ => none

/-- The revision with the baseline error types. -/
def revision : BlockRevision ScriptError Unsupported ConnectBlockError ConnectBlockError := blockRevision noVerifier

/-- The body check of the revision on a block with the coinbase and one transaction, on the made view. -/
def body (active : Bool) (view : List BlockIndex) (lockTime sequence : UInt32) : Except ContextualBodyError Unit :=
  contextualBodyWith revision active (contextOf view 0) (blockOf Hash256.zero blockTime [coinbaseTx, lockedTx lockTime sequence])

/-- Whether a body result is the expected one: `none` for an acceptance, or the error. -/
def bodyIs (r : Except ContextualBodyError Unit) (expected : Option ContextualBodyError) : Bool :=
  match r, expected with
  | .ok (), none => true
  | .error e, some e' => decide (e = e')
  | _, _ => false

/-- A body case: a label, the view, the lock time, the sequence, and the results with `active` true and false. -/
structure BodyCase where
  label : String
  view : List BlockIndex := madeView
  lockTime : UInt32
  sequence : UInt32 := 0
  active : Option ContextualBodyError
  inactive : Option ContextualBodyError

/-- The body cases. -/
def bodyCases : List BodyCase := [
  -- The three boundaries of design record 0012, section 10.1.
  { label := "lock time one below the median cutoff", lockTime := median - 1, active := none, inactive := none },
  { label := "lock time equal to the median cutoff", lockTime := median, active := some .nonFinal, inactive := none },
  { label := "lock time equal to the block time", lockTime := blockTime,
    active := some .nonFinal, inactive := some .nonFinal },
  -- Between the two cutoffs, and on each side of the block time.
  { label := "lock time one above the median cutoff", lockTime := median + 1,
    active := some .nonFinal, inactive := none },
  { label := "lock time one below the block time", lockTime := blockTime - 1,
    active := some .nonFinal, inactive := none },
  { label := "lock time one above the block time", lockTime := blockTime + 1,
    active := some .nonFinal, inactive := some .nonFinal },
  -- A sequence other than `SEQUENCE_FINAL` leaves the transaction to the lock time.
  { label := "sequence 0xfffffffe at the median cutoff", lockTime := median, sequence := 0xfffffffe,
    active := some .nonFinal, inactive := none },
  -- Every input final: the transaction is final at every cutoff.
  { label := "final sequence at the median cutoff", lockTime := median, sequence := 0xffffffff,
    active := none, inactive := none },
  { label := "final sequence at the block time", lockTime := blockTime, sequence := 0xffffffff,
    active := none, inactive := none },
  -- A lock time of 0 is final, and a lock time below 500,000,000 is a height, which the rule does not change.
  { label := "lock time 0", lockTime := 0, active := none, inactive := none },
  { label := "height lock time below the height 5000", lockTime := 4999, active := none, inactive := none },
  { label := "height lock time equal to the height 5000", lockTime := 5000,
    active := some .nonFinal, inactive := some .nonFinal },
  -- Without a predecessor the block is not applicable: the cutoff is the block time for both values of `active`.
  { label := "no predecessor, lock time one below the block time", view := [], lockTime := blockTime - 1,
    active := none, inactive := none },
  { label := "no predecessor, lock time equal to the block time", view := [], lockTime := blockTime,
    active := some .nonFinal, inactive := some .nonFinal }
]

/-! ### The whole of `validateBlock`, at height 1 -/

/-- The time of the mainnet genesis block (SOURCES.md, D9, line 155). -/
def genesisTime : UInt32 := 1386325540

/-- The view of the block at height 1: the genesis block alone. -/
def genesisView : List BlockIndex := [⟨0, genesisTime, 0x1e0ffff0⟩]

/-- The hash of the mainnet genesis block. -/
def genesisHash : Hash256 := (genesisHash? .mainnet).getD Hash256.zero

/-- A block at height 1 with the time `genesisTime + 60` and one coinbase with the sequence 0 and the lock time `lockTime`. -/
def heightOne (lockTime : UInt32) : Block := blockOf genesisHash (genesisTime + 60) [lockedCoinbase lockTime 0]

/-- The context of the block at height 1. The adjusted time is the time of the block. -/
def heightOneContext : ValidateContext := contextOf genesisView 1386325600

/-- The arguments of the block at height 1, without the proof-of-work check and the Merkle check, on the empty coin set. -/
def heightOneArgs (lockTime : UInt32) : BlockArgs :=
  ⟨noVerifier, false, false, heightOneContext, CoinSet.empty, heightOne lockTime⟩

/-- An activation with the height `height` on mainnet. -/
def activationAt (height : Option Nat) : Activation :=
  ⟨fun
    | .mainnet => height
    | _ => none⟩

/-- `validateBlockWith` with the revision on the block at height 1, for an activation. -/
def withActivation (height : Option Nat) (lockTime : UInt32) : BlockOutcome ValidateError ValidateError ConnectResult :=
  validateBlockWith ValidateEmbedding.baseline ConnectEmbedding.baseline (blockRevision noVerifier) (activationAt height)
    false false heightOneContext CoinSet.empty (heightOne lockTime)

/-- The error of a baseline result, or `none` for an acceptance. -/
def baselineError (r : Except ValidateError ConnectResult) : Option ValidateError :=
  match r with
  | .ok _ => none
  | .error e => some e

/-- Whether an outcome is the expected one: an acceptance for `none`, or a rejection with the error. -/
def outcomeIs (o : BlockOutcome ValidateError ValidateError ConnectResult) (expected : Option ValidateError) : Bool :=
  match expected with
  | none => o.isOk
  | some e => decide (o.rejection? = some e)

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  -- The median of the made view, by hand: the sorted time at index 5.
  failures := failures + (← require "the median of the made view"
    (match medianTimePast madeView with | .ok m => m == (median.toNat : Int) | .error _ => false))
  for c in bodyCases do
    failures := failures + (← require s!"{c.label}, active" (bodyIs (body true c.view c.lockTime c.sequence) c.active))
    failures := failures + (← require s!"{c.label}, inactive"
      (bodyIs (body false c.view c.lockTime c.sequence) c.inactive))
  -- The three boundaries at the block level. The median is the genesis time, and the block time is 60 seconds later.
  let nonFinal : ValidateError := .contextualBody .nonFinal
  let blockCases : List (String × UInt32 × Option ValidateError × Option ValidateError) := [
    ("height 1, lock time one below the median cutoff", genesisTime - 1, none, none),
    ("height 1, lock time equal to the median cutoff", genesisTime, some nonFinal, none),
    ("height 1, lock time one below the block time", genesisTime + 59, some nonFinal, none),
    ("height 1, lock time equal to the block time", genesisTime + 60, some nonFinal, some nonFinal)]
  for (label, lockTime, active, baseline) in blockCases do
    let args := heightOneArgs lockTime
    failures := failures + (← require s!"{label}, baseline" (baselineError (baselineValidate args) == baseline))
    failures := failures + (← require s!"{label}, active" (outcomeIs (revisedValidate true args) active))
    failures := failures + (← require s!"{label}, inactive" (outcomeIs (revisedValidate false args) baseline))
    -- The block is at height 1. An activation height of 0 or 1 is active there, and a height of 2 or no height is not.
    failures := failures + (← require s!"{label}, activation height 0" (outcomeIs (withActivation (some 0) lockTime) active))
    failures := failures + (← require s!"{label}, activation height 1" (outcomeIs (withActivation (some 1) lockTime) active))
    failures := failures + (← require s!"{label}, activation height 2"
      (outcomeIs (withActivation (some 2) lockTime) baseline))
    failures := failures + (← require s!"{label}, no activation height" (outcomeIs (withActivation none lockTime) baseline))
  let total := 1 + 2 * bodyCases.length + 7 * blockCases.length
  IO.println s!"Proposals RelativeLockTime: {total} cases, {failures} failures"
  return failures

end KnownAnswers.Proposals.RelativeLockTime
