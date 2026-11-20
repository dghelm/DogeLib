import DogeLib.Proposals
import KnownAnswers.Proposals.RelativeLockTime

/-!
## Proposals: the proposed revision `RelativeLockTime`, the sequence locks of BIP 68

`RelativeLockTime` is the revision of design record 0012.
Through extension E2, the revision runs `sequenceLocks` on each transaction that is not a coinbase.
These cases run `sequenceLocks`, `validateBlockWithActive` and `validateBlockWith` through the compiled code.

Each expected result is derived by hand, never computed by DogeLib, from three sources:

- BIP 68 (SOURCES.md, P1): an input whose sequence has bit 31 clear, in a transaction of version 2 or more, has a relative lock time. With bit 22 clear, the low 16 bits `n` count blocks, and the input is valid in a block at the height of its coin plus `n` or above. With bit 22 set they count units of 512 seconds from the median time past of the block before the coin's block, and the input is valid when the median time past of the block's predecessor has reached that time.
- Core's code of the rule at the pin (SOURCES.md, D114, `src/validation.cpp`, lines 309 to 384): `CalculateSequenceLocks` and `EvaluateSequenceLocks`.
- Core's unit cases of the rule (SOURCES.md, D117, `src/test/miner_tests.cpp`, lines 398 to 470). Design record 0012 names them as reference R14. Their values depend on Core's test chain, so each case here has the same form on a made chain. The comment of a case cites its lines.

The median of n times, for n at most 11, is the sorted time at index n / 2 (D18, `src/chain.h`, lines 286 to 298).

### The made chain

The rule-level cases are for a block at height 40.
`lockView` is the view of its predecessor: heights 39 down to 0, where the entry at height `k` has the time `t0 + 512 * k`.
The times rise with the height, so the median time past of the entry at height `k` is:

- For `k` of 10 or more: the sixth of eleven times, that of height `k - 5`, which is `t0 + 512 * (k - 5)`.
- For `k = 0`: the one time `t0`. For `k = 1`: the upper of two times, `t0 + 512`.

So the median time past of the predecessor is `m = t0 + 512 * 34`.
`shortSecondView` is `lockView` with the time of height 34 one second lower. That entry is still the sixth of the eleven, so the median is `m - 1`.

A lock is met when `c + n ≤ 40` (height), or `t + 512 * n ≤ m` (time), where `c` is the height of the coin and `t` the median time past of the ancestor at height `max (c - 1) 0`.

The cases cover the boundaries of design record 0012, section 10.1:

- A height lock that is met exactly, and one that is one block short.
- A time lock that is met exactly, and one that is one second short.
- A coin of the same block with `n` of 0 and of 1.
- Versions 1, 2 and -1.
- A sequence with bit 31 set and with bit 22 set, and bits outside the mask `0x0040ffff`.
- A coin at height 0 and at height 1, for `max (c - 1) 0`.

Other cases give the three results outside the model, and show where the rule does not apply.

### Made blocks

The block cases run the whole of `validateBlock` and of the revision on a made block at height 1 on the mainnet genesis block, as the cutoff cases do.
The view is the genesis block alone, so the median time past of the predecessor and of the ancestor at height 0 is the time of the genesis block.
The coin set has one coin with the script `OP_1`, at a height that the case gives.
The baseline has no sequence lock, so `validateBlock` accepts every block of these cases.
-/

namespace KnownAnswers.Proposals.RelativeLockTimeSequence

open DogeLib DogeLib.Block DogeLib.Work DogeLib.Transaction DogeLib.Script
open DogeLib.Proposals.Framework DogeLib.Proposals.RelativeLockTime
open KnownAnswers.Proposals.RelativeLockTime (require scriptOf counted coinbaseTx blockOf genesisTime genesisHash
  heightOneContext noVerifier activationAt baselineError)

/-! ### The rule alone -/

/-- The time of the entry at height 0 of the made chain. -/
def t0 : UInt32 := 1400000000

/-- The made view: heights 39 down to 0, with the times `t0 + 512 * height`. -/
def lockView : List BlockIndex := (List.range 40).map fun i => ⟨39 - i, t0 + 512 * UInt32.ofNat (39 - i), 0x1e0ffff0⟩

/-- `lockView` with the time of the entry at height 34 one second lower. Its median time past is one second lower. -/
def shortSecondView : List BlockIndex :=
  lockView.map fun e => if e.nHeight == 34 then { e with nTime := e.nTime - 1 } else e

/-- The median time past of `lockView`: the time of height 34. -/
def median : Int := 1400000000 + 512 * 34

/-- Bit 22 of a sequence: the lock counts units of 512 seconds. -/
def timeFlag : UInt32 := 0x00400000

/-- A transaction with the version `version` and one input for each sequence of the list. -/
def txOf (version : UInt32) (sequences : List UInt32) : Transaction :=
  { version
    inputs := counted (sequences.map fun sequence =>
      { prevout := ⟨Hash256.zero, 0⟩, scriptSig := scriptOf [], sequence })
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [] }]
    lockTime := 0 }

/-- A coin at the height `height`, with an amount of 0 and an empty script. -/
def coinAt (height : Nat) : Coin := ⟨⟨0, scriptOf []⟩, height, false⟩

/-- The expected result of a case. -/
inductive Expected where
  | accepted
  | rejected
  | unsupported (reason : Reason)

/-- Whether the result of `sequenceLocks` for the transaction at index 7 is the expected one. -/
def resultIs (r : BlockOutcome RevisionError Reason Unit) : Expected → Bool
  | .accepted => r.isOk
  | .rejected => decide (r.rejection? = some (.sequenceLocks 7))
  | .unsupported reason => match r with
    | .unsupported got => decide (got = reason)
    | _ => false

/--
A rule case: a label, the view, the height of the block, the version, the inputs as pairs of a sequence and the height of the spent coin, and the expected result with `active` true.
-/
structure RuleCase where
  label : String
  view : List BlockIndex := lockView
  height : Nat := 40
  version : UInt32 := 2
  inputs : List (UInt32 × Nat)
  expected : Expected

/-- The least coin height outside the domain: `2^31 - 65535`. -/
def heightBound : Nat := 2147418113

/-- The rule cases. -/
def ruleCases : List RuleCase := [
  -- Height locks. `miner_tests.cpp`, lines 403 to 420: a lock that fails in the next block and passes one block later.
  { label := "height lock met exactly: 30 + 10 = 40", inputs := [(10, 30)], expected := .accepted },
  { label := "height lock one block short: 30 + 11 = 41", inputs := [(11, 30)], expected := .rejected },
  { label := "height lock one block short: 31 + 10 = 41", inputs := [(10, 31)], expected := .rejected },
  { label := "height lock of 0 on an old coin", inputs := [(0, 30)], expected := .accepted },
  { label := "largest height lock on a coin at height 0: 65535 > 40", inputs := [(0xffff, 0)], expected := .rejected },
  -- A coin of the same block has the height of the block. `miner_tests.cpp`, lines 456 to 462.
  { label := "coin of the same block, height lock 0", inputs := [(0, 40)], expected := .accepted },
  { label := "coin of the same block, height lock 1", inputs := [(1, 40)], expected := .rejected },
  -- Versions, with a lock that is one block short. The version is compared as an unsigned value.
  { label := "version 0", version := 0, inputs := [(11, 30)], expected := .accepted },
  { label := "version 1", version := 1, inputs := [(11, 30)], expected := .accepted },
  { label := "version 2", version := 2, inputs := [(11, 30)], expected := .rejected },
  { label := "version 3", version := 3, inputs := [(11, 30)], expected := .rejected },
  { label := "version -1", version := 0xffffffff, inputs := [(11, 30)], expected := .rejected },
  { label := "version -1, lock met", version := 0xffffffff, inputs := [(10, 30)], expected := .accepted },
  -- Bit 31 turns the lock of the input off.
  { label := "bit 31 with a height lock that is short", inputs := [(0x8000000b, 30)], expected := .accepted },
  { label := "bit 31 with a time lock that is short", inputs := [(0x8040ffff, 39)], expected := .accepted },
  { label := "SEQUENCE_FINAL", inputs := [(0xffffffff, 40)], expected := .accepted },
  -- Bits 16 to 21 and 23 to 30 are outside the mask `0x0040ffff`. `0x7fbf000a` is a height lock of 10.
  { label := "bits outside the mask, height lock met", inputs := [(0x7fbf000a, 30)], expected := .accepted },
  { label := "bits outside the mask, height lock short", inputs := [(0x7fbf000b, 30)], expected := .rejected },
  -- Time locks. The coin at height 21 reads the ancestor at height 20, whose median is `t0 + 512 * 15`.
  -- `miner_tests.cpp`, lines 422 to 436: a time lock that fails, and passes when the median is 512 seconds later.
  { label := "time lock met exactly: 15 + 19 = 34 units", inputs := [(timeFlag ||| 19, 21)], expected := .accepted },
  { label := "time lock one unit short: 15 + 20 = 35 units", inputs := [(timeFlag ||| 20, 21)], expected := .rejected },
  { label := "time lock one second short", view := shortSecondView, inputs := [(timeFlag ||| 19, 21)],
    expected := .rejected },
  { label := "time lock one unit below, median one second lower", view := shortSecondView,
    inputs := [(timeFlag ||| 18, 21)], expected := .accepted },
  -- `0x7fff0013` has bit 22 and the low bits 19.
  { label := "bits outside the mask, time lock met", inputs := [(0x7fff0013, 21)], expected := .accepted },
  { label := "bits outside the mask, time lock short", inputs := [(0x7fff0014, 21)], expected := .rejected },
  -- `max (c - 1) 0`: the coins at heights 0 and 1 both read the ancestor at height 0, with the median `t0`.
  { label := "coin at height 0, time lock of 34 units", inputs := [(timeFlag ||| 34, 0)], expected := .accepted },
  { label := "coin at height 0, time lock of 35 units", inputs := [(timeFlag ||| 35, 0)], expected := .rejected },
  { label := "coin at height 1, time lock of 34 units", inputs := [(timeFlag ||| 34, 1)], expected := .accepted },
  { label := "coin at height 1, time lock of 35 units", inputs := [(timeFlag ||| 35, 1)], expected := .rejected },
  -- The coin at height 2 reads the ancestor at height 1, with the median `t0 + 512`.
  { label := "coin at height 2, time lock of 33 units", inputs := [(timeFlag ||| 33, 2)], expected := .accepted },
  { label := "coin at height 2, time lock of 34 units", inputs := [(timeFlag ||| 34, 2)], expected := .rejected },
  -- A coin of the same block reads the predecessor, whose median is `m`. `miner_tests.cpp`, lines 463 to 466.
  { label := "coin of the same block, time lock 0", inputs := [(timeFlag, 40)], expected := .accepted },
  { label := "coin of the same block, time lock 1", inputs := [(timeFlag ||| 1, 40)], expected := .rejected },
  -- Several inputs: every lock must be met.
  { label := "no input with a lock", inputs := [(0xffffffff, 30), (0x80000000, 31)], expected := .accepted },
  { label := "height and time lock, both met", inputs := [(10, 30), (timeFlag ||| 19, 21)], expected := .accepted },
  { label := "height lock met, time lock short", inputs := [(10, 30), (timeFlag ||| 20, 21)], expected := .rejected },
  { label := "height lock short, time lock met", inputs := [(11, 30), (timeFlag ||| 19, 21)], expected := .rejected },
  { label := "two height locks, the second short", inputs := [(1, 30), (10, 31)], expected := .rejected },
  { label := "a short lock with bit 31, and a met lock", inputs := [(0x80000005, 39), (10, 30)],
    expected := .accepted },
  -- A height lock on a coin above the block reads no ancestor: Core's sum is `41 + 0 - 1 = 40`, which is not below 40.
  { label := "coin above the block, height lock", inputs := [(0, 41)], expected := .rejected },
  -- The three results outside the model.
  { label := "coin above the block, time lock", inputs := [(timeFlag, 41)], expected := .unsupported .coinAboveBlock },
  { label := "coin height at the bound, height lock", inputs := [(0, heightBound)],
    expected := .unsupported .heightOutOfDomain },
  { label := "coin height at the bound, time lock", inputs := [(timeFlag, heightBound)],
    expected := .unsupported .heightOutOfDomain },
  -- One below the bound: Core's sum `2147418112 + 65535` is `2^31 - 1`, which fits `int`, and the result is one less.
  { label := "coin height one below the bound", inputs := [(0xffff, heightBound - 1)], expected := .rejected },
  { label := "coin height at the bound, bit 31", inputs := [(0x80000000, heightBound)], expected := .accepted },
  { label := "view of 11 entries, time lock on an old coin", view := lockView.take 11,
    inputs := [(timeFlag ||| 19, 21)], expected := .unsupported .ancestorOutsideView },
  { label := "view of 11 entries, ancestor inside with too few entries below it", view := lockView.take 11,
    inputs := [(timeFlag, 35)], expected := .unsupported .ancestorOutsideView },
  { label := "view of 11 entries, height lock", view := lockView.take 11, inputs := [(10, 30)], expected := .accepted },
  { label := "view of 11 entries, time lock on a coin of the same block", view := lockView.take 11,
    inputs := [(timeFlag, 40)], expected := .accepted },
  { label := "view of 5 entries: no median of the predecessor", view := lockView.take 5, inputs := [(10, 30)],
    expected := .unsupported .ancestorOutsideView },
  { label := "view of 5 entries, version 1", view := lockView.take 5, version := 1, inputs := [(11, 30)],
    expected := .accepted },
  { label := "view whose first entry is not below the block", height := 41, inputs := [(0, 30)],
    expected := .unsupported .ancestorOutsideView },
  -- The first reason in input order.
  { label := "two reasons, coinAboveBlock first", inputs := [(timeFlag, 41), (0, heightBound)],
    expected := .unsupported .coinAboveBlock },
  { label := "two reasons, heightOutOfDomain first", inputs := [(0, heightBound), (timeFlag, 41)],
    expected := .unsupported .heightOutOfDomain },
  -- A reason after a lock that is short: the result is outside the model, and is not a rejection.
  { label := "a short lock, then a reason", inputs := [(11, 30), (timeFlag, 41)],
    expected := .unsupported .coinAboveBlock },
  -- A block without a predecessor is not applicable.
  { label := "empty view", view := [], height := 0, inputs := [(11, 30)], expected := .accepted }
]

/-! ### Made blocks at height 1 -/

/-- The transaction that created the spent coin: one output of 0 with the script `OP_1`. It is not a coinbase. -/
def fundingTx : Transaction :=
  { version := 1
    inputs := counted [{ prevout := ⟨Hash256.zero, 0⟩, scriptSig := scriptOf [], sequence := 0xffffffff }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [0x51] }]
    lockTime := 0 }

/-- A transaction with the version `version` and one input: it spends output 0 of `prev` with an empty `scriptSig` and the sequence `sequence`. Its one output has the script `OP_1`. -/
def spendTx (prev : Transaction) (version sequence : UInt32) : Transaction :=
  { version
    inputs := counted [{ prevout := ⟨prev.txid, 0⟩, scriptSig := scriptOf [], sequence }]
    outputs := counted [{ value := 0, scriptPubKey := scriptOf [0x51] }]
    lockTime := 0 }

/-- The arguments of a block at height 1 with a coinbase and the transactions `txs`, on the coin set with the coin of `fundingTx` at the height `coinHeight`. -/
def blockArgs (coinHeight : Nat) (txs : List Transaction) : BlockArgs :=
  ⟨noVerifier, false, false, heightOneContext, CoinSet.empty.addTx fundingTx coinHeight,
    blockOf genesisHash (genesisTime + 60) (coinbaseTx :: txs)⟩

/-- `validateBlockWith` with the revision on the arguments, for an activation. -/
def withActivation (height : Option Nat) (a : BlockArgs) : BlockOutcome ValidateRejection ValidateReason ConnectResult :=
  validateBlockWith validateEmbedding connectEmbedding (blockRevision a.verify a.ctx.view) (activationAt height)
    a.fCheckPOW a.fCheckMerkleRoot a.ctx a.coins a.block

/-- The expected outcome of a block case: an acceptance, the failure of the sequence locks of the transaction at an index, or a reason. -/
inductive BlockExpected where
  | accepted
  | sequenceLocks (index : Nat)
  | unsupported (reason : Reason)

/-- Whether an outcome is the expected one. -/
def blockIs (o : BlockOutcome ValidateRejection ValidateReason ConnectResult) : BlockExpected → Bool
  | .accepted => o.isOk
  | .sequenceLocks index => decide (o.rejection? = some (.inr (.sequenceLocks index)))
  | .unsupported reason => match o with
    | .unsupported got => decide (got = .inr reason)
    | _ => false

/-- A block case: a label, the height of the coin of `fundingTx`, the transactions after the coinbase, and the expected outcome of the active revision. -/
structure BlockCase where
  label : String
  coinHeight : Nat
  txs : List Transaction
  active : BlockExpected

/-- A transaction of the block that spends the coin of `fundingTx` with every sequence final, and creates a coin at the height of the block. -/
def middleTx : Transaction := spendTx fundingTx 1 0xffffffff

/-- The block cases. The block is at height 1, and every median time past is the time of the genesis block. -/
def blockCases : List BlockCase := [
  -- A coin at height 0.
  ⟨"coin at height 0, height lock 1: met exactly", 0, [spendTx fundingTx 2 1], .accepted⟩,
  ⟨"coin at height 0, height lock 2: one block short", 0, [spendTx fundingTx 2 2], .sequenceLocks 1⟩,
  ⟨"coin at height 0, height lock 2, version 1", 0, [spendTx fundingTx 1 2], .accepted⟩,
  ⟨"coin at height 0, height lock 2, version -1", 0, [spendTx fundingTx 0xffffffff 2], .sequenceLocks 1⟩,
  ⟨"coin at height 0, height lock 2 with bit 31", 0, [spendTx fundingTx 2 0x80000002], .accepted⟩,
  ⟨"coin at height 0, time lock 0: met exactly", 0, [spendTx fundingTx 2 timeFlag], .accepted⟩,
  ⟨"coin at height 0, time lock 1", 0, [spendTx fundingTx 2 (timeFlag ||| 1)], .sequenceLocks 1⟩,
  -- A coin at the height of the block.
  ⟨"coin at height 1, height lock 0", 1, [spendTx fundingTx 2 0], .accepted⟩,
  ⟨"coin at height 1, height lock 1", 1, [spendTx fundingTx 2 1], .sequenceLocks 1⟩,
  ⟨"coin at height 1, time lock 0", 1, [spendTx fundingTx 2 timeFlag], .accepted⟩,
  ⟨"coin at height 1, time lock 1", 1, [spendTx fundingTx 2 (timeFlag ||| 1)], .sequenceLocks 1⟩,
  -- A coin that the block itself creates: transaction 1 creates it, and transaction 2 spends it.
  ⟨"coin of the same block, height lock 0", 0, [middleTx, spendTx middleTx 2 0], .accepted⟩,
  ⟨"coin of the same block, height lock 1", 0, [middleTx, spendTx middleTx 2 1], .sequenceLocks 2⟩,
  ⟨"coin of the same block, time lock 0", 0, [middleTx, spendTx middleTx 2 timeFlag], .accepted⟩,
  ⟨"coin of the same block, time lock 1", 0, [middleTx, spendTx middleTx 2 (timeFlag ||| 1)], .sequenceLocks 2⟩,
  -- A coin above the block: a height lock fails, and a time lock is outside the model.
  ⟨"coin at height 2, height lock 0", 2, [spendTx fundingTx 2 0], .sequenceLocks 1⟩,
  ⟨"coin at height 2, time lock 0", 2, [spendTx fundingTx 2 timeFlag], .unsupported .coinAboveBlock⟩,
  ⟨"coin height at the bound, height lock 0", 2147418113, [spendTx fundingTx 2 0], .unsupported .heightOutOfDomain⟩]

/-- Runs every case. Returns the number of failures. -/
def check : IO Nat := do
  let mut failures := 0
  -- The medians of the made views, by hand.
  failures := failures + (← require "the median of the made view"
    (match medianTimePast lockView with | .ok m => m == median | .error _ => false))
  failures := failures + (← require "the median of the view with one time a second lower"
    (match medianTimePast shortSecondView with | .ok m => m == median - 1 | .error _ => false))
  failures := failures + (← require "the median of the ancestor at height 20"
    (match ancestorMedianTimePast lockView 40 21 with | .ok t => t == 1400000000 + 512 * 15 | .error _ => false))
  failures := failures + (← require "the median of the ancestor at height 0, for the coins at heights 0 and 1"
    (match ancestorMedianTimePast lockView 40 0, ancestorMedianTimePast lockView 40 1 with
      | .ok t, .ok t' => t == 1400000000 && t' == 1400000000
      | _, _ => false))
  failures := failures + (← require "the median of the ancestor at height 1"
    (match ancestorMedianTimePast lockView 40 2 with | .ok t => t == 1400000000 + 512 | .error _ => false))
  for c in ruleCases do
    let tx := txOf c.version (c.inputs.map (·.1))
    let coins := c.inputs.map fun p => coinAt p.2
    failures := failures + (← require s!"{c.label}, active"
      (resultIs (sequenceLocks true c.view c.height 7 tx coins) c.expected))
    failures := failures + (← require s!"{c.label}, inactive"
      (resultIs (sequenceLocks false c.view c.height 7 tx coins) .accepted))
  for c in blockCases do
    let args := blockArgs c.coinHeight c.txs
    failures := failures + (← require s!"block: {c.label}, baseline" (baselineError (baselineValidate args) == none))
    failures := failures + (← require s!"block: {c.label}, active" (blockIs (revisedValidate true args) c.active))
    failures := failures + (← require s!"block: {c.label}, inactive" (blockIs (revisedValidate false args) .accepted))
    -- The block is at height 1. An activation height of 1 is active there, and a height of 2 is not.
    failures := failures + (← require s!"block: {c.label}, activation height 1"
      (blockIs (withActivation (some 1) args) c.active))
    failures := failures + (← require s!"block: {c.label}, activation height 2"
      (blockIs (withActivation (some 2) args) .accepted))
  let total := 5 + 2 * ruleCases.length + 5 * blockCases.length
  IO.println s!"Proposals RelativeLockTime sequence locks: {total} cases, {failures} failures"
  return failures

end KnownAnswers.Proposals.RelativeLockTimeSequence
