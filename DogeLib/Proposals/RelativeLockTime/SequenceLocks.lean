module

public import DogeLib.Proposals.Framework.Block
public import DogeLib.Work.MedianTimePast

/-!
# `Proposals.RelativeLockTime.SequenceLocks`

The rule of BIP 68 of the proposed revision `RelativeLockTime`: the sequence of an input can state a relative lock time.
Design record 0012, sections 3.3, 6.3 and 7.2, sets the contract.

The source is Core's `CalculateSequenceLocks`, `EvaluateSequenceLocks` and `SequenceLocks` (SOURCES.md, D114, `src/validation.cpp`, lines 309 to 384), and their call in `ConnectBlock` (D114, lines 1948 to 1959).
`GetAncestor` is in D35 (`src/chain.cpp`, lines 113 to 147), and `GetMedianTimePast` in D18.
At the pin, `ConnectBlock` passes `LOCKTIME_VERIFY_SEQUENCE` only with an active CSV state, which no mainnet chain reaches (`csv_never_lockedIn`).
So the definitions state Core's dormant code, and not a rule of the baseline.

## The rule

`ConnectBlock` tests each transaction that is not a coinbase, after it finds the inputs.
The rule applies to a transaction whose version, as an unsigned 32-bit value, is at least 2.
Each input whose sequence has bit 31 clear states a lock. Let `n` be the low 16 bits of the sequence and `c` the height of the spent coin:

- Bit 22 clear, a height lock: the last invalid height is `c + n - 1`.
- Bit 22 set, a time lock: the last invalid time is `t + 512 * n - 1`. Here `t` is the median time past of the ancestor at height `max (c - 1) 0`.

Core keeps the largest value of each kind, from a start of -1 (`calculateSequenceLocks`).
The transaction fails when the largest last invalid height is at least the height of the block.
It also fails when the largest last invalid time is at least the median time past of the predecessor (`evaluateSequenceLocks`).
A failure is the error `RevisionError.sequenceLocks`, Core's `bad-txns-nonfinal` with DoS score 100.

A coin that the same block created has the height of the block.
Its height lock passes for `n` equal to 0 alone.

## The view

`sequenceLocks` takes the view of the predecessor: the predecessor and its ancestors, newest first, as `ValidateContext.view` holds them.
The ancestor at height `a` is the entry at depth `height - 1 - a`, and its median time past is `Work.medianTimePast` of the view from that entry (`ancestorMedianTimePast`).
The transaction test of the block layer has no view argument, so the revision captures the view when the caller builds it.

The rule is inactive on an empty view, as design record 0012, section 5, requires for a block that is not applicable.
`connectBlockWith` connects no transaction of a block with the genesis hash, so the test never runs on the other kind of block that is not applicable.

## Results outside the model

The test returns one of three reasons when it cannot give Core's verdict.
A reason is never a rejection.

| Reason | Condition |
| --- | --- |
| `heightOutOfDomain` | An input with bit 31 clear spends a coin whose height is at least `2^31 - 65535`. Core adds in `int`, and the sum `c + 65535`, before the subtraction of 1, then does not fit. |
| `coinAboveBlock` | A time lock reads a coin whose height is above the height of the block. For a coin one block above, Core reads the median time of the block itself. For a higher coin, `GetAncestor` returns null and Core dereferences it. |
| `ancestorOutsideView` | The view does not give a median time past that the test reads. The first entry of the view is not at the height below the block, or `Work.medianTimePast` returns an adapter error for the view or for the view from the ancestor of a time lock. |

The reasons are checked in input order, and for one input in the order of the table.
The test reads the median time past of the predecessor for every transaction that the rule applies to, as `EvaluateSequenceLocks` does.
It reads an ancestor time only for an input with a time lock.

## Differences from Core

- Core computes in `int` and `int64_t`. The definitions use unbounded integers, and `sequenceLocks_fits` proves that each sum fits its C++ type.
- Core sets the height of an input with bit 31 set to 0 in `prevHeights`. `ConnectBlock` does not read the vector again, so the definitions omit the write.
- Core has an assertion that the two vectors have one length. `connectTransactionWith` passes the coins of `lookupInputs`, which have the length of the inputs. On lists of two lengths, `calculateSequenceLocks` reads the shorter one.

## Difference from BIP 68

BIP 68 chose the unit of 512 seconds for a block interval of 600 seconds.
The pinned code keeps that unit, and Dogecoin's interval is 60 seconds. The definition follows the code (design record 0012, section 2.3).
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/-- The rejections that the revision adds to those of `ConnectBlock`. -/
inductive RevisionError where
  /-- The transaction at `index` fails the sequence locks of BIP 68: Core's `bad-txns-nonfinal`, with DoS score 100 and the code `REJECT_INVALID` (SOURCES.md, D114, lines 1955 to 1958). -/
  | sequenceLocks (index : Nat)
  deriving DecidableEq, Repr

/-- The results outside the model that the revision adds (design record 0012, section 6.3). None is a rejection. -/
inductive Reason where
  /-- The view does not give a median time past that the test reads. -/
  | ancestorOutsideView
  /-- A time lock reads a coin whose height is above the height of the block. -/
  | coinAboveBlock
  /-- A coin height is too large for Core's `int` sum. -/
  | heightOutOfDomain
  deriving DecidableEq, Repr

/-- `CTxIn::SEQUENCE_LOCKTIME_GRANULARITY` (SOURCES.md, D4, line 99): a time lock counts units of `2^9` seconds. -/
def sequenceLockTimeGranularity : Nat := 9

/--
The least coin height outside the domain: `2^31 - 65535`.
Core computes `c + n - 1` from the left in `int` (SOURCES.md, D114, line 364). For a smaller height `c`, the sum `c + 65535` fits `int`, and so does the result (design record 0012, section 7.2).
-/
def coinHeightBound : Nat := 2 ^ 31 - 65535

/-- The lock that one input states. -/
inductive InputLock where
  /-- Bit 31 of the sequence is set: no lock. -/
  | none
  /-- A height lock, with the last height at which the transaction is invalid. -/
  | height (lastInvalid : Int)
  /-- A time lock, with the last median time past at which the transaction is invalid. -/
  | time (lastInvalid : Int)
  deriving DecidableEq, Repr

/--
The median time past of the ancestor that a time lock reads, for a block at `height` and a coin at the height `c` (SOURCES.md, D114, line 348).
`view` is the view of the predecessor, whose first entry has the height `height - 1`.
The ancestor has the height `max (c - 1) 0`, so it is the entry at depth `height - 1 - (c - 1)`, with natural subtraction.
The result is `Work.medianTimePast` of the view from that entry.
-/
def ancestorMedianTimePast (view : List BlockIndex) (height c : Nat) : Except MedianTimeError Int :=
  medianTimePast (view.drop (height - 1 - (c - 1)))

/--
The lock of one input with the sequence `sequence`, which spends a coin at the height `c`, in a block at `height` (the loop body of `CalculateSequenceLocks`, SOURCES.md, D114, lines 334 to 364).
With bit 31 set the input has no lock.
With bit 22 clear the last invalid height is `c + n - 1`, where `n` is the low 16 bits.
With bit 22 set the last invalid time is `t + n * 2^9 - 1`, where `t` is `ancestorMedianTimePast`.
The module documentation states the three reasons.
-/
def inputLock (view : List BlockIndex) (height : Nat) (sequence : UInt32) (c : Nat) : Except Reason InputLock :=
  if sequence.toNat &&& sequenceLockTimeDisableFlag ≠ 0 then .ok .none
  else if coinHeightBound ≤ c then .error .heightOutOfDomain
  else if sequence.toNat &&& sequenceLockTimeTypeFlag ≠ 0 then
    if height < c then .error .coinAboveBlock
    else
      match ancestorMedianTimePast view height c with
      | .error _ => .error .ancestorOutsideView
      | .ok t =>
        .ok (.time (t + (((sequence.toNat &&& sequenceLockTimeMask) <<< sequenceLockTimeGranularity : Nat) : Int) - 1))
  else .ok (.height ((c : Int) + ((sequence.toNat &&& sequenceLockTimeMask : Nat) : Int) - 1))

/--
`CalculateSequenceLocks` for a transaction that the rule applies to (SOURCES.md, D114, lines 309 to 367).
The list holds each input with the coin that it spends, in input order.
The pair is (`nMinHeight`, `nMinTime`): the largest last invalid height and the largest last invalid time so far.
Core starts the pair at (-1, -1).
The result is the first reason, in input order, or the pair after the last input.
-/
def calculateSequenceLocks (view : List BlockIndex) (height : Nat) :
    List (TxIn × Coin) → Int × Int → Except Reason (Int × Int)
  | [], pair => .ok pair
  | (input, coin) :: rest, pair =>
    match inputLock view height input.sequence coin.height with
    | .error reason => .error reason
    | .ok .none => calculateSequenceLocks view height rest pair
    | .ok (.height last) => calculateSequenceLocks view height rest (max pair.1 last, pair.2)
    | .ok (.time last) => calculateSequenceLocks view height rest (pair.1, max pair.2 last)

/--
`EvaluateSequenceLocks` (SOURCES.md, D114, lines 369 to 378), for a block at `height` whose predecessor has the median time past `median`.
The pair passes when its height is below the height of the block and its time is below the median.
-/
def evaluateSequenceLocks (height : Nat) (median : Int) (pair : Int × Int) : Bool :=
  decide (pair.1 < (height : Int)) && decide (pair.2 < median)

/--
`sequenceLocks` with the median time past of the predecessor as an argument: `median` is the result of `Work.medianTimePast` on the view.
`sequenceLocks` passes that result. A proof can pass a known value in its place.
-/
def sequenceLocksWith (median : Except MedianTimeError Int) (active : Bool) (view : List BlockIndex) (height : Nat) :
    TxTest RevisionError Reason :=
  fun index tx coins =>
    if !active || tx.version.toNat < 2 then .ok ()
    else
      match view with
      | [] => .ok ()
      | prev :: _ =>
        if prev.nHeight + 1 ≠ height then .unsupported .ancestorOutsideView
        else
          match median with
          | .error _ => .unsupported .ancestorOutsideView
          | .ok median =>
            match calculateSequenceLocks view height (tx.inputs.val.zip coins) (-1, -1) with
            | .error reason => .unsupported reason
            | .ok pair =>
              if evaluateSequenceLocks height median pair then .ok () else .rejected (.sequenceLocks index)

/--
The sequence locks of BIP 68 as a test of one transaction that is not a coinbase (extension E2 of the block layer): Core's `SequenceLocks` as `ConnectBlock` calls it (SOURCES.md, D114, lines 1948 to 1959).
`view` is the view of the predecessor, `height` is the height of the block, and `coins` are the coins that the inputs spend, in input order.

The test accepts when `active` is false, when the version is below 2 as an unsigned value, and on an empty view.
Otherwise it accepts exactly when the pair of `calculateSequenceLocks` passes `evaluateSequenceLocks` with the median time past of the view.
A transaction that fails gets `RevisionError.sequenceLocks` with its index.
The module documentation states the three results outside the model.
-/
def sequenceLocks (active : Bool) (view : List BlockIndex) (height : Nat) : TxTest RevisionError Reason :=
  sequenceLocksWith (medianTimePast view) active view height

end DogeLib.Proposals.RelativeLockTime
