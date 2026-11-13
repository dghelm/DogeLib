module

public import DogeLib.Transaction.Serialization

/-!
# `Transaction.Check`

Core's `CheckTransaction`: the checks of one transaction that need no context.

The source is `CheckTransaction`, `src/validation.cpp`, lines 527 to 574, at the Core pin (SOURCES.md, D106).
`checkTransaction` follows its statements in order, and returns the first failure.
Each failure is one constructor of `CheckTransactionError`, with Core's reject reason, denial-of-service score and reject code.

The function reads the base fields of a transaction only.
Core's size test uses the stream flag `SERIALIZE_TRANSACTION_NO_WITNESS` (line 535), and no other statement reads a witness stack.
So `checkTransaction` takes a `Transaction`, and a caller that holds a `WitnessTransaction` passes its base fields.

## Integer semantics

`CAmount` is `int64_t` (`src/amount.h`, line 16).
Core tests each output before it adds it (lines 542 to 548).
At the addition, the sum is at most `MAX_MONEY`, and the output is from 0 to `MAX_MONEY`.
So the new sum is at most `2 * MAX_MONEY = 2 * 10^18`, which is below `2^63`, and Core's addition never overflows.
`checkOutputs` computes the same sum in the integers.

`GetSerializeSize` returns a `size_t`, and the comparison with `MAX_BLOCK_BASE_SIZE` is unsigned.
Here the size is the length of the base encoding, a natural number.

## Source

The adaptation follows Core's statements, with a named error for each `return state.DoS(...)`.
The source is MIT-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/validation.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-- `MAX_BLOCK_BASE_SIZE`: 1,000,000 bytes (`src/consensus/consensus.h`, line 17, D106). -/
def maxBlockBaseSize : Nat := 1000000

/-- `MAX_MONEY`: `10000000000 * COIN`, which is 10^18 koinu (`src/amount.h`, lines 18 and 32, D106). -/
def maxMoney : Int := 1000000000000000000

/-- Core's `COutPoint::IsNull`: the hash is zero and the index is `0xffffffff` (D4, line 41). -/
def OutPoint.isNull (o : OutPoint) : Bool := o.hash == Hash256.zero && o.n == 0xffffffff

/-- Core's `CTransaction::IsCoinBase`: exactly one input, whose outpoint is null (D4, lines 354 to 357). -/
def Transaction.isCoinBase (tx : Transaction) : Bool :=
  match tx.inputs.val with
  | [i] => i.prevout.isNull
  | _ => false

/-- The failures of `CheckTransaction`, in source order (D106). -/
inductive CheckTransactionError where
  /-- No inputs (line 531). -/
  | vinEmpty
  /-- No outputs (line 533). -/
  | voutEmpty
  /-- The base serialization has more than `MAX_BLOCK_BASE_SIZE` bytes (line 536). -/
  | oversize
  /-- An output has a negative amount (line 543). -/
  | voutNegative
  /-- An output has an amount above `MAX_MONEY` (line 545). -/
  | voutTooLarge
  /-- The sum of the outputs so far is above `MAX_MONEY` (line 548). -/
  | txoutTotalTooLarge
  /-- Two inputs have the same outpoint, and the caller asked for this check (line 557). -/
  | inputsDuplicate
  /-- A coinbase whose `scriptSig` has fewer than 2 or more than 100 bytes (line 564). -/
  | coinbaseLength
  /-- A transaction that is not a coinbase has an input with a null outpoint (line 570). -/
  | prevoutNull
  deriving DecidableEq, Repr

/-- The reject reason that Core's `CValidationState` holds after each failure (D106). -/
def CheckTransactionError.rejectReason : CheckTransactionError → String
  | .vinEmpty => "bad-txns-vin-empty"
  | .voutEmpty => "bad-txns-vout-empty"
  | .oversize => "bad-txns-oversize"
  | .voutNegative => "bad-txns-vout-negative"
  | .voutTooLarge => "bad-txns-vout-toolarge"
  | .txoutTotalTooLarge => "bad-txns-txouttotal-toolarge"
  | .inputsDuplicate => "bad-txns-inputs-duplicate"
  | .coinbaseLength => "bad-cb-length"
  | .prevoutNull => "bad-txns-prevout-null"

/-- The denial-of-service score of each failure: 10 for the two empty lists and for a null outpoint, and 100 for every other failure (D106). -/
def CheckTransactionError.dosScore : CheckTransactionError → Nat
  | .vinEmpty | .voutEmpty | .prevoutNull => 10
  | _ => 100

/-- The reject code of each failure: `REJECT_INVALID`, which is `0x10` (`src/consensus/validation.h`, line 13, D84). -/
def CheckTransactionError.rejectCode (_ : CheckTransactionError) : Nat := 0x10

/--
The loop over the outputs (D106, lines 539 to 549), with the sum of the earlier outputs in `nValueOut`.
For each output in order it tests the sign, the bound `MAX_MONEY`, and then the bound of the new sum.
Core tests the new sum with `MoneyRange`. The sum is never negative here, so only the upper bound can fail.
-/
def checkOutputs (nValueOut : Int) : List TxOut → Except CheckTransactionError Unit
  | [] => .ok ()
  | o :: rest =>
    if o.amount.toInt < 0 then .error .voutNegative
    else if o.amount.toInt > maxMoney then .error .voutTooLarge
    else if nValueOut + o.amount.toInt < 0 ∨ nValueOut + o.amount.toInt > maxMoney then
      .error .txoutTotalTooLarge
    else checkOutputs (nValueOut + o.amount.toInt) rest

/--
Whether two entries of the list are equal.
Core inserts each outpoint of `vin` into a `std::set<COutPoint>`, and fails at the first insertion that finds an equal member (D106, lines 553 to 558).
An insertion fails exactly when some earlier outpoint has the same hash and the same index (`operator<`, D4, lines 43 to 47).
The test needs a number of comparisons that is quadratic in the length of the list.
-/
def hasDuplicate : List OutPoint → Bool
  | [] => false
  | o :: rest => rest.contains o || hasDuplicate rest

/--
Core's `CheckTransaction` (D106, lines 527 to 574), with the first failing check as its error.
Core returns `true` exactly when the result is `.ok ()`.

1. The inputs and the outputs are not empty.
2. The base serialization has at most `MAX_BLOCK_BASE_SIZE` bytes.
3. Each output has an amount from 0 to `MAX_MONEY`, and so has each sum of the first outputs (`checkOutputs`).
4. With `fCheckDuplicateInputs`, no two inputs have the same outpoint.
5. A coinbase has a `scriptSig` of 2 to 100 bytes. Any other transaction has no input with a null outpoint.

`CheckBlock` and the mempool both call it with `fCheckDuplicateInputs` true at the pin.
-/
def checkTransaction (tx : Transaction) (fCheckDuplicateInputs : Bool) :
    Except CheckTransactionError Unit :=
  if tx.inputs.val.isEmpty then .error .vinEmpty
  else if tx.outputs.val.isEmpty then .error .voutEmpty
  else if (Codec.encode tx).length > maxBlockBaseSize then .error .oversize
  else
    match checkOutputs 0 tx.outputs.val with
    | .error e => .error e
    | .ok () =>
      if fCheckDuplicateInputs && hasDuplicate (tx.inputs.val.map TxIn.prevout) then
        .error .inputsDuplicate
      else if tx.isCoinBase then
        match tx.inputs.val with
        | i :: _ =>
          if i.scriptSig.bytes.val.length < 2 ∨ i.scriptSig.bytes.val.length > 100 then
            .error .coinbaseLength
          else .ok ()
        | [] => .ok ()
      else if tx.inputs.val.any (fun i => i.prevout.isNull) then .error .prevoutNull
      else .ok ()

end DogeLib.Transaction
