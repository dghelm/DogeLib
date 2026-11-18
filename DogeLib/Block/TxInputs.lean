module

public import DogeLib.Block.Coins

/-!
# `CheckTxInputs`

Core's `Consensus::CheckTxInputs` on mainnet: the checks of the coins that a transaction spends.

The source is `src/validation.cpp`, lines 1415 to 1460, at the Core pin (SOURCES.md, D114).
`checkTxInputs` follows its statements in order, and returns the first failure.

The function takes the coins, not the coin set.
Core's first statement tests `inputs.HaveInputs(tx)` (line 1419).
`ConnectBlock` makes the same test on the same view before it calls `CheckInputs` (line 1944), so that statement cannot fail there.
`connectBlock` makes the test once, and passes the coins that it found.

## Integer semantics

`CAmount` is `int64_t`.
Core adds each coin's amount to `nValueIn` before it tests either value (lines 1441 to 1442).
A sum outside the `int64_t` range is undefined behaviour in C++.
The definitions compute in the integers.
When a sum leaves the `int64_t` range, the result is `outOfDomain`, which says nothing about Core (design record 0010, section 3).
`checkInputValues_ne_outOfDomain` (in `DogeLib.Block.Proofs.Connect`) shows that this never happens when every coin has an amount from 0 to `MAX_MONEY`.

`nSpendHeight - coins->nHeight` is an `int` difference of two heights below `2^31`, which cannot overflow.

## The unreachable reasons

Two failures of Core's text cannot happen (design record 0010, section 5):

- `bad-txns-fee-negative` (line 1454). The statement before it returns when `nValueIn < GetValueOut()`.
- `bad-txns-fee-outofrange` (line 1457). `nFees` is 0 before the addition, so it equals the fee, which is at most `nValueIn`. The loop left `nValueIn` at most `MAX_MONEY`.

`checkTxInputs` keeps both tests, and `checkTxInputs_ne_feeNegative` and `checkTxInputs_ne_feeOutOfRange` prove that neither result occurs.
The second needs an output total that is not negative, which `CheckTransaction` gives.

## Source

The adaptation follows Core's statements, with a named error for each `return state.Invalid(...)` and `return state.DoS(...)`.
The source is MIT-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
Original notice from `src/validation.cpp`:

Copyright (c) 2009-2010 Satoshi Nakamoto
Copyright (c) 2009-2016 The Bitcoin Core developers
Copyright (c) 2022-2023 The Dogecoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction

/-- Whether an integer is a value of `int64_t`. -/
def inInt64Range (v : Int) : Bool := -9223372036854775808 ≤ v && v ≤ 9223372036854775807

/-- Core's `MoneyRange` (`src/amount.h`, line 33): from 0 to `MAX_MONEY`. -/
def moneyRange (v : Int) : Bool := 0 ≤ v && v ≤ maxMoney

/--
`nCoinbaseMaturity` of the mainnet record that `GetConsensus(height)` selects (D100, `src/chainparams.cpp`, lines 92 and 131).
It is 30 below height 145,000, and 240 from that height.
Core selects the record by the height of the coin, not of the spending block (D114, line 1433).
-/
def coinbaseMaturity (coinHeight : Nat) : Nat := if coinHeight < 145000 then 30 else 240

/-- Core's `CTransaction::GetValueOut` (`src/primitives/transaction.cpp`, lines 83 to 93) as an integer: the sum of the output amounts.
Core throws when an amount or a partial sum is outside `MoneyRange`. A transaction that `checkTransaction` accepts has no such amount or sum. -/
def _root_.DogeLib.Transaction.Transaction.valueOut (tx : Transaction) : Int := (tx.outputs.val.map fun o => o.amount.toInt).sum

/-- The failures of `Consensus::CheckTxInputs`, in source order (D114), and the domain error. -/
inductive CheckTxInputsError where
  /-- A coinbase coin is spent at a depth below its maturity: `bad-txns-premature-spend-of-coinbase`, score 0 (line 1436). -/
  | prematureSpendOfCoinbase
  /-- A coin's amount, or the sum of the amounts so far, is outside `MoneyRange`: `bad-txns-inputvalues-outofrange`, score 100 (line 1443). -/
  | inputValuesOutOfRange
  /-- The coins are worth less than the outputs: `bad-txns-in-belowout`, score 100 (line 1448). -/
  | inBelowOut
  /-- The fee is negative: `bad-txns-fee-negative`, score 100 (line 1454). Unreachable (`checkTxInputs_ne_feeNegative`). -/
  | feeNegative
  /-- The fee is outside `MoneyRange`: `bad-txns-fee-outofrange`, score 100 (line 1457). Unreachable (`checkTxInputs_ne_feeOutOfRange`). -/
  | feeOutOfRange
  /-- A sum left the `int64_t` range, where Core's addition is undefined. Not a Core result. -/
  | outOfDomain
  deriving DecidableEq, Repr

/-- Core's reject reason for each failure (D114), and `none` for the domain error. -/
def CheckTxInputsError.rejectReason : CheckTxInputsError → Option String
  | .prematureSpendOfCoinbase => some "bad-txns-premature-spend-of-coinbase"
  | .inputValuesOutOfRange => some "bad-txns-inputvalues-outofrange"
  | .inBelowOut => some "bad-txns-in-belowout"
  | .feeNegative => some "bad-txns-fee-negative"
  | .feeOutOfRange => some "bad-txns-fee-outofrange"
  | .outOfDomain => none

/-- The denial-of-service score of each failure: 0 for a premature spend, which calls `state.Invalid` (line 1435), and 100 for the others. -/
def CheckTxInputsError.dosScore : CheckTxInputsError → Nat
  | .prematureSpendOfCoinbase | .outOfDomain => 0
  | _ => 100

/--
The loop over the inputs (D114, lines 1425 to 1445), with the sum of the earlier coins in `nValueIn`.
`spendHeight` is `nSpendHeight`, the height of the spending block.
For each coin in input order:

1. A coinbase coin whose depth `spendHeight - height` is below its maturity fails.
2. The amount is added to `nValueIn`. A sum outside the `int64_t` range is `outOfDomain`.
3. The amount and the sum must both be in `MoneyRange`.

The result is the sum of all the amounts.
-/
def checkInputValues (spendHeight : Nat) (nValueIn : Int) : List Coin → Except CheckTxInputsError Int
  | [] => .ok nValueIn
  | c :: rest =>
    if c.coinbase && decide ((spendHeight : Int) - (c.height : Int) < (coinbaseMaturity c.height : Int)) then
      .error .prematureSpendOfCoinbase
    else if !inInt64Range (nValueIn + c.value) then .error .outOfDomain
    else if !moneyRange c.value || !moneyRange (nValueIn + c.value) then .error .inputValuesOutOfRange
    else checkInputValues spendHeight (nValueIn + c.value) rest

/--
Core's `Consensus::CheckTxInputs` (D114, lines 1415 to 1460) after its `HaveInputs` test, with the first failing check as its error.
`coins` holds the coin that each input spends, in input order, and `valueOut` is `tx.GetValueOut()`.

1. `checkInputValues` accepts the coins, and gives their sum `nValueIn`.
2. `nValueIn` is at least `valueOut`.
3. The fee `nValueIn - valueOut` is not negative.
4. The fee is in `MoneyRange`.
-/
def checkTxInputs (spendHeight : Nat) (coins : List Coin) (valueOut : Int) :
    Except CheckTxInputsError Unit :=
  match checkInputValues spendHeight 0 coins with
  | .error e => .error e
  | .ok nValueIn =>
    if nValueIn < valueOut then .error .inBelowOut
    else if nValueIn - valueOut < 0 then .error .feeNegative
    else if !moneyRange (nValueIn - valueOut) then .error .feeOutOfRange
    else .ok ()

end DogeLib.Block
