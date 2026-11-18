module

public import DogeLib.Block.HeaderSequence
public import DogeLib.Block.SigOpCost
public import DogeLib.Block.Subsidy
public import DogeLib.Block.TxInputs
public import DogeLib.Script.CoreVerifier

/-!
# `ConnectBlock`

Core's `ConnectBlock` on mainnet: the checks of a block against the coin set, and the new coin set.

The sources are at the Core pin (SOURCES.md):

- `ConnectBlock`, `src/validation.cpp`, lines 1783 to 2009 (D114, and D101 for the rules by height).
- `CheckInputs`, lines 1462 to 1518, and `CScriptCheck::operator()`, lines 1398 to 1405 (D114).
- `STANDARD_NOT_MANDATORY_VERIFY_FLAGS`, `src/policy/policy.h`, lines 88 to 105, with `MANDATORY_SCRIPT_VERIFY_FLAGS`, `src/script/standard.h`, line 43 (D116).
- `UpdateCoins`, lines 1366 to 1390 (D113).

`connectBlock` follows Core's statements in order, and returns the first failure:

1. `CheckBlock` with both flags `!fJustCheck` (line 1804).
2. The genesis block changes nothing and is accepted (lines 1821 to 1825).
3. BIP30: no transaction ID of the block has an entry that is not pruned: `bad-txns-BIP30` (lines 1869 to 1887). Core skips the test when the ancestor at `BIP34Height` has the hash `BIP34Hash`.
4. The script flags: `P2SH` always, `DERSIG` from `BIP66Height`, and `CHECKLOCKTIMEVERIFY` from `BIP65Height` (lines 1890 to 1904).
5. For each transaction in order (lines 1935 to 1993):
   1. If it is not a coinbase, every input has a coin: `bad-txns-inputs-missingorspent`.
   2. The signature-operation cost so far is at most `MAX_BLOCK_SIGOPS_COST`: `bad-blk-sigops`.
   3. If it is not a coinbase, its fee is added to `nFees`. Then `CheckInputs` runs `checkTxInputs` and the script of every input.
   4. `UpdateCoins` spends its coins and adds its outputs.
6. The coinbase pays at most `nFees` plus the subsidy: `bad-cb-amount` (lines 1996 to 2001).

## Script failures

`CheckInputs` runs each input's script with the block's flags (lines 1483 to 1516).
After a failure, when the flags have a bit of `STANDARD_NOT_MANDATORY_VERIFY_FLAGS`, it runs the script again without those bits.
If the second run passes, the reason is `non-mandatory-script-verify-flag`, with score 0 and the code `REJECT_NONSTANDARD`.
Otherwise the reason is `mandatory-script-verify-flag-failed`, with score 100.
Both reasons carry the text of `ScriptErrorString` for the error of the first run.
On mainnet the second run has the flag `P2SH` only, and it happens from `BIP66Height`.

The harness runs no script-check threads and leaves `hashAssumeValid` null, so Core checks every script in this order (design record 0010, section 5).
`connectBlock` describes that configuration.

A script runs through `verifyLegacySpend` on the base fields of the transaction.
Without `SCRIPT_VERIFY_WITNESS`, Core's `VerifyScript` reads no witness stack.

## What is outside the model

Six results are not Core's. Each one says nothing about Core's verdict:

- `outOfDomain`: a sum left the `int64_t` range (design record 0010, section 3). Core adds the amounts of a transaction's coins with no check (`GetValueIn`, `src/coins.cpp`, lines 272 to 282), adds the fee to `nFees` before `CheckInputs` (line 1974), and adds the subsidy (line 1996). `connect_fits` (in `DogeLib.Block.Proofs.Connect`) shows when no sum leaves the range.
- `csvActive`: the version-bits state of CSV is `ACTIVE`. Core then sets `CHECKSEQUENCEVERIFY` and enforces sequence locks (lines 1907 to 1911). On mainnet CSV never activates (`csv_never_lockedIn`), and this module does not define those rules.
- `scriptUnsupported`: `verifyLegacySpend` returned `unsupported`.
- `subsidy`: the subsidy ran out of fuel.
- `newCoinsExist`: a transaction that is not a coinbase has the ID of an entry that is not pruned. The test is at the point where `UpdateCoins` adds the outputs. Core's `ModifyNewCoins` then throws `std::logic_error` or replaces the entry, by the state of its cache (`src/coins.cpp`, lines 134 to 153). With BIP30 enforced, an earlier transaction of the same block must have made the entry, so two transactions of the block have one ID.
- `contextBounds`: a transaction has `2^32` or more inputs or outputs, which `verifyLegacySpend` excludes. `CheckBlock` bounds the base size of the block, so no such transaction gets here.

## What a failure leaves out

Two effects of a failing call are absent:

- Core changes the view as it goes. When a later transaction or the coinbase limit fails, the view keeps the changes of the earlier transactions (lines 1988 and 1996). `connectBlock` returns the error alone, so its caller keeps the set from before the block. A caller of Core must discard the view after a failure to get the same state, as the harness does.
- With `fJustCheck` false, a `CheckBlock` failure with `CorruptionPossible` makes Core call `AbortNode`, which puts the state into an error mode and starts a shutdown (lines 1805 to 1811). `connectBlock` returns the `checkBlock` rejection. `validateBlock` calls `connectBlock` with `fJustCheck` true, where `CheckBlock` tests neither the proof of work nor the Merkle root, so no failure has that flag.

## The sequence-lock reason

Core tests `SequenceLocks` for each transaction that is not a coinbase: `bad-txns-nonfinal` (lines 1949 to 1959).
That reason is unreachable on mainnet (design record 0010, section 5), by this argument.
Without an active CSV state, `nLockTimeFlags` is 0, so `CalculateSequenceLocks` returns the pair (-1, -1) (lines 318 to 331).
`EvaluateSequenceLocks` fails only when -1 is at least the height of the block, or at least the median time past of its predecessor (lines 371 to 379).
A height is not negative, and a median of `uint32_t` times is not negative.
`connectBlock` therefore has no such test, and returns `csvActive` in the one case where the argument does not apply.

## Source

The adaptation follows Core's statements, with a named error for each `return state.DoS(...)` and `return state.Invalid(...)`.
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
open DogeLib.Script

/-- `BIP66Height` on mainnet (D100, line 87): the first height with `SCRIPT_VERIFY_DERSIG`. -/
def bip66Height : Nat := 1034383

/-- `BIP65Height` on mainnet (D100, line 86): the first height with `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY`. -/
def bip65Height : Nat := 3464751

/-- `BIP34Hash` on mainnet (D100, line 85), in internal byte order. -/
def bip34Hash? : Option Hash256 :=
  hash256OfHex? "0x80d1364201e5df97e696c03bdd24dc885e8617b9de51e453c10a4f629b1e797a"

/--
`STANDARD_NOT_MANDATORY_VERIFY_FLAGS` (D116, `src/policy/policy.h`, lines 88 to 105): the standard flags without the mandatory flag `P2SH` (`src/script/standard.h`, line 43).
-/
def standardNotMandatoryVerifyFlags : UInt32 :=
  ScriptFlags.derSig ||| ScriptFlags.strictEnc ||| ScriptFlags.minimalData ||| ScriptFlags.nullDummy |||
    ScriptFlags.discourageUpgradableNops ||| ScriptFlags.cleanStack ||| ScriptFlags.minimalIf |||
    ScriptFlags.nullFail ||| ScriptFlags.checkLockTimeVerify ||| ScriptFlags.checkSequenceVerify |||
    ScriptFlags.lowS ||| ScriptFlags.witness ||| ScriptFlags.discourageUpgradableWitnessProgram |||
    ScriptFlags.witnessPubkeyType

/-- The script flags of `ConnectBlock` on mainnet at a height, without CSV and SegWit (D101, lines 1890 to 1904). -/
def connectScriptFlags (height : Nat) : UInt32 :=
  ScriptFlags.p2sh ||| (if bip66Height ≤ height then ScriptFlags.derSig else 0) |||
    (if bip65Height ≤ height then ScriptFlags.checkLockTimeVerify else 0)

/--
`fEnforceBIP30` of `ConnectBlock` (D101, lines 1869 to 1879), from the hash of the ancestor at `BIP34Height`.
Core enforces BIP30 unless that ancestor exists and has the hash `BIP34Hash`.
-/
def enforceBip30 : Option Hash256 → Bool
  | none => true
  | some hash => some hash != bip34Hash?

/-- What `ConnectBlock` reads from the block index and the version-bits cache. -/
structure ConnectContext where
  /-- `pindex->nHeight`: the height of the block. -/
  height : Nat
  /-- The hash of `pindex->pprev`, which is the input of the subsidy (line 1996). -/
  prevHash : Hash256
  /-- The hash of the ancestor of `pindex->pprev` at `BIP34Height`, or `none` when the predecessor is below that height (line 1877). -/
  bip34Ancestor : Option Hash256
  /-- Whether `VersionBitsState` gives `ACTIVE` for CSV (line 1908). Never true on mainnet. -/
  csvActive : Bool

/-- One change that a block makes to the coin set. -/
inductive CoinChange where
  /-- An input spent this coin. -/
  | spent (outpoint : OutPoint) (coin : Coin)
  /-- An output entered the set as this coin. -/
  | created (outpoint : OutPoint) (coin : Coin)
  deriving DecidableEq

/-- The result of a block that `ConnectBlock` accepts. -/
structure ConnectResult where
  /-- The coin set after the block. -/
  coins : CoinSet
  /-- The changes in the order in which `UpdateCoins` makes them: for each transaction, the coin of each input, and then each new coin. -/
  changes : List CoinChange

/-- The failures of `ConnectBlock`, in source order, and the results outside the model. -/
inductive ConnectBlockError where
  /-- `CheckBlock` fails, for the reason in `e` (line 1804). -/
  | checkBlock (e : CheckBlockError)
  /-- A transaction ID of the block has an entry that is not pruned: `bad-txns-BIP30` (line 1886). -/
  | bip30
  /-- An input of the transaction at `tx` has no coin: `bad-txns-inputs-missingorspent` (line 1946). -/
  | inputsMissingOrSpent (tx : Nat)
  /-- The signature-operation cost is above `MAX_BLOCK_SIGOPS_COST`: `bad-blk-sigops` (line 1969). -/
  | sigOps
  /-- `CheckTxInputs` rejects the transaction at `tx`, for the reason in `e` (line 1466). -/
  | txInputs (tx : Nat) (e : CheckTxInputsError)
  /-- The script of input `input` of the transaction at `tx` fails with `e`. `mandatory` is false when the script passes without the non-mandatory flags (lines 1503 and 1512). -/
  | script (tx input : Nat) (mandatory : Bool) (e : ScriptError)
  /-- The coinbase pays more than the fees and the subsidy: `bad-cb-amount` (line 2001). -/
  | coinbaseAmount
  /-- A sum left the `int64_t` range. Not a Core result. -/
  | outOfDomain
  /-- The CSV state is `ACTIVE`. Not a Core result. -/
  | csvActive
  /-- A script needed a capability that `verifyLegacySpend` does not have. Not a Core result. -/
  | scriptUnsupported (reason : Unsupported)
  /-- The subsidy ran out of fuel. Not a Core result. -/
  | subsidy (e : SubsidyError)
  /-- The transaction at `tx` is not a coinbase and has the ID of an entry that is not pruned. Not a Core result. -/
  | newCoinsExist (tx : Nat)
  /-- The transaction at `tx` has `2^32` or more inputs or outputs. Not a Core result. -/
  | contextBounds (tx : Nat)
  deriving DecidableEq, Repr

/-- Core's reject reason for each failure, and `none` for a result outside the model. -/
def ConnectBlockError.rejectReason : ConnectBlockError → Option String
  | .checkBlock e => some e.rejectReason
  | .bip30 => some "bad-txns-BIP30"
  | .inputsMissingOrSpent _ => some "bad-txns-inputs-missingorspent"
  | .sigOps => some "bad-blk-sigops"
  | .txInputs _ e => e.rejectReason
  | .script _ _ true e => some s!"mandatory-script-verify-flag-failed ({e.description})"
  | .script _ _ false e => some s!"non-mandatory-script-verify-flag ({e.description})"
  | .coinbaseAmount => some "bad-cb-amount"
  | .outOfDomain | .csvActive | .scriptUnsupported _ | .subsidy _ | .newCoinsExist _ | .contextBounds _ => none

/-- The denial-of-service score of each failure: the score of `CheckBlock` or `CheckTxInputs`, 0 for a non-mandatory script failure, and 100 for the others. -/
def ConnectBlockError.dosScore : ConnectBlockError → Nat
  | .checkBlock e => e.dosScore
  | .txInputs _ e => e.dosScore
  | .script _ _ false _ => 0
  | .bip30 | .inputsMissingOrSpent _ | .sigOps | .script _ _ true _ | .coinbaseAmount => 100
  | .outOfDomain | .csvActive | .scriptUnsupported _ | .subsidy _ | .newCoinsExist _ | .contextBounds _ => 0

/-- The reject code of each failure: `REJECT_NONSTANDARD`, `0x40`, for a non-mandatory script failure, and `REJECT_INVALID`, `0x10`, for the others (D84). -/
def ConnectBlockError.rejectCode : ConnectBlockError → Nat
  | .checkBlock e => e.rejectCode
  | .script _ _ false _ => 0x40
  | .outOfDomain | .csvActive | .scriptUnsupported _ | .subsidy _ | .newCoinsExist _ | .contextBounds _ => 0
  | _ => 0x10

/-- True for Core's rejections, and false for the results outside the model. -/
def ConnectBlockError.isRejection (e : ConnectBlockError) : Bool := e.rejectReason.isSome

/-- The coin of each input, in order, or `none` when Core's `HaveInputs` fails (D113, `src/coins.cpp`, lines 284 to 297). -/
def lookupInputs (s : CoinSet) : List TxIn → Option (List Coin)
  | [] => some []
  | input :: rest =>
    match s.coin input.prevout with
    | none => none
    | some c => (lookupInputs s rest).map (c :: ·)

/--
Core's `CCoinsViewCache::GetValueIn` (D113, `src/coins.cpp`, lines 272 to 282) from the partial sum `acc`: the sum of the amounts of the coins.
Core adds with no range check. The result is `none` when a partial sum leaves the `int64_t` range.
-/
def getValueIn (acc : Int) : List Coin → Option Int
  | [] => some acc
  | c :: rest => if inInt64Range (acc + c.value) then getValueIn (acc + c.value) rest else none

/--
The statement `nFees += view.GetValueIn(tx) - tx.GetValueOut()` (line 1974).
The result is `none` when the sum of the coins, the difference or the new `nFees` leaves the `int64_t` range.
-/
def addFee (nFees : Int) (coins : List Coin) (valueOut : Int) : Option Int :=
  match getValueIn 0 coins with
  | none => none
  | some total =>
    if inInt64Range (total - valueOut) && inInt64Range (nFees + (total - valueOut)) then
      some (nFees + (total - valueOut))
    else none

/-- The context of input `input` of `tx` for `verifyLegacySpend`, or `none` outside its bounds. -/
def inputContext? (tx : Transaction) (input : Nat) : Option InputContext :=
  if h : input < tx.inputs.val.length ∧ tx.inputs.val.length < 2 ^ 32 ∧ tx.outputs.val.length < 2 ^ 32 then
    some ⟨tx, UInt32.ofNat input, by
      have : input < 2 ^ 32 := by omega
      simpa [UInt32.toNat_ofNat', Nat.mod_eq_of_lt this] using h.1, h.2.1, h.2.2⟩
  else none

/--
The script check of one input in `CheckInputs` (D114, lines 1483 to 1516), with the classification of a failure.
`txIndex` and `input` name the input in the error.
-/
def checkInputScript (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat) (tx : Transaction)
    (input : Nat) (coin : Coin) : Except ConnectBlockError Unit :=
  match inputContext? tx input with
  | none => .error (.contextBounds txIndex)
  | some ctx =>
    match verifyLegacySpend ctx coin.out.scriptPubKey flags verify with
    | .accepted => .ok ()
    | .unsupported u => .error (.scriptUnsupported u)
    | .rejected e =>
      if flags &&& standardNotMandatoryVerifyFlags != 0 then
        match verifyLegacySpend ctx coin.out.scriptPubKey (flags &&& ~~~standardNotMandatoryVerifyFlags) verify with
        | .accepted => .error (.script txIndex input false e)
        | .rejected _ => .error (.script txIndex input true e)
        | .unsupported u => .error (.scriptUnsupported u)
      else .error (.script txIndex input true e)

/-- The script loop of `CheckInputs` (D114, lines 1482 to 1516) from input `input`: the first failure, in input order. -/
def checkInputScripts (verify : SignatureVerifier) (flags : UInt32) (txIndex : Nat) (tx : Transaction)
    (input : Nat) : List Coin → Except ConnectBlockError Unit
  | [] => .ok ()
  | coin :: rest =>
    match checkInputScript verify flags txIndex tx input coin with
    | .error e => .error e
    | .ok () => checkInputScripts verify flags txIndex tx (input + 1) rest

/--
Core's `CheckInputs` (D114, lines 1462 to 1518) for a transaction that is not a coinbase, with script checks and no check queue.
`checkTxInputs` runs first, at the spend height `height`. Then the script of each input runs, in input order.
-/
def checkInputs (verify : SignatureVerifier) (height : Nat) (flags : UInt32) (txIndex : Nat)
    (tx : Transaction) (coins : List Coin) : Except ConnectBlockError Unit :=
  match checkTxInputs height coins tx.valueOut with
  | .error .outOfDomain => .error .outOfDomain
  | .error e => .error (.txInputs txIndex e)
  | .ok () => checkInputScripts verify flags txIndex tx 0 coins

/-- The state of the transaction loop of `ConnectBlock`. -/
structure ConnectState where
  /-- The view: the coin set after the transactions so far. -/
  coins : CoinSet
  /-- `nFees`. -/
  fees : Int
  /-- `nSigOpsCost`. -/
  sigOpsCost : Nat
  /-- The changes so far, newest first. -/
  changes : List CoinChange

/-- The spends of `UpdateCoins` (D113, lines 1370 to 1386): each input's output becomes null, in input order. -/
def spendInputs (s : CoinSet) : List TxIn → CoinSet
  | [] => s
  | input :: rest => spendInputs (s.spend input.prevout) rest

/--
One pass of the transaction loop of `ConnectBlock` (lines 1935 to 1993), for the transaction at `index`.
The steps are those of the module documentation, item 5.
-/
def connectTransaction (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) (index : Nat)
    (st : ConnectState) (tx : Transaction) : Except ConnectBlockError ConnectState :=
  match (if tx.isCoinBase then some [] else lookupInputs st.coins tx.inputs.val) with
  | none => .error (.inputsMissingOrSpent index)
  | some coins =>
    let cost := st.sigOpsCost + getTransactionSigOpCost tx coins (hasFlag flags ScriptFlags.p2sh)
    if cost > maxBlockSigOpsCost then .error .sigOps
    else
      match (if tx.isCoinBase then some st.fees else addFee st.fees coins tx.valueOut) with
      | none => .error .outOfDomain
      | some fees =>
        match (if tx.isCoinBase then .ok () else checkInputs verify ctx.height flags index tx coins) with
        | .error e => .error e
        | .ok () =>
          let spentSet := if tx.isCoinBase then st.coins else spendInputs st.coins tx.inputs.val
          if !tx.isCoinBase && spentSet.haveUnspent tx.txid then .error (.newCoinsExist index)
          else
            let spent := (tx.inputs.val.zip coins).map fun (input, coin) => CoinChange.spent input.prevout coin
            let created := (TxCoins.ofTx tx ctx.height).coins.map fun (o, c) => CoinChange.created o c
            .ok ⟨spentSet.addTx tx ctx.height, fees, cost, created.reverse ++ spent.reverse ++ st.changes⟩

/-- The transaction loop of `ConnectBlock` (lines 1935 to 1993) from the transaction at `index`. -/
def connectTransactions (verify : SignatureVerifier) (ctx : ConnectContext) (flags : UInt32) (index : Nat)
    (st : ConnectState) : List Transaction → Except ConnectBlockError ConnectState
  | [] => .ok st
  | tx :: rest =>
    match connectTransaction verify ctx flags index st tx with
    | .error e => .error e
    | .ok st' => connectTransactions verify ctx flags (index + 1) st' rest

/--
Core's `ConnectBlock` on mainnet (D114, lines 1783 to 2009), with the first failing check as its error.
Core returns `true` exactly when the result is `.ok`, for an input inside the model.

`verify` is the elliptic-curve check of `verifyLegacySpend`.
`fJustCheck` selects the flags of `CheckBlock`, as in Core. The definition returns before Core's writes, which follow line 2009.
`s` is the view, whose best block is the predecessor.
The module documentation lists the checks in Core's order.
-/
def connectBlock (verify : SignatureVerifier) (fJustCheck : Bool) (ctx : ConnectContext) (s : CoinSet)
    (b : Block) : Except ConnectBlockError ConnectResult :=
  match checkBlock .mainnet (!fJustCheck) (!fJustCheck) b with
  | .error e => .error (.checkBlock e)
  | .ok () =>
    if some b.header.pure.getHash == genesisHash? .mainnet then .ok ⟨s, []⟩
    else
      let txs := b.transactions
      if enforceBip30 ctx.bip34Ancestor && txs.any (fun tx => s.haveUnspent tx.txid) then .error .bip30
      else if ctx.csvActive then .error .csvActive
      else
        match connectTransactions verify ctx (connectScriptFlags ctx.height) 0 ⟨s, 0, 0, []⟩ txs with
        | .error e => .error e
        | .ok st =>
          match getDogecoinBlockSubsidy subsidyFuel ctx.height ctx.prevHash with
          | .error e => .error (.subsidy e)
          | .ok subsidy =>
            if !inInt64Range (st.fees + (subsidy : Int)) then .error .outOfDomain
            else if (match txs with | [] => 0 | coinbase :: _ => coinbase.valueOut) > st.fees + (subsidy : Int) then
              .error .coinbaseAmount
            else .ok ⟨st.coins, st.changes.reverse⟩

end DogeLib.Block
