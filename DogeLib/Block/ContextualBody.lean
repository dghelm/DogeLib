module

public import DogeLib.Block.Check
public import DogeLib.Block.VersionBits
public import DogeLib.Script.Number

/-!
# The body of `ContextualCheckBlock`

Core's `ContextualCheckBlock` (SOURCES.md, D110, lines 3121 to 3203) on mainnet.
The function checks a block against the height that its predecessor gives, the version-bits states of CSV and SegWit, and the block's own weight.
It runs the checks of design record 0010, section 4, in Core's order and returns the first failure:

1. Every transaction is final at the candidate height and the lock-time cutoff: `bad-txns-nonfinal`, score 10 (lines 3139 to 3143).
2. From `BIP34Height` (1,034,383), the coinbase `scriptSig` starts with the serialized height: `bad-cb-height`, score 100 (lines 3146 to 3152).
3. With SegWit active and a witness commitment, the witness nonce and the witness Merkle commitment: `bad-witness-nonce-size` and `bad-witness-merkle-match` (lines 3163 to 3181). On mainnet SegWit never activates, so this module takes an active SegWit state as an input outside the comparison domain.
4. Without a checked witness commitment, no transaction has witness data: `unexpected-witness`, score 100 (lines 3183 to 3188).
5. The block weight is at most `MAX_BLOCK_WEIGHT`: `bad-blk-weight`, score 100 (line 3198).

The lock-time cutoff is the predecessor's median time past when CSV is active, and otherwise the block's own time (lines 3128 to 3136).
On mainnet CSV never activates (`csv_never_lockedIn`), so the cutoff is the block time, and the body reads its `prevMedianTimePast` input only in the active case, which mainnet never reaches.

## The version-bits states

The body takes the CSV and SegWit states as inputs, where Core calls `VersionBitsState` (lines 3130 and 3161).
The oracle computes them with `versionBitsShortcut` from the aligned boundary's median time past, and the harness lets Core compute them from the block index that the request builds.
The body reads only whether each state is `ACTIVE`.

## The weight and the unreachable reasons

`Block.weight` follows `GetBlockWeight` (D110, `src/primitives/block.cpp`, lines 43 to 49): three times the base size plus the full size.
When no transaction and no AuxPoW payload transaction has witness data, the full size equals the base size, so the weight is four times the base size.

`bad-blk-weight` is reachable when this body runs alone, because the body has no base-size check.
In `block.validate` (stage 0010b) `CheckBlock` runs first and bounds the base size by `MAX_BLOCK_BASE_SIZE`.
`contextualBody_badBlkWeight_unreachable_after_checkBlock` (in `DogeLib.Block.Proofs.ContextualBody`) shows that the weight branch then cannot fire, under the hypothesis that the AuxPoW payload transaction has no witness data.
That hypothesis excludes some real mainnet blocks: pull request #152 found that the AuxPoW parent coinbase of blocks 6,455,642, 6,456,071 and 6,456,247 carries witness data that Core accepts.
The theorem does not cover a block whose AuxPoW payload transaction has witness data.

## Source

The definitions follow Core's statements in order, with a named error for each `return state.DoS(...)`.
The source is MIT/X11-licensed, with its licence in `LICENSES/dogecoin-core-MIT.txt`.
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
open DogeLib.Serialization

/-- `LOCKTIME_THRESHOLD` (D24, `src/script/script.h`, line 35): a lock time below it is a block height, and otherwise a time. -/
def lockTimeThreshold : Nat := 500000000

/-- `CTxIn::SEQUENCE_FINAL` (D4, `src/primitives/transaction.h`, line 76). -/
def contextualSequenceFinal : UInt32 := 0xffffffff

/-- `MAX_BLOCK_WEIGHT` (D110, `src/consensus/consensus.h`, line 15). -/
def maxBlockWeight : Nat := 4000000

/-- `BIP34Height` on mainnet (D100, line 84): the first height whose coinbase carries the block height. -/
def bip34Height : Nat := 1034383

/--
Core's `IsFinalTx` (D110, lines 258 to 269) for a transaction, the candidate height and the lock-time cutoff.

A lock time of 0 is final.
Otherwise the lock time is compared with the height when it is below `LOCKTIME_THRESHOLD`, and with the cutoff time otherwise.
A lock time below that value is final.
Otherwise the transaction is final exactly when every input has the sequence `SEQUENCE_FINAL`.

Core widens `nLockTime` to `int64_t`, which is `lockTime.toNat`, and the comparison with the `int` height and the `int64_t` cutoff uses `Int`.
-/
def isFinalTx (tx : Transaction) (height : Nat) (blockTime : Int) : Bool :=
  if tx.lockTime == 0 then true
  else
    let cutoff := if tx.lockTime.toNat < lockTimeThreshold then (height : Int) else blockTime
    if (tx.lockTime.toNat : Int) < cutoff then true
    else tx.inputs.val.all (fun i => i.sequence == contextualSequenceFinal)

/--
The coinbase `scriptSig` prefix that BIP34 requires at `height`, as Core builds it with `CScript() << nHeight` (D110, line 3148).
Every mainnet `BIP34Height` is above 16, so `CScript::push_int64` writes `CScriptNum::serialize(nHeight)` as a pushed byte string (D24, lines 379 to 393).
The serialized string has at most five bytes, so the push is one length byte and those bytes.
`DogeLib.Script.ScriptNum.encode` is `CScriptNum::serialize`.
-/
def coinbaseHeightPrefix (height : Nat) : List UInt8 :=
  let s := DogeLib.Script.ScriptNum.encode (height : Int)
  UInt8.ofNat s.length :: s

/-- The full size of a block: `GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION)` (D108, D110), the length of the witness-allowed encoding. -/
def Block.fullSize (b : Block) : Nat := (Block.encode .allowWitness b).length

/--
`GetBlockWeight` (D110, `src/primitives/block.cpp`, lines 43 to 49): three times the base size plus the full size.
The base size drops every witness stack, and the full size keeps them, so the difference is the witness data of the transactions and of any AuxPoW payload transaction.
-/
def Block.weight (b : Block) : Nat := Block.baseSize b * 3 + Block.fullSize b

/-- Whether a transaction has a non-empty witness stack: Core's `CTransaction::HasWitness` (D4, lines 371 to 379). -/
def WitnessTransaction.anyWitness (txs : List WitnessTransaction) : Bool :=
  txs.any WitnessTransaction.hasWitness

/-- The failures of `ContextualCheckBlock` on mainnet, and the adapter errors for an input outside the comparison domain. -/
inductive ContextualBodyError where
  /-- A transaction is not final: `bad-txns-nonfinal`, score 10 (line 3141). -/
  | nonFinal
  /-- The coinbase `scriptSig` does not start with the serialized height: `bad-cb-height`, score 100 (line 3150). -/
  | badCbHeight
  /-- A transaction has witness data without a checked commitment: `unexpected-witness`, score 100 (line 3186). -/
  | unexpectedWitness
  /-- The block weight is above `MAX_BLOCK_WEIGHT`: `bad-blk-weight`, score 100 (line 3198). -/
  | badBlkWeight
  /-- Adapter error: the block has no coinbase input, where Core reads `block.vtx[0]->vin[0]`. The comparison never sends such a block. -/
  | noCoinbase
  /-- Adapter error: the SegWit state is `ACTIVE`, which never happens on mainnet and whose witness-commitment branch this module does not model. -/
  | segwitActive
  deriving DecidableEq, Repr

/-- Core's reject reason for each failure (D110, lines 3141, 3150, 3186 and 3198), and `none` for an adapter error. -/
def ContextualBodyError.rejectReason : ContextualBodyError → Option String
  | .nonFinal => some "bad-txns-nonfinal"
  | .badCbHeight => some "bad-cb-height"
  | .unexpectedWitness => some "unexpected-witness"
  | .badBlkWeight => some "bad-blk-weight"
  | .noCoinbase | .segwitActive => none

/-- The denial-of-service score of each failure: 10 for `bad-txns-nonfinal` (line 3141), and 100 for the other three (lines 3150, 3186 and 3198). -/
def ContextualBodyError.dosScore : ContextualBodyError → Nat
  | .nonFinal => 10
  | .badCbHeight | .unexpectedWitness | .badBlkWeight => 100
  | .noCoinbase | .segwitActive => 0

/-- The reject code of each failure: `REJECT_INVALID`, `0x10` (D84). An adapter error has no Core code. -/
def ContextualBodyError.rejectCode : ContextualBodyError → Nat
  | .noCoinbase | .segwitActive => 0
  | _ => 0x10

/-- True for the four Core rejections, and false for the adapter errors. -/
def ContextualBodyError.isRejection : ContextualBodyError → Bool
  | .nonFinal | .badCbHeight | .unexpectedWitness | .badBlkWeight => true
  | .noCoinbase | .segwitActive => false

/-- The finality loop of `ContextualCheckBlock` (D110, lines 3139 to 3143): the first non-final transaction, or `ok`. -/
def checkFinality (height : Nat) (cutoff : Int) : List Transaction → Except ContextualBodyError Unit
  | [] => .ok ()
  | tx :: rest =>
    if isFinalTx tx height cutoff then checkFinality height cutoff rest
    else .error .nonFinal

/--
Core's `ContextualCheckBlock` on mainnet (D110, lines 3121 to 3203), with the first failing check as its error.

`height` is the candidate height, the predecessor's height plus one.
`prevMedianTimePast` is the predecessor's median time past, used for the lock-time cutoff only when CSV is active.
`csvActive` and `segwitActive` are whether `VersionBitsState` returns `ACTIVE` for CSV and SegWit.

The function runs the checks in Core's order.
With an active SegWit state it returns the adapter error `segwitActive`, which the mainnet comparison never reaches.
-/
def contextualCheckBlockBody (height : Nat) (prevMedianTimePast : Int) (csvActive segwitActive : Bool)
    (b : Block) : Except ContextualBodyError Unit :=
  let cutoff := if csvActive then prevMedianTimePast else (b.header.pure.nTime.toNat : Int)
  match checkFinality height cutoff b.transactions with
  | .error e => .error e
  | .ok () =>
    match b.vtx.val with
    | [] => .error .noCoinbase
    | coinbase :: _ =>
      match coinbase.tx.inputs.val with
      | [] => .error .noCoinbase
      | input :: _ =>
        if bip34Height ≤ height ∧ ¬ (coinbaseHeightPrefix height).isPrefixOf input.scriptSig.bytes.val then
          .error .badCbHeight
        else if segwitActive then .error .segwitActive
        else if WitnessTransaction.anyWitness b.vtx.val then .error .unexpectedWitness
        else if maxBlockWeight < Block.weight b then .error .badBlkWeight
        else .ok ()

end DogeLib.Block
