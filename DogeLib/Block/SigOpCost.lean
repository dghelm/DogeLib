module

public import DogeLib.Block.Check
public import DogeLib.Block.Coins
public import DogeLib.Script.Verify

/-!
# The signature-operation cost of a transaction

Core's `GetTransactionSigOpCost` on mainnet, with the count of Pay to Script Hash (P2SH) inputs.

The sources are at the Core pin (SOURCES.md):

- `GetP2SHSigOpCount` and `GetTransactionSigOpCost`, `src/validation.cpp`, lines 489 to 521 (D114).
- `CScript::GetSigOpCount(bool fAccurate)` and `CScript::GetSigOpCount(const CScript& scriptSig)`, `src/script/script.cpp`, lines 156 to 201 (D107, D115).

## The accurate count

With `fAccurate` true, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` add the number that the opcode before them encodes, when that opcode is `OP_1` to `OP_16`.
Otherwise they add `MAX_PUBKEYS_PER_MULTISIG`, as in the inaccurate count.
The opcode before the first instruction is `OP_INVALIDOPCODE` (`0xff`).

## The count of a P2SH input

Core counts an input only when the output that it spends has the P2SH template (lines 497 to 498).
`CScript::GetSigOpCount(const CScript& scriptSig)` then reads `scriptSig` with `GetOp`.
A read that fails gives 0, and so does an opcode above `OP_16`.
Otherwise the redeem script is the data of the last instruction, and the count is its accurate count.
The data of an opcode that pushes nothing is empty, and an empty `scriptSig` gives the empty redeem script, so both count 0.

## The cost

`GetTransactionSigOpCost` adds three terms (lines 502 to 521):

1. The legacy count times `WITNESS_SCALE_FACTOR`.
2. For a transaction that is not a coinbase, with `SCRIPT_VERIFY_P2SH`: the P2SH count times `WITNESS_SCALE_FACTOR`.
3. The witness count, which `CountWitnessSigOps` gives as 0 without `SCRIPT_VERIFY_WITNESS` (`src/script/interpreter.cpp`, lines 1548 to 1550). `ConnectBlock` never sets that flag on mainnet, so the definition has no third term.

## Integer semantics

`GetLegacySigOpCount` and `GetP2SHSigOpCount` return `unsigned int`, and each product with the `int` constant `WITNESS_SCALE_FACTOR` is computed in `unsigned int`, modulo `2^32`.
The sum of the two products is an `int64_t`.
The definitions reduce each count and each product modulo `2^32`, and add in the natural numbers.
Each product is below `2^32`, so the sum of two is below `2^63`.
-/

@[expose] public section
namespace DogeLib.Block
open DogeLib.Transaction
open DogeLib.Script

/-- `OP_1` (`src/script/script.h`, line 54). -/
def op1 : UInt8 := 0x51

/-- `OP_16` (`src/script/script.h`, line 70). -/
def op16 : UInt8 := 0x60

/-- `OP_INVALIDOPCODE` (`src/script/script.h`, line 187): the value of `lastOpcode` before the first instruction. -/
def opInvalidOpcode : UInt8 := 0xff

/--
The signature operations that one opcode adds with `fAccurate` true, after the opcode `last` (D107, lines 166 to 174).
`OP_CHECKSIG` and `OP_CHECKSIGVERIFY` add 1.
`OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` add `DecodeOP_N(last)`, which is `last - 0x50`, when `last` is `OP_1` to `OP_16`, and `MAX_PUBKEYS_PER_MULTISIG` otherwise.
-/
def opcodeSigOpsAccurate (last opcode : UInt8) : Nat :=
  if opcode = opCheckSig ∨ opcode = opCheckSigVerify then 1
  else if opcode = opCheckMultiSig ∨ opcode = opCheckMultiSigVerify then
    if op1 ≤ last ∧ last ≤ op16 then last.toNat - 0x50 else maxPubkeysPerMultisig
  else 0

/-- The accurate count of a list of opcodes, where `last` is the opcode before the list. -/
def accurateSigOps (last : UInt8) : List UInt8 → Nat
  | [] => 0
  | opcode :: rest => opcodeSigOpsAccurate last opcode + accurateSigOps opcode rest

/-- One step of the accurate count: the state holds the opcode before `opcode` and the count so far, and the step adds `opcodeSigOpsAccurate`. -/
def accurateStep (p : UInt8 × Nat) (opcode : UInt8) : UInt8 × Nat :=
  (opcode, p.2 + opcodeSigOpsAccurate p.1 opcode)

/--
Core's `CScript::GetSigOpCount(true)` (D107, lines 156 to 177), as a natural number.
It reads the instructions with `foldOps`, as the inaccurate count does, and stops at the first failed read.
`getSigOpCountAccurate_eq_scanOps` proves it equal to `accurateSigOps` over the opcodes of `scanOps`.
Core's result is this number modulo `2^32`.
-/
def getSigOpCountAccurate (script : List UInt8) : Nat :=
  (foldOps accurateStep (opInvalidOpcode, 0) script).2

/--
The loop of `CScript::GetSigOpCount(const CScript& scriptSig)` (D115, lines 189 to 196) from cursor `pc`.
`data` is the data of the instruction before the cursor.
The result is `none` when a read fails or an opcode is above `OP_16`, and otherwise the data of the last instruction.
-/
def lastPushFrom (script : List UInt8) (pc : Nat) (data : List UInt8) : Option (List UInt8) :=
  match hr : readInstruction script pc with
  | .atEnd => some data
  | .truncated .. => none
  | .instruction i =>
    have := readInstruction_progress hr
    if i.opcode > op16 then none else lastPushFrom script i.next i.pushed
termination_by script.length - pc
decreasing_by omega

/--
The loop of `lastPushFrom` with the reader `nextOp`, from the bytes `bs` after the cursor.
`readInstruction` drops the bytes before the cursor and measures the rest at each instruction, so `lastPushFrom` is quadratic in the length of the script.
This loop is linear, and `lastPushFrom_eq_lastPushLoop` proves the two equal.
-/
def lastPushLoop (bs : List UInt8) (data : List UInt8) : Option (List UInt8) :=
  match _h : nextOp bs with
  | none => if bs.isEmpty then some data else none
  | some s => if s.opcode > op16 then none else lastPushLoop s.rest s.data
termination_by bs.length
decreasing_by exact nextOp_rest_length ‹_›

/--
Core's `CScript::GetSigOpCount(const CScript& scriptSig)` (D115, lines 180 to 201) for a P2SH `scriptPubKey`.
A `scriptSig` with a failed read or an opcode above `OP_16` counts 0.
Otherwise the result is the accurate count of the data that the last instruction of `scriptSig` pushes.
It reads `scriptSig` with `lastPushLoop`. `p2shSigOpCount_eq_lastPushFrom` proves it equal to the same count with `lastPushFrom`.
-/
def p2shSigOpCount (scriptSig : List UInt8) : Nat :=
  match lastPushLoop scriptSig [] with
  | none => 0
  | some redeem => getSigOpCountAccurate redeem

/--
Core's `GetP2SHSigOpCount` (D114, lines 489 to 502) for a transaction that is not a coinbase, as a natural number.
`coins` holds the coin that each input spends, in input order.
An input counts only when its coin has the P2SH template.
Core's result is this number modulo `2^32`.
-/
def getP2SHSigOpCount (tx : Transaction) (coins : List Coin) : Nat :=
  ((tx.inputs.val.zip coins).map fun (input, coin) =>
    if isPayToScriptHash coin.out.scriptPubKey.bytes.val then p2shSigOpCount input.scriptSig.bytes.val
    else 0).sum

/--
Core's `GetTransactionSigOpCost` (D114, lines 504 to 521) without `SCRIPT_VERIFY_WITNESS`.
`coins` holds the coin that each input spends, in input order. A coinbase reads none.
`p2sh` is whether the flags have `SCRIPT_VERIFY_P2SH`.
-/
def getTransactionSigOpCost (tx : Transaction) (coins : List Coin) (p2sh : Bool) : Nat :=
  let legacy := tx.getLegacySigOpCount % 2 ^ 32 * witnessScaleFactor % 2 ^ 32
  if tx.isCoinBase || !p2sh then legacy
  else legacy + getP2SHSigOpCount tx coins % 2 ^ 32 * witnessScaleFactor % 2 ^ 32

end DogeLib.Block
