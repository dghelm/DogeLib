module

public import DogeLib.Transaction.LegacySighash

/-!
# `Transaction.SigOps`

The legacy count of signature operations: Core's `GetLegacySigOpCount`, with `CScript::GetSigOpCount` in its inaccurate mode.

The sources are at the Core pin (SOURCES.md):

- `GetLegacySigOpCount`, `src/validation.cpp`, lines 475 to 487 (D106).
- `CScript::GetSigOpCount(bool fAccurate)`, `src/script/script.cpp`, lines 156 to 177, and `MAX_PUBKEYS_PER_MULTISIG`, `src/script/script.h`, line 28 (D107).

The count reads a script with `GetOp`, as the legacy signature serializer does, so it uses `scanOps` of `DogeLib.Transaction.LegacySighash`.
It stops at the first instruction that `GetOp` fails to read, and keeps the count of the instructions before it.
It reads every `scriptSig`, the one of a coinbase included, and every `scriptPubKey`.

This module defines the call with `fAccurate` false only.
The accurate mode, which reads the opcode before `OP_CHECKMULTISIG`, belongs to the count of Pay to Script Hash (P2SH) inputs, and is not defined here.

## Integer semantics

Core counts in `unsigned int`, so its results are modulo `2^32`.
The definitions here count in the natural numbers, with no wrap.
Core's value is the value here modulo `2^32`, and the two are equal while the count is below `2^32`.
`Script.getSigOpCount_le` bounds the count of a script by 20 times its length.

The correspondence with `GetOp` covers a script of fewer than `2^31` bytes, the domain of `readOp`.
-/

@[expose] public section

namespace DogeLib.Transaction

/-- `OP_CHECKSIG` (`src/script/script.h`, line 161). -/
def opCheckSig : UInt8 := 0xac

/-- `OP_CHECKSIGVERIFY` (`src/script/script.h`, line 162). -/
def opCheckSigVerify : UInt8 := 0xad

/-- `OP_CHECKMULTISIG` (`src/script/script.h`, line 163). -/
def opCheckMultiSig : UInt8 := 0xae

/-- `OP_CHECKMULTISIGVERIFY` (`src/script/script.h`, line 164). -/
def opCheckMultiSigVerify : UInt8 := 0xaf

/-- `MAX_PUBKEYS_PER_MULTISIG` (D107). -/
def maxPubkeysPerMultisig : Nat := 20

/--
The signature operations that one opcode adds with `fAccurate` false (D107, lines 166 to 174).
`OP_CHECKSIG` and `OP_CHECKSIGVERIFY` add 1.
`OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` add `MAX_PUBKEYS_PER_MULTISIG`, whatever opcode comes before them.
Every other opcode adds 0.
-/
def opcodeSigOps (opcode : UInt8) : Nat :=
  if opcode = opCheckSig ∨ opcode = opCheckSigVerify then 1
  else if opcode = opCheckMultiSig ∨ opcode = opCheckMultiSigVerify then maxPubkeysPerMultisig
  else 0

/--
Core's `CScript::GetSigOpCount(false)` (D107, lines 156 to 177), as a natural number.

The loop reads instructions with `GetOp` until the end of the script or the first failed read, and adds `opcodeSigOps` of each opcode.
`scanOps` gives exactly those instructions.
The data of a push is not read as opcodes.
Core's result is this number modulo `2^32`.
-/
def Script.getSigOpCount (s : Script) : Nat :=
  (((scanOps s.bytes.val).1.map fun o => opcodeSigOps o.1)).sum

/--
Core's `GetLegacySigOpCount` (D106, lines 475 to 487), as a natural number.
It adds `Script.getSigOpCount` of the `scriptSig` of every input, then of the `scriptPubKey` of every output.
Core's result is this number modulo `2^32`.
-/
def Transaction.getLegacySigOpCount (tx : Transaction) : Nat :=
  ((tx.inputs.val.map fun i => i.scriptSig.getSigOpCount).sum) +
    ((tx.outputs.val.map fun o => o.scriptPubKey.getSigOpCount).sum)

end DogeLib.Transaction
