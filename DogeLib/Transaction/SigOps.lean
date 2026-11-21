module

public import DogeLib.Transaction.LegacySighash

/-!
# `Transaction.SigOps`

The legacy count of signature operations: Core's `GetLegacySigOpCount`, with `CScript::GetSigOpCount` in its inaccurate mode.

The sources are at the Core pin (SOURCES.md):

- `GetLegacySigOpCount`, `src/validation.cpp`, lines 475 to 487 (D106).
- `CScript::GetSigOpCount(bool fAccurate)`, `src/script/script.cpp`, lines 156 to 177, and `MAX_PUBKEYS_PER_MULTISIG`, `src/script/script.h`, line 28 (D107).

The count reads a script with `GetOp`, as the legacy signature serializer does.
It stops at the first instruction that `GetOp` fails to read, and keeps the count of the instructions before it.
It reads every `scriptSig`, the one of a coinbase included, and every `scriptPubKey`.

## The reader

`scanOps` of `DogeLib.Transaction.LegacySighash` lists the instructions that `GetOp` reads.
Its reader `readOp` takes the length of the rest of the script at each push.
So a script of n one-byte pushes costs about n^2 steps (issue #149).
The count here reads with `nextOp`, which steps over the data of a push with `dropExact` and never measures the rest.
`foldOps` folds a function over the opcodes that `nextOp` reads, in tail position.

The reading takes steps linear in the length of the script.
A fold whose step takes constant time, such as each count here, is linear too.
`DogeLib.Transaction.Proofs.SigOps` proves that `nextOp` reads the instruction that `readOp` reads, and that `foldOps` folds over the opcodes of `scanOps`.

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

/-- `bs` without its first `n` bytes, or `none` when `bs` has fewer than `n` bytes. It takes at most `n` steps. -/
def dropExact : Nat → List UInt8 → Option (List UInt8)
  | 0, bs => some bs
  | _ + 1, [] => none
  | n + 1, _ :: bs => dropExact n bs

/-- One instruction that `nextOp` reads: its opcode, the bytes after its length field, the size of its data, and the bytes after the instruction. -/
structure OpStep where
  /-- The opcode of the instruction. -/
  opcode : UInt8
  /-- The bytes after the opcode and its length field. The data of the instruction is their first `size` bytes. -/
  tail : List UInt8
  /-- The number of bytes of data. It is 0 for an opcode that pushes nothing. -/
  size : Nat
  /-- The bytes after the instruction. -/
  rest : List UInt8

/-- The data that the instruction pushes: the first `size` bytes of `tail`. -/
def OpStep.data (s : OpStep) : List UInt8 := s.tail.take s.size

/-- A push of `size` bytes from `r`, after the opcode and its length field: the instruction, or `none` when `r` has fewer than `size` bytes. -/
def pushStep (opcode : UInt8) (size : Nat) (r : List UInt8) : Option OpStep :=
  match dropExact size r with
  | some rest => some ⟨opcode, r, size, rest⟩
  | none => none

/--
One instruction from the start of a script, as `CScript::GetOp2` reads it (D24, lines 502 to 552), or `none` when `GetOp2` returns false.
It reads the same opcodes and sizes as `readOp`, in the same order of tests.
It does not copy the data of a push, and it tests the size of the data with `dropExact`, in steps of that size only.
-/
def nextOp : List UInt8 → Option OpStep
  | [] => none
  | op :: r =>
    if op < 0x4c then pushStep op op.toNat r
    else if op = 0x4c then
      match r with
      | b :: r' => pushStep op b.toNat r'
      | [] => none
    else if op = 0x4d then
      match r with
      | b0 :: b1 :: r' => pushStep op (b0.toNat + 2 ^ 8 * b1.toNat) r'
      | _ => none
    else if op = 0x4e then
      match r with
      | b0 :: b1 :: b2 :: b3 :: r' =>
        pushStep op (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat) r'
      | _ => none
    else some ⟨op, r, 0, r⟩

/-- For every `n` and all bytes `bs`: the bytes that `dropExact` leaves are no more than `bs`. -/
theorem dropExact_length_le : ∀ {n : Nat} {bs r : List UInt8}, dropExact n bs = some r → r.length ≤ bs.length
  | 0, _, _, h => by cases h; exact Nat.le_refl _
  | _ + 1, [], _, h => by cases h
  | _ + 1, _ :: _, _, h => Nat.le_succ_of_le (dropExact_length_le (bs := _) h)

/-- For every push that `pushStep` reads from `r`, the bytes after it are no more than `r`. -/
theorem pushStep_rest_length {op : UInt8} {n : Nat} {r : List UInt8} {s : OpStep}
    (h : pushStep op n r = some s) : s.rest.length ≤ r.length := by
  unfold pushStep at h
  split at h
  · cases h; exact dropExact_length_le ‹_›
  · cases h

/-- For all bytes `bs`: an instruction that `nextOp` reads leaves fewer bytes than `bs`. `foldOps` needs this to terminate. -/
theorem nextOp_rest_length {bs : List UInt8} {s : OpStep} (h : nextOp bs = some s) :
    s.rest.length < bs.length := by
  match bs with
  | [] => simp [nextOp] at h
  | op :: t =>
    simp only [nextOp] at h
    split at h
    · have := pushStep_rest_length h; simp; omega
    · split at h
      · split at h
        · have := pushStep_rest_length h; simp; omega
        · cases h
      · split at h
        · split at h
          · have := pushStep_rest_length h; simp; omega
          · cases h
        · split at h
          · split at h
            · have := pushStep_rest_length h; simp; omega
            · cases h
          · cases h; simp

/--
The loop `while (GetOp(pc, opcode))` over a script, with the step `f` on each opcode that it reads, from the value `acc`.
It stops at the end of the script or at the first failed read.
The recursive call is in tail position, so the loop runs in constant stack space.
-/
def foldOps {β : Type} (f : β → UInt8 → β) (acc : β) (bs : List UInt8) : β :=
  match _h : nextOp bs with
  | none => acc
  | some s => foldOps f (f acc s.opcode) s.rest
termination_by bs.length
decreasing_by exact nextOp_rest_length ‹_›

/--
Core's `CScript::GetSigOpCount(false)` (D107, lines 156 to 177), as a natural number.

The loop reads instructions with `GetOp` until the end of the script or the first failed read, and adds `opcodeSigOps` of each opcode.
`foldOps` runs that loop.
The data of a push is not read as opcodes.
`Script.getSigOpCount_eq_scanOps` proves the count equal to the sum of `opcodeSigOps` over the instructions of `scanOps`.
Core's result is this number modulo `2^32`.
-/
def Script.getSigOpCount (s : Script) : Nat :=
  foldOps (fun n o => n + opcodeSigOps o) 0 s.bytes.val

/--
Core's `GetLegacySigOpCount` (D106, lines 475 to 487), as a natural number.
It adds `Script.getSigOpCount` of the `scriptSig` of every input, then of the `scriptPubKey` of every output.
Core's result is this number modulo `2^32`.
-/
def Transaction.getLegacySigOpCount (tx : Transaction) : Nat :=
  ((tx.inputs.val.map fun i => i.scriptSig.getSigOpCount).sum) +
    ((tx.outputs.val.map fun o => o.scriptPubKey.getSigOpCount).sum)

end DogeLib.Transaction
