module

public import DogeLib.Transaction.Txid

/-!
# `Transaction.LegacySighash`

The legacy signature hash: the digest that a pre-witness signature commits to.

Core computes it in `SignatureHash`, `src/script/interpreter.cpp` lines 1178 to 1246 of Dogecoin Core `v1.14.9` (SOURCES.md, D3), when `sigversion` is `SIGVERSION_BASE`.
In that mode `SignatureHash` ignores its `amount` and `cache` arguments, so they are not parameters here.
The function has three outcomes, which `legacySignatureHashPlan` returns as a `LegacyHashPlan`:

1. If `nIn` is not the index of an input, the result is the fixed digest `one` (`legacyOne`).
2. If the hash type is SINGLE and `nIn` is not the index of an output, the result is also `one`.
3. Otherwise the result is the double SHA-256 of a preimage (`legacyPreimage`).
   `CTransactionSignatureSerializer`, lines 1054 to 1143, writes the preimage. `SignatureHash` then appends `nHashType`.

The plan separates the bytes to hash from the hash function (design record 0001, section 5.4).
Two equal plans give equal digests, with no assumption about the hash function.

## The hash type

`nHashType` is an `int` in Core. Here it is its 32 bits, as a `UInt32`.
The serializer reads three flags from it:

| Flag | Condition | Effect |
| --- | --- | --- |
| `HashType.anyoneCanPay` | bit `0x80` is set | the preimage has only input `nIn` |
| `HashType.isNone` | the low 5 bits are 2 | the preimage has no outputs, and the other inputs have sequence 0 |
| `HashType.isSingle` | the low 5 bits are 3 | the preimage has outputs `0` to `nIn`, those before `nIn` replaced by `TxOut.null`, and the other inputs have sequence 0 |

Every other value of the low 5 bits, including 0 and 4 to 31, gives the preimage of ALL.
The appended hash type is all 32 bits, in little-endian order.

## The script code

The caller supplies `scriptCode`. Core's script interpreter passes the script after the last executed `OP_CODESEPARATOR`, with the signature removed.
That preparation is not specified here.
The serializer writes the script code without its `OP_CODESEPARATOR` instructions (`SerializeScriptCode`, lines 1070 to 1091).
It finds them with `CScript::GetOp`, `src/script/script.h` lines 502 to 552 (D24), which `readOp` follows.
A byte `0xab` inside push data is not an instruction, so it stays.

`GetOp` fails on a push whose length bytes or data are cut short, and its cursor stays after the bytes it read.
`SerializeScriptCode` then stops early: it writes the bytes up to that cursor, so it does not write the rest of the short push.
The CompactSize count before them is still the size of the whole script less the number of separators.
For example, the script `4c 05 aa` is written as `03 4c 05`.
`scriptCodeBytes` follows this behavior.

## Sizes

Core holds `nIn`, the input count `nInputs`, the output count `nOutputs` and `nIn + 1` in `unsigned int` variables.
Here those values are reduced modulo 2^32 where Core reduces them.
That happens only for a transaction with at least 2^32 inputs or outputs, or for SINGLE with `nIn = 0xffffffff`, where `nIn + 1` is 0.
Core computes the script-code count as `scriptCode.size() - nCodeSeparators` in `unsigned int`.
Here it is computed in `Nat`.
A `CScript` stores its size in an `unsigned int`, so a script of 2^32 bytes or more has no Core counterpart, and the two computations differ only there.

## Not specified here

- The `SIGVERSION_WITNESS_V0` branch of `SignatureHash`.
- `TransactionSignatureChecker::CheckSig`, which takes the hash type from the last byte of a signature and prepares the script code.

`DogeLib.Transaction.Proofs.LegacySighash` proves properties of these definitions.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-! ## Hash types -/

/-- `SIGHASH_ALL` (D25, `src/script/interpreter.h` line 24). -/
def sighashAll : UInt32 := 1

/-- `SIGHASH_NONE`. -/
def sighashNone : UInt32 := 2

/-- `SIGHASH_SINGLE`. -/
def sighashSingle : UInt32 := 3

/-- `SIGHASH_ANYONECANPAY`. -/
def sighashAnyoneCanPay : UInt32 := 0x80

/-- Whether the hash type has the ANYONECANPAY bit: `nHashType & SIGHASH_ANYONECANPAY` is nonzero. -/
def HashType.anyoneCanPay (h : UInt32) : Bool := h &&& sighashAnyoneCanPay != 0

/-- Whether the hash type is NONE: `(nHashType & 0x1f) == SIGHASH_NONE`. -/
def HashType.isNone (h : UInt32) : Bool := h &&& 0x1f == sighashNone

/-- Whether the hash type is SINGLE: `(nHashType & 0x1f) == SIGHASH_SINGLE`. -/
def HashType.isSingle (h : UInt32) : Bool := h &&& 0x1f == sighashSingle

/-! ## Script instructions -/

/-- `OP_CODESEPARATOR`. -/
def opCodeSeparator : UInt8 := 0xab

/-- The result of one call of Core's `CScript::GetOp` (D24). -/
inductive OpRead where
  /-- The call read a whole instruction: its opcode, its bytes, and the bytes after it. -/
  | op (opcode : UInt8) (bytes : List UInt8) (rest : List UInt8)
  /-- The call returned false. `passed` holds the bytes its cursor moved over: none at the end of the script, or the start of a short push. -/
  | stop (passed : List UInt8)

/-- A push of `size` bytes after the opcode and length bytes `header`: the whole push, or a stop after `header` when fewer than `size` bytes remain. -/
def readPush (opcode : UInt8) (header : List UInt8) (size : Nat) (r : List UInt8) : OpRead :=
  if r.length < size then .stop header else .op opcode (header ++ r.take size) (r.drop size)

/--
One instruction from the start of a script, as `CScript::GetOp2` reads it (D24, lines 502 to 552).

An opcode below `0x4c` pushes that many bytes. `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4` (`0x4c`, `0x4d`, `0x4e`) push the number of bytes in their next 1, 2 or 4 bytes, in little-endian order.
Every other opcode is one byte.
When the length bytes are short, the cursor stops after the opcode. When the data is short, it stops after the length bytes.
-/
def readOp : List UInt8 → OpRead
  | [] => .stop []
  | op :: r =>
    if op < 0x4c then readPush op [op] op.toNat r
    else if op = 0x4c then
      match r with
      | b :: r' => readPush op [op, b] b.toNat r'
      | [] => .stop [op]
    else if op = 0x4d then
      match r with
      | b0 :: b1 :: r' => readPush op [op, b0, b1] (b0.toNat + 2 ^ 8 * b1.toNat) r'
      | _ => .stop [op]
    else if op = 0x4e then
      match r with
      | b0 :: b1 :: b2 :: b3 :: r' =>
        readPush op [op, b0, b1, b2, b3]
          (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat) r'
      | _ => .stop [op]
    else .op op [op] r

/-- The width in bytes of the length field after an opcode. `OP_PUSHDATA1` has 1, `OP_PUSHDATA2` has 2, `OP_PUSHDATA4` has 4, and every other opcode has 0. -/
def lengthFieldWidth (op : UInt8) : Nat :=
  if op = 0x4c then 1 else if op = 0x4d then 2 else if op = 0x4e then 4 else 0

/-- The value of a length field, in little-endian order: `ReadLE16` and `ReadLE32` (D37) for fields of 2 and 4 bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * leValue bs

/--
The size `nSize` of the data that `GetOp2` reads after an opcode and its length field.
A direct push is its own size, and `OP_PUSHDATA1`, `OP_PUSHDATA2` and `OP_PUSHDATA4` take the value of the length field.
Every other opcode has no data.
-/
def pushSize (op : UInt8) (lengthField : List UInt8) : Nat :=
  if op < 0x4c then op.toNat else if op ≤ 0x4e then leValue lengthField else 0

/-- An instruction leaves fewer bytes than it started with. `scanOps` needs this to terminate. -/
theorem readOp_rest_length {bs : List UInt8} {o : UInt8} {b r : List UInt8}
    (h : readOp bs = .op o b r) : r.length < bs.length := by
  match bs with
  | [] => simp [readOp] at h
  | op :: t =>
    have push : ∀ (hd : List UInt8) (n : Nat) (t' : List UInt8), t'.length ≤ t.length →
        readPush op hd n t' = .op o b r → r.length < (op :: t).length := by
      intro hd n t' ht h
      unfold readPush at h
      split at h
      · cases h
      · cases h; simp; omega
    simp only [readOp] at h
    split at h
    · exact push _ _ _ (Nat.le_refl _) h
    · split at h
      · split at h
        · exact push _ _ _ (by simp <;> omega) h
        · cases h
      · split at h
        · split at h
          · exact push _ _ _ (by simp <;> omega) h
          · cases h
        · split at h
          · split at h
            · exact push _ _ _ (by simp <;> omega) h
            · cases h
          · cases h; simp

/-- For all bytes `bs`: if `readPush` reads an instruction from `r`, its bytes and the bytes after them make `header ++ r`. -/
theorem readPush_op_append {opcode o : UInt8} {header r b rest : List UInt8} {size : Nat}
    (h : readPush opcode header size r = .op o b rest) : b ++ rest = header ++ r := by
  unfold readPush at h
  split at h
  · cases h
  · cases h
    rw [List.append_assoc, List.take_append_drop]

/-- For all bytes `bs`: if `readOp` reads an instruction, its bytes and the bytes after them make `bs`. -/
theorem readOp_op_append {bs : List UInt8} {o : UInt8} {b r : List UInt8}
    (h : readOp bs = .op o b r) : b ++ r = bs := by
  match bs with
  | [] => simp [readOp] at h
  | op :: t =>
    simp only [readOp] at h
    split at h
    · exact readPush_op_append h
    · split at h
      · split at h
        · rw [readPush_op_append h]; rfl
        · cases h
      · split at h
        · split at h
          · rw [readPush_op_append h]; rfl
          · cases h
        · split at h
          · split at h
            · rw [readPush_op_append h]; rfl
            · cases h
          · cases h; rfl

/--
The instructions that the loop `while (scriptCode.GetOp(it, opcode))` reads, each with its bytes, and the bytes that the final, failing call passed.
The final bytes are empty exactly when no instruction failed to parse.
-/
def scanOps (bs : List UInt8) : List (UInt8 × List UInt8) × List UInt8 :=
  match _h : readOp bs with
  | .stop passed => ([], passed)
  | .op o b r =>
    let res := scanOps r
    ((o, b) :: res.1, res.2)
termination_by bs.length
decreasing_by exact readOp_rest_length ‹_›

/--
The script code as `SerializeScriptCode` writes it (D3, lines 1070 to 1091): the CompactSize count of the script's bytes less its `OP_CODESEPARATOR` instructions, then the bytes of its other instructions, then the bytes that a failing `GetOp` passed.
-/
def scriptCodeBytes (sc : Script) : List UInt8 :=
  let res := scanOps sc.bytes.val
  let separators := (res.1.filter fun o => o.1 == opCodeSeparator).length
  let kept := res.1.filter fun o => o.1 != opCodeSeparator
  CompactSize.encode (UInt64.ofNat (sc.bytes.val.length - separators)) ++ kept.flatMap (·.2) ++ res.2

/-! ## The preimage -/

/-- The empty script. -/
def Script.empty : Script := ⟨⟨[], by decide⟩⟩

/-- The output of `CTxOut()`: `SetNull` sets the amount to −1 and clears the script (D4). -/
def TxOut.null : TxOut := ⟨0xffffffffffffffff, Script.empty⟩

/--
Input `i` as `SerializeInput` writes it (D3, lines 1094 to 1113).
Input `nIn` has the script code and its own sequence.
Every other input has the empty script, and sequence 0 when `zeroSequence` holds.
-/
def legacyInputBytes (scriptCode : Script) (nIn : Nat) (zeroSequence : Bool) (i : Nat) (txin : TxIn) :
    List UInt8 :=
  if i = nIn then
    Codec.encode txin.prevout ++ scriptCodeBytes scriptCode ++ Codec.encode txin.sequence
  else
    Codec.encode txin.prevout ++ Codec.encode Script.empty ++
      Codec.encode (if zeroSequence then (0 : UInt32) else txin.sequence)

/--
The inputs as `CTransactionSignatureSerializer::Serialize` writes them (D3, lines 1130 to 1134): a count, then each input.
With ANYONECANPAY the count is 1 and the input is `nIn`.
Otherwise the count is the number of inputs modulo 2^32, and the inputs are the first that many.
-/
def legacyInputsBytes (scriptCode : Script) (tx : Transaction) (nIn : UInt32)
    (anyoneCanPay zeroSequence : Bool) : List UInt8 :=
  if anyoneCanPay then
    CompactSize.encode 1 ++
      ((tx.inputs.val.drop nIn.toNat).take 1).flatMap (legacyInputBytes scriptCode nIn.toNat zeroSequence nIn.toNat)
  else
    let n := tx.inputs.val.length % 2 ^ 32
    CompactSize.encode (UInt64.ofNat n) ++
      ((tx.inputs.val.take n).mapIdx (legacyInputBytes scriptCode nIn.toNat zeroSequence)).flatten

/--
The outputs as `CTransactionSignatureSerializer::Serialize` writes them (D3, lines 1135 to 1139): a count, then each output.

- NONE: the count 0.
- SINGLE: the count `nIn + 1` modulo 2^32, then outputs `0` to `nIn`, with `TxOut.null` in place of each one before `nIn`.
- Otherwise: the count of outputs modulo 2^32, then the first that many outputs.
-/
def legacyOutputsBytes (tx : Transaction) (nIn : UInt32) (none single : Bool) : List UInt8 :=
  if none then CompactSize.encode 0
  else if single then
    let n := (nIn.toNat + 1) % 2 ^ 32
    CompactSize.encode (UInt64.ofNat n) ++
      ((tx.outputs.val.take n).mapIdx fun o out =>
        Codec.encode (if o = nIn.toNat then out else TxOut.null)).flatten
  else
    let n := tx.outputs.val.length % 2 ^ 32
    CompactSize.encode (UInt64.ofNat n) ++ CountedList.encodeElems (tx.outputs.val.take n)

/--
The preimage without the hash type: `CTransactionSignatureSerializer::Serialize` (D3, lines 1126 to 1142).
It depends on the hash type only through the three flags.
-/
def legacyBody (scriptCode : Script) (tx : Transaction) (nIn : UInt32)
    (anyoneCanPay none single : Bool) : List UInt8 :=
  Codec.encode tx.version ++
    legacyInputsBytes scriptCode tx nIn anyoneCanPay (single || none) ++
    legacyOutputsBytes tx nIn none single ++
    Codec.encode tx.lockTime

/-- The bytes that `SignatureHash` hashes when it hashes: the body, then the 32 bits of the hash type in little-endian order (D3, line 1244). -/
def legacyPreimage (scriptCode : Script) (tx : Transaction) (nIn hashType : UInt32) : List UInt8 :=
  legacyBody scriptCode tx nIn (HashType.anyoneCanPay hashType) (HashType.isNone hashType)
      (HashType.isSingle hashType) ++
    Codec.encode hashType

/-! ## The plan and the digest -/

/--
Core's `one`, `uint256S("0000…0001")` (D3, line 1225).
`SetHex` reads the hexadecimal digits in display order (D11), so the bytes are `01` and then 31 zero bytes.
-/
def legacyOne : Hash256 := ⟨1 :: List.replicate 31 0, by simp⟩

/-- What `SignatureHash` returns: a fixed digest, or the double SHA-256 of a preimage (design record 0001, section 5.4). -/
inductive LegacyHashPlan where
  /-- A digest that does not depend on any bytes. -/
  | fixedDigest (digest : Hash256)
  /-- The double SHA-256 of these bytes. -/
  | hashBytes (preimage : List UInt8)
  deriving DecidableEq

/-- The digest of a plan. A preimage is hashed with double SHA-256, `CHashWriter::GetHash` (D8). -/
def LegacyHashPlan.digest : LegacyHashPlan → Hash256
  | .fixedDigest d => d
  | .hashBytes p => digestToHash256 (Cryptography.Hash.Sha256d.hash p.toByteArray)

/-- The plan of `SignatureHash` with `SIGVERSION_BASE` (D3, lines 1225 to 1245), with its two checks in Core's order. -/
def legacySignatureHashPlan (scriptCode : Script) (tx : Transaction) (nIn hashType : UInt32) :
    LegacyHashPlan :=
  if tx.inputs.val.length ≤ nIn.toNat then .fixedDigest legacyOne
  else if HashType.isSingle hashType ∧ tx.outputs.val.length ≤ nIn.toNat then .fixedDigest legacyOne
  else .hashBytes (legacyPreimage scriptCode tx nIn hashType)

/-- `SignatureHash` with `SIGVERSION_BASE`: the digest of `legacySignatureHashPlan`. -/
def legacySignatureHash (scriptCode : Script) (tx : Transaction) (nIn hashType : UInt32) : Hash256 :=
  (legacySignatureHashPlan scriptCode tx nIn hashType).digest

end DogeLib.Transaction
