module

public import DogeLib.Transaction.LegacySighash

/-!
# `Transaction.LegacySighashReference`

A second definition of the legacy signature hash, written as a transformation of the transaction.

`legacySignatureHashPlan` follows Core's production serializer, which writes the preimage field by field.
`legacyReferencePlan` follows `SignatureHashOld` instead, `src/test/sighash_tests.cpp` lines 28 to 88 of Dogecoin Core `v1.14.9` (SOURCES.md, D2).
Core keeps that function as a copy of the old `SignatureHash` of `script.cpp`, and its tests compare it with the production function.
It copies the transaction, changes the copy step by step, and serializes the copy:

1. If `nIn` is not the index of an input, the result is `one`.
2. Remove the `OP_CODESEPARATOR` instructions from the script code with `FindAndDelete`.
3. Give every input the empty script, then give input `nIn` the script code.
4. NONE: remove every output, and set the sequence of every other input to 0.
   SINGLE: if `nIn` is not the index of an output, the result is `one`.
   Otherwise keep outputs `0` to `nIn`, and replace each one before `nIn` with the null output.
   Set the sequence of every other input to 0.
5. ANYONECANPAY: keep only input `nIn`.
6. Serialize the copy without witness data, then the hash type, and hash the bytes.

Here the copy is a `Transaction`, and step 6 uses its base codec, `Codec.encode`.
The counts are `Nat` values, not `unsigned int` values.

`findAndDelete` follows `CScript::FindAndDelete`, `src/script/script.h` lines 570 to 596 (D24).
It removes copies of a pattern that start at an instruction boundary.
When `GetOp` fails, it keeps every byte from the start of the failed instruction to the end.
The serializer of `legacySignatureHashPlan` writes the bytes up to the cursor of the failed `GetOp`, and omits the unread rest of the push.
So the two definitions differ on a script that ends in a short push.

Core's `FindAndDelete` counts the copies in an `int`. Here the count is a `Nat`.
The Core compatibility of `findAndDelete` excludes a count that overflows an `int`.
The equality of the two plans is between Lean definitions, so it needs no hypothesis about the count.

`DogeLib.Transaction.Proofs.LegacySighashReference` proves that the two plans are equal under three hypotheses.
No instruction of the script code fails to parse, and the transaction has fewer than 2^32 inputs and 2^32 outputs.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-! ## `FindAndDelete` -/

/--
The leading copies of `b` removed from `rest`, and their number: the inner `while` loop of `FindAndDelete`.
The pattern `b` must not be empty. For the empty pattern the result is `(rest, 0)`.
-/
def dropMatches (b rest : List UInt8) : List UInt8 × Nat :=
  if h : b ≠ [] ∧ b.isPrefixOf rest = true then
    let res := dropMatches b (rest.drop b.length)
    (res.1, res.2 + 1)
  else (rest, 0)
termination_by rest.length
decreasing_by
  have hle := (List.isPrefixOf_iff_prefix.mp h.2).length_le
  have hpos := List.length_pos_iff.mpr h.1
  simp only [List.length_drop]
  omega

/-- `dropMatches` never makes the bytes longer. -/
theorem dropMatches_length_le (b rest : List UInt8) : (dropMatches b rest).1.length ≤ rest.length := by
  rw [dropMatches]
  split
  · have := dropMatches_length_le b (rest.drop b.length)
    simp only [List.length_drop] at this
    simp only
    omega
  · exact Nat.le_refl _
termination_by rest.length
decreasing_by
  rename_i h
  have hle := (List.isPrefixOf_iff_prefix.mp h.2).length_le
  have hpos := List.length_pos_iff.mpr h.1
  simp only [List.length_drop]
  omega

/--
The `do … while (GetOp(pc, opcode))` loop of `FindAndDelete`, from a cursor whose remaining bytes are `rest`.
Each pass removes the copies of `b` at the cursor, then reads one instruction with `readOp` and keeps its bytes.
When `readOp` fails, the bytes from the start of the failed instruction to the end are kept.
The second component counts the removed copies.
-/
def findAndDeleteLoop (b rest : List UInt8) : List UInt8 × Nat :=
  match _h : readOp (dropMatches b rest).1 with
  | .op _ bytes r =>
    let res := findAndDeleteLoop b r
    (bytes ++ res.1, (dropMatches b rest).2 + res.2)
  | .stop _ => dropMatches b rest
termination_by rest.length
decreasing_by
  have := readOp_rest_length ‹_›
  have := dropMatches_length_le b rest
  omega

/-- `findAndDeleteLoop` never makes the bytes longer. -/
theorem findAndDeleteLoop_length_le (b rest : List UInt8) :
    (findAndDeleteLoop b rest).1.length ≤ rest.length := by
  rw [findAndDeleteLoop]
  split
  · rename_i bytes r h
    have hr := findAndDeleteLoop_length_le b r
    have happ := congrArg List.length (readOp_op_append h)
    have hd := dropMatches_length_le b rest
    simp only [List.length_append] at happ ⊢
    omega
  · exact dropMatches_length_le b rest
termination_by rest.length
decreasing_by
  have := readOp_rest_length ‹_›
  have := dropMatches_length_le b rest
  omega

/--
`CScript::FindAndDelete(b)` (D24, lines 570 to 596): the script without the copies of `b` that start at an instruction boundary, and the number of copies removed.
For the empty pattern, or when no copy is found, the script is unchanged.
-/
def findAndDelete (s b : List UInt8) : List UInt8 × Nat :=
  if b = [] then (s, 0)
  else
    let res := findAndDeleteLoop b s
    if res.2 = 0 then (s, 0) else res

/-- `findAndDelete` never makes the script longer. -/
theorem findAndDelete_length_le (s b : List UInt8) : (findAndDelete s b).1.length ≤ s.length := by
  unfold findAndDelete
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.le_refl _
    · exact findAndDeleteLoop_length_le b s

/-! ## The transformed transaction -/

/-- A list whose length is at most the length of a counted list, as a counted list. -/
def CountedList.ofLengthLe {α β : Type} (l : List α) (c : CountedList β) (h : l.length ≤ c.val.length) :
    CountedList α :=
  ⟨l, Nat.lt_of_le_of_lt h c.property⟩

/-- The script code after `scriptCode.FindAndDelete(CScript(OP_CODESEPARATOR))` (D2, line 40). -/
def referenceScriptCode (sc : Script) : Script :=
  ⟨CountedList.ofLengthLe (findAndDelete sc.bytes.val [opCodeSeparator]).1 sc.bytes
    (findAndDelete_length_le _ _)⟩

/--
The inputs of the copy before the ANYONECANPAY step (D2, lines 42 to 45, 53 to 56 and 71 to 74).
Every input gets the empty script, then input `n` gets `code`.
With `zeroSequence`, every other input gets sequence 0.
-/
def referenceSequencedInputs (code : Script) (inputs : List TxIn) (n : Nat) (zeroSequence : Bool) :
    List TxIn :=
  let blanked := inputs.map fun i => { i with scriptSig := Script.empty }
  let withCode := blanked.modify n fun i => { i with scriptSig := code }
  if zeroSequence then withCode.mapIdx fun i x => if i = n then x else { x with sequence := 0 }
  else withCode

/--
The inputs of the copy (D2, lines 42 to 82).
With `anyoneCanPay`, the copy keeps only input `n`: `vin[0] = vin[nIn]; vin.resize(1)` (lines 77 to 82).
-/
def referenceInputs (code : Script) (inputs : List TxIn) (n : Nat) (zeroSequence anyoneCanPay : Bool) :
    List TxIn :=
  let sequenced := referenceSequencedInputs code inputs n zeroSequence
  if anyoneCanPay then
    match sequenced[n]? with
    | some x => (sequenced.set 0 x).take 1
    | none => sequenced
  else sequenced

/--
The outputs of the copy (D2, lines 47 to 69).
NONE removes them all. SINGLE keeps outputs `0` to `n`, `vout.resize(nOut+1)`, and replaces each one before `n` with `TxOut.null`.
-/
def referenceOutputs (outputs : List TxOut) (n : Nat) (none single : Bool) : List TxOut :=
  if none then []
  else if single then (outputs.take (n + 1)).mapIdx fun i o => if i < n then TxOut.null else o
  else outputs

/-- `referenceInputs` never adds inputs. -/
theorem referenceInputs_length_le (code : Script) (inputs : List TxIn) (n : Nat) (z a : Bool) :
    (referenceInputs code inputs n z a).length ≤ inputs.length := by
  unfold referenceInputs referenceSequencedInputs
  simp only
  split
  · split
    · split <;> simp <;> omega
    · split <;> simp <;> omega
  · split <;> simp

/-- `referenceOutputs` never adds outputs. -/
theorem referenceOutputs_length_le (outputs : List TxOut) (n : Nat) (none single : Bool) :
    (referenceOutputs outputs n none single).length ≤ outputs.length := by
  unfold referenceOutputs
  split
  · simp
  · split
    · simp only [List.length_mapIdx, List.length_take]
      omega
    · exact Nat.le_refl _

/-- The copy that `SignatureHashOld` serializes, for the input index `n` and the hash type `hashType`. -/
def referenceTransaction (scriptCode : Script) (tx : Transaction) (n : Nat) (hashType : UInt32) :
    Transaction where
  version := tx.version
  inputs := CountedList.ofLengthLe
    (referenceInputs (referenceScriptCode scriptCode) tx.inputs.val n
      (HashType.isSingle hashType || HashType.isNone hashType) (HashType.anyoneCanPay hashType))
    tx.inputs (referenceInputs_length_le _ _ _ _ _)
  outputs := CountedList.ofLengthLe
    (referenceOutputs tx.outputs.val n (HashType.isNone hashType) (HashType.isSingle hashType))
    tx.outputs (referenceOutputs_length_le _ _ _ _)
  lockTime := tx.lockTime

/-- The plan of `SignatureHashOld` (D2, lines 28 to 88), with its two checks in Core's order. -/
def legacyReferencePlan (scriptCode : Script) (tx : Transaction) (nIn hashType : UInt32) :
    LegacyHashPlan :=
  if tx.inputs.val.length ≤ nIn.toNat then .fixedDigest legacyOne
  else if HashType.isSingle hashType ∧ tx.outputs.val.length ≤ nIn.toNat then .fixedDigest legacyOne
  else .hashBytes (Codec.encode (referenceTransaction scriptCode tx nIn.toNat hashType) ++ Codec.encode hashType)

end DogeLib.Transaction
