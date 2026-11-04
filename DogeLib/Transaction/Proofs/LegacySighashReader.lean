module

public import DogeLib.Transaction.Proofs.LegacySighashReference
public import DogeLib.Transaction.Proofs.Witness

/-!
# Legacy signature hash after a successful transaction read

Core-compatible readers discharge the input and output count bounds of the transformation-reference equality.
The caller must still establish `hParse`: every instruction of the supplied script code parses.
The results concern `SIGVERSION_BASE`, including when the transaction was read in the witness-allowed format.
-/

@[expose] public section

namespace DogeLib.Transaction

/--
After `readBase` succeeds, the production and transformation-reference plans agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
-/
theorem legacySignatureHashPlan_eq_reference_of_readBase (sc : Script) (bs : List UInt8)
    (tx : Transaction) (rest : List UInt8) (nIn h : UInt32)
    (hRead : Transaction.readBase bs = .ok (tx, rest))
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHashPlan sc tx nIn h = legacyReferencePlan sc tx nIn h := by
  have hb : tx.WithinMaxSize := ((Transaction.readBase_eq_ok_iff bs tx rest).mp hRead).2
  exact legacySignatureHashPlan_eq_reference sc tx nIn h hParse hb.inputs_lt hb.outputs_lt

/--
After `readBase` succeeds, the production and transformation-reference digests agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
-/
theorem legacySignatureHash_eq_reference_of_readBase (sc : Script) (bs : List UInt8)
    (tx : Transaction) (rest : List UInt8) (nIn h : UInt32)
    (hRead : Transaction.readBase bs = .ok (tx, rest))
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHash sc tx nIn h = (legacyReferencePlan sc tx nIn h).digest := by
  rw [legacySignatureHash, legacySignatureHashPlan_eq_reference_of_readBase
    sc bs tx rest nIn h hRead hParse]

/--
After `decodeBaseComplete` succeeds, the production and transformation-reference plans agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
-/
theorem legacySignatureHashPlan_eq_reference_of_decodeBaseComplete (sc : Script) (bs : List UInt8)
    (tx : Transaction) (nIn h : UInt32)
    (hRead : Transaction.decodeBaseComplete bs = .ok tx)
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHashPlan sc tx nIn h = legacyReferencePlan sc tx nIn h := by
  have hBase := (Transaction.decodeBaseComplete_eq_ok_iff bs tx).mp hRead
  have hb := ((Transaction.readBase_eq_ok_iff bs tx []).mp hBase).2
  exact legacySignatureHashPlan_eq_reference sc tx nIn h hParse hb.inputs_lt hb.outputs_lt

/--
After `decodeBaseComplete` succeeds, the production and transformation-reference digests agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
-/
theorem legacySignatureHash_eq_reference_of_decodeBaseComplete (sc : Script) (bs : List UInt8)
    (tx : Transaction) (nIn h : UInt32)
    (hRead : Transaction.decodeBaseComplete bs = .ok tx)
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHash sc tx nIn h = (legacyReferencePlan sc tx nIn h).digest := by
  rw [legacySignatureHash, legacySignatureHashPlan_eq_reference_of_decodeBaseComplete
    sc bs tx nIn h hRead hParse]

/--
After `readAllowWitness` succeeds, the production and transformation-reference plans agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
The hashing mode is `SIGVERSION_BASE` on `w.tx`, the base fields only.
It makes no claim about segregated witness.
-/
theorem legacySignatureHashPlan_eq_reference_of_readAllowWitness (sc : Script) (bs : List UInt8)
    (w : WitnessTransaction) (rest : List UInt8) (nIn h : UInt32)
    (hRead : Transaction.readAllowWitness bs = .ok (w, rest))
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHashPlan sc w.tx nIn h = legacyReferencePlan sc w.tx nIn h := by
  have hb : w.tx.WithinMaxSize := Transaction.readAllowWitness_withinMaxSize bs w rest hRead
  exact legacySignatureHashPlan_eq_reference sc w.tx nIn h hParse hb.inputs_lt hb.outputs_lt

/--
After `readAllowWitness` succeeds, the production and transformation-reference digests agree for every input index and hash type.
The caller must supply `hParse`: every instruction of the script code parses.
The hashing mode is `SIGVERSION_BASE` on `w.tx`, the base fields only.
It makes no claim about segregated witness.
-/
theorem legacySignatureHash_eq_reference_of_readAllowWitness (sc : Script) (bs : List UInt8)
    (w : WitnessTransaction) (rest : List UInt8) (nIn h : UInt32)
    (hRead : Transaction.readAllowWitness bs = .ok (w, rest))
    (hParse : (scanOps sc.bytes.val).2 = []) :
    legacySignatureHash sc w.tx nIn h = (legacyReferencePlan sc w.tx nIn h).digest := by
  rw [legacySignatureHash, legacySignatureHashPlan_eq_reference_of_readAllowWitness
    sc bs w rest nIn h hRead hParse]

end DogeLib.Transaction
