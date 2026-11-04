module

public import DogeLib.Base.Proofs.ByteArray
public import DogeLib.Base.Proofs.Bytes
public import DogeLib.Cryptography.Proofs.Hash.Sha256d
public import DogeLib.Transaction.Txid

/-!
# Proofs: `Transaction.Txid`

- `digestToHash256_val`: for a digest of 32 bytes, the bytes of `digestToHash256 d` are the bytes of `d`.
- `Transaction.txid_val`: the bytes of the transaction ID are the bytes of the double SHA-256 digest of the base serialization.
  So `txid` never takes the fallback branch of `digestToHash256`, whose result is `Hash256.zero`.
  The theorem does not say that a digest differs from `Hash256.zero`.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/-- For every byte array `d` of 32 bytes, the bytes of `digestToHash256 d` are the bytes of `d`. -/
theorem digestToHash256_val (d : ByteArray) (h : d.size = 32) : (digestToHash256 d).val = d.toList := by
  have hl : d.toList.length = 32 := by
    rw [ByteArray.toList_eq_data_toList, Array.length_toList]; exact h
  unfold digestToHash256 Hash256.ofBytes?
  rw [Bytes.ofListExact?_val ⟨d.toList, hl⟩ |> fun e =>
    (show Bytes.ofListExact? (n := 32) d.toList = some ⟨d.toList, hl⟩ from e)]

/-- For every transaction, the bytes of `txid` are the bytes of the double SHA-256 of its base serialization. -/
theorem Transaction.txid_val (tx : Transaction) :
    tx.txid.val = (Cryptography.Hash.Sha256d.hash (Codec.encode tx).toByteArray).toList :=
  digestToHash256_val _ (Cryptography.Hash.Sha256d.size_hash _)

end DogeLib.Transaction
