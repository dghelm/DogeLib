module

public import DogeLib.Cryptography.Hash.Sha256d
public import DogeLib.Transaction.Serialization

/-!
# `Transaction.Txid`

The transaction ID: the double SHA-256 of the base serialization of a transaction.

Core computes it in `CTransaction::ComputeHash`, `src/primitives/transaction.cpp` lines 65 to 68 (SOURCES.md, D23).
That function calls `SerializeHash` with `SERIALIZE_TRANSACTION_NO_WITNESS`, so it hashes the base serialization, with no witness data.
`SerializeHash` is double SHA-256 (D8).
The ID is a `Hash256`, in the order that SHA-256 outputs its bytes. Core displays it reversed (D11).

`DogeLib.Transaction.Proofs.Txid` proves that the bytes of the ID are the bytes of the digest.
-/

@[expose] public section

namespace DogeLib.Transaction

open DogeLib.Serialization

/--
A digest as a `Hash256`, when it has 32 bytes.
For any other length the result is `Hash256.zero`.
A double SHA-256 digest always has 32 bytes, so `txid` never reaches that case (`Transaction.txid_val`).
-/
def digestToHash256 (d : ByteArray) : Hash256 :=
  match Hash256.ofBytes? d.toList with
  | some h => h
  | none => Hash256.zero

/--
The transaction ID: the double SHA-256 of the base serialization, `CTransaction::ComputeHash` (D23).

Core's `CTransaction::GetHash` returns a cached value.
Each constructor stores `ComputeHash()` in the cache, except the default constructor `CTransaction()`, which stores zero (D23, lines 78 to 81).
So `txid` is `GetHash` for every `CTransaction` except a default-constructed one.
That object has version 1, no inputs, no outputs and lock time 0, and `txid` gives the digest of those fields.
Core's deserialization and its conversion from `CMutableTransaction` both compute the cache.
-/
def Transaction.txid (tx : Transaction) : Hash256 :=
  digestToHash256 (Cryptography.Hash.Sha256d.hash (Codec.encode tx).toByteArray)

end DogeLib.Transaction
