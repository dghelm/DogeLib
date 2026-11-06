module

public import DogeLib.Cryptography.Hash.Pbkdf2
public import DogeLib.Cryptography.Proofs.Hash.Pbkdf2Spec
public import DogeLib.Cryptography.Proofs.Hash.Hmac

/-!
# PBKDF2 agreement with the list model

The executable agrees with the list model for every password, salt, iteration count and output length.
The model uses executable SHA-256, as the HMAC agreement theorem does.
There is no cryptographic hypothesis or security conclusion.

`G`, `G_succ`, `nb_lt` and `pbkdf2_eq` adapt the PRF-generic lemmas in
pyca/verified-garbage `lean/VerifiedGarbage/Proof/Pbkdf2/Whole/Common.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes names, documentation and the byte type spelling, and removes the machine-model imports.
The conversion and executable agreement proofs are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Pbkdf2

open Hmac.Spec (toBytes)

/-- The first `k` model blocks in output order, for any PRF. -/
def G (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8)) (c k : Nat) :
    List (BitVec 8) :=
  (List.range k).flatMap fun j => Spec.F prf salt c (j + 1)

/-- For every PRF, the first `k + 1` blocks append block `k + 1` to the first `k` blocks. -/
theorem G_succ (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8))
    (c k : Nat) : G prf salt c (k + 1) = G prf salt c k ++ Spec.F prf salt c (k + 1) := by
  simp only [G, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- For positive block size `D`, an admitted output length needs fewer than 2^32 blocks. -/
theorem nb_lt {D ol : Nat} (hD : 0 < D) (h : ol ≤ (2 ^ 32 - 1) * D) :
    (ol + D - 1) / D < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]
  omega

/-- For any PRF, an admitted length returns the requested prefix of its concatenated blocks. -/
theorem pbkdf2_eq (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8))
    {c D ol : Nat} (hol : ol ≤ (2 ^ 32 - 1) * D) :
    Spec.pbkdf2 prf D salt c ol = some ((G prf salt c ((ol + D - 1) / D)).take ol) := by
  simp only [Spec.pbkdf2, show ¬ ((2 ^ 32 - 1) * D < ol) by omega, ↓reduceIte]
  rfl

/-- Conversion preserves all four counter bytes, including indices outside the 32-bit range. -/
theorem int_eq_spec (i : Nat) : toBytes (int i) = Spec.int i := by
  rfl

/-- Conversion preserves bytewise XOR, including truncation of unequal inputs. -/
theorem xorBytes_eq_spec (a b : ByteArray) :
    toBytes (xorBytes a b) = Spec.xorBytes (toBytes a) (toBytes b) := by
  simp [xorBytes, Spec.xorBytes, Hmac.Spec.toBytes, List.map_zipWith, UInt8.toBitVec_xor]

/-- Conversion preserves any number of further HMAC iterations, for all accumulator and input arrays. -/
theorem iterate_eq_spec (password : ByteArray) (n : Nat) (u t : ByteArray) :
    toBytes (iterate password n u t) =
      Spec.iterate (Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password)) n (toBytes u) (toBytes t) := by
  induction n generalizing u t with
  | zero => rfl
  | succ n ih =>
    simp only [iterate, Spec.iterate, ih, xorBytes_eq_spec, Hmac.hmac_eq_spec]

/-- Every output block equals its list model for all counts, including zero iterations. -/
theorem block_eq_spec (password salt : ByteArray) (c i : Nat) :
    toBytes (block password salt c i) =
      Spec.F (Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password)) (toBytes salt) c i := by
  simp only [block, Spec.F, iterate_eq_spec, Hmac.hmac_eq_spec, Hmac.toBytes_append, int_eq_spec]

/-- The first `n` executable blocks equal the first `n` model blocks, for all counts and inputs. -/
theorem blocks_eq_spec (password salt : ByteArray) (c n : Nat) :
    toBytes (blocks password salt c n) =
      G (Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password)) (toBytes salt) c n := by
  induction n with
  | zero => simp only [blocks, Nat.fold_zero, G, List.range_zero, List.flatMap_nil,
      Hmac.Spec.toBytes, ByteArray.data_empty, Array.toList_empty, List.map_nil]
  | succ n ih =>
    simp only [blocks, Nat.fold_succ, Hmac.toBytes_append, block_eq_spec, G_succ]
    exact congrArg (· ++ _) ih

/-- Conversion preserves the first `n` bytes, with truncation at the array's end. -/
theorem toBytes_extract_zero (b : ByteArray) (n : Nat) :
    toBytes (b.extract 0 n) = (toBytes b).take n := by
  simp [Hmac.Spec.toBytes, ByteArray.data_extract, List.extract_eq_take_drop, List.map_take]

/--
For every password, salt, natural iteration count and output length, the executable equals the list model.
Both return `none` above `(2^32 - 1) * 32` bytes, and `some` of the same bytes otherwise.
Zero iterations uses `U₁`, and zero output bytes returns an empty result.
RFC 8018 §5.2 requires `c ≥ 1` and `dkLen ≥ 1`.
The model uses executable SHA-256, with no FIPS input bound or cryptographic assumption in this equality.
-/
theorem pbkdf2_eq_spec (password salt : ByteArray) (c dkLen : Nat) :
    (pbkdf2 password salt c dkLen).map toBytes =
      Spec.pbkdf2HmacSha256 (toBytes password) (toBytes salt) c dkLen := by
  unfold pbkdf2 Spec.pbkdf2HmacSha256
  split
  · rename_i h
    simp only [Spec.pbkdf2, h, ↓reduceIte, Option.map_none]
  · rename_i h
    rw [pbkdf2_eq _ _ (Nat.le_of_not_gt h)]
    simp only [Option.map_some, toBytes_extract_zero, blocks_eq_spec]

end DogeLib.Cryptography.Hash.Pbkdf2
