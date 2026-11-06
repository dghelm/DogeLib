module

public import DogeLib.Cryptography.Hash.Pbkdf2
public import DogeLib.Cryptography.Proofs.Hash.Pbkdf2Spec
public import DogeLib.Cryptography.Proofs.Hash.Hmac

/-!
# PBKDF2 agreement with the list model

The executable agrees with the list model for every password, salt, iteration count and output length.
The unconditional equality uses executable SHA-256, as the HMAC agreement theorem does.
The bounded corollary uses the FIPS 180-4 model.
There is no cryptographic hypothesis or security conclusion.

`Spec.blocksPrefix`, `Spec.blocksPrefix_succ`, `nb_lt` and `Spec.pbkdf2_eq_take` adapt the PRF-generic lemmas in
pyca/verified-garbage `lean/VerifiedGarbage/Proof/Pbkdf2/Whole/Common.lean` at
`28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause.
The licence and copyright notice are in `LICENSES/verified-garbage-BSD-3-Clause.txt`.
The adaptation changes names, documentation and the byte type spelling, and removes the machine-model imports.
It inlines `Tb` and `nb`, and states `pbkdf2_eq` without the auxiliary `out` hypothesis.
It omits `G_zero`, `lt_nb`, `ol_le`, `nb_zero` and `done_nb`.

`Spec.iterate_congr` adapts the lemma of that name in `Proof/Pbkdf2/Memory.lean` at the same pin.
Only its namespace, documentation and byte type spelling change.
The conversion and executable agreement proofs are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Cryptography.Hash.Pbkdf2

open Hmac.Spec (toBytes)

/-- The first `k` model blocks in output order, for any PRF. -/
def Spec.blocksPrefix (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8)) (c k : Nat) :
    List (BitVec 8) :=
  (List.range k).flatMap fun j => Spec.F prf salt c (j + 1)

/-- For every PRF, the first `k + 1` blocks append block `k + 1` to the first `k` blocks. -/
theorem Spec.blocksPrefix_succ (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8))
    (c k : Nat) : Spec.blocksPrefix prf salt c (k + 1) = Spec.blocksPrefix prf salt c k ++ Spec.F prf salt c (k + 1) := by
  simp only [Spec.blocksPrefix, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- For positive block size `D`, an admitted output length needs fewer than 2^32 blocks. -/
theorem nb_lt {D ol : Nat} (hD : 0 < D) (h : ol ≤ (2 ^ 32 - 1) * D) :
    (ol + D - 1) / D < 2 ^ 32 := by
  rw [Nat.div_lt_iff_lt_mul hD]
  omega

/-- For any PRF, an admitted length returns the requested prefix of its concatenated blocks. -/
theorem Spec.pbkdf2_eq_take (prf : List (BitVec 8) → List (BitVec 8)) (salt : List (BitVec 8))
    {c D ol : Nat} (hol : ol ≤ (2 ^ 32 - 1) * D) :
    Spec.pbkdf2 prf D salt c ol = some ((Spec.blocksPrefix prf salt c ((ol + D - 1) / D)).take ol) := by
  simp only [Spec.pbkdf2, show ¬ ((2 ^ 32 - 1) * D < ol) by omega, ↓reduceIte]
  rfl

/-- PRFs that agree on 32-byte inputs give equal iterations from a 32-byte input.
The second PRF must return 32 bytes on every input. -/
theorem Spec.iterate_congr {f g : List (BitVec 8) → List (BitVec 8)}
    (hfg : ∀ u, u.length = 32 → f u = g u) (hg : ∀ u, (g u).length = 32) :
    ∀ n u t, u.length = 32 → Spec.iterate f n u t = Spec.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

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
      Spec.blocksPrefix (Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password)) (toBytes salt) c n := by
  induction n with
  | zero => simp only [blocks, Nat.fold_zero, Spec.blocksPrefix, List.range_zero, List.flatMap_nil,
      Hmac.Spec.toBytes, ByteArray.data_empty, Array.toList_empty, List.map_nil]
  | succ n ih =>
    simp only [blocks, Nat.fold_succ, Hmac.toBytes_append, block_eq_spec, Spec.blocksPrefix_succ]
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
    rw [Spec.pbkdf2_eq_take _ _ (Nat.le_of_not_gt h)]
    simp only [Option.map_some, toBytes_extract_zero, blocks_eq_spec]

private theorem model_hmac_length (password : ByteArray) (u : List (BitVec 8)) :
    (Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password) u).length = 32 := by
  have h := Hmac.hmac_eq_spec password (Hmac.Spec.fromBytes u)
  rw [Hmac.toBytes_fromBytes] at h
  rw [← h, Hmac.toBytes_length, Hmac.hmac_size]

private theorem model_hmac_eq_fips (password : ByteArray) (u : List (BitVec 8))
    (passwordBound : password.size < 2 ^ 61) (messageBound : 64 + u.length < 2 ^ 61) :
    Hmac.Spec.hmac Hmac.Spec.sha256 (toBytes password) u =
      Hmac.Spec.hmac Hmac.Spec.fipsSha256 (toBytes password) u := by
  have size := Hmac.toBytes_length (Hmac.Spec.fromBytes u)
  rw [Hmac.toBytes_fromBytes] at size
  have he := Hmac.hmac_eq_spec password (Hmac.Spec.fromBytes u)
  have hf := Hmac.hmac_eq_fips password (Hmac.Spec.fromBytes u) passwordBound (by omega)
  simpa only [Hmac.toBytes_fromBytes] using he.symm.trans hf

/-- Under the password and salt SHA-256 bounds, every output block equals the FIPS-based list model.
The count and block index are arbitrary natural numbers, including zero. -/
theorem block_eq_fips (password salt : ByteArray) (c i : Nat)
    (passwordBound : password.size < 2 ^ 61) (saltBound : 64 + salt.size + 4 < 2 ^ 61) :
    toBytes (block password salt c i) =
      Spec.F (Hmac.Spec.hmac Hmac.Spec.fipsSha256 (toBytes password)) (toBytes salt) c i := by
  rw [block_eq_spec]
  have first := model_hmac_eq_fips password (toBytes salt ++ Spec.int i) passwordBound
    (by
      simp only [List.length_append, Hmac.toBytes_length, Spec.int, List.length_cons, List.length_nil]
      omega)
  unfold Spec.F
  rw [← first]
  exact (Spec.iterate_congr
    (fun u hu => (model_hmac_eq_fips password u passwordBound (by rw [hu]; decide)).symm)
    (model_hmac_length password) _ _ _ (model_hmac_length password _)).symm

/-- Under the password and salt SHA-256 bounds, the first `n` blocks equal the FIPS-based model blocks. -/
theorem blocks_eq_fips (password salt : ByteArray) (c n : Nat)
    (passwordBound : password.size < 2 ^ 61) (saltBound : 64 + salt.size + 4 < 2 ^ 61) :
    toBytes (blocks password salt c n) =
      Spec.blocksPrefix (Hmac.Spec.hmac Hmac.Spec.fipsSha256 (toBytes password)) (toBytes salt) c n := by
  induction n with
  | zero => simp only [blocks, Nat.fold_zero, Spec.blocksPrefix, List.range_zero,
      List.flatMap_nil, Hmac.Spec.toBytes, ByteArray.data_empty, Array.toList_empty, List.map_nil]
  | succ n ih =>
    simp only [blocks, Nat.fold_succ, Hmac.toBytes_append,
      block_eq_fips password salt c _ passwordBound saltBound, Spec.blocksPrefix_succ]
    exact congrArg (· ++ _) ih

/--
Below the password and salt SHA-256 bounds, PBKDF2 equals the list model with FIPS 180-4 SHA-256.
The bounds require `password.size < 2^61` and `64 + salt.size + 4 < 2^61`.
The equality covers all natural iteration counts and output lengths, including rejection above `(2^32 - 1) * 32` bytes.
Zero iterations uses `U₁`, and zero output bytes returns an empty result.
RFC 8018 §5.2 requires positive iteration counts and output lengths.
-/
theorem pbkdf2_eq_fips (password salt : ByteArray) (c dkLen : Nat)
    (passwordBound : password.size < 2 ^ 61) (saltBound : 64 + salt.size + 4 < 2 ^ 61) :
    (pbkdf2 password salt c dkLen).map toBytes =
      Spec.pbkdf2 (Hmac.Spec.hmac Hmac.Spec.fipsSha256 (toBytes password)) 32 (toBytes salt) c dkLen := by
  unfold pbkdf2
  split
  · rename_i h
    simp only [Spec.pbkdf2, h, ↓reduceIte, Option.map_none]
  · rename_i h
    rw [Spec.pbkdf2_eq_take _ _ (Nat.le_of_not_gt h)]
    simp only [Option.map_some, toBytes_extract_zero,
      blocks_eq_fips password salt c _ passwordBound saltBound]

end DogeLib.Cryptography.Hash.Pbkdf2
