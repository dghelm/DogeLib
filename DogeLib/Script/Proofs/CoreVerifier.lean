module

public import DogeLib.Script.CoreVerifier
public import DogeLib.Script.Proofs.MultisigRecovery
public import DogeLib.Cryptography.Proofs.Secp256k1.PubKey

/-!
# Proofs: `Script.CoreVerifier`

## The steps of `CPubKey::Verify`

- `coreVerifier_some`: `coreVerifier` never returns `none`.
- `isValidPubKey_of_parsePubKey`: a key that `parsePubKey` accepts passes `isValidPubKey`, so step 1 never rejects a key that step 2 accepts.
- `coreVerifier_invalidKey`, `coreVerifier_badPoint`, `coreVerifier_emptySig` and `coreVerifier_badDer`: steps 1 to 4 give `some false`.
- `coreVerifier_eq_verify`: for a key that parses and a signature that `parseDerLax` accepts, the result is `Ecdsa.verify` on the point, the digest, R and `normalizeS S`.

## Normalization

- `parseDerLax_lt`: the lax parser stores scalars below `n`.
- `normalizeS_le_half`: for `s ≤ n`, the normalized S is at most `secp256k1HalfOrder`, so the high-S test of `secp256k1_ecdsa_verify` never rejects it.
- `normalizeS_sub`: for `s ≤ n`, `s` and `n - s` normalize to the same value.
- `coreVerifier_normalize`: two signatures that parse to `(r, s)` and `(r, n - s)` give the same result, for every key and digest.
- `coreVerify_valid`: on the request of `coreVerifier_eq_verify`, R and the normalized S are below `n`, and the point is on the curve and not infinity. So `Ecdsa.verify` reaches its final test exactly when R and S are not zero.

## The digest and the checker

- `hashToInt_legacyOne`: the fixed digest one of `SIGHASH_SINGLE` gives `e = 2^248`.
- `transactionChecker_coreVerifier_some`: with `coreVerifier`, every `checkSig` request of `transactionChecker` with a script code shorter than 2^64 bytes answers `some`.
- `multisigRecovery_sound_coreVerifier`: `multisigRecovery_sound` with `coreVerifier` in place of the parameter, with no hypothesis about the verifier.

These theorems are statements about the definitions. They do not say that `coreVerifier` matches Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Cryptography.Secp256k1 DogeLib.Transaction

/-! ## The steps of `CPubKey::Verify` -/

/-- For every signature, key and digest, `coreVerifier` returns `some`. -/
theorem coreVerifier_some (sig key : List UInt8) (d : Hash256) : (coreVerifier sig key d).isSome = true := rfl

/-- Step 1: a key that fails `isValidPubKey` gives `some false`, for every signature and digest. -/
theorem coreVerifier_invalidKey {key : List UInt8} (h : isValidPubKey key = false) (sig : List UInt8) (d : Hash256) :
    coreVerifier sig key d = some false := by
  simp [coreVerifier, coreVerify, h]

/-- Step 2: a key that `parsePubKey` rejects gives `some false`, for every signature and digest. -/
theorem coreVerifier_badPoint {key : List UInt8} (h : parsePubKey key = none) (sig : List UInt8) (d : Hash256) :
    coreVerifier sig key d = some false := by
  simp only [coreVerifier, coreVerify, h]
  split <;> rfl

/-- Step 3: the empty signature gives `some false`, for every key and digest. -/
theorem coreVerifier_emptySig (key : List UInt8) (d : Hash256) : coreVerifier [] key d = some false := by
  simp only [coreVerifier, coreVerify, List.isEmpty_nil]
  split
  · rfl
  · split <;> rfl

/-- Step 4: a signature that `parseDerLax` rejects gives `some false`, for every key and digest. -/
theorem coreVerifier_badDer {sig : List UInt8} (h : parseDerLax sig = none) (key : List UInt8) (d : Hash256) :
    coreVerifier sig key d = some false := by
  simp only [coreVerifier, coreVerify, h]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- A key that parses passes `isValidPubKey`: its length is the one that its first byte gives. -/
theorem isValidPubKey_of_parsePubKey {key : List UInt8} {q : Point} (h : parsePubKey key = some q) :
    isValidPubKey key = true := by
  unfold parsePubKey at h
  match key, h with
  | header :: rest, h =>
    simp only [List.getD_cons_zero, List.length_cons] at h
    unfold isValidPubKey pubKeyLength
    split at h
    · rename_i hc
      obtain ⟨hl, hh⟩ := hc
      rcases hh with rfl | rfl <;> simp_all
    · split at h
      · rename_i hc
        obtain ⟨hl, hh⟩ := hc
        rcases hh with rfl | rfl | rfl <;> simp_all
      · cases h

/-- The lax parser rejects the empty signature. -/
theorem parseDerLax_nil : parseDerLax [] = none := rfl

/--
Steps 5 and 6: for a key that parses to `q` and a signature that `parseDerLax` parses to `(r, s)`, the result is `Ecdsa.verify q d r (normalizeS s)`.
-/
theorem coreVerifier_eq_verify {sig key : List UInt8} {q : Point} {r s : Nat} (hq : parsePubKey key = some q)
    (hsig : parseDerLax sig = some (r, s)) (d : Hash256) :
    coreVerifier sig key d = some (Ecdsa.verify q d r (normalizeS s)) := by
  have hv := isValidPubKey_of_parsePubKey hq
  have hne : sig.isEmpty = false := by
    cases sig with
    | nil => rw [parseDerLax_nil] at hsig; cases hsig
    | cons _ _ => rfl
  simp [coreVerifier, coreVerify, hv, hq, hne, hsig]

/-! ## Normalization -/

/-- `secp256k1Order` of `Script.SignatureEncoding` is `Fn.modulus` of the curve. -/
theorem secp256k1Order_eq : secp256k1Order = Fn.modulus := rfl

/-- The order is odd, and `secp256k1HalfOrder` is half of it, rounded down. -/
theorem secp256k1Order_eq_half : secp256k1Order = 2 * secp256k1HalfOrder + 1 := by decide

/-- `laxStore` stores scalars below the order. -/
theorem laxStore_lt (rBytes sBytes : List UInt8) :
    (laxStore rBytes sBytes).1 < secp256k1Order ∧ (laxStore rBytes sBytes).2 < secp256k1Order := by
  unfold laxStore
  simp only
  split
  · exact ⟨by decide, by decide⟩
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not, not_or, Nat.not_lt] at h
    omega

/-- For every size of `size_t`, the lax parser stores scalars below the order. -/
theorem parseDerLaxWith_lt {n : Nat} {sig : List UInt8} {r s : Nat} (h : parseDerLaxWith n sig = some (r, s)) :
    r < secp256k1Order ∧ s < secp256k1Order := by
  unfold parseDerLaxWith at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Option.some.injEq] at h
          exact (fun a b (h : laxStore a b = (r, s)) => by
            have := laxStore_lt a b; rw [h] at this; exact this) _ _ h

/-- The lax parser on a 64-bit build stores scalars below the order. -/
theorem parseDerLax_lt {sig : List UInt8} {r s : Nat} (h : parseDerLax sig = some (r, s)) :
    r < secp256k1Order ∧ s < secp256k1Order := parseDerLaxWith_lt h

/-- For `s ≤ n`, the normalized S is at most `secp256k1HalfOrder`. -/
theorem normalizeS_le_half {s : Nat} (h : s ≤ secp256k1Order) : normalizeS s ≤ secp256k1HalfOrder := by
  have := secp256k1Order_eq_half
  unfold normalizeS; split <;> omega

/-- For `s ≤ n`, the normalized S is below `n`, and it is zero only when `s` is zero or `n`. -/
theorem normalizeS_lt {s : Nat} (h : s ≤ secp256k1Order) :
    normalizeS s < secp256k1Order ∧ (normalizeS s = 0 ↔ s = 0 ∨ s = secp256k1Order) := by
  have := secp256k1Order_eq_half
  unfold normalizeS; split <;> omega

/-- For `s ≤ n`, `s` and `n - s` normalize to the same value. -/
theorem normalizeS_sub {s : Nat} (h : s ≤ secp256k1Order) : normalizeS (secp256k1Order - s) = normalizeS s := by
  have := secp256k1Order_eq_half
  unfold normalizeS; split <;> split <;> omega

/--
Two signatures that parse to `(r, s)` and `(r, n - s)` give the same result, for every key and digest.
So `coreVerifier` accepts a high S exactly when it accepts the low S with the same R.
-/
theorem coreVerifier_normalize {sig₁ sig₂ key : List UInt8} {r s : Nat} (h₁ : parseDerLax sig₁ = some (r, s))
    (h₂ : parseDerLax sig₂ = some (r, secp256k1Order - s)) (d : Hash256) :
    coreVerifier sig₁ key d = coreVerifier sig₂ key d := by
  have hs := (parseDerLax_lt h₁).2
  cases hq : parsePubKey key with
  | none => rw [coreVerifier_badPoint hq, coreVerifier_badPoint hq]
  | some q => rw [coreVerifier_eq_verify hq h₁, coreVerifier_eq_verify hq h₂, normalizeS_sub (by omega)]

/--
On the request of `coreVerifier_eq_verify`, R and the normalized S are below `n`, the normalized S is zero only when S is, and the point is on the curve and not infinity.
`Ecdsa.verify_of_valid` then applies when R and S are not zero, and `Ecdsa.verify_r_zero` and `verify_s_zero` apply otherwise.
-/
theorem coreVerify_valid {sig key : List UInt8} {q : Point} {r s : Nat} (hq : parsePubKey key = some q)
    (hsig : parseDerLax sig = some (r, s)) :
    r < Fn.modulus ∧ normalizeS s < Fn.modulus ∧ (normalizeS s = 0 ↔ s = 0) ∧ q ≠ .infinity ∧ q.isOnCurve = true := by
  have ⟨hr, hs⟩ := parseDerLax_lt hsig
  have hn := normalizeS_lt (Nat.le_of_lt hs)
  exact ⟨hr, hn.1, by omega, parsePubKey_valid hq⟩

/-! ## The digest and the checker -/

/-- The fixed digest one of `SIGHASH_SINGLE`, the bytes `01` and 31 zero bytes, gives `e = 2^248`. -/
theorem hashToInt_legacyOne : Ecdsa.hashToInt legacyOne = 2 ^ 248 := by decide

/--
With `coreVerifier`, every `checkSig` request of `transactionChecker tx nIn` with a script code shorter than 2^64 bytes answers `some`.
-/
theorem transactionChecker_coreVerifier_some (tx : Transaction) (nIn : UInt32) (sig key : List UInt8)
    {code : List UInt8} (h : code.length < 2 ^ 64) :
    ((transactionChecker tx nIn coreVerifier).checkSig sig key code).isSome = true := by
  simp only [transactionChecker]
  split
  · rfl
  · split
    · rfl
    · simp [coreVerifier]

/--
`multisigRecovery_sound` with `coreVerifier` as the verifier.
An accepted spend of the template satisfies the ordinary branch or the recovery branch, where each signature check is a `coreVerifier` result.
No hypothesis about the verifier remains.
-/
theorem multisigRecovery_sound_coreVerifier {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {k : Nat} {keys : List (List UInt8)} {R : List UInt8} {S : List (List UInt8)}
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags coreVerifier k keys R S)
    (hacc : verifyLegacySpend ctx prevScriptPubKey flags coreVerifier = .accepted) :
    OrdinaryBranch ctx coreVerifier flags k keys R S ∨ RecoveryBranch ctx coreVerifier flags k keys R S :=
  multisigRecovery_sound h hacc

end DogeLib.Script
