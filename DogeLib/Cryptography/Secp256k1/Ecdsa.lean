module

public import DogeLib.Cryptography.Secp256k1.Curve
public import DogeLib.Base.Bytes

/-!
# `Secp256k1.Ecdsa`

ECDSA verification over secp256k1, from SEC 1 v2 §4.1.4.

A signature on a 32-byte hash is a pair of integers `(r, s)`.

The signer picks a secret nonce `k` and sets `R = k G`.

The signature is `r = x_R mod n` and `s = k^(-1) (e + r d) mod n`.

Here `d` is the private key and `e` the hash read as an integer.

The verifier knows `Q = d G`, not `d`, and rebuilds `R` from public values:

- `u1 = e s^(-1) mod n` and `u2 = r s^(-1) mod n`.
- `u1 G + u2 Q = s^(-1) (e + r d) G = k G = R`.

The signature is valid when the `x` of that point is `r` mod `n`.

The scalar predicate `isLowS` is separate from verification.
Verification accepts either S when the ECDSA equation holds.

## Source

This whole file adapts `EthLib/Cryptography/Secp256k1/Ecdsa.lean` from EthLib, commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`, under CC0 1.0.
The namespace and module documentation are DogeLib's.
The arithmetic definitions are unchanged.
The digest type is `DogeLib.Hash256` instead of `Vector UInt8 32`.

`ofBytesBE` comes unchanged from upstream `Secp256k1/Encoding.lean` at the same commit.
The rest of that file, including the key parser, is outside this adaptation.
The low-S documentation describes the scalar predicate without Ethereum's transaction rules.
-/

@[expose] public section

namespace DogeLib.Cryptography.Secp256k1

/-- The integer that big-endian bytes write, by SEC 1 v2 §2.3.8. -/
def ofBytesBE (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => 256 * acc + b.toNat) 0

namespace Ecdsa

/-- The integer `e` of a hash, by SEC 1 v2 §4.1.4 step 3.

`n` has 256 bits, as many as the hash, so step 3.2 keeps every bit. -/
def hashToInt (hash : Hash256) : Nat := ofBytesBE hash.val

/-- Whether `(r, s)` is a valid signature on `hash` under the public key `q`, by SEC 1 v2 §4.1.4.

`q` must be a valid public key, as SEC 1 v2 §3.2.2.1 checks: on the curve, and not `O`.

The 32 digest bytes are read big-endian in storage order, then reduced mod `n`.

The key `O` would accept any `r` that some `u1 G` hits, so it is rejected here too. -/
def verify (q : Point) (hash : Hash256) (r s : Nat) : Bool :=
  -- Step 1: `r` and `s` lie in `[1, n - 1]`, and the key is valid.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then
      if q ≠ .infinity ∧ q.isOnCurve then
        -- Steps 3 and 4: `e` acts mod `n`, like every scalar.
        let e : Fn := Fin.ofNat _ (hashToInt hash)
        let sInv := Fn.inv ⟨s, hs.2⟩
        let u1 := e * sInv
        let u2 := (⟨r, hr.2⟩ : Fn) * sInv
        -- Steps 5 to 8: `R = u1 G + u2 Q` must not be `O`, and `x_R mod n` must be `r`.
        match Point.mulAdd u1 .generator u2 q with
        | .infinity => false
        | .affine x _ => x.val % Fn.modulus == r
      else false
    else false
  else false

/-- Whether `s` is at most `n / 2`, rounded down.

Exactly one of `s` and `n - s` passes it, since `n` is odd. -/
def isLowS (s : Nat) : Bool := s ≤ Fn.modulus / 2

end Ecdsa

end DogeLib.Cryptography.Secp256k1
