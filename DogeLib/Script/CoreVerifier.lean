module

public import DogeLib.Cryptography.Secp256k1.PubKey
public import DogeLib.Script.Signature

/-!
# `Script.CoreVerifier`

`coreVerifier`, a `SignatureVerifier` that decides every request as Dogecoin Core's `CPubKey::Verify` does on a 64-bit build.

| DogeLib | Core | Source |
| --- | --- | --- |
| `coreVerify`, `coreVerifier` | `CPubKey::Verify` | D50, lines 168 to 186 |
| `normalizeS` | `secp256k1_ecdsa_signature_normalize` | D52, lines 381 to 398 |

`CPubKey::Verify` runs these steps in this order:

1. A key that fails `isValidPubKey` gives `false` (line 169).
2. A key that `parsePubKey` rejects gives `false` (lines 173 to 175).
3. An empty signature gives `false` (lines 176 to 178).
4. A signature that `parseDerLax` rejects gives `false` (lines 179 to 181).
5. An S above `secp256k1HalfOrder` becomes `n - S` (line 184).
6. The result is `Ecdsa.verify` on the point, the digest, R and the normalized S (line 185).

`transactionChecker` already rejects steps 1 and 3 before it calls its verifier.
`coreVerifier` keeps both steps, so that it is `CPubKey::Verify` as a function of its own inputs.

## Domain

The digest is a `Hash256` in the byte order in which Core stores a `uint256`.
Core passes `hash.begin()` to `secp256k1_ecdsa_verify`, which reads the 32 bytes big-endian and reduces them mod `n` (D53, lines 119 to 129).
`Ecdsa.hashToInt` reads them in the same order.

`parseDerLax` fixes `sizeof(size_t)` at 8 bytes, so the claim is about a 64-bit build of Core.
A 32-bit build can differ only on a signature of at least 2^24 bytes (design record 0005, section 3).

`secp256k1_ecdsa_verify` also rejects a high S (D52, lines 411 to 413).
After step 5, S is never high, so `coreVerify` omits that test.

## What is not proved

No theorem states that `coreVerifier` equals Core's function, which lies outside Lean.
SOUNDNESS.md records what the proofs establish and which part of the agreement rests on comparison with Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Cryptography.Secp256k1

/--
`secp256k1_ecdsa_signature_normalize` on the stored S (D52, lines 381 to 398): `n - s` when `s` is above `secp256k1HalfOrder`, and `s` otherwise.
For every `s ≤ n`, the result is at most `secp256k1HalfOrder`.
-/
def normalizeS (s : Nat) : Nat := if secp256k1HalfOrder < s then secp256k1Order - s else s

/--
`CPubKey(key).Verify(digest, sig)` (D50, lines 168 to 186) on a 64-bit build, for the signature `sig` without its hash-type byte.
The steps run in Core's order, as the module documentation lists them.
-/
def coreVerify (sig key : List UInt8) (digest : Hash256) : Bool :=
  if !isValidPubKey key then false
  else match parsePubKey key with
    | none => false
    | some q =>
      if sig.isEmpty then false
      else match parseDerLax sig with
        | none => false
        | some (r, s) => Ecdsa.verify q digest r (normalizeS s)

/--
The verifier of `transactionChecker` that decides every request as `CPubKey::Verify` does on a 64-bit build.
It always returns `some`.
-/
def coreVerifier : SignatureVerifier := fun sig key digest => some (coreVerify sig key digest)

end DogeLib.Script
