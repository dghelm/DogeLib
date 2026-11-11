# Model read: Cryptography (secp256k1 verification and hashes)

- Reader: GPT-6 (Codex), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Cryptography/Secp256k1/{Field,Curve,Ecdsa,PubKey}.lean`, `Jacobian.lean`, `Inverse.lean`, `Hash/{Sha256,Sha256d,Ripemd160,Sha1,Hash160,Hmac,Pbkdf2,Scrypt}.lean`, and `DogeLib/Script/CoreVerifier.lean`, against the Core code that the [brief](briefs/crypto.md) names. The read also traced the lax parser and the key-size rules that `CoreVerifier.lean` depends on.

## Result

The read found no consensus-divergent discrepancy in `coreVerify`, the portable hashes, or generic scrypt.
It found four differences of domain in helper definitions, which appear below.
Confidence is high from source comparison, without executable confirmation.

## Findings

1. **Raw verification accepts high S.**

   Lean [`Ecdsa.lean:63`](../../DogeLib/Cryptography/Secp256k1/Ecdsa.lean) accepts either S when the equation holds.
   Core `src/secp256k1/src/secp256k1.c:400–413` rejects high S.

   Concrete input: `Q = G`, digest = 32 zero bytes, `r = G.x`, `s = n − r`.
   Lean accepts, because the reconstructed point is `−G`.
   The public verifier of libsecp256k1 rejects.
   This distinction between the two operations is intentional.
   Core `src/pubkey.cpp:184` and Lean `CoreVerifier.lean:70` normalize S first, so their outer verification agrees.

   **Severity:** domain-boundary. **Confidence:** high, from the source.

2. **The curve predicate includes infinity.**

   Lean [`Curve.lean:50`](../../DogeLib/Cryptography/Secp256k1/Curve.lean) returns true for infinity.
   Core `src/secp256k1/src/group_impl.h:260–270` returns false from `secp256k1_ge_is_valid_var` for infinity.
   Concrete input: the point at infinity.
   Lean `Ecdsa.verify` separately rejects infinity at line 67, so this distinction does not change verification.

   **Severity:** domain-boundary. **Confidence:** high.

3. **The coordinate helper consumes the whole list.**

   Lean [`PubKey.lean:43`](../../DogeLib/Cryptography/Secp256k1/PubKey.lean) interprets every supplied byte.
   Core `src/secp256k1/src/field_5x52_impl.h:309–345` reads exactly 32 bytes.
   Concrete buffer: 32 zero bytes and then `01`.
   Lean returns coordinate 1, and Core reads coordinate 0.
   `parsePubKey` always supplies exactly 32 bytes, so its behaviour agrees.

   **Severity:** domain-boundary. **Confidence:** high.

4. **PBKDF2 differs at the maximum iteration counter.**

   Lean [`Pbkdf2.lean:40`](../../DogeLib/Cryptography/Hash/Pbkdf2.lean) uses a finite natural-number recursion.
   Core `src/crypto/scrypt.cpp:80,100–109` uses `uint64_t j` with `j <= c`.
   Concrete input: empty password and salt, `c = 2^64 − 1`, `dkLen = 1`.
   Core's counter wraps, so the loop cannot finish.
   Lean defines a finite sequence of iterations.
   Scrypt always supplies `c = 1`, so this boundary does not affect its digest.

   **Severity:** domain-boundary. **Confidence:** high, from the source, not executed.

## Checked and agreeing

Lean paths below are relative to `DogeLib/`.
Core paths are relative to its pinned checkout.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `src/secp256k1/src/group_impl.h:28–64`, `scalar_4x64_impl.h:13–27`, `field_5x52_impl.h:345,635–637` | `Cryptography/Secp256k1/Field.lean:41`, `Curve.lean:33,55` | Exact p, n, half-order, G and b. |
| `src/secp256k1/src/field_5x52_impl.h:309–345` | `Cryptography/Secp256k1/PubKey.lean:43` | Big-endian coordinates and rejection at p, for 32-byte inputs. |
| `src/secp256k1/src/field_impl.h:38–135` | `Cryptography/Secp256k1/Field.lean:64,88` | Same square-root exponent and square check. |
| `src/secp256k1/src/field_5x52_impl.h:635–666`, `scalar_4x64_impl.h:831–860` | `Cryptography/Inverse.lean:33,48` | Modular inverse semantics, including zero. |
| `src/secp256k1/src/group_impl.h:67–104,273–390` | `Cryptography/Jacobian.lean:56,66,80`, `Secp256k1/Curve.lean:60,74` | Same affine results on curve points. Different projective scaling is harmless. |
| `src/secp256k1/src/ecdsa_impl.h:220–224`, `ecmult_impl.h:228–347` | `Cryptography/Jacobian.lean:105,117,135`, `Secp256k1/Curve.lean:118,123` | Same scalar-product sum. Lean's 256 steps cover Fn. |
| `src/secp256k1/src/group_impl.h:214–229,260–270,677–695` | `Cryptography/Secp256k1/PubKey.lean:63,78` | Decompression, parity and affine validity. Production subgroup check adds no restriction. |
| `src/secp256k1/src/eckey_impl.h:17–35`, `secp256k1.c:228–244` | `Cryptography/Secp256k1/PubKey.lean:78` | Exact lengths and prefixes 02/03/04/06/07. Hybrid parity precedes curve check. |
| `src/pubkey.h:59–66,143–146,189–196` | `Script/SignatureEncoding.lean:268,280` | Empty inputs, header rules and size checks. |
| `src/pubkey.cpp:27–166`, `src/secp256k1/src/secp256k1.c:335–354` | `Script/SignatureEncoding.lean:105–185` | Lax lengths, ignored sequence length, trailing bytes, unsigned integers and joint overflow-to-zero. 64-bit domain. |
| `src/secp256k1/src/secp256k1.c:295–317,381–413`, `scalar_4x64_impl.h:119–168` | `Script/CoreVerifier.lean:56`, `Cryptography/Secp256k1/Ecdsa.lean:54,84` | Stored scalar interpretation, digest reduction and S normalization. |
| `src/secp256k1/src/ecdsa_impl.h:207–274` | `Cryptography/Secp256k1/Ecdsa.lean:63` | Zero scalars, verification equation and infinity result. `x mod n = r` covers both r and r+n with the strict p bound. |
| `src/pubkey.cpp:168–185` | `Script/CoreVerifier.lean:62,76` | Same outer check order and Boolean result. |
| `src/crypto/sha256.cpp:34–88,258–336,346–398` | `Cryptography/Hash/Sha256.lean:38–166` | Constants, schedule, rounds, wrapping words, padding and big-endian length/output. |
| `src/crypto/ripemd160.cpp:17–233,242–291` | `Cryptography/Hash/Ripemd160.lean:47–202` | Both 80-step schedules, rotations, constants, state merge and little-endian length/output. |
| `src/crypto/sha1.cpp:43–69,253–345,357–406` | `Cryptography/Hash/Sha1.lean:25–88` | Constants, schedule, rounds and big-endian output. Shared padding agrees. |
| `src/hash.h:27–30,51–54` | `Cryptography/Hash/Sha256d.lean:24`, `Hash160.lean:22` | Exact compositions, without reversal. |
| `src/crypto/hmac_sha256.cpp:9–33` | `Cryptography/Hash/Hmac.lean:41,54` | Key boundary at 64 bytes, zero fill, ipad/opad and digest order. |
| `src/crypto/scrypt.cpp:69–117` | `Cryptography/Hash/Pbkdf2.lean:31–62` | Agreement within Core's output bound and `c < 2^64 − 1`. Includes c=0, empty output and partial final blocks. |
| `src/crypto/scrypt.cpp:121–185` | `Cryptography/Hash/Scrypt.lean:35–76` | Every Salsa statement, four double rounds, XOR and feed-forward. |
| `src/crypto/scrypt.cpp:187–218`, `scrypt.h:40–53` | `Cryptography/Hash/Scrypt.lean:79–130` | N=1024, r=p=1, 80-byte password/salt, scratchpad indexing and 32-byte output. |

## Not checked

- The ARM and AVX2 hash implementations, the external Intel routines, and SSE2 scrypt.
- Core's public-key serialization, which has no Lean counterpart in the scoped files.
- The limb arithmetic of fields and scalars, the internals of the modular inverse, and the correctness of libsecp256k1's precomputed tables. The comparison used their mathematical semantics.
- Proofs, compiled substitutions, extraction and runtime behavior.
- Builds and all automated repository gates: **not run**. That includes the tests on standard vectors and `scripts/compare_core.py`.

The reader confirmed both revisions with `git rev-parse`, and that the scoped source files were unchanged with `git diff --exit-code`.
The reader changed no file.

## After the read

A check against Core at the pin, by the model that prepared this record, confirmed the four findings from the source.
The doc comments of `Ecdsa.verify`, `Point.isOnCurve`, `readCoordinate` and `pbkdf2` state the boundaries.
So do [SOUNDNESS.md](../../SOUNDNESS.md#secp256k1-curve-and-ecdsa-scalar-verification) and the rows of [COVERAGE.md](../../COVERAGE.md) for those operations.
