# Brief of the cryptography read

This text is the prompt that produced [the record](../crypto.md).
It is exact, except that two placeholders replace the local clone paths.

````markdown
# Model read: Cryptography (secp256k1 verification and hashes) against Dogecoin Core

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides.

- DogeLib (read-only): <DogeLib clone> at commit 865754b
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>

## Scope

**Lean**, definitions outside `Proofs/` and `Exports/`: DogeLib/Cryptography/Secp256k1/*.lean (Field, Curve, Ecdsa, PubKey), DogeLib/Cryptography/Jacobian.lean, Inverse.lean, and DogeLib/Script/CoreVerifier.lean as it uses them. Also DogeLib/Cryptography/Hash/*.lean (Sha256, Sha256d, Ripemd160, Sha1, Hash160, Hmac, Pbkdf2, Scrypt).

**Core**:
- src/secp256k1/src: secp256k1.c (ecdsa_verify, signature_normalize, signature_load, ec_pubkey_parse), ecdsa_impl.h (secp256k1_ecdsa_sig_verify), eckey_impl.h (pubkey parse and serialize), group_impl.h (ge_set_xo_var, is_valid_var), field and scalar semantics (not the limb arithmetic: compare the mathematical result);
- src/pubkey.cpp (CPubKey::Verify, ecdsa_signature_parse_der_lax, IsValid and size rules);
- src/crypto/sha256.cpp, ripemd160.cpp, sha1.cpp, hmac_sha256.cpp;
- src/crypto/scrypt.cpp (scrypt_1024_1_1_256, PBKDF2_SHA256);
- src/hash.h (CHash256, CHash160).

**Focus:**
- the curve constants (p, n, G, b);
- the point validity checks;
- the verification equation, including the x-coordinate comparison against r and r+n;
- the handling of r or s equal to 0 or at least n;
- the high-S normalization;
- the public-key prefixes 02, 03, 04, 06 and 07 (hybrid keys), and their lengths;
- the hash constants, padding, length encoding and endianness;
- the scrypt parameters and the Salsa20/8 core.

Hash outputs are also checked against standard vectors. Mainly look for constants and semantic choices that vectors would not catch.

## Method

For each Core function, find the Lean counterpart and compare:
- the order of checks;
- every error or reject reason and which check produces it;
- bounds and off-by-one cases;
- integer widths, signedness, overflow and truncation;
- byte order and serialization;
- empty and edge inputs;
- height and parameter boundaries;
- which network parameters are used.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it. The project's differential comparison (`scripts/compare_core.py`, plus fixtures under tests/) can test it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: Cryptography (secp256k1 verification and hashes)

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: <files>

## Result
<two or three sentences: discrepancies found, yes or no; overall confidence>

## Findings
<one entry per discrepancy or suspected discrepancy: Lean file:line, Core file:line, what differs, a concrete input if known, severity (consensus-divergent / domain-boundary / documentation-only), confidence>

## Checked and agreeing
| Core construct (file:lines) | Lean definition (file:line) | Notes |
<one row per function or opcode group you actually compared>

## Not checked
<anything in scope you did not compare, and why>
```

Be terse. Don't pad the agreeing table with prose.
````
