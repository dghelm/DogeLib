# Soundness: Cryptography

This file states what the cryptographic proofs of DogeLib establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#operations) for per-operation evidence.

- **Scope**: SHA-1, SHA-256, HMAC-SHA-256, PBKDF2-HMAC-SHA-256, RFC 7914 scrypt, Dogecoin's scrypt digest, double SHA-256, RIPEMD-160, Hash160, and secp256k1 ECDSA verification.
- **Specification modules**: `DogeLib.Cryptography.Hash.*`, `DogeLib.Cryptography.Secp256k1.*`, and `DogeLib.Script.CoreVerifier`.
- **Proof modules**: `DogeLib.Cryptography.Proofs.*` and `DogeLib.Script.Proofs.CoreVerifier`.
- **Key boundaries**: No theorem states collision resistance, preimage resistance, unforgeability, or constant-time behavior (A3, A4).
  Group-law arithmetic in `secp256k1` and source correspondence to pinned Core remain A1 claims.

## SHA-1

`Sha1.hash_eq_spec` equates `Sha1.hash` with `Sha1.Spec.hash` for every whole-byte message with `message.size < 2 ^ 61`.
`Sha1.hash_size` gives twenty output bytes for every message.
The definition is total beyond that bound, where its encoded bit length wraps modulo 2^64.
The theorem makes no FIPS compatibility claim on those longer messages.
`hash_eq_spec` depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.
`hash_size` depends on `propext` and `Quot.sound`.

The model uses 32-bit bit vectors and five named working variables.
Its round function, constants, schedule recurrence, block recursion and digest restate FIPS 180-4 §6.1.2 separately from the executable SHA-1 definitions.
The executable code reuses SHA-256's padding, big-endian reader, Ch and Maj.
The model reuses SHA-256's independent padding and input-word model, because FIPS 180-4 §5.1.1 and §5.2.1 prescribe both for SHA-1.
`f_toBitVec` relates the reused Ch and Maj to independent bit-vector expressions.
A reader must still compare this model with FIPS and pinned Core's `CSHA1` (A1).

The Core source review covers the portable `Transform` body and its `Round`, `f1`, `f2`, `f3` and `left` helpers.
The ARMv8 and experimental AVX2 bodies are outside that source review.

`lake test` checks 65 short and 64 long NIST messages and 100 Monte Carlo checkpoints through compiled `Sha1.hash`.
The Monte Carlo procedure makes 100,000 hash calls, following SHAVS §6.4.
The same test checks Core's ten SHA-1 cases, including two million-byte messages.
[Fixture provenance](../../tests/cryptography/sha1/cavp/README.md) records the NIST files and checksums.
Core cases come from `sha1_testvectors` and `LongTestString` at the pinned revision.
These finite tests do not prove compiled-code equivalence to Core (B1).

SHA-1 has [broken collision resistance](https://csrc.nist.gov/News/2017/Research-Results-on-SHA-1-Collisions).
The functional equality theorem establishes no collision-resistance, preimage-resistance or other security property.
No cryptographic assumption enters the theorem.

## SHA-256

`hash_eq_spec` says that `hash` equals `Spec.hash` on every message shorter than 2^61 bytes.
`Spec.hash` restates FIPS 180-4 over 32-bit bit vectors, with separate padding, schedule, round and block definitions.
The model shares the round constants `K` with the executable code.
The theorem depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.

The theorem does not show that `Spec.hash` matches FIPS 180-4.
A reader checks that by comparing the model with the standard (A1).
`lake test` runs the 129 byte-oriented NIST CAVP vectors through the compiled `hash` (B1).
The vectors come from NIST, not from the code under test, and `tests/cryptography/sha256/cavp/README.md` records their provenance.
They test the compiled code only on those inputs.

The SHA-256 definition and proof adapt EthLib at commit `6a93711`.
The current pin `bb6dfe5` restructures them in `d59f0e3a`, which DogeLib has not ported.

## HMAC-SHA-256

`Hmac.hmac_eq_spec` equates the executable with a separate list model for every byte-array key and message.
The model adapts verified-garbage's `Spec/Hmac.lean` at the pin, under BSD-3-Clause, and retains its bit-vector byte representation.
Its hash is a parameter, instantiated with DogeLib's executable SHA-256 through byte conversions.
`fromBytes_toBytes` and `toBytes_fromBytes` prove both conversion round trips.
The executable and structural lemmas adapt EthLib's HMAC files at the pin.
The existing DogeLib SHA-256 API requires no algorithm changes to those files.

`Hmac.hmac_eq_fips` replaces the executable hash with the FIPS 180-4 model.
Its hypotheses require `key.size < 2^61` and `64 + message.size < 2^61`.
The inner hash input has `64 + message.size` bytes, and the outer input has 96 bytes.
A key longer than 64 bytes is hashed before zero padding.
The bound on the key admits that hash input.
Both theorems state algorithm equalities, with no cryptographic assumption or security conclusion.

`hmac_eq_spec` and the conversion round trips depend on `propext` and `Quot.sound`.
`hmac_eq_fips` also depends on `Classical.choice`, by `#print axioms` on Lean `v4.35.0`.

A reader must compare the list model with RFC 2104 §2 and FIPS 198-1 §4 (A1).
The Lean compiler, C compiler and runtime remain trusted (B1), including Lean core's byte-array operations (B2).
`lake test` compares the compiled executable with all seven RFC 4231 HMAC-SHA-256 cases.
Case 5 fixes only the first 16 bytes, and cases 6 and 7 exercise 131-byte keys.
No theorem or test here establishes agreement with compiled Core or constant-time behaviour (A3).

## PBKDF2-HMAC-SHA-256

`Pbkdf2.pbkdf2_eq_spec` equates the executable with the separate list model for every password, salt, natural iteration count and output length.
The equality includes `none` above `(2^32 - 1) * 32` output bytes.
Zero iterations uses `U₁`, and zero output bytes returns an empty result.
Those cases extend RFC 8018 §5.2, which requires positive iterations and output length.
For a positive block size, here 32, and an admitted output length, `nb_lt` bounds the number of blocks below 2^32.
Thus the four-byte block indices do not wrap during derivation.

The model adapts verified-garbage's `Spec/Pbkdf2.lean` at the pin, under BSD-3-Clause, with its list and bit-vector representation unchanged.
The generic block lemmas adapt `Proof/Pbkdf2/Whole/Common.lean` at the same pin.
`Spec.iterate_congr` adapts `Proof/Pbkdf2/Memory.lean` at that pin.
The HMAC instance uses executable SHA-256, as `Hmac.hmac_eq_spec` does.

`pbkdf2_eq_fips` replaces that hash with the FIPS 180-4 model under `password.size < 2^61` and `64 + salt.size + 4 < 2^61`.
Those bounds admit the long-key hash and the first inner hash with salt and four counter bytes.
Every later HMAC message has 32 bytes, and each outer hash input has 96 bytes.
The corollary covers all natural counts and lengths, including rejection and both zero extensions.
It assumes no cryptographic property and proves no security claim.

`pbkdf2_eq_spec`, `pbkdf2_eq_fips` and `block_eq_fips` depend on `propext`, `Classical.choice` and `Quot.sound`.
`iterate_eq_spec`, `blocks_eq_spec`, `Spec.iterate_congr` and `nb_lt` depend on `propext` and `Quot.sound`, by `#print axioms` on Lean `v4.35.0`.
A reader must compare the list model with RFC 8018 §5.2 (A1).
The Lean compiler, C compiler, runtime and Lean core byte-array operations remain trusted (B1, B2).
The executable uses whole-message HMAC and makes no constant-time or resource-bound claim (A3).
No runtime substitution or trust-policy exception is added.

`lake test` compares both complete 64-byte RFC 7914 §11 outputs through compiled code, including the 80,000-iteration case.
It also checks prefixes of the first vector and the zero-count, empty-output and oversized-output branches.
The RFC errata search, read on 2026-11-06, has no correction to those vectors.
No theorem or test here establishes agreement with compiled Core.

Core's `PBKDF2_SHA256` counts iterations in `uint64_t` with the loop test `j <= c` (D61, line 100), so its loop does not end at `c = 2^64 - 1` with a positive output length.
With a zero output length, Core's outer loop at line 88 runs no iteration.
A correspondence with Core can therefore cover only `c < 2^64 - 1` or a zero output length, and Core's scrypt digest uses `c = 1`.

## Scrypt RFC 7914 model

`Cryptography.Hash.Scrypt.Spec` adapts verified-garbage's `Spec/Scrypt.lean` at the pin, under BSD-3-Clause.
It retains lists of `BitVec 8`, 32-bit words, and the quadratic ROMix reference fill.
The PBKDF2 model uses DogeLib's executable SHA-256 through HMAC.
The general scrypt definition has no FIPS-based equality theorem.
`Pbkdf2.pbkdf2_eq_fips` remains a separate result with password and salt bounds.
For Dogecoin's parameters, `powHash_eq_fips` states the digest with the FIPS 180-4 model, as the [next subsection](#dogecoins-scrypt-digest) describes.

`blockMix_eq` expresses the output as the even-indexed `Y` blocks followed by the odd-indexed blocks, for every byte list and natural block parameter.
`serialize_length`, `salsa_length` and `yAt_length` give 64-byte outputs.
`blockMix_length` and `repeat_blockMix_length` preserve `128 * r` bytes under that input-length hypothesis.
These structural lemmas adapt VG's `Proof/Scrypt/BlockMix.lean` and the length lemmas of `Proof/Scrypt/RoMix.lean`.
They do not prove agreement with the RFC or Core (A1).

`fillLoop_eq` relates sequential array fill to the reference list of iterates, for every step function, count, initial state and initial array.
It equates both the stored states and the final state.
`fill_eq_spec` specializes it to BlockMix and an empty array.
The generic theorem applies to an implementation that stores whole states as array elements.
It provides no flattening theorem for a flat word array or commutation theorem for a conversion between state types.
Each of these two theorems, `blockMix_eq`, and the five length lemmas above depends on `propext` and `Quot.sound`, by `#print axioms`.

The component operations are total outside their RFC length domains.
Word reads supply zero for missing bytes, XOR truncates, and natural subtraction saturates at zero.
The top-level `scrypt` checks the published parameter bounds and delegates the output upper bound to PBKDF2.
The [errata review](../../tests/cryptography/scrypt/README.md#errata) records the retained parameter bound and Integerify interpretation (A1).
The model introduces no cryptographic hypothesis and makes no side-channel or resource-bound claim (A3).

The compiled known answers compare complete RFC 7914 outputs for Salsa20/8, BlockMix, ROMix and the `N = 16` scrypt case.
The [test cost report](../../tests/cryptography/scrypt/README.md#test-cost) distinguishes those passes from timed-out optional cases.
These comparisons rely on the compiler and runtime (B1), and are not kernel digest proofs (C2).
This model has no Core comparison or full header proof-of-work claim.
The [next subsection](#dogecoins-scrypt-digest) relates Dogecoin's executable to it.

## Dogecoin's scrypt digest

`Scrypt.scrypt_1024_1_1_256` follows Core's `scrypt_1024_1_1_256_sp_generic` and `xor_salsa8` (D61, lines 121–218).
Its input type, `Bytes 80`, admits exactly 80 bytes.
`powHash_eq_spec` runs `Spec.scrypt` on every such input, as password and salt, with N = 1024, r = 1, p = 1 and 32 output bytes.
It states that the model returns `some` of the executable's digest bytes.
The theorem has no hypothesis.
The model's HMAC uses DogeLib's executable SHA-256, as `Pbkdf2.pbkdf2_eq_spec` does.

`powHash_eq_fips` restates the digest with HMAC over the FIPS 180-4 SHA-256 model.
It writes scrypt out as its three steps for p = 1.
They are PBKDF2 to 128 bytes, scryptROMix with r = 1 and N = 1024, and PBKDF2 to 32 bytes.
It uses `Pbkdf2.pbkdf2_eq_fips` twice. The password has 80 bytes and the salts have 80 and 128 bytes, far below its bounds.
It does not restate `Spec.scrypt` with a second hash instance, so it adds no model definition.

The proof crosses the representation in these lemmas:

- `doubleRound_toBitVec`: the executable runs the 32 statements of each double round in Core's order.
  `step_comm` shows that two steps commute when neither writes a word that the other reads or writes.
  `columnsCore_eq` and `rowsCore_eq` sort Core's interleaved quarter-rounds into the RFC order of `Spec.doubleRound`.
  A reader compares the executable's statements with Core's text, but not Core's order with the RFC order.
- `xorSalsa8_toBitVec` and `blockMix_toModel`: `xor_salsa8(&X[0], &X[16])` and `xor_salsa8(&X[16], &X[0])` equal the model's `blockMix 1` under `toModel`, which serializes `X[0..31]` as little-endian words.
- `fill_flat`: the flat scratchpad `V` holds the words of the states that `fillLoop` stores whole, so `fillLoop_eq` gives the model's reference fill.
- `index_eq` and `integerify_toModel`: `32 * (X[16] & 1023)` in 32-bit arithmetic is 32 times Integerify of the model state modulo 1024.
- `flat_getElem!_lo` and `flat_getElem!_hi`: each `!` read of the scratchpad in the second loop is in bounds, so its default value is never used.
- `decode_toModel` and `encode_toBytes`: `le32dec` and `le32enc` convert between the 128 PBKDF2 bytes and the word state.
- `pbkdf2_some`: PBKDF2 with one iteration returns `some` for 128 and 32 output bytes, so the executable's `getD` defaults are never used.

`powHash_eq_spec` and `powHash_eq_fips` depend on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` on Lean `v4.35.0`.
No theorem evaluates a scrypt digest in the kernel (C2).
The theorems relate two DogeLib definitions.
A reader must still compare the executable with D61 and the model with RFC 7914 (A1).
They say nothing about memory layout, so the little-endian and no-padding assumption of design record 0004, section 6, still applies to any comparison with Core.
They also cover only the generic Core variant, not the SSE2 variant.

`lake test` runs the five header and digest pairs of Core's `scrypt_hashtest` (D62) through the compiled executable, with the expected digests reversed from display order.
With `DOGELIB_SCRYPT_MODEL` set, it also runs the first pair through the compiled model.
The [test report](../../tests/cryptography/scrypt/README.md#dogecoin-header-digests) records the cost.
These runs rely on the compiler and runtime (B1).
`scrypt.hash` compares the five exact output digests and seeded header mutations with generic Core scrypt.

[Header proof of work](headers.md#header-proof-of-work) composes the digest with `checkProofOfWork` and `CheckAuxPowProofOfWork`.
The executable makes no constant-time or resource-bound claim (A3).

## Double SHA-256

`Sha256d.hash` is `CHash256` of Dogecoin Core (SOURCES.md, D8): SHA-256 applied to the SHA-256 digest of the message.
`size_hash` says that the digest has 32 bytes.
`hash_eq_spec` says that `Sha256d.hash` equals the FIPS 180-4 model applied twice, on every message shorter than 2^61 bytes.
The inner digest has 32 bytes, so the outer application needs no hypothesis of its own.
`hash_eq_spec` depends on `propext`, `Classical.choice` and `Quot.sound`, and `size_hash` on `propext` and `Quot.sound`, by `#print axioms`.

`lake test` checks the compiled `Sha256d.hash` against four values that Dogecoin Core asserts.
They are the genesis merkle root and the genesis block hashes of the main, test and regression-test networks.
The bytes to hash are derived by hand from `src/chainparams.cpp`, and the derivation is in `tests/KnownAnswers/Genesis.lean`.

Neither theorem says how Dogecoin orders the bytes of a hash for display, or which bytes it hashes.
Those belong to the definitions of the objects that are hashed.

## RIPEMD-160 and Hash160

`Ripemd160.hash` adapts EthLib's executable definition at `6a93711`, as SOURCES.md records.
The current pin `bb6dfe5` adds bounds hypotheses in `4f798a14`, which DogeLib has not ported.
Its UInt32 arithmetic wraps, and its eight-byte length suffix reduces the bit length modulo 2^64.
Source inspection compares the tables, round functions, constants, padding and digest order with Core's `CRIPEMD160` at the compatibility pin.
This inspection is not a Lean equivalence proof.

For every message, `hash_size` proves a twenty-byte digest.
The padding theorems prove whole blocks, minimal zero padding, preservation of message bytes, the delimiter, zero bytes and the length-byte suffix.
The suffix theorem identifies `lengthBytes message.size`, without separately proving a mathematical decoding theorem for those bytes.
The constant theorems check integer square-root and cube-root inequalities.
The table theorems check that each sixteen-step group includes every word index.
Fourteen kernel-checked fixed-vector theorems cover eight published messages and six selected padding boundaries.

No theorem equates `Ripemd160.hash` with a separate model of RIPEMD-160.

`Hash160.hash_eq_composition` states the defining composition: executable RIPEMD-160 applied to executable SHA-256.
It holds for every message and does not establish independent functional correctness of the composition.
`Hash160.size_hash` proves a twenty-byte digest for every message.
Neither operation has a theorem about collision resistance, preimage resistance or constant-time execution.

With Lean `v4.35.0`, `#print axioms` reports `propext` and `Quot.sound` for both digest-size theorems and `hash_eq_composition`.
The RIPEMD-160 padding theorems use the same axioms, with `Classical.choice` also used by `pad_length_suffix`.
Both constant theorems use `propext` and `Quot.sound`, and the table theorems use only `propext`.
The fourteen fixed-vector theorems use all three standard axioms.

`lake test` checks nine author vectors and ten Core RIPEMD-160 vectors, including both million-byte Core messages.
It also checks twelve Hash160 digests produced by hashlib and independently matched by compiled Core `CHash160`.
Some author and Core records share an input and digest.
The fixture README records provenance, versions, encodings and checksums.
These comparisons cover the recorded inputs, and do not prove equality to Core on every message.
The compiler and runtime boundaries remain those of Gap B.

## Secp256k1 curve and ECDSA scalar verification

`Cryptography.Secp256k1.Ecdsa.verify` checks a point, a `Hash256` digest and natural R and S.
It rejects infinity, off-curve points and scalars outside `1 ≤ r, s < n`.
It reads the digest bytes big-endian in storage order and reduces the result modulo `n`.
It computes `u1 G + u2 Q` in Jacobian coordinates, converts to affine coordinates, and compares `x mod n` with R.
It rejects a result at infinity.
The scalar predicate `isLowS` is separate and does not restrict `verify`.

So `verify` accepts a high S, which Core's `secp256k1_ecdsa_verify` rejects before the equation (D52, line 411).
`verify` corresponds to the inner test `secp256k1_ecdsa_sig_verify`, and `Script.coreVerifier` normalizes S before it calls `verify`.
`Point.isOnCurve` is true for infinity, where Core's `secp256k1_ge_is_valid_var` returns 0 (D58, lines 260 to 270).
The two agree on every affine point, and `verify` rejects the key at infinity with its own test.

The arithmetic adapts EthLib at `bb6dfe55198243682bc2eaf94611af2dbce1be6f` without changes to its formulas (SOURCES.md E7 to E11).
The source argument for Core's verification equation is design record 0005, section 4.3.
That argument requires parsed points and scalars, and is not an equivalence theorem about the arithmetic implementation or Core's compiled code.
No general theorem here proves primality, the group law, inverses, square roots, scalar multiplication or the Jacobian formulas.
EthLib's Mathlib-dependent proofs are outside this adaptation.
No theorem states that SEC 1 signing produces a signature that this verifier accepts.

There is no unforgeability or constant-time claim.

`Ecdsa.wycheproof_p1363_1` kernel-checks one accepted verification on the stated coordinates, digest, R and S.
`lake test` checks 234 scalar pairs against independent Wycheproof expectations (W1).
Eighteen other P1363 records have signatures of a different length and check only the fixture boundary.
The fixture README records their provenance and the distinction.
These finite checks establish no all-input correctness claim.
`#print axioms` reports `propext`, `Classical.choice` and `Quot.sound` for `Ecdsa.wycheproof_p1363_1`.

Four theorems relate `verify` to Core's final test, `secp256k1_ecdsa_sig_verify` (SOURCES.md D60, lines 207 to 275):

- `verify_r_zero` and `verify_s_zero`: a zero R or S gives `false`, as Core's lines 216 to 218 do.
- `verify_of_valid`: for `0 < r < n`, `0 < s < n` and a key on the curve other than infinity, `verify` is the test on `Point.mulAdd u1 G u2 Q`. It gives `false` at infinity and otherwise compares `x mod n` with R.
- `xmod_eq_iff`: for `x < p` and `r < n`, `x mod n = r` holds exactly when `x = r`, or `r + n < p` and `x = r + n`. Core tests those two cases in Jacobian coordinates (lines 244 to 272), so on an affine `x` the two tests agree.

The [public-key parser and Core's verifier](#secp256k1-public-key-parser-and-cores-verifier) connect `verify` to Script.
No foreign code decides a scalar verification in the Lean specification.
Compiled evaluation still depends on the compiler and runtime (B1 and B2).

## Secp256k1 public-key parser and Core's verifier

`Cryptography.Secp256k1.parsePubKey` is `secp256k1_ec_pubkey_parse` of the libsecp256k1 copy in Core at the pin (SOURCES.md D5, D52, D58 and D59).
It is written from that source, not adapted from EthLib, and it accepts the hybrid encodings `06` and `07`.
It omits the subgroup test, which returns true outside libsecp256k1's exhaustive-test build because the cofactor of secp256k1 is 1.
`Script.coreVerifier` is `CPubKey::Verify` (D50, lines 168 to 186) on a 64-bit build.
It runs Core's steps in order: `isValidPubKey`, `parsePubKey`, the empty-signature test, `parseDerLax`, S normalization and `Ecdsa.verify`.
The theorems are in `DogeLib.Cryptography.Proofs.Secp256k1.PubKey` and `DogeLib.Script.Proofs.CoreVerifier`.

`readCoordinate` reads its whole list as one big-endian integer, and `secp256k1_fe_set_b32` reads exactly 32 bytes (D59).
The two correspond on a list of exactly 32 bytes, and `parsePubKey` passes no other list.

For every input:

- `parsePubKey_valid`: a parsed key is a point on the curve other than infinity.
- `parsePubKey_hybrid_even` and `parsePubKey_hybrid_odd`: a hybrid key parses as the `04` key with the same coordinates. The result stays only when the parity of `y` matches the first byte.
- `isValidPubKey_of_parsePubKey`: a parsed key passes `isValidPubKey`.
- `coreVerifier_some`: `coreVerifier` always answers `some`. `transactionChecker_coreVerifier_some`: so does every `checkSig` request of `transactionChecker` with a script code shorter than 2^64 bytes.
- `coreVerifier_invalidKey`, `coreVerifier_badPoint`, `coreVerifier_emptySig` and `coreVerifier_badDer`: Core's first four steps give `some false`.
- `coreVerifier_eq_verify`: otherwise the result is `Ecdsa.verify` on the parsed point, the digest, R and `normalizeS S`.
- `parseDerLax_lt`: the lax parser stores scalars below `n`, for every size of `size_t`. `normalizeS_le_half`: after normalization S is at most half the order, so the high-S test of `secp256k1_ecdsa_verify` never rejects. `normalizeS_lt`: the normalized S is below `n`, and zero only when S is.
- `coreVerifier_normalize`: two signatures that parse to `(r, s)` and `(r, n − s)` give the same result for every key and digest.
- `coreVerify_valid`: on the request of `coreVerifier_eq_verify`, R and the normalized S are below `n` and the point passes the key test. With `verify_r_zero`, `verify_s_zero` and `verify_of_valid`, `coreVerifier` then rejects a zero R or S, as Core does, and otherwise computes the test on `Point.mulAdd`.
- `hashToInt_legacyOne`: the fixed digest one of `SIGHASH_SINGLE` gives `e = 2^248`, the value that Core's storage-order read gives.
- `multisigRecovery_sound_coreVerifier`: the soundness direction of the worked property with `coreVerifier`, with no verifier hypothesis.

These theorems leave one step of the agreement with Core unproved.

**Arithmetic agreement with Core (design record 0005, section 4.3).**

Take R and S in `[1, n − 1]`, a key `Q` from `parsePubKey` and the digest scalar `e`.
Then `Point.mulAdd (e · s⁻¹) G (r · s⁻¹) Q`, with `Fn.inv`, must be the affine form of Core's `secp256k1_ecmult` result `u1 G + u2 Q` (D60, lines 220 to 227).
This includes the case in which that result is the point at infinity.
A proof needs the group law, correct Jacobian formulas, a correct `Fn.inv` and the primality of `n`.
Each of these needs Mathlib (design record 0005, decision 3), so until a proof exists, this step is an A1 claim.
The comparison obligation has finite evidence from 598 dedicated `pubkey.verify` inputs, all with agreeing verdicts:

- 464 Wycheproof bitcoin cases, with Core as the verdict source because Core normalizes high S.
- Four Core-signed inputs and two reversed digest-one inputs.
- 20 key and signature parser boundaries.
- 36 constructed infinity cases, all rejected.
- 24 constructed verification points with `x ∈ [n,p)`, all accepted, and 24 changed-S cases, all rejected. Another 24 mismatched-R cases retain x above `n` and reject.

The [fixture notes](../../tests/cryptography/secp256k1/README.md) record their provenance and constructions.
The comparison also gives agreeing verdicts on all 925 Script corpus records and 159 eligible transaction inputs.
These include the 44 records and 60 inputs that require signature verification.
The 2,000 legacy transaction mutations give 1,956 agreeing verdicts and 44 unsupported flags.

These checks close the comparison obligation of stage 3.
They do not prove that `mulAdd` agrees with `secp256k1_ecmult` on every scalar and point, or compare intermediate points.
The group-arithmetic and inverse claim remains unproved.

`decompress` relies on `Fp.sqrt`, which returns a root only after it checks the square.
No theorem says that it finds a root whenever `x^3 + 7` is a square.
That needs Euler's criterion, and the known answers are its present evidence.

The claim covers a 64-bit build of Core, because `parseDerLax` fixes `sizeof(size_t)` at 8 bytes.
A 32-bit build can differ only on a signature of at least 2^24 bytes (design record 0005, section 3).

`lake test` checks the parser on libsecp256k1's own `ec_pubkey_parse_pointtest` at the pin (D57).
The test tries 23 points with every first byte and every length from 3 to 65, and its formulas give the expectations.
`lake test` also runs 11 `coreVerifier` hand cases and both Core corpora with `coreVerifier`, as [Script signature opcodes and the checker](script.md#script-signature-opcodes-and-the-checker) states.
These finite checks establish no all-input correctness claim.
The oracle's `transaction` checker uses `coreVerifier`, and `pubkey.verify` calls `Script.coreVerify` for one signature ([docs/oracle.md](../oracle.md#public-key-verification)).
The Core harness answers the same requests with Core's `CPubKey::Verify`.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `modulus_lt_two_mul`, `secp256k1Order_eq`, `secp256k1Order_eq_half` | None |
| `hashToInt_legacyOne` | `propext` |
| `parseDerLax_nil`, `normalizeS_le_half`, `normalizeS_sub` | `propext`, `Quot.sound` |
| `Fp.neg_mul_neg`, `decompress_valid`, `parsePubKey_valid`, `parsePubKey_hybrid_even`, `parsePubKey_hybrid_odd`, `isValidPubKey_of_parsePubKey`, `verify_r_zero`, `verify_s_zero`, `xmod_eq_iff`, `verify_of_valid`, the `coreVerifier_*` theorems, `coreVerify_valid`, `laxStore_lt`, `parseDerLaxWith_lt`, `parseDerLax_lt`, `normalizeS_lt`, `transactionChecker_coreVerifier_some`, `multisigRecovery_sound_coreVerifier` | `propext`, `Classical.choice`, `Quot.sound` |
