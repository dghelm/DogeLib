# Coverage: Cryptography

This file holds the per-operation coverage detail for `Cryptography`: hashes, HMAC-SHA-256, PBKDF2, scrypt, and secp256k1.
See [COVERAGE.md](../../COVERAGE.md#operations) for the compact matrix and [COVERAGE.md](../../COVERAGE.md#legend) for field meanings and theorem tags.
See [docs/soundness/cryptography.md](../soundness/cryptography.md) for theorem hypotheses and boundaries, and [docs/comparison-evidence.md](../comparison-evidence.md) for finite Core comparison counts.

## Double SHA-256

- **Definition**: `Cryptography.Hash.Sha256d.hash`
- **Theorems**: `size_hash`: 32 bytes. `hash_eq_spec`: equals the FIPS 180-4 model applied twice, for messages shorter than 2^61 bytes
- **Comparison**: `lake test`: the genesis coinbase txid and the three genesis block hashes that Dogecoin Core asserts
- **Refinement**: None
- **Excluded**: Messages of 2^61 bytes or more

## ECDSA scalar verification

- **Definition**: `Cryptography.Secp256k1.Ecdsa.verify`, `hashToInt`, `isLowS`
- **Theorems**: `wycheproof_p1363_1`: the stated point, digest and scalar pair verify, by kernel computation. `verify_r_zero`, `verify_s_zero`: a zero R or S gives `false`, for every key and digest. `verify_of_valid`: for `0 < r < n`, `0 < s < n` and a key on the curve other than infinity, `verify` is the test on `Point.mulAdd`. `xmod_eq_iff`: for `x < p` and `r < n`, `x mod n = r` exactly when `x = r`, or `r + n < p` and `x = r + n`, the two tests of Core's `secp256k1_ecdsa_sig_verify`
- **Comparison**: `lake test`: 234 scalar cases from W1, 167 accepted and 67 rejected. Eighteen non-64-byte records check only the fixture boundary. Digest order check: `01` followed by 31 zero bytes gives `2^248`. [Provenance](../../tests/cryptography/secp256k1/README.md).
- **Refinement**: None
- **Excluded**: No all-input ECDSA correctness theorem, no proof that `Point.mulAdd` computes Core's `secp256k1_ecmult`, no signing or unforgeability claim. The key parser and Core's verifier have their own rows. Core's `secp256k1_ecdsa_verify`, which rejects a high S: `verify` accepts one and corresponds to `secp256k1_ecdsa_sig_verify`

## HMAC-SHA-256

- **Definition**: `Cryptography.Hash.Hmac.hmac`, `blockKey`, `xorPad`
- **Theorems**: `hmac_eq_spec`: equality with the VG-derived list model for every key and message using executable SHA-256. `hmac_eq_fips`: FIPS-based model equality for `key.size < 2^61` and `64 + message.size < 2^61`. Conversion round trips, 32-byte tags, 64-byte key blocks, pad size and bytes, and zero extension of short keys.
- **Comparison**: `lake test`: all seven RFC 4231 HMAC-SHA-256 cases, with 131-byte keys in cases 6 and 7. Case 5 compares the first 16 bytes only.
- **Refinement**: None
- **Excluded**: Core comparison, cryptographic security and constant-time behaviour. The FIPS corollary excludes keys of 2^61 bytes or more and messages with `64 + message.size ≥ 2^61`.

## Hash160

- **Definition**: `Cryptography.Hash.Hash160.hash`, `Hash.hash160`
- **Theorems**: `size_hash`: twenty bytes for every message. `hash_eq_composition`: equals the executable RIPEMD-160 of executable SHA-256, for every message, by definition
- **Comparison**: `lake test`: twelve fixed digests produced by hashlib and independently matched by compiled Core `CHash160`, including binary inputs and SHA-256 padding boundaries. `scripts/compare_core.py`: the twelve fixtures and 279 generated padding-boundary messages against Core `CHash160` at `e0a1c15`. All agree.
- **Refinement**: None
- **Excluded**: No independent RIPEMD-160 model theorem, all-input Core equivalence or cryptographic security theorem.

## Jacobian arithmetic and modular inverse

- **Definition**: `Cryptography.euclid`, `Fin.inverse`, `Jacobian` and its arithmetic
- **Theorems**: None
- **Comparison**: Exercised by the ECDSA scalar known answers
- **Refinement**: None
- **Excluded**: No general inverse or Jacobian correctness theorem adopted

## PBKDF2-HMAC-SHA-256

- **Definition**: `Cryptography.Hash.Pbkdf2.pbkdf2`, `block`, `blocks`, `iterate`, `xorBytes`, `int`
- **Theorems**: `pbkdf2_eq_spec`: equality with the VG-derived list model for all passwords, salts, natural iteration counts and output lengths, including rejection. `pbkdf2_eq_fips`: equality with the FIPS-based model for `password.size < 2^61` and `64 + salt.size + 4 < 2^61`, for every natural iteration count and output length. The unconditional model uses executable SHA-256. `iterate_eq_spec`, `block_eq_spec` and `blocks_eq_spec` cross the byte representation. `nb_lt`: for a positive block size, admitted output lengths need fewer than 2^32 blocks.
- **Comparison**: `lake test`: both RFC 7914 §11 cases, including 80,000 iterations and complete 64-byte outputs. The first vector also fixes prefixes of 0, 1, 31, 32, 33 and 63 bytes. API checks cover zero iterations, empty output and rejection one byte above the limit.
- **Refinement**: None
- **Excluded**: Core comparison, cryptographic security, constant-time behaviour and resource bounds. Zero counts and zero output length extend RFC 8018. Iteration counts of `2^64 - 1` or more with a positive output length, where Core's `PBKDF2_SHA256` loop does not end or `c` has no `uint64_t` value.

## RIPEMD-160

- **Definition**: `Cryptography.Hash.Ripemd160.hash`, `Hash.ripemd160`
- **Theorems**: `hash_size`: twenty bytes for every message. `pad_size_mod`, `paddingZeros_minimal`, `pad_prefix`, `pad_delimiter`, `pad_zero`, `pad_length_suffix`: padding shape and preservation. `K_from_square_roots`, `K'_from_cube_roots`: constant inequalities. `r_groups_permute`, `r'_groups_permute`: each group reads every word. Fourteen fixed-vector theorems
- **Comparison**: `lake test`: nine published author vectors and ten Core RIPEMD-160 vectors, including the million-byte repeated and binary inputs. Some records share inputs. `scripts/compare_core.py`: all nineteen fixtures and 279 generated padding-boundary messages against Core `CRIPEMD160` at `e0a1c15`. All agree.
- **Refinement**: None
- **Excluded**: No theorem against a separate algorithm model, all-input Core equivalence or cryptographic security.

## SHA-1

- **Definition**: `Cryptography.Hash.Sha1.hash`, `Cryptography.Hash.sha1`
- **Theorems**: `hash_size`: twenty bytes for every message. `hash_eq_spec`: equality with the separate FIPS 180-4 §6.1.2 bit-vector model for `message.size < 2 ^ 61`
- **Comparison**: `lake test`: 65 short and 64 long NIST CAVP vectors, 100 Monte Carlo checkpoints (100,000 hash calls), and Core's ten `sha1_testvectors` cases. `scripts/compare_core.py`: 129 NIST short/long vectors and independently derived final inputs for 100 Monte Carlo checkpoints. Also ten Core vectors and 279 padding-boundary messages against Core `CSHA1` at `e0a1c15`. All agree.
- **Refinement**: None
- **Excluded**: Non-byte inputs and FIPS compatibility at 2^61 bytes or more. No collision-resistance or other security property.

## SHA-256

- **Definition**: `Cryptography.Hash.Sha256.hash`
- **Theorems**: `hash_eq_spec`: equals a separate FIPS 180-4 model, for messages shorter than 2^61 bytes
- **Comparison**: `lake test`: 129 NIST CAVP vectors (CAVS 11.0) through the compiled code
- **Refinement**: None
- **Excluded**: Messages of 2^61 bytes or more, and inputs that are not whole bytes

## Scrypt proof-of-work digest

- **Definition**: `Cryptography.Hash.Scrypt.scrypt_1024_1_1_256` and its loops in `Hash.Scrypt`
- **Theorems**: `powHash_eq_spec`: for every 80-byte input, equality with `Spec.scrypt` with N = 1024, r = 1, p = 1 and 32 output bytes. The input is password and salt, and HMAC uses executable SHA-256. `powHash_eq_fips`: the same digest as the three scrypt steps with FIPS 180-4 SHA-256 in HMAC. `doubleRound_toBitVec`: Core's statement order equals the RFC double round. `blockMix_toModel`, `fill_flat`, `integerify_toModel`, `mix_toModel`, `roMix_toModel`, `decode_toModel`, `encode_toBytes`: the representation and loop lemmas
- **Comparison**: `lake test`: the five header and digest pairs of D62, through the compiled executable, about 1.5 ms per digest. With `DOGELIB_SCRYPT_MODEL` set, the first pair also through the compiled model. [Provenance and cost](../../tests/cryptography/scrypt/README.md#dogecoin-header-digests). `scrypt.hash` compares all five exact output digests and seeded header mutations with generic Core scrypt ([streams](../comparison-evidence.md#header-proof-of-work-evidence)).
- **Refinement**: None
- **Excluded**: The SSE2 variant, cryptographic security, constant-time behaviour and resource bounds

## Scrypt RFC 7914 model

- **Definition**: `Cryptography.Hash.Scrypt.Spec.salsa`, `blockMix`, `roMix`, `scrypt` in `Proofs.Hash.ScryptSpec`
- **Theorems**: `blockMix_eq`: even-then-odd `Y` blocks for every byte list and natural block parameter. `serialize_length`, `salsa_length`, `yAt_length`: 64-byte outputs. `blockMix_length` and `repeat_blockMix_length`: `128 * r` bytes on inputs of that length. `fillLoop_eq`: sequential fill equals the list of iterates, with the final state, for every step function, count, initial state and initial array. `fill_eq_spec` specializes it to reference ROMix fill.
- **Comparison**: `lake test`: RFC 7914 §§8–10 and §12 case 1 (`N = 16`, `r = 1`, `p = 1`), through the compiled list model. Parameter checks cover invalid cost, block size, parallelism and output length. [Provenance and cost](../../tests/cryptography/scrypt/README.md). Larger §12 cases are optional and unconfirmed.
- **Refinement**: None
- **Excluded**: The Dogecoin executable, which has its own row. Core comparison, all-input agreement with the RFC, cryptographic security, constant-time behaviour and resource bounds. The model uses executable SHA-256 through PBKDF2.

## Secp256k1 fields and curve

- **Definition**: `Cryptography.Secp256k1.Fp`, `Fn`, `Point` and their arithmetic
- **Theorems**: None
- **Comparison**: Exercised by the ECDSA scalar known answers
- **Refinement**: None
- **Excluded**: No primality, group-law, scalar multiplication or Jacobian-to-affine theorem adopted. `Point.isOnCurve` is true for infinity, where Core's `secp256k1_ge_is_valid_var` returns 0

## Secp256k1 public-key parser

- **Definition**: `Cryptography.Secp256k1.parsePubKey`, `decompress`, `readCoordinate`, `Point.isOddY` in `Cryptography.Secp256k1.PubKey`
- **Theorems**: `parsePubKey_valid`: a parsed key is a point of the curve other than infinity. `parsePubKey_hybrid_even`, `parsePubKey_hybrid_odd`: a `06` or `07` key parses exactly when the `04` key with the same coordinates parses and the parity of `y` matches. Both keys then give the same point. `isValidPubKey_of_parsePubKey`: a parsed key passes Core's `CPubKey::IsValid`. `decompress_valid`: a point that `decompress` returns is a point of the curve other than infinity
- **Comparison**: `lake test`: libsecp256k1's own `ec_pubkey_parse_pointtest` at the pin (D57), on its 23 points with every first byte and every length from 3 to 65. The expectations are that test's `xpass` and `ypass` formulas. 56 keys parse: 32 compressed and 24 uncompressed or hybrid. Every other input fails. The 12 compressed keys with the parity byte of a valid point satisfy both formulas, so the test counts 32 `xpass` and 36 `ypass` parses. Each parsed point has the expected coordinates and parity. The points cover every row of design record 0005, section 4.1, and each failure. Core itself does not run
- **Refinement**: None
- **Excluded**: No theorem that `decompress` finds a root whenever `x^3 + 7` is a square, which needs Euler's criterion and so Mathlib (design record 0005, section 9). `pubkey.verify` reaches the parser through `coreVerify`, so its compared verdicts, including parser boundaries and hybrid keys, are indirect finite evidence. No comparison checks returned points, and no theorem proves equivalence with Core's parser. `readCoordinate` on a list that does not have exactly 32 bytes
