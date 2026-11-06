# Signature verifier

**Status:** Proposed. The maintainer decides each item of section 10.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-06
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [architecture](../../ARCHITECTURE.md), [oracle contract](../oracle.md) and [design record 0003](0003-legacy-spend-validation.md).

## 1. Purpose and boundary

This record sets the scope for a signature verifier that agrees with Dogecoin Core's `CPubKey::Verify` [C1].
`transactionChecker tx nIn verify` in `DogeLib.Script.Signature` takes that verifier as its parameter `verify`.
DogeLib has no instance of the parameter that decides a signature.
The oracle's `transaction` checker uses a verifier that is always unavailable, so a request that reaches it gives `unsupported` with the reason `signature_verifier`.

That gap removes these requests from the Core comparison ([docs/oracle.md](../oracle.md#the-comparison)):

- 44 of the 925 inside-milestone records of Core's `script_tests.json`, with the `transaction` checker.
- 60 of the 159 eligible transaction inputs: 42 of the 91 inputs that Core must accept, and 18 of the 68 inputs with no expectation.
- The part of each seeded legacy mutation stream that reaches a signature opcode with the `transaction` checker.

The record compares three ways to close the gap and recommends one.
It then sets the contract, the stages, the evidence and the exit conditions for the recommended option.
The theorems in section 9 are targets, not implemented results.

The record excludes these subjects:

- Signing, nonce generation and private keys in the specification. Section 8 uses Core's signer only to make fixtures.
- Unforgeability or any other security claim about ECDSA.
- Witness signature hashing, Schnorr signatures and every `SIGVERSION` other than `SIGVERSION_BASE`.
- The `NULLFAIL` flag, which stays unsupported (design record 0003, section 3).
- Constant-time execution. Verification reads only public data.
- Implementation refinement and Rust extraction.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The bundled libsecp256k1 is the copy under `src/secp256k1` at that commit.
The line ranges identify the inspected source for each contract:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [pubkey.cpp, lines 168–186](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pubkey.cpp#L168-L186) | `CPubKey::Verify`: key validity, key parsing, the empty-signature test, lax DER parsing, S normalization and verification, in that order. SOURCES.md D50. |
| C2 | [pubkey.cpp, lines 27–166](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pubkey.cpp#L27-L166) | `ecdsa_signature_parse_der_lax`, which `Script.parseDerLax` already specifies. SOURCES.md D50. |
| C3 | [pubkey.h, lines 59–66, 143–146 and 189–196](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pubkey.h#L59-L66) | `CPubKey::Set`, `IsValid` and `GetLen`, which `Script.isValidPubKey` already specifies. SOURCES.md D51. |
| C4 | [secp256k1.c, lines 228–244](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/secp256k1.c#L228-L244) | `secp256k1_ec_pubkey_parse`: the point parser and the subgroup test. |
| C5 | [secp256k1.c, lines 295–307 and 381–414](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/secp256k1.c#L381-L414) | `secp256k1_ecdsa_signature_load`, `secp256k1_ecdsa_signature_normalize` and `secp256k1_ecdsa_verify`, which rejects a high S. |
| C6 | [eckey_impl.h, lines 17–35](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/eckey_impl.h#L17-L35) | `secp256k1_eckey_pubkey_parse`: the compressed, uncompressed and hybrid encodings. |
| C7 | [group_impl.h, lines 214–229, 260–271 and 677–697](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/group_impl.h#L214-L229) | `secp256k1_ge_set_xo_var`, `secp256k1_ge_is_valid_var` and `secp256k1_ge_is_in_correct_subgroup`. |
| C8 | [field_5x52_impl.h, lines 309–345](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/field_5x52_impl.h#L309-L345) | `secp256k1_fe_set_b32`: a big-endian coordinate, which fails when it is at least `p`. |
| C9 | [ecdsa_impl.h, lines 207–275](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/ecdsa_impl.h#L207-L275) | `secp256k1_ecdsa_sig_verify`: zero scalars, `u1 G + u2 Q`, and the test of `x_R mod n` against `r`. |
| C10 | [scalar_4x64_impl.h, lines 119–129](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/scalar_4x64_impl.h#L119-L129) | `secp256k1_scalar_set_b32`: a big-endian scalar, reduced mod `n`. SOURCES.md D53. |
| C11 | [interpreter.cpp, lines 1248–1272](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1248-L1272) | `VerifySignature` and `TransactionSignatureChecker::CheckSig`, which `transactionChecker` already specifies. SOURCES.md D3. |
| C12 | [key.cpp, lines 169–182](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/key.cpp#L169-L182), [ecdsa_impl.h, lines 304–305](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/ecdsa_impl.h#L304-L305) | `CKey::Sign`: RFC 6979 nonces, a low S and strict DER output. |
| C13 | [key_tests.cpp, lines 167–177](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/key_tests.cpp#L167-L177) | Two deterministic DER signatures on a fixed message digest. |

The record also cites these documents outside Core:

| Reference | Document | Subject |
| --- | --- | --- |
| X1 | [SEC 1 v2](https://www.secg.org/sec1-v2.pdf) §2.2.1, §2.3.3–§2.3.6 and §4.1.4, [SEC 2 v2](https://www.secg.org/sec2-v2.pdf) §2.4.1 | The group law, point encodings, ECDSA verification and the curve parameters. |
| X2 | EthLib `6a93711`, `EthLib/Cryptography/Secp256k1/` `Field.lean`, `Curve.lean`, `Encoding.lean` and `Ecdsa.lean`, with the proofs under `EthLib/Cryptography/Proofs/Secp256k1/` | A pure Lean ECDSA verifier under CC0 1.0. SOURCES.md E6 already cites `Encoding.lean`. |
| X3 | `C2SP/wycheproof` at `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, `ecdsa_secp256k1_sha256_bitcoin_test.json` and `ecdsa_secp256k1_sha256_p1363_test.json` | Edge cases of ECDSA verification under the Apache License 2.0. EthLib pins 818 cases from them. |

An implementation lane adds the identifiers it uses to [SOURCES.md](../../SOURCES.md), without a change to any pin.
The findings come from source inspection, without a Core comparison run.

## 3. Contract for implementation

The central operation is `coreVerifier : SignatureVerifier`, a total function.
It takes the signature bytes without the hash-type byte, the public-key bytes and a `Hash256` digest.
It always returns `some b`, where `b` is the result of `CPubKey(pubKey).Verify(digest, sig)` [C1].
`transactionChecker tx nIn coreVerifier` then answers every request with `some`.

The digest is a `Hash256` in the order in which Core stores a `uint256`.
Core passes `hash.begin()` to `secp256k1_ecdsa_verify` [C1, line 185].
The scalar `e` is therefore the big-endian value of the 32 digest bytes, reduced mod `n` [C10].
For the fixed digest one of `SIGHASH_SINGLE` without a matching output, the bytes are `01` and 31 zero bytes (`Transaction.legacyOne`), so `e = 2^248`.
A verifier that reads the digest in display order gives a different `e` for every digest.

The function follows Core's order, although only the Boolean result is part of the contract:

1. The key fails `isValidPubKey`: `false` [C1, line 169].
2. The key fails the point parser of section 4.1: `false` [C1, lines 173–175].
3. The signature is empty: `false` [C1, lines 176–178].
4. `parseDerLax` fails: `false` [C1, lines 179–181].
5. S is above `(n − 1) / 2`: replace S with `n − S` [C1, line 184].
6. The ECDSA test of section 4.3 on the scalars, the point and `e` [C1, line 185].

`transactionChecker` already rejects steps 1 and 3 before it calls `verify` [C11].
`coreVerifier` keeps both tests, so that it equals `CPubKey::Verify` as a function of its own inputs.

## 4. Core behaviour that the specification must preserve

### 4.1 Public-key parsing

`secp256k1_ec_pubkey_parse` accepts exactly these inputs [C4, C6]:

| Length | First byte | Condition |
| --- | --- | --- |
| 33 | `02` or `03` | The 32-byte `x` is below `p` [C8], and `x^3 + 7` has a square root. The root with the parity of the first byte is `y` [C7, lines 214–229]. |
| 65 | `04` | `x` and `y` are below `p`, and `(x, y)` is on the curve [C7, lines 260–271]. |
| 65 | `06` or `07` | As for `04`, and the parity of `y` is even for `06` and odd for `07` [C6, lines 27–30]. |

The subgroup test returns true on secp256k1, whose cofactor is 1 [C7, lines 677–697].
No encoding gives the point at infinity.

EthLib's `Point.decode` rejects the hybrid prefixes `06` and `07` [X2].
The adaptation therefore adds the hybrid case.
A hybrid key reaches the verifier when `STRICTENC` is clear, because `CheckPubKeyEncoding` rejects it only under that flag (interpreter.cpp, line 215).

### 4.2 Signature parsing and normalization

`parseDerLax` returns R and S as natural numbers below `n`, or fails.
It returns zero for both when either value overflows [C2], and the verification of step 6 then fails.
`secp256k1_ecdsa_signature_load` reads the stored scalars without a further reduction [C5, lines 295–307].

Normalization replaces S with `n − S` when S is above `(n − 1) / 2` [C5, lines 381–398].
Without it, `secp256k1_ecdsa_verify` rejects every high S [C5, lines 411–413].
After normalization, that test never rejects, so the verifier accepts a high S exactly when it accepts `n − S`.
The `LOW_S` flag stays a separate encoding check in `checkLowS`, which runs before any verifier call.

### 4.3 The verification equation

`secp256k1_ecdsa_sig_verify` returns false when R or S is zero [C9, lines 216–218].
Otherwise it computes `P = u1 G + u2 Q`, where `u1 = e / S` and `u2 = R / S` mod `n` [C9, lines 220–224].
It returns false when `P` is the point at infinity [C9, lines 225–227].
It returns true when the x-coordinate of `P`, reduced mod `n`, is R.
The source tests `x = R` and, when `R + n < p`, `x = R + n` in Jacobian coordinates [C9, lines 244–272].
Since `2n > p`, those two tests are the test of `x mod n = R`.

EthLib's `Ecdsa.verify` computes the same test in affine coordinates [X2].
It requires `0 < r < n`, `0 < s < n` and a key on the curve other than infinity, and it reduces `e` mod `n`.
A lane must show that the two tests agree on every scalar and point that sections 4.1 and 4.2 produce.
A theorem or an argument in SOUNDNESS.md can show it.

## 5. The options

### 5.1 Option A: a Lean verifier adapted from EthLib

The specification library contains the curve, the point parser of section 4.1 and `coreVerifier`.
The code adapts EthLib's `Field`, `Curve` and `Ecdsa` definitions and parts of `Encoding` [X2].
Those four files have 372 lines at `6a93711` and import only Lean core.
`coreVerifier` reuses `parseDerLax`, `isValidPubKey` and the order constants of `Script.SignatureEncoding`.

The comparison then checks DogeLib's ECDSA against Core's libsecp256k1 on every request that reaches a signature check.
Outside users can verify a signed legacy spend in Lean, with no foreign code.
The option adds no foreign boundary, no new Lake dependency and no exception to the trust policy.

### 5.2 Option B: libsecp256k1 through `@[extern]`

The oracle executable links a C build of libsecp256k1 and calls it through an `@[extern]` declaration in `Exports`.
The specification keeps the verifier as a parameter.

`lake exe check-decls` reports every `@[extern]` declaration, in `Exports` as elsewhere.
The option therefore needs a trust-policy exception, which only the maintainer can grant.
SOUNDNESS.md B4 and B5 gain a foreign boundary, and the oracle build gains a C library and its build options.
The Lean library still has no verifier for outside users.
The comparison then tests the same library on both sides, so it checks Script execution and digests, not ECDSA.

### 5.3 Option C: a verifier process

The oracle sends `(pubKey, sig, digest)` queries to a separate process, such as the Core harness, and uses its answers.
The specification keeps the verifier as a parameter.

The Lean library and `check-decls` do not change.
SOUNDNESS.md B4 gains a process protocol and its failure modes.
As with option B, the comparison shares the cryptography with Core, so a fault in it cannot appear as a disagreement.
The oracle also needs a running Core-derived process to answer the `transaction` checker, and outside users still have no verifier.

### 5.4 Trust consequences

| Item of SOUNDNESS.md | Option A | Option B | Option C |
| --- | --- | --- | --- |
| A1, a wrong definition | Applies to the curve, the parser and `coreVerifier`. Source mappings, known answers and the Core comparison of section 8 mitigate it. | Moves to the C library, which is trusted, not compared. | As option B. |
| A2, the verifier-agreement hypothesis | Stays in the parameterized theorems. For `coreVerifier`, it becomes an A1 claim that the comparison tests. | Stays a hypothesis with no evidence that is independent of libsecp256k1. | As option B. |
| A3, timing | No change. Verification has no secret input. | No change. | No change. |
| B4, foreign boundaries | No change. | A new C boundary: argument marshalling, error handling and the library build. | A new process protocol: framing, timeouts and process failure. |
| B5, compiler substitutions | No change. | A new `@[extern]` and a `check-decls` exception. | No change. |
| C1 and C2, the kernel and compiled code | No new axiom. Known answers may use `decide +kernel`, which the kernel checks. | No change. | No change. |
| D2, dependencies | No Lake dependency in the root package. | A pinned C library in the oracle build. | A run-time dependency of the oracle on a Core build. |
| Maintainer-only change | None. | An exception to the trust policy. | None, but B4 grows. |

### 5.5 Measured cost of option A

A prototype compiled EthLib's definitions at `6a93711` unchanged and timed one verification.
The machine was an AMD Ryzen AI MAX+ 395, with the process fixed to one core by `taskset`.
The input was test 1 of the Wycheproof P1363 file, which EthLib's proofs pin [X3].
Half the runs changed the digest, and every run gave the expected result.

| Variant | Milliseconds per verification, three runs |
| --- | --- |
| EthLib's definitions unchanged: affine points, a Fermat inverse at each addition | 64.8, 64.5, 64.6 |
| The same affine formulas with an extended Euclidean inverse | 20.2, 20.0, 20.4 |
| Jacobian coordinates, one joint double-and-add pass and one inverse | 1.31, 1.33, 1.35 |

Only the first variant is an adaptation of EthLib, and the other two are measurements only.
The prototype did not time libsecp256k1.

The number of verifications in the comparison of section 7 is not measured.
An estimate is a few thousand: 104 requests of section 1, the signature requests of the mutation streams, and the inputs of section 8.
At 65 milliseconds each, 2,000 verifications take about 130 seconds on one core.
`lake test` runs fewer inputs than the comparison, so the unchanged definitions fit both budgets if the estimate holds.
A seeded stream of hundreds of thousands of signature requests would need the Jacobian variant.

### 5.6 Recommendation

Choose option A, with EthLib's definitions unchanged for the curve arithmetic (decision 1).
It is the only option in which the comparison tests ECDSA, and it needs no maintainer-only change.
It also gives outside users a complete legacy spend check in Lean.
Design record 0003, section 8, chose "a trusted backend for comparison". This record asks the maintainer to replace that choice (decision 1).

Options B and C remain possible later as a fast path for large seeded streams.
Either one then needs its own record, with the boundary of section 5.4.

## 6. Placement and checks

Under option A, the code has this layout:

| Module | Contents | Source |
| --- | --- | --- |
| `DogeLib.Cryptography.Secp256k1.Field` | `Fp`, `Fn`, powers, the inverse and the square root | EthLib `Field.lean`, unchanged except for the namespace |
| `DogeLib.Cryptography.Secp256k1.Curve` | `Point`, the group law and scalar multiplication | EthLib `Curve.lean`, unchanged except for the namespace |
| `DogeLib.Cryptography.Secp256k1.PubKey` | `parsePubKey`: the parser of section 4.1, with the hybrid prefixes | EthLib `Encoding.lean` for `decompress` and the coordinate reads, plus C6 |
| `DogeLib.Cryptography.Secp256k1.Ecdsa` | `verify` on scalars, a point and a digest | EthLib `Ecdsa.lean`, unchanged except for the namespace and the digest type |
| `DogeLib.Script.CoreVerifier` | `coreVerifier`, the six steps of section 3 | C1, with `parseDerLax` and `isValidPubKey` |

The curve modules belong to the `Cryptography` layer, which ARCHITECTURE.md already reserves for secp256k1.
`coreVerifier` belongs to `Script`, because it uses `parseDerLax` and `isValidPubKey` from `Script.SignatureEncoding`.
`Script.Signature` keeps the parameter, so every existing theorem keeps its statement.

Each adapted file states its EthLib origin, commit and licence in its module docstring, as CONTRIBUTING.md requires.
The specification library contains no `@[extern]`, `@[implemented_by]`, `partial` or new axiom, so `lake exe check-decls` needs no change.

EthLib's proofs of these definitions import Mathlib [X2].
The root DogeLib package has no Lake dependencies, so its `Proofs` library cannot import them.
Decision 3 chooses between three placements for any adopted proof:

- No adopted proof now. Section 9 lists the theorems that need no Mathlib.
- The separate `Refinement` package, which already pins Mathlib `v4.35.0`, the version that EthLib uses.
- A new optional package for proofs that need Mathlib.

SOUNDNESS.md changes in the implementation lanes:

- *Script signature opcodes and the checker* states that `coreVerifier` exists, and that the agreement hypothesis is an A1 claim for it.
- A new subsection states what is proved about the curve code and what is not.
- B4 states that the `transaction` checker uses `coreVerifier`, and that no foreign code decides a signature.

## 7. Implementation stages and exit conditions

### Stage 1: the curve and ECDSA

Adapt the EthLib modules of section 6, except the key parser.
Add the known answers of section 8 for `Ecdsa.verify` on points and scalars.
Exit: the build and `lake test` pass, `check-decls` reports no finding, and the licence and source rows exist.

### Stage 2: `coreVerifier`

Add `parsePubKey` and `coreVerifier`.
Prove the theorems of section 9 that need no Mathlib.
Add known answers for each row of the table in section 4.1, for overflow, for a high S and for the digest one.
Exit: `lake test` runs the 159 eligible transaction inputs with `coreVerifier`.
All 91 required acceptances accept, and no input is unsupported.

### Stage 3: oracle, harness and comparison

The `transaction` checker of `script.verify_legacy` uses `coreVerifier`.
The `signature_verifier` reason then never occurs, and the oracle and the comparator drop it (decision 4).
Add an operation `pubkey.verify` with fields `pubkey_hex`, `sig_hex` and `digest_hex` that returns `{"valid": b}`.
The Core harness answers it with `CPubKey(pubkey).Verify(uint256(digest), sig)`, with `digest_hex` as the 32 bytes of the `uint256` in storage order.
The format is `dogelib-oracle/1`. Under its [development policy](../oracle.md#format-stability), these changes settle in the stage 3 pull request and need no new format name.

Exit conditions:

- The 44 corpus records and 60 transaction inputs of section 1 each give a compared verdict that agrees with Core.
- Every seeded legacy mutation stream with the `transaction` checker gives zero disagreements, and an unsupported result only for flags.
- `pubkey.verify` agrees with Core on the inputs of section 8.
- The comparator self-test gains mutations that flip a `valid` field and a verdict that depends on a verification. Each mutation fails with its own code.

### Stage 4: signed spends of the worked property

Add fixtures of signed spends of the multisig-with-recovery template (`DogeLib/Script/MultisigRecovery.lean`), as section 8 describes.
Exit conditions:

- A realistically signed spend of each branch verifies in Lean and in Core.
  The spends are the 2-of-3 branch for each of the three pairs of signers, and the recovery branch.
- Each mutation of section 8 gives a Lean verdict that agrees with Core.

The stages run in order, and stage 4 needs the harness signer of section 8.

## 8. Evidence plan

### Known answers

No expected value of these inputs comes from DogeLib:

| Source | Cases | Expected value |
| --- | --- | --- |
| Wycheproof P1363 [X3] | The 252 cases that EthLib pins, on points and scalars | Wycheproof's result, for `Ecdsa.verify`. These cases test the curve code, not Core's parsers. |
| Wycheproof bitcoin set [X3] | Cases with valid DER and every S | Core's result from the harness. Wycheproof rejects a high S and Core accepts it after normalization, so Wycheproof's result is not Core's. |
| Core's `key_tests.cpp` [C13] | The two deterministic signatures | Accepted. The public keys come from the pinned harness, with that provenance. |
| Section 4.1 | One key per row, plus each failure: `x ≥ p`, no square root, the wrong hybrid parity, off the curve | Core's result from the harness, checked against the source reading of C6 to C8. |
| Section 3 | The digest one of `SIGHASH_SINGLE`, signed by the harness signer | Accepted for `e = 2^248`, and rejected when the digest bytes are reversed. |

The P1363 cases are 64-byte `r ‖ s` pairs, so the test reads them as scalars and does not call `parseDerLax`.
At least one known answer runs through `decide +kernel` in the `Proofs` library, as EthLib's proofs do for one verification.

### The harness signer

A signed fixture needs a signer that is independent of DogeLib.
The recommended signer is a small program built with the Core harness, which calls `CKey::Sign` at the pin [C12] (decision 5).
It signs with fixed test keys and RFC 6979 nonces, so the signatures are deterministic and low-S.
It runs only to make fixtures and is not part of the comparison loop.
Each fixture records the keys, the unsigned transaction, the digest, the signatures, the harness revision and Core's verdict.
The Lean verdict is never the source of an expected value.

### Signed spends and mutations

The template is the 2-of-3 instance of `multisigRecoveryScript`, in a P2SH output with `p2shScriptPubKey`.
The fixtures use compressed keys, `SIGHASH_ALL`, and the flags `P2SH`, `STRICTENC`, `DERSIG`, `LOW_S`, `NULLDUMMY` and `CHECKLOCKTIMEVERIFY`.

| Mutation | Expected class of outcome |
| --- | --- |
| A change to a committed field: an output value, an output script, the version, a previous outpoint | Rejection, because the digest changes |
| The two multisig signatures in the reverse order | Rejection, because the ordered matching fails |
| The branch selector of the other branch, with the same signatures | Rejection |
| A lock time below 1,000,000, signed again | `UNSATISFIED_LOCKTIME` on the recovery branch |
| A lock time below 1,000,000, not signed again | Rejection by the signature check |
| A final sequence on the recovery input, signed again | `UNSATISFIED_LOCKTIME` |
| A high S for one signature | `SIG_HIGH_S` with `LOW_S`, and acceptance without it |
| A hybrid key in place of a compressed key, with `STRICTENC` clear and the spend signed again | Core's result |

Every row is a Core comparison, and the table gives only the expected class.
A row that Core decides differently is a finding against this table, not against Core.

## 9. Theorem targets

These targets need no Mathlib:

- `coreVerifier_invalidKey`, `coreVerifier_badPoint`, `coreVerifier_emptySig` and `coreVerifier_badDer`: steps 1 to 4 of section 3 give `some false`.
- `coreVerifier_normalize`: `coreVerifier` gives the same result for S and for `n − S`, for every key and digest.
- `coreVerifier_some`: `coreVerifier` never returns `none`.
- `transactionChecker_coreVerifier_some`: every `checkSig` request of `transactionChecker tx nIn coreVerifier` answers `some`, for a script code shorter than 2^64 bytes.
- `parsePubKey_hybrid`: a hybrid key parses exactly when the uncompressed key with the same coordinates parses and the parity matches.
- A corollary of `multisigRecovery_sound` with `coreVerifier` in place of the parameter, with no hypothesis about the verifier.

These targets need Mathlib and depend on decision 3:

- The group law and the prime field facts that EthLib proves.
- That a signature of SEC 1 signing verifies under `Ecdsa.verify`.
- That `parsePubKey` returns the encoded point, and accepts exactly the encodings of section 4.1.

No target states that `coreVerifier` equals Core's `CPubKey::Verify`.
Core's function is outside Lean, so that agreement stays an A1 claim with the evidence of section 8.

## 10. Decisions

**Date:** 2026-11-06. **Decision maker:** Maintainer.
Each proposal awaits the maintainer's decision:

| Number | Topic | Proposal | Status |
| --- | --- | --- | --- |
| 1 | Verifier backend | Option A: a pure Lean verifier adapted from EthLib, with the curve arithmetic unchanged. It replaces the choice of "a trusted backend for comparison" in design record 0003, section 8. Options B and C stay out of scope. | Proposed |
| 2 | Speed | Keep EthLib's affine arithmetic, at about 65 milliseconds per verification. A faster executable path waits until a stream needs it, and then needs an equality theorem with the affine definition. | Proposed |
| 3 | Proofs that need Mathlib | No adopted proof in the first lanes. The theorems of section 9 that need no Mathlib come first. A later lane proposes a package for the others. | Proposed |
| 4 | Oracle surface | The `transaction` checker uses `coreVerifier`, and the reason `signature_verifier` is removed. Add `pubkey.verify`. Both settle in the stage 3 pull request under the [development policy](../oracle.md#format-stability) of `dogelib-oracle/1`. | Proposed |
| 5 | Signer for fixtures | A program built with the pinned Core harness, which calls `CKey::Sign` with fixed test keys. DogeLib does not sign. | Proposed |
| 6 | Rust work | Implementation refinement and Rust extraction stay outside this scope. | Proposed |

## 11. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The verifier reads the digest in display order. | The digest-one known answer of section 8, which fails for the reversed order. The signed corpus inputs also detect it, because their signatures sign the digest in storage order. |
| The key parser rejects the hybrid encodings, as EthLib's decoder does. | A known answer for each prefix and parity, and the hybrid mutation of section 8. |
| A high S fails because normalization is missing. | `coreVerifier_normalize`, and the Wycheproof bitcoin cases with a high S through the Core comparison. |
| The overflow case of `parseDerLax` gives a nonzero scalar. | `parseDerLax` keeps that case, and a known answer checks it through `coreVerifier`. |
| Verification is too slow for a large stream. | The budget of section 5.5. The faster paths of decision 2 need a separate decision. |
| The fixtures and Core share a signer, so a signing fault is invisible. | The signer only makes inputs. The Lean verifier is an independent implementation that must accept them, and the mutations must fail in both. |
| The harness build differs from a release build of Core. | The harness records its build options, as it does for the existing comparison. |

There is no pin change, trust-policy exception, public API implementation or fixture-format change in this record.
Adoption of the scope does not establish any target theorem, and it does not authorize the merge of a later implementation.
