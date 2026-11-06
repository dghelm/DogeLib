# secp256k1 known answers

The `verify/` directory contains 252 P1363 records from EthLib commit `bb6dfe55198243682bc2eaf94611af2dbce1be6f`.
Each `data.yaml` and `verify/format.md` is unchanged.
`SHA256SUMS` contains their entries from EthLib's manifest, without the unrelated recovery and signing entries.

The original source is `C2SP/wycheproof`, commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, file `ecdsa_secp256k1_sha256_p1363_test.json`.
EthLib's fixture names preserve Wycheproof's test identifiers 1 through 252.
The expectations come from Wycheproof, not from DogeLib.
EthLib computed `msg_hash` as SHA-256 of each source message.

The data keeps the Apache License 2.0 in [LICENSES/wycheproof-Apache-2.0.txt](../../../LICENSES/wycheproof-Apache-2.0.txt).
The fixture directory also keeps the upstream `LICENSE` copy.
The complete Wycheproof tree at the source commit contains no `NOTICE` file.
The adaptation adds this README and selects the verification entries in the hash manifest.

`lake test` reads the uncompressed coordinates directly, without a public-key parser.
It requires 65 key bytes, prefix `04`, coordinates below `p`, and exactly 32 digest bytes.
For a 64-byte signature, it reads R and S big-endian and calls `Ecdsa.verify`.
That covers 234 scalar cases: 167 accepted and 67 rejected.
The other 18 records have `output: null` and a signature length other than 64.
They check the fixture boundary and do not call `Ecdsa.verify`.

Case 1 also runs through `decide +kernel` in `DogeLib.Cryptography.Proofs.Secp256k1.Ecdsa`.
Its digest is not a byte palindrome, so its accepted result exercises the byte order in a full verification.
A separate integer check fixes `01` followed by 31 zero bytes as `e = 2^248`, before reduction modulo `n`.
The driver forces each scalar verification with `IO.lazyPure` between the two clock reads.
Fixture IO and decoding occur outside the interval.
The design record's comparison point is about 1.15 milliseconds per verification, rather than a hard test threshold.

These cases test the scalar verifier, which accepts high S when the ECDSA equation holds.
They do not test Core's key parser, lax DER parsing or S normalization.
The oracle comparison covers Core's parsers and normalization through `pubkey.verify`.

The `bitcoin/ecdsa_secp256k1_sha256_bitcoin_test.json` file is unchanged from the same Wycheproof revision.
It comes through EthLib's pinned `bindings/python/tests/secp256k1/wycheproof/` copy.
The file contains 464 cases and keeps its Apache License 2.0 terms.
The comparator hashes each message with Python hashlib and sends its DER signature and uncompressed key to both programs.
Core supplies the verdict, since its high-S normalization differs from Wycheproof's non-malleability rule.

The `core/requests.jsonl` file comes from `build/core-harness/core-signer --verification-vectors`.
The generator uses Core's `key_tests.cpp` private scalars and its message `Very deterministic message` (D63, lines 19 to 22 and 167 to 177).
The two deterministic signatures match that test's literal signatures.
The generator also signs `01` followed by 31 zero bytes with each key.
Those bytes are the storage-order digest one, which Core passes directly to libsecp256k1.
The comparison adds each reversed digest and requires the Core verdict to agree with Lean.

`python3 -I scripts/check_signed_spends.py build/core-harness/core-signer` checks the four requests by byte-for-byte regeneration.
The generator's optional mode changes no signed-spend field except the source blob that records generator provenance.

`scripts/oracle_pubkey.py` constructs 36 infinity inputs from `Q = dG` and `e = -rd mod n`.
The choices are `d ∈ {1, 2, 3, n-1}`, `r ∈ {1, 2, n-1}` and `s ∈ {1, 2, n-1}`.
Thus `u1 G + u2 Q` is infinity, also after high-S normalization.

For 24 further inputs, the generator selects the first eight curve x-coordinates above `n`, sets `r = x-n`, and uses `s = 2`.
For each, it selects `e ∈ {0, 1, 2^248}` and constructs `Q = r⁻¹(sR-eG)` by affine integer arithmetic.
The verification point is then `R`, with `x ∈ [n,p)`.
Another 24 inputs retain Q and e but change S to 3.

A further 24 inputs retain R and e and use `r2 = r+1`.
They set `Q = r2⁻¹(sR-eG)` and use `r2` in the signature.
Their verification point remains R, with x above `n`, but `x-n ≠ r2`.
The Core harness alone supplies all comparison verdicts.
These constructions test the infinity and `r+n` branches of D60 without a Lean-generated expectation.
