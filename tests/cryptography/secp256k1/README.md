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
The bitcoin Wycheproof set, Core deterministic signatures and signed digest-one case of design record 0005 need those interfaces.
They belong to stage 2 and its Core harness evidence.
