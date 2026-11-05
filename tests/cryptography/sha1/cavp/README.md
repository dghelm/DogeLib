# NIST CAVP SHA-1 vectors

These three files are the byte-oriented SHA-1 vectors of NIST's Cryptographic Algorithm Validation Program (CAVP).
The short and long files identify CAVS 11.0, and the Monte Carlo file identifies CAVS 11.1.
They contain 65 short messages, 64 long messages and 100 Monte Carlo checkpoints.

The source is [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip), downloaded on 2026-11-05 UTC.
The archive's SHA-256 digest is `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`.
NIST material is public domain.
The `.rsp` files are byte-for-byte copies, with their CRLF line endings preserved by `.gitattributes`.
`SHA256SUMS` pins their bytes.

To check the files from this directory, run:

```text
sha256sum -c SHA256SUMS
```

The checksum confirms that the committed bytes are unchanged.
It does not establish the correctness of their expected digests.

`lake test` runs these files through compiled `DogeLib.Cryptography.Hash.Sha1.hash`.
The short and long tests hash the first `Len / 8` bytes of each message, including the empty message's `Msg = 00` placeholder.

The Monte Carlo test follows [SHAVS §6.4, Figure 1](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/SHAVS.pdf).
For each checkpoint, three digest registers start at the seed.
Each of 1,000 steps hashes their concatenation and shifts the registers.
The last digest is the checkpoint and the next seed.
The test compares every checkpoint with its NIST digest.
These tests provide finite conformance evidence, not NIST validation or a SHA-1 security property.
