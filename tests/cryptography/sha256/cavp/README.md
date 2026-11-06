# NIST CAVP SHA-256 vectors

The two `.rsp` files are the byte-oriented SHA-256 files of the NIST CAVP secure-hashing test vectors, CAVS 11.0.
CAVP is NIST's Cryptographic Algorithm Validation Program.
For each message, a file gives the digest that a correct SHA-256 returns.

- Source: [`shabytetestvectors.zip`](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip), downloaded on 2026-11-03.
  The archive had SHA-256 digest `929ef80b7b3418aca026643f6f248815913b60e01741a44bba9e118067f4c9b8`.
- Licence: NIST material is public domain.
- Copy: byte for byte from the archive, including the CRLF line endings.
  `.gitattributes` keeps git from converting them.
  EthLib vendors the same two files, and their digests agree.

`SHA256SUMS` pins the two files.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

The pin shows only that the files are unchanged since they were copied.
To check them against NIST, download the archive and compare the files byte for byte.

`lake test` runs every vector, from `tests/KnownAnswers/Hash.lean`, through the compiled `DogeLib.Cryptography.Hash.Sha256.hash`.
