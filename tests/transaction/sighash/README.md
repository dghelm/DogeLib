# Dogecoin Core signature-hash corpus

`sighash.json` is `src/test/data/sighash.json` of Dogecoin Core `v1.14.9`, commit [`e0a1c15`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/sighash.json) (SOURCES.md, D26).
Core's test `sighash_from_data`, in `src/test/sighash_tests.cpp`, checks each record against `SignatureHash` with `SIGVERSION_BASE`.

- Licence: MIT. Copyright (c) 2009-2024 The Bitcoin Core developers, and (c) 2013-2024 The Dogecoin Core developers.
  The licence text is in `LICENSES/dogecoin-core-MIT.txt`, copied from `COPYING` at the same commit.
- Copy: byte for byte. The git blob ID of the file, `f49c46f`, equals the blob ID of `src/test/data/sighash.json` at `e0a1c15`.

The first record is a comment. Each of the other 500 records is `[raw_transaction, script, input_index, hashType, signature_hash]`:

- `raw_transaction` and `script` are hexadecimal bytes.
- `input_index` and `hashType` are signed decimal integers. Core stores them in an `int`.
- `signature_hash` is the digest in Core's display order, `uint256::GetHex`, which reverses the bytes.

The records give digests only, not preimages.

`SHA256SUMS` pins the file.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

`lake test` runs every record, from `tests/KnownAnswers/Transaction.lean`, through the compiled `DogeLib.Transaction.legacySignatureHash`.
