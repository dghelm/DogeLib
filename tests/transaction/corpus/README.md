# Dogecoin Core transaction corpus

`tx_valid.json` and `tx_invalid.json` are `src/test/data/tx_valid.json` and `src/test/data/tx_invalid.json` of Dogecoin Core `v1.14.9`, commit [`e0a1c15`](https://github.com/dogecoin/dogecoin/tree/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data) (SOURCES.md, D28 and D29).
Core's tests `tx_valid` and `tx_invalid`, in `src/test/transaction_tests.cpp` (D30), read each transaction with witness data allowed and then check its scripts.

- Licence: MIT. Copyright (c) 2009-2024 The Bitcoin Core developers, and (c) 2013-2024 The Dogecoin Core developers.
  The licence text is in `LICENSES/dogecoin-core-MIT.txt`.
- Copy: byte for byte. The git blob IDs of the files, `a3f47fc` and `f7d9e18`, equal the blob IDs of the two files at `e0a1c15`.

A record is `[[prevouts], serializedTransaction, verifyFlags]`. Every other entry is a comment of one string.

| File | Records | Base mode | Witness serialization | Comments |
| --- | ---: | ---: | ---: | ---: |
| `tx_valid.json` | 118 | 91 | 27 | 125 |
| `tx_invalid.json` | 80 | 68 | 12 | 97 |

A record is in base mode when byte 4 of its transaction, the first byte of the input count, is not `00`.
A record of `tx_invalid.json` is a transaction that Core reads and then rejects for another reason, such as a script check.

`SHA256SUMS` pins the files.
To check the pin, run this from the directory:

```text
sha256sum -c SHA256SUMS
```

`lake test` reads and writes every base-mode transaction, from `tests/KnownAnswers/Transaction.lean`, through the compiled base-mode reader and codecs.
It also reads every record of both kinds with the reader of the witness-allowed format, `Transaction.readAllowWitness`, and writes each one again.

The format models serialization only.
Core rejects blocks with witness data on main and test at the pin (D9, D36).
The module documentation of `DogeLib.Transaction.Witness` records the separate consensus mechanisms.
The checks use Core's bytes as known answers. Core itself does not run.
