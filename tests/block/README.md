# Block known answers

`lake test` checks pure headers, transaction Merkle roots and mutation flags.
The test never fetches data or overwrites expectations.
`SHA256SUMS` pins the three fixture files.

## Mainnet blocks

`mainnet.json` records raw pure headers and base transactions at heights 1, 3000 and 4000.
These blocks have one, three and two transactions.
The source is `dogecoin.stackwallet.com`, TCP port 50022, with TLS.
The fetch date is 2026-11-05 (UTC).
The requests use Electrum JSON-RPC:

```text
blockchain.block.header [height]
blockchain.transaction.id_from_pos [height, position, false]
blockchain.transaction.get [txid, false]
```

Positions start at zero and increase until the server returns an error for the first absent position.
The raw header commits to the transaction list, so an incorrect termination cannot silently shorten an accepted fixture.
The fixture records the transaction IDs and raw bytes in position order.

| Height | Block hash in display order |
| --- | --- |
| 1 | `82bc68038f6034c0596b6e313729793a887fded6e92a31fbdf70863f89d9bea2` |
| 3000 | `a0ec0c60566646efb29aa45508c830ea43159dea3cd5e74e652debf417d5a75a` |
| 4000 | `0ef21338533aa9937d0e0294d1b8694c31a16c4231d4c685c7e09429c8bc827e` |

An independent Python `hashlib.sha256` computation supplies each recorded block hash as double SHA-256 of the raw 80 bytes.
Before import, Python checked every raw transaction against its server-supplied ID.
It reconstructed each Merkle root with odd-level duplication and compared the result with bytes 36 through 67 of the raw header.
Thus the expected Merkle roots come from serialized headers, not explorer JSON fields.
`lake test` repeats these checks through DogeLib's pure header codec, block hash, transaction ID and `blockMerkleRoot`.

The source is untrusted, and these isolated blocks have no authenticated chain connection or proof-of-work check.
The checks establish consistency with the recorded commitments, subject to the hash commitment assumption.

The genesis transaction and header are the literals in `tests/KnownAnswers.lean`.
Their expected commitments come from Core's `src/chainparams.cpp` at the SOURCES.md pin (D9).

## The existing header range

The 312 headers at heights 144719 through 145030 retain their provenance in [`../work/mainnet-headers/README.md`](../work/mainnet-headers/README.md).
For the first 311, the next recorded header's previous-hash field supplies the expected hash.
`last-header-hash.txt` records the hash of the final raw header, in display order.
Python `hashlib.sha256` applied twice supplied that expectation on 2026-11-05 (UTC).
It is an independent computation, not output from Core.

`lake test` checks exact encoding, hash equality, suffix preservation and rejection of all 80 proper prefixes for each header.
The existing checkpoint test also remains in place.

## Deterministic Merkle cases

`merkle.json` uses the deterministic portion of `src/test/merkle_tests.cpp`, `merkle_test`, at Core commit `e0a1c157791544e818c901bd9341896965afbf9d`.
Each initial transaction has version 1, empty inputs, empty outputs and locktime equal to its zero-based position.
Its base bytes are `01 00 00 00 00 00` followed by four little-endian locktime bytes.
Sizes range from 0 through 16.
Each mutation duplicates the final `n & -n` leaves, unless that would duplicate the entire tree.

There are at most three successive mutations per initial list.
Core's loop excludes size zero through its early break.
This fixture adds the empty case with the zero root and a false mutation flag from `MerkleComputation`.
The resulting 34 records include odd levels, complete-subtree duplicates and final sweeps across several levels.

Python `hashlib` computes transaction IDs and roots independently of DogeLib.
Its mutation computation transcribes the production leaf pass and final sweep, rather than a scan of padded levels.
The test checks each record's root and mutation flag, and checks every unmutated leaf list against DogeLib's transaction IDs.

A local C++ driver also passed all 34 leaf lists to the pinned `ComputeMerkleRoot`.
Its roots and mutation flags agreed with every recorded expectation.
The build used unmodified `merkle.cpp`, `sha256.cpp`, `uint256.cpp` and `utilstrencodings.cpp` from the pin, with unused sections discarded.
The committed [Core harness and comparator](../../docs/oracle.md#the-core-harness) repeat the fixture comparison and add generated subtree duplications.
These finite cases do not prove equivalence to Core for every input.

The Core compatibility domain has at most 2^31 leaves because larger lists can wrap its final sweep counter.
[SOUNDNESS.md](../../SOUNDNESS.md#pure-headers-and-transaction-merkle-roots) explains the wrap and undefined shift at the pinned revision.
The Lean definitions remain total on all finite lists without a rejection rule.

## Licence

The mainnet headers and transactions are public chain data, not server software or explorer text.
The deterministic list construction adapts MIT-licensed Dogecoin Core test code.
The adaptation records fixed expectations and omits random sizes and branch tests.
Core's licence is in [`../../LICENSES/dogecoin-core-MIT.txt`](../../LICENSES/dogecoin-core-MIT.txt).
The original notice for `src/test/merkle_tests.cpp` is:

```text
Copyright (c) 2015-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
```
