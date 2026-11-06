# Block known answers

`lake test` checks pure headers, full headers with the AuxPoW payload, transaction Merkle roots and mutation flags.
The test never fetches data or overwrites expectations.
`SHA256SUMS` pins the four fixture files.

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

## AuxPoW headers

`auxpow-headers.json` records six whole mainnet blocks at the checkpoint heights 371337, 450000, 771275, 1000000, 2000000 and 3000000.
Each block starts with a full header: the 80-byte pure header, then the AuxPoW payload, because each version sets bit 8.
For each block, the fixture records the checkpoint hash, the flag and the length of the full header.
It also records the transaction count, the raw bytes and the payload fields.
Payload hashes are in serialized (internal) byte order. `txid` is in display order.

The source is a third-party explorer, Blockchair, fetched on 2026-11-06 at 16:25 UTC:

```text
curl -s "https://api.blockchair.com/dogecoin/raw/block/<checkpoint hash>"
```

The response has the exact raw block (`raw_block`) and, separately, the explorer's decoded fields (`decoded_raw_block`).
The explorer is untrusted. The independent checks below make the bytes acceptable as fixtures.
`import_auxpow_headers.py` wrote the fixture from the saved responses, with Python `hashlib` and its own parser of Core's stream format (D41, D54, D4, D1), not DogeLib:

```text
python3 -I tests/block/import_auxpow_headers.py <fetch-dir> tests/block/auxpow-headers.json
```

Before the import, `--self-test` checks its transaction reader on three hand-written transactions.
They are an empty input list with zero flags, which Core ends without an output count (D4, lines 220 to 226), a base form and an extended form with one empty stack.

It checks each block in these ways, and fails on any mismatch:

- The double SHA-256 of the first 80 bytes equals the Core checkpoint for the height (D9, `src/chainparams.cpp` lines 180 to 205).
- The payload fields equal the explorer's decoded `auxpow` object: the transaction bytes, its ID, both branches, both indices and the parent header.
  The decoded `tx.blockhash` is the parent header's hash, as Core's `AuxpowToJSON` writes it (`src/rpc/blockchain.cpp` line 91), so `hashBlock` has no decoded counterpart.
- The transaction list after the full header reads to the end of the block, and its IDs equal the decoded list.
  Their Merkle root equals bytes 36 to 67 of the header.

The checkpoint fixes only the 80-byte pure header.
The block hash does not cover the payload (D40, D41).
So the evidence for the payload is the explorer's decoded fields, not the checkpoint.
None of these blocks has witness data, so both read modes return the same header.

Design record 0004, section 7, requires the pinned Core harness to read each full header and record Core's result.
That check is pending: it belongs to stage 5, with the `block.header.read` oracle operation.

`lake test` reads each block in both modes.
It checks the consumed length, the remainder, the checkpoint hash, the flag, the re-encoding and `decodeComplete` on the header bytes.
It also checks the payload fields, and the transaction list and Merkle root of the remainder.
It checks that the reader rejects every proper prefix of each full header, 7222 prefixes in all.
It also reads the 315 flag-clear pure headers above as full headers without a payload, in both modes.

## Hand-written AuxPoW cases

`tests/KnownAnswers.lean` writes byte strings from Core's format: a pure header with only the AuxPoW flag set, a one-input transaction and zero payload fields.
They check these behaviours:

- The base form and the extended form with one empty witness stack read as one header in the witness-allowed mode (D4, lines 210 to 243). The writer emits the base form (D4, lines 245 to 263).
- Base mode reads the extended form as a different transaction, with no inputs and one output, and leaves 35 bytes. With `fAllowWitness` false, Core reads the empty input list and then an output list (D4, lines 219 to 230).
- Flags `02` fail with `unknownOptionalData`. A branch count of `0x02000001` fails with `tooLarge`. A set flag with no payload bytes fails with `truncated`.
- Every proper prefix of each hand-written header is rejected.

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

The mainnet headers, payloads and transactions are public chain data, not server software or explorer text.
The deterministic list construction adapts MIT-licensed Dogecoin Core test code.
The adaptation records fixed expectations and omits random sizes and branch tests.
Core's licence is in [`../../LICENSES/dogecoin-core-MIT.txt`](../../LICENSES/dogecoin-core-MIT.txt).
The original notice for `src/test/merkle_tests.cpp` is:

```text
Copyright (c) 2015-2016 The Bitcoin Core developers
Distributed under the MIT software license, see the accompanying
file COPYING or http://www.opensource.org/licenses/mit-license.php.
```
