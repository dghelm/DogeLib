# Real mainnet blocks

These fixtures hold complete Dogecoin mainnet blocks: the full header, with its AuxPoW payload if it has one, and every transaction.
The Core comparison runs `block.check` with both flags on each block (design record 0010, section 4, exit condition 1).

| Set | Heights | Blocks | Stored |
| --- | --- | ---: | --- |
| Rule changes | 144,998 to 145,001, 371,336 to 371,338, 599,998 to 600,001, 1,034,382 to 1,034,384, 3,464,750 to 3,464,752 | 17 | [`rule-changes/`](rule-changes), committed |
| Genesis to 10,000 | 0 to 10,000 | 10,001 | Release asset |
| Recent | 6,455,302 to 6,456,301 | 1,000 | Release asset |

The subsidy rule changes at 145,000 and at 600,000, and the first AuxPoW block is 371,337.
BIP34 and BIP66 start at 1,034,383, and BIP65 at 3,464,751.
`block.check` reads none of those heights.
The blocks show that the check agrees with Core on the block forms of each period.

## Source

The source is the maintainer's mainnet node, which reported the version `/Shibetoshi:1.14.9/ (1140900)` (design record 0010, decision 1).
The fetch date is 2026-11-13 (UTC), and the node's tip was at height 6,456,361.
`scripts/fetch_blocks.py` read each block with `getblockhash` and `getblock <hash> false`:

```bash
python3 -I scripts/fetch_blocks.py --heights 144998,144999,145000,145001,371336,371337,371338,599998,599999,600000,600001,1034382,1034383,1034384,3464750,3464751,3464752 --output tests/block/mainnet-blocks/rule-changes
python3 -I scripts/fetch_blocks.py --range 0 10000 --output build/fetch/genesis-10000
python3 -I scripts/fetch_blocks.py --recent 1000 --output build/fetch/recent
```

The recent range ends 60 blocks below the tip, the default of `--confirmations`.
A second fetch of `--recent` gives other blocks, so the committed hashes fix this range.

Each fixture has the format `dogelib-blocks/1`, which the documentation of `scripts/fetch_blocks.py` defines.
`blocks.bin` holds the raw blocks, and `manifest.json` holds one record for each block: height, hash, size, number of transactions, and the label `auth`.
No test fetches from the node, and no test overwrites a fixture.

## Authentication

The node is untrusted.
Before the script wrote a block, it checked that:

- the block parses exactly, with no bytes after the last transaction
- the double SHA-256 of the 80-byte header is the hash that `getblockhash` returned
- the Merkle root of the transaction IDs is the root in the header, with no duplicated pair
- the previous-hash field is the hash of the block below
- the hash equals each pinned hash that the repository has for the height.

`python3 -I scripts/fetch_blocks.py --check DIR` repeats those checks on a fixture without a node.
The label `auth` of each block records the result of the last check:

| Set | `pinned` | `linked` | Pinned by |
| --- | ---: | ---: | --- |
| Rule changes | 13 | 4 | [`tests/work/mainnet-headers`](../../work/mainnet-headers) for 144,998 to 145,001, [`mainnet-subsidy-prev-hashes`](../mainnet-subsidy-prev-hashes/README.md) for 144,998 and 144,999, [`mainnet-auxpow-activation-headers`](../mainnet-auxpow-activation-headers) for 371,336 to 371,338, [`mainnet-bip66-headers`](../mainnet-bip66-headers) for 1,034,382 to 1,034,384, [`mainnet-bip65-headers`](../mainnet-bip65-headers) for 3,464,750 to 3,464,752, and Core's checkpoints at 145,000 and 371,337 (D9) |
| Genesis to 10,000 | 10,001 | 0 | `mainnet-subsidy-prev-hashes` for every height, and Core's checkpoint at 0 |
| Recent | 0 | 1,000 | None |

A `pinned` block has a hash that a committed fixture or a Core checkpoint gives.
With the Merkle check, that hash commits to every transaction ID of the block, if SHA-256 is collision resistant.
It does not commit to the bytes of an AuxPoW payload or to witness data.

A `linked` block has no pinned hash.
The four linked blocks of the rule changes are 599,998 to 600,001, and every block of the recent range is linked.
Such a block is consistent with its own header and with its neighbours in the fixture, and nothing connects it to a pinned hash.
The first block of each linked run was compared only with the node's own answer for the height below it.
The manifest records that as `"previous": "node"`.
So the statement that these bytes are the mainnet blocks of those heights rests on the node.
The highest checkpoint of Core at the pin is at height 5,050,000, below the recent range.

The comparison adds one check for every block, pinned or linked: Core's own `CheckBlock` accepts it with `fCheckPOW` true.
So the header, or the parent header of the AuxPoW payload, has a scrypt digest that meets the target of the block's own `nBits`.
No check compares that `nBits` with the difficulty that the chain requires at the height.
[SOUNDNESS.md](../../../SOUNDNESS.md#d3-wrong-fixtures) states what the comparison shows for a linked block.

## Sizes and storage

| Set | Bytes of the blocks | `blocks.bin` | `blocks.bin` with xz | `manifest.json` | `manifest.json` with xz |
| --- | ---: | ---: | ---: | ---: | ---: |
| Rule changes | 344,408 | 344,544 | 268,444 | 4,250 | 1,460 |
| Genesis to 10,000 | 43,937,365 | 44,017,373 | 31,077,776 | 1,490,331 | 389,756 |
| Recent | 19,939,510 | 19,947,510 | 14,701,988 | 153,517 | 41,956 |

The largest fixture that the repository holds is `mainnet-subsidy-prev-hashes`, with 4.64 MB.
Genesis to 10,000 has 44 MB, and 31 MB with xz, so it is not committed.
Under decision 2 of design record 0010, it and the recent range are assets of the GitHub release `fixtures-mainnet-blocks-2026-11-13`.
The largest block is 112,620 bytes at height 8,084 in the first range, and 284,395 bytes at height 6,456,196 in the recent range.
996 blocks of the recent range have an AuxPoW payload, and no block up to 10,000 has one.

[`release.json`](release.json) has the format `dogelib-block-assets/1`.
It names the repository and the tag of the release.
For each range it gives the heights and the number of blocks.
Each range has two files.
For each file it gives the asset name, and the size and SHA-256 of the asset and of the decompressed file.

`scripts/fetch_release_blocks.py` restores the two fixtures under `build/mainnet-blocks`:

```bash
python3 -I scripts/fetch_release_blocks.py
```

It downloads each asset without credentials and requires the committed size and SHA-256 before and after decompression.
It then runs the checks of `scripts/fetch_blocks.py --check` on each fixture.
A fixture whose files already have the committed hashes needs no download.
`python3 -I scripts/test_fetch_release_blocks.py` tests the script on synthetic blocks, with a planted fault for each check.

The assets were made from the fetched fixtures with `--pack`, which also printed the entries of `release.json`:

```bash
python3 -I scripts/fetch_release_blocks.py --pack build/fetch/genesis-10000 genesis-10000 --assets build/assets
python3 -I scripts/fetch_release_blocks.py --pack build/fetch/recent recent-6455302-6456301 --assets build/assets
```

## Checks and coverage

`scripts/oracle_block_check.py` builds the requests, and `scripts/compare_core.py` compares the oracle with Core's `CheckBlock`.

The full comparison holds the set *mainnet rule changes*, with 168 requests on the 17 committed blocks.
Each block passes with both flags, in both reader modes.
Four mutations of each block follow, with the expected result read from Core's text:

- another lock time in the last transaction gives `bad-txnmrklroot` with both flags, and passes without the Merkle test
- a longer transaction list with the same Merkle root gives `bad-txns-duplicate` with both flags, and passes without the Merkle test. 16 blocks have such a list, and the block with one transaction has none
- another nonce in the header that carries the work gives `high-hash`, and passes without the header test
- one byte fewer gives the read error `truncated`, and one byte more gives `trailing_bytes`.

A synthetic block has no work.
So the earlier sets reach `bad-txns-duplicate` only without the header test.
They reach `bad-txnmrklroot` after a passed header test only with another transaction list under a real header.

`python3 -I scripts/compare_core.py --mainnet-blocks build/mainnet-blocks <oracle> <harness>` compares the two ranges: 11,001 requests, one for each block, with both flags in the mode `allow_witness`.
The run requires the committed hashes of `release.json` for each file, and it fails with `BLOCK_ASSETS` without them.
Both programs must return a valid verdict, and the hash, the number of transactions and the base size that the manifest gives.

Three blocks of the recent range, at heights 6,455,642, 6,456,071 and 6,456,247, have a base size 36 bytes below their size.
The coinbase transaction of the parent block in their AuxPoW payload is in the extended format, with one witness item of 32 bytes.
`CheckBlock` measures the block without those bytes.
The expected base size of each request is the size without the witness data of that transaction, which Python computes from the bytes.
The mode `base` does not read the extended format, so it cannot read these three blocks.
No committed block has such a payload.

Licence: the blocks are public chain data, not node software.
The checkpoint values come from MIT-licensed Dogecoin Core at the pin, whose licence is in [`LICENSES/dogecoin-core-MIT.txt`](../../../LICENSES/dogecoin-core-MIT.txt).
