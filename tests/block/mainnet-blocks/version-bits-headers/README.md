# Version-bits headers for the block body comparison

`headers.bin` holds the raw 80-byte mainnet headers that `block.contextual_check_body` needs for the real-block ranges of design record 0010, section 4.
Core's `ContextualCheckBlock` reads the version-bits state at a block's aligned boundary.
So the comparison on a real block needs the contiguous headers from that boundary, and its ten predecessors, up to the block's predecessor.
The committed block fixtures already hold each block's own header.
So each run here ends just below the first committed block of its group, and the chain builder joins them.

`manifest.json` lists the runs, each with its first height and count, and the block it links to.
The file has 35,312 headers in six runs, 2,824,960 bytes, in height order.
Blocks that share an aligned boundary share one run, so a header is stored once.

| Run | First | Count | Joins block |
| --- | ---: | ---: | ---: |
| Rule change 144,998–145,001 | 141,109 | 3,889 | 144,998 |
| Rule change 371,336–371,338 | 362,869 | 8,467 | 371,336 |
| Rule change 599,998–600,001 | 594,709 | 5,289 | 599,998 |
| Rule change 1,034,382–1,034,384 | 1,028,149 | 6,233 | 1,034,382 |
| Rule change 3,464,750–3,464,752 | 3,457,429 | 7,321 | 3,464,750 |
| Recent 6,455,302–6,456,301 | 6,451,189 | 4,113 | 6,455,302 |

## Source

The source is the maintainer's mainnet node, which runs the signed Dogecoin Core v1.14.9 release, the pinned commit (design record 0010, decision 1).
The fetch date is 2026-11-13 (UTC).
`scripts/fetch_version_bits_headers.py` read each header with `getblockheader <hash> false` and hashed it.
It checked that each header links to the header before it and matches any pinned checkpoint at its height.

The headers are **linked**, not independently **pinned**.
No run contains a Core checkpoint height (SOURCES.md D9).
So the fetch authenticated each run by the double-SHA-256 link from its last header to the first committed block of its group.
The committed blocks carry their own provenance in the rule-change and release block fixtures.

Four rule-change groups are pinned through those fixtures.
The groups 144,998–145,001 and 371,336–371,338 are pinned through the checkpoints 145,000 and 371,337 and the committed header fixtures.
The groups 1,034,382–1,034,384 and 3,464,750–3,464,752 are pinned through the BIP66 and BIP65 header fixtures.
So the runs that join those four groups are pinned transitively.
The group at 599,998–600,001 and the recent range are node-sourced, so their runs are linked to node-sourced blocks, as the block fixtures record.
A `uint256S` display-order checkpoint that a future run contained would be checked against D9, and `manifest.json` records any that a run holds.

To re-fetch into another directory, run:

```bash
python3 -I scripts/fetch_version_bits_headers.py path/to/out
```

`python3 -I scripts/fetch_version_bits_headers.py --check` re-verifies the committed file: the hashes, the intra-run links, the joins to the committed rule-change blocks, and the pinned checkpoints.
The pinned-vectors gate checks `SHA256SUMS`.
