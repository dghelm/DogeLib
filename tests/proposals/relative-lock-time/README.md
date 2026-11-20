# Cutoff candidates of `RelativeLockTime`

`cutoff-candidates.json` lists the candidate blocks of the cutoff count of [design record 0012](../../../docs/design/0012-relative-lock-time.md), section 10.3.
It is an expectation for a run of `scripts/compare_csv_forced.py`, and it is committed before that run.

## Content

The proposed revision `RelativeLockTime` replaces the lock-time cutoff of a block.
The baseline cutoff is the time of the block, and the revised cutoff is the median time past of the predecessor (BIP 113).
A *cutoff transaction* is a transaction that the change can reach:

- Its lock time is a time: at least 500,000,000.
- Its lock time is from the median cutoff to below the block time.
- One of its inputs has a sequence other than `0xffffffff`.

A *candidate block* has a cutoff transaction.
The file covers the 11,018 mainnet blocks of `block.contextual_check_body`, in three groups:

| Group | Blocks | Source |
| --- | ---: | --- |
| `genesis-10000` | 10,001 | Heights 0 to 10,000, an asset of the release that [`../../block/mainnet-blocks/release.json`](../../block/mainnet-blocks/release.json) pins |
| `recent-6455302-6456301` | 1,000 | Heights 6,455,302 to 6,456,301, an asset of the same release |
| `rule-changes` | 17 | The committed blocks of [`../../block/mainnet-blocks/rule-changes`](../../block/mainnet-blocks/rule-changes) |

For each group the file gives the count of transactions with a time lock time and an input that is not final, the count of cutoff transactions, and each candidate block with its transactions.
The list has 0 cutoff transactions and 0 candidate blocks.
Three transactions of the recent range have a time lock time and an input that is not final, and each lock time is below the median cutoff of its block.

## Provenance

`scripts/relative_lock_time_candidates.py` writes the file from the block bytes and the header times alone.
It computes each median as Core's `GetMedianTimePast` does: the sorted time at index n / 2 of the n predecessors, for n at most 11 (SOURCES.md, D18).
It runs no DogeLib code, so no implementation under test produced the list.
The header times of the predecessors come from the blocks of each group and from [`../../block/mainnet-blocks/version-bits-headers`](../../block/mainnet-blocks/version-bits-headers).

```bash
python3 -I scripts/fetch_release_blocks.py
python3 -I scripts/relative_lock_time_candidates.py --check
```

The second command fails when the committed file differs from the list that the script computes.

## Limits

The list is a statement about these 11,018 blocks.
It says nothing about other heights, and nothing about unconfirmed transactions, such as a signed transaction that waits for its lock time.
An empty list is not a compatibility proof.
`relativeLockTime_eq_of_cutoff_untouched` shows that a block without a cutoff transaction has one result under the baseline and under the revision with the rule of BIP 113.
