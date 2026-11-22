# Candidate lists of the historical impact runs

Each file `<NAME>.json` lists the candidate blocks of one range for the historical impact runs of [design record 0011](../../../docs/design/0011-mainnet-ranges.md), section 10.3, case 2, and [design record 0012](../../../docs/design/0012-relative-lock-time.md), section 10.3.
The lists are expectations for `scripts/impact_run.py`, and each list is committed before the runs of its range.

## Content

A candidate block has a spend whose scripts hold the opcode that a revision redefines, or a spend whose coin the script cannot find.
For `RelativeLockTime`, a block with a cutoff transaction or a sequence candidate is also a candidate.
`scripts/impact_candidates.py` states each definition.

A candidate covers spends only, as design record 0011, section 10.3, and design record 0012, section 10.3, define it.
The scripts of a spend are its `scriptSig`, the `scriptPubKey` of the coin that it spends, and the P2SH redeem script of that spend.
A `scriptPubKey` that a block creates does not make the block a candidate.
For `RelativeLockTime` the list counts each created output that holds `0xb2`, and whether the range spends it.

| Revision | Opcode | Other candidates |
| --- | --- | --- |
| `ExampleVersionVerify` | `0xb9` | A missing coin |
| `ExampleFaultyLocktime` | `0xb3` | A missing coin |
| `RelativeLockTime` | `0xb2` | A missing coin, a cutoff transaction, a sequence candidate |

Each file also has the counts of the range.
They are the transactions, the inputs, the outputs and the missing coins, and the counts of `RelativeLockTime`.
Those are the time lock times with an input that is not final, the cutoff transactions, the sequence candidates, the opcode spends, and each created output that holds `0xb2`.

| File | Heights | Start of the coins |
| --- | --- | --- |
| `genesis-10000.json` | 0 to 10,000 | The empty set |
| `genesis-145000.json` | 0 to 145,000 | The empty set |
| `short.json` | 9,001 to 10,000 | The snapshot at 9,000 |
| `S.json` | 100,001 to 101,000 | The snapshot at 100,000 |
| `A.json` to `H.json`, `E1.json`, `E2.json` | The ranges of design record 0011, section 4 | The snapshot of the Core pass at the range start |

Every list has 0 candidate blocks for each of the three revisions, and 0 missing coins.

## Provenance

The script reads the blocks file, the `chain` and the snapshot of the range request of `scripts/impact_run.py request`.
It runs no DogeLib code, so no implementation under test produced a list.
Each file names its blocks file by SHA-256.
`--check` fails when a committed file differs from the list that the script computes:

```bash
python3 -I scripts/impact_run.py request --range genesis-10000 --fixture build/mainnet-blocks/genesis-10000 --output build/impact/requests/genesis-10000
python3 -I scripts/impact_candidates.py --range genesis-10000 --request build/impact/requests/genesis-10000/request.json --check
```

## Limits

A list is a statement about the blocks of its range.
It says nothing about other heights, and nothing about unconfirmed transactions.
An empty list is not a compatibility proof.
The theorems `validateBlockWith_congr` and `relativeLockTime_eq_of_untouched` show that a block whose two verdicts differ is a candidate.
The script finds a redeem script only at its spend, so a created P2SH output can hide an opcode until a later block spends it.
