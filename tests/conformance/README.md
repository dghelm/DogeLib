# The conformance corpus

This directory holds the expected results of the conformance corpus ([design record 0011](../../docs/design/0011-mainnet-ranges.md), stage 5).
[docs/conformance.md](../../docs/conformance.md) defines the formats and the steps of a run.

| File | Content |
| --- | --- |
| `ranges/<range>/expected.jsonl` | The expected results of one range, in the format `dogelib-range-results/1`. They are the results of the Core harness |
| `release.json` | The release of the blocks and the range requests, in the format `dogelib-corpus-assets/1`. It gives the size and the SHA-256 of each asset and of each file |
| `SHA256SUMS` | The SHA-256 of each expected-results file |

[`tests/generators.toml`](../generators.toml) records the run that wrote each expected-results file: the programs, their commits, the SHA-256 of the inputs and the times.

## How the files were made

The maintainer's machine holds the inputs: the block fixtures of the ranges, the snapshots of the Core pass, and the source requests.
The source request of a range is the request of `scripts/impact_run.py request`, and it gives the chain context of the range.
The snapshots are not published ([docs/conformance.md](../../docs/conformance.md#the-snapshot-dogelib-coins1)).

1. For each range, `scripts/conformance.py request` wrote the range request with the restricted coins, and the block fixture of the range:

   ```bash
   python3 -I scripts/conformance.py request --range <range> --source <source-request> --snapshot <snapshot> --fixture <fixture> --output build/conformance-work/<range>
   ```

   The snapshot must have the size and the SHA-256 of its committed manifest in `tests/block/mainnet-blocks/snapshots`.
   For the short range, the fixture is the released fixture of heights 0 to 10,000, which the command cuts to heights 9,001 to 10,000.

2. For each range, `scripts/conformance.py compare` ran the Core harness and the oracle on the request, and wrote the results of both:

   ```bash
   python3 -I scripts/conformance.py compare --range <range> --dir build/conformance-work/<range> [--recorded <range-oracle-response.json>] .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
   ```

   The two responses must agree in every field of the full comparison, and the checker must pass on the oracle's results against the harness's.
   `--recorded` names a response of a recorded run of the range on the whole coin set. The block records of the run must equal its records.

3. The harness's results of each range became `ranges/<range>/expected.jsonl`, and `scripts/conformance.py record` wrote `tests/generators.toml` and `SHA256SUMS`.

4. `scripts/conformance.py pack` wrote the assets and `release.json`:

   ```bash
   python3 -I scripts/conformance.py pack --work build/conformance-work --assets build/conformance-assets --tag <tag>
   ```

A change of an expected-results file needs a new run of step 2 and a new table in `tests/generators.toml`.
A change of an asset needs a new release with a new tag.
