# Previous block hashes for the random subsidy

`prev-hashes.bin` contains the hashes of the Dogecoin mainnet blocks at heights 0 to 144,999.
It has 145,000 records of 32 bytes, with no separator, and is 4,640,000 bytes long.
Record `k`, counted from zero, is the hash of the block at height `k`, in the byte order of Core's `uint256`.
So it is the previous block hash of height `k + 1`.

Below height 145,000, Core derives the block subsidy from the previous block hash (SOURCES.md D104).
The Core comparison needs that hash for every height from 1 to 145,000.
The headers of those heights have 11.6 MB, and the comparison reads only their hashes.
A hash is the output of SHA-256, so the file does not compress.

## Source

The source is the public Electrum server `dogecoin.stackwallet.com`, TCP port `50022`, with TLS and the default certificate checks.
The fetch date is 2026-11-13 (UTC).
`scripts/fetch_subsidy_prev_hashes.py` sent 72 requests of this form, for at most 2,016 headers each:

```json
{"id":0,"method":"blockchain.block.headers","params":[0,2016]}
```

It read the 145,001 raw headers at heights 0 to 145,000.
To repeat the fetch into another file, run:

```bash
python3 -I scripts/fetch_subsidy_prev_hashes.py build/prev-hashes.bin
sha256sum build/prev-hashes.bin
```

No test fetches data, and no test overwrites the fixture.

The server is untrusted.
Before the script wrote the file, it checked the headers with Python's `hashlib`:

- Every header has 80 bytes.
- The previous-hash field of each header from height 1 to 145,000 is the double SHA-256 of the header before it.
- The hashes at heights 0, 104679 and 145000 are the checkpoints of Core at the pin (D9, `src/chainparams.cpp`, lines 182 to 184).

Those checks connect every record to Core's checkpoint at 145,000, subject to the hash commitment assumption.
The fixture holds the hashes alone, without the headers.
So no test can repeat the link checks from the fixture, and its bytes rest on the fetch and on `SHA256SUMS`.

Licence: the hashes are public chain data, not server software.
The checkpoint values come from MIT-licensed Dogecoin Core at the pin.
Core's licence is in [`LICENSES/dogecoin-core-MIT.txt`](../../../LICENSES/dogecoin-core-MIT.txt).

## Checks and coverage

`scripts/compare_core.py` sends each height from 1 to 145,000 with its record to the oracle and to Core's own `GetDogecoinBlockSubsidy`, in 145 `block.subsidy` requests.
The two programs must return the same subsidy for every height ([the comparison](../../../docs/oracle.md#block-subsidy)).
`scripts/oracle_subsidy.py` builds the requests.

The fixture has no expected subsidy.
The table `CORE_VALUES` of `scripts/oracle_subsidy.py` records 35 subsidies that Core's function returned for these hashes through the harness, at the pin with Boost 1.70.0, on 2026-11-13.
They are the heights 1, 2, 99999, 100000 and 144999, and the 30 heights below 145,000 for which the oracle reports a redraw.
`scripts/test_oracle.py` checks the oracle against that table, and the Core comparison computes the values again.
To capture them again, send the request of `core_values_request()` to `build/core-harness/core-oracle`.

The comparison shows agreement on these 145,000 inputs.
It does not show that a block at one of these heights is valid, or that its coinbase claims the subsidy.

`SHA256SUMS` pins `prev-hashes.bin`.
From this directory, check it with:

```bash
sha256sum -c SHA256SUMS
```
