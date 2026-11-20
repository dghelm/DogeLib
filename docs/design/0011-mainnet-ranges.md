# Mainnet coin-set replay above height 145,000

**Status:** Draft, proposed on 2026-11-20.
No part of this record is adopted, and every decision of section 11 has the status `Proposed`.

**Date:** 2026-11-20
**Companions:** [Design record 0010](0010-block-validity.md), [oracle contract](../oracle.md), [coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md) and the [block fixtures](../../tests/block/mainnet-blocks/README.md).

## 1. Purpose

`block.validate` agrees with Core on mainnet from the genesis block to height 145,000 ([recorded run](../oracle.md#replay-of-mainnet-to-height-145000)).
Most of the rules of the chain today start above that height: AuxPoW at 371,337, BIP34 and BIP66 at 1,034,383, and BIP65 at 3,464,751.
The replay does not reach them.

A serial replay from the genesis block cannot reach them at the speed of the oracle (section 2).
A range that starts above the genesis block needs the coin set at its start.
Design record 0010, section 5, planned a fetch tool for the coins of the recent range.
That tool needs each funding transaction, and the maintainer's node has no transaction index.

This record proposes coin-set snapshots.
The Core harness replays the chain once and writes its coin set at chosen heights.
The oracle starts a range from a snapshot, checks each block against Core, and checks the digest of the whole set at the end.
The record gives the ranges, the storage, the options for the recent range, the costs and the stages.

Core is Dogecoin Core at the pin `e0a1c157`. Line numbers refer to `src/validation.cpp` unless a file is named.

## 2. Measurements

The measurements come from the recorded runs and from the blocks of two fixtures on disk.
A script read the blocks and counted their transactions, inputs and outputs. It ran no oracle and no node.
An *input* below is an input of a transaction other than a coinbase.

| Quantity | Heights 0 to 145,000 | Heights 6,455,302 to 6,456,301 |
| --- | ---: | ---: |
| Blocks | 145,001 | 1,000 |
| Bytes of the blocks | 3,023,283,774 | 19,939,510 |
| Transactions | 8,629,425 | 26,419 |
| Inputs | 15,048,625 | 56,518 |
| Inputs that spend a coin that the range creates, in the same block or an earlier one | 15,048,625 | 38,441 |
| Inputs that spend a coin from below the range | 0 | 18,077 |
| Transaction IDs of the coins from below the range | 0 | 15,999 |
| Largest number of inputs in one transaction | 675 | 568 |
| Outputs that enter the coin set | 20,143,296 | 63,002 |

The input and output counts of the first column equal the `spent` and `created` totals of the recorded run.
In the recent range, 11,378 of the 63,120 outputs are Pay to Script Hash (P2SH), and 51,402 are Pay to Public Key Hash.

**Cost for each input.**
The recorded run took 61,365 seconds in the oracle and 1,340 seconds in Core, each on one core.
That is 4.1 ms for each input in the oracle and 89 µs in Core, with all other work included.
Pull request 173 measured the parts: about 1.5 ms for one ECDSA verification, and the rest mostly SHA-256 of signature-hash preimages.

**Cost of the set.**
The oracle's digest of the whole set costs about 13 µs for each coin (pull request 173).
At height 145,000 the set has 5,094,671 coins, so one digest takes about 66 seconds.

The oracle's resident memory was 7.6 GB at height 112,000, with about 5.3 million coins.
That is about 1.4 KB for each coin, with everything else that the process holds.
It is one observation, not a bound for a larger set.
A coin record of a Pay to Public Key Hash output has 76 bytes ([digests](../oracle.md#digests)).
So the set at height 145,000 has about 0.39 GB as records.

**The whole chain.**
No measurement of this record covers the chain above height 145,000, except the recent range.
Core's `chainTxData` gives 226,128,837 transactions from the genesis block to height 5,050,000 (`chainparams.cpp`, lines 207 to 215).
The two ranges above have 1.74 and 2.14 inputs for each transaction.

Take 226,128,837 transactions with 1.74 to 2.14 inputs each, to height 5,050,000.
Add the 1,405,301 blocks from there to the recent range, at the 56.5 inputs for each block of the recent range.
The sum is about 0.47 to 0.56 billion inputs.
It assumes that the two measured ratios bound the chain between them, which nothing here shows.

At the measured costs, Core then needs about 12 to 14 hours on one core.
The oracle needs about 22 to 27 days on one core.
These numbers are estimates. The cost of an input can differ where many inputs spend P2SH outputs.

Three quantities are unknown, and stage 0 measures them:

- The bytes of the whole chain.
- The number of coins in the set at the tip.
- The memory that the harness needs for that set.

The development machine had 122 GB of free disk space on 2026-11-20.
So the plan below does not store the whole chain.

## 3. Snapshots

A *snapshot* at height `h` is the coin set after the accepted block at height `h`, written as a file.
A *range* from `a + 1` to `b` starts from the snapshot at `a`.

### 3.1 Format

A snapshot file is the sequence of the coin records of the whole set, in the order of `set_digest_hex` ([digests](../oracle.md#digests)).
Each record has the tag 2, the outpoint, the height, the coinbase byte and the serialized output.
The transaction IDs are in the order of their bytes, and the outputs of one ID are in index order.
The fixed part of a record and the CompactSize length of its script give its length, so the file needs no other framing.

The digest of a snapshot is the existing digest of the whole set.
A reader computes it from the records as it reads them, with no second format.
A manifest names the height, the block hash, the number of coins, the digest, and the size and SHA-256 of the file.
The proposed format name is `dogelib-coins/1`.

A reader rejects a file with any of these faults:

- A tag other than 2, or bytes after the last complete record.
- A record that is not above the record before it in the order of the set.
- Two records of one transaction ID with different heights or coinbase bytes.
- An amount outside the range from 0 to `MAX_MONEY` as a signed 64-bit value, which excludes the amount -1 of a null output.
- An output index of 1,048,576 or more, or a script that `IsUnspendable` rejects.
- A height above 2,147,483,646, or a coinbase byte other than 0 and 1.
- A script length that is not in the shortest CompactSize form.

The `coins` argument has the same limits on the amount, the index, the script and the height today.
The record does not hold the version of the transaction, as the `coins` argument does not.

### 3.2 How the harness writes a snapshot

Dogecoin Core 1.14 has no command that writes the coin set at a past height.
The harness already carries the set through a `block.validate` request in a `std::map` (`harness/core/core_block_validate.inc`).
Core's `uint256` compares its bytes with `memcmp` (`uint256.h`, line 48), so the map already has the order of the digest.

The proposal adds two arguments to `block.validate` in the harness:

- `coins_file`: the path of a snapshot, in the place of `coins`. The harness loads the whole file into its set, and reports the digest and the number of the coins that it read.
- `snapshot_heights` with `snapshot_dir`: after each accepted block at a listed height, the harness writes its set as a snapshot file and reports its digest.

The *Core pass* is one replay of the chain from the genesis block by the harness, in segments.
Each segment is one request, and it starts from the snapshot at the end of the segment before it.
It writes a snapshot at its own end and at each range start inside it.
It also reports the digest of the whole set at each range end, with or without a file.
A segment has at most 100,000 blocks.
So an interrupted pass continues from the last snapshot, and no response holds more block records than the recorded run did.

**Context of a segment.**
The digest of a coin set does not commit to a block hash or to the chain below it.
So the pass keeps every header that it accepts, and the manifest of each snapshot names the hash of its block.
The pass script requires that the first block of a segment names that hash as its previous hash.
It builds `chain` and `bip34_ancestor_hex` for the segment from its kept headers.
Every request of the pass has both flags true and the same adjusted time.

**The CSV window.**
The harness refuses a request whose aligned boundary has a median time between the CSV start and the CSV timeout (`harness/core/core_block_validate.inc`, line 322).
A pass from the genesis block must cross those heights, about 1.2 million to 1.72 million.
So the pass needs a change of the harness first.
Each entry of `chain` gains the version of its header, and the harness removes the refusal.

Core's own `VersionBitsState` then walks the supplied entries and the accepted blocks.

A segment that starts inside the window gets a dense chain back to the last boundary below the CSV start.
The chain also holds the ten real headers below that boundary.
Core reads the median time of that boundary from them (`versionbits.cpp`, line 44, and `chain.h`, line 286).
The chain has up to about 525,000 entries, and the harness refuses a shorter one.
This change is a condition of stage 2. The same change in the oracle is the option of stage 4.

**Arithmetic.**
Core adds amounts in `ConnectBlock` with no range check, and an overflow is undefined behaviour (design record 0010, section 3).
In a comparison, the oracle's `out_of_domain_at` keeps such a block from the harness.
The pass runs blocks that the oracle never reads, so it has no such guard.

The proposal builds the harness of the pass with `-fsanitize=signed-integer-overflow` and `-fno-sanitize-recover`.
The flags apply to the compilation of Core's `validation.cpp` and `coins.cpp`, which hold the sums.
An overflow then ends the pass with an error, and the lane stops and reports the block.
The record does not claim that any block of mainnet overflows.

The pass checks every script, as the harness does today: `hashAssumeValid` is null and no check thread runs.
The pass computes the digest of the whole set only at the listed heights: where it writes a snapshot, and at each range end.
The existing digest at each multiple of 1,000 would cost one pass over the set for each 1,000 blocks.
No measurement supports that cost at the size of the set today.

If the map does not fit in memory, the harness can carry the set in Core's own `CCoinsViewDB` on a scratch directory (`txdb.h`, line 71).
Its cursor visits the transaction IDs in key order, which is also the order of their bytes (`txdb.cpp`, lines 93 to 104).
Stage 0 decides between the two.

### 3.3 How the oracle starts from a snapshot

The oracle cannot hold the set of a recent height.
If the ratio of section 2 holds, 30 million coins need about 42 GB.
But a range reads few entries of its start state.
The recent range reads 15,999 transaction IDs from below its first block.

`validateBlock` reads and changes entries of the coin set by transaction ID alone.
Let `T` be the IDs that the blocks of a request name.
They are the ID of each transaction, and the ID in each outpoint that an input spends.
The first group covers the BIP30 test and the new entries.
The second group covers the input tests, the P2SH sigop count and the spends.

The proposal adds `coins_file` to `block.validate` in the oracle, for a request with `blocks_file`:

1. The oracle reads the blocks once and collects `T`.
2. It reads the snapshot once. It computes the digest of all records, and keeps the entries whose ID is in `T`. The response reports the digest and the number of coins as `start_set_digest_hex` and `start_set_coins`.
3. It runs the blocks on the kept entries, as today. The record of each block has the verdict and the digest of the coin changes. No record has a digest of the whole set.
4. It reads the snapshot again and computes the digest of the end state. That state is the records of the file whose ID is not in `T`, merged in order with the entries of the run. The response reports the digest as `set_digest_hex`, with `set_coins`.

The oracle holds only the entries of `T`.
Each read of the file costs time in the size of the set.
The measured digest cost gives about 13 µs for each coin, or about 22 minutes for 100 million coins.
The executable reads the files in `Exports.respondIO`, as it reads `blocks_file`, and no theorem covers a file read (SOUNDNESS.md, B4).

The steps are correct only if the run on the kept entries equals the run on the whole set.
The theorem target `validateBlock_restrict` states that claim:
take a coin set `s`, and a set `T` that contains every ID that the block names.
Write `s|T` for the entries of `s` with an ID in `T`.

Then `validateBlock` gives the same error or the same verdict on `s` and on `s|T`, with the same coin changes.
For an accepted block, write `s'` and `r'` for the two returned sets.
Then three statements hold:

- `s'` and `r'` have equal entries for every ID in `T`.
- `r'` has no entry outside `T`.
- `s'` and `s` have equal entries for every ID outside `T`.

The two results are not equal as values, because the returned sets differ outside `T`.
Set equality here means equal entries for each ID.
The statement needs the invariant that each entry is under the key of its own ID.
The name is a proposal.
Until a proof exists, a test gives the only evidence: both forms of the request give equal responses on ranges below height 145,000 (stage 1).

### 3.4 What a range from a snapshot shows

Take a range from `a + 1` to `b`, and write `D(h)` for the digest that the Core pass reported at height `h`.
The comparator sends the oracle and the harness the same request, with the snapshot at `a` and the blocks of the range.
A range agrees when all of these hold:

- Both programs report the start digest `D(a)`, and the number of coins of the manifest.
- Both programs accept every block, with equal block records and equal digests of the coin changes.
- Both programs report the end digest `D(b)`.

The comparison then shows this statement.
Suppose that the snapshot at `a` is Core's coin set at height `a`.
Then the Lean definitions and Core give the same verdict and the same coin changes on each block of the range.
They also give the same coin set at `b`.
Equal digests show equal sets only if double SHA-256 is collision resistant, as for every digest of `block.validate`.

The statement has a hypothesis, and the comparison does not discharge it:

- **The start state comes from Core.** The harness made the snapshot with Core's `ConnectBlock` on every block from the genesis block. The oracle checked those blocks only up to height 145,000 and inside the earlier ranges. An error of the Lean definitions on a block outside every range stays unseen.
- **The harness, not Core, carries the set.** The map, the commit after each block and the snapshot writer are harness code. A fault there can give both programs the same wrong start state. The replay from the genesis block compares that code with the oracle up to height 145,000. Exit condition 3 of stage 2 compares the last set of the pass with a node.
- **The arithmetic.** No sum of `ConnectBlock` left the `int64_t` range in the pass. The build of section 3.2 ends the pass on an overflow, so a finished pass gives this hypothesis, if the sanitizer finds every such overflow.
- **The context.** The digest covers coins alone. The chain view, the ancestor hash and the predecessor of the first block come from the headers that the pass kept (section 3.2). The comparator requires that the first block of a range names the block hash of the snapshot's manifest. Both programs get the same context, so a wrong context is a wrong supplied state, as a wrong snapshot is.
- **The blocks.** Section 5 states what authenticates them.

Two ranges that meet at a height chain by equal digests.
The first range ends at the digest `D(b)` and at the block hash of the manifest at `b`.
The second range starts from the snapshot with that digest, and its first block names that hash.
So the two ranges together show the statement for the range from `a + 1` to the end of the second.

The snapshot at 145,000 must have the digest `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d`, which the oracle itself reached from the empty set.
So a range that starts at 145,001 chains to the genesis block with no assumed start state.
The replay from the genesis block to height 145,000 stays the check from the empty set, and no range replaces it.

## 4. Ranges and order

Each range below holds a rule change, or tests the block forms of one period.
A range around a rule change at height `h` runs from `h - 1,000` to `h + 999`.

| Range | Heights | Blocks | Reason |
| --- | --- | ---: | --- |
| S | 100,001 to 101,000 | 1,000 | Self-test of the snapshot path on blocks that the genesis replay covers |
| A | 145,001 to 155,000 | 10,000 | Chains to the genesis replay. The first blocks with the fixed subsidy and with coinbase maturity 240 |
| B | 370,337 to 372,336 | 2,000 | The first AuxPoW block, 371,337 |
| C | 599,000 to 600,999 | 2,000 | The last subsidy change, at 600,000 |
| D | 1,033,383 to 1,035,382 | 2,000 | BIP34, BIP66 and the DERSIG flag, from 1,034,383 |
| F | 3,463,751 to 3,465,750 | 2,000 | BIP65 and the CLTV flag, from 3,464,751 |
| H | 5,049,001 to 5,050,000 | 1,000 | The period of the largest transaction rate in `chainTxData`. The range ends at Core's last checkpoint |
| G | 6,455,302 to 6,456,301 | 1,000 | The recent range of design record 0010, with the blocks of stage 0010a |
| E1, E2 | Fixed in stage 4 | 2,000 each | The CSV window: one range across the first `STARTED` boundary and one across the `FAILED` boundary |

**Cost.**
The ranges A, B, C, D, F, H and G have 20,000 blocks.
Range A has about 0.45 million inputs, from the last 5,000 blocks below it, so the oracle needs about 30 minutes.
Range G needs about 4 minutes by the same rate.

`chainTxData` gives 92,752,025 transactions to height 4,556,625, about 20 for each block, and about 270 for each block from there to 5,050,000.
So each of B, C, D and F has about 0.1 million inputs, and H has about 0.6 million.
The oracle then needs a few hours on one core for all block work.
Each range adds two reads of its snapshot (section 3.3).
These numbers are estimates, and stage 2 records the measured times.

**Order.**
The Core pass reaches the start heights in order, so the ranges become ready in the order S, A, B, C, D, F, H, G.
Range S needs no new block and comes first, with the stage that adds the snapshot path.

**Parallel runs.**
The Core pass is serial and uses one core.
Each range is one oracle process on one core, and it needs only its own snapshot.
So up to three ranges run beside the pass, at low priority, within four of the eight cores of the budget.
Each range run is a registered job with a log, as the recorded replay was.

**The CSV window.**
Between about heights 1.2 million and 1.72 million, Core counts the versions of every block of each period (design record 0010, section 4, case 3).
`block.validate` returns an adapter error for a boundary in that window today.
The harness loses its refusal for the Core pass (section 3.2).
A range in the oracle needs the same change there: a version in each entry of `chain`, and the full walk of the state.

The version-bits walk already compares the state on the real header chain through the window.
So decision 9 asks whether the two ranges are worth this change.

## 5. Blocks

**The Core pass.**
The pass needs every block once, in order.
The proposal reads them from the maintainer's node with `scripts/fetch_blocks.py`, in segments of at most 4 GB.
The pass deletes a segment when the harness accepts all of it and writes the snapshot at its end.

The script checks each block as it does today.
It checks the parse, the header hash, the Merkle root, the link to the block below, and each pinned hash.
The harness then checks each block's proof of work and its `nBits` against `GetNextWorkRequired`, in `CheckBlockHeader` and `ContextualCheckBlockHeader`.

**The ranges.**
The blocks of each range are kept as a fixture in the format `dogelib-blocks/1`.
At about 20 KB for each block, the two measured fixtures suggest about 40 MB for a range of 2,000 blocks.
Each range becomes an asset of a GitHub release, with its SHA-256 in `tests/block/mainnet-blocks/release.json`, under decision 2 of design record 0010.
The blocks of range G are already an asset.

**Authentication.**
A block hash commits to the hash of the block below it.
So a checkpoint of Core commits to every block below it on its chain, if SHA-256 is collision resistant.
The pass reads every block from the genesis block and requires each checkpoint.
So when the pass reaches a checkpoint, each range block below it has a hash on the chain of that checkpoint.

The proposal commits the list of the block hashes of each range, as `mainnet-subsidy-prev-hashes` does for the first 145,000 heights.
`scripts/fetch_blocks.py` then labels those blocks `pinned`.
A reader can check the list again with the headers from the range to the next checkpoint, from any source.

Core's last checkpoint is at height 5,050,000.
Range H ends there, so the checkpoint pins all of its blocks directly.
Range G is above it, and its blocks stay `linked`: their place in the chain rests on the node.
Decision 6 offers a committed hash for height 6,456,301.
The lane commits it only if the node and two public Electrum servers agree on it, as for the headers at height 600,000.

**Snapshots.**
A snapshot is too large for the repository, and the proposal does not publish it.
The implementation lane commits the manifest of each snapshot, with its digest and SHA-256.
A second Core pass writes the same files again, so the files themselves stay local.

**The restricted coins.**
The entries of a snapshot that a range reads are small.
For range G they are the entries of 15,999 transaction IDs.
A tool writes them as the `coins` argument of an ordinary request, and they become a release asset with a committed SHA-256.
CI can then run the range with no snapshot (section 9, stage 3).

## 6. The recent range and the transaction index

Stage 0010b is open in one part: the recent range, range G here.
Design record 0010, section 5, planned a fetch tool that takes each spent coin from its funding transaction.
Without `-txindex`, `getrawtransaction` finds a confirmed transaction only through a coin entry of its ID.
`GetTransaction` takes the height from that entry and reads the block (lines 1108 to 1125).
After the node flushes the last spend of a funding transaction, the database has no entry for it (`txdb.cpp`, lines 53 to 54).
So the node does not reliably supply every funding transaction.

A change of `-txindex` needs `-reindex-chainstate` (`init.cpp`, lines 1515 to 1517).

The options for the coins of range G follow. Decision 5 leaves the choice to the maintainer.

| Option | Work | Cost | What the coins rest on |
| --- | --- | --- | --- |
| T1: transaction index | Start the node with `-txindex` and `-reindex-chainstate`. The fetch tool of design record 0010 then reads 15,999 funding transactions and their blocks. | The node rebuilds its coin set from its block files in a background thread (`init.cpp`, line 1661). It answers requests during that time, but its chain and its index are not complete until the rebuild ends. The index has one entry for each transaction of the chain, at least 226 million. Neither the time nor the disk space is measured. | The transaction ID authenticates each funding transaction, and a Merkle branch gives its height in a header. Nothing shows that a coin was unspent at the start of the range. The request states that 26,419 transaction IDs are absent, and nothing authenticates that statement. |
| T2: snapshot | The Core pass of section 3, to height 6,455,301. | About 12 to 14 hours of one core by the estimate of section 2, and one read of the whole chain from the node. No change to the node. | Core's `ConnectBlock`, run by the harness on every block from the genesis block (section 3.4). The start state is complete: a missing entry is absent in Core's set. |
| T3: a public source | The fetch tool reads each funding transaction and its Merkle branch from public Electrum servers, with `blockchain.transaction.get` and `blockchain.transaction.get_merkle`. | About 32,000 requests to servers that DogeLib does not control. Their limits are not measured. | As T1. The source is untrusted, and the same checks apply. |
| T4: public heights, node blocks | A public source gives only the height of each funding transaction. The tool reads that block from the node and finds the transaction in it. | At most 15,999 blocks from the node. No change to the node. | As T1. A wrong height gives a block without the transaction, and the tool fails. |

For T1, T3 and T4, each funding block above height 5,050,000 has no pinned header.
So the height of its coins rests on the source of the header.
Those three options serve one range for each fetch.
T2 also gives the start states of the other ranges.

**Recommendation.**
T2, because it needs no change to the node, gives a complete start state, and serves every range.
If stage 0 shows that the Core pass does not fit the machine, T4 is the proposed replacement for range G alone.

Under T2 the fetch tool of design record 0010 is not built.
Exit condition 2 of its stage 0010b names that tool.
Decision 5 therefore also asks the maintainer to replace that exit condition with exit condition 2 of stage 1 below.

## 7. Oracle speed

**What the plan needs.**
The ranges need no faster oracle.
At 4.1 ms for each input, the block work of all ranges takes a few hours on one core (section 4).
At that average, one day on one core covers about 21 million inputs.
That is 1.4 times the inputs of the whole genesis replay.

The plan does need the two changes of section 3.
A range has no digest of the whole set inside it, and the set in memory holds only the entries of `T`.
With the existing form, each digest costs about 13 µs for each coin.
The one memory observation of section 2 gives about 1.4 KB for each coin.

**What stays slow.**

- **Signature checks and signature hashes.** They are most of the 4.1 ms. The legacy signature hash is quadratic in the inputs of one transaction, in Core too. A rough count takes 41 bytes times the square of the inputs of each transaction. It gives 9.7 GB of preimages for the blocks from height 105,000 to 110,000.
- **The sigop count** ([issue 149](https://github.com/dghelm/DogeLib/issues/149)). Its time grows with the square of the number of instructions of a script. No block above height 145,000 was read for long scripts, except the recent range.
- **The duplicate-input test** of `checkTransaction`. Its time grows with the square of the number of inputs. Pull request 173 measured under 0.4 seconds on a block with 6,259 inputs.
- **The reads of the snapshot.** Two for each range, in the size of the set.

Before the oracle starts a range, the comparator runs `block.check` on its blocks.
That check needs no coins and no snapshot, and it finds a block that the sigop count or the duplicate-input test makes slow.
A range with such a block waits for issue 149, or the lane records the time.

**A replay of every block.**
The ranges chain, so a set of ranges that covers every height from 145,001 is a replay of the whole chain on several cores.
At 4.1 ms for each input, that is the 22 to 27 days of one core from section 2.
At 0.4 ms for each input it would be about 2 to 3 days.
This record does not propose that replay or that speed.
It keeps the snapshot format and the chain of digests so that later ranges can fill the gaps.

## 8. Changes to the format

The changes are additive, within `dogelib-oracle/1` ([format stability](../oracle.md#format-stability)):

- `block.validate` takes `coins_file` in the place of `coins`, in both programs, only with `blocks_file`.
- The result gains `start_set_digest_hex` and `start_set_coins` for such a request.
- A request with `coins_file` has no `set_digest_hex` in a block record. The field of the result keeps its meaning.
- The harness alone takes `snapshot_heights` and `snapshot_dir`, and a list of heights at which it reports the digest of the whole set. The oracle returns a request error for them.
- In the harness, each entry of `chain` can hold a `version` (section 3.2).
- The comparator and `scripts/oracle_block_validate.py` learn the two forms. Where this record compares a request with `coins_file` to a request without it, the block records are compared without `set_digest_hex`.
- New errors of kind `block_validate` for a snapshot that does not open, is truncated, or has a fault of section 3.1.

The snapshot file `dogelib-coins/1` is a fixture format, so its adoption is the maintainer's (decision 1).
A request with `coins` and no file does not change.

## 9. Stages and exit conditions

### Stage 0: measurements

The stage adds no Lean code. It needs the node.

1. The size of the node's block files, and the `transactions` and `txouts` values of `gettxoutsetinfo` at a recorded height.
2. A committed script that counts the transactions and inputs of a fixture, as section 2 did.
3. A statement of whether the Core pass fits the machine. It gives the disk space for the segments and the snapshots, and the memory of the harness for the set at the tip.

The stage exits with those numbers in the pull request, and with the choice between the map and `CCoinsViewDB`.
If the pass does not fit, the lane stops and asks the maintainer.

### Stage 1: the snapshot path

The stage adds the format, the arguments of section 8 in both programs, `validateBlock_restrict` if the maintainer accepts it, and a gate for range S.
It needs no new block.

1. The harness replays heights 0 to 145,000, writes snapshots at 100,000 and 145,000, and reports the digest at 101,000. The snapshot at 145,000 has 5,094,671 coins and the digest of section 3.4.
2. A changed snapshot fails. One case changes each field: the amount, the script, the height and the coinbase byte. The other cases are a removed record, an added record, two records in the wrong order and a truncated file. Each other fault of section 3.1 has a case, and one has the amount -1. One removed record has an ID outside `T`, so only the start digest finds it.
3. Range S agrees under section 3.4. Its block records equal those of the same heights in a replay from the genesis block, without `set_digest_hex`.
4. The oracle runs range S in two forms: with `coins_file`, and with the whole set of height 100,000 in memory. Both give the same end digest, and the same block records without `set_digest_hex`.
5. CI runs a short form of conditions 2 to 4, on the released blocks of heights 0 to 10,000 with a snapshot at 9,000.

### Stage 2: the Core pass and the ranges A, B, C, D, F and H

The stage first adds the version of each `chain` entry to the harness, and removes its refusal in the CSV window (section 3.2).
A request with a dense chain through the window must agree with the version-bits walk on the state at each boundary.

1. The Core pass reaches height 5,050,000. It accepts every block, with every checkpoint. Each segment starts at the block hash of the manifest before it. The pass writes the start snapshot of each of the six ranges and reports the digest at each range end.
2. Each of the six ranges agrees under section 3.4, in a recorded run outside CI. The record names the builds, the SHA-256 of each file, the counts and the times.
3. If decision 7 is accepted: the pass continues to a height at which the node reported `gettxoutsetinfo`. The harness computes Core's `hash_serialized` for its own set (`rpc/blockchain.cpp`, lines 874 to 905). The value equals the node's value, with equal `transactions` and `txouts`. That hash covers each transaction ID, output index, amount and script. It also covers the hash of the best block, which the record of the run names. It does not cover the height or the coinbase flag.
4. COVERAGE.md, SOUNDNESS.md and `docs/oracle.md` state the hypothesis of section 3.4 for each range.

### Stage 3: the recent range

The stage follows the option of decision 5. Under T2:

1. The Core pass reaches height 6,456,301, and range G agrees under section 3.4 in a recorded run.
2. A tool writes the restricted coins of range G. The oracle's run on them gives the block records of condition 1, without `set_digest_hex`.
3. In CI, `block.validate` agrees with Core on range G with the restricted coins. The two agree on every block record, with the digest of each block's coin changes. They also agree on each digest of the restricted set, which is not a digest of the coin set of mainnet. This closes exit condition 1 of stage 0010b.

### Stage 4: the CSV window in the oracle

The stage runs only if decision 9 is accepted.
It adds a version to each entry of `chain` in the oracle, and the full walk of the version-bits state in `block.validate`.
It fixes the heights of E1 and E2 from the output of the version-bits walk.
It exits when both ranges agree under section 3.4, and Core reports `STARTED` and then `FAILED` in them.

### Gates

Each stage adds its commands to the gate table of AGENTS.md.
The gates of stage 1, condition 5, and stage 3, condition 3, run in CI.
The Core pass and the ranges of stage 2 are recorded gates outside CI, as the replay to height 145,000 is.

## 10. Excluded

- A replay of every block above height 145,000, and any work on the speed of the oracle. Issue 149 stays a separate task.
- A published snapshot, and any claim that a snapshot is the coin set of mainnet without the hypothesis of section 3.4.
- A digest that a program can update for one coin, such as MuHash. It would remove the reads of section 3.3, and it needs new cryptography in Lean and in the harness.
- Reorganization, undo data, and Core's own database format on disk.
- Script-check threads and assumed-valid blocks, as in design record 0010.
- Testnet and regtest.
- The total value of the coin set ([issue 171](https://github.com/dghelm/DogeLib/issues/171)), except the count comparison of stage 2, condition 3.

## 11. Decisions

**Date:** none. **Decision maker:** Maintainer.
Every row is a proposal.

| Number | Topic | Proposal | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | Snapshot format | `dogelib-coins/1`: the coin records of the whole set in digest order, with the existing digest and a manifest (section 3.1). | A format with an index for random reads. A digest that updates for one coin. | Proposed |
| 2 | Oracle start state | The entries of `T` in memory, with one read of the file for the start digest and one for the end digest. The theorem target `validateBlock_restrict` (section 3.3). | The whole set in memory, which fits only while the set is small. The same reads with test evidence and no theorem. | Proposed |
| 3 | Core pass | One replay by the harness from the genesis block, in segments of at most 100,000 blocks. It checks every script, it runs the version-bits walk in the CSV window, and its build stops on a signed overflow. Blocks come from the node in segments that the pass deletes (sections 3.2 and 5). | A pass without script checks, which is faster and checks less of the start states. A check of each sum in wider integers before `ConnectBlock`, in the place of the sanitizer. A pass that reads the node's block files in place. | Proposed |
| 4 | Ranges | S, A, B, C, D, F, H and G of section 4, in that order, with up to three oracle runs beside the pass. | Range G alone. More or longer ranges. | Proposed |
| 5 | Coins of the recent range | T2: the snapshot at 6,455,301. The fetch tool is not built, and exit condition 2 of stage 0010b becomes exit condition 2 of stage 1 here (section 6). | T1, T3 or T4 of section 6. | Proposed |
| 6 | Storage and pins | Range blocks and restricted coins as release assets with committed SHA-256 values. A committed list of block hashes for each range. Snapshot manifests committed, and snapshot files local. A committed hash for height 6,456,301 if three sources agree (section 5). | Range blocks local only. Range G stays `linked`. | Proposed |
| 7 | Comparison with a node | Stage 2, condition 3: `hash_serialized`, `transactions` and `txouts` of the harness's last set against `gettxoutsetinfo` of the node at one height. | No comparison. The second item of section 3.4 then rests on the replay to height 145,000 alone. | Proposed |
| 8 | CI | Stage 1, condition 5, and range G with restricted coins, in the `core` workflow. The pass and the other ranges outside CI. | All of it outside CI. | Proposed |
| 9 | CSV window | Stage 4: the ranges E1 and E2, with a version in each `chain` entry of the oracle. The harness gets that change in stage 2 in every case. | No range in the window. The version-bits walk stays the evidence there. | Proposed |

## 12. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The set at the tip does not fit the harness's memory, or the snapshots do not fit the disk. | Stage 0 measures both before any code. `CCoinsViewDB` replaces the map, and the pass keeps only the snapshots of range starts. |
| The estimates of section 2 are wrong by a large factor. | Stage 0 counts inputs on fetched blocks. The pass runs in segments, so its rate shows early. |
| A fault of the harness's set code gives a wrong snapshot that both programs accept. | The replay to height 145,000 compares that code with the oracle. Decision 7 compares the last set with a node. Section 3.4 states the hypothesis. |
| The restricted run differs from the run on the whole set. | `validateBlock_restrict`, and condition 4 of stage 1. The end digest of each range also fails if the restricted run changes an entry in another way than Core. |
| A range holds a block that the sigop count makes very slow. | The `block.check` run before each range (section 7). |
| Agreement on ranges is read as a replay of the chain. | Each record states the heights and the hypothesis of section 3.4. The ranges of section 4 without S, E1 and E2 cover 20,000 of about 6.3 million blocks above height 145,000. |
| The node changes or is not reachable in the middle of the pass. | The pass continues from its last snapshot. Each block is checked against the pins and the links, whatever the source. |

This record changes no pin and no agreed theorem statement, and it asks for no exception to the trust policy.
Decision 1 introduces a fixture format, and decision 5 replaces an exit condition of an adopted record. Both need the maintainer.
Adoption of the scope establishes no result, and it does not authorize the merge of a later implementation.
