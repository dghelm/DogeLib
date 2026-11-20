# Mainnet coin-set replay above height 145,000

**Status:** Draft, proposed on 2026-11-20.
No part of this record is adopted, and every decision of section 13 has the status `Proposed`.

**Date:** 2026-11-20
**Companions:** [Design record 0010](0010-block-validity.md), [design record 0007](0007-proposed-revisions.md), [design record 0001](0001-initial-handoff.md), [oracle contract](../oracle.md), [coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md) and the [block fixtures](../../tests/block/mainnet-blocks/README.md).

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

Design record 0001, section 1, gives DogeLib three purposes.
The record has a deliverable for each one:

| Purpose | Deliverable | Sections |
| --- | --- | --- |
| Make existing consensus behaviour precise | Each range compares named Lean definitions with Core on the blocks of one rule change. The record flags each rule that `block.validate` does not model | 3, 4 and 4.1 |
| Support versioned protocol proposals | A run of a proposed revision of design record 0007 over every range, which reports each historical block whose verdict changes | 10 |
| Give contracts to other implementations | A public corpus that a program other than the oracle can run: the range fixtures, the request of each range, the expected results and the snapshot format | 9 |

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

### 4.1 Rules and definitions

The table names the rule of each range, and the Lean definitions that the range compares with Core.
Every range also compares the whole of `validateBlock`: the five checks of section 5 of design record 0010, and the coin set.

| Range | Rule that the range exercises | Lean definitions | In `block.validate` |
| --- | --- | --- | --- |
| S | The random subsidy and coinbase maturity 30 | `getDogecoinBlockSubsidy` with `generateMTRandom`, `coinbaseMaturity` | Yes |
| A | The fixed subsidy from 145,000. Maturity 240 for a coinbase from that height, first spent from 145,240. The DigiShield retarget at each block | `getDogecoinBlockSubsidy` with `mainnetSimplifiedRewards`, `coinbaseMaturity`, and the `nBits` check of `contextualCheckBlockHeader` | Yes |
| B | AuxPoW from 371,337: the payload check, the chain ID, and the end of legacy blocks | `checkBlockHeader` with `AuxPow.check`, and `getContextualParams` with `mainnetAuxpowContextualParams` | Yes |
| C | The subsidy of 10,000 coins from 600,000 | `getDogecoinBlockSubsidy` | Yes |
| D | From 1,034,383: the height in the coinbase script, block versions below 3 rejected, and the DERSIG flag | `coinbaseHeightPrefix` in `contextualCheckBlockBody`, `contextualCheckBlockHeader`, and `connectScriptFlags` | Yes |
| F | From 3,464,751: block versions below 4 rejected, and the CLTV flag | `contextualCheckBlockHeader` and `connectScriptFlags` | Yes |
| H, G | No rule change. P2SH spends, the sigop limit with P2SH, and the blocks of two recent periods | `verifyLegacySpend` through `checkInputScripts`, and `getTransactionSigOpCost` | Yes |
| E1, E2 | The version-bits state of CSV inside its window | The full walk of `Block.VersionBits` | No. `block.validate` returns an adapter error there, and stage 4 adds the walk |

Three limits apply to every row:

- A block of mainnet shows only the accepting side of a rule. The rejecting side has its evidence in the changed blocks of the full comparison ([evidence](../oracle.md#block-validation-comparison-evidence)).
- `block.validate` runs `contextualCheckBlockHeader` with checkpoints disabled. So no range exercises the checkpoint rule, in either program.
- CSV and SegWit semantics stay outside the Lean definitions, which prove them inactive on mainnet (design record 0010, section 7). A range in the oracle fails with `outside_model` if a block needs them.

Apart from E1 and E2, the record found no rule change of a range that `block.validate` does not model.

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
A tool writes them as the `coins` argument of an ordinary request.

The *range request* is that request without its blocks: the restricted coins, `chain`, `bip34_ancestor_hex`, the adjusted time and the flags.
It becomes a release asset with a committed SHA-256, for every range.
CI can then run the range with no snapshot (section 11, stage 3).

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
So is the results file `dogelib-range-results/1` of section 9 (decision 13).
The `revision` argument of section 10.2 belongs to a separate executable, and `dogelib-oracle` does not take it.
A request with `coins` and no file does not change.

## 9. The ranges as a conformance corpus

The third purpose of DogeLib is a contract against which another implementation can be checked.
A program that validates Dogecoin blocks can run the ranges with no oracle, no Core harness and no node.
The proposal publishes what such a run needs:

| Part | Format | Where | What fixes it |
| --- | --- | --- | --- |
| The blocks of each range | `dogelib-blocks/1` | Release asset | SHA-256 in `release.json`, and the committed list of block hashes |
| The range request of each range | The arguments of `block.validate` in `dogelib-oracle/1` | Release asset | SHA-256 in `release.json` |
| The expected results of each range | A proposed format `dogelib-range-results/1` | Committed | The repository |
| The snapshot at each range start | `dogelib-coins/1` | Local. The manifest is committed | The digest, the number of coins and the SHA-256 of the manifest |

**Expected results.**
The file of a range holds one line for each block.
The line gives the height, the hash, the verdict, the digest of the coin changes, and the numbers of spent and created coins.
It also holds the digests of the restricted set at the start and at the end.
The values are the response of the Core harness to the range request, with its restricted coins, in a run in which the oracle agreed.
Stage 5 runs that request for every published range, because stage 2 compares whole snapshots.

So the expectation of a third program comes from Core's code and not from that program.

**What a third party runs.**
The party downloads the blocks and the range request, and checks both against the committed SHA-256 values.
Its program reads the two files and writes a results file.
A committed checker compares that file with the expected results, and needs no other program.
The document of the formats defines the modes, the flags, the chain context and the digests that the program needs.

`scripts/compare_core.py` is not that checker.
It requires the version names of the oracle and of the harness, and request sets beyond `block.validate`.
So a third program cannot stand in either place there, and this record proposes no change to it.

A result on the restricted coins shows agreement on verdicts and coin changes.
It does not show the digest of the whole coin set, which needs the snapshot.

**A snapshot stays local.**
A third party makes the file again in two steps.
It builds the Core harness at the pin with `scripts/build_core_harness.sh`, and it runs the Core pass on blocks from its own node.

A snapshot has one byte sequence for one coin set (section 3.1).
So the new file must have the SHA-256, the digest and the number of coins of the committed manifest.
Its block must have the block hash of the manifest.
A file that fails any of the four is not the snapshot of the record.
Stage 1 makes the snapshot at height 9,000 in CI from released blocks alone, so that case needs no node.

**Versions.**
Each format has a name with a version, and a document that defines it without reference to the Lean code.
The assets belong to a release with a dated tag, as the block fixtures of design record 0010 do.
A change of a published file is a new release, and the old tag stays.

**The Rust path.**
The corpus is also the conformance test of a later Rust implementation.
For example, a Rust reader of `dogelib-coins/1` with a refinement theorem, as the CompactSize reader has, would run the same snapshots.
This record proposes no Rust work.

## 10. Historical impact of a proposed revision

The second purpose of DogeLib is support for versioned protocol proposals.
Design record 0007 states a proposed revision and proves its compatibility at the level of one Script spend.
Its section 8.3 names what the block level needs, and that record had no block validity to build on.
With the snapshots and the ranges, a run can answer a first question at the block level:
which historical blocks get another verdict under a revision?

### 10.1 Definitions

A proposed revision of the Script rules gives a revised spend check, with an `active` argument (design record 0007, sections 6 and 7).
`connectBlock` takes Core's signature verifier, not a spend check.
So the proposal adds `connectBlockWith` and `validateBlockWith` to the `Proposals` library, with the spend check as a parameter.
The addition follows option M2 of design record 0007: no baseline file changes, and an agreement theorem pins the copy to the baseline.
The block height and an `Activation` value give `active` (design record 0007, section 7.2).

The theorem targets follow. The names are proposals:

| Target | Statement |
| --- | --- |
| `connectBlockWith_baseline` | With the baseline spend check and the baseline error type, `connectBlockWith` equals `connectBlock`. |
| `validateBlockWith_inactive` | Take a revision with the inactive equality. Below the activation height, or with no activation height, `validateBlockWith` equals the embedded result of `validateBlock`. |
| `validateBlockWith_congr` | Take a block in which no `scriptSig`, no spent `scriptPubKey` and no P2SH redeem script holds an instruction that the revision redefines. Then `validateBlockWith` of the active revision equals the embedded result of `validateBlock`. It lifts `verifyScriptWith_congr`, for both calls of the script check. |
| `connectBlockWith_restricts` | Take a revision whose spend check restricts acceptance. If `connectBlockWith` accepts a block on a coin set, `connectBlock` accepts it on that set with the same coin set and the same changes. |

**Errors.**
A proposal can have its own error type, as `ExampleVersionVerify` has `ScriptError ⊕ ExampleError`, and `ConnectBlockError.script` holds a `ScriptError` alone.
So the two definitions are generic in the script error, with an embedding of the baseline errors, as the Script framework is (design record 0007, section 6.2).
*The embedded result* above is the baseline result with its errors mapped through that embedding.

**The second script check.**
`checkInputScript` runs a failed script again without the flags that are not mandatory, and takes the reject reason from that second run (`DogeLib/Block/Connect.lean`, line 253).
`connectBlockWith` keeps that contract.
It runs the revised check again with the reduced flags and the same `active`, classifies by the second run, and keeps the first error.
Acceptance depends on the first run alone, so `connectBlockWith_restricts` needs no statement about the second.

**Signature operations.**
The definitions change the spend check and nothing else.
`getTransactionSigOpCost` counts as in the baseline, so a revision that would count operations in another way is outside this section.

The last target is the block obligation of design record 0007, section 8.3, for a Script revision with the identity projection.
The statement for chains needs an induction over it, and this record does not require that step.

### 10.2 The request

Design record 0007, decision 8, keeps the `Exports` library and `dogelib-oracle` free of proposals during 0.x.
It allows a later decision to add a `ProposalExports` library.
Decision 10 below is that later decision, as a proposal.

A separate executable, built from `ProposalExports`, answers `block.validate` with one more argument:

```text
"revision": {"name": "ExampleVersionVerify", "variant": null, "activation_height": 0}
```

`activation_height` is a height or null for no activation.
`dogelib-oracle` returns a request error for the argument, and the import check keeps every baseline library free of `DogeLib.Proposals`.

The executable carries the baseline state through the range, as `block.validate` does.
For each block it runs the baseline and the revision on the same state before the block.
Each block record gains a `revised` object with the verdict of the revision and, for a rejection, the transaction, the input and the error.
A *changed block* is a block whose two verdicts differ.
So the run answers one question for each block: what does the revision say about this block on the historical chain below it?
It does not build the chain that revised nodes would have built after the first changed block.

The report of a run lists the changed blocks of each range, each with its height, its hash, both verdicts and the reason.
The run costs about twice the block work of section 4, because each input runs two script checks.

### 10.3 The self-test

The two examples of the `Proposals` library test the run: `ExampleVersionVerify`, and the corrected variant of `ExampleFaultyLocktime`.
The expected number of changed blocks is fixed before each run, from a source other than the run:

1. **No activation height.** No block of any range changes, by the inactive equality of each example.
2. **Active from height 0.** A separate script reads the blocks and the range requests, and lists the *candidate blocks*. A candidate has a spend that holds the redefined opcode as an instruction, `0xb9` or `0xb3`. The lane commits that list before the run. This case is a property test, not a known answer. Every changed block must be a candidate, by the congruence theorem. Each change must go from accepted to rejected, because both examples are soft forks. If the list is empty, the expected number of changed blocks is 0. For each candidate of a list that is not empty, the lane derives the expected verdict by hand from the text of the rule before the run.
3. **Made blocks.** The test builds blocks as `scripts/oracle_block_validate.py` builds the changed blocks of the full comparison. Each block stands on a committed rule-change block, with a valid coinbase, a synthetic coin whose script holds the rule, a transaction with one output that spends it, and no proof of work. The scripts follow the witnesses of each example. The expected verdict of each block comes from the text of the rule under the flags of its height, derived by hand. The witness theorems do not give it: they use flags 0 and a transaction that no block can hold. The cases are: a spend that the baseline accepts and the revision rejects, which must be the one changed block of its request, with the error of the rule. A spend that runs the rule and passes, which must not change. The counterexample of the faulty variant, which must change in the other direction. And one rejection by the active revision above height 1,034,383, where the second script check runs with other flags.

The record does not predict the number of candidates.
Cases 1 and 3 have expected numbers that are fixed in advance. Case 2 has one only for an empty list, or after the derivation by hand.

### 10.4 What a result shows

A result is a statement about the blocks of the ranges, on the hypothesis of section 3.4:

- The ranges are a sample: about 20,000 of the blocks above height 145,000. A revision that changes only blocks outside the ranges gives an empty report.
- The replay from the genesis block to height 145,000 is the only range that starts from the empty set. A run of a revision over it costs about as much as two replays of section 2.
- The run shows what the Lean definition of the revision does. No Core behaviour exists for a revision, so no comparison supports the `revised` verdicts (design record 0007, section 9).
- An empty report is not a compatibility proof. The theorem targets of section 10.1 are the proofs, and they hold for every block.
- The report says nothing about transactions that no block of the ranges holds, such as unconfirmed spends of existing coins.
- The run revises the spend check alone. It does not show the effect of a revision on the sigop count, or on any rule outside Script.

### 10.5 The whole chain

Three ways give the impact of a revision on every block. Decision 12 leaves the choice to the maintainer.

| Option | Work | Cost | What the result rests on |
| --- | --- | --- | --- |
| W1: the ranges alone | Section 10.2. | About twice the block work of the ranges. | The Lean definition of the revision, on a sample. |
| W2: candidate blocks from the Core pass | The Core pass takes a list of opcodes. It lists each candidate block of the chain, and writes the block with its range request. The proposal executable then runs those blocks alone. | One more Core pass, about 12 to 14 hours by the estimate of section 2. No added pass if the opcodes are known before the first one. Then the run of the candidates in the proposal executable and the storage of their requests. The number of candidates is not known. If most blocks are candidates, the run costs about as much as the replay of the chain in section 2. | The Lean definition, on every candidate block. `validateBlockWith_congr` shows that a block changes only if it is a candidate. The scan of the harness is a trusted premise. The theorem says nothing about a candidate that the scan misses in a spent script or a redeem script. |
| W3: a patched harness | A patch of Core's interpreter states the revision in C++. A replay with the patch alone stops at the first block that it rejects. So the harness runs Core's unchanged check to carry the state, and the patched check on the same state before each block. | One Core pass for each revision and each activation height, with two script checks for each input, about twice the cost of the pass. Also the patch, and the harness code that runs both. | A second implementation of the revision, with no theorem that relates it to the Lean definition. Design record 0007 calls that a comparison with another implementation, never a Core comparison. |

**Recommendation.**
W1 in this record, and W2 as a later stage when a revision with a congruence theorem needs the whole chain.
The record does not recommend W3 as a way to measure impact.
A patch is useful as an independent implementation to compare with, which is a separate kind of evidence.
The record commits to none of W2 and W3.

## 11. Stages and exit conditions

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

### Stage 5: the conformance corpus

The stage follows stages 2 and 3, and runs only if decision 13 is accepted.

1. A document defines `dogelib-blocks/1`, `dogelib-coins/1`, the range request and `dogelib-range-results/1`, with the digests, and without reference to the Lean code.
2. Each range has its blocks and its range request as release assets, and its expected results in the repository. For each range, the oracle and the Core harness run the range request, and agree on every block record and on both digests of the restricted set. The expected results are the response of the harness in that run.
3. A committed checker compares a results file with the expected results. It passes on a file from the oracle and on a file from the harness. It fails on a planted wrong verdict, a wrong digest, a missing block and an added block.
4. A person who did not write the tools runs one range from the document alone. They use the assets, the checker, and a program of their own or a wrapper of the harness that writes a results file. The pull request records the steps that the document lacked.
5. In CI, the checker runs range G and the short range of stage 1 from the released assets.

### Stage 6: the historical impact of a proposed revision

The stage follows stage 2, and runs only if decisions 10 and 11 are accepted.
It adds `connectBlockWith` and `validateBlockWith`, the `ProposalExports` library with its executable, and the report.

1. `connectBlockWith_baseline` and `validateBlockWith_inactive` are proved. The other two targets of section 10.1 are proved, or the pull request states why one is not. In that case it labels the evidence of case 2 as a test alone.
2. With no `revision` argument, the proposal executable gives the response of `dogelib-oracle` byte for byte on every request of the full comparison of `block.validate`.
3. The import check passes, and its self-test still fails on a baseline module that imports `DogeLib.Proposals`.
4. Cases 1 and 3 of section 10.3 give their expected numbers for both examples. Case 2 holds its two properties on every range of stages 1 to 3, with the candidate list committed before the run.
5. COVERAGE.md records each report in the section for proposals, with the label of section 10.4. The label says: a sample of ranges, with no Core comparison of the `revised` verdicts.

### Gates

Each stage adds its commands to the gate table of AGENTS.md.
The gates of stage 1, condition 5, and stage 3, condition 3, run in CI.
So do condition 5 of stage 5, and case 3 of section 10.3. Case 1 runs in CI on the short range of stage 1 and on range G.
The Core pass and the ranges of stage 2 are recorded gates outside CI, as the replay to height 145,000 is.

## 12. Excluded

- A replay of every block above height 145,000, and any work on the speed of the oracle. Issue 149 stays a separate task.
- A published snapshot, and any claim that a snapshot is the coin set of mainnet without the hypothesis of section 3.4.
- A digest that a program can update for one coin, such as MuHash. It would remove the reads of section 3.3, and it needs new cryptography in Lean and in the harness.
- Reorganization, undo data, and Core's own database format on disk.
- Script-check threads and assumed-valid blocks, as in design record 0010.
- Testnet and regtest.
- A revision of a rule outside Script, such as a header or subsidy rule. Section 10 covers revisions that the Script framework of design record 0007 states.
- The chain that revised nodes would build after a changed block, activation by signalling, and the merits of any proposal.
- A patched Core build, except as option W3 of decision 12.
- The total value of the coin set ([issue 171](https://github.com/dghelm/DogeLib/issues/171)), except the count comparison of stage 2, condition 3.

## 13. Decisions

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
| 10 | Proposal request | A `ProposalExports` library and a separate executable that answers `block.validate` with a `revision` argument. `dogelib-oracle` and `Exports` stay baseline-only (section 10.2). Decision 8 of design record 0007 allows this later decision. | The test executable `proposal-replay` alone, as in design record 0009, decision 11, with no exported library. | Proposed |
| 11 | Block level of a revision | `connectBlockWith` and `validateBlockWith` in the `Proposals` library, with the four theorem targets of section 10.1. | A copy of `connectBlock` for each proposal. | Proposed |
| 12 | Scope of an impact run | W1: the ranges, in stage 6. W2 is a later stage, decided when a revision needs it. W3 is not used to measure impact (section 10.5). | W2 in this record, with the opcodes of the examples in the first Core pass. W3. | Proposed |
| 13 | Conformance corpus | Publish the blocks, the range request and the expected results of each range, with a document of the formats, `dogelib-range-results/1` and a checker (section 9, stage 5). | The fixtures stay tools of the DogeLib comparison, with no expected results and no promise to other programs. | Proposed |
| 14 | Self-test of the impact run | The three cases of section 10.3 with `ExampleVersionVerify` and the corrected `ExampleFaultyLocktime`, and the faulty variant in case 3. | Case 1 alone. | Proposed |

## 14. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The set at the tip does not fit the harness's memory, or the snapshots do not fit the disk. | Stage 0 measures both before any code. `CCoinsViewDB` replaces the map, and the pass keeps only the snapshots of range starts. |
| The estimates of section 2 are wrong by a large factor. | Stage 0 counts inputs on fetched blocks. The pass runs in segments, so its rate shows early. |
| A fault of the harness's set code gives a wrong snapshot that both programs accept. | The replay to height 145,000 compares that code with the oracle. Decision 7 compares the last set with a node. Section 3.4 states the hypothesis. |
| The restricted run differs from the run on the whole set. | `validateBlock_restrict`, and condition 4 of stage 1. The end digest of each range also fails if the restricted run changes an entry in another way than Core. |
| A range holds a block that the sigop count makes very slow. | The `block.check` run before each range (section 7). |
| Agreement on ranges is read as a replay of the chain. | Each record states the heights and the hypothesis of section 3.4. The ranges of section 4 without S, E1 and E2 cover 20,000 of about 6.3 million blocks above height 145,000. |
| An impact report is read as the effect of a revision on the whole chain, or as a proof that it is a soft fork. | Section 10.4, and the label of stage 6, condition 5. The proofs are the targets of section 10.1. |
| The proposal executable differs from the oracle on the baseline. | `connectBlockWith_baseline`, and condition 2 of stage 6. |
| A proposal reaches a baseline library through the new executable. | The import check and its self-test, condition 3 of stage 6. |
| The expected results hold a mistake that the oracle and Core share. | The file states its source. A third program that disagrees is a finding to examine, not a failure of that program by itself. |
| A published file changes after another project pins it. | Dated release tags and committed SHA-256 values (section 9). |
| The node changes or is not reachable in the middle of the pass. | The pass continues from its last snapshot. Each block is checked against the pins and the links, whatever the source. |

This record changes no pin and no agreed theorem statement, and it asks for no exception to the trust policy.
Decisions 1 and 13 introduce fixture formats, and decision 5 replaces an exit condition of an adopted record.
Decision 10 uses the later decision that decision 8 of design record 0007 allows. All four need the maintainer.
Adoption of the scope establishes no result, and it does not authorize the merge of a later implementation.
