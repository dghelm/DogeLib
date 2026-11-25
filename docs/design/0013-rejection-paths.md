# Rejection paths and negative conformance vectors

**Status:** Proposed on 2026-11-25. The maintainer has not adopted this record.
Section 13 lists the decisions that adoption needs.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-25
**Companions:** [Design record 0009](0009-bug-finding-campaign.md), [design record 0010](0010-block-validity.md), [design record 0011](0011-mainnet-ranges.md), [design record 0008](0008-header-sequence-validation.md), [the conformance corpus](../conformance.md), [the campaign](../campaign.md), [oracle contract](../oracle.md), [the Core harness](../core-harness.md), [comparison evidence](../comparison-evidence.md), [coverage](../../COVERAGE.md) and [soundness](../../SOUNDNESS.md).

## 1. Purpose and boundary

The conformance corpus holds nine mainnet ranges, and Core accepts every block of every range.
So a pass of the conformance corpus shows no agreement on a rejected block ([what a run shows](../conformance.md#what-a-run-shows)).
The rejecting side of each rule has other evidence: changed blocks that a person built for each reachable reject reason ([evidence](../comparison-evidence.md#block-validation-comparison-evidence)).
That evidence has two limits:

- A person chose each changed block. No generated search looks for a rejected block on which the two programs disagree.
- The changed blocks are requests of the DogeLib comparison. A program other than the oracle and the Core harness cannot run them from published files.

This record proposes two deliverables for those limits.
The first is a *rejection search*.
It has a generator of blocks that Core rejects, and a comparison of both programs on each block.
It also has the tools that make a disagreement useful.
The second is a *negative corpus*: published cases with Core's verdict and reject reason, which a third program can run and check.

A project review of 2026-11-23 recommended both.
It asked for a differential search of `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock` and `AcceptBlockHeader`, and for negative vectors in the conformance corpus.
The repository does not hold the text of that review, so this record states each reason itself.

The record reuses the campaign of design record 0009 where it fits, and section 7 says what changes.
The record adds no Lean definition and no theorem target.
A result of the search is finite comparison evidence, and it is not a proof of agreement on every rejected block.

## 2. Reference software revision

Core is Dogecoin Core at the pin `e0a1c157791544e818c901bd9341896965afbf9d` of [SOURCES.md](../../SOURCES.md).
Line numbers refer to `src/validation.cpp` at that commit unless a file is named.
The findings below come from source inspection and from the committed records.
No search of this record has run.

The harness calls Core's own functions for every operation of this record ([what the harness runs](../core-harness.md#what-the-harness-runs)).
It compiles `src/validation.cpp` unchanged, so it can call the static `AcceptBlockHeader` (line 3205).
The harness builds the inputs of those functions: the block index, the coin view and the version-bits cache ([block validation in the harness](../core-harness.md#block-validation-in-the-harness)).
So a fault of that code can change a verdict, and section 6.5 gives its checks.

## 3. Scope

### 3.1 Operations

The search sends requests of six operations of [`dogelib-oracle/1`](../oracle.md#operations).
The record changes none of them:

| Operation | Core's function | Lean definition | Compared fields of a rejection |
| --- | --- | --- | --- |
| `tx.check` | `CheckTransaction` (lines 527 to 574) | `Transaction.checkTransaction` | `valid`, `reject_reason`, `dos`, `reject_code` |
| `block.check` | `CheckBlock` (lines 2939 to 2998) | `Block.checkBlock` | The same, and `corruption_possible` |
| `block.contextual_check` | `ContextualCheckBlockHeader` (lines 3066 to 3119) | `Block.contextualCheckBlockHeader` | `valid`, `reject_reason` |
| `block.contextual_check_body` | `ContextualCheckBlock` (lines 3121 to 3203) | `Block.contextualCheckBlockBody` | `valid`, `reject_reason`, `dos`, `reject_code` |
| `block.validate` | The five checks of a new block, with `ConnectBlock` (lines 1783 to 2009) | `Block.validateBlock` | The same four fields in each block record, and the digests of the coins |
| `block.header_sequence` | `AcceptBlockHeader` (lines 3205 to 3267) | `Block.processNewBlockHeaders` | `valid`, `failed_at`, `reject_reason`, `dos`, `reject_code`, `added`, `marked_failed_child` |

The oracle reports no score and no code for `block.contextual_check` ([contextual header validation](../oracle.md#contextual-header-validation)).
The search compares both for the same seven reasons through `block.validate` and `block.header_sequence`.

`block.validate` is the main target.
It runs the five checks in Core's order and stops at the first failure ([block validation](../oracle.md#block-validation)).
The four other block operations reach a check alone, with arguments that `block.validate` fixes.
For example, `block.check` takes all four combinations of its two flags, and `block.contextual_check` takes `checkpoints_enabled`.
`block.validate`, `block.check` and `block.contextual_check_body` are mainnet only, and the search adds no network to them.

### 3.2 Reject sites

A *reject site* is one statement of Core that sets a reject reason.
The table below names nine functions of Core: those of section 3.1, `CheckBlockHeader`, `Consensus::CheckTxInputs` (lines 1415 to 1459) and `CheckInputs` (lines 1462 to 1512).
Together they have 47 reject sites.
The search targets 40 of them, which the table lists.
The score is the first argument of `state.DoS`, and a site that calls `state.Invalid` has the score 0 (`src/consensus/validation.h`, lines 36 to 54).
The codes are `REJECT_INVALID` 16, `REJECT_OBSOLETE` 17, `REJECT_NONSTANDARD` 64 and `REJECT_CHECKPOINT` 67 (`src/consensus/validation.h`, lines 13 to 19).

| Function | Reject reason | Line | Score | Code |
| --- | --- | ---: | ---: | ---: |
| `CheckTransaction` | `bad-txns-vin-empty` | 531 | 10 | 16 |
| | `bad-txns-vout-empty` | 533 | 10 | 16 |
| | `bad-txns-oversize` | 536 | 100 | 16 |
| | `bad-txns-vout-negative` | 543 | 100 | 16 |
| | `bad-txns-vout-toolarge` | 545 | 100 | 16 |
| | `bad-txns-txouttotal-toolarge` | 548 | 100 | 16 |
| | `bad-txns-inputs-duplicate` | 557 | 100 | 16 |
| | `bad-cb-length` | 564 | 100 | 16 |
| | `bad-txns-prevout-null` | 570 | 10 | 16 |
| `CheckBlockHeader` | `high-hash` | 2934 | 50 | 16 |
| `CheckBlock` | `bad-txnmrklroot` | 2956 | 100 | 16 |
| | `bad-txns-duplicate` | 2962 | 100 | 16 |
| | `bad-blk-length` | 2973 | 100 | 16 |
| | `bad-cb-missing` | 2977 | 100 | 16 |
| | `bad-cb-multiple` | 2980 | 100 | 16 |
| | `bad-blk-sigops` | 2994 | 100 | 16 |
| `ContextualCheckBlockHeader` | `late-legacy-block` | 3077 | 100 | 16 |
| | `early-auxpow-block` | 3086 | 100 | 16 |
| | `bad-diffbits` | 3090 | 100 | 16 |
| | `bad-fork-prior-to-checkpoint` | 3099 | 100 | 67 |
| | `time-too-old` | 3104 | 0 | 16 |
| | `time-too-new` | 3108 | 0 | 16 |
| | `bad-version(0x…)` | 3115 | 0 | 17 |
| `ContextualCheckBlock` | `bad-txns-nonfinal` | 3141 | 10 | 16 |
| | `bad-cb-height` | 3151 | 100 | 16 |
| | `unexpected-witness` | 3187 | 100 | 16 |
| | `bad-blk-weight` | 3199 | 100 | 16 |
| `ConnectBlock` | `bad-txns-BIP30` | 1886 | 100 | 16 |
| | `bad-txns-inputs-missingorspent` | 1946 | 100 | 16 |
| | `bad-blk-sigops` | 1969 | 100 | 16 |
| | `bad-cb-amount` | 2001 | 100 | 16 |
| `CheckTxInputs` | `bad-txns-premature-spend-of-coinbase` | 1436 | 0 | 16 |
| | `bad-txns-inputvalues-outofrange` | 1443 | 100 | 16 |
| | `bad-txns-in-belowout` | 1448 | 100 | 16 |
| `CheckInputs` | `non-mandatory-script-verify-flag (…)` | 1503 | 0 | 64 |
| | `mandatory-script-verify-flag-failed (…)` | 1512 | 100 | 16 |
| `AcceptBlockHeader` | `duplicate` | 3220 | 0 | 0 |
| | `bad-prevblk`, for an unknown predecessor | 3231 | 10 | 0 |
| | `bad-prevblk`, for a predecessor with a failure flag | 3234 | 100 | 16 |
| | `bad-prevblk`, for a failed ancestor | 3253 | 100 | 16 |

Three notes apply to the table:

- `CheckBlock` passes a reason of `CheckTransaction` on with its score and its code (lines 2984 to 2986). `bad-txns-oversize` is not reachable there, because the size test of line 2972 comes first ([evidence](../comparison-evidence.md#transaction-and-block-check-comparison-evidence)).
- `bad-fork-prior-to-checkpoint` is reachable through `block.contextual_check` and `block.header_sequence`. `block.validate` runs with checkpoints disabled.
- `bad-blk-weight` is a target of `block.contextual_check_body` alone. In `block.validate` the search does not target it (design record 0010, section 4).

Six sites test more than one condition: lines 563, 1442, 2972, 2976, 3113 to 3114 and 3149 to 3150.
The search has one directed class for each condition that a request can reach alone (section 5.3).
Two conditions have no request of their own.
A block with more than 1,000,000 transactions also fails the size condition of the same line 2972 ([evidence](../comparison-evidence.md#real-mainnet-blocks)).
A block with no transaction fails line 2972 before the same condition of line 2976.

### 3.3 Sites out of scope

The search does not target seven sites, because no request of the baseline reaches them:

| Site | Line | Reason that it is not reachable |
| --- | ---: | --- |
| `bad-witness-nonce-size`, `bad-witness-merkle-match` | 3173, 3177 | The SegWit state is never active on a mainnet header chain whose headers pass `checkBlockHeader`: `segwit_never_active` ([coverage](../coverage/blocks.md#contextual-block-body-contextualcheckblock)) |
| `bad-txns-nonfinal` of `ConnectBlock` | 1958 | Without the flag `LOCKTIME_VERIFY_SEQUENCE`, the sequence locks constrain nothing (lines 324 to 331). `ConnectBlock` sets the flag only for an active CSV state (lines 1907 to 1911), and `csv_never_lockedIn` excludes that state on such a chain. Design record 0012 compares this site with the CSV state forced ([evidence](../comparison-evidence.md#core-with-the-csv-state-forced-to-active-results)) |
| The empty reason of `CheckTxInputs` | 1420 | `ConnectBlock` makes the same test first (line 1944) |
| `bad-txns-fee-negative`, `bad-txns-fee-outofrange` | 1454, 1457 | The two tests of the input values come first (design record 0010, section 5). `checkTxInputs_ne_feeNegative` and `checkTxInputs_ne_feeOutOfRange` state it for the Lean definition |
| The rejection without a reason | 2004 | It follows a queued script check. The harness has no check thread (`nScriptCheckThreads` is 0, line 69), so `CheckInputs` runs each check itself (line 1492) |

A run of the search still fails if Core returns one of these reasons.
Such a result contradicts a row of the table, so it is a finding.

These subjects are also out of scope:

- **The causes of `high-hash`.** `CheckBlockHeader` has one reject reason for every failure of `CheckAuxPowProofOfWork` (lines 2933 to 2934). `block.check_pow` and `auxpow.check` compare those failures (design record 0004, and [evidence](../comparison-evidence.md#header-proof-of-work-evidence)). The search reaches the site with a changed header of a real block, and adds no class for the parts of a payload.
- **Reader errors.** A block that does not read gives an `error`, not a verdict ([errors](../oracle.md#errors)). The 976 reader requests of the full comparison stay the evidence there.
- **Testnet and regtest block rules,** which the Lean definitions do not have ([coverage](../coverage/blocks.md#block-check-checkblock)). `block.header_sequence` and `block.contextual_check` keep their three networks.
- **`AcceptBlock`, `ProcessNewBlock` and `ActivateBestChain`,** the choice of a chain, and every write to disk (design record 0010, section 7).
- **An active CSV or SegWit state,** which design record 0012 compares for `RelativeLockTime`.
- **The mempool and its policy.**
- **Memory errors of Core.** A verdict comparison cannot see them. Section 12 keeps native fuzzing as a later option, as design record 0009 does.

## 4. Seeds

A *seed* is a block or a header sequence that the generator changes.
The generator uses only committed files and released assets of the repository:

| Seed | Source | Use |
| --- | --- | --- |
| The 24,000 blocks of the nine ranges of the conformance corpus | The assets of [`tests/conformance/release.json`](../../tests/conformance/release.json), with the range request of each range | Real blocks with their real proof of work, on the coins of Core's own replay |
| The blocks of heights 0 to 10,000 | The asset of that range in [`tests/block/mainnet-blocks/release.json`](../../tests/block/mainnet-blocks/release.json) | Real blocks from the empty coin set, with no supplied state |
| The 17 blocks at and next to the rule changes | [`tests/block/mainnet-blocks/rule-changes`](../../tests/block/mainnet-blocks/README.md) | The context of a made block: a real header, its chain and its height |
| The made chain on the genesis block | `genesis_chain_cases` of `scripts/oracle_block_validate.py` | A chain whose every coin the generator can spend |
| The full mainnet headers and the regtest header sequences | `tests/block/mainnet-*-full-headers` and [`tests/block/regtest-header-sequences`](../../tests/block/regtest-header-sequences/README.md) | Seeds of `block.header_sequence` |

No other block is a seed.
A *made block* keeps the header and the chain of a real block, replaces the transactions and the Merkle root, and runs with `check_pow` false.
The class `Base` of `scripts/oracle_block_validate.py` builds the made blocks of the full comparison in this way, on synthetic coins.

Every block that the generator emits satisfies the hypothesis `Block.payloadNoWitness` (`DogeLib/Block/Proofs/ContextualBody.lean`, line 28).
The generator tests each emitted block against it, and drops a block that fails.

## 5. The generator

### 5.1 Cases

A *case* is a construction plan, not a byte string, as in design record 0009, section 6.1.
The driver builds the request of a case from its plan, so the reducer can change the plan and build the request again.
A block plan has these parts:

- The seed: a range and a height, or a made context and its transactions.
- The *state*: the chain, the coins, the adjusted time, the BIP34 ancestor hash and the two flags of the request.
- A list of mutations. Each one names its class, its target and its value.
- The fix-ups that the plan applies after its mutations (section 5.4).
- The mode of section 5.2 and, in the directed mode, the expected reject site.

A header plan has the index entries, the failed list, the adjusted time, the checkpoint option and the headers of a `block.header_sequence` request.

A plan has one of two kinds of mutation.
A *block mutation* changes the bytes of a candidate block and leaves the state as the seed has it.
A *state mutation* leaves the block as it is and changes the state that the request supplies.
A real block under a state mutation keeps its real proof of work and its real Merkle root, so its request keeps both flags true.

### 5.2 Two modes

- **Directed.** The plan aims at one reject site, and it names that site before any program runs. A person derives the rule of each directed class from Core's text, and the class records the cited lines. The expected verdict and reason of the case come from that rule and the plan.
- **Free.** The driver draws a list of one to four mutations with `random.Random(seed)`. A free case has no expected reason. Its property is agreement alone.

The directed mode gives each reject site a case with an expectation that neither program made.
The free mode reaches combinations that no person listed, such as two faults whose order of detection matters.

### 5.3 Mutation classes

Each class names the reject sites that it aims at.
The stage that adds a class settles its operators and its boundary values:

| Class | Mutations | Sites |
| --- | --- | --- |
| Header fields | The base version, the legacy and AuxPoW bits of the version, `nTime`, `nBits`, the Merkle root and the nonce of the 80-byte header | `late-legacy-block`, `early-auxpow-block`, `bad-diffbits`, `time-too-old`, `time-too-new`, `bad-version`, `bad-txnmrklroot`, `high-hash` |
| Transaction form | No input. No output. A size of 1,000,001 base bytes. A negative amount. An amount or a total above `MAX_MONEY`. A repeated outpoint. A null outpoint outside the coinbase. A coinbase script of 1, 2, 100 and 101 bytes | The nine sites of `CheckTransaction` |
| Block structure and order | No transaction. A first transaction that is not a coinbase. A second coinbase. A transaction before the one that funds it. A repeated tail of the list, as in CVE-2012-2459. A Merkle root without its fix-up | `bad-blk-length`, `bad-cb-missing`, `bad-cb-multiple`, `bad-txns-inputs-missingorspent`, `bad-txns-duplicate`, `bad-txnmrklroot` |
| Sizes | A block of exactly 1,000,000 and of 1,000,001 base bytes, in `block.check` and in `block.contextual_check_body` | `bad-blk-length`, `bad-blk-weight` |
| Signature operations | Exactly 20,000 and 20,001 operations: by legacy operations in an output, in a `scriptSig` and in the coinbase, and by a P2SH input. Both multisig counts. A `scriptSig` that is malformed or is not push-only | Both sites of `bad-blk-sigops` |
| Coins and inputs | An outpoint without a coin. A coin that an earlier transaction of the block spent. A coinbase coin at depth 29 and 30, and at depth 239 and 240. Inputs whose sum is above `MAX_MONEY`. Inputs below the outputs | `bad-txns-inputs-missingorspent`, the three sites of `CheckTxInputs` |
| Subsidy and coinbase amount | A coinbase that claims one koinu above the subsidy and the fees, with and without a fee. The heights are on each side of 145,000 and of 600,000, and one has the random subsidy | `bad-cb-amount` |
| Scripts | A changed byte of a real signature, of its hash type or of its public key. On made coins: a signature that is not strict DER and `OP_CHECKLOCKTIMEVERIFY`, each below and from its height, and a P2SH redeem script that fails | Both script sites |
| BIP30 and BIP34 | An unspent coin under the ID of a transaction of the block. The same with the ancestor hash `BIP34Hash`, which skips the test (lines 1877 to 1879). A coinbase script without the height, with a short height and with another height, on each side of 1,034,383 | `bad-txns-BIP30`, `bad-cb-height` |
| Time and finality | A lock time by height and by time on each side of the block's height and time, with final and other sequences. A block time at the median time and one second above it. A block time at the adjusted time plus 7,200 seconds and one second above it | `bad-txns-nonfinal` of `ContextualCheckBlock`, `time-too-old`, `time-too-new` |
| Witness data | Witness data in a transaction of the block's list | `unexpected-witness` |
| Supplied state | A removed coin. A coin with another amount, script, height or coinbase flag. An added coin. Changed times and `nBits` of chain entries. Another adjusted time. Heights of the chain moved by a multiple of 10,080 | The sites of `ConnectBlock` and of `ContextualCheckBlockHeader`, with a real block |
| Header index | An unknown predecessor. A known header with a failure flag. A predecessor with a failure flag. A failed ancestor. An anchor. A fork below a known checkpoint | The four sites of `AcceptBlockHeader`, and `bad-fork-prior-to-checkpoint` |

The class *Supplied state* is the part of the search that the hand-built evidence lacks most.
It tests a real mainnet block, with its real proof of work, on a state that makes Core reject it.
For example, a real block with one of its coins removed must give `bad-txns-inputs-missingorspent`.
A real block with an unspent coin under one of its own transaction IDs must give `bad-txns-BIP30`.

A chain whose heights move tests a real block at a height with other rules.
Take a predecessor at height 145,000 or above.
Core computes the required `nBits` from three values: the time and the `nBits` of the predecessor, and the time of the entry below it (`src/pow.cpp`, lines 50 to 54 and 77 to 87, and `src/dogecoin.cpp`, lines 41 to 87).
The height selects only the parameter record there (`src/validation.cpp`, line 3070).
So a block from that era can keep a correct `nBits` at another height of that era, and reach a later check.
A move by a multiple of 10,080 keeps the offset of the aligned version-bits boundary, so the chain of the seed stays long enough.

Four examples follow, each with the first check of Core's order that the moved block fails:

- A block of range A at a height from 371,337 is a legacy block after the AuxPoW start: `late-legacy-block` (lines 3073 to 3077).
- An AuxPoW block of range B at a height below 371,337: `early-auxpow-block` (lines 3082 to 3086).
- A block of range C at a height from 1,034,383, if its base version is below 3: `bad-version` (lines 3113 to 3116).
- A block of range D from height 1,034,383, moved up by 10,080: its coinbase script holds another height, so `bad-cb-height` (lines 3146 to 3151).

A block from below height 600,000, moved to that height or above, claims the larger subsidy of its real height.
If its coins pass at the new height, it reaches `bad-cb-amount`, the last check of `ConnectBlock` (lines 1996 to 2001).
These statements come from source inspection, and no run has tested them.
The stage that adds this class confirms each one with the coverage report.

### 5.4 Reaching a deep check

Core stops at the first failure, so a careless change of a block ends at an early check.
Three rules keep a case on its way to its site.

**Fix-ups.**
After its mutations, a plan repairs each field that an earlier check reads, unless a mutation of the plan aims at that field:

1. The Merkle root of the header follows the changed transactions.
2. The coinbase script keeps the height where BIP34 applies, and the coinbase claims at most the subsidy and the fees.
3. A made spend gets a signature again when a mutation changes a field that its signature commits to. Section 7 names the signer.

A real transaction cannot be signed again, because its keys are not known.
So a mutation of a committed field of a real spend ends at a script site.
The classes that go past the scripts use made coins.

**Proof of work.**
A changed header has no valid proof of work.
The generator has three ways to pass `CheckBlockHeader`:

- **Unmined.** The request has `check_pow` false, as the made blocks of the full comparison have. Core then skips the test of line 2933. An unmined block reaches every later site at every height.
- **Unchanged header.** The mutation leaves the 80 bytes and the payload as they are, and the request has `check_pow` true. A block mutation of this kind reaches three sites. `bad-txnmrklroot` follows a changed transaction without a new root. `bad-txns-duplicate` and `unexpected-witness` follow changes that keep the root. Every state mutation is of this kind.
- **Mined.** The generator searches a nonce for a made block. On mainnet the heights 1 to 239 keep the `nBits` of the genesis block, `0x1e0ffff0` (`src/chainparams.cpp`, lines 89, 90 and 155, and `src/pow.cpp`, lines 54 and 72). That target accepts about one scrypt digest in 2^20. The regtest fixtures of design record 0008 are mined in this way at the regtest limit. Stage 0 measures the time of one mainnet block.

**Depth.**
The order of Core's checks gives each site a depth.
`ConnectBlock` makes the BIP30 test first (lines 1881 to 2001).
Then it tests the coins, the signature operations, the input values and the scripts of each transaction in turn.
It tests the coinbase amount last.

The report of a run counts the cases that end at each site (section 9.1).
A class whose cases end above its site is a defect of the generator, and the stage that adds the class corrects it.

### 5.5 A context that both programs accept

The state of a request must stay inside the domain of both programs, or the case gives a request error and tests nothing.
The generator keeps these rules:

- A block mutation changes no part of the state. It never changes the previous hash of a `block.validate` candidate. A block that does not link gives the adapter error `not_linked` and no verdict ([errors](../oracle.md#errors-1)). A changed previous hash is a mutation of `block.header_sequence` alone, where line 3231 gives a verdict.
- A changed chain stays contiguous, and long enough for the median time, the retarget and the aligned version-bits boundary with its ten predecessors. The harness refuses a shorter chain ([block validation in the harness](../core-harness.md#block-validation-in-the-harness)).
- A changed chain keeps the case of the version-bits shortcut. The median time of the aligned boundary stays below the CSV start, or at or after the CSV timeout. A seed of the ranges E1 and E2 keeps its chain unchanged.
- A changed coin keeps the bounds of the `coins` argument ([the coins](../conformance.md#the-coins)). They limit the amount to `MAX_MONEY`, the index to 1,048,575 and the height to 2,147,483,646. No script starts with `OP_RETURN` or has more than 10,000 bytes.
- The BIP34 ancestor hash follows the height of the predecessor: null below 1,034,383, and the previous hash of the first block at that height.
- The adjusted time stays at most `INT64_MAX - 7200`.

The coins of a case at a height inside a range come from a *derived state*.
The harness runs the range request to the block below the case and writes its carried set with `snapshot_heights` ([the harness arguments](../core-harness.md#block-validation-in-the-harness)).
`scripts/restrict_coins.py` then keeps the coins whose transaction ID a block of the case names.
So the coins of a case are Core's own entries, and the case needs no replay of the range.
`validateBlock_restrict` states, for the Lean definition, that the restricted coins give the same error or the same changes ([soundness](../soundness/blocks.md#validateblock_restrict-a-block-on-the-coins-that-it-names)).
Property R4 of section 6.2 tests the same statement on Core for rejected blocks.

A verdict of a case is Core's verdict on the supplied state.
The supplied state of a state mutation is not a state of mainnet, and no result of the search says that it is.

## 6. The comparison

### 6.1 Agreement

The driver sends each request to the oracle and to the Core harness, and applies the agreement function of the operation from `scripts/compare_core.py`.
That function requires equal `ok` fields, except the oracle's `diagnostic`, and equal `error` objects.
It also checks both responses against Core's text: the score, the code and the corruption flag of each reason.
For `block.header_sequence` it keeps the exclusion of `marked_failed_child` of design record 0008, decision 12.
So a search agreement means what an agreement of the CI comparison means.

A block record of an accepted block must also agree in its digest of the coin changes.
The response must agree in the digest and the number of the coins after the last block.
So a rejected block that changes a coin in one program fails the comparison.

### 6.2 Properties

Agreement compares the two programs with each other.
Four more properties compare each program with an expectation that neither program made:

| Property | Statement | Expected value from |
| --- | --- | --- |
| R1 Agreement | Both programs give the same response to each request, under section 6.1. | The comparison itself |
| R2 Directed site | A directed case is rejected with the reason, the score and the code of its site. | The rule of the class, which a person derived from the cited lines, and the table of section 3.2 |
| R3 No change after a rejection | Take a rejected candidate and then the real block of the same height. The real block is accepted with the digest of the changes of the committed expected results of its range. | [`tests/conformance/ranges`](../../tests/conformance/README.md) |
| R4 Restriction | A case gives the same block records on its restricted coins and on the whole carried set of its derived state. | The first run is the expectation of the second. The property is a relation, not a known answer |
| R5 First failure | A plan with two directed mutations is rejected at the site that Core's order reaches first. | The order of the cited lines |

R3 applies to block mutations, which leave the state of the seed unchanged.
No expected value comes from the oracle, from the harness or from the signer, as design record 0009, decision 4, requires.

### 6.3 Outcome classes

The driver gives each case one class.
The first six are the classes of design record 0009, section 7.2, and the last two are additions:

| Class | Condition |
| --- | --- |
| `verdict` | The verdicts, reasons, scores or codes differ, or a response differs from the expectation of R2, R3 or R5. |
| `digest` | A digest or a count of coins differs between the programs, or R3 or R4 fails on a digest. |
| `crash` | A program exits with a nonzero status or a signal, or its output fails the checks of the stream. |
| `timeout` | A batch, or the bisected request alone, exceeds the time limit. |
| `unsupported` | The oracle returns the error `outside_model` where the property needs a verdict ([errors](../oracle.md#errors-1)). |
| `refusal` | Either program returns a request error or an adapter error for the case. |
| `out-of-domain` | The oracle ends the range at the candidate with `out_of_domain_at` ([the arithmetic domain](../oracle.md#the-arithmetic-domain)). |
| `known` | The case matches an entry of the list of known behaviours (section 6.6). |

`unsupported`, `refusal` and `out-of-domain` are not disagreements.
The driver counts them and saves a sample of each, so that a loss of coverage stays visible.
A `verdict` or `digest` failure also records the failing side, by the table of design record 0009, section 7.2.

The search runs the trap build of the harness, `core-oracle-trap` ([the Core pass](../core-harness.md#the-core-pass)).
Core adds amounts in `ConnectBlock` with no range check, and an overflow there is undefined behaviour (design record 0010, section 3).

The driver sends the oracle each request first.
It sends the harness an `out-of-domain` request without the candidate, as the CI comparison does.
A trap on any other request is a `crash` on the Core side.
In such a case Core left the `int64_t` range on a request that the oracle kept inside its domain.
So the case is a candidate about the domain test of `connectBlock`.

### 6.4 What counts as a finding

A *candidate* is a saved failure of class `verdict`, `digest`, `crash` or `timeout`.
A candidate becomes a *finding* when all of these hold:

1. Its replay reproduces the class and the failing side.
2. The reducer gives a reduced case that keeps the failure condition.
3. A person reads Core's text at the site of the reduced case and derives the result by hand.
4. The checks of section 6.5 give it a label other than `generator-fault`.

A count of `unsupported`, `refusal` or `out-of-domain` cases above the limit of section 9.2 fails a run, but it is not a finding.

### 6.5 Triage

The hand derivation from the pinned source decides which side is wrong ([sources of truth](../../CONTRIBUTING.md#sources-of-truth)).
Each finding gets one label:

| Label | Meaning | Follow-up |
| --- | --- | --- |
| `dogelib-model` | A Lean definition differs from Core's text. | A correction of the definition, a fixture with Core's behaviour as the expected value, and a theorem where one fits |
| `dogelib-adapter` | The oracle's adapter differs: the request reader, the response writer or a file read. | A correction and a fixture |
| `harness-fault` | The harness gives Core's function another input than the request states. | A correction of the harness and a fixture |
| `generator-fault` | The expectation of the plan is wrong, and both programs agree with Core's text. | A correction of the class. No fixture |
| `core-outside-model` | Core's behaviour is real and lies outside the Lean model: undefined behaviour, or a domain that the adapter refuses. | An entry of the known behaviours with a citation, and a statement of the domain in SOUNDNESS.md |
| `core-candidate` | Core's own function gives a result that its text or its rule contradicts. | Section 6.7 |

Three checks separate a harness fault from a behaviour of Core.
Design record 0009, section 9.1, has the levels L1 to L3, and the checks below take their place for blocks.

**B1: another carrier.**
The harness can carry the coin set in a `std::map` and in Core's own `CCoinsViewDB` ([the Core pass](../core-harness.md#the-core-pass)).
It can read the coins from the request and from a snapshot file.
A candidate that depends on the carrier or on the form of the coins is a fault of the harness's set code.
The harness also reports Core's version-bits state for a chain, which checks the seeded state of a request.

**B2: Core's own composition.**
`TestBlockValidity` (lines 3412 to 3433) is Core's own call of the checks on the tip of a node, with `fCheckPOW` as an argument.
It calls `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock` and `ConnectBlock` with `fJustCheck` true, and `CheckBlock` calls `CheckBlockHeader` (line 2948).
The RPC `getblocktemplate` in the mode `proposal` calls it with `fCheckPOW` false (`src/rpc/mining.cpp`, lines 454 to 481).
It returns the reject reason (lines 326 to 339 of the same file).

So a node can judge an unmined candidate on its own tip, through its own block index and its own coin database.
`submitblock` judges a mined candidate through `ProcessNewBlock` (lines 764 to 827 of the same file).

The replay builds the predecessor chain of the candidate on a node, as level L3 of the campaign builds its outputs.
Two chains can exist:

- A made chain from the mainnet genesis block below height 240, mined at the `nBits` of the genesis block. It reaches the rules that are active there.
- A regtest chain. On regtest, AuxPoW starts at height 20, BIP66 at 1,251 and BIP65 at 1,351 (`src/chainparams.cpp`, lines 390, 391 and 432). The replay builds a case of the same class at the regtest height of its rule. Its verdict is evidence about Core's code for the class, and not about the mainnet parameters.

A candidate that neither chain can hold has the replay outcome `not-comparable`, as in the campaign.
Stage 4 confirms that a node without peers answers a proposal, and it records the classes that each chain can hold.

**B3: the current upstream revision.**
A candidate that reproduces at the pin runs again on a harness build of the current upstream commit of the pin's branch.
Design record 0009, section 9.2, sets the rules of that build.
The result is labelled with its commit, and the pin does not change.

### 6.6 Known behaviours

Some baseline behaviours look like faults, and the search must not report them.
The driver keeps a list, and an entry enters it only with a citation of the pinned source:

- `ConnectBlock` skips the BIP30 test when the ancestor at `BIP34Height` has the hash `BIP34Hash`, and then replaces an unspent entry (lines 1877 to 1879, and design record 0010, section 2).
- A failed script that passes without the flags that are not mandatory gives `non-mandatory-script-verify-flag`, with the score 0 and the code 64 (lines 1493 to 1503). At the pin a DERSIG or a CLTV failure of a block has this reason (design record 0010, section 5, and [the campaign](../campaign.md#l3)).
- `bad-txns-premature-spend-of-coinbase` has the score 0 (lines 1435 to 1437).
- The oracle's limit on the height of a predecessor is narrower than Core's domain ([block validation](../oracle.md#block-validation)).

### 6.7 A candidate against Core

A `core-candidate` can be a vulnerability of Core.
The rules of design record 0009, section 9.4, and of [SECURITY.md](../../SECURITY.md) apply without change:

- The saved failure stays in the uncommitted `build/campaign/` directory, and the maintainer learns of it privately.
- No issue, pull request, CI log or fixture holds the input or its effect before the report is resolved.
- CI runs only a fixed seed whose results a person has reviewed. A run with a fresh seed stays on a contributor's machine.
- A case enters the negative corpus only after a person has reviewed it.

## 7. What the search reuses from the campaign

The search is a campaign of `scripts/campaign.py`, under a name of its own.
It reuses these parts of design record 0009 without change:

- The commands `run`, `replay` and `reduce`, with a seed, a budget of cases and a budget of seconds.
- Batches of a fixed size, with bisection of a stream failure to one request.
- The saved failure `dogelib-campaign-failure/1`, with the exact requests, both complete responses, the revisions and the replay command.
- The label `minimal` or `budget` of a reduced output.
- The rule that a self-test with planted faults measures the reach of the generator (section 10).

These parts change:

| Part | In design record 0009 | In this record |
| --- | --- | --- |
| The plan | A signed spend of one template | A block plan or a header plan (section 5.1). The field `plan` of a saved failure holds it, and a field `plan_kind` names its kind. The field is an addition to the format |
| The operations | `script.verify_legacy` and `sighash.legacy` | The six operations of section 3.1 |
| The signer | `core-signer --sign` signs every case | The signer signs only a made spend of a made coin. A real spend keeps its real signature |
| The properties | Q1 to Q7 of one Script template | R1 to R5 of section 6.2 |
| The outcome classes | Six | Eight (section 6.3) |
| The reducer | Changes to a spend plan | Changes to a block plan (below) |
| Production replay | L1 to L3 for a spend | B1 to B3 of section 6.5 |
| The harness build | `core-oracle` | `core-oracle-trap` |

The reducer changes the plan, and a candidate plan replaces the current one when it keeps the property, the class and the failing side.
It tries these changes in order, and repeats them until no change applies:

1. Remove one mutation, then two adjacent mutations, then halves.
2. Remove each transaction that no mutation names and no later transaction spends. Then remove each input and each output of a made transaction.
3. Replace a real seed with a made block on the same header, when the failure condition stays.
4. Restrict the coins to the IDs that the blocks of the case name.
5. Replace each number with the simplest value of its boundary class.
6. Clear `check_merkle_root`, then `check_pow`, when the failure condition stays.

The reducer applies the fix-ups of the plan again after each change.
It does not shorten the chain, because the harness refuses a chain that is too short (section 5.5).

## 8. The negative corpus

### 8.1 Options

The corpus of design record 0011 has one request and one blocks file for each range, and its results have one line for each height.
A rejected block can stand only at the last height of such a file ([the results](../conformance.md#the-results-dogelib-range-results1)).
Two forms can hold rejected blocks:

- **N1: rejected candidates in a range.** A second blocks file of a range holds rejected candidates before the real block of their height. `block.validate` already takes such a file ([blocks from a file](../oracle.md#blocks-from-a-file)). The results format changes: a height can have more than one line. A third program must run the whole range to reach a candidate, and all candidates share the flags of one request. A state mutation has no place in this form.
- **N2: cases.** Each rejected block is a small request of its own, with the coins that its blocks name. The existing formats do not change. A third program runs one case in the time of one block. Both kinds of mutation fit.

**Recommendation: N2.**
It changes no published file and no published format, and it holds state mutations.
A third program does not replay 2,000 blocks for one verdict.

### 8.2 The formats

The proposal adds three formats.
The names are proposals:

**`dogelib-block-cases/1`, a group of cases.**
A group file is one JSON object for one derived state:

| Key | Value |
| --- | --- |
| `format` | `"dogelib-block-cases/1"` |
| `group` | The name of the group |
| `seed` | The range, the height and the hash of the seed block, or the name of a made context |
| `request` | The keys of a range request: `op`, `mode`, `check_pow`, `check_merkle_root`, `adjusted_time`, `chain`, `bip34_ancestor_hex` and `coins` ([the range request](../conformance.md#the-range-request)) |
| `cases` | A list of cases |

A case is an object with these keys:

| Key | Value |
| --- | --- |
| `case` | The name of the case, which is unique in its group |
| `class` | The mutation class of section 5.3 |
| `site` | The file and the line of the reject site of Core that the case reaches, or null for a case with no rejected block |
| `replace` | An object with some of the keys of `request`. Each value takes the place of the value of the group |
| `blocks_hex` | The blocks of the case in order, each one all of its bytes |

The request of a case is the `request` of its group, with the values of `replace`, and with `blocks_hex`.
It is a `block.validate` request of `dogelib-oracle/1`, so a program that runs a range request runs it.
The verdict of each block follows the rules of the range request without change ([the verdict of a block](../conformance.md#the-verdict-of-a-block)).
A block mutation has an empty `replace`, or one that sets a flag.
A state mutation gives the changed `coins`, `chain`, `adjusted_time` or `bip34_ancestor_hex` in `replace`.
A case can hold a rejected candidate and then the real block of the same height, which tests that the rejection changed nothing.

**`dogelib-case-results/1`, the results of a group.**
A results file holds one line of JSON for the start and one line for each case, in the order of the group.
The start line has `format`, `group` and `group_sha256`, the SHA-256 of the group file.
A case line has these keys:

| Key | Value |
| --- | --- |
| `case` | The name of the case |
| `blocks` | One object for each block of the case: `hash_display`, `valid`, `reject_reason`, `changes_digest_hex`, `spent` and `created`, as in a block line of `dogelib-range-results/1` |
| `end_set_digest_hex`, `end_set_coins` | The digest and the number of the coins after the last block ([digests](../conformance.md#digests)) |

A case line can also hold `dos` and `reject_code` in each block object.
The expected results hold both, and the checker compares them only when a results file has them.

**`dogelib-case-assets/1`, the list of the assets.**
A committed file names the release, as `release.json` does for the ranges.
It gives the size and the SHA-256 of each group asset and of each group file.

The table gives the change to each existing part, and each change is additive:

| Existing part | Change |
| --- | --- |
| `dogelib-blocks/1`, `dogelib-coins/1`, `dogelib-range-results/1`, `dogelib-corpus-assets/1` | None |
| The published assets and the expected results of the nine ranges | None |
| `scripts/check_range_results.py` | None |
| `dogelib-oracle/1` | None. A case uses `block.validate` with `blocks_hex` |
| The range request | It defines `check_pow` and `check_merkle_root` already. The corpus of the ranges sets both to true, and a case can set either to false |
| `docs/conformance.md` | New sections for the three formats and for a run of a group |
| `tests/generators.toml`, the pinned-vectors gate | New entries |

One requirement on a third program is new.
A case of an unmined block has `check_pow` false.
So the program must be able to skip the proof-of-work test of `CheckBlockHeader`, as Core's `fCheckPOW` does (lines 2933 and 3412 to 3424).
A program without that option can still run the cases with `check_pow` true.
Decision 9 asks whether the corpus holds unmined cases.

### 8.3 The checker

A committed checker `scripts/check_case_results.py` compares a results file with the expected results of its group.
It uses only the Python standard library, as the checker of the ranges does.
It must fail on each of these faults:

- A case without a line, a line of no case, a case with two lines, and cases in another order.
- A case with another number of block objects than it has blocks.
- A wrong verdict, a wrong reject reason, a wrong digest or a wrong number of coins.
- A `group_sha256` that is not the SHA-256 of the committed group.
- A file that is not a results file.

Its ordinary mode compares the verdict, the reject reason and the digests.
The option `--verdict-only` leaves out the reject reason.
A reject reason is a text of Core, and a program that is not Core can state its reasons in another way.
The report of the checker says which mode ran, so a pass in the second mode is not read as agreement on the reasons.

### 8.4 How a case enters the corpus

1. A case of a run at a reviewed seed, or a reduced finding, is a candidate for the corpus. A directed case has its site from its plan. A free case has a site only after a person derives it.
2. The oracle and the Core harness run the request of the case, and must agree under section 6.1.
3. The expected results of the case are the response of the Core harness in that run ([provenance](../conformance.md#provenance)).
4. For a directed case, the expected reason, score and code must also equal those of its site in section 3.2.
5. `tests/generators.toml` records the run. The record names the harness, its Core commit, the DogeLib commit, the seed and the SHA-256 of each group. It also names the oracle build that agreed.
6. `SHA256SUMS` pins the expected results, and the pinned-vectors gate adds the directory.

So an expected value comes from Core's code, and for a directed case also from Core's text.
It never comes from the program under test.
The corpus holds at least one case for each of the reject sites that `block.validate` reaches.
It also holds at least one accepted control in each group: the real seed block alone.

EthLib, the model project, has negative vectors at its pin `bb6dfe5`.
Its directory `tests/execution/legacytests` holds blockchain tests of `ethereum/legacytests`, with the `InvalidBlocks` suites.
In those tests each block is valid, or names the exception with which a client rejects it.
Its `tests/sources.toml` records one pinned commit for each source repository.
That directory has a `SHA256SUMS` file, and its README names the source and each case where EthLib disagrees.

DogeLib follows that model for the pins, the `SHA256SUMS` file and the README.
DogeLib has no upstream suite of rejected Dogecoin blocks to copy.
So the proposal records the generator and its inputs where EthLib records an upstream commit.

### 8.5 Size

The assets of the nine ranges have 267,382,512 bytes in all ([`release.json`](../../tests/conformance/release.json)).
Most of a group file is its `chain`, which reaches the aligned version-bits boundary.
The range request of E2 shows the cost of a long chain.
It has 116,409,971 bytes, and its chain has 513,092 entries ([the chain](../conformance.md#the-chain)).

The proposal sets this budget:

- No group stands on a seed of E1 or E2.
- Each group asset has at most 2 MB after compression with xz.
- All group assets together have at most 25 MB, under one tenth of the assets of the ranges.
- The committed expected results have at most 2 MB.

No file of a group exists, so these numbers are limits and not measurements.
Stage 0 measures one group at a height of each range, and the maintainer can change the budget then.

### 8.6 Header cases

A `block.header_sequence` request is already a complete case: the index, the failed list and the headers.
Its verdict reads node state that is not consensus data: the failure flags and the failed list (lines 3219, 3233 and 3241 to 3255).
The proposal publishes header cases only for an index without a failure flag and with an empty failed list.
Those cases reach `high-hash`, the unknown predecessor of line 3231 and the seven reasons of `ContextualCheckBlockHeader`.

A group of header cases has the keys of a `block.header_sequence` request in its `request`, and each case has `headers` in the place of `blocks_hex`.
Its results hold the fields of the result that are not node state: `valid`, `failed_at` and `reject_reason`.
Decision 11 asks whether the corpus holds them.

## 9. Evidence and coverage

### 9.1 The report of a run

Each run writes `summary.json`, as a campaign run does, with these added counts:

- For each reject site of section 3.2: the number of cases that ended there, in each mode, and the number that agreed.
- For each mutation class: the cases, and the sites where they ended.
- For each rejecting constructor of the Lean error types: the number of cases whose `diagnostic` names it.
- For each outcome class: the count, with the saved samples.
- The sites and the constructors that no case reached.

A run knows the site of a case from three sources.
The reject reason gives the site, except where two sites share a reason.
The oracle's `diagnostic` names the failing step and the Lean error, which separates the two sites of `bad-blk-sigops` and the three of `bad-prevblk` ([block validation](../oracle.md#block-validation)).
A directed plan names the condition of a site with more than one.

### 9.2 The coverage target

A run at the CI seed must meet all of these:

1. Each of the 40 sites of section 3.2 has a directed case. Core rejects it at that site, and the oracle agrees.
2. Each condition of section 3.2 that a request can reach alone has a directed case.
3. Each rejecting constructor of the Lean error types has a case. Otherwise section 3.3 names the theorem or the argument that excludes it.
4. No case ends at a site of section 3.3.
5. The cases of class `refusal`, `unsupported` and `out-of-domain` are together under 2 percent of the cases.
6. No candidate exists other than `known`.

The target counts reject sites of Core's text, and a site can hide a path that no class reaches.
So a recorded run outside CI also measures the lines that Core executed.

The proposal adds a build option `--coverage` to `scripts/build_core_harness.sh`, beside `--trap-overflow`.
It compiles the unit that includes `src/validation.cpp` with the coverage option of the compiler.
After a run, `gcov` gives the execution count of each line and each branch of the functions of section 3.2.
The record of the run lists each line of those functions that no case executed, with the reason or with an open question.
The coverage build is a measurement tool, and no verdict comes from it.

### 9.3 CI and runs outside CI

| Run | Where | Seed | Budget | Harness |
| --- | --- | --- | --- | --- |
| The directed cases and a free search | The `core` workflow, in the job `compare` | One fixed seed, reviewed by a person | 10 minutes of the job on a GitHub runner | `core-oracle-trap` |
| The self-test of section 10 | The same job | Fixed | Inside the same 10 minutes | A wrapper |
| The corpus groups from the released assets | The job `conformance` | None | 5 minutes | `core-oracle` and the oracle |
| A search with a fresh seed | A contributor's machine | Fresh | 8 hours on at most 8 cores, at low priority | `core-oracle-trap` |
| The coverage measurement | A contributor's machine | The CI seed and one fresh seed | 1 hour | The coverage build |
| The replay on a node | A contributor's machine | The planted fault of stage 4 | Minutes | A node build |

The budgets are limits, and no time of this search is measured.
One recorded figure gives a first estimate: the oracle takes about 4.1 ms for each input of a block, and Core about 89 µs (design record 0011, section 2).
A request with a long chain also pays for its chain.
So the driver sends the block mutations of one derived state as candidates of one request, which reads the chain once.
`block.validate` takes several candidates for one height in this way ([block validation](../oracle.md#block-validation)).
Stage 0 measures the rate, and the CI run takes the largest number of free cases that fits its budget.

The job `compare` has a limit of 60 minutes (`.github/workflows/core.yml`).
Stage 1 records the time of that job before and after.
It moves the search to a job of its own if the limit is near.

## 10. The self-test

A run with zero candidates says little if the generator cannot reach a deep fault.
`scripts/test_campaign.py` gains planted faults for blocks, as design record 0009, section 8.2, has for spends.
A wrapper stands in for one program and changes its response when a request meets a semantic trigger:

| Mutant | Side | Trigger | Change | Expected class |
| --- | --- | --- | --- | --- |
| K1 | Core | A coinbase that claims exactly one koinu above the subsidy and a fee that is not zero | Accept the block | `verdict` |
| K2 | Lean | A coinbase coin at depth 239 from height 145,000 | Accept the block | `verdict` |
| K3 | Core | A block whose 20,001st signature operation comes from a P2SH input | Accept the block | `verdict` |
| K4 | Lean | A failed strict-DER signature at a height from 1,034,383 | Report the mandatory reason | `verdict` |
| K5 | Core | A rejected candidate of the class *Coins and inputs* | Report the digests of a set in which one of its spends took effect | `digest` |
| K6 | Lean | A real block with an added unspent coin under the ID of its second transaction | Accept the block | `verdict` |
| K7 | Core | A header whose predecessor has a failed ancestor two entries below it | Report the score 10 | `verdict` |
| K8 | Core | A block of exactly 1,000,001 base bytes | Exit with status 3 | `crash` |

The list is a proposal, and the stage settles the triggers.
For each mutant the self-test requires detection within the CI budget, and records the case index of the first detection.
It also requires that the reducer keeps the trigger, and that the replay reproduces the stored class.
K5 has no difference in a verdict, so only the digests and property R3 find it.
K6 needs a state mutation, so only that class finds it.

## 11. Stages and exit conditions

### Stage 0: measurements

The stage adds no Lean code and no gate.

1. The number of seed blocks of each range that pass the constraint of section 4.
2. The size of one group file at a height of each range, with and without compression.
3. The time of each program for one request of 100 candidates, with a short chain and with a long one.
4. The time to mine one made block at the `nBits` of the genesis block.
5. A build of the harness with the coverage option, and the `gcov` output of the full comparison of `block.validate`.

The stage exits with those numbers in the pull request.
If a number breaks a budget of sections 8.5 or 9.3, the lane stops and asks the maintainer.

### Stage 1: block mutations

The stage adds block plans, the directed and free modes, the fix-ups, and each class of section 5.3 except *Supplied state* and *Header index*.
It adds the report of section 9.1, the outcome classes, and the mutants K1 to K4 and K8.

1. At the CI seed, the sites of five functions meet conditions 1 and 2 of section 9.2. The functions are `CheckTransaction`, `CheckBlockHeader`, `CheckBlock`, `ContextualCheckBlockHeader` and `ContextualCheckBlock`. `bad-fork-prior-to-checkpoint` meets the conditions through `block.contextual_check`.
2. Each site of `ConnectBlock`, `CheckTxInputs` and `CheckInputs` meets the same conditions through made blocks.
3. Conditions 4 to 6 of section 9.2 hold.
4. Each of the five mutants is detected within the budget, and its saved failure replays.
5. The run is in CI under section 9.3.

### Stage 2: state mutations, derived states and the reducer

The stage adds the class *Supplied state*, the derived states of section 5.5 and the properties R3 to R5.
It also adds the reducer for block plans, and the mutants K5 and K6.

1. Take a derived state at a height of each range. The real block of that height gives its block record of the committed expected results.
2. At the CI seed, each site of `ConnectBlock`, `CheckTxInputs` and `CheckInputs` has a directed case with a real block. Both flags of the case are true. Otherwise the pull request states why a site has none.
3. The moved heights of section 5.3 reach `late-legacy-block`, `early-auxpow-block`, `bad-version`, `bad-cb-height` and `bad-cb-amount` with real blocks. Otherwise the pull request states which statement of that section failed.
4. R4 holds on every case of the run, in both programs.
5. The reducer keeps the trigger of each mutant, and each output with the label `minimal` replays.

### Stage 3: header acceptance

The stage adds header plans, the class *Header index*, and the mutant K7.

1. At the CI seed, each of the four sites of `AcceptBlockHeader` has a directed `block.header_sequence` case. So has each of the seven sites of `ContextualCheckBlockHeader`. The oracle agrees on each case.
2. Condition 3 of section 9.2 holds for `HeaderRejection`.
3. The search detects K7, the reducer keeps its trigger, and the replay reproduces it.

### Stage 4: triage and replay

The stage adds the checks B1 to B3 of section 6.5 and the labels.

1. The search finds a planted fault of the harness's set code, and the reducer reduces it. B1 gives another result with the other carrier, and the label is `harness-fault`.
2. A node answers a proposal for a made candidate on a made chain from the mainnet genesis block. A regtest node answers one on a regtest chain. On each chain, one candidate of each of four classes gets the reject reason of its site.
3. The pull request lists the classes that each chain can hold, and the classes that are `not-comparable`.

### Stage 5: the negative corpus

The stage runs only if the maintainer accepts decisions 8 to 12.

1. `docs/conformance.md` defines the three formats and the steps of a run of a group, without reference to the Lean code.
2. The groups are release assets with committed SHA-256 values, and their expected results are committed. They meet section 8.4 and the budget of section 8.5.
3. The checker passes on the results of both programs, and fails on each fault of section 8.3.
4. A person who did not write the tools runs one group from the document alone. They use a program of their own or a wrapper of the harness. The pull request records the steps that the document lacked.
5. In CI, the oracle runs the groups from the released assets, and the checker passes.

### Stage 6: a recorded run and the documents

1. A recorded run outside CI uses a fresh seed and the budget of section 9.3. It has no candidate other than `known`, or each finding has its label and its follow-up.
2. The pull request records the coverage measurement of section 9.2, with each line that no case executed.
3. Each understood finding has a fixture under `tests/block/campaign/`. Its README records the plan, the seed, both revisions and the reduction.
4. COVERAGE.md, SOUNDNESS.md, `docs/campaign.md` and `docs/comparison-evidence.md` state the counts and the limits of the evidence.

### Gates

Each stage adds its commands to the gate table of AGENTS.md and to `scripts/release_gates.json`.
The runs of stages 1 to 3 and condition 5 of stage 5 run in CI.
The fresh-seed run, the coverage measurement and the node replay are recorded gates outside CI.

## 12. Excluded

- A proof of agreement on rejected blocks, and any theorem on the order of the checks. COVERAGE.md records that no theorem covers that order, and such a theorem is a separate candidate.
- Native fuzzing with libFuzzer and sanitizers for memory errors, which needs a separate Clang build of Core (design record 0009, section 12).
- Coverage feedback inside the search. The coverage build measures a finished run and does not steer the generator.
- Testnet and regtest block rules in the oracle.
- A generator of the parts of an AuxPoW payload, and reader errors (section 3.3).
- A replay of a candidate through `ActivateBestChain`, a reorganization or the peer protocol.
- Any block that is not a seed of section 4.
- A stability promise for the three formats beyond the 0.x policy ([format stability](../oracle.md#format-stability)).
- Properties of an application or of a downstream project.

## 13. Decisions

**Decision maker:** Maintainer. Every decision is open.

| Number | Topic | Proposal | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | Scope | The six operations of section 3.1 and the 40 reject sites of section 3.2, with the exclusions of section 3.3. | The sites of `ConnectBlock` alone. Or `block.validate` alone, without the operations that reach one check. | Open |
| 2 | Seeds | The seeds of section 4, and no other block. | Made blocks alone, with no real block. | Open |
| 3 | Generator | Plans with block mutations and state mutations, in a directed and a free mode, with the fix-ups of section 5.4. | Byte-level mutation of block bytes, which ends mostly at the reader and at the Merkle root. | Open |
| 4 | State mutations | The class *Supplied state*, with derived states from the harness's carried set (sections 5.3 and 5.5). | Block mutations alone. Each real block then loses its proof of work when a check below the Merkle root is the target. | Open |
| 5 | Expected values | From the rule of a directed class, which a person derives from Core's text. Never from either program (section 6.2). | Agreement alone, with no expectation. | Open |
| 6 | Comparison | The agreement functions of the CI comparison, properties R1 to R5 and the eight outcome classes. The trap build is the harness of the search (section 6). | The ordinary harness build, with no trap. | Open |
| 7 | Triage and replay | The six labels of section 6.5, and the checks B1 to B3 with a node replay through `getblocktemplate` in the mode `proposal`. The disclosure rules of design record 0009 apply (section 6.7). | Triage by source inspection alone, with no node replay. | Open |
| 8 | Form of the negative corpus | N2: cases in groups, with the formats `dogelib-block-cases/1`, `dogelib-case-results/1` and `dogelib-case-assets/1`. No existing format and no published file changes (section 8). | N1: rejected candidates in the ranges, with a second version of `dogelib-range-results`. Or no negative corpus, with the search as a tool of the DogeLib comparison alone. | Open |
| 9 | Unmined cases | The corpus holds cases with `check_pow` false, so a third program needs that option. | Cases with both flags true alone: state mutations, the three block mutations that keep a header, and mined blocks below height 240. | Open |
| 10 | Reject reasons in the checker | The ordinary mode compares the reject reason, and `--verdict-only` leaves it out. The expected results also hold the score and the code (section 8.3). | Verdicts alone. Or the reason, the score and the code as required fields. | Open |
| 11 | Header cases | Published for an index without failure flags, in the same formats (section 8.6). | No header case in the corpus. The search still compares them. | Open |
| 12 | Size | The budget of section 8.5, and no group on E1 or E2. | Another budget after stage 0. | Open |
| 13 | Coverage | The target of section 9.2, and a build option `--coverage` for a measurement outside CI. | The response counts alone, with no measurement of executed lines. | Open |
| 14 | CI | The directed cases, a free search at one reviewed seed and the self-test in the job `compare`, within 10 minutes. The groups in the job `conformance` (section 9.3). | All of it outside CI. Or a job of its own. | Open |
| 15 | Campaign reuse | The search is a campaign of `scripts/campaign.py`. `dogelib-campaign-failure/1` gains the field `plan_kind`, and the regression fixtures go in `tests/block/campaign/` (section 7). | A separate driver and a separate format of saved failures. | Open |
| 16 | Mined blocks | Stage 0 measures the cost. If one block takes under one minute, the corpus holds a mined case for each class that a chain below height 240 can hold. | No mined block. | Open |

## 14. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The generator ends at early checks, so zero candidates say little about the deep sites. | The fix-ups, the count of cases at each site, the coverage target and the mutants of section 10. |
| The rule of a directed class is wrong, so the run reports false failures. | Review of each rule against its cited lines. A false failure shows as "both violate", and gets the label `generator-fault`. |
| The oracle and Core share a mistake, and both agree with a wrong verdict. | Properties R2, R3 and R5 take their expectations from Core's text and from the committed results. A third program that disagrees with the corpus is a finding to examine. |
| A fault of the harness's index or set code gives a wrong verdict that looks like Core's. | The checks B1 and B2 of section 6.5, and exit condition 1 of stage 4. |
| A state mutation leaves the domain of a program, and most cases are refusals. | The rules of section 5.5 and the limit of 2 percent in section 9.2. |
| The statements of section 5.3 about moved heights do not hold for some seed. | Exit condition 3 of stage 2 names the statement that failed. The class of made blocks reaches the same sites without it. |
| The coverage build changes the behaviour of the harness. | No verdict comes from that build. Its responses must equal those of the ordinary build on the same requests. |
| A group file is much larger than the budget. | Stage 0 measures before any format is fixed, and decision 12 can change the budget. |
| A third program reads agreement on the corpus as agreement on every rejected block. | The corpus document states the classes, the sites and the seed of each run, and that the cases are a finite sample. |
| A reject reason of Core is read as a consensus requirement on another implementation. | The mode `--verdict-only`, and the statement of section 8.3. |
| A public CI log or a published case shows a vulnerability of Core before a report. | Section 6.7: reviewed seeds in CI, uncommitted storage, and review before a case is published. |
| The search costs more CI time than its budget. | Stage 0 measures the rate, and the CI run takes the number of free cases that fits. |

This record changes no pin and no agreed theorem statement, and it asks for no exception to the trust policy.
Decisions 8 to 12 introduce fixture formats and published files, so they need the maintainer.
Decision 15 adds a field to a local file format and a fixture directory.
Decision 13 adds a build option of a harness tool, under the 0.x policy.
Adoption of the scope establishes no result, and it does not authorize the merge of a later implementation.
