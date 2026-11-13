# Block validity

**Status:** Adopted on 2026-11-13, with the decisions of section 8.
This record is frozen. Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-13
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [oracle contract](../oracle.md), [design record 0003](0003-legacy-spend-validation.md), [design record 0008](0008-header-sequence-validation.md) and the [model reads](../reviews/README.md).

## 1. Purpose

DogeLib cannot judge a block.
It has no definition of `CheckTransaction`, `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock` or the block subsidy.
So the oracle cannot replay the chain.
This record sets the scope, exit conditions and theorem targets for those functions in three stages.
Each stage ends in a capability that a test shows.

Stage 0, pull request #143, put Core's own `validation.cpp` into the harness.
Every comparison below calls Core's function there, never a copy.
Open questions go to issues.

Core is Dogecoin Core at the pin `e0a1c157`. Line numbers refer to `src/validation.cpp` unless a file is named.

## 2. Facts at the pin

| Rule | Mainnet behaviour | Source |
| --- | --- | --- |
| BIP34 | From height 1,034,383, the coinbase script starts with the height. The block version is not read. | `chainparams.cpp:84`, 3146–3152 |
| BIP30 | Checked for every transaction ID that the block creates, at every height. Core skips the check when the ancestor at `BIP34Height` (1,034,383) has the hash `BIP34Hash`. But `BIP34Hash` is the hash of block 1,032,483, so the skip never applies on mainnet. | 1869–1887, `chainparams.cpp:84–85`, `tests/block/mainnet-bip66-headers` |
| Script flags | P2SH at every height, DERSIG from 1,034,383, CLTV from 3,464,751. The logic is inline. | 1890–1917 |
| CSV | Never active. Version bits need the top bits `001`. A header that passes the mainnet chain-ID check is legacy or has chain ID `0x62`, so its top bits are `000`. The lock-time cutoff is therefore the block's own time. | `versionbits.cpp:155`, `pureheader.h:110–155`, `dogecoin.cpp:89–122`, `chainparams.cpp:120–136`, 3128–3136 |
| SegWit | `IsWitnessEnabled` returns false directly. `ContextualCheckBlock` reads the deployment, whose timeout is 0. If the earlier checks pass, witness data gives `unexpected-witness`. | 3002–3008, 3138–3188 |
| Script failures | Core runs no script-check threads here. If a failing input passes again without the non-mandatory flags, the reason is `non-mandatory-script-verify-flag` with no DoS score (1503). Otherwise it is `mandatory-script-verify-flag-failed` (1512). | 1488–1512 |
| Coin set | Unspendable outputs never enter it: a script that starts with `OP_RETURN` or exceeds `MAX_SCRIPT_SIZE`. The genesis block adds nothing. | `coins.h:90–126`, `script.h:635–637`, 1819–1824 |
| Maturity | Chosen by the height of the spent coin: 30 below 145,000, then 240. | 1433 |
| Limits | Base size 1,000,000 bytes. Sigop cost 80,000 at scale 4, so 20,000 sigops. `MAX_MONEY` is 10^18 koinu, in a signed 64-bit `CAmount`. | `consensus.h:13–19`, `primitives/transaction.h:17`, `amount.h:32` |
| Subsidy | Heights 1 to 144,999: `(1 + draw) * COIN`. `draw` is one value of `boost::uniform_int<>(1, maxReward)` over `boost::mt19937`, seeded from hex characters 7 to 13 of the previous hash. `maxReward` is 999,999 below 100,000, then 499,999. From 145,000: `(500000 * COIN) >> (h / 100000)`, and 10,000 coins from 600,000. | `dogecoin.cpp:16–21, 127–149` |

The subsidy follows the rejection algorithm of Boost 1.70.0, not only Core's text.
The definition cites that Boost source, and the comparison records the Boost version that the harness used.

## 3. Arithmetic domain

`CheckTransaction` checks each output before it adds it (542–548).
Other sums have no check before use.
`GetValueIn` adds input values with no range check (`coins.cpp:272–279`).
`ConnectBlock` adds each fee before `CheckInputs` checks it (1974–1978).
The block's fees have no `MoneyRange` check before the subsidy is added (1996).
For example, ten transactions that each pay `MAX_MONEY` overflow `int64`, which is undefined behaviour in C++.

The definitions use unbounded integers and check each accumulation against the `int64` range.
Every supplied coin value must lie in [0, `MAX_MONEY`], or the request gets an adapter error.
In a replay, a block whose accumulation leaves the range gets the error `outOfDomain`.
The comparator then ends the range before that block on both sides.

The theorem `connect_fits` shows when Core's sums stay in range.
It has two hypotheses.
Every coin value lies in [0, `MAX_MONEY`].
The sum of the coins spent by all input occurrences, plus `MAX_MONEY` and the subsidy, is below `2^63`.

Each occurrence is valued against the coin set just before its transaction, so coins created earlier in the block count.
The bound covers rejected attempts too.
Real blocks are far inside it. The total supply is not: about 1.5 × 10^19 koinu, above `2^63`. So chain-level statements use unbounded integers.

## 4. Stage 0010a: block checks without coins

**Scope.**

- A block reader for the full header and the transactions, which accepts witness serialization.
- `CheckTransaction`, `CheckBlock` with both flags, `ContextualCheckBlock`, the subsidy and the script flags.
- Legacy sigop counting (475–485, `script.cpp:156–177`). It counts every `scriptSig`, coinbase included, and every output script, in inaccurate mode. `CHECKMULTISIG` counts 20, and parsing stops at the first malformed opcode.
- `VersionBitsState` for CSV and SegWit, with the shortcut below.

**Operations.** `tx.check`, `block.check` with `fCheckPOW` and `fCheckMerkleRoot`, `block.contextual_check_body`, and `block.subsidy`.
`block.subsidy` takes a batch of (height, previous hash) pairs.
Each operation compares the verdict, reject reason, DoS score and reject code.

**Version bits.**
Core aligns the predecessor to a period boundary with `GetAncestor`, then consults its cache (`versionbits.cpp:31–38`).
On a miss it reads the boundary's median time past and walks back one period at a time (44–47).
Below height 10,080 the aligned boundary is null, and the state is `DEFINED`.

Each request supplies the aligned boundary and its 10 predecessors, linked to the predecessor with skip pointers as the harness builds them today.
Three cases follow:

1. Boundary median time before the CSV start (2016-05-01, about height 1.2 million): both states are `DEFINED` on the first step. The request needs no more history.
2. Boundary median time at or after the CSV timeout (2017-05-01): the harness installs `FAILED` for both deployments. It does so at that boundary, for this request only. That time is past the SegWit start, so the shortcut also holds for SegWit. `DEFINED`, `STARTED` and `FAILED` all go to `FAILED` at the timeout (`versionbits.cpp:56–99`). So, given `csv_never_lockedIn`, `FAILED` is Core's own result for every history that the header checks accept.
3. Between the two, about heights 1.2 million to 1.72 million, Core counts the versions of every block in each period. A request there needs about 525,000 dense entries, so CI compares no blocks in this window.

The Lean definition takes the same three cases.
The theorem `versionBits_shortcut` shows that cases 1 and 2 equal the full walk, under the hypothesis of `csv_never_lockedIn`.
One run outside CI compares Lean's full walk with Core's on the real header chain through the window.
SOUNDNESS.md records the seed as a harness input, with this argument.

**Reachable reject reasons.**

- `CheckTransaction`: `bad-txns-vin-empty`, `-vout-empty`, `-oversize`, `-vout-negative`, `-vout-toolarge`, `-txouttotal-toolarge`, `-inputs-duplicate`, `-prevout-null`, and `bad-cb-length`.
- `CheckBlock`: `high-hash`, which covers every proof-of-work and AuxPoW failure (2927–2934), `bad-txnmrklroot`, `bad-txns-duplicate`, `bad-blk-length`, `bad-cb-missing`, `bad-cb-multiple` and `bad-blk-sigops`.
- `ContextualCheckBlock`: `bad-txns-nonfinal`, `bad-cb-height`, `unexpected-witness`, and `bad-blk-weight` when the operation runs alone. `ContextualCheckBlock` has no base-size check, so a block over 1,000,000 base bytes reaches `bad-blk-weight` (3198).
- Unreachable on mainnet: `bad-witness-nonce-size` and `bad-witness-merkle-match`, because SegWit cannot activate. In `block.validate`, `bad-blk-weight` is unreachable too: without witness data its bound equals the `CheckBlock` size bound (2971), and with witness data `unexpected-witness` comes first.

**Exit conditions.**

1. `block.check` and `block.contextual_check_body` agree with Core on two ranges. One is every block from genesis to 10,000. The other is the 1,000 most recent blocks at fetch time. They also agree on the blocks at and next to the rule changes: 144,999 and 145,000, 371,337 (AuxPoW start), 599,999 and 600,000, 1,034,383, and 3,464,751.
2. They agree on mutations of those blocks, at least one for each reachable reason above. The sigop cases include multisig, malformed scripts and the exact limit.
3. Each unreachable reason has a theorem or a cited argument.
4. `block.subsidy` agrees at every height from 1 to 145,000 on the real previous hashes. Headers suffice, from the Electrum source of the existing header fixtures.
5. Outside CI, `block.subsidy` agrees on all 2^28 seeds for both random ranges. Every case must succeed, and the run records the largest number of redraws.

**Theorem targets.**

- `csv_never_lockedIn`: take a header chain from the mainnet genesis in which every header passed `checkBlockHeader` and `contextualCheckBlockHeader`. On it, `VersionBitsState` for CSV and SegWit is never `LOCKED_IN` or `ACTIVE`. An arbitrary supplied index does not meet this hypothesis.
- `versionBits_shortcut`, above.
- `uniformInt_preimages`: in Boost's draw, `bucket` is 4,294 for `maxReward` 999,999 and 8,589 for 499,999. Every value in [1, `maxReward`] has exactly `bucket` accepted 32-bit words, and every rejected word is at least `maxReward × bucket`. A modulo draw or a wrong bucket would fail it.
- A witness by kernel computation: the 10,000th output of MT19937 from its default seed is 4123659995.

The draw has no easy termination proof, so the definition takes fuel and returns `fuelExhausted` when the fuel runs out.
Exit condition 5 shows that the fuel suffices on every seed.

## 5. Stage 0010b: connecting blocks

**Scope.**

- A coin set: outpoint to value, script, height and coinbase flag, with Core's pruning.
- `CheckTxInputs`, BIP30, and the coinbase limit.
- P2SH sigops (489–500, `script.cpp:180–201`): non-coinbase inputs only. The last push of a push-only `scriptSig` is counted accurately, and a malformed or non-push `scriptSig` counts zero. The limit applies to legacy and P2SH sigops together.
- Script verification of every input through `script.verify_legacy`, with Core's failure classification.
- `ConnectBlock`, and `block.validate`, which follows Core's order for a new block: `CheckBlockHeader`, `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock` (3224–3239, 3329–3330). `ConnectBlock` alone repeats no contextual check (1791–1803). For the genesis hash, `block.validate` skips the header checks (3212) and adds no coins.

Reachable reasons beyond 0010a: `bad-txns-BIP30`, `-inputs-missingorspent`, `-premature-spend-of-coinbase`, `-inputvalues-outofrange`, `-in-belowout`, `bad-blk-sigops`, `bad-cb-amount`, and the two script classifications.
Unreachable: `bad-txns-fee-negative` and `-fee-outofrange`, after the two input-value checks. Also the sequence-lock `bad-txns-nonfinal`, because CSV is inactive.

**Harness.**
The harness runs no script-check threads and leaves `hashAssumeValid` null, so `ConnectBlock` checks every script (1827–1849, 1924).
Each attempt runs `ConnectBlock` with `fJustCheck` true on a fresh `CCoinsViewCache` over the carried set.
On success the harness commits the coins and sets the best block itself, because `fJustCheck` returns before `SetBestBlock` (2008, 2035).
On rejection it discards the view, because `UpdateCoins` runs before the coinbase check (1988, 1996).
The harness keeps the index entry of the view's best block, which `CheckInputs` reads for the spending height (1407–1411).

With `fJustCheck`, `ConnectBlock` calls `CheckBlock` with both flags false (1804).
That skips the Merkle root and all of `CheckAuxPowProofOfWork`, including the chain-ID and AuxPoW checks.
So real blocks run `block.validate` with proof of work on.
Mutations run it with proof of work off, which bypasses those checks on purpose.

**Replay.**
One request carries a range of blocks, and each side carries its coin set through the range.
Agreement requires the same verdict and reason at every block.
It also requires the same digest of each block's spent and created coins.
Every 1,000 blocks and at the end, it requires the same digest of the whole set.

**Ranges.**
The two ranges test different things.
Genesis to 10,000 needs no supplied coins, so each side builds the whole coin set itself, and it covers the random-reward era.
The recent range tests the rules and transaction patterns of the chain today: AuxPoW, BIP34, DERSIG, CLTV and P2SH spends.

A range that does not start at genesis takes a partial coin set that answers every query the range makes.
That is every coin the range spends.
For each transaction ID that the range creates, it also holds the existing coins or a statement that there are none.
The request also supplies the ancestor hash at 1,034,383.
On mainnet BIP30 is never skipped (section 2), so the recent range states that every transaction ID it creates is absent.
Nothing authenticates that statement.
BIP34 supports it for the real chain: each coinbase from 1,034,383 contains its height, so a repeated ID needs a SHA-256d collision.

The fetch tool takes each spent coin from its funding transaction and checks the transaction against its ID.
It checks the coin's height with a Merkle branch to the pinned header chain.
That authenticates each coin as a real output.
It does not show that the coin was unspent at the start of the range, or that the absence statements are true.
So agreement on a recent range shows agreement on the supplied state, not on the historical coin set.

**Exit conditions.**

1. In CI, `block.validate` agrees with Core, digests included, on both ranges of 0010a. A recorded gate outside CI runs from genesis to 145,000, the whole random-reward era.
2. The fetch tool authenticates every coin of the recent range. Its checks fail on a planted wrong value, script or height.
3. Mutations agree, at least one for each reachable reason. They include:
   - a premature coinbase spend at each maturity value
   - a double spend within a block, and a spend of an output that the block creates later
   - a missing outpoint and a BIP30 collision
   - a DERSIG failure, which is classified non-mandatory
   - P2SH sigops with a malformed and a non-push `scriptSig`, and the combined limit
   - a coinbase that claims one koinu too much.

**Theorem target.** `connect_fits`, from section 3.

## 6. Stage 0010c: properties

The three targets assume a coin set whose values all lie in [0, `MAX_MONEY`], a successful subsidy, and the domain of section 3.

- `connect_spends_available`: suppose `connectBlock` accepts block `b` on coin set `s`. Then each non-coinbase input spends a coin present in the set just before its transaction, and that transaction removes the coin. Coins that the block created earlier count as present. This excludes the bug class of CVE-2018-17144. The statement is about coins as created, not about outpoints. With BIP30 skipped, a later transaction can recreate an outpoint, and the theorem does not exclude a spend of the new coin.
- `connect_value_bound`: under the same hypothesis, the total value of the new set is at most that of `s` plus the subsidy. Fees cancel. Pruned and overwritten coins have nonnegative values, so their removal only lowers the total.
- `chain_issuance_bound`: take a chain from the mainnet genesis that `connectBlock` accepts block by block, from the empty set. Genesis adds nothing. Then the total value of the set is at most the sum of the subsidies. The bound is an upper bound only. A miner may claim less, and pruned outputs leave the set.

## 7. Excluded

- Reorganization, and disk and undo state.
- `AcceptBlock` and `ActivateBestChain`, except their check order.
- The mempool and its policy, and P2P messages.
- Script-check threads and assumed-valid blocks.
- Testnet and regtest block rules.
- SegWit and CSV semantics, beyond proving them inactive.
- Downstream and DogeOS properties.

Each new definition gets a model read against Core in the pull request that adds it, recorded under `docs/reviews/`.

## 8. Decisions

**Date:** 2026-11-13. **Decision maker:** Maintainer.

| Number | Topic | Decision | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | Block source | The maintainer's mainnet node, which runs the signed v1.14.9 release, the pinned commit. The pinned header chain and the Merkle roots authenticate the blocks. Spent coins come from their funding transactions, authenticated as section 5 describes. | A public block API, checked the same way. | Accepted |
| 2 | Ranges and storage | Genesis to 10,000 and the 1,000 most recent blocks, in CI. Genesis to 10,000 is committed if small enough, measured in 0010a. Larger ranges are a GitHub release asset, fetched and checked against committed SHA-256 sums. | Genesis to 10,000 alone, which tests none of the rules after 2014. | Accepted |
| 3 | Version-bits seed | Install `FAILED` after the CSV timeout, justified by `csv_never_lockedIn` and `versionBits_shortcut` (section 4). | Dense history in each request, or no recent blocks in CI. | Accepted |
