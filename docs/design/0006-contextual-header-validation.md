# Contextual header validation

**Status:** Proposed. The open decisions of section 12 await a maintainer decision.
Implementation status will belong in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-06
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [architecture](../../ARCHITECTURE.md), [oracle contract](../oracle.md) and [design record 0004](0004-header-proof-of-work.md).

## 1. Purpose and boundary

This record sets the scope for an executable specification of Dogecoin Core's `ContextualCheckBlockHeader` [C1].
That function checks a block header against the chain that it extends, the node's adjusted time and the checkpoints that the node knows.
`AcceptBlockHeader` calls it after the proof-of-work check `CheckBlockHeader` and before it adds the header to the block index [C3].

DogeLib already specifies three parts of the function:

- The two version gates, `late-legacy-block` and `early-auxpow-block`, as `Block.checkVersion` with a caller-selected record (design record 0004, stage 4b).
- `GetNextWorkRequired` on a checked finite view of ancestors, as `Work.nextWorkRequired`, with parameter selection at the candidate height.
- `CheckBlockHeader`, as `Block.checkBlockHeader` (design record 0004, stage 4a).

The remaining checks are the comparison of `nBits` with the required work, the checkpoint check, the two time checks and the rejection of outdated versions.
No theorem or comparison covers them, and [SOUNDNESS.md](../../SOUNDNESS.md#version-gating) records that gap.
This record sets out how to close it.
The theorems in section 11 are targets, not implemented results.

DogeLib is a specification library for Dogecoin Core.
A property of an application or of DogeOS belongs in a downstream project, and this record proposes none.

The record excludes these subjects:

- `ContextualCheckBlock` and every other check of a full block: transaction finality, the coinbase height of BIP34, witness commitments and block weight [C13]. Section 4.8 gives the reason.
- The checks of `AcceptBlockHeader` that read node state: the duplicate test, the lookup of the previous block and the failed-ancestor walk [C3].
- Chain selection, chain work and the block-index state machine.
- The sources of time: the system clock and the peer offsets that `GetAdjustedTime` adds [C11].
- The choice of network by `Params()` and the command-line option `-checkpoints` [C12]. The specification takes both as explicit inputs.
- Implementation refinement and Rust extraction.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The line ranges identify the inspected source:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [validation.cpp, lines 3066–3119](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3066-L3119) | `ContextualCheckBlockHeader`. |
| C2 | [validation.cpp, lines 2927–2937](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2927-L2937) | `CheckBlockHeader`. |
| C3 | [validation.cpp, lines 3205–3267](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3205-L3267), [lines 3270–3286](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3270-L3286), [lines 3412–3423](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3412-L3423) | The callers: `AcceptBlockHeader`, `ProcessNewBlockHeaders` and `TestBlockValidity`. |
| C4 | [validation.cpp, lines 49–52 and 64–90](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L49-L90), [validation.h, line 144](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L144) | The Boost includes, the globals `mapBlockIndex`, `fCheckpointsEnabled` and `mempool`, and `DEFAULT_CHECKPOINTS_ENABLED`. |
| C5 | [validation.cpp, line 96](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L96), [lines 3368–3378](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3368-L3378) | `IsSuperMajority`: a declaration and a definition, with no caller. |
| C6 | [pow.cpp, lines 32–88](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pow.cpp#L32-L88), [dogecoin.cpp, lines 26–87](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp#L26-L87) | `GetNextWorkRequired`, `AllowDigishieldMinDifficultyForBlock` and `CalculateDogecoinNextWorkRequired`. |
| C7 | [chain.h, lines 274–298](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.h#L274-L298), [pureheader.h, lines 73–95](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.h#L73-L95), [lines 129–155](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.h#L129-L155) | `CBlockIndex::GetBlockTime`, `GetMedianTimePast`, and the header's `GetBlockTime`, `GetBaseVersion`, `IsAuxpow` and `IsLegacy`. |
| C8 | [checkpoints.cpp, lines 18–30](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/checkpoints.cpp#L18-L30), [chainparams.h, lines 28–32 and 82](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.h#L28-L82) | `Checkpoints::GetLastCheckpoint` and the checkpoint map. |
| C9 | [chainparams.cpp, lines 84–87](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L84-L87), [lines 119–141](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L119-L141), [lines 180–205](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L180-L205), [lines 237–247](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L237-L247), [lines 276–306](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L276-L306), [lines 340–361](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L340-L361), [lines 388–391](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L388-L391), [lines 417–437](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L417-L437), [lines 461–464](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L461-L464), [lines 494–506](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L494-L506) | Per network: `BIP65Height` and `BIP66Height`, the testnet minimum-difficulty fields, the record tree, the checkpoint table, and `GetConsensus`. |
| C10 | [consensus/params.h, lines 43–53 and 79–88](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/params.h#L43-L88) | The majority fields, `BIP34Height`, `BIP65Height`, `BIP66Height`, `fAllowLegacyBlocks` and `nHeightEffective`. |
| C11 | [timedata.cpp, lines 34–37 and 70–85](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/timedata.cpp#L34-L85), [timedata.h, line 13](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/timedata.h#L13) | `GetAdjustedTime` and the bound on the peer offset. |
| C12 | [init.cpp, line 951](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/init.cpp#L951) | The option `-checkpoints`. |
| C13 | [validation.cpp, lines 3121–3203](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3121-L3203), [line 1877](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1877) | `ContextualCheckBlock`, and the BIP30 shortcut of `ConnectBlock` that reads `BIP34Height`. |

The registry already records seven of these files: `validation.cpp` (D33), `pow.cpp` (D17), `dogecoin.cpp` (D6), `chain.h` (D18), `pureheader.h` (D10), `chainparams.cpp` (D14) and `consensus/params.h` (D15).
An implementation lane adds an identifier for each other file that it uses, from D64 on, without a change to any pin.
The findings come from source inspection, without a Core comparison run.

## 3. Inventory of the function

`ContextualCheckBlockHeader(block, state, pindexPrev, nAdjustedTime)` computes the candidate height as `pindexPrev->nHeight + 1`, or zero for a null `pindexPrev` [C1, line 3068].
It selects the record `Params().GetConsensus(nHeight)` [C1, lines 3069–3070].
Then it runs seven checks in this order, and it returns at the first failure:

| Order | Lines of C1 | Check | Reject reason | Status in DogeLib |
| --- | --- | --- | --- | --- |
| 1 | 3073–3077 | Without `fAllowLegacyBlocks`, the header must not be legacy. | `late-legacy-block` | Specified: `checkVersion` |
| 2 | 3082–3086 | With `fAllowLegacyBlocks`, the AuxPoW flag must be clear. | `early-auxpow-block` | Specified: `checkVersion` |
| 3 | 3089–3090 | `nBits` must equal `GetNextWorkRequired(pindexPrev, &block, record)`. | `bad-diffbits` | The required value is specified as `Work.nextWorkRequired`. The comparison is not. |
| 4 | 3093–3100 | If checkpoints are enabled and the node knows a checkpoint, the candidate height must not be below its height. | `bad-fork-prior-to-checkpoint` | Not specified |
| 5 | 3103–3104 | The header time must be greater than the median time past of `pindexPrev`. | `time-too-old` | Not specified |
| 6 | 3107–3108 | The header time must be at most `nAdjustedTime + 2 * 60 * 60`. | `time-too-new` | Not specified |
| 7 | 3113–3116 | The base version must be at least 3 from `BIP66Height`, and at least 4 from `BIP65Height`. | `bad-version(0x…)` | Not specified |

The function reads no field of the AuxPoW payload.
It reads `nVersion`, `nTime` and `nBits` of the header, and the height, time and `nBits` of ancestors.
The handoff for this record listed four subjects that the source inspection settles in this way:

- **Future time.** At the pin, `CheckBlockHeader` contains only the proof-of-work check [C2]. The future-time check is check 6 of `ContextualCheckBlockHeader`.
- **Outdated versions.** `IsSuperMajority` has a declaration and a definition, but no caller [C5]. Check 7 is the only rejection of outdated versions, and it uses fixed heights.
- **BIP34.** Check 7 does not read `BIP34Height`. Among the consensus checks, `ContextualCheckBlock` reads it for the coinbase height, and `ConnectBlock` reads it for the BIP30 shortcut [C13].
- **Checkpoints.** `GetLastCheckpoint` searches the whole block index, not the candidate's chain [C8]. Section 4.3 gives the consequences.

## 4. Core behaviour that the specification must preserve

Each item comes from the pinned source.
The specification must keep each behaviour, and a theorem or a known answer must pin it.

### 4.1 Height, record and domain

1. Both callers in C3 pass a non-null `pindexPrev`.
   `AcceptBlockHeader` skips every check for the genesis hash, and `TestBlockValidity` asserts a tip [C3].
   Check 5 dereferences `pindexPrev` without a null test [C1, line 3103].
   So the specification requires a predecessor, and its domain excludes the genesis header.
2. The record comes from the candidate height, not from the predecessor's height [C1, line 3070].
   `Work.nextWorkRequired` already selects its parameters in this way.
3. Each network copies its base record into the later records [C9, lines 126, 134, 282, 291, 297, 425 and 430].
   So every record of a network has the same `BIP65Height` and `BIP66Height`.
   The checkpoint table belongs to `CChainParams`, not to a consensus record [C8].

### 4.2 Required work (check 3)

4. The check compares two 32-bit compact values for equality [C1, line 3089].
   It does not decode either value.
   So a compact value that encodes the same target in another form fails the check.
5. `GetNextWorkRequired` receives the candidate header, and reads its time for the minimum-difficulty rules of testnet and regtest [C6].
   On testnet, the two rules start at different heights (section 9.2).
   So `nTime` can change the expected `nBits`, as well as the result of checks 5 and 6.
6. `GetNextWorkRequired` asserts when a retarget ancestor is absent [C6, pow.cpp lines 83–85].
   A node always has the full chain, so the assertion does not fail in Core.
   A finite view in the specification can lack that ancestor, and `Work.nextWorkRequired` then returns the adapter error `missingAncestor`.

### 4.3 Checkpoints (check 4)

7. The global `fCheckpointsEnabled` is true by default, and `-checkpoints=0` sets it false [C4, C12].
8. `GetLastCheckpoint` walks the checkpoint table from the greatest height down [C8].
   It returns the block-index entry of the first checkpoint hash that `mapBlockIndex` contains.
   That entry can be on any branch, and its validity status is not read.
9. The check rejects a candidate height strictly below the height of that entry [C1, line 3098].
   A candidate at the checkpoint height passes check 4, even if it is a different block.
10. The result therefore depends on node state that the candidate's chain does not determine.
    The specification takes that state as an explicit input (section 6).
11. Mainnet has 23 checkpoints, from height 0 to 5,050,000 [C9, lines 180–205].
    Testnet has 19, from height 0 to 5,900,000 [C9, lines 340–361].
    Regtest has only the genesis block [C9, lines 461–464].

### 4.4 Median time past (check 5)

12. `GetMedianTimePast` collects at most 11 times: that of `pindexPrev` and those of up to ten predecessors [C7, chain.h lines 284–298].
    It stops early at genesis.
13. It sorts the collected times and returns the element at index `count / 2`.
    An even count occurs only for a predecessor below height 10, and then that element is the upper median.
14. The times are `int64_t` values widened from `uint32_t` [C7, chain.h lines 274–277].
    The header time is widened in the same way [C7, pureheader.h lines 73–76].
15. A header whose time equals the median fails: the comparison is `<=` [C1, line 3103].
16. Core's view has all predecessors, so the walk never stops early above genesis.
    A finite view in the specification must therefore hold `min(11, h + 1)` entries for a predecessor at height `h`.
    In Core's function, a shorter view gives a different median, not an error.
    So the specification must reject a shorter view as an adapter error.

### 4.5 Future time (check 6)

17. `nAdjustedTime` is a parameter of the function [C1, line 3066].
    The callers pass `GetAdjustedTime()`, the system time plus a peer offset [C3, C11].
    By default, the offset is at most 70 minutes in either direction [C11, timedata.h line 13].
    The specification takes the adjusted time as an explicit `int64_t` input and does not model its source.
18. The bound is `nAdjustedTime + 7200` in signed 64-bit arithmetic [C1, line 3107].
    The sum overflows only for an adjusted time above `INT64_MAX − 7200`, which is undefined behaviour in C++.
    So Core's agreement domain includes only adjusted times up to that bound.
    The specification returns an adapter error above the bound, and the oracle refuses those values (decision 9).
    The check accepts a header time equal to the bound.

### 4.6 Outdated versions (check 7)

19. `GetBaseVersion` is `nVersion % 256` with C++ signed remainder [C7, pureheader.h lines 88–95].
    A negative version therefore has a base version of zero or less, and fails both thresholds once they apply.
    The AuxPoW flag never changes the base version, because it never changes the sign of `nVersion`.
    A chain ID that changes bit 31 changes the sign.
    The base version then changes unless the low byte is zero.
    For example, `0x00000003` has base version 3, and `0x80000003` has base version −253.
    `0x00000000` and `0x80000000` both have base version zero.
    Other changes of the chain ID keep the base version.
20. The thresholds use `>=` on the candidate height [C1, lines 3113–3114]:

    | Network | `BIP66Height` (base version at least 3) | `BIP65Height` (base version at least 4) |
    | --- | --- | --- |
    | Mainnet | 1,034,383 | 3,464,751 |
    | Testnet | 708,658 | 1,854,705 |
    | Regtest | 1251 | 1351 |

    The values come from C9, lines 86–87, 246–247 and 390–391.
21. The source comment at mainnet `BIP66Height` calls that height "the last block that could be v2" [C9, line 87].
    The code rejects base version 2 at that height.
    The specification follows the code.
22. The reject reason contains the base version as eight hexadecimal digits, `bad-version(0x%08x)` [C1, line 3115].
    The rejection code is `REJECT_OBSOLETE`, not `REJECT_INVALID`.

### 4.7 Order and reject reasons

23. Checks 5, 6 and 7 use `state.Invalid` without a denial-of-service score, and checks 1 to 4 use `state.DoS(100, …)` [C1].
    The score belongs to peer management, which this record excludes.
24. The reject reason identifies the first failing check.
    So a comparison of reject reasons pins the order of section 3, and a comparison of Boolean results does not.

### 4.8 Why `ContextualCheckBlock` stays outside

`ContextualCheckBlock` reads the transactions of the block [C13].
It needs transaction finality with `IsFinalTx`, the versionbits state of the CSV and segwit deployments, the witness commitment and the block weight.
Each of those needs a model of full blocks and of deployment state that DogeLib does not have.
The header check needs none of them.
A later record can scope `ContextualCheckBlock` with the other checks of a full block.

## 5. The chain context

The function needs four kinds of context:

| Context | Core source | Proposed model |
| --- | --- | --- |
| Predecessor and ancestors | `pindexPrev` and its `pprev` links | `Work.BlockIndex` entries, newest first: `nHeight`, `nTime` and `nBits` |
| Adjusted time | `nAdjustedTime`, from `GetAdjustedTime()` | An explicit `Int64` input |
| Known checkpoints | `mapBlockIndex` through `GetLastCheckpoint`, and `fCheckpointsEnabled` | An explicit input (section 6.2) |
| Network | `Params()` | An explicit `WorkNetwork` |

The existing view fits without a change to `Work.BlockIndex`.
No check reads an ancestor's version, because `IsSuperMajority` has no caller [C5].
No check reads an ancestor's hash, because `AcceptBlockHeader` finds `pindexPrev` by hash before the call [C3].
So the specification cannot check that the view is the chain of the header's `hashPrevBlock`.
The caller asserts that link, as Core's lookup does.

`validateWorkView` checks heights and links, but it accepts a view that stops above genesis.
Check 5 adds a depth requirement: the view must hold `min(11, h + 1)` entries for a predecessor at height `h` (item 16).
Check 3 keeps the depth requirement of `Work.nextWorkRequired`, which reports `missingAncestor` when it needs a missing entry.
A view that reaches height 0 satisfies both requirements.

## 6. Options

### 6.1 How the chain enters

**Option A: an explicit finite view.**
The function takes the existing newest-first list of `Work.BlockIndex`, and returns an adapter error when the list is too short.
The list matches `work.next` in the oracle and the linked `CBlockIndex` objects that the Core harness already builds.
A downstream project with another chain representation supplies the first entries of its chain.
A prefix theorem (section 11) shows that more entries do not change the result.

**Option B: an abstract chain interface.**
The function takes a structure with an ancestor lookup by height, and laws for heights and links.
The interface is more general, but each instance must prove its laws.
The oracle and the harness still need a concrete list, and `Work.nextWorkRequired` would need a second form.

**Option C: a model of the block index.**
The function takes a map from hashes to entries with predecessor links and status flags, as `mapBlockIndex` does.
That model could also decide check 4 and the lookup of `pindexPrev`.
It brings node state into the specification, which section 1 excludes.

**Recommendation: option A.**
It reuses the checked view and its theorems, and it keeps every input visible in an oracle request.
The prefix theorem gives the bridge that option B would give, without a second interface.

### 6.2 How the checkpoint state enters

Check 4 reads two things that the chain does not determine: the option `fCheckpointsEnabled`, and the set of checkpoint hashes in `mapBlockIndex`.
Three forms are possible:

- **Form 1: the height of the last known checkpoint**, as an optional natural number. The caller computes it, and `none` means that checkpoints are disabled or that no checkpoint is known.
- **Form 2: the set of known checkpoint heights and the enabled flag.** The specification adds `lastCheckpoint`, which follows `GetLastCheckpoint` over the network's table [C8, C9]. Form 1 is then a derived value.
- **Form 3: exclude check 4**, as node policy rather than consensus.

**Recommendation: form 2.**
It specifies the table and the search that Core runs, and the harness can call Core's `GetLastCheckpoint` (section 8.2).
The core predicate still takes the derived height, so a theorem can state check 4 as one comparison.
The record does not recommend form 3, because check 4 is part of the function that `AcceptBlockHeader` calls, and it is enabled by default.

The block-index entry of a checkpoint hash has the height of that block.
The specification uses the table key as that height.
The two agree when the hash identifies the checkpoint block, which is the hash commitment assumption of [SOUNDNESS.md](../../SOUNDNESS.md).

## 7. Contract for implementation

### 7.1 The predicate

The central operation is a function of a pure header, an explicit context and a network:

```text
contextualCheckBlockHeader
  (network : WorkNetwork) (header : PureBlockHeader) (view : List BlockIndex)
  (adjustedTime : Int64) (lastCheckpointHeight : Option Nat)
  : Except ContextualHeaderError Unit
```

The names are proposals.
The function returns `.ok ()` exactly when Core's function returns `true`, on the domain of section 4.1 and section 5.
That domain also requires an adjusted time of at most `INT64_MAX − 7200` (item 18).
`ContextualHeaderError` has two kinds of constructor:

- One rejection for each check of section 3, in source order, each with Core's reject reason.
  The `bad-version` reason carries the base version.
- Adapter errors for an input outside the domain, which are not Core verdicts.
  The inputs are an empty view, a view that `validateWorkView` rejects, a view too short for the median, and each `NextWorkError` of check 3.
  An adjusted time above `INT64_MAX − 7200` is also an adapter error.

The function composes existing definitions without a change to them:

- `checkVersion` with the record that `GetConsensus` selects for the candidate height. Stage 2 adds that selection.
- `Work.nextWorkRequired` on the same view, with the candidate time.
- Comparisons of `nTime` with the median, the adjusted time and the thresholds, in `Int` arithmetic, which is exact for these widened values.

It takes a pure header, because no check reads the payload.
A second function `lastCheckpoint` maps the network table, a set of known heights and the enabled flag to `lastCheckpointHeight`.

### 7.2 Placement

`medianTimePast` acts on `Work.BlockIndex` views and belongs to the `Work` layer.
The composition reads `PureBlockHeader` and `checkVersion`, so it belongs to the `Block` layer.
[ARCHITECTURE.md](../../ARCHITECTURE.md#layers) lets `Block` import `Work`.
The lane that adds the composition updates the `Block` row of ARCHITECTURE.md.

## 8. Oracle and Core harness

### 8.1 Operation

The record proposes one additional operation, `block.contextual_check`:

| Field | Content |
| --- | --- |
| `bytes_hex` | Exactly 80 bytes of a pure header. |
| `network` | `mainnet`, `testnet` or `regtest`. |
| `chain` | The newest-first view of `work.next`: objects with `height`, `time` and `bits`. |
| `adjusted_time` | A signed 64-bit integer, at most `INT64_MAX − 7200` (item 18). |
| `checkpoints_enabled` | Boolean. |
| `known_checkpoints` | Heights from the network's checkpoint table whose hashes the node knows. |

The response has `valid`, `reject_reason`, and a Lean-only `diagnostic`.
`reject_reason` is null on acceptance and Core's reject reason otherwise.
The comparator compares `valid` and `reject_reason`, and excludes `diagnostic`.
Under the [development policy](../oracle.md#format-stability), the stage 4 pull request settles the field names under ordinary review.

A height in `known_checkpoints` outside the table is a request error.
A view outside the domain gives the existing `work_view` error, or an additional reason for a view too short for the median.

### 8.2 The Core side

`ContextualCheckBlockHeader` is in `validation.cpp`, in `libdogecoin_server.a`.
That object defines globals with constructors, such as `mempool`, and includes Boost Filesystem and Boost Thread [C4].
The harness links no Boost library and does not compile `validation.cpp` ([docs/oracle.md](../oracle.md#the-core-harness)).
Two approaches are possible:

- **H1: link Core's function.** The harness links `validation.cpp` and its dependencies, fills `mapBlockIndex`, sets `fCheckpointsEnabled` and calls `ContextualCheckBlockHeader` directly.
  The comparison then runs Core's function itself.
  The build adds Boost libraries, LevelDB and the server library, and this record does not measure that cost.
- **H2: transcribe the body and call Core's helpers.** The harness transcribes the 54 lines of C1, as it does for the two branches of `block.check_version`.
  Each step calls Core's own code: `GetConsensus`, `IsLegacy`, `IsAuxpow`, `GetNextWorkRequired`, `CBlockIndex::GetMedianTimePast`, `GetBaseVersion` and `Checkpoints::GetLastCheckpoint`.
  The harness defines its own `mapBlockIndex` and `fCheckpointsEnabled`, and links `checkpoints.cpp` in addition to the objects of `work.next`.
  This record does not test that build.

**Recommendation: H2, with a check of the transcription.**
H2 keeps the current build, and Core's code computes every value that a check compares.
A transcription mistake could make the harness agree with a wrong specification.

Two measures limit that risk.
Independent review compares the transcription with C1 line by line.
The known answers of section 9 take their expectations from hand derivation, not from the harness.
A later lane can still add H1 if the maintainer wants Core's function itself in the loop.

The harness builds the chain as `work.next` does: linked `CBlockIndex` objects with `pprev`, `nHeight`, `nTime` and `nBits`.
For each known checkpoint height, it adds an entry to its `mapBlockIndex` under the table hash, with that height.
It refuses a request whose view is too short, before it calls Core, because Core would compute a different median from a short view (item 16).

## 9. Evidence plan

### 9.1 Existing fixtures

`tests/work/mainnet-headers` holds the 312 headers at heights 144719 to 145030, with their predecessor links checked.
They give real contexts for every candidate from height 144730, with at least 11 predecessors in the view.
They cover check 3 across the first DigiShield height 145000.
They also cover the retarget at candidate height 144960, which needs the first header as its ancestor.
They do not reach AuxPoW activation, either version threshold, the minimum-difficulty rules of testnet, or candidate heights below 11.

### 9.2 Additional fixtures

Checks 1, 2 and 7 need real headers near their activation heights.
The proposed mainnet ranges are pure 80-byte headers, each with at least 11 predecessors:

| Range | What it pins | Anchor in the pinned source |
| --- | --- | --- |
| Heights 0 to 12 | The median of fewer than 11 entries, with even and odd counts | Checkpoint 0, the genesis hash [C9] |
| About 371,320 to 371,340 | AuxPoW activation: checks 1 and 2 with real versions, and check 3 under DigiShield | Checkpoint 371337 [C9] |
| About 1,034,370 to 1,034,390 | `BIP66Height` on real versions | The hash in the comment on `BIP66Height` [C9, line 87] |
| About 3,464,739 to 3,464,760 | `BIP65Height` on real versions | The hash in the comment on `BIP65Height` [C9, line 86] |

The fixtures need only the pure header, because the function reads no payload.
The Electrum server of the existing fixtures is one possible source.
The lane must confirm that the source returns the 80-byte pure header at AuxPoW heights, and record the source, the command and the fetch date.
An independent Python check confirms the predecessor links and the anchor hash of each range, before the fixture enters the repository.

Testnet and regtest need synthetic contexts.
On testnet, two minimum-difficulty rules apply at different candidate heights:

- The rule between retargets applies below candidate height 145000, at heights that are not retargets [C6, pow.cpp lines 54–62, and C9, line 237].
  From candidate 145000, the selected record turns it off [C9, line 287].
  From predecessor height 145000, every block is a retarget [C6, pow.cpp line 50].
- The rule for every block, `AllowDigishieldMinDifficultyForBlock`, needs a predecessor at height 157500 or more [C6, dogecoin.cpp lines 33–35].
  So it starts at candidate 157501, although the record that permits it applies from candidate 157500 [C9, lines 291–295].
  At candidate 157500, the interval of one also skips the rule between retargets, so no minimum-difficulty rule applies.

The fixtures must include candidates at 157500 and 157501, each with a time on both sides of the delay.
AuxPoW activates at 158100.
Real testnet headers are optional evidence, and section 12 lists the choice.

### 9.3 Expected values

For real headers, chain acceptance supplies the expected result of checks 1, 2, 3, 5 and 7: each passes.
The adjusted time and the known checkpoints are not chain data.
The fixture chooses them, records them, and derives the results of checks 4 and 6 by hand from C1.
For example, an adjusted time equal to the header time accepts, and an adjusted time 7201 seconds earlier rejects with `time-too-new`.

A value that DogeLib computes is never an expected value for DogeLib.
The Core harness gives comparison evidence, not known answers.

### 9.4 Mutations

Each rejection needs a mutation on each side of its boundary:

| Check | Mutations |
| --- | --- |
| 1, 2 | A legacy version at the activation height, and the AuxPoW flag one height before it, on each network. |
| 3 | `nBits` plus and minus one. Another compact encoding of the same target. On testnet, a candidate time one second on each side of the delay that permits minimum difficulty, at candidates 157500 and 157501 and below 145000. |
| 4 | A last checkpoint at the candidate height (accept) and one above it (reject). No known checkpoint, and checkpoints disabled with a higher known checkpoint. |
| 5 | A header time equal to the median (reject) and one second later (accept). Ancestor times out of order, so that the median differs from the time of the 6th entry. Views of 1 to 11 entries near genesis. |
| 6 | A header time equal to the adjusted time plus 7200 (accept) and one second later (reject). A negative adjusted time. |
| 7 | Base versions 2 and 3 at `BIP66Height − 1` and `BIP66Height`, and 3 and 4 at `BIP65Height − 1` and `BIP65Height`. A negative version. AuxPoW versions whose base version is below the threshold. The pair `0x00000003` and `0x80000003` at `BIP66Height`, which differ only in the chain ID and give base versions 3 and −253. |
| Order | Headers that fail two checks, so that the reject reason pins the first failure. |

The Core comparison adds seeded mutations of `nVersion`, `nTime`, `nBits`, the adjusted time and the known checkpoints.
Any mismatch becomes a minimized regression case before an agreement claim.

## 10. Stages and exit conditions

### Stage 1: median time past

The stage adds `Work.medianTimePast` on a checked view, with the depth requirement of item 16.
It sorts with `List.mergeSort` from Lean core, which has the permutation and sortedness lemmas in `Init.Data.List.Sort`.

The stage exits with these results:

- The median characterization of section 11, and the prefix theorem for the median.
- Known answers from the mainnet range at heights 0 to 12, and from the existing 312 headers.
- Hand-derived cases for even counts and for times out of order.

### Stage 2: parameters by height

The stage adds the per-network projection of `fAllowLegacyBlocks`, `BIP65Height` and `BIP66Height`, and the checkpoint tables.
It reuses the generic `ParamsTree` and `GetConsensus` search of `Block.ProofOfWork`.

The stage exits with these results:

- Per network, a theorem that gives `fAllowLegacyBlocks` for every height: true below the activation height and false from it.
- Per network, a theorem that every record has the same `BIP65Height` and `BIP66Height` (item 3).
- The `lastCheckpoint` characterization of section 11.

### Stage 3: the composition

The stage adds `contextualCheckBlockHeader` and its error type (section 7).

The stage exits with these results:

- The characterization theorems of section 11, one for acceptance and one for each rejection.
- Known answers through the compiled code for the fixtures and mutations of section 9.

### Stage 4: oracle and Core comparison

The stage adds `block.contextual_check` to the oracle and to the Core harness (section 8), with fixtures and comparator self-tests.

The stage exits with reproducible differential runs that record both revisions, the selected cases and the random seeds.
The documentation in [docs/oracle.md](../oracle.md), COVERAGE.md and SOUNDNESS.md changes in the same pull request.

## 11. Theorem targets

The names below are proposals.
Each theorem states its domain and hypotheses in its doc comment.
`Int` comparisons widen `UInt32` times exactly.

| Target | Statement |
| --- | --- |
| `medianTimePast_eq` | Let `h` be the height of the first entry and `k = min(11, h + 1)`. For a checked view of at least `k` entries, the median is the element at index `k / 2` of the sorted first `k` times. |
| `medianTimePast_mem`, `_bounds` | The median is the time of one of the first `k` entries, and it lies between their least and greatest times. |
| `medianTimePast_congr_prefix` | Two checked views that agree on their first `k` entries give the same median. |
| `lastCheckpoint_eq` | With checkpoints enabled, the result is the greatest table height in the known set, or `none` if the set has no table height. With checkpoints disabled, the result is `none`. |
| `allowLegacyBlocks_getConsensus` | Per network, the selected `fAllowLegacyBlocks` is false exactly from height 371,337 on mainnet, 158,100 on testnet and 20 on regtest. |
| `contextualCheck_eq_ok_iff` | On the domain, the function accepts exactly when all seven conditions of section 3 hold, each stated over the inputs. |
| `contextualCheck_eq_error_iff` | For each rejection, the function returns it exactly when its condition fails and the conditions of all earlier checks hold. |
| `contextualCheck_congr_header` | The result depends on the header only through `nVersion`, `nTime` and `nBits`. |
| `contextualCheck_adjustedTime_mono` | If the function accepts with one adjusted time, it accepts with every greater adjusted time up to `INT64_MAX − 7200`. |
| `contextualCheck_no_checkpoint` | With `lastCheckpointHeight = none`, check 4 never rejects. |
| `contextualCheck_congr_prefix` | Two checked views that agree on their first `max(11, d)` entries give the same result, where `d` is the depth that `nextWorkRequired` reads. |
| `contextualCheck_complete` | On a checked view that reaches height 0, with an adjusted time of at most `INT64_MAX − 7200`, the function returns no adapter error for any network. |
| `badVersion_iff` | Let `b` be the signed remainder of `nVersion` by 256. Check 7 rejects exactly when `b < 3` from `BIP66Height`, or `b < 4` from `BIP65Height`. |

The record leaves the exact statement of the depth `d` to stage 3.
It is at most the retarget lookback or the recovery walk of `getNextWorkRequiredFromView`.
No target assumes collision resistance or another cryptographic property.

The theorems establish the behaviour of DogeLib's definitions.
A claim of agreement with Core needs the source review of [SOUNDNESS.md](../../SOUNDNESS.md) and the comparison of stage 4.
The adjusted time, the known checkpoints and the link from the header to the view are inputs that the caller supplies.
No theorem says that a caller supplies the values that a node would compute.
Stage 3 records each of these inputs as an execution boundary in SOUNDNESS.md.
The record adds no axiom and no trust assumption.

## 12. Open decisions

Each proposal below needs a maintainer decision before stage 1 starts:

| Number | Topic | Proposal | Status |
| --- | --- | --- | --- |
| 1 | Chain context | Option A: the existing finite view of `Work.BlockIndex`, newest first, with adapter errors for short views (section 6.1). | Open |
| 2 | Checkpoint state | Form 2: the set of known checkpoint heights and the enabled flag, with `lastCheckpoint` over the network's table. The predicate takes the derived height (section 6.2). | Open |
| 3 | Core harness | H2: a transcription of C1 that calls Core's helpers, with line-by-line review. H1, which links `validation.cpp`, stays a later option (section 8.2). | Open |
| 4 | Comparison | Compare `valid` and Core's `reject_reason`, so that the comparison pins the order of the checks. Exclude the Lean diagnostic (section 8.1). | Open |
| 5 | Fixtures | Fetch the four mainnet ranges of section 9.2 as pure headers, anchored to hashes in the pinned source. Use synthetic contexts for testnet and regtest, without real testnet headers. | Open |
| 6 | `ContextualCheckBlock` | Exclude it from this scope (section 4.8). | Open |
| 7 | Header sequence | Exclude a composition that checks a sequence of headers with `CheckBlockHeader`, the contextual check and the predecessor hash. A later record can propose it. | Open |
| 8 | Rust work | Implementation refinement and Rust extraction stay outside this scope. | Open |
| 9 | Adjusted time above `INT64_MAX − 7200` | An adapter error in the specification and a request error in the oracle, because Core's addition overflows there. The alternative is an `Int` extension outside Core's domain, which no comparison can check (item 18). | Open |

## 13. Remaining risks

| Risk | Mitigation |
| --- | --- |
| A short view gives a different median in Core, not an error, so a truncated fixture passes with a wrong expectation. | The depth requirement of item 16 in the specification, and a harness refusal of short views before the Core call. |
| The transcription of H2 differs from C1, so the harness and the specification agree on a wrong rule. | Line-by-line review, hand-derived known answers and Core's helpers for every compared value. Decision 3 keeps H1 available. |
| The specification decodes `nBits` and compares targets instead of compact values. | The mutation with another encoding of the same target (section 9.4), and a characterization theorem stated over the 32-bit value. |
| The specification selects the record at the predecessor's height. | Item 2, `allowLegacyBlocks_getConsensus`, and mutations at each activation height. |
| The upper median for even counts becomes a lower median or a mean. | `medianTimePast_eq` with index `k / 2`, and known answers at heights 1 to 10. |
| A checkpoint test reads the candidate's chain instead of the known set, or uses `<=`. | `lastCheckpoint_eq`, and the accept and reject mutations at the checkpoint height. |
| Overflow of the future-time bound. | The specification returns an adapter error and the oracle refuses adjusted times above `INT64_MAX − 7200` (decision 9). |
| The source comment on mainnet `BIP66Height` suggests that a version 2 block may occur at that height. | The specification follows the code (item 21), and the fixture at that height records the real version. |

There is no pin change, trust-policy exception or fixture-format change in this record.
Adoption of the scope does not establish any target theorem, and it does not authorize the merge of a later implementation.
