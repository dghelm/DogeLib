# Header-sequence validation

**Status:** Proposed.
Section 13 lists the proposals that wait for a maintainer decision.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-07
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [architecture](../../ARCHITECTURE.md), [oracle contract](../oracle.md), [design record 0004](0004-header-proof-of-work.md), [design record 0006](0006-contextual-header-validation.md) and [design record 0007](0007-proposed-revisions.md).

## 1. Purpose and boundary

This record sets the scope for an executable specification of the way Dogecoin Core accepts a sequence of block headers.
Core does this in `ProcessNewBlockHeaders`, which calls `AcceptBlockHeader` once for each header [C1, C2].
`AcceptBlockHeader` finds the header in the block index or checks it.
The checks are the proof of work, the predecessor and the contextual check, and then the function adds the header to the index.

Design record 0006, decision 7, excluded this composition and left it to a later record.
DogeLib already specifies the two checks that the composition calls:

- `CheckBlockHeader`, as `Block.checkBlockHeader` (design record 0004, stage 4a).
- `ContextualCheckBlockHeader`, as `Block.contextualCheckBlockHeader` (design record 0006, stage 3).

The remaining behaviour reads and changes node state: the block index, its failure flags and the set of failed blocks.
No definition, theorem or comparison covers that behaviour.
This record proposes how to specify it.
It also discharges one execution boundary that design record 0006 left to the caller: the link from a header to its view.
The theorems in section 11 are targets, not implemented results.

DogeLib is a specification library for Dogecoin Core.
A property of an application or of DogeOS belongs in a downstream project, and this record proposes none.

The record excludes these subjects:

- Block bodies: `CheckBlock`, `ContextualCheckBlock`, `AcceptBlock` and `ConnectBlock`. Design record 0006, decision 6, excluded `ContextualCheckBlock`, and section 4.9 gives the reason here.
- Chain selection, reorganization and the best-header pointer `pindexBestHeader`. Section 6.4 discusses the chain work that a header adds.
- Disk state: block files, `setDirtyBlockIndex` and the block-tree database.
- Peer management: the denial-of-service score as a peer penalty, `Misbehaving`, and the checks of the `headers` message in `net_processing.cpp` (section 4.8).
- The sources of time and the option `-checkpoints`. As in design record 0006, the specification takes both as explicit inputs.
- The debug check `CheckBlockIndex` (item 26).
- The operations that set or clear failure state [C6]. They are `AcceptBlock`, `InvalidBlockFound`, `FindMostWorkChain`, `InvalidateBlock`, `ResetBlockFailureFlags`, and the load and unload of the index. The specification takes their result as input state.
- Implementation refinement and Rust extraction.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The line ranges identify the inspected source:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [validation.cpp, lines 3205–3267](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3205-L3267) | `AcceptBlockHeader`. |
| C2 | [validation.cpp, lines 3270–3286](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3270-L3286), [validation.h, line 258](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L258) | `ProcessNewBlockHeaders`. |
| C3 | [validation.cpp, lines 2755–2788](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2755-L2788) | `AddToBlockIndex`. |
| C4 | [validation.cpp, lines 2927–2937](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2927-L2937), [validation.h, line 496](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L496), [dogecoin.cpp, lines 89–125](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp#L89-L125) | `CheckBlockHeader`, its default `fCheckPOW = true`, and `CheckAuxPowProofOfWork`. |
| C5 | [validation.cpp, lines 3066–3119](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3066-L3119) | `ContextualCheckBlockHeader`. |
| C6 | [validation.cpp, lines 105–187](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L105-L187), [lines 1339–1364](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1339-L1364), [lines 2385–2410](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2385-L2410), [lines 2659–2716](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2659-L2716), [lines 2722–2752](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2722-L2752), [lines 3329–3335](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3329-L3335), [lines 3674–3678](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3674-L3678), [line 3958](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3958) | The anonymous namespace with `gFailedBlocks`, and every write of `BLOCK_FAILED_VALID`, `BLOCK_FAILED_CHILD` and `gFailedBlocks` outside C1: `InvalidBlockFound`, `FindMostWorkChain`, `InvalidateBlock`, `ResetBlockFailureFlags`, `AcceptBlock`, `LoadBlockIndexDB` and `UnloadBlockIndex`. |
| C7 | [chain.h, lines 113–148](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.h#L113-L148), [lines 308–329](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.h#L308-L329) | `BlockStatus`, `IsValid` and `RaiseValidity`. |
| C8 | [chain.cpp, lines 113–162](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp#L113-L162) | `GetAncestor`, `BuildSkip` and `GetBlockProof`. |
| C9 | [consensus/validation.h, lines 12–19 and 29–62](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/validation.h#L12-L62) | The reject codes, and `CValidationState::DoS` and `Invalid`. |
| C10 | [net_processing.cpp, lines 2390–2475](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L2390-L2475), [line 2144](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L2144), [validation.h, lines 100, 154 and 157](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L100-L157) | The callers of `ProcessNewBlockHeaders`, and the limits of the `headers` message. |
| C11 | [chainparams.cpp, lines 157–160, 316–320 and 447–450](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L157-L450) | `hashGenesisBlock` of each network, with its assertion. |
| C12 | [validation.cpp, lines 77 and 4136–4163](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L4136-L4163), [init.cpp, line 950](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/init.cpp#L950) | `fCheckBlockIndex` and `CheckBlockIndex`. |
| C13 | [validation.cpp, lines 3980–4010](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3980-L4010) | `InitBlockIndex`, which adds the genesis block. |
| C14 | [pow.cpp, lines 32–88](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pow.cpp#L32-L88), [dogecoin.cpp, lines 26–87](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp#L26-L87) | `GetNextWorkRequired`, `AllowDigishieldMinDifficultyForBlock` and `CalculateDogecoinNextWorkRequired`. |
| C15 | [validation.h, lines 170 and 199](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L170-L199), [validation.cpp, line 3299](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3299), [utiltime.cpp, lines 38–41](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/utiltime.cpp#L38-L41), [timedata.cpp, lines 34–37](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/timedata.cpp#L34-L37) | The exported `mapBlockIndex` and `pindexBestHeader`, the call of `AcceptBlockHeader` in `AcceptBlock`, `SetMockTime` and `GetAdjustedTime`. |
| C16 | [validation.cpp, lines 1630–1645 and 2238–2250](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1630-L2250) | `DisconnectBlock` and its check of undo data, and the call in `DisconnectTip`. |

The registry already records `validation.cpp` (D33), `chain.h` (D18), `chain.cpp` (D35), `dogecoin.cpp` (D6), `pow.cpp` (D17), `chainparams.cpp` (D14), `validation.h` (D69) and `timedata.cpp` (D72).
An implementation lane adds an identifier for each other file that it uses, from D74 on, without a change to any pin.
The findings come from source inspection, without a Core comparison run.

## 3. Inventory

### 3.1 `AcceptBlockHeader`

`AcceptBlockHeader(block, state, chainparams, ppindex)` computes the hash of the pure header [C1, line 3209].
If that hash is the genesis hash of the network, the function skips every check (section 4.1).
Otherwise it runs these steps in order, and it returns at the first failure:

| Order | Lines of C1 | Step | Reject reason | DoS | Reject code |
| --- | --- | --- | --- | --- | --- |
| 1 | 3214–3222 | If the index has the hash, return its entry. Fail if the entry has a failure flag. | `duplicate` | 0 | 0 |
| 2 | 3224–3225 | `CheckBlockHeader` with `fCheckPOW = true`. | `high-hash` | 50 | `REJECT_INVALID` |
| 3 | 3229–3231 | The index must have `hashPrevBlock`. | `bad-prevblk` | 10 | 0 |
| 4 | 3233–3234 | The predecessor must have no failure flag. | `bad-prevblk` | 100 | `REJECT_INVALID` |
| 5 | 3238–3239 | `ContextualCheckBlockHeader` with `GetAdjustedTime()`. | The reason of design record 0006 | 100 for checks 1 to 4, 0 for checks 5 to 7 | `REJECT_INVALID`, `REJECT_CHECKPOINT` or `REJECT_OBSOLETE` |
| 6 | 3241–3256 | Unless the predecessor is valid to `BLOCK_VALID_SCRIPTS`, no member of `gFailedBlocks` may be an ancestor. | `bad-prevblk` | 100 | `REJECT_INVALID` |
| 7 | 3258–3259 | `AddToBlockIndex`. | None | | |

Step 1 returns success for a known header without a failure flag, and it runs no other step.
Step 6 changes the index before it rejects (item 13).
The values of step 2 come from C4, line 2934.
The values of step 5 come from C5 and design record 0006, item 23.
Every other value comes from the line in the table and the defaults of C9.

### 3.2 `AddToBlockIndex`

`AddToBlockIndex` returns the existing entry if the index has the hash [C3, lines 2757–2761].
Otherwise it makes an entry from the header fields, inserts it under the hash and searches the index for `hashPrevBlock` [C3, lines 2764–2772].
If the predecessor exists, the entry gets the predecessor link and the height of the predecessor plus one [C3, lines 2773–2778].
The entry gets `nChainWork`, the predecessor's chain work plus `GetBlockProof` of the entry, and the validity level `BLOCK_VALID_TREE` [C3, lines 2780–2781].
It also updates `nTimeMax`, `pindexBestHeader` and `setDirtyBlockIndex` [C3, lines 2779 and 2782–2785].

### 3.3 `ProcessNewBlockHeaders`

`ProcessNewBlockHeaders(headers, state, chainparams, ppindex)` calls `AcceptBlockHeader` on each header in order, under one lock [C2, lines 3272–3283].
It returns `false` at the first failure, with the state of that failure.
Headers before the failure stay in the index.
On success, `ppindex` points to the entry of the last header, and the function calls `NotifyHeaderTip` [C2, lines 3279–3284].

The function does not require that each header links to the one before it.
Each header needs only a predecessor in the index, which an earlier header of the same call can supply.
So one call can extend several branches.

## 4. Core behaviour that the specification must preserve

Each item comes from the pinned source.
The specification must keep each behaviour, and a theorem or a known answer must pin it.

### 4.1 Genesis

1. `AcceptBlockHeader` compares the hash with `GetConsensus(0).hashGenesisBlock` [C1, line 3212].
   For that hash it skips steps 1 to 6, and `AddToBlockIndex` adds the header or returns the existing entry.
   So the genesis header never gets `duplicate`, even if its entry has a failure flag.
2. A genesis entry has no predecessor and height 0 [C3, lines 2772–2778].
   `AddToBlockIndex` finds no entry for its null `hashPrevBlock`.
3. Each network asserts its genesis hash [C11]: `1a91e3da…5691` on mainnet, `bb0a7826…559e` on testnet and `3d2160a3…73a5` on regtest.
   Each is also the height-0 entry of the checkpoint table of design record 0006.
4. `InitBlockIndex` adds the genesis block at startup [C13, line 4005].
   So a running node always has a genesis entry.
   The genesis case of C1 occurs only when a peer sends the genesis header again.

### 4.2 Duplicates (step 1)

5. Step 1 runs before `CheckBlockHeader` [C1, lines 3214–3224].
   So a known header passes without a proof-of-work check.
6. The key is the hash of the 80-byte pure header.
   Two full headers with the same pure header and different AuxPoW payloads have the same key.
   So step 1 accepts the second header without a check of its payload.
7. A known header with `BLOCK_FAILED_VALID` or `BLOCK_FAILED_CHILD` fails with `duplicate` [C1, lines 3219–3220].
   `state.Invalid` gives DoS 0 and reject code 0 [C9].

### 4.3 The predecessor (steps 3 and 4)

8. Steps 3, 4 and 6 have the same reject reason, `bad-prevblk`.
   Step 3 has DoS 10 and reject code 0 [C1, line 3231].
   Steps 4 and 6 have DoS 100 and `REJECT_INVALID` [C1, lines 3234 and 3253].
   So the reject reason alone does not identify the step.
9. The predecessor can be any entry of the index, on any branch.
   The lookup reads only `mapBlockIndex` [C1, line 3229].

### 4.4 The contextual check (step 5)

10. Step 5 passes the predecessor's entry and `GetAdjustedTime()` [C1, line 3238].
    The contextual check reads the predecessor chain through `pprev`, and the checkpoint search reads all of `mapBlockIndex` [C5].
    So each header of a call sees the index that the earlier headers of the call extended.
    A header after a checkpoint block in the same call can fail `bad-fork-prior-to-checkpoint` where it passed before.
11. `GetAdjustedTime()` runs once for each header.
    The clock can advance between two headers of one call.
12. `GetLastCheckpoint` returns the index entry, and check 4 compares `pcheckpoint->nHeight` [C5, line 3098].
    In the block-index model of section 5, that height is the entry's height.
    It is not the key of the checkpoint table.

### 4.5 Failed ancestors (step 6)

13. Step 6 runs only if the predecessor is not valid to `BLOCK_VALID_SCRIPTS` [C1, line 3241].
    A header-only entry has `BLOCK_VALID_TREE` [C3, line 2781], so step 6 runs for it.
    It looks for a member of `gFailedBlocks` that is an ancestor of the predecessor [C1, lines 3242–3243].
    For the first such member, it marks each entry from the predecessor down to that member [C1, lines 3245–3250].
    The mark is `BLOCK_FAILED_CHILD`.
    The member itself gets no new flag, and then step 6 rejects.
    So this rejection changes the index, and every other rejection leaves it unchanged.
14. Step 6 runs after step 5 [C1, lines 3238–3241].
    A header that fails the contextual check and has a failed ancestor gets the contextual reason.
15. Step 6 reads `gFailedBlocks`, not the status flags.
    Only `InvalidBlockFound` and `InvalidateBlock` insert into the set [C6, lines 1359 and 2701].
    `FindMostWorkChain` marks a candidate chain above a failed entry with `BLOCK_FAILED_CHILD` [C6, line 2400].
    It does not change the set.
    `ResetBlockFailureFlags` clears both flags on an entry, its descendants and its ancestors [C6, lines 2731 and 2747].
    `AcceptBlock` sets `BLOCK_FAILED_VALID` on a block that fails `CheckBlock` or `ContextualCheckBlock`, and does not insert it [C6, lines 3329–3335].
    The set is empty after a restart [C6, line 3958].
    Instead, the load of the index marks descendants with `BLOCK_FAILED_CHILD` [C6, lines 3674–3678].
    Consider a header whose grandparent has `BLOCK_FAILED_VALID` from `AcceptBlock`, and whose predecessor has no flag.
    If the grandparent is not in the set, the header passes steps 4 and 6.
16. `gFailedBlocks` is a `std::set<CBlockIndex*>`, so the loop visits its members in address order [C6, line 180].
    With two failed ancestors on one path, the address order decides which member the loop finds first.
    The verdict is the same for both orders, but the set of entries that get `BLOCK_FAILED_CHILD` differs.
    Address order is an implementation detail, not a protocol requirement ([CONTRIBUTING.md](../../CONTRIBUTING.md#sources-of-truth)).
17. `gFailedBlocks` is in the anonymous namespace of `validation.cpp` [C6, lines 105–187].
    Code outside that file cannot read or write it directly.

### 4.6 Failure flags in a header-only run

18. No step of C1, C2 or C3 sets `BLOCK_FAILED_VALID` or inserts into `gFailedBlocks`.
    A header that fails steps 2 to 5 does not enter the index and gets no flag.
19. So, from an index without failure flags and with an empty `gFailedBlocks`, steps 1, 4 and 6 never reject.
    Those rejections need state from block validation or from `InvalidateBlock`, which section 1 excludes.

### 4.7 Chain work

20. `GetBlockProof` returns 0 when `SetCompact` reports a negative value, an overflow or a zero target [C8, lines 150–157].
    Otherwise it returns `(~target / (target + 1)) + 1` in 256-bit arithmetic [C8, line 162].
    Without overflow, the target is a value of at most 23 significant bits, shifted left by whole bytes.
    So the target is never 2^256 − 1.
    So `t + 1` is below 2^256, and the value equals `⌊2^256 / (t + 1)⌋`.
21. `nChainWork` is the predecessor's `nChainWork` plus that value, or that value alone without a predecessor [C3, line 2780].
    `arith_uint256` addition wraps at 2^256.
22. `AddToBlockIndex` sets `pindexBestHeader` to the new entry only when the entry has strictly more chain work [C3, lines 2782–2783].
    So among headers with equal chain work, the first one stays the best header.

### 4.8 The callers

23. The `headers` message handler rejects a message with more than `MAX_HEADERS_RESULTS` = 2000 headers [C10, net_processing.cpp lines 2399–2403].
24. Suppose that the first header has no known predecessor and the message has fewer than `MAX_BLOCKS_TO_ANNOUNCE` = 8 headers.
    Then the handler does not call `ProcessNewBlockHeaders` [C10, lines 2428–2445].
    The handler also rejects a message in which a header does not link to the one before it [C10, lines 2448–2454].
    Its log message is `non-continuous headers sequence`.
    These checks belong to the peer layer.
    They are not part of `ProcessNewBlockHeaders`, and they do not set a reject reason in the state.
25. The compact-block handler calls `ProcessNewBlockHeaders` with one header [C10, line 2144].
    `AcceptBlock` calls `AcceptBlockHeader` before it checks a block body [C15, validation.cpp line 3299].

### 4.9 What stays outside

26. `CheckBlockIndex` runs at the end of each acceptance, but returns at once unless `fCheckBlockIndex` is set [C12, validation.cpp lines 4136–4140].
    The option is false by default on mainnet and testnet and true on regtest [C12, init.cpp line 950].
    It asserts the consistency of the whole index, and it can abort the process.
    It never changes a verdict that the function returns.
27. `ContextualCheckBlock`, `CheckBlock` and `AcceptBlock` read the transactions of a block [C6].
    Design record 0006, section 4.8, gives the reasons to keep them outside a header scope, and they apply here too.

## 5. The block-index model

### 5.1 What Core's state holds

`AcceptBlockHeader` reads these parts of node state:

| State | Core source | Read by |
| --- | --- | --- |
| Entries by hash | `mapBlockIndex` | Steps 1 and 3, the checkpoint search of step 5, and `AddToBlockIndex` |
| Predecessor links and heights | `CBlockIndex::pprev` and `nHeight` | Step 5 through the view, step 6 through `GetAncestor` |
| Header fields | `nVersion`, `nTime`, `nBits` and the others | Step 5 through the view |
| Failure flags | `BLOCK_FAILED_VALID` and `BLOCK_FAILED_CHILD` in `nStatus` | Steps 1 and 4, written by step 6 |
| Validity level | The low bits of `nStatus` | Step 6, through `IsValid(BLOCK_VALID_SCRIPTS)` |
| Failed blocks | `gFailedBlocks` | Step 6 |
| Chain work | `nChainWork` | `AddToBlockIndex` |
| Checkpoint option | `fCheckpointsEnabled` | Step 5 |
| Adjusted time | `GetAdjustedTime()` | Step 5 |

### 5.2 Options

**Option S1: an explicit model of the block index.**
The state is a finite map from hashes to entries.
Each entry holds the pure header, the height, an optional predecessor hash, the two failure flags, a flag for `BLOCK_VALID_SCRIPTS` and the chain work.
The state also holds `gFailedBlocks` as a list of hashes.
The model can represent several branches, known headers, failure flags and the checkpoint search over the whole index.
So it can express every step of section 3 and every item of section 4.

**Option S2: a list of headers anchored on a known tip.**
The state is one chain, newest first, as the view of design record 0006.
A sequence must extend the tip, and each header must link to the one before it.
The model is smaller, and its theorems are shorter.
It cannot represent a known header, a second branch, a failure flag or `gFailedBlocks`.
So it cannot express steps 1, 4 and 6, items 9 and 13 to 16, or a call that extends two branches.

On a sequence that is not linear, S2 would give a different result from Core.

**Option S3: S1 as the definition, with S2 as a theorem.**
The definition follows Core with S1.
A theorem then states the linear case of S2.
Take a linear extension of a tip, without failure state.
Then Core accepts the sequence exactly when each header passes its checks against the view that its predecessors extend.

**Recommendation: option S3.**
The definition must follow Core on every input of its domain, so S2 alone is not sufficient.
The linear theorem gives a consumer the short statement that S2 would give.

### 5.3 Anchors

A real index reaches the genesis block.
A fixture or a downstream consumer often has only a recent part of the chain.
The model therefore lets an entry have no predecessor above height 0.
The record calls such an entry an *anchor*.

An anchor is outside Core's state, and the view below it ends early, as the finite view of design record 0006 can end early.
`contextualCheckBlockHeader` then returns its existing adapter errors, `shortView` or `nextWork missingAncestor`, when it needs an entry below the anchor.

Step 6 also needs a convention.
Suppose that the walk from the predecessor reaches an anchor above the height of a member of `gFailedBlocks`.
Core's `GetAncestor` would then fail its assertion on `pprev` [C8, line 131].
The specification treats that member as no ancestor, and states this convention as part of the domain.
The oracle refuses a request in which a member of `failed_blocks` is not in the index.

The alternative is to require an index that reaches height 0.
It is closer to Core's state, but every fixture would need the full chain from genesis.
Mainnet has more than five million headers, so the recommendation is to allow anchors.
`contextualCheck_complete` already gives the guarantee for a chain that reaches height 0 (section 11).

### 5.4 Views and checkpoint state for each step

For each header, the step builds the inputs of `contextualCheckBlockHeader` from the index:

- **The view.** The step walks the predecessor links from the predecessor's entry, and collects `⟨nHeight, nTime, nBits⟩` for each entry as a `Work.BlockIndex`.
  It stops after `contextualViewDepth network prev` entries, or at an entry without a predecessor.
  `contextualCheck_congr_prefix` shows that more entries do not change the result.
- **The last checkpoint.** With checkpoints enabled, the step walks the network's checkpoint table from the greatest height down.
  It returns the height of the index entry of the first table hash that the index has, as `GetLastCheckpoint` does [C5, item 12].
  With checkpoints disabled, it returns `none`.
- **The adjusted time.** The step uses the adjusted time of the context (section 6.3).

The view comes from the predecessor's entry, and the step finds that entry by `hashPrevBlock`.
So the link that design record 0006 left to the caller holds by construction.
The model still trusts the anchors that the caller supplies (section 11).

Design record 0006 used the table key as the checkpoint height, under the hash commitment assumption.
The block-index model uses the entry's own height, as Core does.
The two agree when each index key is the hash of its entry's header, and the table hash identifies the checkpoint block.
`lastCheckpointInIndex_eq` (section 11) states that relation.

### 5.5 Well-formed index

The model has states that Core's index never has, such as a predecessor link to a missing hash.
The record proposes a predicate `WellFormed network index` with these conditions:

- Each key is the hash of the pure header of its entry.
- If an entry has a predecessor hash, the index has that hash, and the entry's `hashPrevBlock` equals it.
  The entry's height is then the predecessor's height plus one.
- An entry without a predecessor has height 0 and the genesis hash, or it is an anchor.
- Each height is below 2147483647, as `validateWorkView` requires.
  A step keeps this bound with the adapter error `heightOutOfRange` (section 7.1).
- Each member of the failed list is in the index and has `BLOCK_FAILED_VALID`, as Core asserts [C1, line 3244].

The specification checks this predicate as an adapter error before the first header.
The theorems take it as a hypothesis, and `wellFormed_preserved` shows that each step keeps it.

## 6. Options

### 6.1 Representation of the map

**Form M1: an association list** `List (Hash256 × IndexEntry)`, with lookup by `List.lookup` and insertion at the head.
The proofs use the list lemmas of Lean core, and the oracle can print the list.
A lookup costs time linear in the size, which is acceptable for fixtures of a few thousand entries.

**Form M2: `Std.HashMap Hash256 IndexEntry`.**
Lookups are fast, and Lean core has the insertion and lookup lemmas.
`Hash256` needs a `Hashable` instance, and the oracle must order the entries to print them.

**Form M3: a function** `Hash256 → Option IndexEntry`.
The proofs are simplest, but the oracle cannot list the entries, and every lookup walks a chain of closures.

**Recommendation: form M1, behind one interface of lookup and insertion.**
The specification reads the map only through that interface.
A later lane can change the form with a congruence theorem and no change to any other theorem.

### 6.2 Failure state

The model must keep the three parts of failure state apart, because Core reads them at different steps (item 15):

- `failedValid` and `failedChild`, the two flags in `nStatus`.
- `scriptsValid`, which records `IsValid(BLOCK_VALID_SCRIPTS)` without the failure flags.
- `failedBlocks`, the list of `gFailedBlocks` members.

For item 16, the specification visits `failedBlocks` in list order.
A theorem shows that the verdict does not depend on that order.
The set of marked entries can depend on it, only when two members are ancestors of one predecessor.
Section 8.3 says how the comparison handles that case.

The alternative is to omit step 6, because only block validation and `InvalidateBlock` fill the set.
The record does not recommend it.
Step 6 is part of `AcceptBlockHeader`, and the order of item 14 is observable.

### 6.3 Adjusted time

Core reads the clock once for each header (item 11).

- **Form T1: one adjusted time for the call.** The context holds one `Int64`.
- **Form T2: one adjusted time for each header.** The input holds a list with one value for each header.

**Recommendation: form T1.**
A call holds `cs_main` for its whole run, and the harness fixes the time.
`process_adjustedTime_mono` (section 11) extends `contextualCheck_adjustedTime_mono` of design record 0006 to sequences.
The same argument for each step shows that an acceptance stays an acceptance when the clock advances during a call.
Form T2 stays available as a generalization that does not change any step.

### 6.4 Chain work

A header-sync consumer usually needs the chain work of a branch.
Three scopes are possible:

- **W1: exclude chain work.** The entries hold no chain work.
- **W2: chain work for each entry.** The model specifies `GetBlockProof` and the sum of item 21, and each entry holds its `nChainWork`.
  An anchor holds a chain work that the caller supplies.
- **W3: W2 and the best header.** The model also specifies `pindexBestHeader` and its first-seen rule (item 22).

**Recommendation: W2, in its own stage (stage 4).**
The values are deterministic functions of the header fields, and `Work.ArithUint256` already has `setCompact` and 256-bit division.
The best header starts chain selection, which section 1 excludes.
A consumer can compare the chain work of two entries without a model of `pindexBestHeader`.

### 6.5 The proof-of-work check

The step calls `checkBlockHeader network` on the full header, with its AuxPoW payload.
A parameter for the header check, as the signature checker of Script verification, is the alternative.
The record does not recommend it: Core's step 2 is a fixed function, and no theorem of section 11 needs to vary it.
Most theorems do not unfold `checkBlockHeader`, so they do not depend on scrypt.

### 6.6 The peer layer

The checks of item 24 decide whether `ProcessNewBlockHeaders` runs.
They are not consensus checks, and they set no reject reason.
The record proposes to exclude them.
A later lane can add a wrapper for the `headers` message, if a consumer needs it.

## 7. Contract for implementation

### 7.1 Types

The names below are proposals:

```text
structure IndexEntry where
  header       : PureBlockHeader
  height       : Nat
  prev         : Option Hash256    -- none: genesis or an anchor
  failedValid  : Bool              -- BLOCK_FAILED_VALID
  failedChild  : Bool              -- BLOCK_FAILED_CHILD
  scriptsValid : Bool              -- validity level at least BLOCK_VALID_SCRIPTS
  chainWork    : ArithUint256      -- stage 4

structure HeaderIndex where
  entries      : List (Hash256 × IndexEntry)
  failedBlocks : List Hash256      -- gFailedBlocks, in visit order

structure HeaderContext where
  network            : WorkNetwork
  adjustedTime       : Int64
  checkpointsEnabled : Bool
```

`HeaderRejection` has one constructor for each rejection of section 3.1:

- `duplicate`, step 1.
- `highHash (error : CheckPowError)`, step 2.
- `prevBlockNotFound`, step 3.
- `prevBlockInvalid`, step 4.
- `contextual (error : ContextualHeaderError)`, step 5, for a Core rejection only.
- `failedAncestor (failed : Hash256)`, step 6, with the member that the walk found.

Functions `rejectReason`, `dosScore` and `rejectCode` give Core's values from section 3.1.
They are observables for the comparison, not a model of peer management.

`HeaderAdapterError` holds the inputs outside the domain:

- An index that `WellFormed` rejects.
- An adapter error of `contextualCheckBlockHeader` at an anchor: `shortView`, `nextWork` or `invalidView`.
- An adjusted time above `INT64_MAX − 7200` (design record 0006, decision 9).
- `heightOutOfRange`: a predecessor at height 2147483646, so that the candidate height would be 2147483647.

The step checks `heightOutOfRange` after step 4 and before step 5, where Core computes the candidate height [C5, line 3068].
Core accepts a candidate at `INT_MAX`, but the next height would overflow `int`, which is undefined behaviour.
The specification excludes that last height, so that every entry stays in the domain of `validateWorkView`.
At one block each minute, no Dogecoin chain reaches that height for about 4000 years.

### 7.2 Functions

```text
acceptBlockHeader (ctx : HeaderContext) (index : HeaderIndex) (header : BlockHeader)
  : HeaderIndex × Except HeaderStepError Hash256

processNewBlockHeaders (ctx : HeaderContext) (index : HeaderIndex) (headers : List BlockHeader)
  : HeaderIndex × Except HeaderSequenceError (Option Hash256)
```

`HeaderStepError` is a rejection or an adapter error.
`HeaderSequenceError` adds the position of the failing header in the list.

`acceptBlockHeader` follows section 3.1.
It returns the index after the step and the hash of the header's entry.
On a rejection of step 6, the returned index has the `failedChild` marks of item 13.
On every other error, it is the input index.

`processNewBlockHeaders` folds `acceptBlockHeader` over the list, and stops at the first error.
It returns the index after the last step that ran, and the hash of the last header on success.
For an empty list, the result is `none`, as Core leaves `ppindex` unchanged.

`composeSequence n first second` combines two results, where `n` is the length of the first list:

- If `first` is an error, the result is `first`.
- Otherwise the index is the index of `second`.
  An error of `second` has its position increased by `n`.
  A success of `second` with `none` keeps the last hash of `first`.

### 7.3 Composition of existing definitions

The step composes these definitions without a change to them:

- `Block.checkBlockHeader`, for step 2.
- `Block.contextualCheckBlockHeader`, for step 5, with the view and the last checkpoint of section 5.4.
- `Block.checkpoints` and `PureBlockHeader.getHash`, for the checkpoint search over the index.
- `Work.ArithUint256.setCompact`, for `GetBlockProof` in stage 4.

Step 5 passes the candidate's own `nTime` to `nextWorkRequired`, through `contextualCheckBlockHeader`.
`nextWorkRequired` selects the record at the candidate height for each network.
On testnet, that record decides the two minimum-difficulty rules (design record 0006, section 9.2).
On regtest, it decides the DigiShield change at candidate height 10.
Neither `GetNextWorkRequired` nor `CalculateDogecoinNextWorkRequired` reads `fPowNoRetargeting` at the pin [C14], so regtest needs no other rule.
The sequence layer adds no work rule.

The step adds these definitions:

- `ancestorView`, the walk of section 5.4.
- `lastCheckpointInIndex`, the checkpoint search of section 5.4.
- `failedAncestor?` and `markFailedChild`, step 6.
- `addToBlockIndex`, the insertion of section 3.2, without `nTimeMax`, `pindexBestHeader` and the dirty set.
- `blockProof`, `GetBlockProof`, in stage 4.

### 7.4 Placement

The composition reads full headers, `checkBlockHeader` and `contextualCheckBlockHeader`, so it belongs to the `Block` layer.
The record proposes the module `DogeLib.Block.HeaderSequence`, with its theorems in `DogeLib.Block.Proofs.HeaderSequence`.
`blockProof` acts on compact targets, so it belongs to the `Work` layer, as `Work.ChainWork`.
The lane that adds the modules updates the `Block` and `Work` rows of ARCHITECTURE.md.

## 8. Oracle and Core harness

### 8.1 Operation

The record proposes one additional operation, `block.header_sequence`:

| Field | Content |
| --- | --- |
| `network` | `mainnet`, `testnet` or `regtest`. |
| `mode` | The read mode of the embedded transaction in each full header, as in `block.check_pow`. |
| `adjusted_time` | A signed 64-bit integer, at most `INT64_MAX − 7200`. |
| `checkpoints_enabled` | Boolean. |
| `index` | The initial entries: `header_hex` (exactly 80 bytes), `height`, `anchor`, `failed_valid`, `failed_child`, `scripts_valid` and, from stage 4, `chain_work`. |
| `failed_blocks` | Hashes in display order, in visit order. |
| `headers` | The full headers of the call, each as hexadecimal bytes with its AuxPoW payload. |

The oracle derives each key from `header_hex`, and each predecessor from `hashPrevBlock` unless `anchor` is true.
An index that `WellFormed` rejects is a request error.

The response has these fields:

- `valid`, and `failed_at`: the position of the failing header, or null.
- `reject_reason`, `dos` and `reject_code`: Core's values, or null on acceptance.
- `last_hash`: the hash of the last header on acceptance.
- `added`: for each added entry, its hash, height and, from stage 4, chain work.
- `marked_failed_child`: the hashes that step 6 marked.
- A Lean-only `diagnostic`.

The comparator compares every field except `diagnostic` (item 8), with one exception.
If two members of `failed_blocks` are ancestors of one predecessor, it also excludes `marked_failed_child` (section 8.3).
Under the [development policy](../oracle.md#format-stability), the stage 5 pull request settles the field names under ordinary review.

### 8.2 The Core side

`AcceptBlockHeader` is `static` in `validation.cpp` [C1, line 3205].
So a caller outside that file can reach it only through `ProcessNewBlockHeaders` or `ProcessNewBlock`.
Two approaches are possible.

**H1: call `ProcessNewBlockHeaders` on a scratch chainstate.**
The harness links `validation.cpp` and the server library, with LevelDB and the Boost Filesystem, Thread and System libraries.
It must prepare this global state:

- `SelectParams` for the network, and a scratch data directory.
- The block-tree database and `InitBlockIndex`, which writes the genesis block to disk [C13].
- `mapBlockIndex`, which is an exported global [C15, validation.h line 170].
  The harness can insert anchor entries with `pprev`, `nHeight`, `nStatus` and `nChainWork`, and call `BuildSkip`.
- `pindexBestHeader` [C15, validation.h line 199].
- `fCheckBlockIndex` false, because `CheckBlockIndex` asserts that the index has exactly one entry without a predecessor [C12, validation.cpp line 4163].
  An index with anchors fails that assertion.
- The adjusted time through `SetMockTime`, with a peer offset of zero [C15].

`gFailedBlocks` is in the anonymous namespace (item 17), so the harness fills it through `InvalidateBlock`.
That function disconnects the entry only while `chainActive` contains it [C6, line 2672].
After that loop, it sets `BLOCK_FAILED_VALID` and inserts the entry [C6, lines 2698–2701].
So a header-only entry, which is never active, works.
It needs an active tip, because `InvalidChainFound` asserts one [C6, line 1349], and it needs `pcoinsTip` for its mempool update.
A scratch chainstate with the genesis block active supplies both.

The disconnect loop limits this route.
`DisconnectTip` calls `DisconnectBlock`, which returns an error when the block has no undo data [C16, lines 1639–1642].
The genesis block has no undo data, so `InvalidateBlock` on the active genesis entry returns before the insertion.
A direct write of `nStatus` sets flags, but it cannot reach the set in the anonymous namespace.

So H1 supports these failure states:

- Any failure flags, including those of item 15 without set membership, through direct writes of `nStatus`.
- Members of the failed list that are not in `chainActive`, through `InvalidateBlock`.

H1 cannot put the genesis entry in the failed list, and the record found no other mechanism at the pin that can.
H2 owns its failed list, so it has no such gap, and it compares those states alone.
A state with genesis in the failed list may not occur in a running node, but `WellFormed` allows it.
In that state, step 6 rejects a header whose predecessor lacks `scriptsValid` when the predecessor's chain reaches genesis.
On a branch that ends at an anchor, the walk never meets genesis, so step 6 passes.

**H2: transcribe the bodies and call Core's helpers.**
The harness transcribes `AcceptBlockHeader` [C1] and the index part of `AddToBlockIndex` [C3], as it transcribes `ContextualCheckBlockHeader` for `block.contextual_check`.
Each step calls Core's code: `CheckAuxPowProofOfWork`, the existing transcription of `ContextualCheckBlockHeader` with Core's helpers, `CBlockIndex::GetAncestor`, `BuildSkip`, `GetBlockProof` and `Checkpoints::GetLastCheckpoint`.
The harness owns `mapBlockIndex`, `fCheckpointsEnabled` and a failed list.
The existing operation inserts each known checkpoint under its table hash, but this operation keys the map by the hash of each header.

Anchors need two guards, because Core's `GetAncestor` asserts `pprev` when a walk passes below an anchor [C8, line 131]:

- `BuildSkip` calls `GetAncestor` at the skip height [C8, line 147].
  For example, the skip height of 144720 is 144704, below an anchor at 144719.
  The harness calls `BuildSkip` only when the skip height is at least the height of the branch's anchor, and leaves `pskip` null otherwise.
  The existing work and contextual operations use the same guard with Core's skip-height formula ([core_oracle.cpp](../../harness/core/core_oracle.cpp), `availableSkipHeight` and its use in the chain build).
- Step 6 calls `GetAncestor` for each failed member.
  The harness replaces that call with an adapter that walks `pprev`, and returns null when it reaches an anchor above the member's height.
  The adapter follows the convention of section 5.3, and review checks it against C8, lines 113–137.

The contextual check also reads ancestors through `GetAncestor` at a retarget [C14, pow.cpp line 84].
So the harness refuses a step whose view is too short before it calls the transcription, as the existing operation does.

The build links no additional object: `auxpow.o`, `chain.o`, `checkpoints.o`, `dogecoin.o` and `pow.o` are already in it.
This record does not test that build.

**Recommendation: H2, with a check of the transcription.**
As in design record 0006, H2 keeps the current build, and Core's code computes every value that a step compares.
Its risk is a transcription mistake.
Line-by-line review, and known answers with hand-derived expectations, limit that risk.
H1 stays a later option, when the maintainer wants Core's own `AcceptBlockHeader` in the loop.

### 8.3 Order of the failed list

The H2 harness visits its failed list in request order, not in address order.
That order is a transcription choice, and section 4.5, item 16, says why it does not matter for the protocol.
On a request in which two members of `failed_blocks` are ancestors of one predecessor, the comparator compares the verdict and the reason, and excludes `marked_failed_child`.
The theorem `failedAncestor_verdict_perm` (section 11) covers that case for every order.

## 9. Evidence plan

### 9.1 Existing fixtures

| Fixture | Heights | Use for sequences |
| --- | --- | --- |
| `tests/work/mainnet-genesis-headers` | 0 to 12 | A sequence from genesis with no anchor. The headers have no AuxPoW payload, so each is a full header. |
| `tests/work/mainnet-headers` | 144719 to 145030 | A sequence with an anchor at 144719, across the retarget at candidate 144960 and the first DigiShield height 145000. Full headers. |
| `tests/block/mainnet-auxpow-activation-headers` | 371320 to 371340 | Pure headers only. The README records that the payloads were removed. |
| `tests/block/mainnet-bip66-headers` | 1032483 to 1034390 | Pure headers only. |
| `tests/block/mainnet-bip65-headers` | 3464739 to 3464760 | Pure headers only. |

From an anchor at 144719, the candidates from 144730 have 11 predecessors in the view, as in design record 0006, section 9.1.
The retarget at candidate 144960 reads the anchor itself.
The checkpoint at 145000 is in this range, so a sequence through it changes the last checkpoint for the headers after it (item 10).

### 9.2 Additional fixtures

Step 2 reads the AuxPoW payload, so the three ranges after AuxPoW activation need full headers.
The Electrum server of those fixtures returns each header with its payload ([README](../../tests/block/mainnet-auxpow-activation-headers/README.md)).
The proposal is three additional directories with the same heights and the full bytes, next to the existing pure fixtures.
The existing fixtures do not change.
Each README records the source, the request, the fetch date and a second server that returned the same bytes.
An independent Python check confirms the predecessor links, the anchor hash of each range and the split of each payload.

Regtest needs synthetic sequences.
The regtest proof-of-work limit is `0x207fffff`, so an independent Python script can mine each header with `hashlib.scrypt`.
The script and its seed enter the repository with the fixture.
The expected verdicts come from hand derivation, not from DogeLib or the harness.
Testnet needs no sequence fixture of its own, because the sequence layer adds no rule that depends on the network.
The per-step testnet rules keep the evidence of design record 0006.

### 9.3 Expected values

For real headers, chain acceptance supplies the expected verdict of each step: each header is accepted.
The initial failure state, the adjusted time and the checkpoint option are not chain data.
The fixture chooses them, records them, and derives each expected reason, DoS score, reject code and mark set by hand from C1.

A value that DogeLib computes is never an expected value for DogeLib.
The Core harness gives comparison evidence, not known answers.

### 9.4 Mutations

Each rejection needs a mutation on each side of its boundary:

| Subject | Mutations |
| --- | --- |
| Link | A header whose `hashPrevBlock` is unknown, as the first header and in the middle of a sequence. The prefix before it stays in the index. |
| Proof of work | A nonce change that fails step 2. The change also changes the hash, so the fixture records the new hash. |
| Required work | `nBits` plus one in the middle of a sequence: `bad-diffbits` at that position, and no later header runs. |
| Duplicate | A header sent twice in one sequence: the second step accepts without a change. The same header with a failure flag: `duplicate`. The genesis header with a failure flag: accepted (item 1). |
| Failed predecessor | A predecessor with `failedValid`, and one with `failedChild`. |
| Failed ancestor | A failed grandparent in `failed_blocks` with `scripts_valid` false: rejection and marks. The same with `scripts_valid` true: acceptance. A failed grandparent with `failedValid` that is not in `failed_blocks`: acceptance (item 15). A header that fails step 5 and has a failed ancestor: the contextual reason (item 14). Two failed ancestors on one path. |
| Branches | A sequence that extends two branches from one predecessor. A sequence whose header links to an earlier header that is not the one before it. |
| Retarget and DigiShield | A sequence across candidate 144960 and across 145000, on mainnet. |
| Version gates | Sequences across 371337, `BIP66Height` and `BIP65Height`, with full headers, and a legacy or AuxPoW version at the activation height. |
| Checkpoints | A sequence through the block at 145000, followed by a header on a branch below 145000: `bad-fork-prior-to-checkpoint` with checkpoints enabled, and acceptance with them disabled. |
| Anchors | A sequence whose first candidate needs an entry below the anchor: the adapter error. |
| Empty input | An empty list: acceptance with no change. |

The Core comparison adds seeded mutations of the order of headers, `nBits`, `nTime`, `hashPrevBlock`, the failure flags and the failed list.
Any mismatch becomes a minimized regression case before an agreement claim.

## 10. Stages and exit conditions

### Stage 1: the block-index model

The stage adds `IndexEntry`, `HeaderIndex`, `WellFormed`, `ancestorView` and `lastCheckpointInIndex`.

The stage exits with these results:

- `ancestorView_congr` and `lastCheckpointInIndex_eq` of section 11.
- Known answers for views built from the existing mainnet fixtures.

### Stage 2: one step

The stage adds `acceptBlockHeader`, its error types and `addToBlockIndex` without chain work.

The stage exits with these results:

- The step theorems of section 11.
- Known answers through the compiled code for each row of section 9.4 that concerns one header.

### Stage 3: the sequence

The stage adds `processNewBlockHeaders`.

The stage exits with these results:

- The sequence theorems of section 11, with the linear theorem.
- Known answers for each sequence of section 9.4, on the existing fixtures and on the full-header fixtures of section 9.2.

### Stage 4: chain work

The stage adds `Work.blockProof` and the `chainWork` field (section 6.4).

The stage exits with these results:

- `blockProof_eq` and `chainWork_add` of section 11.
- Known answers of `GetBlockProof` for compact values at the proof-of-work limits, a negative value, an overflow and a zero target, with hand-derived expectations.

### Stage 5: oracle and Core comparison

The stage adds `block.header_sequence` to the oracle and to the Core harness (section 8), with fixtures and comparator self-tests.

The stage exits with reproducible differential runs that record both revisions, the selected cases and the random seeds.
The documentation in [docs/oracle.md](../oracle.md), COVERAGE.md and SOUNDNESS.md changes in the same pull request.

## 11. Theorem targets

The names below are proposals.
Each theorem states its domain and hypotheses in its doc comment.

Every theorem except `wellFormed_preserved` assumes `WellFormed` of the input index.
The theorems on sequences state their height budget: the greatest height in the index plus the length of the list stays below 2147483647.
The last column estimates the proof cost.
A *cheap* target follows from the definitions and existing theorems.
A *new lemmas* target needs lemmas about the map, the walk or `ArithUint256`.

| Target | Statement | Cost |
| --- | --- | --- |
| `ancestorView_congr` | For a predecessor whose chain reaches height 0, `contextualCheckBlockHeader` gives the same result on `ancestorView` as on the whole chain of predecessors. | Cheap, from `contextualCheck_congr_prefix` |
| `lastCheckpointInIndex_eq` | Suppose that each table hash in the index belongs to an entry at its table height. Then `lastCheckpointInIndex` equals `lastCheckpoint` of design record 0006, applied to the table heights whose hashes the index has. | New lemmas |
| `accept_genesis` | For the genesis hash, the step accepts, even when its entry has a failure flag (item 1). If the index has no genesis entry, the step inserts one with no predecessor, height 0, no flags and chain work `blockProof` of its `nBits`. Otherwise the index does not change. | Cheap |
| `accept_known` | For a known hash other than genesis, with no failure flag, the step accepts and returns the input index. With a flag, it returns `duplicate` and the input index. | Cheap |
| `accept_eq_ok_iff` | Take an unknown hash other than genesis. The step accepts exactly when five conditions hold. Step 2 passes. The predecessor exists without a flag. The predecessor's height is below 2147483646. The contextual check accepts on the view and checkpoint of section 5.4. The predecessor has `scriptsValid`, or no member of the failed list is its ancestor. | New lemmas |
| `accept_eq_error_iff` | Take a hash other than genesis. For each rejection of section 3.1, the step returns it exactly when its condition fails and the conditions of all earlier steps hold. For steps 5 and 6, the earlier conditions include the height bound of `heightOutOfRange`. A companion statement gives `heightOutOfRange` exactly when steps 1 to 4 pass and the predecessor is at height 2147483646. | New lemmas |
| `accept_ok_insert` | On acceptance of an unknown hash other than genesis, the result index is the input index with one inserted entry. The entry has the predecessor hash, the predecessor's height plus one and no flags. The failed list does not change. | Cheap |
| `accept_error_index` | On an adapter error, and on a rejection other than `failedAncestor`, the result index is the input index. On `failedAncestor`, only `failedChild` changes, on the entries from the predecessor down to the found member. | New lemmas |
| `wellFormed_preserved` | Each step maps a well-formed index to a well-formed index. | New lemmas |
| `accept_link` | Take the acceptance of an unknown hash other than genesis. The added entry's predecessor hash is the header's `hashPrevBlock`, and its height is the predecessor's height plus one. | Cheap |
| `process_append` | Processing `xs ++ ys` from an index gives `composeSequence xs.length` of the result of `xs` and the result of `ys` from the index after `xs`. | Cheap |
| `process_error_suffix` | If processing `xs` fails at position `i`, processing `xs ++ ys` fails at `i` with the same rejection and the same index. | Cheap, from `process_append` |
| `process_prefix_ok` | If processing `xs ++ ys` succeeds, processing `xs` succeeds. | Cheap |
| `process_linear` | Let the index have an entry `t` with `t.height + n < 2147483647`, and let `h₁ … hₙ` link from `t` in order. Their hashes are unknown and differ from the genesis hash, and the path has no failure state. The sequence succeeds exactly when each `hᵢ` passes step 2 and the contextual check. That check uses the view of `hᵢ₋₁ … h₁` followed by the view of `t`, and the last checkpoint of the index after `hᵢ₋₁`. | New lemmas |
| `process_height` | In the setting of `process_linear`, on success the entry of `hᵢ` has height `t.height + i`. | Cheap, from `accept_link` |
| `process_no_failure` | Start from an index without failure flags and with an empty failed list. No step returns `duplicate`, `prevBlockInvalid` or `failedAncestor`, and no step sets a flag (item 19). | New lemmas |
| `failedAncestor_verdict_perm` | The verdict and reason of a step do not depend on the order of the failed list. | New lemmas |
| `process_adjustedTime_mono` | If processing accepts with one adjusted time, it accepts with every greater adjusted time up to `INT64_MAX − 7200`, and gives the same index. | New lemmas, from `contextualCheck_adjustedTime_mono` |
| `process_complete` | Take an index without anchors, an adjusted time in the domain, and a list of `n` headers. If every height in the index is below `2147483647 − n`, processing returns no adapter error. | Cheap, from `contextualCheck_complete` |
| `blockProof_eq` | For a compact value whose `setCompact` result is not negative, does not overflow and is not zero, `blockProof` is `⌊2^256 / (t + 1)⌋` for its target `t`. Otherwise it is 0. | New lemmas |
| `chainWork_add` | The chain work of an added entry is the predecessor's chain work plus `blockProof` of its `nBits`, modulo 2^256. | Cheap |

`process_linear` is the step-wise characterization that option S3 asks for.
It is the main theorem for a consumer that follows one chain.
No target assumes collision resistance or another cryptographic property.
`lastCheckpointInIndex_eq` names the hash commitment assumption as a hypothesis instead.

The theorems establish the behaviour of DogeLib's definitions.
A claim of agreement with Core needs the source review of [SOUNDNESS.md](../../SOUNDNESS.md) and the comparison of stage 5.
The block-index model removes one execution boundary of design record 0006: the link from the header to the view (section 5.4).
Three inputs stay execution boundaries, and stage 3 records them in SOUNDNESS.md:

- The adjusted time, as in design record 0006.
- The checkpoint option, as in design record 0006.
- The initial index: its anchors, failure flags, validity flags, failed list and anchor chain work.
  No theorem says that this state is the state that a node holds.

The record adds no axiom and no trust assumption.

## 12. Relation to design record 0007

Design record 0007, section 8.3, needs a specification of block validity for a full soft-fork claim.
This record does not supply it.
It contributes three parts:

- **A chain-level header predicate.** A revision of a header check can state its claim over a sequence.
  The claim is that the baseline accepts every sequence that the revised step accepts, from the same index.
  The proof is an induction with `process_append`, from a header-local theorem at each step.
- **The candidate height from the index.** The height of the block-level activation model of design record 0007, section 7.2, comes from the predecessor's entry, not from a caller.
- **A state for block validity.** `HeaderIndex` gives a later block-validity record the index that `AcceptBlock` extends.

A full soft-fork claim still needs `CheckBlock`, `ContextualCheckBlock`, `ConnectBlock`, a UTXO set and the legacy projection.
Every claim that this record enables stays header-local in the labels of design record 0007, section 8.2.

## 13. Decisions

These proposals wait for a maintainer decision:

| Number | Topic | Proposal | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | State model | Option S3: an explicit block-index model as the definition, with the linear case as the theorem `process_linear` (section 5.2). | S2: a list of headers anchored on a tip, which cannot express steps 1, 4 and 6 or branches. | Proposed |
| 2 | Anchors | Entries without a predecessor above height 0, with the adapter errors of `contextualCheckBlockHeader` below them (section 5.3). | An index that must reach height 0. | Proposed |
| 3 | Map representation | M1: an association list behind one lookup and insertion interface (section 6.1). | M2 `Std.HashMap`, or M3 a function. | Proposed |
| 4 | Failure state | Keep both flags, `scriptsValid` and the failed list apart, and specify step 6 with its marks (section 6.2). | Omit step 6, because only block validation fills the failed list. | Proposed |
| 5 | Order of the failed list | List order in the specification and the harness. A theorem shows that the verdict does not depend on the order. The comparison excludes `marked_failed_child` when two members of `failed_blocks` are ancestors of one predecessor (section 8.3). | Model address order, which is not observable from a request. | Proposed |
| 6 | Adjusted time | T1: one value for the call (section 6.3). | T2: one value for each header. | Proposed |
| 7 | Checkpoints | Derive the last checkpoint from the index and the enabled flag, with the entry height (section 5.4). | Take known checkpoint heights from the caller for each step, as in design record 0006. | Proposed |
| 8 | Chain work | W2: `GetBlockProof` and `nChainWork` for each entry, in stage 4. No best header (section 6.4). | W1: no chain work. W3: also `pindexBestHeader`. | Proposed |
| 9 | Proof of work | Call `checkBlockHeader` directly on full headers (section 6.5). | A header-check parameter. | Proposed |
| 10 | Peer layer | Exclude the checks of the `headers` message (section 6.6). | Add a wrapper for the message. | Proposed |
| 11 | Core harness | H2: a transcription of C1 and the index part of C3 that calls Core's helpers (section 8.2). | H1: link `validation.cpp` and call `ProcessNewBlockHeaders` on a scratch chainstate. | Proposed |
| 12 | Comparison | Compare `valid`, `failed_at`, the reason, DoS score and reject code, `last_hash`, `added` and `marked_failed_child`. Exclude the Lean diagnostic. Exclude `marked_failed_child` when two members of `failed_blocks` are ancestors of one predecessor (sections 8.1 and 8.3). | Compare only `valid` and the reason, which cannot separate the three `bad-prevblk` steps. | Proposed |
| 13 | Fixtures | Full-header copies of the three ranges after AuxPoW activation, in additional directories. Synthetic regtest sequences mined by an independent script. No testnet sequence fixture (section 9.2). | Real testnet headers, or synthetic testnet sequences mined at the minimum difficulty. | Proposed |
| 14 | Block bodies | Exclude `CheckBlock`, `ContextualCheckBlock`, `AcceptBlock` and `ConnectBlock` (section 1). | None in this scope. | Proposed |
| 15 | `CheckBlockIndex` | Exclude it, because it never changes a verdict (item 26). | Model its assertions as an adapter error. | Proposed |
| 16 | Rust work | Implementation refinement and Rust extraction stay outside this scope. | None in this scope. | Proposed |
| 17 | Height bound | The adapter error `heightOutOfRange` for a candidate at height 2147483647, so that every entry stays below that height (section 7.1). | Allow that one height in the index, and let later steps return `invalidView`. | Proposed |

## 14. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The specification reads failure flags in step 6 instead of `gFailedBlocks`, and rejects a header that Core accepts. | Item 15, the mutation with a failed grandparent that is not in the list, and `accept_eq_ok_iff`. |
| The specification runs step 6 before step 5, so a header gets `bad-prevblk` where Core gives the contextual reason. | Item 14, `accept_eq_error_iff` and the mutation with both failures. |
| A rejection of step 6 leaves the index unchanged in the specification. | `accept_error_index`, the comparison of `marked_failed_child`, and a sequence that sends a second header after the rejection. |
| A comparison of reasons alone hides a confusion of the three `bad-prevblk` steps. | Decision 12 compares the DoS score and the reject code as well. |
| The specification requires each header to link to the one before it, as the peer layer does. | Item 24, decision 10 and the mutation with two branches. |
| A known header with a different AuxPoW payload fails in the specification. | Item 6, `accept_known` and a mutation of the payload of a known header. |
| The checkpoint search ignores entries that earlier headers of the call added. | Item 10, `lastCheckpointInIndex_eq` and the mutation through the checkpoint at 145000. |
| The transcription of H2 differs from C1, so the harness and the specification agree on a wrong rule. | Line-by-line review, hand-derived known answers and Core's helpers for every compared value. Decision 11 keeps H1 available. |
| Scrypt in the compiled code makes the long fixture ranges slow in `lake test`. | Stage 3 measures the cost, and can run the long ranges in the oracle comparison only. |
| A fixture with anchors gives a different result from a full chain. | `ancestorView_congr`, `process_complete`, and anchors deep enough for each candidate (section 9.1). |

There is no pin change, trust-policy exception, change to an agreed theorem statement or change to an existing fixture format in this record.
Adoption of the scope does not establish any target theorem, and it does not authorize the merge of a later implementation.
