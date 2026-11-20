# Relative lock time as a proposed revision

**Status:** Adopted on 2026-11-20, with the decisions that section 13 records.
This record is frozen.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-20
**Companions:** [Design record 0007](0007-proposed-revisions.md), [design record 0010](0010-block-validity.md), [design record 0011](0011-mainnet-ranges.md), [sources](../../SOURCES.md), [coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [oracle contract](../oracle.md) and [DogeLib in practice](../in-practice.md).

## 1. Purpose and boundary

Design record 0007 gave DogeLib a way to state a proposed revision.
Its two examples are invented rules, and their theorems are Script-local.
Its section 8.3 said that a soft-fork claim about blocks needed a specification of block validity.
Design record 0010 added that specification: `connectBlock` and `validateBlock`.

This record takes its revision from a public proposal for Dogecoin.
It is the first such revision in DogeLib.
The revision turns on three rules that Bitcoin deployed together under the name CSV:

- BIP 68: the sequence of an input can state a relative lock time, in blocks or in units of 512 seconds.
- BIP 112: the opcode `OP_CHECKSEQUENCEVERIFY` (CSV) replaces `OP_NOP3`.
- BIP 113: the lock-time test of a block compares with the median time past of its predecessor.

Dogecoin Core 1.14.9 holds the code of the three rules.
Their version-bits deployment cannot activate on mainnet (section 3.5).
A maintainer of Dogecoin Core proposed their activation in discussion 3509 of `dogecoin/dogecoin` in 2024.
The record uses the neutral name `RelativeLockTime` for the revision.

The record has three purposes:

1. It states the revision on the block-level layer of design record 0011, with each extension of that layer that the rules need.
2. It states the theorem targets, with their domains and hypotheses.
3. It states the evidence: known answers, a comparison with Core's own dormant code, and a replay of mainnet history.

The record is a design.
It adds no Lean code, and every theorem of section 9 is a target, not a result.
DogeLib is a specification library.
The record does not argue for or against the activation of these rules on Dogecoin.

## 2. Sources

### 2.1 Reference software revision

Every Core citation refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The findings come from source inspection, without a Core run.

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| R1 | [validation.cpp, lines 258–269](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L258-L269) | `IsFinalTx`. |
| R2 | [validation.cpp, lines 309–384](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L309-L384) | `CalculateSequenceLocks`, `EvaluateSequenceLocks` and `SequenceLocks`. |
| R3 | [validation.cpp, lines 1906–1911 and 1942–1959](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1906-L1959) | `ConnectBlock`: the CSV flag, `nLockTimeFlags`, the heights of the spent coins and the `SequenceLocks` test. |
| R4 | [validation.cpp, lines 3127–3140](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3127-L3140) | `ContextualCheckBlock`: the lock-time cutoff. |
| R5 | [validation.cpp, line 3104](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3104) | `ContextualCheckBlockHeader`: the reason `time-too-old`. |
| R6 | [validation.cpp, lines 1488–1512](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1488-L1512) | `CheckInputs`: the two reasons of a script failure. |
| R7 | [interpreter.cpp, lines 392–427 and 1310–1354](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L392-L427) | `OP_CHECKSEQUENCEVERIFY` in `EvalScript`, and `CheckSequence`. |
| R8 | [primitives/transaction.h, lines 76–99 and 283–289](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/transaction.h#L76-L99) | The sequence constants, `CURRENT_VERSION` and `MAX_STANDARD_VERSION`. |
| R9 | [consensus/consensus.h, lines 21–28](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/consensus.h#L21-L28) | `LOCKTIME_VERIFY_SEQUENCE` and `LOCKTIME_MEDIAN_TIME_PAST`. |
| R10 | [chain.h, lines 286–298](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.h#L286-L298), [chain.cpp, lines 113–147](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp#L113-L147) | `GetMedianTimePast` and `GetAncestor`. |
| R11 | [chainparams.cpp, lines 104–106, 121, 403–405 and 418](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L104-L121) | The CSV deployment and `fStrictChainId`, on mainnet and regtest. |
| R12 | [policy/policy.h, lines 88–109](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/policy/policy.h#L88-L109), [validation.cpp, lines 639 and 740–741](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L639) | The standard flags, and the two lock tests of mempool acceptance. |
| R13 | [tx_valid.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_valid.json), [tx_invalid.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_invalid.json), [script_tests.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/script_tests.json) | Core's corpora: the records with `CHECKSEQUENCEVERIFY`. |
| R14 | [miner_tests.cpp, lines 398–470](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/miner_tests.cpp#L398-L470) | Core's unit cases for sequence locks and the median-time cutoff. |
| R15 | [qa/pull-tester/rpc-tests.py, lines 129, 195 and 199](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/qa/pull-tester/rpc-tests.py#L129), with `qa/rpc-tests/bip68-112-113-p2p.py`, `bip68-sequence.py` and `bip9-softforks.py` | The three functional tests of CSV, which the test list of the pin turns off. |

The registry records most of these files: D36, D101, D110 and D114 (`validation.cpp`), D3, D4, D18, D35, D100, D28, D29 and D45.
A lane that cites a file without an identifier adds one, without a change to any pin.

### 2.2 Proposal documents

Design record 0007, section 5, gives each external document of a proposal an identifier in the *Proposal documents* table of SOURCES.md.
Stage 1 adds these rows.
None of them is a pin of Core, and none changes a pin:

| ID | Document | Revision or digest | Date |
| --- | --- | --- | --- |
| P1 | BIP 68, `bip-0068.mediawiki` in `bitcoin/bips` | Commit `6ac8c268704a479bdf65fad642c46d43cf19677e`, the last change of the file | 2026-05-28 |
| P2 | BIP 112, `bip-0112.mediawiki` in `bitcoin/bips` | Commit `24e96e870fffaa257b465ce1f0370c14aac588e8`, the last change of the file | 2026-01-12 |
| P3 | BIP 113, `bip-0113.mediawiki` in `bitcoin/bips` | The same commit as P2 | 2026-01-12 |
| P4 | [Discussion 3509 of `dogecoin/dogecoin`](https://github.com/dogecoin/dogecoin/discussions/3509), "Proposal: activate CSV with 1.15", by `patricklodder` | SHA-256 `f991a5409472fd30c565fc9a99b9974e638e39335918e51344ce78b553d79200` of the UTF-8 body. The GitHub API returned the body on 2026-11-20, with no edit time | 2024-04-04 |

A discussion has no commit, so P4 has a digest of its first post.
The digest does not cover the replies.
Decision 4 proposes this form for every source of that kind.

P4 proposes three steps.
The first is a version-bits layout that leaves the AuxPoW bits free, and the second is a choice of activation mechanism.
The third is the activation of BIP 68, BIP 112 and BIP 113 as Bitcoin has them.
It also names a possible later soft fork for a finer time unit.
This record covers the rules of the third step only.

Two more public texts give background, and the record registers neither.
[Issue 1798](https://github.com/dogecoin/dogecoin/issues/1798) (2021) planned CSV for a release 1.21.
The branch `1.21-dev` at commit `56b3c4994aa538a96f1828e967fc6ef60934e6ac` gates the rules with a height field, `consensus.CSVHeight`.
That field has the largest `int` value on mainnet, with the comment "Disabled on Dogecoin" (`src/chainparams.cpp`, line 76).

### 2.3 Which source decides

The Lean definitions follow Core's code at the pin (R1 to R10), which is Core's own implementation of the three BIPs.
The BIPs explain the rules.
Where a BIP and the pinned code differ, the definition follows the code, and the module documentation records the difference (design record 0007, section 5).
Stage 1 starts that list with two known items:

- The BIPs state a version-bits deployment with Bitcoin's parameters. The revision has a fixed activation height (section 5).
- BIP 68 chose the unit of 512 seconds for a block interval of 600 seconds. The pinned code keeps that unit, and Dogecoin's interval is 60 seconds. The revision keeps the unit of the code.

## 3. The rules at the pin

`csvActive` below means that `VersionBitsState` returns `THRESHOLD_ACTIVE` for the CSV deployment.
Core reads that state at two places, and each one turns on part of the rules.

### 3.1 BIP 113: the lock-time cutoff

`IsFinalTx` accepts a transaction with lock time 0 [R1].
It also accepts when the lock time is below a limit, or when every input has the sequence `SEQUENCE_FINAL`.
The limit is the block height for a lock time below 500,000,000, and a time cutoff otherwise.

`ContextualCheckBlock` selects the cutoff [R4].
Without `csvActive` the cutoff is the time of the block.
With `csvActive` the cutoff is the median time past of the predecessor.
A transaction that fails the test gives `bad-txns-nonfinal`.

### 3.2 BIP 112: the opcode

This section describes the opcode under the flags that `ConnectBlock` can set.
Those flags have neither `DISCOURAGE_UPGRADABLE_NOPS` nor `MINIMALDATA`, which change the opcode as policy.

With the flag `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` clear, opcode `0xb2` is `OP_NOP3` [R7].
With the flag set, the opcode checks in this order:

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item decodes as a `CScriptNum` of at most 5 bytes. A longer item gives `UNKNOWN_ERROR`. A negative operand gives `NEGATIVE_LOCKTIME`.
3. An operand with bit 31 set makes the opcode a NOP.
4. `CheckSequence` fails when the transaction version, as an unsigned 32-bit value, is below 2.
5. `CheckSequence` fails when bit 31 of the input's sequence is set.
6. Both values are masked with `0x0040ffff`. `CheckSequence` fails when their bits 22 differ, or when the masked operand is above the masked sequence.

A failure of steps 4 to 6 gives `UNSATISFIED_LOCKTIME`.
The opcode never pops its operand.
`ConnectBlock` sets the flag exactly when `csvActive` holds [R3, lines 1908–1909].

The flag is in `STANDARD_NOT_MANDATORY_VERIFY_FLAGS` [R12].
So `CheckInputs` reports a failure of this opcode alone as `non-mandatory-script-verify-flag`, with DoS score 0 [R6].
The block is still rejected.

### 3.3 BIP 68: sequence locks

`ConnectBlock` tests each transaction that is not a coinbase, after it finds the inputs and before it counts signature operations [R3, lines 1948–1959].
It reads the height of each spent coin from the `CCoins` entry of the coin's transaction ID.
`CalculateSequenceLocks` then computes a pair (`nMinHeight`, `nMinTime`), which starts at (-1, -1) [R2].

The rule applies to a transaction only when two conditions hold.
`nLockTimeFlags` has `LOCKTIME_VERIFY_SEQUENCE`, which `ConnectBlock` sets exactly with `csvActive`.
The version, as an unsigned 32-bit value, is at least 2.
Then each input whose sequence has bit 31 clear adds a constraint. Let `n` be the low 16 bits of the sequence and `c` the height of the spent coin:

- Bit 22 clear: `nMinHeight` becomes the larger of itself and `c + n - 1`.
- Bit 22 set: `nMinTime` becomes the larger of itself and `t + 512 * n - 1`. Here `t` is the median time past of the ancestor at height `max(c - 1, 0)`.

`EvaluateSequenceLocks` fails when `nMinHeight` is at least the height of the block.
It also fails when `nMinTime` is at least the median time past of the predecessor.
A failure gives `bad-txns-nonfinal` with DoS score 100.

Three consequences follow from the text of R2 and R3:

- A coin that the same block created has the height of the block. A height lock with `n` of 1 or more then fails, and `n` equal to 0 passes.
- Version -1 is `0xffffffff` as an unsigned value, so the rule applies to it.
- The time rule reads up to 11 ancestor times at the height of each spent coin, at any depth of the chain [R10].

### 3.4 The rules as policy

At the pin, mempool acceptance applies both lock-time flags as policy [R12].
`CheckFinalTx` gives `non-final` (line 639), and `CheckSequenceLocks` gives `non-BIP68-final` (lines 740 and 741).
`STANDARD_SCRIPT_VERIFY_FLAGS` holds the CSV flag.
The wallet of the pin writes transaction version 1, and version 2 is standard [R8].

The facts of this section describe node policy, not consensus.
A block can hold a transaction that the mempool of the pin refuses.
Section 10.3 measures how often that happened.

### 3.5 Why the rules never run on mainnet

The CSV deployment of mainnet started on 1 May 2016 and timed out on 1 May 2017 [R11].
Design record 0007, section 3, fact 3, shows that no mainnet or regtest header can signal.
The theorem `csv_never_lockedIn` proves that the state is never `LOCKED_IN` or `ACTIVE`.
Its domain is a mainnet header chain from the genesis block on which every header passed the header checks (design record 0010, section 4).

The same fact turns Core's functional tests off.
Regtest has `fStrictChainId` true, so the three tests of R15 cannot activate CSV, and the test list comments them out.

## 4. What DogeLib has and what is missing

| Part | State in DogeLib at `3a8401b` |
| --- | --- |
| The opcode (section 3.2) | Defined. `Script.checkSequenceStep` and `sequenceSatisfied` follow R7, and `supportedFlags` holds the CSV flag. The comparison with Core includes 940 targeted CSV requests and the CSV records of `script_tests.json` ([docs/oracle.md](../oracle.md#the-comparison)). |
| The cutoff (section 3.1) | Defined. `Block.contextualCheckBlockBody` takes `csvActive` and the median time past of the predecessor. The oracle derives `csvActive` from the version-bits state, which is never `ACTIVE` on the compared blocks. |
| Median time past | Defined. `Work.medianTimePast` gives the value for the first entry of a view. |
| Coin heights | Defined. `Block.Coin` has the height and the coinbase flag of its `CCoins` entry. |
| The flag in `ConnectBlock` | Missing. `connectScriptFlags` never sets the CSV flag. With `csvActive` true, `connectBlock` returns the result `csvActive`, which is outside the model. |
| Sequence locks (section 3.3) | Missing. No definition of `CalculateSequenceLocks` or `EvaluateSequenceLocks` exists. `DogeLib.Block.Connect` documents why the baseline needs none. |
| Ancestor times at a coin's height | Missing. `ValidateContext.view` is a contiguous view from the predecessor, and nothing reads it at the depth of a coin. |
| A revision of block rules | Not built. Design record 0011, decision 11, defines `connectBlockWith` and `validateBlockWith` for a revised spend check. Section 6 states what they lack for these rules. |
| An unsupported reason of a proposal | Defined for Script. The result types of the framework take a type `υ` of unsupported reasons, and a map `embedU : Unsupported → υ` for the baseline reasons (issue #122, pull request #176). The block level has no such parameter. |

## 5. Identity and activation

**Name.** The revision is `DogeLib.Proposals.RelativeLockTime`.
The name describes the rule and names no release, as design record 0007, section 5, requires.

**One activation for three rules.**
Core turns on the three rules with one state.
The revision has one `Activation` value (design record 0007, section 7.2), and its rule-level definitions take one argument `active : Bool`.

**A fixed height.**
The record proposes the fixed-height model of design record 0007, decision 4, for four reasons:

1. The pinned deployment is the baseline, and it never activates on mainnet (section 3.5). So no activation rule of the pin is left to copy.
2. P4 leaves the mechanism open between BIP 9 with another bit layout and BIP 8. DogeLib has no ground to choose for Dogecoin.
3. On one chain, a mechanism whose active state is terminal gives a first active height. Every theorem of section 9 holds for every `Activation`, so it holds for that height.
4. The branch `1.21-dev` already has the form of a height field (section 2.2).

The revision is active on no network, so no default `Activation` exists.
A signalling model stays the later work of design record 0007, section 7.4.
Reason 3 covers one chain only. Two branches of a fork can reach `ACTIVE` at different heights under signalling, and the fixed-height model does not describe that case.

**Mainnet only.**
`validateBlock` and `connectBlock` specify mainnet.
The revision reads `Activation.height .mainnet` alone.

**Where the rules apply.**
A block is *applicable* when two conditions hold.
Its view of the predecessor is not empty.
The hash of its own header is not the hash of the mainnet genesis block.
The revised rules apply only to an applicable block, and for every other block the revision is inactive at every activation height.

`validateBlock` runs no header check on a header with the genesis hash, and `connectBlock` connects none of its transactions.
So no check gives the time order that the cutoff needs (section 6.4), and no transaction of such a block reaches the two other rules.
The block at height 1 is applicable: its predecessor is the genesis block, and its own hash is another hash.

Core's cutoff reads `pindexPrev->GetMedianTimePast()` [R4, line 3135], and `EvaluateSequenceLocks` asserts a predecessor [R2, line 373].
At the pin, `VersionBitsState` of a null predecessor is `DEFINED`, so Core never reaches either line without one.

## 6. The block level: design record 0011 and its extensions

### 6.1 The layer that this record builds on

Design record 0011, section 10.1 and decision 11, defines the block level of a proposed revision.
This record defines no second framework. It uses that layer and states each change that the three rules need.

The layer has these parts:

- `connectBlockWith` and `validateBlockWith` in the `Proposals` library, with the spend check as a parameter. They follow option M2 of design record 0007, so no baseline file changes.
- A generic script error, with an embedding of the baseline errors.
- The second script check: a failed check runs again with the reduced flags and the same `active`, and the second run classifies the failure.
- The baseline count of signature operations. The layer changes the spend check and nothing else.
- Four targets: `connectBlockWith_baseline`, `validateBlockWith_inactive`, `validateBlockWith_congr` and `connectBlockWith_restricts`.
- A `ProposalExports` library and its executable, which answers `block.validate` with a `revision` argument (decision 10 of that record).

Section 12 of that record excludes a revision of a rule outside Script.
Its section 10.4 says that a run revises the spend check alone.
Two of the three rules here are outside Script, so the layer needs the extensions below.

### 6.2 What the layer can state today

| Rule | With the layer as design record 0011 defines it |
| --- | --- |
| BIP 112, the opcode | Acceptance: yes. The revised spend check is the baseline check with the CSV flag added to its flags. Reject reason: no. The second run adds the flag again, so it fails again, and the reason is `mandatory-script-verify-flag-failed`. Core removes the flag in its second run, and gives `non-mandatory-script-verify-flag` (section 3.2). |
| BIP 68, sequence locks | No. The test reads the transaction, the heights of its coins and the view. It is not a check of one input's script. |
| BIP 113, the cutoff | No. The cutoff is an argument of `contextualCheckBlockBody`, which `validateBlock` takes from its context. |

The reason of the first row matters only for section 10.2, which compares reasons with Core's own code.

### 6.3 The extensions

Each extension is a change to the layer of design record 0011.
Each new parameter has a baseline value, and with the baseline values the layer is the layer of that record.
So the two examples and their theorems keep their statements.

**E1: the flags of a block.**
`connectBlockWith` takes the flags of a block as a parameter, `scriptFlags : Nat → UInt32`, with the baseline value `connectScriptFlags`.
The second script check removes the flags that are not mandatory from that value, as the baseline does.
`RelativeLockTime` adds the CSV flag when `active` is true, and uses the baseline spend check.
Core's reason of section 3.2 then follows with no added rule.

**E2: a test of one transaction.**
`connectBlockWith` takes a test with the height, the index, the transaction and its spent coins.
It runs the test for each transaction that is not a coinbase.
The test follows the lookup of the inputs and precedes the count of signature operations [R3, lines 1948–1959].
The baseline value accepts every transaction.
`RelativeLockTime` supplies `sequenceLocks` (section 7.2).

**E3: the arguments of the body check.**
`validateBlockWith` takes the two lock-time arguments of `contextualCheckBlockBody` from the revision: `csvActive` and the median time past.
The baseline values are those of the context.
`connectBlockWith` has no `csvActive` result, because a revision that sets the argument defines the rules that the baseline leaves out.
`RelativeLockTime` passes `active` and the median of the view.

So the cutoff needs no copy of `contextualCheckBlockBody`. The revision runs the baseline definition with `csvActive` true, which is Core's own dormant branch.

**E4: errors and unsupported reasons of a proposal.**
The layer is generic in the script error.
E2 needs an error that is not a script error, and it needs results that are not rejections.
The Script framework has a type parameter `υ` for unsupported reasons, beside the error parameter `ε` (issue #122, pull request #176).
Its `ofBaseline` maps take `embed : ScriptError → ε` and `embedU : Unsupported → υ`.
The block level follows that form:

```text
inductive BlockOutcome (ε υ α : Type) where
  | ok (a : α)
  | rejected (error : ε)
  | unsupported (reason : υ)
```

`ConnectBlockError` holds Core's rejections and six results outside the model, and `isRejection` separates the two kinds.
So the block level has two maps of that one type, in the roles of `embed` and `embedU`.
A baseline error with `isRejection` true becomes `rejected` through the first map, and every other error becomes `unsupported` through the second.
A script result inside a block result keeps the two Script maps.
A proposal with its own errors `E` and reasons `U` uses sums with the baseline values under `Sum.inl`.
A proposal without its own reasons uses the identity, as in the Script framework.

`RelativeLockTime` adds one error and three reasons:

| Kind | Name | Meaning |
| --- | --- | --- |
| Error | `sequenceLocks index` | The transaction at `index` fails section 3.3. The reason is `bad-txns-nonfinal`, with DoS score 100 and the code `REJECT_INVALID`. |
| Reason | `ancestorOutsideView` | A time lock needs ancestor times below the supplied view. |
| Reason | `coinAboveBlock` | A time lock reads a coin whose height `c` is above the height `h` of the block. For `c = h + 1`, Core reads the median time of the block itself. For a larger `c`, `GetAncestor` returns null, and Core dereferences it [R2, line 348]. The revision excludes both cases as a limit of its input. |
| Reason | `heightOutOfDomain` | A height is too large for Core's `int` sums (section 7.2). |

A reason is never a rejection.
It says that the specification cannot give Core's verdict, and `RestrictsAcceptance` reads accepted results only.

The names and the exact types are proposals.
The lane can group the parameters of E1 and E2 with the spend check in one record.
Section 9.1 fixes what the types must support.

### 6.4 Restriction with the extensions

`connectBlockWith_restricts` of design record 0011 has one hypothesis: the spend check restricts acceptance.
With the extensions, the hypothesis has four conditions.
A revision *restricts* the baseline when they hold at every height:

1. If the revised spend check accepts an input under the revised flags, the baseline check accepts it under the baseline flags.
2. The revised flags and the baseline flags agree on `SCRIPT_VERIFY_P2SH`, because the count of signature operations reads that flag.
3. The baseline value of the test of E2 accepts everything, so this condition holds for every revised test.
4. For `validateBlockWith`: the revised cutoff is at most the baseline cutoff.

Every statement takes the baseline with `csvActive` false in its context.
With `csvActive` true, the baseline `connectBlock` returns a result outside the model, and no restriction holds.

The conclusion does not change.
If the revision accepts a block, the baseline accepts it with the same coin set and the same list of coin changes.
That equality is the state part of the legacy projection.

Condition 4 is not free for the cutoff of section 3.1.
It needs that the median time past of the predecessor is at most the time of the block.
`validateBlock` runs `contextualCheckBlockHeader` first, which rejects a block whose time is not above that median [R5].
So the lift for `validateBlockWith` needs no added hypothesis for an applicable block.
A header with the genesis hash skips that check, which is one reason for the limit of section 5.
The revision computes the median from the same view that the header check reads, not from a separate argument.

### 6.5 The request and the report

The proposal executable of design record 0011 answers for this revision with its own argument:

```text
"revision": {"name": "RelativeLockTime", "variant": null, "activation_height": 1}
```

The `revised` object of a block record names the rule of a rejection: the cutoff, the opcode or a sequence lock.
For a result outside the model it holds the reason of E4, and the block is then not a changed block.
`dogelib-oracle` and the `Exports` library get no operation of the revision.

### 6.6 Layout and import boundary

```text
DogeLib/Proposals/RelativeLockTime.lean         the revision
DogeLib/Proposals/RelativeLockTime/             SequenceLocks.lean, Block.lean
DogeLib/Proposals/RelativeLockTime/Proofs/      its theorems
tests/KnownAnswers/Proposals/                   its known answers
```

The extensions E1 to E4 change the modules that design record 0011 adds for its layer.
No baseline library imports a module of the revision.
The gate *Import boundaries* and its self-test already check the prefix `DogeLib.Proposals`.

### 6.7 Order of work

Design record 0011 builds its layer in its stage 6, which follows its Core pass.
Stage 1 of this record needs the two definitions and their agreement theorem, and it needs nothing of the snapshots.
Decision 7 proposes that the lane for the definitions of that stage 6 can run first, apart from the report on the ranges.
Stage 1 here then adds E1 to E4 to those definitions.

## 7. The revision in Lean

### 7.1 The three rules

With `active` false, each part below has its baseline value.
With `active` true:

| Rule | Extension | Value |
| --- | --- | --- |
| BIP 113 | E3 | `csvActive` true, with the median time past of the view. |
| BIP 112 | E1 | `connectScriptFlags height` with the CSV flag added. |
| BIP 68 | E2 | `sequenceLocks` of section 7.2. |

Each rule-level definition applies its rule only when `active` is true and the block is applicable (section 5).
The block-level definition takes `active` from the activation at the height on mainnet.

### 7.2 Sequence locks

`sequenceLocks` follows R2 with unbounded integers.
It takes the view, the height of the block, the transaction and the spent coins.
It returns the pair of section 3.3 and applies the test of `EvaluateSequenceLocks`.

The ancestor at height `a` is the view entry at depth `height - 1 - a`.
Its median time past is `Work.medianTimePast` of the view from that entry.
A view that is too short for that read gives `ancestorOutsideView`.
The revision reads no ancestor time for a transaction without a time lock.

Core adds in `int` and `int64_t`.
The largest term of a height lock is `c + 65535 - 1`, and the largest term of a time lock adds `512 * 65535` to a 32-bit time.
The second sum always fits `int64_t`.
The first fits `int` when `c` is below `2^31 - 65535`. A larger height gives `heightOutOfDomain`.

### 7.3 Request arguments

A time lock on an old coin needs a view as deep as the coin.
The replay from the genesis block has that view, because its view is the whole chain below the block.
A range that starts above the genesis block (design record 0011) needs a longer `chain` argument for such a block, or it gets `ancestorOutsideView`.
Section 10.3 counts those results, and it never counts one as a changed verdict.

## 8. Compatibility class

The revision is a soft fork with the identity legacy projection (design record 0007, section 8.4).
It changes no encoding, and section 6.4 gives an equal coin set for every accepted block.
The record proposes a third label beside *Script-local* and *header-local*:

- *Block-level*: a theorem about `validateBlock` or `connectBlock` for one block on a supplied coin set and view, or about a list of blocks through `connectChain`.

A block-level theorem is still not a claim about the network.
It holds for mainnet rules, for a supplied view and coin set, and inside the domains of design record 0010, section 3.
It says nothing about fork choice, convergence or liveness.

## 9. Theorem targets

The names are proposals.
Each theorem states its domain and hypotheses in its doc comment.
No target assumes a cryptographic property. The signature verifier is a parameter of every statement.

### 9.1 Framework

The first four rows are the targets of design record 0011, section 10.1, with the change that the extensions make to each statement.
The last two rows are additions.

| Target | Statement with the extensions |
| --- | --- |
| `connectBlockWith_baseline` | With the baseline spend check and the baseline values of E1 and E2, `connectBlockWith` equals the embedded result of `connectBlock`. The embedding is the pair of maps of E4. The context has `csvActive` false. |
| `validateBlockWith_inactive` | As in design record 0011, for a revision whose values of E1 to E3 are the baseline values when `active` is false. |
| `validateBlockWith_congr` | The hypothesis also requires that the values of E1 to E3 agree with the baseline on the block. `relativeLockTime_eq_of_untouched` is the instance for this revision. |
| `connectBlockWith_restricts` | The hypothesis is conditions 1 to 3 of section 6.4, and the baseline context has `csvActive` false. The conclusion is that of design record 0011. |
| `validateBlockWith_restricts` | New. The same for `validateBlockWith`, with condition 4. The revised values of E1 to E3 are the baseline values on a block that is not applicable. |
| `connectChainWith_restricts` | New. The lift of `connectBlockWith_restricts` to a list of blocks, by induction. An accepted list gives the same final coin set under the baseline, with `csvActive` false in each baseline context. The statement covers connection alone, so it has no part for the cutoff. Design record 0011 names this step and does not require it. |

### 9.2 Rule level

| Target | Statement |
| --- | --- |
| `isFinalTx_mono` | If `isFinalTx tx height t` holds and `t ≤ t'`, then `isFinalTx tx height t'` holds. |
| `contextualCheckBlockBody_csv_restricts` | Suppose that the median time past `m` is at most the time of the block. If `contextualCheckBlockBody` accepts with `csvActive` true and `m`, it accepts with `csvActive` false. The other arguments are equal. |
| `csvFlagStep_restricts` | For every checker and flag set `f`, the baseline step with `f` and the CSV flag restricts the baseline step with `f` (`Restricts` of design record 0007). |
| `csvFlag_soft_fork_local` | Script-local. If `verifyLegacySpend` accepts an input with `f` and the CSV flag, it accepts the input with `f`. For every verifier, input context and supported `f`. |
| `csv_accepted_iff` | Script-local. Let the `scriptPubKey` push an operand `n` of at most 5 bytes, run `0xb2`, then run a script without `0xb2`. Let the `scriptSig` have no `0xb2`. With the CSV flag, the spend is accepted exactly when three conditions hold. It is accepted without the flag. `0 ≤ n` holds. Bit 31 of `n` is set, or `sequenceSatisfied version sequence n` holds. |
| `sequenceLocks_inactive` | With `active` false, or with a version below 2 as an unsigned value, `sequenceLocks` accepts every transaction. |
| `sequenceLocks_iff` | The characterization of sequence locks. Take `active` true, a version of at least 2, and a result that is not unsupported. `sequenceLocks` accepts exactly when each input with bit 31 clear meets its lock. With bit 22 clear the lock is `c + n ≤ height`. With bit 22 set it is `t + 512 * n ≤ m`. The symbols are those of section 3.3, and `m` is the median time past of the predecessor. |
| `sequenceLocks_fits` | Under the height bound of section 7.2 and 32-bit times, each sum of R2 fits its C++ type. |

`csv_accepted_iff` follows the form of `example_accepted_iff`.
Stage 2 fixes its exact domain, including the push forms of the operand and the P2SH case.

### 9.3 Block level

Write `revised active` for the revised `validateBlock` with the Boolean of section 7.1, and `baseline` for `validateBlock` with `csvActive` false.
The context holds the verifier, the two check flags, the view, the times, the coin set and the block.

| Target | Statement |
| --- | --- |
| `relativeLockTime_inactive_eq` | `revised false` equals the embedded `baseline` result, for every context. The equality covers each rejection and each result outside the model. |
| `relativeLockTime_restricts` | If `revised active` accepts a block with a result, `baseline` accepts it with the same result. For every `active` and context, applicable or not. |
| `relativeLockTime_strict` | Three witnesses, one for each rule: a context where `baseline` accepts and `revised true` rejects with the error of that rule. |
| `relativeLockTime_use` | Three witnesses: a context where `revised true` accepts and the rule runs. The first case has a time lock time below the median cutoff. The second has an executed `0xb2` with a satisfied operand. The third has a version 2 input with a met height lock of `n ≥ 1`. |
| `relativeLockTime_softFork` | The framework's `SoftFork` for `revised` and `baseline`, from the four targets above. Block-level. |
| `relativeLockTime_activation` | For every `Activation`: below the activation height, or with no height, the block-level revision equals `baseline`. From `Activation.isActive_lt` and `none_inactive`. |
| `relativeLockTime_chain` | Block-level, for connection alone. Take a list of blocks with their contexts. If the revised connection accepts the list from a coin set, `connectChain` accepts it from that set to the same final set. Each baseline context has `csvActive` false. For every `Activation`. The statement covers the flag and the sequence locks. `connectChain` runs no body check, so the cutoff has the one-block target alone. |
| `relativeLockTime_eq_of_untouched` | Take a block in which no rule has an object. No transaction has a time lock time from the median cutoff to below the block time. No transaction that is not a coinbase has both a version of at least 2 and an input with bit 31 clear. No `scriptSig`, spent `scriptPubKey` or P2SH redeem script holds an instruction `0xb2`. Then `revised true` equals the embedded `baseline` result. A block that is not applicable needs none of the three conditions. |
| `relativeLock_enforced` | Block-level. Suppose that `revised true` accepts an applicable block. Suppose that an input of a transaction that is not a coinbase spends a coin whose script has the form of `csv_accepted_iff`. Let the operand `n` have bits 22 and 31 clear, and let `d` be its low 16 bits. Then the height of the block is at least the height of the coin plus `d`. |

`relativeLock_enforced` is the property that a user of the rule wants.
It joins the opcode and the sequence lock.
The opcode bounds the sequence of the input, and the sequence lock bounds the depth of the coin.
A property of this kind answers the second question of [DogeLib in practice](../in-practice.md#two-questions).
Without the two conditions on the block and the transaction, no check of the rule runs, and the conclusion can fail.
The time form of the target has the same conditions and the same shape, with ancestor times in the place of heights.

A second target of that kind is optional in stage 3.
`sequenceLocks_zero` states that a lock with `n` equal to 0 always passes.
Its time form needs that the median time past does not decrease along the view.
That holds when each entry of the view passed the `time-too-old` test, which becomes a stated hypothesis.

### 9.4 Hypotheses and where Core enforces them

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The median time past of the predecessor is at most the block time. | `contextualCheckBlockBody_csv_restricts` | `ContextualCheckBlockHeader`, `time-too-old` [R5]. `validateBlock` runs it first, so the block-level targets do not assume it. |
| The block is applicable. | Every active rule | Section 5, as part of the definition and not as a hypothesis of a restriction target. Core reaches the code only with a non-null `pindexPrev`. |
| The height bound of section 7.2. | `sequenceLocks_fits` | Not enforced as a rule. A coin height is at most the height of a block of its chain, and mainnet heights are far below the bound. |
| The coin height is at most the block height. | Time locks | Not enforced as a rule. It holds for a coin set that a replay built. A supplied coin set can break it, and the result is then `coinAboveBlock`. Core has a defined result for a coin one block above (section 6.3), which the revision does not give. |
| The domain of design record 0010, section 3. | Every block-level target | As in that record. The revision adds no sum of amounts. |

The targets add no axiom and no trust assumption.
SOUNDNESS.md gets a subsection under *What the proofs say* for the block-level claim, with these hypotheses.

## 10. Evidence

Design record 0007, section 9, says that no Core behaviour exists for a proposal.
This revision differs in one respect: Core's code of the rules exists at the pin, and only its activation state never occurs.
The evidence has three parts, and each part has its own label.

### 10.1 Known answers

Known answers run through the compiled code in `lake test`.
No expected value comes from DogeLib.

| Source | Content | Use |
| --- | --- | --- |
| `script_tests.json` [R13] | 12 records that hold `CHECKSEQUENCEVERIFY`. | The Script corpus already holds them. Stage 2 lists each one as run or as unsupported. A record with a flag outside `supportedFlags`, such as `MINIMALDATA`, is unsupported and is no evidence. |
| `tx_valid.json`, `tx_invalid.json` [R13] | 30 and 16 records with the flag `CHECKSEQUENCEVERIFY`. Core's tests run `VerifyScript` on each input with the flags of the record. | Stage 2 states which existing gate runs each record's scripts, and adds the others as cases of `verifyLegacySpend`. It lists a record with an unsupported flag as unsupported. |
| `miner_tests.cpp` [R14] | Cases of `SequenceLocks` and `IsFinalTx` on a test chain: a height lock, a time lock, and the cutoff one second apart. | The values depend on the test chain. Stage 3 derives cases of the same form by hand, and cites each line. |
| The functional tests [R15] | Tables of versions, sequences and operands, with the expected verdict of a node. | A source of hand-made cases only. The tests do not run at the pin (section 3.5), and this lane uses no node. |
| P1, P2 and P3 | The rules in prose and the reference code of each BIP. | Expected values derived by hand, on each side of every boundary of sections 3.1 to 3.3. |

The hand-made cases include at least these boundaries:

- A height lock that is met exactly, and one that is one block short.
- A time lock that is met exactly, and one that is one second short.
- A coin of the same block with `n` of 0 and of 1.
- Versions 1, 2 and -1.
- A sequence with bit 31 set and with bit 22 set, and bits outside the mask `0x0040ffff`.
- A coin at height 0 and at height 1, for `max(c - 1, 0)`.
- A lock time equal to the median cutoff, one below it, and equal to the block time.

### 10.2 Comparison with Core, CSV forced active

The harness already writes the version-bits cache: it seeds `THRESHOLD_FAILED` after the CSV timeout (design record 0010, decision 3).
The record proposes one more request argument, `force_csv_active`, for `block.contextual_check_body` and `block.validate` in the Core harness.
With it, the harness seeds `THRESHOLD_ACTIVE` for CSV at the boundary that each applicable block reads.
Core's own `ContextualCheckBlock` and `ConnectBlock` then run the lines of R3 and R4.
No line of Core's source changes.

The seed is set for one block and cleared after it.
Below height 10,080 the aligned boundary is null, which is also the cache key of a block without a predecessor.
A seed that stays there makes Core dereference a null predecessor at line 3135.
So the harness seeds nothing for a block that is not applicable (section 5), and such a block gets the baseline result on both sides.

The two seeds differ in kind.
`csv_never_lockedIn` shows that `FAILED` is Core's own result on a mainnet chain.
`ACTIVE` is a state that no mainnet chain reaches, so the run shows what Core's code does in a state that Core never enters.

**The Lean side.**
The proposal executable of design record 0011 answers the same requests, with the `revision` argument of section 6.5.
Its activation height is at or below the first block.
The comparison reads the `revised` object of each block record.
`dogelib-oracle` refuses both arguments with a request error.

**Label.**
COVERAGE.md records this evidence only in its section *Proposed revisions*.
Each entry starts with the words "Core at `e0a1c15` with the CSV state forced to `ACTIVE`".
It ends with the sentence "This state does not occur on mainnet (`csv_never_lockedIn`)."
The entry never has the words "Core comparison" alone, and no baseline row cites it.
`docs/oracle.md` describes the argument under the same label.
SOUNDNESS.md records the seed as a harness input with no theorem behind it.

**Content.** The comparison covers verdict, reject reason, DoS score, reject code and coin digests, as `block.validate` does:

1. Heights 0 to 10,000 of mainnet in one request. The harness runs each block twice on the state before it: once unchanged, and once with CSV forced active. Only the unchanged run carries the coin set and the chain to the next block, as the proposal executable does (design record 0011, section 10.2). The two programs must agree on the forced result of each block. The run does not require acceptance.
2. Made blocks for each boundary of section 10.1. Each block stands on a committed block and has no proof of work, as in case 3 of design record 0011, section 10.3.
3. Each new reason at least once: `bad-txns-nonfinal` from the cutoff, `bad-txns-nonfinal` from a sequence lock, and `non-mandatory-script-verify-flag` from the opcode.
4. A self-test: the comparison fails when the Lean side runs with the revision inactive on a block of item 2.
5. The genesis block with the argument: both programs give the baseline result. The block at height 1 with the argument: Core runs with CSV active, and the two programs agree.

Agreement shows that the Lean revision equals Core's dormant code on those requests.
It does not show that the rules are right for Dogecoin, and it is not evidence about mainnet.

### 10.3 Historical impact

The question is: which blocks, transactions and outputs of mainnet history get another verdict under the revision?
Design record 0011, section 10, defines the run, and this record adds counts to its report.
Each block is judged on the historical state before it, with the revision active from height 1.
A *changed block* is a block whose two verdicts differ.
`relativeLockTime_restricts` shows that every change goes from accepted to rejected.

The run reports more than changed blocks for this revision:

| Count | Meaning | Needs coins |
| --- | --- | --- |
| Cutoff transactions | A time lock time from the median cutoff to below the block time, with an input that is not final. | No |
| Sequence candidates | A version of at least 2 and an input with bit 31 clear. | No |
| Sequence failures | A sequence candidate that fails section 3.3. | Yes |
| Opcode spends | An input whose run executes `0xb2`, with the verdict of the flag. | Yes |
| Opcode outputs | A created `scriptPubKey` that holds the instruction `0xb2`, and whether the range spends it. | No |
| Unsupported | A block with a result outside the model, by reason. | Yes |

An opcode output that stays unspent is an output whose spend the revision could later refuse.
The count cannot see a P2SH redeem script before its spend.

**Expected values.**
A separate script lists the *candidate blocks* before each run.
It reads the blocks, the headers and the scripts of the spent coins.
A candidate has a cutoff transaction, a sequence candidate, or a script with the instruction `0xb2`.
The scripts are each `scriptSig`, each spent `scriptPubKey`, and the last push of a `scriptSig` that spends a P2SH output, parsed as a script.

In a replay from the genesis block, each spent script is in an earlier block.
A range above the genesis block takes the spent scripts from the coins of its range request.
A spend whose script the script cannot find makes its block a candidate.
`relativeLockTime_eq_of_untouched` shows that every changed block is a candidate.
The lane commits the list before the run.
The record predicts no count.

**Ranges.**

| Range | Run | Depends on |
| --- | --- | --- |
| The 11,018 blocks of `block.contextual_check_body` | The cutoff count alone, in CI. | Stage 1 |
| Heights 0 to 10,000 | Every count, in CI. | Stage 3 |
| Heights 0 to 145,000 | Every count, in one recorded run outside CI, on one core at low priority. | Stage 3 |
| The ranges of design record 0011 | Every count, when that record's snapshots exist. | Stages 2 and 6 of that record |

The run to height 145,000 costs about two replays of the baseline, which is about 34 hours of the oracle at the recorded speed.

A result is a statement about the blocks of the ranges.
It says nothing about unconfirmed transactions, such as a signed transaction that waits for its lock time.
An empty report is not a compatibility proof. The proofs are the targets of section 9.

## 11. Stages and exit conditions

Each stage is one lane with one pull request.
A stage that extends the rules of the proposal has `!` in its title, as design record 0007, section 5, requires.
Until stage 3 merges, COVERAGE.md labels the proposal as partial and names the rules that it has.

### Stage 1: the extensions of the layer and BIP 113

The stage follows the definitions of design record 0011 (section 6.7).
The change for issue #122 is in `main` (pull request #176).
It adds the extensions E1 to E4 to that layer, and the revision with the cutoff alone.
It adds P1 to P4 to SOURCES.md, and the label of section 8 and the rows to COVERAGE.md.

1. The targets of section 9.1 are proved with the extensions, except that `connectChainWith_restricts` may wait for stage 3. The examples of design record 0011 keep their theorems.
2. `isFinalTx_mono`, `contextualCheckBlockBody_csv_restricts`, and the inactive equality, the restriction and both witnesses for the cutoff are proved.
3. Known answers cover the three cutoff boundaries of section 10.1.
4. The harness has `force_csv_active` for `block.contextual_check_body`. The comparison of section 10.2 agrees on the 11,018 blocks and on made blocks for the cutoff. Its self-test fails as item 4 requires.
5. The cutoff count runs on the 11,018 blocks, with the candidate list committed first.
6. The import check passes, and `check-decls` reaches every new module.

### Stage 2: BIP 112

The stage adds the flag to the revision.

1. `csvFlagStep_restricts`, `csvFlag_soft_fork_local` and `csv_accepted_iff` are proved, and the block-level restriction covers the flag.
2. The strictness and use witnesses of the opcode are proved at the block level. If the lane proves them at the spend level, the pull request gives the reason (section 14).
3. Each record of R13 with the flag and with supported flags alone has a named gate that runs its scripts. The pull request lists every other record as unsupported, with its flag.
4. The harness has `force_csv_active` for `block.validate`. Made blocks reach `non-mandatory-script-verify-flag` through the opcode, and the two programs agree.

### Stage 3: BIP 68 and the block-level soft fork

The stage adds `sequenceLocks`, the reads of the view and the three reasons of section 6.3.

1. `sequenceLocks_inactive`, `sequenceLocks_iff` and `sequenceLocks_fits` are proved.
2. Every target of section 9.3 is proved. `relativeLockTime_softFork` has the label *block-level* in COVERAGE.md.
3. Known answers cover every boundary of section 10.1.
4. The comparison of section 10.2 is complete: items 1 to 4, with each new reason.
5. SOUNDNESS.md has the subsection of section 9.4, and `docs/in-practice.md` has a worked example of the revision.
6. A model read of `sequenceLocks` against R2 is recorded under `docs/reviews/`, as design record 0010 requires for a new definition.

### Stage 4: the historical counts

1. The candidate script and its list are committed before each run.
2. The run of heights 0 to 10,000 is a CI gate. Every changed block is a candidate, and every change goes from accepted to rejected.
3. The run of heights 0 to 145,000 is recorded with its builds, counts and time.
4. COVERAGE.md records each report in *Proposed revisions*, with the heights and the limits of section 10.3.

The ranges above height 145,000 follow when the snapshots of design record 0011 exist.
They are not an exit condition of this record.

### Gates

Each stage adds its commands to the gate table of AGENTS.md.
The known answers run in `lake test`.
The forced-active comparison and the count of heights 0 to 10,000 run in the `core` workflow.
The run to height 145,000 is a recorded gate outside CI.

## 12. Excluded

- Witness data, SegWit, and every rule about an AuxPoW payload transaction.
- The choice of an activation height or mechanism, version-bits layouts, BIP 8 and BIP 9, and signalling (design record 0007, section 7.4).
- A finer time unit or any other change of the rules of P1 to P3. Such a rule is another proposal with its own name.
- The mempool: `CheckSequenceLocks`, `LockPoints`, `CheckFinalTx` and standardness. Section 3.4 reports them as facts only.
- Testnet and regtest block rules, as in design record 0010.
- Fork choice, reorganization, convergence and liveness.
- A node, a regtest network and a patched Core build.
- An operation of the revision in `dogelib-oracle` or `Exports`.
- Rust extraction and refinement of the revision.
- The merits of the proposal.

## 13. Decisions

**Date:** 2026-11-20. **Decision maker:** Maintainer.
The maintainer accepted each proposal as its status states.

| Number | Topic | Proposal | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | Form of this scope | A design record of its own, 0012. Design record 0007 stays frozen, and this record builds on its decisions. | An amendment of design record 0007, sections 8.2 and 8.3. | Accepted |
| 2 | Name | `DogeLib.Proposals.RelativeLockTime`, one proposal for the three rules. | Three proposals, one for each BIP. A name with "CSV". | Accepted |
| 3 | Deciding source | Core's code of the rules at the pin (R1 to R10). The BIPs explain, and the module documentation lists each difference (section 2.3). | The BIP text decides, and the code is a comparison. | Accepted |
| 4 | Proposal documents | P1 to P3 by the commit of `bitcoin/bips` that last changed each file. P4 by URL, author, date and the SHA-256 of its first post. Issue 1798 and `1.21-dev` are background and get no identifier. | A committed copy of each text. Identifiers for the background texts too. | Accepted |
| 5 | Activation | One fixed height on mainnet through `Activation`, for the three rules together, with no default. Inactive for a block that is not applicable: one with an empty view, or one whose own header has the genesis hash (section 5). | One Boolean for each rule. A signalling model first. | Accepted |
| 6 | Block level | The layer of design record 0011, decision 11, and no second framework. The extensions E1 to E3 are changes to that layer: the flags of a block, a test of one transaction, and the arguments of the body check (section 6.3). | The layer unchanged: the opcode as a revised spend check with another reject reason than Core's, and no sequence locks or cutoff. A copy of `connectBlock` for this proposal. | Accepted |
| 7 | Order with design record 0011 | The definitions and the agreement theorem of that record's stage 6 can land before its Core pass. Stage 1 here follows them (section 6.7). | Stage 1 waits for the whole of that stage 6. Stage 1 builds the definitions itself, under that record's decision 11. | Accepted |
| 8 | Results at the block level | Extension E4: a block error and an unsupported reason of the proposal, in the form of issue #122. An unsupported reason is never a rejection (section 6.3). | `Except` with one sum type and an `isRejection` function of the proposal. | Accepted |
| 9 | The cutoff | Through E3, the revision runs the baseline `contextualCheckBlockBody` with `csvActive` true and the median of the view. No copy. | A cutoff function as a parameter. | Accepted |
| 10 | Ancestor times | The contiguous view, read at the depth of the coin. A short view gives `ancestorOutsideView` (section 7.2). | A supplied table of heights and median times, which adds an input that nothing checks. | Accepted |
| 11 | Compatibility claim | Block-level `SoftFork` with the identity projection, three strictness and three use witnesses, and the chain target. A third label, *block-level*, in COVERAGE.md (sections 8 and 9.3). | The Script-local and rule-level targets alone. | Accepted |
| 12 | Core with CSV forced active | The harness argument `force_csv_active`, which seeds `THRESHOLD_ACTIVE`. The label and the sentences of section 10.2 in COVERAGE.md, `docs/oracle.md` and SOUNDNESS.md. | No such run, and known answers alone. A patched Core build. | Accepted |
| 13 | Lean side of that comparison | The proposal executable of design record 0011, decision 10, with the argument and the report of section 6.5. No operation in `dogelib-oracle`. | The test executable `proposal-replay`. | Accepted |
| 14 | Known answers | The sources of section 10.1. The functional tests of R15 are a source of hand-made cases and are not run. | A regtest run of those tests on a build with another activation. | Accepted |
| 15 | Historical counts | The six counts and the ranges of section 10.3, with a committed candidate list before each run. | Changed blocks alone, as in design record 0011. | Accepted |
| 16 | Order of stages | BIP 113 with the extensions of the layer, then BIP 112, then BIP 68 with the block-level soft fork, then the counts. Each extension of the rules has `!` in its title. | BIP 112 first, as the smallest step. One lane for all three rules. | Accepted |
| 17 | Issue #122 | Stage 1 waits for that change and follows its form. The change merged on 2026-11-20 as pull request #176, and section 6.3 states its form. | Stage 1 defines its own parameter, and a later change joins the two. | Accepted |

## 14. Remaining risks

| Risk | Mitigation |
| --- | --- |
| A block-level theorem is read as a soft-fork proof of the network. | The label of section 8 and its limits. Design record 0007, section 8.3, lists what a network claim adds. |
| The forced-active comparison is read as mainnet behaviour, or as a Core comparison of the baseline. | The fixed label and sentence of section 10.2, in the section for proposals only. |
| The forced seed stays in the harness after a request. | Every exit of the harness clears the version-bits cache today. Stage 1 adds a case to `scripts/test_core_harness.py`: a request without the argument, after a request with it, gets the baseline result. |
| An extension changes the layer for the examples of design record 0011. | Each new parameter has a baseline value, and `connectBlockWith_baseline` is proved with those values. The examples keep their theorems (stage 1, condition 1). |
| The kernel cannot evaluate `validateBlock` on a witness block in acceptable time. | The witness blocks are small, with scripts that need no signature. If a witness is still too slow, the lane states it for `connectBlockWith` or for one transaction, and the pull request labels the level. |
| The soft-fork theorem holds for a revision that rejects everything. | Three strictness and three use witnesses, the characterizations, and `relativeLock_enforced`. |
| The Lean rule and Core's code share a misreading of a BIP. | Hand-made known answers from the BIP text (section 10.1), separate from the comparison with Core's code. |
| A later Dogecoin proposal changes the rules, such as the time unit. | The name describes the rule of P1 to P3. Another rule gets another name (design record 0007, section 5). |
| The layer of design record 0011 lands late, behind its Core pass. | Decision 7. Stages 1 to 3 need the definitions and the executable, and nothing of the snapshots. |
| The block level cannot use `embedU : Unsupported → υ` as it is, because its results outside the model have the type `ConnectBlockError`. | Extension E4 gives the block level its own pair of maps, and keeps the rule of issue #122: an unsupported result is never a rejection. |
| A time lock on an old coin gives `ancestorOutsideView` in a range above the genesis block. | Section 10.3 counts those blocks by reason, and never counts one as changed. |
| A historical count is read as the whole effect of an activation. | Section 10.3 states the ranges and the limits. Unconfirmed transactions and unspent P2SH scripts are outside every count. |
| The record is read as support for activation. | Sections 1 and 12. The record names the proposal and its source, and it takes no position. |

This record changes no pin, and it asks for no exception to the trust policy.
It changes no baseline definition and no agreed theorem statement.

Four of its decisions need the maintainer.
Decision 4 sets how SOURCES.md records a proposal document.
Decision 6 changes the layer of design record 0011, and removes that record's exclusion of rules outside Script for this revision.
Decision 11 adds a label to COVERAGE.md.
Decision 12 adds a harness argument and a kind of evidence.

Adoption of the record establishes no target theorem, and it does not authorize the merge of a later implementation.
