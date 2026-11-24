# Bug-finding campaign and replay

This document describes the differential campaign driver, the signed-spend generator, the planted proposal search, the reducer, L1 and L3 production replay and campaign regression fixtures.
See [docs/oracle.md](oracle.md) for the `dogelib-oracle/1` wire format and [docs/core-harness.md](core-harness.md) for the Core harness build.
See [design record 0009](design/0009-bug-finding-campaign.md) for the campaign design and [COVERAGE.md](../COVERAGE.md#campaign-infrastructure) for the campaign status summary.

## Campaign runs and replay

`scripts/campaign.py --campaign generated` checks Q1 to Q7 from [design record 0009](design/0009-bug-finding-campaign.md#11-properties).
It reuses `compare` from `scripts/compare_core.py` without changing the CI comparison stream.
The default campaign checks Q6 alone.
It shuffles existing requests with the selected seed and sends fixed-size batches.
The generated campaign adds signed plans and independent property checks.

Build the oracle and the [Core harness](core-harness.md#the-core-harness), then run these commands:

```bash
python3 -I scripts/campaign.py run --seed 20261108 --cases 10000 --seconds 600 --output build/campaign/check .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py replay build/campaign/check/<run>/failures/<digest>.json .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/test_campaign.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py run --campaign generated --signer build/core-harness/core-signer --seed 20261108 --cases 3000 --seconds 600 --batch-size 64 --output build/campaign/generated .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

`--inputs` selects `signed-spends`, `cltv`, `csv` or `signed-digests`.
The default selects the first three groups.
The digest group uses the existing recovery transactions, redeem scripts and hash types.
The timelock groups retain their original construction seed `20261107`.
The campaign seed selects the order, and `--cases` limits the prefix without repeating inputs.

`--campaign generated` selects the signed recovery-family generator and requires `--signer`.
Other names select existing requests and record the supplied name.

The generated stream starts with the 25 recovery fixtures and the targeted CLTV stream, including its boundary cases.
It then enumerates shuffled boundaries and draws plans with `random.Random(seed)`.
Plans cover both branches, signer pairs, mixed hash types, input positions, counts, selectors, supported flags and signature encodings.
The preserve mode mutates a plan before signing it.
The commitment mode signs first, then changes the spend while keeping its signatures.

The explicit `FIELDS` table in `scripts/campaign_generator.py` follows pinned `interpreter.cpp`, lines 1054 to 1143 and 1225 to 1246 (D3).
It records the committed and open fields of [section 6.3](design/0009-bug-finding-campaign.md#63-committed-and-open-fields).
SINGLE output-count changes stay above the input index, except in separate fixed-digest cases.

Before constructing a spend, the driver checks every signing digest against both programs through `sighash.legacy`.
Q1 to Q5 and Q7 derive expectations from the plan and field table, without using a program's verdict.
Q6 still checks agreement on every request, including the before and after digests.
Q4 checks Lean preimages as well as both digests and rejection.
Its security assumptions remain those of [section 11](design/0009-bug-finding-campaign.md#11-properties).
These finite checks add no theorem.

`core-signer --sign` reads JSONL requests with `id`, `tx_hex`, `input_index`, `script_code_hex`, `hash_type` and `key_ids`.
It accepts base transactions of at most 100,000 bytes, with 1 to 4 inputs, 0 to 5 outputs and an existing input index.
Script code has at most 10,000 bytes, and the hash type is a byte.
The 1 to 3 key identifiers select public test scalars 1 to 4.
A response echoes `id` and supplies `ok` with `digest_hex`, `signatures_hex`, `CORE_SIGNER_BLOB` and `request_source_blob`.
The digest uses wire byte order, and each DER signature includes its hash-type byte.

A refusal supplies `error` with `kind: "refusal"` and a `reason` string.
The request mode calls Core's `SignatureHash` and deterministic `CKey::Sign`, without returning a Script verdict.
The no-argument fixture generator and `--verification-vectors` retain their byte-for-byte regeneration checks.

`--batch-size` defaults to 2,000 cases and `--timeout` to 60 seconds per program invocation.
Each generated case sends one signing request per signature and several oracle requests.
`--seconds` limits scheduling and each invocation's remaining time.
Each version probe has a fixed 0.25-second timeout.
Probe time counts against the campaign budget.
An invocation stopped by the remaining budget marks the run incomplete without recording a program timeout.

The driver bisects a failed stream until it isolates individual requests, while time remains.
Bisection assumes that responses depend only on their requests.
If one half isolates a crash, the driver does not also save the parent batch.
A separate failure that requires requests from both halves can therefore escape attribution.

A failure that disappears in smaller batches retains its original batch for replay.
A budget that interrupts isolation also retains the failed batch and marks the run incomplete.
Exit status 1 means a disagreement, a process failure or an incomplete run.

Each run creates a fresh directory below `--output` and prints its path and counts.
Its `summary.json` records revisions, versions, seed, budgets, input selection and counts for all six outcome classes.
Generated summaries also record coverage counts for branches, hash types, errors, mutations, properties, modes and transaction boundaries.
The `q6_requests` count records assessed requests separately from cases and signing preflight requests.
The per-case `counts`, including passes, sum to `completed`.

`batch_counts` records stream failures that bisection did not attribute to individual requests.
The `failures` total includes both per-case disagreements and process failures, and these separate batch failures.

`unsupported` and harness `refusal` count apart from disagreements, and each gets a saved record.
`known` counts accepted fixed-digest cases and early recovery with CLTV disabled, after the property checks pass.
The duplicate-key behaviour is registered but unreachable in this template, whose keys are distinct.
Saved `unsupported` records name Q6 and its agreement expectation, as exclusions from comparison.
Every Q6 result retains that expectation rather than the generated plan's independent property.
A Q6 disagreement has failing side `undetermined`: agreement alone cannot establish which implementation violates an independent property.

Saved records use `dogelib-campaign-failure/1`, with the fields of [section 7.3](design/0009-bug-finding-campaign.md#73-the-saved-failure).
A file name hashes the canonical request text with SHA-256, or the request array for a batch-only failure.
Records contain exact requests, full responses, process status, standard error and the raw output of failed batches before bisection.
Per-request records retain the full raw stream in `stdout`, with its request order in `stdout_requests`.
Invalid UTF-8 bytes use JSON surrogate escapes and round-trip with Python's `surrogateescape` codec.

Existing cases have an empty `signer` array and a null `CORE_SIGNER_BLOB`.
Generated failures retain exact signing requests and responses, or process evidence, together with both signer source blobs.
The adjacent `core.stamp` records the harness build provenance, or null for a wrapper without a stamp.

Replay uses the configured `timeout` from the record and reports whether the class and failing side reproduce.
It exits with status 0 for reproduction, 1 otherwise, or 2 for an invalid invocation or saved record.
Oracle and harness failures replay stored requests without signing again.
Signer failures require `replay --signer build/core-harness/core-signer <failure> <oracle> <harness>`.
This path repeats the signing requests and checks refusals, malformed responses, process failures or digest discrepancies.

Keep saved candidates private under `build/campaign/`, as [SECURITY.md](../SECURITY.md) requires.
Console output contains counts, without candidate requests or responses.
The self-test checks six outcome classes, crash attribution within a batch, malformed output, response counts and response identifiers.

It also requires semantic mutants M1 to M6 to be detected and replayed within fixed budgets.
It writes their seed, first detected case, class and timing to `build/campaign/mutant-detection.json`.
Signer checks cover repeated-request determinism, refusal replay and malformed-response replay.
[Production replay](#production-replay) replays a saved candidate through Core's production path.

The `core` workflow runs the generated campaign at seed `20261108` with 3,000 cases, the command above.
A person reviewed the results of that seed, so a CI log shows no new candidate ([design record 0009, section 9.4](design/0009-bug-finding-campaign.md#94-a-real-finding)).
A run with a fresh seed stays on a contributor's machine.
The other campaign commands do not run in CI.

### The planted proposal search

`--campaign proposal` searches for a violation of `RestrictsAcceptance` by the planted fault of [design record 0009, section 8.1](design/0009-bug-finding-campaign.md#81-the-planted-proposal-fault).
In this campaign, the harness argument is `proposal-replay`, a test executable under `tests/`.
It is not part of `Exports`, and `dogelib-oracle` gets no proposal operation.

```bash
lake build dogelib-oracle proposal-replay
python3 -I scripts/campaign.py run --campaign proposal --variant corrected --seed 0 --cases 374480 --output build/campaign/proposal .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
```

`proposal-replay ExampleFaultyLocktime (faulty|corrected) [--active]` reads `script.verify_legacy` requests in [`dogelib-oracle/1`](oracle.md).
It answers each request with the revised spend predicate of the named variant, through the oracle's own request decoding and response encoding.
Without `--active`, the revised step equals the baseline step.
It answers every other operation with an unknown-operation error, and `--version` prints the format with `"program": "proposal-replay"`.

The driver enumerates every script of one to five instructions from the alphabet of section 8.1, shortest first, with no seed.
Each of the 37,448 scripts runs with five lock times and two sequences, so the space has 374,480 cases.
The spending transaction has version 1, one input with a null outpoint and an empty `scriptSig`, no outputs and flags 0.
`--variant` selects the variant, and `--cases` limits the prefix of the enumeration.

A violation is a request that `proposal-replay` accepts and `dogelib-oracle` rejects.
Its saved failure names the property `RestrictsAcceptance`, the class `verdict` and the failing side `revised`.
The record keeps the replay's arguments in `program_arguments`, so `replay` runs the same variant.
Process failures, `unsupported` results and refusals keep the classes of section 7.2.

A failure of `proposal-replay` names the side `revised`.
A response that is not an `ok` object with the result `accepted`, `rejected` or `unsupported` checks nothing.
On either side, it is a `crash` with the code `RESULT`, so a search cannot pass without verdicts.
Flags 0 make every case of the space supported, so a proposal run also exits with status 1 when its `unsupported` count is above zero.
Other differences between two verdicts are not violations of this property.

`--script` runs one script instead of the enumeration, with `--lock-time` (default 2) and `--sequence` (default `0xfffffffe`).
It accepts hex bytes, and it splits them into instructions at push boundaries.

### Reduction

`campaign.py reduce <failure> <oracle> <harness> [<signer>]` reduces a saved failure of one generated or proposal case.
A generated failure needs the signer.
The reducer refuses a record of existing requests, and a batch of several cases, because they have no single construction plan.
It exits with status 0 when it writes an output.
It exits with status 2 for such a record, or when the stored plan no longer reproduces its failure condition.

```bash
python3 -I scripts/campaign.py run --campaign proposal --script '51 52 b3 51 87' --seed 0 --cases 1 --output build/campaign/seed .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
python3 -I scripts/campaign.py reduce build/campaign/seed/<run>/failures/<digest>.json .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
```

The reducer changes the plan, not the bytes.
It runs each candidate plan alone through the same run path as `run`, with the record's seed and timeout.
So a preserve plan is signed again after its mutations, and a commitment plan is signed before them and keeps its signatures.
A candidate replaces the plan when that run saves a failure with the same property, class and failing side.
A candidate that the plan's construction cannot build, such as a mutation of an input that the candidate removed, is skipped.

It tries the changes of [section 7.4](design/0009-bug-finding-campaign.md#74-replay-and-the-reducer) in this order:

1. Remove one element, then two adjacent elements, then each half of four or more elements. An element is a mutation, the signature-encoding mutation or a script instruction.
2. Remove each other input and each output, then move input `n` to position 0 or one position towards it.
3. Replace the value of each push in a script with 0. Then set the version to 1, each nonfinal sequence to 0 and each output value to 0. Replace the lock time with the least value of its class.
4. Clear each flag that is not P2SH in a generated plan. Keep each result inside the assertion domain of C7.
5. Set every hash type to ALL, then each one. Then replace a true selector with `01` and a false selector with the empty push.
6. Remove one byte of each other script.

The lock-time classes are the values below 1,000,000, the values from 1,000,000 to 499,999,999, and the values from 500,000,000.
The classes are specific to the 2-of-3 recovery template of decision 1.
Its CLTV operand is 1,000,000, and 500,000,000 separates heights from times (C4).
The template has no `OP_CHECKSEQUENCEVERIFY`, so 0 represents every nonfinal sequence.
A plan for another template needs its own classes.

A candidate must also stay in the domain of its property (section 7.4).
Every property of section 11 assumes a P2SH spend, so a generated candidate keeps the P2SH flag.
The ordinary branch (Q1) needs a true selector, and the recovery branch (Q2 and Q3) needs a false one.
The reducer skips a candidate that leaves this domain, when the stored plan is inside it.

After each accepted change, the reducer starts its current step again on the new plan.
It repeats the six steps until a complete pass accepts no change, and then it gives the label `minimal`.
The output is then 1-minimal for these changes only.
`--max-candidates` (default 2,000) limits the candidates that the reducer runs.
If the limit stops the reduction before such a pass, the label is `budget`, and the output still keeps the failure condition.

The reducer caches each result by its canonical plan, so a candidate runs once.
It writes the output to `reduced/<digest>.json` beside the run's `failures/` directory.
The output is a complete saved failure with `reduced_from` set to the original file name.
Its `reduction` field records the label, the number of candidates, the limit and each accepted change with its step.
The console shows the output path, the label and the counts, without requests.

The campaign self-test needs `proposal-replay` beside the oracle, or `--proposal-replay PATH`.

It runs the faulty search over all scripts of up to three instructions and requires violations of exactly three instructions.
It runs the corrected search over the whole space and requires no violation.
It reduces `51 52 b3 51 87` and requires three instructions with the label `minimal`.
It also reduces the first saved detection of each mutant M1 to M6.
Each reduction must keep the failure condition and the mutant's trigger, and its output must replay.
Each reduced generated plan must keep the P2SH flag and a selector of its branch's truth value.

A planted Core fault flips the verdict of each spend with a hash type `0x82` signature.
The self-test reduces its first three detections, and each reduced plan must keep a `0x82` signature.
The unmodified harness must also give the expected verdict on the reduced spend, so the template runs.
A stand-in replay that answers every request with an error must fail all 200 cases of a corrected search.
It writes the labels, candidate counts and plan sizes to `build/campaign/mutant-reduction.json`.

### Production replay

Design record 0009, [section 9.1](design/0009-bug-finding-campaign.md#91-levels), counts a candidate as a finding only after a replay through Core's production path.
`campaign.py replay --level` replays one saved failure of one generated signed-spend case at level L1 or L3.
Each replay appends its evidence to the saved failure, in the `production` field.
The field is an addition to `dogelib-campaign-failure/1`, so the format name stays the same.

Build the programs at one Core commit, each in its own directory:

```bash
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
taskset -c 16-23 nice -n 19 scripts/build_core_node.sh --revision e0a1c157791544e818c901bd9341896965afbf9d <dogecoin-git-clone> build/core-node
```

Replay a saved failure at each level:

```bash
python3 -I scripts/campaign.py replay --level L1 <failure> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py replay --level L3 --signer build/core-harness/core-signer --node build/core-node <failure> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

`--target pin` is the default, and it needs builds at the pin `e0a1c15`.
`--target upstream` labels builds of another commit, as [section 9.2](design/0009-bug-finding-campaign.md#92-the-current-upstream-revision) requires.
`--revision COMMIT` also requires each build to name that full commit.
Every result records the commit, the build stamps and the SHA-256 of each program.

The replay refuses a program without a build stamp, such as a wrapper of the self-test.
It refuses a stamp of another commit, an L3 call without `--signer` and `--node`, and a saved failure outside `build/campaign/`.

| Exit status | Outcome |
| --- | --- |
| 0 | `reproduced` |
| 1 | `not-reproduced` |
| 2 | A refusal, SIGTERM or an unexpected error. The saved failure does not change. |
| 3 | `not-comparable` at L3, or `error` at L1. The replay decides nothing. |

SIGTERM stops the node and deletes its data directory before the replay exits.
The node also gets SIGKILL from Linux when the replay process dies by SIGKILL (`PR_SET_PDEATHSIG`).
After a SIGKILL, the data directory stays under `build/campaign/`.
The console shows the level, the commit, the outcome and the labels at the pin and at upstream, without requests.

#### Builds at another commit

`scripts/build_core_harness.sh --revision COMMIT <clone> <build-dir>` builds the harness and `core-signer` at that commit.
The directory must not be `build/core-harness`.
The first line of `core.stamp` is then `revision <commit>`, and `core.revision` holds the commit.
Both programs add `core_revision` to their `--version` output.
Without `--revision`, the build and its output do not change, and the pin in SOURCES.md and in CI stays `e0a1c15`.

For the upstream check, read the current commit of the pin's branch, and build from it:

```bash
git ls-remote https://github.com/dogecoin/dogecoin refs/heads/1.14-maint
scripts/build_core_harness.sh --revision <commit> <dogecoin-git-clone> build/core-harness-upstream
python3 -I scripts/campaign.py replay --level L1 --target upstream <failure> .lake/build/bin/dogelib-oracle build/core-harness-upstream/core-oracle
```

The clone must contain that commit.
On 2026-11-08 the branch was at the pin itself, `e0a1c157791544e818c901bd9341896965afbf9d`.

`scripts/build_core_node.sh --revision COMMIT <clone> <build-dir>` builds a `dogecoind` without a wallet, GUI, tests or ZMQ.
It exports the commit with `git archive` and writes `node.stamp` and `node.revision`.
It reuses the node when the stamp matches.

Pinned Core needs the Boost libraries system, filesystem, program_options, thread and chrono.
Recent distributions omit `boost_system`, so the script builds Boost 1.70.0 into the build directory.
It checks the SHA-256 of the archive first.
Boost 1.70.0 does not compile with glibc 2.34 or later, so the script applies the one-line change that Boost 1.78.0 made to `boost/thread/pthread/thread_data.hpp`.
`BOOST_ROOT` selects an installed Boost instead, and `BOOST_ARCHIVE` selects a local copy of the archive.
On this project's development machine, the node and its Boost built in 62 seconds with 8 jobs.

#### L1

L1 sends the stored requests, unchanged, to the oracle and to the harness build.
For the signed-spend family, `script.verify_legacy` calls `VerifyScript`, and `sighash.legacy` calls `SignatureHash` ([what the harness runs](core-harness.md#what-the-harness-runs)).
The outcome is `reproduced` when the stored class and failing side recur.
It is `error` when either program fails, crashes or times out, and `not-reproduced` otherwise.
L1 does not include the caller of [section 4, item 8](design/0009-bug-finding-campaign.md#4-behaviour-to-preserve): a node uses `CachingTransactionSignatureChecker` through `CScriptCheck`.

#### L3

L3 starts `dogecoind -regtest` in a new temporary data directory under `build/campaign/`.
The node binds RPC to 127.0.0.1 on the first free port from 24440 to 24479.
It does not listen for peers and does not connect to them.
These ports are outside the range of Core's functional test framework, 11000 to 20999, and differ from the default ports.
The replay stops the node on every exit path and deletes the data directory.

The outpoints of a saved case are random bytes, so L3 builds the same case on real outputs:

1. It mines 19 legacy blocks and 1,333 AuxPoW blocks, to height 1,352, with `generatetoaddress` (D96). Regtest starts AuxPoW at height 20, DERSIG at 1,251 and CHECKLOCKTIMEVERIFY at 1,351 (D14).
2. One funding transaction makes an output for each input. Input `n` gets the P2SH output of the redeem script, and each other input gets a bare `OP_TRUE` output. A block confirms the transaction.
3. The plan's inputs get these outpoints. In preserve mode, L3 first applies the mutations, because the signer signs the mutated transaction. In commitment mode, the mutations stay. A mutation of an outpoint or of the input count is refused, because no output can match it.
4. If the spend has no output, L3 adds one zero-value `OP_TRUE` output, because `CheckTransaction` rejects a transaction without outputs (D90). The evidence records this change.
5. `core-signer --sign` signs the same plan again: the same mode, keys, hash types, selector and signature mutation. The oracle and the harness check each signing digest, as in a run.
6. The rebuilt case must keep the saved property, verdict, error name and digest relation. Otherwise the outcome is `not-comparable`.
7. The harness that found the candidate must show the saved class and failing side on the rebuilt bytes. It is the harness of the record's replay command, or `--candidate-harness`. Otherwise the rebuilt case lost the candidate's trigger, and a node that agrees with the property gives `not-comparable`.

The node checks the spend twice:

| Path | Script flags | Source |
| --- | --- | --- |
| `sendrawtransaction` and `AcceptToMemoryPool` | The flags of the spend request, through `-promiscuousmempoolflags`. A hash-type mutation or a `hash_byte` signature clears STRICTENC from the plan's flags (`spend_flags` in `scripts/campaign_generator.py`). Regtest does not require standard transactions, so the node accepts the option. | D95, D97, D14 |
| `submitblock` with an AuxPoW block that holds the spend | The consensus flags of the block's height: P2SH, DERSIG and CHECKLOCKTIMEVERIFY, flags 517. CHECKSEQUENCEVERIFY is not active at that height, and `IsWitnessEnabled` returns false. | D96, D36 |

Both paths call `VerifyScript` through `CScriptCheck` with `CachingTransactionSignatureChecker`, the production caller.
The replay starts the node with `-par=1`, so a block's script check runs in the calling thread and its error reaches `submitblock`.
The replay maps each rejection reason to an error name through `ScriptErrorString` (D99).
Another rejection, such as `non-final` or `bad-txns-vout-empty`, makes the path `not-comparable`.

The mempool result decides the L3 outcome, because the mempool uses the flags of the spend request.
If the rebuilt request has other flags, the outcome is `not-comparable`.
After the plan's flags, the mempool checks P2SH alone again, and it reports only the first failing input (D97).
So L3 refuses a plan without P2SH or with CLEANSTACK, which the bare `OP_TRUE` inputs would fail.
The outcome is `reproduced` when the node's verdict or error name differs from the saved expectation, and `not-reproduced` when it agrees.

Core prefixes a Script rejection with `non-mandatory-script-verify-flag` when the spend passes without the flags of `STANDARD_NOT_MANDATORY_VERIFY_FLAGS` (D98).
At the pin, `MANDATORY_SCRIPT_VERIFY_FLAGS` is P2SH alone.
So that prefix does not separate policy from consensus: a block also reports a CHECKLOCKTIMEVERIFY failure with it.
The block result separates them.
The evidence sets `policy_only` when the mempool rejects the spend and the block accepts it.
For example, a high-S signature fails LOW_S in the mempool, and flags 517 accept it in a block.

After funding, the tip is at height 1,353, and `CheckFinalTx` tests the spend for the next block, height 1,354.
L3 can compare only a spend that is final in that block.
A spend is final when every sequence is `0xffffffff`.
It is also final when its lock time is a height below 1,354, or a time before the median time past.
The node rejects any other spend with `non-final`, so its outcome is `not-comparable`.

A valid recovery spend (Q2) is never final there, because the template's CLTV operand is the height 1,000,000.
The generator's acceptance cases also set lock time 1,000,000 with a nonfinal sequence on input `n`.
So most generated Q1, Q4 and Q5 cases, and every Q2 case, are `not-comparable` at L3.
Q3 cases at a lock time below 1,354 or a time lock time, and spends at lock time 0, are comparable.

#### Classification

After each replay, `production.classification` labels the candidate from the latest outcome of each level.
`label` uses the replays at the pin, and `upstream` uses the replays at upstream, or is null.
A Core-side candidate has the failing side `core`, `both` or `undetermined`.

| Candidate | Outcomes | Label |
| --- | --- | --- |
| Core-side `verdict` | L3 `reproduced` | `reproduced` |
| Core-side `verdict` | L3 `not-reproduced`, L1 `reproduced` or `not-reproduced` | `harness-fault` |
| Core-side `verdict` | L1 `reproduced`, no comparable L3 result | `reproduced-at-l1`: the candidate still needs L3 |
| Core-side `digest` | L1 `reproduced` | `reproduced` |
| Core-side `digest` | L1 `not-reproduced` with a harness whose SHA-256 differs from the harness that found the candidate | `harness-fault` |
| Any other | A `reproduced` outcome at either level | `reproduced` |
| Any | Every other combination, including an L1 `error` | `undetermined` |

For a `verdict`, L3 overrides L1, because only a node runs the production caller of [section 9.1](design/0009-bug-finding-campaign.md#91-levels).
Suppose that L1 reproduces the candidate and L3 does not.
Then the fault is in the harness's own code around `VerifyScript`, such as its transaction or flag handling.
For a `digest`, L1 decides: `sighash.legacy` calls `SignatureHash` itself, and L3 checks only verdicts.

`production.replays` keeps every replay in order, with its level, target, commit, build identities, requests, full responses and node rejection reasons.
L3 evidence also keeps the funding transaction, the new outpoints and the signer's requests and responses.
It keeps the end of the node's `debug.log` and the time of the replay.
Keep this evidence private under `build/campaign/`, as [SECURITY.md](../SECURITY.md) requires.

#### The stage 4 self-test

```bash
python3 -I scripts/test_campaign_production.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle --node build/core-node --upstream-harness build/core-harness-upstream/core-oracle
```

The self-test plants the harness fault M3 of [section 8.2](design/0009-bug-finding-campaign.md#82-planted-harness-and-model-faults), which treats lock time 500,000,000 as a height on the recovery branch.
It runs the generated campaign until it finds the fault, then reduces the first detection.
The unchanged harness must not reproduce the reduced candidate at L1, and the replay must refuse the planted wrapper.
It checks the table of labels on stated outcomes.
A stamped build that exits with status 3 must give the L1 outcome `error`.
A stamped build that contains the planted fault stands for a faulty adapter: it must reproduce at L1 and get `reproduced-at-l1`.

`--node` adds L3.
The node must reject the reduced spend with `UNSATISFIED_LOCKTIME` in its mempool and in a block, and the planted wrapper must accept the same bytes.
The candidate must then have the label `harness-fault`.
The stamped faulty build must also become `harness-fault` after L3.
With `--candidate-harness` set to the unchanged harness, the trigger is lost, and the outcome must be `not-comparable`.
`--node` also checks five other spends:

- An ordinary 2-of-3 spend, which the mempool and a block accept.
- An early recovery spend at lock time 1,000, which both reject with `UNSATISFIED_LOCKTIME`.
- A commitment-mode spend whose version changes after signing, which both reject with `mandatory-script-verify-flag-failed`.
- A spend whose first signature has bit `0x20` of its hash-type byte flipped (`hash_byte`). The node and the harness must both use flags 541, without STRICTENC.
- A high-S spend, which the mempool rejects with `SIG_HIGH_S` and a block accepts, so `policy_only` is true.

`--upstream-harness` adds L1 against another harness build, with `--target upstream`.
It sends the requests of 500 generated cases to both harness builds and reports how many responses differ.
When the node build names the same commit, it also runs L3 with `--target upstream`.

`scripts/test_campaign.py` runs the L1 part, without `--node`.
`--keep DIR` copies the first detection and its reduced output to a directory under `build/campaign/`, which the self-test otherwise deletes.
With `--node` and `--upstream-harness`, the self-test passed 17 cases in 32 seconds on the development machine.
Each L3 replay took about 1.5 seconds, and the search and reduction took about 18 seconds.

### Regression fixtures

[`tests/script/campaign/`](../tests/script/campaign/README.md) keeps each understood counterexample of the campaign as a fixture ([design record 0009, section 10](design/0009-bug-finding-campaign.md#10-regression-and-proof-follow-up)).
The fixtures reuse the format of `tests/oracle`: `script.verify_legacy` requests, and the expected response on the same line of another file.
`expected.jsonl` gives the baseline response. `expected-faulty.jsonl` and `expected-corrected.jsonl` give the responses of `proposal-replay` for each variant, with `--active`.

The README of the directory records the property, the plan, the run, both revisions, the reduction and the source of each expected value.
`lake test` checks the expected values, and `scripts/compare_core.py` sends the requests to both programs as the set `Script campaign fixtures`.
A person reviews a candidate before it becomes a fixture.
A candidate that can be a vulnerability becomes a fixture only after its report is resolved ([section 9.4](design/0009-bug-finding-campaign.md#94-a-real-finding)).

## Recorded campaign results

At seed `20261108`, the default campaign compares 1,897 requests with Core at `e0a1c15`, with zero in all six outcome classes.
The optional signed-digest group compares 25 requests at the same seed, also with zero in all six classes.
The campaign self-test also checks M1 to M6 with semantic triggers and fixed budgets, signer determinism, refusal replay and malformed-response replay.

At seed `20261108`, the generated campaign completes 3,000 cases with 9,408 assessed Q6 requests and zero disagreements or process failures.
It records 2,930 passes, 67 known behaviours and 3 unsupported cases. The unsupported cases are labelled Q6.
The known counts are 38 fixed-digest cases and 29 early recoveries with CLTV disabled.

The 2,043 generated plans cover both branches, all eleven selected hash-type bytes, input positions 0 to 3 and output counts 0 to 5.
They reach Q1 to Q5 and Q7, both mutation modes and every operator in the field table.
The field boundaries move the signed input in all six directions among positions 0 to 2. Under SINGLE, with and without ANYONECANPAY, they change an output before and an output after the signed input.

The self-test passes 40 cases. Each mutant is detected within 3,000 cases and 120 seconds, with a three-second invocation timeout.

`campaign.py reduce` reduces the plan of a saved generated or proposal failure, in the order of design record 0009, section 7.4.
After each mutant detection, the self-test reduces the saved failure through the same wrapper.
Each of the six reductions ends with the label `minimal`, after 14 to 25 candidates.
Each keeps the property, class and failing side, keeps the mutant's trigger in its requests, and reproduces on replay.

Each reduced plan also keeps the P2SH flag and a selector of its branch's truth value.
A planted Core fault that flips the verdict of spends with a hash type `0x82` signature is detected and reduced three times.
Each reduced plan keeps a `0x82` signature, and the unmodified harness accepts its spend, so the template runs.
These results test the reducer and the campaign, and they add no theorem.

`run --campaign proposal` compares `dogelib-oracle` with the test executable `proposal-replay` on the search space of section 8.1.
It is a self-test of the campaign, not a comparison with Core.
Against the active faulty rule of `ExampleFaultyLocktime`, the first 5,840 cases give 16 violations of `RestrictsAcceptance`.
All 16 have three instructions, such as `51 00 b3`, and the 720 cases of one or two instructions give none.
The reducer takes `51 52 b3 51 87`, at lock time 2 and sequence `0xfffffffe`, to `51 00 b3` at lock time 0 and sequence 0, with the label `minimal`.

Against the active corrected rule, all 374,480 cases give no violation, as `corrected_restrictsAcceptance` requires.
A response without a Script verdict is a failure, so a stand-in replay that answers with errors fails the search.
Every case of this space is supported, so an `unsupported` result also makes the search exit with status 1.

### Production replay results

`scripts/test_campaign_production.py` runs the exit check of stage 4 with the planted harness fault M3.
The generated campaign at seed `20261108` detects M3 at case 1,907 as a Q3 `verdict` failure on the Core side.
The reducer reduces it with the label `minimal` to one input, no outputs, lock time 500,000,000 and flags 513.

The unchanged harness at `e0a1c15` does not reproduce it at L1.
L3 adds one zero-value output, because Core rejects a transaction without outputs.
The node at `e0a1c15` then rejects the re-signed spend with `UNSATISFIED_LOCKTIME` in its mempool and in a block.
The planted harness accepts the same bytes.
The classification is `harness-fault`.

The same check shows four production verdicts at L3 that agree with their properties.
The node accepts an ordinary 2-of-3 spend (Q1). It rejects an early recovery spend at lock time 1,000 with `UNSATISFIED_LOCKTIME` (Q3).
It rejects a commitment-mode spend whose version changed after signing (Q4).
A high-S signature fails LOW_S in the mempool and passes in a block, so the replay reports the rejection as policy only.

On 2026-11-08, the branch `1.14-maint` of `dogecoin/dogecoin` was at the pin `e0a1c15`, so the upstream check used builds of that commit.
A separate harness build with `--revision` gave the same L1 result for the planted candidate, and the same L3 result with `--target upstream`.
It also gave the same responses as the pin harness to all 2,046 requests of 500 generated cases.

After funding, the tip is at height 1,353, and L3 compares only spends that are final in the next block, height 1,354.
A valid recovery spend (Q2) is never final there, because the template's operand is height 1,000,000.
The generator's acceptance cases use lock time 1,000,000 with a nonfinal sequence, so most generated Q1, Q4 and Q5 cases are not final either.
For these spends the node reports `non-final`, and the replay labels the case `not-comparable`.
With the L1 part of stage 4, `scripts/test_campaign.py` passes 47 cases.
These results test the replay procedure, and they add no theorem.

### Regression fixture results

[`tests/script/campaign/`](../tests/script/campaign/README.md) keeps the two understood counterexamples of the campaign, as design record 0009, section 10, requires.
Both come from planted faults. The campaign found no fault in Core or in DogeLib.

- `proposal-faulty-locktime-5100b3`: the stage 3 search finds `51 00 b3` at lock time 2 and sequence `0xfffffffe`. The faulty rule of `ExampleFaultyLocktime` accepts it, and the baseline rejects it with `EVAL_FALSE`.
- `harness-fault-m3-locktime-500000000`: the reduced M3 candidate of stage 4, labelled `harness-fault`. The baseline rejects it with `UNSATISFIED_LOCKTIME`.

Each expected value comes from its property and a hand check against pinned `interpreter.cpp`, which the fixture README cites by line.
`lake test` checks `verifyLegacySpend` and both revised variants against these values.
`scripts/compare_core.py` compares the oracle with the Core harness on the same requests, as the set `Script campaign fixtures`.
The two checks together require the Core harness to give the baseline values.
The known behaviours of design record 0009, section 7.5, get no fixture, because no property of section 11 has them as a counterexample.

The `core` workflow runs the generated campaign at the reviewed seed `20261108` with 3,000 cases.
On the development machine, that run took 8.7 seconds, with the counts above.
The regtest replay of stage 4 stays a local gate.
Its node build took 3 minutes and 51 seconds with 8 jobs, and it downloads Boost 1.70.0.
These checks are finite regression evidence, and they add no theorem.
