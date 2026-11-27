# Core comparison evidence and recorded runs

This document records the finite comparison streams, request counts, mainnet replays, snapshot ranges, Core pass measurements and historical impact runs.
See [docs/oracle.md](oracle.md) for the wire protocol and [docs/core-harness.md](core-harness.md) for the harness build and comparator mechanics.
See [docs/soundness/oracle-and-harness.md](soundness/oracle-and-harness.md) for trust boundaries and [COVERAGE.md](../COVERAGE.md) for per-operation coverage.

## The comparison

[Comparator and self-test mechanics](core-harness.md#comparator-and-self-test-mechanics) describes how `scripts/compare_core.py` sends requests, compares projections and tests failure detection.

A full comparison with Core `e0a1c157791544e818c901bd9341896965afbf9d` sends 389,785 stream requests.
The table `EXPECTED_OPERATION_COUNTS` of `scripts/compare_core.py` gives the number of requests for each operation.
A full run fails with `REQUEST_COUNT` when the count of any operation differs from the table.
So a change to a request set changes the table, and this section, in the same pull request:

| `op` | Stream requests |
| --- | ---: |
| `auxpow.check` | 404 |
| `block.check` | 2,232 |
| `block.check_pow` | 806 |
| `block.check_version` | 207 |
| `block.contextual_check` | 2,903 |
| `block.contextual_check_body` | 22 |
| `block.header.read` | 7,878 |
| `block.header_sequence` | 257 |
| `block.subsidy` | 148 |
| `block.validate` | 42 |
| `compactsize.encode` | 26 |
| `compactsize.read` | 404 |
| `hash.hash160` | 292 |
| `hash.ripemd160` | 299 |
| `hash.sha1` | 519 |
| `header.encode` | 349 |
| `header.hash` | 347 |
| `header.read` | 25,865 |
| `merkle.compute` | 550 |
| `pubkey.verify` | 602 |
| `script.eval` | 8,882 |
| `script.read_op` | 1,233 |
| `script.verify_legacy` | 8,137 |
| `scrypt.hash` | 272 |
| `sighash.legacy` | 4,496 |
| `tx.check` | 1,384 |
| `tx.decode_base` | 37,694 |
| `tx.decode_witness` | 45,958 |
| `tx.read_base` | 137,991 |
| `tx.read_witness` | 42,286 |
| `work.calculate_next` | 49,255 |
| `work.get_compact` | 1,552 |
| `work.next` | 1,353 |
| `work.set_compact` | 5,140 |
| Total | 389,785 |

The four transaction-reader operations receive 263,929 of the requests.
Most of them are proper prefixes and field changes of corpus transactions.
`script.eval` and `script.verify_legacy` receive 17,019, and `block.header_sequence` receives 257.
So the total is mostly evidence about the transaction readers.

The pull request records the tested DogeLib revision.
The comparison passes with zero failures, including 12 checked harness refusals, plus 22 adapter-limit cases and the 1,193 two-call compositions.
The adapter-limit cases and the compositions run outside the stream, so the table does not count them.
With `--quick` or `--rust-compactsize`, the comparator sends a subset and does not check the table.

With `--mainnet-blocks DIR`, the comparator sends only requests on real mainnet blocks, 22,020 in all.
Of these, 11,001 are `block.check` requests on the [two ranges](#transaction-and-block-check-comparison-evidence).
The other 11,018 are [`block.contextual_check_body`](#contextual-block-body-comparison-evidence) requests on the two ranges and the 17 blocks of `tests/block/mainnet-blocks/rule-changes`.
One is the [`block.validate`](#real-mainnet-blocks-from-the-genesis-block) request that replays heights 0 to 10,000.
The comparator checks each count against `tests/block/mainnet-blocks/release.json` and the number of blocks in that directory.

The transaction inputs and targeted timelocks have these counts:

| Stream | Requests | Agreement | Unsupported | Harness-refused | Disagreements |
| --- | ---: | ---: | ---: | ---: | ---: |
| Transaction inputs, accept, base | 91 | 91 | 0 | 0 | 0 |
| Transaction inputs, unknown, base | 68 | 68 | 0 | 0 | 0 |
| Transaction inputs, accept, transaction | 91 | 91 | 0 | 0 | 0 |
| Transaction inputs, unknown, transaction | 68 | 68 | 0 | 0 | 0 |
| Legacy corpus, transaction | 925 | 925 | 0 | 0 | 0 |
| Legacy mutations, transaction, seed `20261106` | 2,000 | 1,956 | 44 flags | 0 | 0 |
| Public-key Wycheproof bitcoin | 464 | 464 | 0 | 0 | 0 |
| Public-key Core signatures and reversed digest one | 6 | 6 | 0 | 0 | 0 |
| Public-key parser boundaries | 20 | 20 | 0 | 0 | 0 |
| Public-key infinity constructions | 36 | 36 | 0 | 0 | 0 |
| Public-key x above order, including changed S and R | 72 | 72 | 0 | 0 | 0 |
| Signed recovery spends | 25 | 25 | 0 | 0 | 0 |
| Fixed-digest spends and their signature hashes | 115 | 115 | 0 | 0 | 0 |
| Targeted CLTV, transaction, seed `20261107` | 932 | 932 | 0 | 0 | 0 |
| Targeted CSV, transaction, seed `20261107` | 940 | 940 | 0 | 0 | 0 |
| Refusal precedence | 7 | 7 | 0 | 0 | 0 |
| Synthetic flag refusals | 8 | 0 | 0 | 8 | 0 |

Agreement in the unknown streams means agreement with Core on the input, not agreement with a fixture expectation.
All 91 independent Core acceptance requirements passed.
The 44 Script records and 60 transaction inputs that require signature verification each give a compared verdict.

All 932 CLTV requests and 940 CSV requests reach their target opcode by construction.
The comparator counts only Core acceptance or a `NEGATIVE_LOCKTIME` or `UNSATISFIED_LOCKTIME` rejection as evidence of the target opcode.
Any other Core outcome fails the run.
The outcome counts are CLTV: 151 accepted, 84 negative-locktime and 697 unsatisfied-locktime rejections.
CSV gives 414 accepted, 60 negative-locktime and 466 unsatisfied-locktime rejections.

`lake test` runs all 159 eligible transaction inputs with `verifyLegacySpend` and `coreVerifier`.
All 159 decode as complete base bytes, and the runner excludes the other 108 input records.
All 91 required acceptances accept.
For the 68 null expectations, 11 accept and 57 reject.
The null expectations supply counts only.

The request stream is deterministic, and the random sets use a fixed seed:

- The fixtures of `tests/oracle/`, except the request errors, `oracle.version` and the request that repeats a key.
  The script prints each fixture it leaves out.
- Core's `sighash.json`, and the base-mode records of Core's transaction corpus.
- Every proper prefix of every transaction of the two corpora, and each transaction followed by 1, 3 and 40 bytes.
- Field changes in the transaction corpus and the first 100 transactions of `sighash.json`.
  Each count and length is replaced by non-canonical forms, by `MAX_SIZE` and larger values, and by a truncated CompactSize.
  Also each version, sequence, output value and lock time replaced by boundary values.
- The same transactions rebuilt with no inputs, no outputs, or empty scripts.
- CompactSize values and encodings at every boundary of the forms and of `MAX_SIZE`.
- `sighash.legacy` on the first 25 transactions of `sighash.json`, at the boundaries of the input index and the hash type.
  Also transaction arguments that fail to read, and random script codes on all of its transactions.
- Random byte changes in the transactions of both corpora.
- All 198 transaction corpus records through both witness operations, with the 39 extended records also reported as a separate set.
- Every proper prefix of those 39 records through both witness operations, and each record with 1, 3 and 40 suffix bytes.
- Count, length and fixed-field changes in all 198 records through the witness operations, plus empty stacks, empty items and replacement stack contents.
- Hand-built cases from the known answers in `tests/KnownAnswers/Transaction.lean` (`Witness.cases`).
  They cover flags `02`, `03`, `ff`, zero flags, flags `01` with zero inputs, and errors before the flag check.
- 5,000 seeded byte mutations of the 198 records, each through both witness operations.
- The `large structured base` set, through both base operations and the transaction argument of `sighash.legacy`.
  It includes transactions with 253 or 254 inputs and outputs, 1000 inputs or outputs, and scripts of 4096 or 16384 bytes.
  Variants replace both vector counts, the first input script length and the first output script length with malformed encodings.
  They also truncate fields and scripts, and append trailing bytes.

The Script comparison reports these sets separately:

- Both scripts of every one of the 1,193 corpus records, as independent calls with empty initial stacks and unchanged effective flags.
  The comparison has no witness input: a record's witness is ignored, and only its two base scripts run.
- A composition for every record: `scriptSig`, then `scriptPubKey` with the first call's successful main stack.
  Each implementation supplies its own stack to its second call.
  A rejection or unsupported result ends that side's composition.
  The composition does not run `VerifyScript` or use the corpus's expected spending verdict.
  It ignores the record's witness and runs only the two base scripts.
- Eight synthetic legacy requests violate Core's flag dependencies, with each checker and flags 256, 2048, 2304 and 257.
  The comparator checks and excludes them as `harness-refused`.
- Every inside-milestone record through `script.verify_legacy`, separately with `base` and `transaction`.
  Each request uses the recorded spending transaction, input index and previous-output script.
- All 159 inside-milestone inputs of `tx_spends.jsonl`, with each checker and separate streams for accept and unknown expectations.
  Requests retain the exact transaction bytes, input index, previous-output script and flags.
  Core and Lean must accept all 91 accept inputs with the transaction checker.
  The run also fails if the number of acceptance checks differs from the size of that stream.
  The 68 null expectations supply outcome counts without fixture agreement claims.
- Targeted transaction-checker streams for CLTV and CSV under seed `20261107`.
  Each script pushes its operand, executes its named opcode, then drops the operand and pushes true.
  This construction reaches the target opcode without a signature check or an earlier Script error.
  Cartesian boundaries and 500 seeded cases per opcode vary version, locktime, sequence and operand.
  Boundaries include 499,999,999 and 500,000,000, equality, final sequences, versions 1 and 2, and disable and type bits.
- Seven refusal-precedence requests combine unsafe flags with malformed transaction bytes, trailing bytes, empty inputs or an out-of-range index.
  These errors must compare normally, without a harness-refused exemption.
- 2,000 legacy mutations for each checker, under seed `20261106`.
  Mutations change scriptSig, scriptPubKey, version, sequence, locktime or flags.
  A scriptSig mutation serializes a fresh length in a synthetic one-input transaction.
- Base-checker copies of the individual corpus evaluations, resource boundaries and 2,000 generated evaluations.
- Every opcode and every prefix of representative direct and extended pushes, including all short length-field and payload forms.
  Extra cases read at arbitrary offsets within push encodings and at the end.
- Below, at and above the 201-operation, 520-byte push, 1,000-item stack and 10,000-byte script limits.
  Cases include skipped branches, altstack moves and caller stacks above 1,000 items.
  Bounded pushes form accepted scripts of 9,999 and 10,000 bytes, followed by a 10,001-byte `SCRIPT_SIZE` case.
- 22 adapter-limit requests sent to both programs, 18 for Script and four for `pubkey.verify`, with results checked against the documented limits.
- 2,000 generated scripts under seed `20261105`, with nested conditionals, stack operations and numeric and hash candidates.
  Comparison depends on each returned capability result, rather than a fixed list of supported opcodes.

The work comparison reports these sets separately:

- D16's `bignum_SetCompact` cases and D7's six `get_next_work_*` cases from the oracle fixtures.
- Compact exponent, mantissa, sign and overflow boundaries, plus magnitudes around every bit boundary through 256 bits.
- Retarget timespan, rounding, height and parameter boundaries on all three networks, with UInt32 time endpoints.
  Spans −69, −68, −67, 307, 308 and 309 cover DigiShield's clamp edges for timespan 60.
  Spans −8, −7 and −6 cover the lower edge for regtest's timespan 1.
  The signed compact `0x04923456` checks that retarget arithmetic ignores the sign flag.
- The `regtest legacy wrap case`: selection height 0, last height 1, times 901 and 0, and bits `0x207fffff`.
  Core's multiplication wraps modulo 2^256, and returns `0x1f02467a`.
- Synthetic network chains at the legacy, DigiShield and minimum-difficulty boundaries, with strict delay endpoints.
- Testnet recovery walks to a nonminimum target or an interval boundary below height 145000.
- The 312 recorded mainnet headers as history for 310 candidates, heights 144721 through 145030.
  Height 144720 lacks its retarget ancestor and stays an oracle error fixture in the known-answer tests.
- A retarget whose ancestor traversal crosses a block with a null skip pointer.

The hash and block comparison reports these sets separately:

- All 315 recorded pure headers: fields, exact encoding, block hash and a three-byte suffix.
- Every proper header prefix, lengths 0 through 79, for all 315 records.
- Raw header field boundaries, including signed version bits and the AuxPoW flag.
- The 34 committed Merkle cases and three mainnet transaction-ID lists.
- Generated leaf lists of sizes 0 through 64, with aligned duplicates, complete-subtree duplicates and final-subtree extension.
- All committed RIPEMD-160 and Hash160 vectors, plus the 129 short and long NIST SHA-1 vectors and Core's ten SHA-1 vectors.
  These include million-byte inputs.
- The final input of each of 100 NIST SHA-1 Monte Carlo checkpoints.
  Python hashlib derives each 60-byte input independently, and NIST supplies the expected final digest.
  The comparator does not chain the oracle's intermediate digests.
  `lake test` checks the full 100,000-call chain.
- Generated binary hash messages of lengths 0 through 200 and around padding boundaries, up to length 1025, separately for each hash.

The fixture helper reads committed expectations and fixed header offsets independently of the executables.
The comparison checks complete results, including both byte orders, fields, consumption, remainder, truncation errors and mutation flags.
The Merkle caller bound is explicit, but the comparison uses only small lists.

Agreement covers the requests in the stream and nothing more.

Public-key mutations flip a `valid` field and fail with `PUBKEY_VALID`.
A mutation changes the signed recovery spend's verdict and fails with `SIGNATURE_VERDICT`.
The public-key stream includes all 464 bitcoin Wycheproof cases, with Core as the verdict source, including high S.
It includes key-parser boundaries and four Core-signed inputs, plus two reversed digest-one inputs.

The [fixture notes](../tests/cryptography/secp256k1/README.md) give the provenance and arithmetic of the constructed edge cases.
The 36 infinity inputs reject, and the 24 x-above-order inputs accept.
All 24 changed-S inputs reject.
Another 24 inputs retain the verification point above `n` but claim a different R scalar, and all reject.
These comparisons give finite evidence about verdicts, not a theorem that `mulAdd` equals Core's `secp256k1_ecmult`.

### Compiled Rust CompactSize

With `--rust-compactsize PATH`, the comparator selects only `compactsize.read` from the fixtures and CompactSize boundary set.
It sends all three programs the same 404 reader requests and compares their full responses.
The Rust crate has no encoder.
The comparator reads the oracle's version at runtime and passes it to the adapter.
The adapter identifies its projection as `FORMAT-rust-compactsize`.
[BUILDING.md](../BUILDING.md#compiled-rust-compactsize-comparison) gives the commands.

## Header proof-of-work evidence

The harness builds with `--disable-scrypt-sse2` and calls `scrypt_1024_1_1_256_sp_generic` for `scrypt.hash`.
Its build stamp records the Core revision, configure options, compiler versions, host architecture and flags.
`CheckAuxPowProofOfWork` also uses generic scrypt in this build.
Core's error logging goes to a harness `LogPrintStr` sink on standard error.
The sink changes no returned verdict and keeps logs outside the JSONL stream.

The full-header reader uses Core's `CBlockHeader` reader with the requested stream mode.
The predicates call `CAuxPow::check` and `CheckAuxPowProofOfWork` directly.
For proof of work, Core selects the actual record with `Params().GetConsensus(selection_height)`.
The harness does not reproduce that parameter table.

`core-oracle --check-auxpow-fixtures` reconstructs the 26 deterministic cases of Core's `check_auxpow` with Core's classes.
The adaptation preserves their construction order and replaces assertions with serialized records and Core verdicts.
The standalone harness omits the test's chain lock because it has no concurrent chain state.
Every comparison run requires exact payload bytes, arguments and verdicts to match `tests/block/check-auxpow.json`.
The comparator also checks the 16 boundary payloads and all six historical AuxPoW payloads against committed verdict expectations.

[The Core fixture report](../tests/block/core-header-pow.json) records all 321 historical header verdicts.
Each entry identifies exact bytes by SHA-256 in the existing header fixtures and gives the selected height.
The report names the network, the three relevant parameters, the Core revision and the scrypt variant.
All 321 headers pass Core's proof-of-work check, including six complete AuxPoW headers.
The fixture loader checks the report's identities and parameters before the comparison.

The header comparison includes these streams:

| Stream | Requests | Compared result |
| --- | ---: | --- |
| Header PoW fixtures | 407 | Sixteen exact scrypt digests, 321 historical header verdicts, 48 payload verdicts and 22 mined-case replays |
| Full header readers | 7,878 | Complete decoded fields, consumption, remainder or read error in both modes |
| Version boundaries | 207 | Two version gates at activation, record-selection and signed-version boundaries |
| Mutations, seed `20261108` | 1,075 | Payload/script mutations, version bits, nonces and child/parent `nBits` |

One hundred script mutations recompute the parent Merkle root to retain the coinbase-to-parent binding.
These mutations exercise the merged-mining search after the binding check passes.
Other reader cases cover malformed branch counts, optional transaction flags and empty witness stacks.
The comparison checks fixture expectations independently of cross-implementation equality.

The self-test changes each operation's compared result and requires `SCRYPT_DIGEST`, `FULL_HEADER`, `AUXPOW_VERDICT`, `HEADER_POW` or `HEADER_VERSION`.
A reconstruction-byte mutation must fail with `AUXPOW_RECONSTRUCTION`.
Assertions also check that a Lean diagnostic difference is ignored and that an integer cannot replace a Boolean verdict.
These checks supply finite comparison evidence, not an all-input equivalence theorem with Core.

`core-oracle --auxpow-pow-fixtures` ports `mineBlock` and `auxpow_pow` from pinned Core lines 327 to 451.
It mines the nonces again on every Core comparison and records all 12 predicate assertions.
It also records the 11 mining assertions and the two version/hash assertions.

All assertions must match Core's source expectations, and all captured bytes must match [the comparison records](../tests/block/auxpow-pow.json).
Lean and Core replay the 12 cases from identical pure-header and nullable payload bytes.
Ten cases also replay through the full-header reader.
The two flag/payload mismatches require split inputs.
These records are snapshots of runtime-mined comparison cases, rather than independent fixed known answers of the source test.

[The capture script](../scripts/capture_header_pow.py) records both header reports without running Lean.
The reports name their generator and capture date.
The [fixture notes](../tests/block/README.md#core-header-proof-of-work-report) give the exact capture command.
A mined-byte self-test mutation must fail with `AUXPOW_POW_RECONSTRUCTION`.
A separate verdict mutation targets the `payload_hex` path and must fail with `HEADER_POW`.
An extra diagnostic field on a full-header reader response must fail with `FULL_HEADER`.

## Contextual header comparison evidence

The harness calls Core's `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
The verdict is its return value, and the reject reason is `GetRejectReason` of its `CValidationState`.
Earlier revisions used a transcription of that function, H2 of [design record 0006](design/0006-contextual-header-validation.md#82-the-core-side).
The harness no longer contains it.

The harness sets Core's `fCheckpointsEnabled` and fills Core's `mapBlockIndex`.
Each known height adds the corresponding table hash with that height to the block index.
The remaining harness trust is the in-memory index.
The harness builds the `CBlockIndex` entries and their links from the request, and it refuses a view that is too short.
Core's function does not reach `VersionBitsState`, so the request needs no version-bits history.

The contextual stream contains these requests:

| Stream | Requests | Compared result |
| --- | ---: | --- |
| Contextual fixtures | 2231 | Verdict and first reject reason |
| Contextual boundaries | 172 | Verdict and first reject reason, checked against hand derivations |
| Contextual mutations, seed `20261109` | 500 | Verdict and first reject reason |

The fixture stream uses real mainnet candidates from five header ranges.
Chain acceptance supplies their expected verdicts with adjusted time equal to the candidate time and no known checkpoints.
The 172 boundary expectations follow D33 and the hand derivations in `KnownAnswers.ContextualCheck`.
They cover all seven checks, first-failure order, medians near genesis and out of order, equivalent-target compact encodings, checkpoint equality and disabled checkpoints.
They also cover signed versions, the future-time bounds, AuxPoW and BIP heights on all networks, and testnet delay boundaries at candidates 100001, 157500 and 157501.

A further 500 requests mutate version, time, bits, adjusted time or known checkpoints with seed `20261109`.
They use 167 mainnet, 167 testnet and 166 regtest contexts.
Mainnet and testnet checkpoint mutations include table heights above the candidate, which can produce `bad-fork-prior-to-checkpoint`.

The comparator self-test corrupts `valid` and `reject_reason` independently.
These mutations must fail with `CONTEXTUAL_HEADER`.
A third mutation swaps one rejection string for another on a request without an independent expectation.
That mutation preserves the response shape and must fail the stream comparison of result values.
It also checks Boolean types, result fields, acceptance reasons, rejection reasons and the exclusion of Lean diagnostics.
These runs give finite evidence, not an all-input equivalence theorem with compiled Core.

## Transaction and block check comparison evidence

The harness calls Core's own `CheckTransaction`, `CheckBlock` and `GetLegacySigOpCount` (D106), on objects that Core's stream code reads.
The comparator requires equal `ok` fields, except the oracle's `diagnostic`, and equal `error` objects.
It also checks both sides against Core's text: the score and the corruption flag of each reason, and the reject code 16.
It checks the block hash against `hashlib`, and `base_size` against the byte count in base mode.
A full run fails with `REASON_NOT_REACHED` if Core never returns one of the reachable reasons of design record 0010, section 4.
`bad-txns-oversize` is exempt for `block.check`: the size test of `CheckBlock` (line 2972) comes first, and both programs return `bad-blk-length`.

The 3,616 requests of the full run are in ten sets, defined in `scripts/oracle_block_check.py`:

| Set | Requests | Contents |
| --- | ---: | --- |
| Known answers | 61 | One case or more for each reason, with the expected result read from Core's text |
| `tx.check` reasons | 242 | Each reason of `CheckTransaction` with its boundary values, both values of `check_duplicate_inputs`, and pairs of faults in each order |
| `block.check` transaction reasons | 222 | The same faults in a transaction of a block |
| `block.check` reasons | 448 | Each reason of `CheckBlock`, with the four combinations of the two flags. Mutations of the mainnet genesis block and of synthetic blocks, and Merkle duplications at the leaf level and one level above |
| Signature operations | 724 | Exactly 20,000 and 20,001 operations, both multisig opcodes after each of `OP_1` to `OP_16`, short pushes that hide later opcodes, opcode bytes in push data, and a coinbase `scriptSig` |
| Readers and witness data | 976 | Every proper prefix of a small block, bytes after a block, counts above `MAX_SIZE`, counts that are not canonical, the extended format in both modes, and unknown optional data |
| Real full headers | 402 | The mainnet full headers of [the AuxPoW activation fixture](../tests/block/mainnet-auxpow-activation-full-headers/README.md) before a synthetic transaction list, with `check_pow` true and `check_merkle_root` false |
| Size limits | 16 | Transactions and blocks of exactly 1,000,000 and 1,000,001 base bytes |
| Mainnet rule changes | 168 | The 17 real blocks at and next to the rule changes of design record 0010, with both flags in both modes, and four mutations of each block ([fixture](../tests/block/mainnet-blocks/README.md)) |
| `tx.check` corpus | 357 | The records of `tx_valid.json` and `tx_invalid.json` (D28, D29), with no expected value: agreement of the two programs |

Every request agrees.
In the full run Core returns each of the seven reasons of `CheckBlock` 30 times or more.
It returns each of the nine reasons of `CheckTransaction` 3 times or more.
`scripts/test_oracle.py` checks 3,233 requests that have an expected value, and 25 argument errors, without Core.

### Real mainnet blocks

`scripts/fetch_blocks.py` read three sets of blocks from the maintainer's mainnet node on 2026-11-13, and checked each block before it wrote a fixture.
[The fixture README](../tests/block/mainnet-blocks/README.md) records the source, the checks, the sizes and the label of each block.

| Set | Heights | Blocks | `pinned` | `linked` | Compared in |
| --- | --- | ---: | ---: | ---: | --- |
| Rule changes | 144,998 to 145,001, 371,336 to 371,338, 599,998 to 600,001, 1,034,382 to 1,034,384, 3,464,750 to 3,464,752 | 17 | 17 | 0 | The full run, set *Mainnet rule changes* |
| Genesis to 10,000 | 0 to 10,000 | 10,001 | 10,001 | 0 | `--mainnet-blocks` |
| Recent | 6,455,302 to 6,456,301 | 1,000 | 0 | 1,000 | `--mainnet-blocks` |

A `pinned` block has a hash that a committed fixture or a Core checkpoint gives.
A `linked` block has no pinned hash.
It is consistent with its header and with its neighbours, and its place in the chain rests on the node.
The linked blocks are the whole recent range.
The blocks at heights 599,998 to 600,001 match a committed header fixture.
The node and two public TLS Electrum servers agreed on those bytes, but no checkpoint connects to that range.

The rule-change blocks are committed.
The two ranges have 44.0 MB and 19.9 MB, so they are assets of a GitHub release (design record 0010, decision 2).
`python3 -I scripts/fetch_release_blocks.py` downloads them, requires the SHA-256 values of the committed `tests/block/mainnet-blocks/release.json`, and repeats the checks of the fetch.
Then this command compares every block of both ranges:

```bash
python3 -I scripts/compare_core.py --mainnet-blocks build/mainnet-blocks .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

Each request has `check_pow` and `check_merkle_root` true, in the mode `allow_witness`.
Both programs must return a valid verdict, with the hash and the number of transactions of the manifest.
The expected base size is the size of the block without the witness data of the parent coinbase in its AuxPoW payload.
Three blocks of the recent range have such data, 36 bytes each.

All 11,001 requests agree.
The run fails with `BLOCK_ASSETS` when a file is absent or does not have its committed hash.
It fails with `REQUEST_COUNT` when the stream does not hold one request for each block of `release.json`.

The ranges are a separate run, not sets of the full run.
The comparator's self-test repeats the full run twice, with the oracle in both places.
On a development machine the oracle takes about 70 seconds for the 11,001 blocks, and Core takes about 3 seconds.
The largest sigop count of a block is 3,367, so the cost of [issue 149](https://github.com/dghelm/DogeLib/issues/149) does not show on these blocks.

This closes exit condition 1 of stage 0010a for `block.check`.
[`block.contextual_check_body`](#contextual-block-body-comparison-evidence) closes the other part.
`python3 -I scripts/test_fetch_blocks.py` and `python3 -I scripts/test_fetch_release_blocks.py` test the checks of the two fetch scripts on synthetic blocks.

Three cases have no request.
A block with more than 1,000,000 transactions has at least 10 MB, and the size clause rejects it too.
A sigop product that wraps modulo `2^32` needs `2^30` operations.
The strict chain ID rule through `block.check` needs a mined mainnet header, and `block.check_pow` covers that rule.

Until [issue 149](https://github.com/dghelm/DogeLib/issues/149) was fixed, the oracle's sigop count took time that grew with the square of the number of instructions.
A `tx.check` request whose one input has a `scriptSig` of 80,000 `OP_0` bytes (`0x00`) took about 3 seconds with the oracle of `main` at `bf5598e`.
So the requests of a megabyte hold one large push, and no request has more than about 30,000 separate opcodes in one script.
The count now reads with `nextOp`, in time linear in the length of the script.
The same request takes 0.04 seconds, and one with 1,000,000 `OP_0` bytes takes under 0.5 seconds.
Each time is the best of a few runs of the oracle on one core of a shared development machine, at nice 19.

## Contextual block body comparison evidence

The harness calls Core's own `ContextualCheckBlock` (D33) on a `CBlock` that Core's stream code reads.
The harness builds the predecessor and the version-bits boundary from the chain.
The comparator requires equal `ok` fields, except the oracle's `diagnostic`.
It also checks both sides against Core's text: the score of each reason and the reject code 16.
A full run fails with `REASON_NOT_REACHED` if Core never returns one of the four reachable reasons of design record 0010, section 4.

The 22 requests are in six sets, defined in `scripts/oracle_contextual_body.py`:

| Set | Requests | Contents |
| --- | ---: | --- |
| Valid | 3 | The genesis block, and final blocks below the first period |
| Finality | 5 | A non-final lock time by time and by height, a final sequence, lock time 0, and a non-final coinbase |
| Coinbase height | 8 | `bad-cb-height` at a period boundary, the exact boundary 1,034,382 and 1,034,383, a short height, and valid heights at the BIP65 boundary |
| Witness | 2 | Witness data in a transaction and in the coinbase |
| Weight | 2 | Blocks of exactly 1,000,000 and 1,000,001 base bytes |
| Version bits | 2 | A boundary below the CSV start (case 1) and one at or after the CSV timeout (case 2, seeded `FAILED`) |

The height boundaries use a contiguous chain back to the aligned version-bits boundary, about 6,200 entries for 1,034,383 and 7,300 for 3,464,751.
The other requests use a short chain, so the six sets add about 39,600 chain entries in all.
Every request agrees, and Core returns each of the four reasons.
`scripts/compare_core.py --mainnet-blocks` also compares the body on 11,018 real blocks: the genesis-to-10000 range, the 1,000 most recent blocks and the 17 rule-change blocks.
Below the first period the chain is the predecessor alone, and otherwise it reaches the aligned boundary from the committed blocks and the version-bits header runs of `tests/block/mainnet-blocks/version-bits-headers`.
`scripts/test_oracle.py` checks the 22 requests against their expected verdicts without Core.

## Block validation comparison evidence

The harness calls Core's own five functions, as in [block validation in the harness](core-harness.md#block-validation-in-the-harness).
The comparator requires equal block records, except the oracle's `diagnostic`, and an equal digest and size of the final coin set.
It checks both sides against Core's text: the score and the code of each reason of `ConnectBlock`.
A full run fails with `REASON_NOT_REACHED` if Core returns one of the nine reachable reasons of design record 0010, section 5, for no block.

The 42 requests are in eight sets, defined in `scripts/oracle_block_validate.py`.
They need no download.
One request starts at the real genesis block.
The others start at a committed rule-change block: each keeps the real header and chain of that block, replaces the transactions and the Merkle root, and clears `check_pow`.
Their coins are synthetic.

| Set | Requests | Contents |
| --- | ---: | --- |
| Genesis chain | 2 | The genesis block with its real proof of work. A chain of 33 made blocks on the genesis block, with 17 rejected candidates: maturity 30 at depth 29 and 30, the genesis coinbase, unspendable outputs, a missing index, a double spend within a block, a spend of an output that the block creates later, a spend within the block, `bad-txns-in-belowout`, and four script failures |
| Coinbase maturity | 7 | Depth 29 and 30 for a coin below height 145,000, depth 239 and 240 from it, a coin of maturity 30 spent above height 145,000, and a coin above the spend height |
| Values and coinbase limit | 7 | `bad-txns-inputvalues-outofrange`, `bad-txns-in-belowout`, a coin of `MAX_MONEY`, and a coinbase that claims one koinu too much at heights 145,000, 599,999 and 600,000, with and without a fee |
| Arithmetic domain | 5 | Nine fees of `MAX_MONEY` in one block, which Core accepts. A tenth fee, and ten coins of `MAX_MONEY` in one transaction, which end the range. A supplied amount above `MAX_MONEY` |
| Signature operations | 3 | Exactly 20,000 operations, and 20,001 by a P2SH input, by a later transaction, by a legacy operation in an output and by one in the coinbase. The accurate count of `OP_16 OP_CHECKMULTISIG`. A `scriptSig` that is malformed, has an opcode above `OP_16`, or ends with an opcode that pushes nothing, each of which counts 0 |
| Script failures | 8 | A signature that is not strict DER below and from `BIP66Height`, with a right and a wrong signature. `OP_CHECKLOCKTIMEVERIFY` below and from `BIP65Height`. The predecessor at `BIP34Height` and above it |
| BIP30 | 4 | A coinbase and another transaction whose IDs have unspent coins. The same coinbase with the ancestor hash `BIP34Hash`, where Core skips the test and replaces the entry |
| Order and adapter errors | 6 | One block for each of the five steps, with a later fault in each. A truncated block, bytes after a block, and the three chain errors |

The expectations come from Core's text.
`scripts/oracle_block_validate.py` also computes every digest a third time, from the definition in [digests](oracle.md#digests), in a model of the coin set that takes the verdicts from the expectations.
All 42 requests agree with Core and with the expectations.
The block records hold 60 accepted blocks and 54 rejected ones, and Core returns each of the nine reasons.

The signatures are made in the script with the private key 1, which is public test data.
A signature that is not strict DER has one more zero byte before R.
Core's verdict on each signature comes from the comparison, not from the script.

The request of the tenth fee is the example of design record 0010, section 3.
The oracle returns `out_of_domain_at`, and the harness gets the request without that block.
So no request makes Core add past the `int64_t` range.

`scripts/test_oracle.py` checks the 42 requests against their expectations without Core.

### Real mainnet blocks from the genesis block

`scripts/compare_core.py --mainnet-blocks` sends one more request: all 10,001 blocks of heights 0 to 10,000, in one `block.validate` request with an empty chain and no coins.
Both flags are true, so each block passes its real proof of work.
Each program builds the whole coin set.

Both programs accept every block, and all 10,001 block records agree.
So do the 11 digests of the whole set, at each multiple of 1,000 and at the end.
The blocks have 155,931 transactions.
They spend 197,189 coins and create 340,566, and the final set has 143,377 coins.
Every spent output in the range is Pay to Public Key Hash or Pay to Public Key, so each input runs one ECDSA verification.

On a development machine the oracle takes about 460 seconds for this request on one core, and Core takes about 12 seconds.
The comparator runs the request in a second oracle process, at the same time as the other requests of `--mainnet-blocks`.
The default timeout of that mode is 3,600 seconds.

This closes the first part of exit condition 1 of stage 0010b: agreement on the genesis-to-10,000 range, digests included.
The recent range needs supplied coins, which design record 0011 takes from a coin-set snapshot.
The range to height 145,000 is a gate outside CI, and the next section records its runs.
Neither is in this comparison.

### Replay of mainnet to height 145,000

`scripts/replay_blocks.py` replays mainnet from the genesis block to height 145,000, the whole random-reward era.
It is the gate *Mainnet replay to 145,000* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.
This section records a run that started on 2026-11-19 and ended on 2026-11-20.
It also records a later run, which compares the [total value](oracle.md#total-value) of the coin set as well.

The script checks the two fixtures against their manifests and requires a pinned hash for every block.
It writes all 145,001 blocks to one file of 3,024,443,782 bytes, with the SHA-256 value `5295801124f275bd7b6aad9f60bc734631e8157d99a07d8a9c66ee8f2bd034e3`.
Each program gets one request that names the file through `blocks_file`, with the empty chain, the empty coin set and both flags true.
So each block passes its real proof of work, and each program builds the whole coin set.

| Input | Value |
| --- | --- |
| Oracle | Built from commit `873f0da` of pull request 170, which is `main` at `f7aeb10` with the file argument |
| Core harness | Built from the harness sources of the same commit, with Core at `e0a1c157` |
| Heights 0 to 10,000 | The release asset of the [fixtures](../tests/block/mainnet-blocks/README.md), 10,001 blocks |
| Heights 10,001 to 145,000 | `scripts/fetch_blocks.py --range 10001 145000` from a node `/Shibetoshi:1.14.9/` on 2026-11-18: 135,000 blocks, 2,979,346,409 bytes, SHA-256 `b3354074540c702ffa8f958a1276c4fb8c911a9be461d6f89e8980ef2c0c7f14`. The file is not committed and is not a release asset |

Later commits of the pull request change the answer to a failed read of the file alone, and no read failed in this run.

Both programs accept every block, and all 145,001 block records agree, each with the digest of its coin changes.
So do the 147 digests of the whole set, at each multiple of 1,000 and at the end.
The blocks spend 15,048,625 coins and create 20,143,296.
The set after height 145,000 has 5,094,671 coins, and its digest is `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d`.
The last block has the hash `cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72`.
No block leaves the arithmetic domain: `out_of_domain_at` is null.

The oracle took 61,365 seconds, about 17 hours, on one core at low priority, on a machine that ran other work.
Its resident memory was 7.6 GB when it passed height 112,000.
Core took 1,340 seconds.

An earlier run used an oracle from before pull request 173, which made block reads and signature hashes faster and changed no result.
That run took 149,428 seconds for the oracle.
Its response is byte for byte the response of the run above, so two builds of the oracle agree with Core on this range.

A later run used the oracle and the Core harness built from commit `18310a8` of pull request 175, which added `set_value` and merged as `3a8401b`.
It read the same blocks, from a file with the same SHA-256 value.
The command is the one of the gate in [AGENTS.md](../AGENTS.md#checks), run with `taskset -c 6 nice -n 19`.
It started at 2026-11-20T16:50:34Z and ended at 2026-11-21T11:59:26Z, and it exited with status 0.

Both programs accept every block, and the block records, the 147 digests and the 147 totals of the whole set agree.
The counts of coins, the digest of the set and the hash of the last block are those of the run of 2026-11-19.

| Quantity | Koinu |
| --- | --- |
| `set_value` after height 145,000 | 6,117,565,627,100,000,000 |
| Sum of the subsidies of heights 1 to 145,000 | 6,122,723,674,900,000,000 |
| Subsidy sum minus `set_value` | 5,158,047,800,000,000 |

Both programs gave the same subsidy for each height from 1 to 145,000.
Each of the 147 totals is at most the subsidy sum up to its height, which is the bound of `chain_issuance_bound`.
The check does not say why the set holds less than the subsidy sum.

The oracle took 67,606 seconds, about 19 hours, on one core at low priority, on a machine that ran other work.
Core took 1,283 seconds.

The runs are evidence for these blocks alone.
A node supplied the blocks above height 10,000.
Each has a pinned hash, and the [fixtures](../tests/block/mainnet-blocks/README.md) state what a pinned hash commits to.
This replay stops at height 145,000.
[Ranges A to H](#ranges-a-to-h) and [the CSV window ranges E1 and E2](#the-csv-window-ranges-e1-and-e2) cover selected ranges above height 145,000 from snapshots.

### Ranges from a snapshot

`scripts/snapshot_range.py` runs a range of mainnet blocks from a [coin-set snapshot](oracle.md#coin-set-snapshots) in both programs.
It is the gate of [design record 0011](design/0011-mainnet-ranges.md), stage 1, which tests the snapshot path on blocks that the replay from the genesis block covers.
A range from the height `a + 1` to the height `b` starts from the snapshot at `a`.

The script first lets the harness replay the blocks from the genesis block, from the empty coin set.
In that *pass* the harness writes each snapshot and reports the digest of the whole set at `b`.
The script computes the SHA-256, the digest, the number of coins and the total value of each snapshot again from the file.
It requires the values of the harness and the committed [manifest](../tests/block/mainnet-blocks/README.md#coin-set-snapshots).
Both programs then get one request with `coins_file` and the blocks of the range.
A range agrees when all of these hold:

- Both programs report the digest and the number of coins of the manifest as the start.
- Both programs accept every block, with equal block records.
- Both programs report the digest of the pass at `b` as the end.
- The block records equal those of the same heights in the pass, without the digests of the whole set.
- The oracle with `coins_in_memory` returns the same `ok` object.

The script also runs 29 changed copies of the snapshot, each with the first 10 blocks of the range, in both programs:

| Change | Cases | Required result |
| --- | ---: | --- |
| Another amount, script, height or coinbase byte in one record. A removed record and an added record | 6 | Both programs report a start digest that is not the manifest's. It is the digest that the script computes from the changed file. The script also accepts the error `not_linked` from both programs, after a block that the changed coin makes both reject. In the two recorded runs, all six gave a changed start digest |
| Two records in the wrong order, and one record twice | 2 | `coins_file_order` |
| A file that ends inside a record, and a byte after the last record | 4 | `coins_file_truncated` |
| Each other fault of the [checks](oracle.md#coin-set-snapshots): the tag, the entry, the amount with the values `MAX_MONEY` + 1, -1 and another negative number, the index, the script, the height, the coinbase byte and the length of the script | 15 | The error of the fault, with the position of the record |
| A removed record whose transaction ID a block of the request names | 1 | A changed start digest, or the error `not_linked` after a block that both programs reject |
| A removed record whose transaction ID no block of the request names | 1 | Both programs return the block records of the unchanged snapshot. The start digest and the end digest differ from those of the unchanged snapshot |

The last step runs the 33 small requests of the [full comparison](#block-validation-comparison-evidence) that have one record for each block, with their coins in a snapshot.
Both programs must return the result of the request with `coins`, without the digests of the whole set in the block records.
The start digest must be the one that `Model` of `scripts/oracle_block_validate.py` computes.
These requests hold rejected blocks, the BIP30 cases and the script failures.
`scripts/test_oracle.py` runs the same requests and 33 changed synthetic snapshots or requests in the oracle alone.

**The short form.**
CI runs the script on the released blocks of heights 0 to 10,000, with the snapshot at height 9,000.
The snapshot has 114,056 coins and 8,719,196 bytes.
Heights 9,001 to 10,000 agree: the blocks spend 47,185 coins and create 76,506, and the set after height 10,000 has the 143,377 coins of the replay.
On a development machine the run takes about 160 seconds on two cores, of which each oracle run of the range is about 106 seconds.

**Range S.**
This part records one run of range S of the design record, heights 100,001 to 101,000, on 2026-11-20.
It is the gate *Snapshot range S* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.

| Input | Value |
| --- | --- |
| Oracle and Core harness | Built from commit `f42b049` of the pull request, with Core at `e0a1c157` |
| Blocks | The fixtures of the [replay to height 145,000](#replay-of-mainnet-to-height-145000). The file of all 145,001 blocks has the SHA-256 value `5295801124f275bd7b6aad9f60bc734631e8157d99a07d8a9c66ee8f2bd034e3` of that replay |
| Command | The gate command, with `--write-manifests`, because the run wrote the two committed manifests |

The pass took 1,524 seconds, and the harness accepted every block.

| Snapshot | Coins | Bytes | Digest of the set | SHA-256 of the file |
| --- | ---: | ---: | --- | --- |
| Height 100,000 | 5,556,212 | 422,359,596 | `dda64f97c6bc79ee64954d5e95ba26fb207c15b5255ffd041be333d6cbe4e817` | `fc9a4ebf7a2ef72a555aa1caf06583160d1e5785d18738cca729d3cd3783bca9` |
| Height 145,000 | 5,094,671 | 387,316,918 | `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` | `0fa2f2a1e1aa43c54bf877e5aed1884cb9731412c45a06c9b8a9c84ad0b32012` |

The snapshot at height 145,000 has the number of coins and the digest of the recorded replay.
The script holds both values as constants and requires them in every run.
So the harness's snapshot at that height is the set that the oracle reached from the empty set, if double SHA-256 is collision resistant.

Range S agrees.
Both programs start from 5,556,212 coins with the digest of the manifest, and accept all 1,000 blocks with equal block records.
The blocks spend 121,665 coins and create 151,427.
Both programs end with 5,585,974 coins and the digest `e6aeca49614547750a803c3d4dd85f6986f69f819a207531f896e1aa7840aa1b`, which the pass reports at height 101,000.
The block records equal those of the pass at the same heights.
The oracle with `coins_in_memory` returns the same `ok` object.
All 29 changed snapshots give their required results.

Core took 18 seconds for the range.
The oracle took 682 seconds on the coins that the blocks name, with its two reads of the snapshot, and 728 seconds with `coins_in_memory`.
A separate run of the first form alone had a peak resident memory of 317 MB.
The whole run took about 60 minutes on four cores at low priority, on a machine that ran other work.

The run is evidence for these blocks, and it is one run.
It tests the snapshot path: every block of the range is also in the replay from the genesis block, so the range adds no agreement on a new block.
The oracle did not check the blocks between heights 101,001 and 145,000 in this run.
The hypothesis of section 3.4 of the design record applies to every later range from a snapshot: the comparison does not show that the snapshot is Core's coin set.

### Measurements for the Core pass

Stage 0 of [design record 0011](design/0011-mainnet-ranges.md) measures the chain, the coin set at the tip, and the memory of the harness.
The stage decides whether the Core pass fits the development machine, and whether the harness carries the set in its map or in Core's `CCoinsViewDB`.
The measurements were made on 2026-11-20.

**The node.**
The node is `/Shibetoshi:1.14.9/`, and the measurements read it over read-only RPC.
At height 6,465,793, with the block hash `9ebb986b0b16a65680c5f3447baca7154e2999680c76c97f24c4441897bc7385`, the node reported these values:

| RPC value | Value |
| --- | ---: |
| `getblockchaininfo` `size_on_disk`: the block files and the undo files (`CalculateCurrentUsage`, `validation.cpp`, lines 3440 to 3449) | 204,053,139,409 bytes |
| `gettxoutsetinfo` `transactions`: the transaction IDs with an unspent output | 181,209,861 |
| `gettxoutsetinfo` `txouts`: the coins | 202,470,869 |
| `gettxoutsetinfo` `bytes_serialized`: 32 bytes and the stored value of each transaction ID (`rpc/blockchain.cpp`, lines 874 to 905) | 11,466,045,328 |
| `gettxoutsetinfo` `hash_serialized` | `a053d324494c91478b7e8525f52b062b56e976c61ef856509d59d33360048680` |
| `gettxoutsetinfo` `total_amount` | 156,830,432,860.16806 DOGE |

`gettxoutsetinfo` ran once and took 198 seconds.
The block files alone have no RPC value, so the sample below estimates them.

**The chain.**
`scripts/count_blocks.py --sample-heights --last 6465793` splits the heights from 0 to 6,465,793 into strata of 1,000 heights, and draws one height from each with the seed 20261120.
`scripts/fetch_blocks.py --heights` fetched the 6,466 sampled blocks from the node and checked them.
The fixture has 179,503,696 bytes of blocks, and its `blocks.bin` has the SHA-256 value `d3e682e3d48541cf71e71d7d869f4e72d1b964eceb2fc14f1eeb26d1f3fdcbb2`.
Of the blocks, 147 are `pinned` and 6,319 are `linked`.
The fixture is not committed.

`scripts/count_blocks.py --estimate --last 6465793` scales each stratum to the number of its heights: 1,000, or 794 for the last.
The standard error comes from collapsed strata, so it is itself an estimate.

| Quantity, heights 0 to 6,465,793 | Estimate | Standard error |
| --- | ---: | ---: |
| Bytes of the blocks | 179.5 GB | 6.4 GB |
| Transactions | 400.2 million | 18.0 million |
| Inputs | 763.8 million | 27.6 million |
| Outputs that enter the coin set | 936.4 million | 42.3 million |

The heights from 4,500,000 to 5,499,999 hold about 103 GB of the bytes and 271 million of the transactions.
There, 100,000 blocks have up to about 13 GB.

Two checks support the estimate.
The same sampled blocks give 217.3 million transactions up to height 5,050,000, and Core's `chainTxData` gives 226,128,837 (`chainparams.cpp`, lines 207 to 215).
The estimate of 179.5 GB is below the 204.1 GB of `size_on_disk`, which also counts the undo files.

Section 2 of the design record estimated 0.47 to 0.56 billion inputs.
The sample gives 0.76 billion, about 1.4 to 1.6 times as many.
Core took 89 µs for each input in the recorded run.
At that rate the pass needs about 19 hours on one core, without the cost of `CCoinsViewDB`.
At the 4.1 ms of the oracle, a replay of every block would need about 36 days on one core.
Design record 0011 does not propose that replay.

**The count script.**
`scripts/count_blocks.py` without a mode counts the transactions, inputs and outputs of a fixture.
On the recent range it gives every value of the second column of section 2 of the design record.
On the fixtures of heights 0 to 145,000, with `--coin-set`, it gives the 15,048,625 inputs and the 20,143,296 created coins of the recorded replay.
The set after height 145,000 has the 5,094,671 coins of that replay, under 2,675,914 transaction IDs.

**The memory of the harness.**
The harness carries the set as a `std::map` from the transaction ID to Core's `CCoins` (`harness/core/core_block_validate.inc`).
Two runs measured it with `/usr/bin/time -v`, each with one `block.validate` request from the empty set, as in the replay above.
The harness was built from commit `18310a8`, whose harness sources and build script equal those of `main` at `ae66db4`, with Core at `e0a1c157`.

| Run | Coins after the last block | Transaction IDs | Peak resident memory | Memory per coin | Memory per ID | Time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Heights 0 to 72,500 | 4,222,230 | 2,857,327 | 1,004.8 MB | 238 bytes | 352 bytes | 448 seconds |
| Heights 0 to 145,000 | 5,094,671 | 2,675,914 | 1,545.4 MB | 303 bytes | 578 bytes | 1,166 seconds |

The second run reports the set digest `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` of the recorded replay.
The peak includes the response, which holds one record for each block.
It is 28 MB and 57 MB of JSON in the two runs.

Suppose that the lower ratios of the first run hold at the tip.
Then the map needs about 48 GB for 202.5 million coins, or about 64 GB for 181.2 million transaction IDs.
No run measured a set of that size.
The machine has 125 GiB of memory, and `free` reported 46 GiB available, with other work running.

**The decision: `CCoinsViewDB`.**
The map does not fit reliably at the tip.
So stage 0 selected Core's `CCoinsViewDB` on a scratch directory for the Core pass, with a `CCoinsViewCache` of bounded size over it.
These measurements preceded the `CCoinsViewDB` implementation.
[The Core pass](core-harness.md#the-core-pass) describes the database mode that the harness uses, and [the recorded Core pass](#the-recorded-core-pass) records its mainnet run.

**The disk.**
`df` reported 909 GB available on 2026-11-20, after this stage's measurements.
Design record 0011 recorded 122 GB earlier that day.
The pass needs this space at one time:

| Item | Size |
| --- | ---: |
| One segment of blocks, which the pass deletes when the harness accepts it | At most 4 GB. Above height 4,500,000 a fetch then holds about 30,000 blocks |
| The `CCoinsViewDB` directory | At most about 35 GB: twice the keys and values of a set with 1.5 times the coins of the tip |
| The start snapshots of the eight ranges and two segment snapshots | At most about 231 GB, if no set has more than 1.5 times the coins of the tip |

The node's `bytes_serialized` of 11.5 GB is the sum of the keys and values of its database at the tip.
It does not count the other files of LevelDB or the space that a compaction needs, and no measurement here covers them.
So the table allows twice that size.

A record of a snapshot has 51 bytes and the script.
The coins at height 145,000 have 25.0 bytes of script on average, which gives 76 bytes for each record.
With the same average, a snapshot of the set at the tip has about 15.4 GB.
The coins at heights between 145,000 and the tip are not measured, and the pass reports them.

Under these assumptions the sum is at most about 270 GB, so the pass fits the 909 GB available.
The assumptions are the number of coins of each set, the average script length and the overhead of the database.
With 122 GB it fits only if the pass deletes each start snapshot after the oracle runs its range.

### The recorded Core pass

This part records the run of [the Core pass](core-harness.md#the-core-pass) for stage 2 of [design record 0011](design/0011-mainnet-ranges.md).
It is the gate *Core pass* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.

| Input | Value |
| --- | --- |
| Harness | `core-oracle-trap`, built by `scripts/build_core_harness.sh --trap-overflow` from commit `46c8fa8` of pull request #185, with Core at `e0a1c157`. Its SHA-256 value is `bc49248d69c75f99b05ec8bc3c4484713edf9b126d7bd4eb4249f864aeaccd0f`. The harness of `main` at `df1b04c` differs from it only by the argument `force_csv_active` of #184, which the pass never sends |
| Script | `scripts/core_pass.py` at commit `1deb9d1` of the same pull request. The script of `df1b04c` differs in two places. It opens the headers read-only beside a running pass, and it saves the state before it deletes an old restart snapshot. Neither changes a request or a check |
| Blocks | Heights 0 to 145,000 from the fixtures of the [replay to height 145,000](#replay-of-mainnet-to-height-145000). Every later block from the maintainer's node, in segments of 100,000 blocks and at most 4 GB |
| Command | `nice -n 19 taskset -c 8,9 python3 -I scripts/core_pass.py --state build/core-pass --cache-mb 6144 --local <genesis-10000> --local <range-10001-145000> build/core-harness/core-oracle-trap`, started at 2026-11-20T23:14Z |

The pass ended at 2026-11-21T16:02Z, at height 6,465,793 with the block `9ebb986b0b16a65680c5f3447baca7154e2999680c76c97f24c4441897bc7385`.
It accepted all 6,465,794 blocks, 182,679,205,792 bytes, in 84 segments.
The segments took 60,266 seconds together, and the longest took 1,928 seconds.
Every checkpoint of Core held, and the trap build reported no signed overflow.

At height 6,465,793, three values of the pass equal those of the node's `gettxoutsetinfo` in the [measurements of stage 0](#measurements-for-the-core-pass) (decision 7):

| Value | The pass and the node |
| --- | ---: |
| `hash_serialized` | `a053d324494c91478b7e8525f52b062b56e976c61ef856509d59d33360048680` |
| `transactions` | 181,209,861 |
| `txouts`, the coins | 202,470,869 |

The script requires all three.
`hash_serialized` covers the best block, and the ID, the index, the amount and the script of each coin.
So the pass's set at the tip and the node's set have the same coins, amounts and scripts, if double SHA-256 is collision resistant.
It does not cover the height or the coinbase flag of a coin, which the digest of the set covers.
The node is not the reference software revision: it is `/Shibetoshi:1.14.9/`, and the harness is Core at `e0a1c157`.

At that height the set has the digest `6ff386f2a37464a65e11a9e48673c602e2a4f1a707040e12a7c4d06751cb90b5` and a `set_value` of 15,683,043,286,016,806,072 koinu.
The value exceeds 2^63 - 1, the largest `CAmount`, and the harness's 128-bit sum holds it exactly ([total value](oracle.md#total-value)).
The node's `total_amount` was 156,830,432,860.16806 DOGE in the record of stage 0, which agrees with the pass to the digits that the record kept.
Core at `e0a1c157` sums `total_amount` in an `arith_uint256` (`rpc/blockchain.cpp`, lines 868 and 885), so that sum does not wrap either.
The script does not compare `total_amount`.

The pass has this snapshot at the start of each range.
Each committed manifest in [`tests/block/mainnet-blocks/snapshots`](../tests/block/mainnet-blocks/snapshots) is the file that the pass wrote:

| Snapshot | Coins | Bytes | Digest of the set | SHA-256 of the file |
| --- | ---: | ---: | --- | --- |
| Height 145,000, range A | 5,094,671 | 387,316,918 | `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` | `0fa2f2a1e1aa43c54bf877e5aed1884cb9731412c45a06c9b8a9c84ad0b32012` |
| Height 370,336, range B | 8,576,188 | 654,238,056 | `3d63c9adf6858f73548dd3f0028ae3b6fadc71e837d6107c22aa43afc003b957` | `f16e3bf23a92d5a8112bbfdd2d07c6ab21a6cdeb6e45c9a7c22d252f0c72be0c` |
| Height 598,999, range C | 15,572,301 | 1,186,513,976 | `4355e90c77611cf22e2e1e70c4814f1d230481de5093c282a022388d66672856` | `234d2af5029ffea71986a2e18a5488515cb6bc8583ab29568c31562bd5211707` |
| Height 1,033,382, range D | 16,869,346 | 1,285,351,570 | `dd23f0095e9dd8f43f86fcab3e1f704e487974a7c8643bb365e4673c2e07d0e2` | `2ef63d136fcb1b4a61b6bc86c9f67af1832575c740f4a8644af81f5db5fb34b6` |
| Height 3,463,750, range F | 14,485,802 | 1,103,862,190 | `eaf159fc6ec3a7f8a2472271a8f162534f15c2166fd2400c7d37f1808a38a7b8` | `1043e1a13dca76e739dbb2f474594926ec57b604a5e1f928f6fec61bc1cf82c7` |
| Height 5,049,000, range H | 87,775,851 | 6,695,944,802 | `667fad0814f4f37fd1a4ecc7b6276370ed3d3bcf7b169df0498dc67865f58ccc` | `cb0176075521b01e81d998b6ac05410f24a0952b64d816118c5ad525a27394a6` |
| Height 6,455,301, range G (stage 3) | 202,740,183 | 15,407,228,563 | `5fde11f23206730ea665463a2035fd59cf55305fca973c8071dc997555869096` | `1cf629daa4fea574a32ebb80b09584df5a91a0a92a6f407a56d0916ef843375a` |

The snapshot at height 145,000 is the file of [range S](#ranges-from-a-snapshot), with the digest of the recorded replay.
So the pass reached the set that the oracle reached from the empty set.
The pass's block at height 6,456,301 is the last block of the recent range of the [released fixtures](../tests/block/mainnet-blocks/README.md).
That range starts after the snapshot of range G.
The pass also reached the recorded digests at heights 100,000 and 101,000, and it requires all three values.

The pass checked the states of the CSV window with `--version-bits`, on the headers of the pass to height 1,709,999:

```bash
python3 -I scripts/core_pass.py --state build/core-pass --version-bits .lake/build/bin/dogelib-oracle build/core-harness-rebased/core-oracle
```

All 52 boundaries from 1,189,439 to 1,703,519 agree with both full walks.
The CSV state is `defined` at 1,189,439, `started` from 1,199,519 to 1,693,439, and `failed` at 1,703,519.
The SegWit state is `defined` up to 1,461,599 and `failed` from 1,471,679, the first boundary after its start time, because its timeout is 0.

### Ranges A to H

`scripts/run_range.py` runs each range from the pass's snapshot at its start, in the oracle and in Core.
A range agrees under section 3.4 of the design record when three things hold.
Both programs report the start digest of the manifest, accept every block with equal block records, and report the pass's digest at the end.
The block records must also equal those of the pass.
Before the range, `block.check` with both flags accepts every block in both programs.
Each range ran on one core at low priority, while the pass ran:

```bash
nice -n 19 taskset -c 10 python3 -I scripts/run_range.py --range <NAME> --pass build/core-pass --fixture build/ranges/<NAME> --output build/range-runs/<NAME> --write-hashes .lake/build/bin/dogelib-oracle build/core-harness-rebased/core-oracle
```

The oracle was built at `e927a4d`, whose Lean sources equal those of `main` at `df1b04c`.
The harness `core-oracle` was built from `df1b04c`.
Each fixture holds the blocks from `a + 1` to `b`, which `scripts/fetch_blocks.py --range` fetched from the node.
`--write-hashes` wrote the committed [hash list](../tests/block/mainnet-blocks/README.md#range-hash-lists) of each range from the headers of the pass.

| Range | Heights | Blocks | SHA-256 of `blocks.bin` | Start | End: coins and digest | Spent | Created | Core | Oracle |
| --- | --- | ---: | --- | ---: | --- | ---: | ---: | ---: | ---: |
| A | 145,001 to 155,000 | 10,000 | `c022bf754ddeb09663473add359918132d26b9fc0e742cb379cb50ac6635e82b` | 5,094,671 | 5,379,012, `fe00b205affdd2344d15cdeb073ad18a85ebfb2e8468e66c3ae96494631734c6` | 472,618 | 756,959 | 38 s | 1,426 s |
| B | 370,337 to 372,336 | 2,000 | `83140d38ea1010f69412306b5be617017a1c314a27d18ee9e5fb9aae487f4db1` | 8,576,188 | 8,622,709, `9a2633ff9d56b1de6ef4bc82016d1b22e7c43c3c8f1140a3de782f8b2afca67c` | 90,664 | 137,185 | 23 s | 568 s |
| C | 599,000 to 600,999 | 2,000 | `8594c4f65d706672e36c76db917cc0fb230fecdb7bf7a5d35cc6bd0acbdc08b9` | 15,572,301 | 15,588,181, `77b4529dad926f3bc516ee39d17b80955d4eea7e4234dcdd8b2a27271ae26179` | 173,936 | 189,816 | 67 s | 1,278 s |
| D | 1,033,383 to 1,035,382 | 2,000 | `fe0a039a16f6075981e88f8ac40614f286e58f97e5f5fa245b31b6fa3526e2a1` | 16,869,346 | 16,874,755, `c7e86aed9d7606e98d5385dec25d5176f37b77a8609390b0da70df29582f0d20` | 61,002 | 66,411 | 32 s | 856 s |
| F | 3,463,751 to 3,465,750 | 2,000 | `7b2b4b2fa443dbdbcbf4a9fa6f1188a51d30d3c8977b071a92ed282b2b154905` | 14,485,802 | 14,520,734, `a6b3bb146f7e3c41c97cdf63f699b5d50a47adc51b2e940b35980d37b8fc4849` | 154,273 | 189,205 | 36 s | 1,224 s |
| H | 5,049,001 to 5,050,000 | 1,000 | `6e2d5d9e79a327d4e0855a989ee83d4503ac9e8fb8764fbc79d20c01c53c86a9` | 87,775,851 | 87,790,115, `e3d9dec9b3a6fdfcc0cd72a3812f0961ae7c06ebe9a475cdb873d1fba7f66cfb` | 224,569 | 238,833 | 220 s | 4,466 s |

Every range agrees.
The start of each range has the coins and the digest of its snapshot in the table above.
The oracle's time includes its two reads of the snapshot.
`block.check` took the oracle 63, 14, 42, 10, 18 and 37 seconds on the six ranges.
On range H, the largest resident set of the run was 3,518,408 KiB, about 3.6 GB, which `/usr/bin/time -v` measured.
The other runs were not measured.

Each result is one run.
It holds under the hypothesis of section 3.4: the snapshot at the start is Core's coin set at its height.

Range A starts from the snapshot at 145,000, which has the digest that the oracle reached from the empty set.
So range A chains to the genesis block with no assumed start state.
The other ranges assume their start states.
The oracle did not check the blocks between the ranges.
[SOUNDNESS.md](../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries) states the hypothesis for each range.

### The CSV window ranges E1 and E2

E1 and E2 are the two ranges of design record 0011, stage 4.
The first Core pass recorded Core's version-bits state at each period boundary.
CSV is `STARTED` from the block after the boundary 1,199,519, and `FAILED` from the block after the boundary 1,703,519.
So the rule changes at 1,199,520 and 1,703,520, and each range runs from `h - 1,000` to `h + 999`, the rule of section 4.

**The second pass.**
The first pass kept no snapshot at the two range starts.
`scripts/core_pass.py --seed` ran a second pass from the kept snapshot of range D at 1,033,382, which the first pass wrote in its replay from the genesis block:

```bash
nice -n 19 taskset -c 28 python3 -I scripts/core_pass.py --state build/core-pass-csv --seed build/core-pass --seed-height 1033382 --last 1704519 build/core-harness/core-oracle-trap
```

It ran on 2026-11-21 from 16:45 to 17:39 UTC, with the trap build of the harness at `e70318f`, and read the blocks above 1,033,382 from the node.
It accepted every block to 1,704,519 and wrote the snapshots at 1,198,519 and 1,702,519.
Its state names the heights that it checked against the first pass.
At 1,035,382 and at the seven segment ends of the first pass from 1,099,999 to 1,699,999, the digest, the number of coins and the total value equal the first pass's.
At the 67 boundaries in its heights, its version-bits states equal the first pass's.
Its 1,704,520 headers equal those of the first pass byte for byte.
`python3 -I scripts/core_pass.py --state build/core-pass-csv --version-bits .lake/build/bin/dogelib-oracle build/core-harness/core-oracle` then compared its 52 boundaries of the CSV window with both full walks, and each agreed.

| Snapshot | Coins | Digest | Total value | Bytes |
| ---: | ---: | --- | ---: | ---: |
| 1,198,519 | 16,774,101 | `c425e4c6d026e6019de51921dba183cf090da2f0f134650e2494a874c5154578` | 10,415,769,565,167,663,246 | 1,278,149,154 |
| 1,702,519 | 11,591,197 | `34d3337fd66c3e7f29a8419d816d28faa23434d3fd5a49ca112f10d81d2dec8a` | 10,919,769,565,167,663,246 | 883,951,730 |

The committed manifests are [`coins-1198519.json`](../tests/block/mainnet-blocks/snapshots/coins-1198519.json) and [`coins-1702519.json`](../tests/block/mainnet-blocks/snapshots/coins-1702519.json).

**The ranges.**
`scripts/run_range.py` ran each range from the second pass's snapshot at its start, as for the ranges A to H.
The chain of each request holds the version of each entry, and reaches at least the boundary 1,189,439, the base of the window, and its ten predecessors.
`chain_floor` of `scripts/core_pass.py` also keeps one period and 260 blocks below the range start, as for the other ranges.
So the chain of E1 reaches down to 1,188,179, with 10,341 entries, and the chain of E2 down to 1,189,428, with 513,092 entries.
Each request has `version_bits_heights` at the range start and at the boundary inside the range:

```bash
nice -n 19 taskset -c <core> python3 -I scripts/run_range.py --range <NAME> --pass build/core-pass-csv --fixture build/ranges/<NAME> --output build/range-runs/<NAME> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The oracle was built from `main` at `cc8bd97`, and the harness `core-oracle` from `e70318f`, whose harness sources equal those of `cc8bd97`.
The two ranges ran at once on 2026-11-21, on one core each.
`--write-hashes` wrote the committed [hash lists](../tests/block/mainnet-blocks/README.md#range-hash-lists): in an earlier run of E1, and in the recorded run of E2.

| Range | Heights | SHA-256 of `blocks.bin` | Start | End: coins and digest | Spent | Created | CSV states | Core | Oracle |
| --- | --- | --- | ---: | --- | ---: | ---: | --- | ---: | ---: |
| E1 | 1,198,520 to 1,200,519 | `f0647f8e1fdb6109e6297c498f8df154b24829295032824662bd34eba6a584a7` | 16,774,101 | 16,809,066, `5fa47879680925ec78db0c2ba6025722390edbe6d0bd60b01f5ea285f47d2ebe` | 57,055 | 92,020 | `DEFINED` at 1,198,519, `STARTED` at 1,199,519 | 75 s | 825 s |
| E2 | 1,702,520 to 1,704,519 | `95e0f69d1565f412da666ec68b6b4669d9a280849e12225c1964c8e4f9177225` | 11,591,197 | 11,581,142, `99dfcecda777971dff54621b7eb9b177781abe34d9194aa78a242679cc4070f0` | 68,452 | 58,397 | `STARTED` at 1,702,519, `FAILED` at 1,703,519 | 82 s | 1,100 s |

Both ranges agree under section 3.4.
Both programs report the start of the manifest, accept every block with equal block records, and report the second pass's digest at the end.
The block records also equal those of the second pass.
Both programs report the CSV states of the table, and each state at a boundary equals the one that both passes recorded.
`block.check` took the oracle 10 and 17 seconds before the ranges, and accepted every block in both programs.
An earlier run of E1, on a build of the oracle before the fix of an active CSV state, gave the same result.

Each result is one run.
It holds under the hypothesis of section 3.4: the snapshot at the start is Core's coin set at its height.
Both snapshots come from Core's replay from the genesis block: the first pass to 1,033,382, and the second pass from there.
The oracle did not check the blocks between the ranges.
On mainnet the CSV state is never active, so the walk changes no verdict of the ranges ([docs/soundness/blocks.md](soundness/blocks.md#version-bits)).
The ranges compare the states that the walk reports, in the oracle and in Core.

### The conformance corpus

The conformance corpus is stage 5 of design record 0011.
[docs/conformance.md](conformance.md) defines its formats and the steps of a run.
Each range of the corpus has a range request with restricted coins. They are the coins of the snapshot at its start whose transaction ID the blocks name.
`validateBlock_restrict` states why these coins give each block the verdict of the whole set ([coverage](coverage/blocks.md#block-validation-on-the-coins-that-a-block-names)).

**The run.**
For each range, `scripts/conformance.py request` wrote the range request from the snapshot of the Core pass and the source request of `scripts/impact_run.py request`.
Then `scripts/conformance.py compare` ran both programs on it, on one core at low priority:

```bash
nice -n 19 taskset -c 12 python3 -I scripts/conformance.py compare --range <NAME> --dir build/conformance-work/<NAME> --recorded <range-oracle-response.json> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The oracle and the harness `core-oracle` were built from `main` at `7444635`, the harness without `--trap-overflow`.
The runs were on 2026-11-24, one range at a time.
[`tests/generators.toml`](../tests/generators.toml) records the command, the SHA-256 of each input and output, and the times of each range.

| Range | Heights | Blocks | Start coins | End: coins and digest | Spent | Created | Core | Oracle |
| --- | --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| short | 9,001 to 10,000 | 1,000 | 35,224 | 64,545, `df2822c32b94e18245581f49a345faabe590f648c320112d64f92ebbe798f30d` | 47,185 | 76,506 | 2 s | 89 s |
| A | 145,001 to 155,000 | 10,000 | 1,126,994 | 1,411,335, `18e2c2cf047b8ebd86bd81c8352bd156dd4bb58552e24d06155a966aefab4daa` | 472,618 | 756,959 | 41 s | 1,274 s |
| B | 370,337 to 372,336 | 2,000 | 594,617 | 641,138, `19fa027a5cf528937013668a62cd88d907889c34d299e674cfa6da3a4014c1ba` | 90,664 | 137,185 | 10 s | 227 s |
| C | 599,000 to 600,999 | 2,000 | 580,188 | 596,068, `9a9b2dfeaf468affdb624d5e40f87bf83471d8a451fdce7bd74b940e15ec3319` | 173,936 | 189,816 | 14 s | 483 s |
| D | 1,033,383 to 1,035,382 | 2,000 | 493,817 | 499,226, `7b31b0be6e08ce6511db42f925596fee4d1a1b4aa1bc7ae16142aa9790b1dc1d` | 61,002 | 66,411 | 7 s | 173 s |
| E1 | 1,198,520 to 1,200,519 | 2,000 | 282,022 | 316,987, `232e024d1738c360ce0cd02aad91e9ef4f5970b04ff640a6fe80b48858af00d7` | 57,055 | 92,020 | 6 s | 159 s |
| E2 | 1,702,520 to 1,704,519 | 2,000 | 785,232 | 775,177, `ff9a583be94733c0b803bbaa7a2f448d86b29dcb94b4eea838abe7a16ed6fa89` | 68,452 | 58,397 | 12 s | 215 s |
| F | 3,463,751 to 3,465,750 | 2,000 | 467,821 | 502,753, `41fdcd7e7085f8e915241f79f970b555141b6ba3fb540ceda985805d8125446e` | 154,273 | 189,205 | 13 s | 389 s |
| H | 5,049,001 to 5,050,000 | 1,000 | 568,840 | 583,104, `6aec16b0c5419b2c27ccba406f2be56521dacc5deaf0531d5909773e6da8249c` | 224,569 | 238,833 | 14 s | 598 s |

In each range, both programs accept every block.
Their two `block.validate` responses agree in every field of the full comparison.
So they agree on every block record, on the start digest and on the end digest of the restricted set.
The checker `scripts/check_range_results.py` passes on the results of the oracle against those of the harness.
The results of the harness are the committed expected results in [`tests/conformance/ranges/`](../tests/conformance).

For A, B, C, D, F and H, `--recorded` named the oracle's response of the recorded run of the range from the whole snapshot ([ranges A to H](#ranges-a-to-h)).
For the short range it named Core's response of its replay from the genesis block to height 10,000, which `scripts/impact_run.py request --harness` wrote.
In each of these seven ranges, the block records of the run from the restricted coins equal the recorded records.
No response of the recorded runs of E1 and E2 was kept, so their records were compared only between the two programs.
For A to H, E1 and E2, the numbers spent and created equal those of the recorded runs in the tables above.

The oracle took 3,607 seconds for the nine ranges, about one hour on one core.
Each result is one run.
It holds under the hypothesis of section 3.4: the snapshot at the start is Core's coin set at its height.

**The assets.**
`scripts/conformance.py pack` wrote the blocks, the block manifest and the range request of each range as release assets, 27 files of 256 MB in all.
They are in the release `conformance-corpus-2026-11-24`, and [`tests/conformance/release.json`](../tests/conformance/release.json) gives the size and the SHA-256 of each.
In CI, the job `core` / `conformance` fetches the short range and range D from the release.
The oracle runs each, and the checker compares its results with the expected results.

**A run from the document alone.**
Exit condition 4 of stage 5 asks for a run of one range by someone who did not write the tools.
An AI agent made that run on 2026-11-25 UTC, not a person.
The agent was a Codex session with no prior access to the repository.
The agent had these files and programs, in a directory outside the repository:

- `docs/conformance.md` and `docs/oracle.md`, equal to the files at `a4e8b0c`.
- `tests/conformance/release.json`, `scripts/check_range_results.py`, and the expected results of the short range and range D, each equal to the committed file at `a4e8b0c`.
- A copy of the source of Dogecoin Core 1.14.9, given to it as the pinned commit `e0a1c157`.
- A build of the Core harness `core-oracle`, with the SHA-256 `2931c88cd772bbe5d977ab127b090e89958ad8b0475b3017bd0fb75535f71871`, as a program that it did not inspect.

Its report states that it read no other file of DogeLib, and that it ran the checker without reading it.
The agent's code is not in the repository.

The agent's sandbox had no network, so the agent could not download the assets.
The maintainer's orchestrating agent downloaded the six compressed assets of the two ranges for it, unchanged.
The agent's own code checked the size and the SHA-256 of each asset and of each decompressed file against `release.json`, and all of them agreed.
So the run does not test the download from the document.

The agent wrote two programs from the documents:

- A driver of the harness, which writes a results file. It sends the range request with `blocks_file`, first with an empty blocks file and then with the blocks. It ran the short range and range D.
- A validator in Python with the standard library alone, which does not call the harness. It decides each verdict, and it computes the coin changes and both digests itself. It ran the short range.

On 2026-11-25 the checker of this repository at `a4e8b0c` passed again on each of the three results files:

```bash
python3 -I scripts/check_range_results.py <results file> tests/conformance/ranges/<range>/expected.jsonl
```

| Program | Range | Blocks | SHA-256 of the results file | Checker |
| --- | --- | ---: | --- | --- |
| Driver of the harness | short | 1,000 | `0224c2f5ac73b884c7bde69a954401447be72a99c5acb9798e47b5188b770765` | `PASS` |
| Driver of the harness | D | 2,000 | `2c07fc053c838bab3834dcd36fc15aad1e0f162896de5134a8ee48cecfca8bc8` | `PASS` |
| Independent validator | short | 1,000 | `0224c2f5ac73b884c7bde69a954401447be72a99c5acb9798e47b5188b770765` | `PASS` |

The two results files of the short range are equal byte for byte.
The first complete run of the validator passed.
It checked 35,548 transactions and the scripts of 47,185 inputs in about 74 seconds.

The validator covers only the blocks of the short range, in the random subsidy era, and only blocks that Core accepts.
It does not check AuxPoW or the rules of later activations, and it is not a program of the `dogelib-oracle/1` protocol.
The corpus has no rejected block, so the run shows no agreement on a reject reason.

The report of the agent lists the points where the document was missing or needed Core's source:

- The document needed `docs/oracle.md` to complete a request and read its response.
- It needed Core's source for the serialization of transactions, the proof of work, the retarget, the median time and finality, and the random subsidy.
- It also needed Core's source for coinbase maturity and BIP30, Script, and the bounds of blocks and transactions.
- It did not say that the results format holds no rejected block before the last height.
- Its commands and links assume a clone of the repository.

From these points, [docs/conformance.md](conformance.md) gives an example of a request and its results, and a table of the Core files of each rule. It also states the scope of the results format and the command of a copied checker.
The report found no ambiguity in the digests or the results format.

## Block subsidy comparison evidence

The harness calls Core's own `GetDogecoinBlockSubsidy` (D104), so the comparison tests Core's code and the Boost release of the harness build.
The comparator requires equal `subsidies`, and it checks the form of `redraws` and `boost_version` without a comparison.
It also requires each subsidy to lie in the range that Core's text allows for the height (D104, lines 138 to 148).
Its report names the Boost release, the number of cases with a redraw and the largest number of redraws.

The 148 requests hold 145,166 cases:

| Set | Requests | Cases | Expected values |
| --- | ---: | ---: | --- |
| Mainnet heights 1 to 145,000 on their real previous hashes ([fixture](../tests/block/mainnet-subsidy-prev-hashes/README.md)) | 145 | 145,000 | None: agreement of the two programs |
| Fixed schedule: 18 heights from 145,000 to 2147483647, each on three hashes | 1 | 54 | Read by hand from D104, lines 142 to 148 |
| Recorded Core values: 35 mainnet heights below 145,000 | 1 | 35 | Captured from Core's function through the harness, and computed again in each run |
| Boundaries: 11 heights from 0 to 600,001, each on seven hashes | 1 | 77 | None: agreement of the two programs |

With Boost 1.70.0 every case agrees.
The oracle reports one redraw for 30 of the 145,000 mainnet heights, and no case has more than one.
`scripts/test_oracle.py` checks the fixed schedule, the recorded Core values and the request errors without Core.

The 144,999 mainnet heights with a random subsidy hold 144,965 distinct seeds of the `2^28`, each at the height of its block.
`scripts/compare_subsidy_seeds.py` covers every seed outside CI.
It sends all `2^28` seeds at height 1, where `maxReward` is 999,999, and at height 100,000, where it is 499,999.
It fails on any disagreement and on any error, so a pass shows that 624 words of fuel suffice for every seed.
The run of 2026-11-13 passed on all 536,870,912 cases, and no seed takes more than 2 redraws.
[COVERAGE.md](../COVERAGE.md#operations) records the run.

## Header-sequence comparison evidence

The harness calls Core's static `AcceptBlockHeader` (D33, lines 3205 to 3267) once for each header of the request, in order.
That function calls Core's `CheckBlockHeader`, `ContextualCheckBlockHeader` and `AddToBlockIndex` (lines 2755 to 2788).
Earlier revisions used a transcription of these passages, H2 of [design record 0008](design/0008-header-sequence-validation.md#82-the-core-side).
The harness no longer contains it.
The harness does not call `ProcessNewBlockHeaders`, so `NotifyHeaderTip` does not run.

Each response field comes from Core's state:

- `valid`, `reject_reason`, `dos` and `reject_code` come from the return value and the `CValidationState` of the first rejected call.
- `added` lists each header whose hash `mapBlockIndex` lacked before its call, with the height and chain work of Core's new entry.
- `marked_failed_child` lists the members of Core's `setDirtyBlockIndex` after the rejected call. A rejected call adds no entry, so the set holds exactly the entries that the marking loop visited (lines 3246 to 3250).

The remaining harness trust is the in-memory index.
The harness creates one `CBlockIndex` for each index entry of the request, in Core's `mapBlockIndex`.
It sets the height, status flags, chain work and predecessor of each entry, and calls Core's `BuildSkip` with predecessors first.
It inserts the failed list into Core's `gFailedBlocks`.
That set orders its members by address, so Core visits the failed list in address order, not in request order.
The comparator already excludes `marked_failed_child` where the order can change it.

The harness sets the adjusted time through Core's mock time and time offset, and calls `UnloadBlockIndex` before and after each request.
It restores mock time 0 and offset 0 on every exit from the request, so no later request sees the adjusted time.
Mock time 0 selects the system clock, so the harness gets adjusted time 0 from mock time 1 and offset -1.

The harness accepts every adjusted time from -2^63 to 2^63 - 7201, as the oracle does.
On this path Core reads the time only through `GetAdjustedTime` and adds 7200 to it, which cannot overflow in that range.
Core also formats a log timestamp from the mock time, and that conversion fails outside the years 1400 to 9999.
The harness turns off Core's log timestamps and its debug log, so Core never makes the conversion.
`scripts/test_core_harness.py` sends sequence requests at -2^63, 0, 10^12 and 2^63 - 7201, alone and in one stream with contextual checks between them.
Each harness response must be the same alone and in the stream, and must agree with the oracle.

The harness has one internal operation, `harness.time_state`, which is not part of `dogelib-oracle/1`.
It returns Core's mock time and time offset.
The oracle has no such operation, and the comparator never sends it.
The same test sends it after a success, a consensus rejection, a request error and a decoding error, at adjusted time 0 and at 10^12.
Both values must be 0 each time.
The test fails when either reset is removed.

A request names no ancestor below an anchor.
Core's `GetAncestor` asserts a predecessor at every step, and `AddToBlockIndex` reaches it through `BuildSkip`.
So each anchor above height 0 gets one placeholder entry as its predecessor.
The placeholder is its own predecessor and its own skip entry, and it is outside `mapBlockIndex`.

`GetAncestor` returns it for every height below the anchor, and it is equal to no entry of the request.
Core follows a skip pointer only when its skip height is at least the target.
So a walk to a height at or above the anchor never passes through the placeholder.

Before each call, a preflight refuses a request with a short median, recovery or retarget history.
It applies only where `AcceptBlockHeader` reads that history.
There the header is not the genesis block, is unknown, has valid work, and has a known predecessor without a failure flag.
So Core never reads the placeholder as history, and `GetNextWorkRequired` cannot call `GetAncestor` below an anchor at `pow.cpp:84`.
The preflight returns no verdict.
`AcceptBlockHeader` does not reach `VersionBitsState`, so the request needs no version-bits history.

For the three fixture adapter errors, the comparator requires the exact Lean `work_view` error and the corresponding Core request-refusal message.
Neither response is a consensus rejection.

`scripts/oracle_header_sequence.py` defines these streams:

| Stream | Requests | Evidence |
| --- | ---: | --- |
| Regtest | 34 | D83's complete requests and hand-derived expected fields |
| Mainnet | 15 | Five full-header ranges, three pure-header initial indices, checkpoint branches, two anchor refusals and three version mutations |
| State boundaries | 8 | Prefix marks, an existing child flag, anchor separation, three failed-list search orders, the candidate height bound and size-before-decode precedence |
| Mutations, seed `20261110` | 200 | Header order, bits, time, predecessor bytes, failure/validity flags and failed-list order |

The mainnet sequences use every full candidate after the first eleven context entries of each non-genesis range.
The genesis sequence starts with an empty index.
Chain acceptance supplies expected verdicts.
Python integer arithmetic independently computes block proofs and wrapped sums from D35, lines 150 to 162.
No expectation comes from DogeLib or the harness.

The comparator prints both source revisions and each selected stream with its seed and count.
These finite comparisons do not prove agreement on all inputs.

The self-test plants disagreements in every response field and each added-entry field.
It checks both failed-list orders, keeps the other fields comparable when marks are excluded, and rejects duplicate-member over-exclusion.
The oracle tests compare fixture expectations, exact adapter errors, malformed requests and resource-limit refusals.

## Core with the CSV state forced to `ACTIVE`: results

See [Core with the CSV state forced to `ACTIVE`](core-harness.md#core-with-the-csv-state-forced-to-active) for the `force_csv_active` harness mechanics, commands and unsupported-read scan.

| Part | Requests | Contents |
| --- | ---: | --- |
| Refusals | 5 | Each program refuses the argument that it does not have, and the harness refuses a value that is not a Boolean |
| Made blocks | 37 | A lock time on each side of the median cutoff and of the block time. Final and other sequences, a height lock time and a locked coinbase. Unsorted times, and heights 1, 2, 3, 11 and 12. A period boundary before the CSV start and after the CSV timeout. Three blocks that are not applicable. Each verdict is derived by hand from `IsFinalTx` and from lines 3127 to 3140 |
| Harness state | 74 | After each made block with the argument, the same request without it and with the value false. Each gets the hand-derived baseline verdict |
| Mainnet blocks | 11,018 | Heights 0 to 10,000, heights 6,455,302 to 6,456,301 and the 17 rule-change blocks, each with the argument |
| Self-test | 32 | For 16 made blocks with two verdicts, the comparison fails with the revision inactive, and fails against a harness run without the seed |
| `block.validate` refusals | 4 | Each program refuses the argument that it does not have, and the harness refuses a value that is not a Boolean |
| `block.validate` made blocks | 36 | 18 spends of one supplied coin, at heights 1,034,382 and 3,464,751. A height operand met exactly and one short. Versions 1, 2 and -1. A sequence with bit 31, and with bits outside the mask. Time and height types. An operand with bit 31, a negative operand, one of six bytes, and an empty stack. The opcode in a skipped branch, in the `scriptSig` and in a P2SH redeem script. A script with a false result. Each verdict is derived by hand from D3, lines 392 to 427 and 1310 to 1354, and from D101, lines 1488 to 1512 |
| `block.validate` harness state | 72 | After each made block with the argument, the same request without it and with the value false. The response with the argument, without its objects `forced`, equals the response without the argument |
| `block.validate` self-test | 40 | For 20 made blocks with two verdicts, the comparison fails with the revision inactive. It also fails when the harness record without the seed stands in the place of `forced`. Each failure is a difference of verdicts |
| Sequence locks, made blocks | 61 | Each with the argument and then without it. 23 blocks at each of the heights 1,034,382 and 3,464,751: a height lock met exactly, and one block short. Versions 1, 2 and -1. Bit 31, and bits outside the mask. A coin that the block itself creates, with a height lock and a time lock of 0 and of 1. The largest time lock that is met on a coin 20 blocks below, and one unit more. A height lock on a coin above the block. Five blocks at each height are outside the model, for the three reasons. 14 blocks at height 40 on a made chain from height 0, whose entry at height `k` has the time 1,400,000,000 + 512 * `k`: time locks that are met exactly and one unit more on coins at heights 0, 1, 2 and 21, a time lock that is one second short, and height locks on the coins at heights 0 and 1. One block that Core rejects through BIP30, for the scan of the harness. Each result is derived by hand from D114, lines 309 to 384, and from BIP 68. The script computes the median times past from the times of the request |
| Sequence locks, self-test | 75 | For the 33 made blocks with two results, the comparison fails with the revision inactive. It also fails when the harness record without the seed stands in the place of `forced`. Nine malformed results of the two programs are not taken for results: an acceptance without a digest of its changes, a digest of another length, the number 1 as a verdict, a reason with a verdict, and a result outside the model with a digest, a reject field or an unknown reason |
| Scan of the harness | 1 | A block above the BIP34 height, where Core does not enforce BIP30. One transaction overwrites an unspent entry of its own ID, and the next has a time lock on a coin two blocks above the block. The harness must name `coinAboveBlock`. This check reads the harness alone |
| `block.validate` on mainnet | 1 | Heights 0 to 10,000 in one request from the empty coin set, with the argument. The harness runs each block with the seed and without it, and the run without the seed carries the state |

Every forced result agrees with its `revised` object.
The made blocks reach `bad-txns-nonfinal` from the cutoff 20 times.
One made block has a time below the median, which `ContextualCheckBlockHeader` rejects. This operation runs no header check, and both programs then accept a lock time that the baseline rejects.

The forced run accepts each of the 11,018 mainnet blocks, so no block is changed.
That count equals the committed candidate list, [`tests/proposals/relative-lock-time/cutoff-candidates.json`](../tests/proposals/relative-lock-time/README.md), which has no candidate block.
In `block.validate`, the forced run also accepts each block of heights 0 to 10,000, with the changes of the run without the seed, and the proposal executable gives the same result for each. No block of that range is changed or outside the model.
One recorded run of the whole script on a development machine takes about 16 minutes, most of it for that replay, and the proposal executable uses about 1.8 GB of memory.

The 36 made blocks reach `non-mandatory-script-verify-flag` through the opcode 20 times, and `mandatory-script-verify-flag-failed` twice, for a script that also fails without the flag.
The 61 made blocks of the sequence locks reach `bad-txns-nonfinal` of `ConnectBlock` 23 times, with the score 100.

Agreement shows that the Lean rule equals Core's dormant code on these requests.
It does not show that the rule is right for Dogecoin, and a count says nothing about other heights or about unconfirmed transactions.
The comparison covers the rule of BIP 113 through `ContextualCheckBlock`, and the rules of BIP 112 and BIP 68 through `block.validate`, on made blocks and on mainnet heights 0 to 10,000.
No forced run of `block.validate` covers a mainnet block above height 10,000.
The time lock that is one second short, and the coins at heights 0 and 1, are on the made chain alone: the made blocks on real headers have the times of their headers.
This state does not occur on mainnet (`csv_never_lockedIn`).

## Historical impact runs

See [historical impact tooling](core-harness.md#historical-impact-tooling) for `scripts/impact_run.py`, `scripts/impact_candidates.py` and `scripts/test_impact.py`.

The recorded runs used `dogelib-proposal-oracle` and `dogelib-oracle` as built at `6ef0e12`, a commit of pull request #195.
Their SHA-256 values are `220a29cdff67c47bb80541fb7cbf75098b9965f68837b56155216b47c24d4548` and `32b9fc94235fe8408d0bd06d3bc90945d0314057e037d68fb8db50647cf1a025`.
That build of the proposal executable also named the two examples, which only `proposal-test-oracle` names since pull request #200.
The code of `RelativeLockTime` and of the block level of the framework has no difference between `6ef0e12` and `33f5c82`.
On the short range, `dogelib-proposal-oracle` built at `33f5c82` writes the same bytes for `RelativeLockTime` from height 1.
Each run had one core at low priority, and each candidate list has the SHA-256 of its file on `main`.

| Range | Heights | Blocks | Transactions | Inputs | Seconds, `RelativeLockTime` | Memory |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `genesis-145000` | 0 to 145,000 | 145,001 | 8,629,425 | 15,048,625 | 148,352 | 7.5 GiB |
| `short` | 9,001 to 10,000 | 1,000 | 35,548 | 47,185 | 181 | 0.1 GiB |
| `S` | 100,001 to 101,000 | 1,000 | 67,318 | 121,665 | 771 | 0.4 GiB |
| `A` | 145,001 to 155,000 | 10,000 | 149,903 | 472,618 | 2,702 | 1.1 GiB |
| `B` | 370,337 to 372,336 | 2,000 | 37,646 | 90,664 | 750 | 0.5 GiB |
| `C` | 599,000 to 600,999 | 2,000 | 72,751 | 173,936 | 1,456 | 0.5 GiB |
| `D` | 1,033,383 to 1,035,382 | 2,000 | 21,630 | 61,002 | 1,263 | 0.4 GiB |
| `E1` | 1,198,520 to 1,200,519 | 2,000 | 21,465 | 57,055 | 995 | 0.3 GiB |
| `E2` | 1,702,520 to 1,704,519 | 2,000 | 21,558 | 68,452 | 871 | 0.9 GiB |
| `F` | 3,463,751 to 3,465,750 | 2,000 | 57,886 | 154,273 | 1,287 | 0.5 GiB |
| `H` | 5,049,001 to 5,050,000 | 1,000 | 102,617 | 224,569 | 5,054 | 0.6 GiB |

Every candidate list has 0 candidate blocks, so case 2 expects no changed block.
`RelativeLockTime` from height 1 changed no block, and gave no unsupported result, on each range.
So each count of design record 0012, section 10.3, is 0 on these ranges.
The counts are the cutoff transactions, the sequence candidates and failures, the opcode spends and outputs, and the unsupported blocks.

On each range but `genesis-145000`, the response without the `revised` objects equals a response of `dogelib-oracle`.
It is the recorded response of `scripts/run_range.py`, or for `short`, `S`, `E1` and `E2`, a response of the build above.
The run of heights 0 to 145,000 ends with the digest `b28411dc…` of 5,094,671 coins, the digest of the [recorded replay](#replay-of-mainnet-to-height-145000).
It took 41 hours and 13 minutes on one core.
A power loss stopped its first start at about height 46,000, and it ran again from the empty set with the same command and build.

Before pull request #200, both examples ran on every range of the table except `genesis-145000`, with no activation height and from height 0.
Every `revised` object without an activation height equalled its block record, and no block changed from height 0.
After all runs, `impact_run.py check` as merged in pull request #195 passed on each of the 51 saved responses.

[`tests/proposals/impact/runs/`](../tests/proposals/impact/runs/index.json) has one record for each run, which `scripts/impact_records.py write` made from the saved outputs.
A record has the revision, the activation and the SHA-256 of the executable. It also has the SHA-256 of the request, the blocks file, the coins file, the baseline, the response, the report and the summary.
It has the counts, the digest at the end, the time, the memory and the recheck.
The maintainer's machine keeps the requests, responses and logs under `build/impact/`, outside Git and outside any release asset.
`scripts/impact_records.py --check` checks the records against their index and `SHA256SUMS`, and with `--outputs build/impact` against the saved files.

## Measurements for the rejection search

Stage 0 of [design record 0013](design/0013-rejection-paths.md) measures five quantities before any generator exists (section 11).
The stage adds no Lean code and no gate, and it fixes no format.
The measurements were made on 2026-11-27 on a development machine with an AMD Ryzen AI MAX+ 395 (16 cores, 32 threads), at nice level 19.
Other jobs shared the machine, and each program ran on one core that `taskset` selected.

The revision is DogeLib `5c092f5`, with `scripts/rejection_measurements.py`, `scripts/core_coverage.py` and the option `--coverage` of `scripts/build_core_harness.sh` as committed beside this section.
Core is the pin `e0a1c157791544e818c901bd9341896965afbf9d`, built with gcc 16.2.1.
The inputs are the assets of the nine ranges that `python3 -I scripts/conformance.py fetch` wrote to `build/conformance`.
Each `blocks.bin` and each `request.json` has the SHA-256 that [`tests/conformance/release.json`](../tests/conformance/release.json) gives, and that file has the SHA-256 `b51b028b812a41a3525d66600d1930eddd8224fc9c537ec87e64b13d23657a16`.
The executables have these SHA-256 values:

| Executable | SHA-256 |
| --- | --- |
| `.lake/build/bin/dogelib-oracle` | `d142d5c97d19fea93994ba5bb4e108c90c8315fc513c504ae74b690b7209de34` |
| `build/core-harness/core-oracle` | `2a71275c8b5ce1c3389f9e18570258d9bde215272a3d77d91f4497f000aa1132` |
| `build/core-harness/core-oracle-trap` | `18c1b538e24e7b37f14d4ce29dfcd59cfa805fbf37502b4197eb1e7430fcfc6a` |
| `build/core-harness/core-oracle-coverage` | `8a3bcaf8df838e1044f72b6f6b44e8554b158ddca0b4a64899f59a20349ba4fd` |

### The seeds

The count follows the definition of `Block.payloadNoWitness`.

| Range | Blocks | Blocks that pass |
| --- | ---: | ---: |
| `short` | 1,000 | 1,000 |
| `A` | 10,000 | 10,000 |
| `B` | 2,000 | 2,000 |
| `C` | 2,000 | 2,000 |
| `D` | 2,000 | 2,000 |
| `E1` | 2,000 | 2,000 |
| `E2` | 2,000 | 2,000 |
| `F` | 2,000 | 2,000 |
| `H` | 1,000 | 1,000 |
| All | 24,000 | 24,000 |

So every block of the nine ranges can be a seed.

### The size of a group file

`python3 -I scripts/rejection_measurements.py groups --output build/stage0/groups` writes a group file in the proposed format `dogelib-block-cases/1` for two seeds of each range.
The seeds are the first block and the largest block of the range.
Each group has the accepted control and 40 cases, and each case holds a changed copy of the seed block and then the seed block.
So the cases are as large as a case on a real block can be, and they aim at no reject site.
The compression is xz at the preset of the corpus assets, 9 with the extreme flag.

`python3 -I scripts/rejection_measurements.py controls --groups build/stage0/groups .lake/build/bin/dogelib-oracle build/core-harness/core-oracle-trap` checks the state of each group.
Both programs accept each seed block on the group's request, with the same digests.
The digest of the coin changes equals the value of the committed expected results of the range.
So the chain and the coins of each group are a correct derived state.
That result also holds where the script computed the chain and the coins from the earlier blocks of the range.

| Group | Block bytes | Chain entries | Coin entries | Request bytes | File bytes | File bytes, xz |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `short`, 9,001 | 10,752 | 9,001 | 39 | 470,182 | 2,215,595 | 32,248 |
| `short`, 9,633 | 62,268 | 9,633 | 180 | 547,282 | 10,638,289 | 86,684 |
| `A`, 145,001 | 18,184 | 10,341 | 106 | 1,738,363 | 4,687,756 | 192,956 |
| `A`, 152,911 | 352,787 | 18,251 | 2,292 | 3,273,395 | 60,428,476 | 737,428 |
| `B`, 370,337 | 1,301 | 10,341 | 5 | 549,633 | 763,980 | 64,904 |
| `B`, 371,224 | 338,636 | 11,228 | 1,710 | 3,268,126 | 58,130,745 | 539,572 |
| `C`, 599,000 | 12,734 | 10,341 | 54 | 775,495 | 2,841,988 | 112,320 |
| `C`, 600,084 | 451,367 | 11,425 | 1,159 | 2,871,428 | 75,996,469 | 741,236 |
| `D`, 1,033,383 | 3,016 | 10,341 | 10 | 561,397 | 1,053,576 | 57,848 |
| `D`, 1,034,671 | 331,274 | 11,629 | 1,276 | 1,046,375 | 54,716,352 | 339,476 |
| `E1`, 1,198,520 | 22,607 | 10,341 | 56 | 936,201 | 4,602,124 | 116,928 |
| `E1`, 1,198,761 | 237,544 | 10,582 | 106 | 3,229,450 | 41,715,169 | 588,800 |
| `E2`, 1,702,520 | 965 | 513,092 | 1 | 36,943,169 | 37,103,088 | 2,291,492 |
| `E2`, 1,704,268 | 97,101 | 514,840 | 612 | 37,801,856 | 53,535,809 | 2,594,404 |
| `F`, 3,463,751 | 4,801 | 10,341 | 21 | 569,751 | 1,351,100 | 61,564 |
| `F`, 3,464,390 | 405,407 | 10,980 | 1,571 | 1,230,573 | 66,910,096 | 430,564 |
| `H`, 5,049,001 | 74,772 | 10,341 | 416 | 686,633 | 12,803,284 | 117,512 |
| `H`, 5,049,750 | 998,731 | 11,090 | 601 | 789,229 | 162,587,240 | 910,316 |

The budget of section 8.5 allows 2 MB for each group asset after xz, and no group on a seed of E1 or E2.
Every group of the seven other ranges has at most 910,316 bytes after xz, under that limit.
The two groups of E2 are above it, at 2.3 MB and 2.6 MB, because their chain has about 514,000 entries.
The budget already excludes them.

Without compression a group of 40 cases on a large block has up to 163 MB, because each case holds the block twice, in hexadecimal.
The budget sets no limit on that size.
The total of 25 MB and the expected results of 2 MB depend on the number of groups, which stage 5 sets.

### The time of a request

`SEEDS=... python3 -I scripts/rejection_measurements.py time --groups build/stage0/groups --cpu 27 --output build/stage0/time.json <programs>` runs one `block.validate` request in a new process for each program.
`SEEDS` is not set in the recorded run, so the default list of five groups applies.
A request of 100 candidates has 99 rejected candidates and then the seed block:

- In a *shallow* candidate, the lock time of the last transaction changes and the Merkle root does not. Both flags are true, and `CheckBlock` rejects it with `bad-txnmrklroot`.
- In a *deep* candidate, the coinbase claims 1 to 99 koinu more, the Merkle root follows, and `check_pow` is false. Every check runs, and `ConnectBlock` rejects it last, with `bad-cb-amount`.

The baseline is the seed block alone.
Each response gave the expected reasons, and the three programs ended with the same digest of the coins.
The times in seconds include the read of the request:

| Group | Inputs | Chain entries | Request | Oracle | `core-oracle-trap` | `core-oracle` |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| `D`, 1,033,383 | 10 | 10,341 | Baseline | 0.056 | 0.018 | 0.018 |
| | | | 100 shallow | 0.479 | 0.053 | 0.052 |
| | | | 100 deep | 1.821 | 0.028 | 0.029 |
| `D`, 1,034,671 | 1,280 | 11,629 | Baseline | 5.043 | 0.173 | 0.181 |
| | | | 100 shallow | 11.156 | 0.961 | 0.974 |
| | | | 100 deep | 499.539 | 7.286 | 7.994 |
| `H`, 5,049,750 | 1,425 | 11,090 | Baseline | 3.321 | 0.103 | 0.105 |
| | | | 100 shallow | 20.653 | 2.518 | 2.476 |
| | | | 100 deep | 324.944 | 3.782 | 3.811 |
| `E2`, 1,702,520 | 1 | 513,092 | Baseline | 0.610 | 0.647 | 0.640 |
| | | | 100 shallow | 1.457 | 0.670 | 0.657 |
| | | | 100 deep | 1.289 | 0.656 | 0.636 |
| `E2`, 1,704,268 | 623 | 514,840 | Baseline | 2.565 | 0.704 | 0.703 |
| | | | 100 shallow | 9.561 | 0.951 | 0.960 |
| | | | 100 deep | 173.078 | 3.112 | 3.378 |

The cost of the oracle follows the inputs of the candidates.
On the deep request of D at 1,034,671 it takes about 3.9 ms for each input of a candidate.
Design record 0011, section 2, recorded 4.1 ms.

The chain of E2 adds about 0.6 seconds to each request in both programs.
In Core a deep candidate takes less time than the seed block alone.
The reason is Core's signature cache, which keeps the signatures of the seed block after the first candidate (`fCacheResults` is `fJustCheck`, `validation.cpp`, line 1977).
A candidate on the same real transactions has the same signatures, so the cache also applies in the search.

The CI budget of section 9.3 is 10 minutes of the job `compare` on a GitHub runner.
One deep request of 100 candidates on a block of about 1,300 inputs takes 5 to 8 minutes of the oracle on this machine.
So the CI run of stage 1 can hold only a few such requests.
Its deep cases need seeds with few inputs, or made blocks.
The deep request of D at 1,033,383, with 10 inputs, takes 1.8 seconds.

A run with a fresh seed has 8 hours on 8 cores, which hold about 460 deep requests of the largest kind.
Seeds with fewer inputs give many more.
This machine is not a GitHub runner, so stage 1 records the time of its run in CI.

### The cost of a mined block

`python3 -I scripts/rejection_measurements.py mine --samples N --workers W --output FILE --check .lake/build/bin/dogelib-oracle build/core-harness/core-oracle` mines made blocks at height 1 of mainnet.
Their `nBits` is `0x1e0ffff0`, the value of the genesis block.
That target accepts a scrypt digest with the probability 1 in 1,048,592, so a block needs 1,048,592 attempts on average.
The miner uses Python's `hashlib.scrypt`, as `scripts/generate_header_sequences.py` does.
Both programs accept each mined header with `block.check_pow`, and reject it with the nonce below.

| Workers | Samples | Hashes per second | Nonces of the samples | Seconds of the samples | Mean time of a block |
| ---: | ---: | ---: | --- | --- | ---: |
| 1 | 3 | 5,843 to 5,924 | 34,682, 457,516, 1,275,685 | 5.9, 77.8, 215.4 | about 178 s |
| 3 | 5 | 17,162 to 17,528 | 34,682, 457,516, 1,275,685, 613,121, 191,429 | 2.0, 26.1, 72.8, 35.1, 10.9 | about 60 s |

The mean time is 1,048,592 attempts at the measured rate.
The time of one block varies widely, as the samples show, because the number of attempts has a geometric distribution.

Core's generic scrypt, `scrypt_1024_1_1_256` as the harness builds it, computes about 7,790 digests per second on one core of this machine.
With it a block takes about 135 seconds.

### Executed lines of Core

`scripts/build_core_harness.sh --trap-overflow --coverage <dogecoin-git-clone> build/core-harness` builds the [coverage build](core-harness.md#the-coverage-build).
A build without `--coverage` reuses the libraries and gives a `core-oracle` with the same SHA-256 as the build with it.
`python3 -I scripts/core_coverage.py --output build/core-coverage/validate .lake/build/bin/dogelib-oracle build/core-harness` runs the 42 `block.validate` requests of the full comparison.
`core-oracle` and `core-oracle-coverage` gave equal responses, and both agreed with the oracle.
gcov gave these counts for the functions of section 3.2:

| Function | Lines | Lines executed | Branches | Branches taken |
| --- | ---: | ---: | ---: | ---: |
| `CheckTransaction` (lines 527 to 574) | 29 | 21 | 82 | 31 |
| `CheckBlockHeader` (lines 2927 to 2937) | 4 | 3 | 12 | 4 |
| `CheckBlock` (lines 2939 to 3000) | 30 | 24 | 92 | 39 |
| `ContextualCheckBlockHeader` (lines 3066 to 3119) | 28 | 16 | 96 | 30 |
| `ContextualCheckBlock` (lines 3121 to 3203) | 38 | 24 | 106 | 32 |
| `ConnectBlock` (lines 1783 to 2050) | 132 | 91 | 368 | 128 |
| `Consensus::CheckTxInputs` (lines 1415 to 1459) | 28 | 25 | 68 | 33 |
| `CheckInputs` (lines 1462 to 1519) | 25 | 22 | 52 | 30 |
| `AcceptBlockHeader` (lines 3205 to 3267) | 42 | 0 | 106 | 0 |

The requests executed 13 of the 40 reject sites of section 3.2.
They are all 9 sites of `ConnectBlock`, `CheckTxInputs` and `CheckInputs`, and `bad-txns-inputs-duplicate`, `bad-txnmrklroot`, `bad-diffbits` and `bad-txns-nonfinal` of `ContextualCheckBlock`.
They executed no site of section 3.3.
`block.validate` does not call `AcceptBlockHeader`, which has 4 of the other sites.

The other 23 sites are the targets of other operations of the full comparison or of the search.
`report.md` lists each line that no request executed.
The recorded `report.json` has the SHA-256 `fc796c2e09c19bbd846069de2c7e5b314d136dad51902db2e3849c59e9c521bb`.
Section 9.2 sets the coverage target of a run of the search, which stage 6 measures.
