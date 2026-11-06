# Dogecoin Core Script corpus

These files prepare known answers for the legacy spend milestone in [design record 0003](../../../docs/design/0003-legacy-spend-validation.md).
They do not execute Script or establish agreement between DogeLib and Core.

## Sources and licence

The reference software revision is Dogecoin Core `v1.14.9`, commit `e0a1c157791544e818c901bd9341896965afbf9d`.
The three JSON files copy `src/test/data/` byte for byte at that revision:

| File | Source | Test records |
| --- | --- | ---: |
| `script_tests.json` | [Core script tests](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/script_tests.json) | 1,193 |
| `tx_valid.json` | [Core accepted transactions](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_valid.json) | 118 |
| `tx_invalid.json` | [Core rejected transactions](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_invalid.json) | 80 |

The files keep Core's MIT licence.
Copyright (c) 2009-2024 The Bitcoin Core developers.
Copyright (c) 2013-2024 The Dogecoin Core developers.
The licence text is in [LICENSES/dogecoin-core-MIT.txt](../../../LICENSES/dogecoin-core-MIT.txt).
The converter adapts the pinned Core assembly and fixture code to Python, with source locations and classifications.
Its module docstring records the source files, adaptation and notice.

The transaction files also occur in `tests/transaction/corpus/` for serialization tests.
This directory preserves them for spend-validation work.
The transaction converter records the runner's requirement that every `tx_valid` input passes Script verification.
It assigns no per-input rejection outcome to `tx_invalid`.
Core's `tx_invalid` runner can reject a transaction before Script execution, or after an earlier input fails.
The pinned [transaction runner](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp) establishes that boundary.

## Normalized records

`script_tests.jsonl` has one record per test, in source order.
The 50 single-string comment entries remain in the upstream JSON file.
Each normalized record has these fields:

| Field | Meaning |
| --- | --- |
| `source_index` | Zero-based index in the upstream array, including comment entries. |
| `source_line` | One-based line of the record's opening bracket in `script_tests.json`. |
| `scriptSig_hex`, `scriptPubKey_hex` | Exact bytes from Core's `ParseScript` assembly syntax. |
| `flags`, `flags_mask` | Sorted original flag set and its numeric mask. `NONE` denotes the empty set. |
| `effective_flags`, `effective_flags_mask` | Flags that Core's `DoTest` supplies, including P2SH and WITNESS whenever CLEANSTACK appears. |
| `expected_error` | Core's expected `ScriptError` name, without `SCRIPT_ERR_`. `OK` means acceptance. |
| `comment` | The test's comment string, or the empty string when absent. |
| `witness` | Witness stack items as hexadecimal strings, in order. A stack containing an empty item is nonempty. |
| `witness_context_present` | Whether the optional witness-and-amount array occurs, even when its stack is empty. |
| `context` | Base transaction bytes, input index zero and the amount in satoshis. |
| `classification` | Milestone eligibility, exclusion reasons, estimated earliest stage and features that defer a case. |

[Core's script runner](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/script_tests.cpp) defines the expected errors and transaction construction.
The converter preserves the fixture's expectation without consulting DogeLib.
The generated transaction bytes describe construction context, not an independent transaction known answer.

The crediting transaction has version 1, locktime zero, one null outpoint, `scriptSig` bytes `0000`, and final sequence.
Its only output has the supplied `scriptPubKey` and fixture amount, which defaults to zero.
The spending transaction also has version 1, locktime zero and final sequence.
Its only input spends output zero of the crediting transaction and uses the supplied `scriptSig` and witness.
Its only output has the same amount and an empty script.

The committed context contains base serialization, so consumers must separately attach the `witness` stack for witness cases.
All pinned amounts are zero or one satoshi and fit the runner's `int` credit argument.
The converter rejects larger amounts outside the portable `int` domain instead of choosing a platform-dependent narrowing result.

[Core's ParseScript](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/core_read.cpp) splits only on spaces, tabs and newlines.
Decimal integers use small-integer opcodes or sign-magnitude pushes.
Raw `0x` tokens insert bytes without a push prefix.
Quoted tokens push their UTF-8 bytes, and cannot contain token separators.
Opcode names follow `GetOpName`, with and without `OP_`, only in the range admitted by `ParseScript`.

For example, `OP_1`, `PUSHDATA1` and `NOP2` are not accepted names.
Numeric overflow follows `strtoll` saturation, but `INT64_MIN` causes undefined negation in Core's push construction.
The converter rejects that value. No pinned record uses it.

The converter preserves malformed instruction bytes from raw tokens.
It never repairs a truncated push or normalizes its encoding.

## Transaction spend records

`tx_spends.jsonl` has one record per serialized input of `tx_valid.json` and `tx_invalid.json`, in file and input order.
It joins inputs to the supplied previous outputs by outpoint, rather than by fixture-array position.
The converter does not execute Script, call DogeLib or obtain expected values from DogeLib.

| Field | Meaning |
| --- | --- |
| `source_file`, `source_index`, `source_line` | Upstream filename, zero-based array index including comments, and one-based opening line. |
| `input_index` | Zero-based input index in the serialized transaction. |
| `tx_hex` | Transaction hex exactly as pinned, including its letter case and any trailing bytes. |
| `prevout_txid`, `prevout_n` | Input outpoint with the txid in display order and the output index as uint32. A source index of -1 becomes 4294967295. |
| `prevout_scriptPubKey_hex` | Previous output script converted with the same `ParseScript` adaptation as `script_tests.jsonl`. |
| `prevout_amount` | Optional signed int64 amount in satoshis, copied from the supplied previous output. The runner uses zero when absent. |
| `scriptSig_hex`, `witness` | Input script bytes and ordered witness stack, including empty items. |
| `flags`, `flags_mask` | Sorted flag names and their mask. `NONE` becomes an empty set and mask zero. |
| `test_expectation` | Transaction-level `valid` or `invalid`, according to the source file. |
| `per_input_expectation` | `accept` for `tx_valid`, and null for `tx_invalid`. |
| `per_input_expectation_source`, `per_input_expectation_reason` | Runner lines and the reason for that expectation or its absence. |
| `comment` | Array of strings in the nearest preceding comment block, or an empty array. Adjacent tests share that block until another occurs. The first test's block includes the file-header comments. |
| `classification` | The same milestone and stage fields as Script records, plus `check_transaction`. |
| `classification.check_transaction` | An `estimated` marker, `rejects_before_script`, the first rejection `reason` or null, and source lines. |

The [transaction runner's flag table and parser](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp#L41-L76) define the accepted names, including `NONE`.
The transaction runner passes the parsed flags unchanged.
It does not add P2SH and WITNESS when CLEANSTACK appears.

The [valid-input loop](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp#L155-L176) requires `CheckTransaction` acceptance and `VerifyScript` acceptance for every input.
The [invalid-input loop](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp#L239-L261) stops after `CheckTransaction` rejects or an input fails.
Thus null means an unknown individual outcome, including for later inputs that the runner never checks.
No record derives an individual Script rejection or error from transaction rejection.

The runner ignores comment entries and prints the transaction test itself in failure messages.
The comment array preserves source context rather than runner output.
The [prevout maps](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp#L120-L142) overwrite scripts for repeated outpoints.
An amount entry changes only when the source supplies an amount for that outpoint.
The converter follows both rules and rejects missing mappings.

The Python prefix reader adapts [Core's witness-allowed reader](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/transaction.h#L210-L243) independently of DogeLib.
It checks canonical, bounded CompactSize values, reads signed output amounts and preserves nonempty witness stacks.
Like the transaction runner, it permits trailing bytes after the transaction prefix.
The converter accepts only exact byte-pair hex and 64-digit previous txids, which all pinned records supply.
It does not implement all the permissive text parsing of Core's `ParseHex` and `uint256S`.

### Estimated rejection before Script

The estimate follows [CheckTransaction](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L527-L574) in source order:

| Check | Pinned source lines |
| --- | --- |
| Empty inputs, then empty outputs | `src/validation.cpp:530–533` |
| Base serialization size above 1,000,000 bytes | `src/validation.cpp:534–536` and `src/consensus/consensus.h:16–17` |
| Negative output, output above MAX_MONEY, then total above MAX_MONEY | `src/validation.cpp:538–548` and `src/amount.h:18,32–33` |
| Duplicate input outpoints | `src/validation.cpp:551–558` |
| Coinbase script length outside 2 through 100 bytes | `src/validation.cpp:561–564` |
| A null prevout in a transaction that is not coinbase | `src/validation.cpp:566–570` |

Dogecoin's `MAX_MONEY` is 10,000,000,000 times 100,000,000 satoshis, which differs from Bitcoin's value.
The `tx_invalid.json` comments name “MAX_MONEY + 1 output” at line 41 and “MAX_MONEY output + 1 output” at line 45.
Both entries have output values and totals below Dogecoin's limit, so the estimate finds no `CheckTransaction` rejection.

The size check uses base bytes directly, without a weight multiplier.
Base size excludes witness data and trailing bytes.
Every estimate has `estimated: true`.
A null reason means the Python checks found no rejection, not that Core ran or that Script passes.

Milestone eligibility depends only on flags and witness, so an eligible input can belong to a transaction estimated to fail before Script.
Stage estimates describe its scripts and do not assign an expectation to such an input.

| Source | Transactions | Input records | Per-input expectation |
| --- | ---: | ---: | --- |
| `tx_valid.json` | 118 | 171 | `accept` |
| `tx_invalid.json` | 80 | 96 | Unknown |
| Total | 198 | 267 | 171 accept, 96 unknown |

The milestone includes 159 input records and excludes 108.
Among included inputs, the estimated earliest stages contain 11 at stage 2, 55 at stage 3 and 93 at stage 4.
The estimate identifies nine invalid transactions that fail before Script and no such valid transaction.
These counts come from Python classification, not a Core comparison.

`tx_spends.summary.json` records source and converter digests, transaction and input counts, exclusions, stage estimates and estimated transaction rejections.
Zero-input transactions would produce no spend records and have a separate count in the summary.
Neither pinned file contains one.
`SHA256SUMS` also pins both transaction spend outputs.

## Classification and conservative estimates

The milestone permits P2SH, STRICTENC, DERSIG, LOW_S, NULLDUMMY, CHECKLOCKTIMEVERIFY and CHECKSEQUENCEVERIFY, including the empty set.
A record is inside the milestone only if its effective flags are a subset and its witness stack is empty.
Every outside record lists all applicable reasons, so reason counts can overlap.
The manifest retains every outside record and its original expectation.

| Classification | Records |
| --- | ---: |
| Inside the milestone | 925 |
| Outside the milestone | 268 |
| Total | 1,193 |

The stage estimates count cumulative candidates among the 925 inside records:

| Stage | Candidates | Additional candidates |
| --- | ---: | ---: |
| 2: ordinary execution, numbers and hashes | 743 | 743 |
| 3: signature operations | 906 | 163 |
| 4: P2SH and timelocks | 925 | 19 |

The estimator scans instruction boundaries in both scripts and stops at a truncated push.
It ignores opcode-like bytes inside pushed data.
Any CHECKSIG or CHECKMULTISIG instruction defers the record to stage 3, including instructions in skipped branches or after an earlier failure.
An exact P2SH output template with the P2SH flag defers the record to stage 4, without analysis of the redeem script.
CLTV or CSV instructions with their respective flags also defer the record to stage 4.
Those instructions without their flags have NOP behavior and do not defer the record.

The estimates assume that the stage implements all its ordinary operations and prerequisites.
The estimated stage can be later than execution requires.
The cumulative counts are lower bounds on the records each completed stage can run.

They do not predict which unsupported operations execution will reach, or count passing comparisons.
Later runners must report actual supported, unsupported and excluded totals separately.

`summary.json` records these counts, overlapping exclusion counts, the source commit and file digest, and the converter's SHA-256 digest.
The converter digest identifies its exact source bytes without a self-referential git commit field.
`SHA256SUMS` pins the three upstream files, normalized records and summary.

## Reproduction

Run these commands from the repository root:

```text
python3 -I scripts/convert_script_tests.py --check
python3 -I scripts/test_convert_script_tests.py
(cd tests/script/corpus && sha256sum -c SHA256SUMS)
```

To regenerate the four derived files, run `python3 -I scripts/convert_script_tests.py`.
Review any change against the pinned source before updating checksums.
The `--check` mode fails on stale or missing output and writes no file.
The converter tests cover hand-derived assembly bytes, push boundaries, source locations, flags, context fields and classification.
Transaction tests also cover input order, outpoint lookup, comments, witness exclusions, rejection estimates and freshness without writes.
CI checks freshness, converter tests and digests.
