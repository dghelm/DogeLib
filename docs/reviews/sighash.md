# Model read: Transactions, serialization and legacy signature hashing

- Reader: Codex, based on GPT-6 (exact model version unavailable), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Transaction/{Types,Serialization,Witness,Txid,LegacySighash,LegacySighashReference}.lean`, against the Core transaction, serialization and signature-hash code that the [brief](briefs/sighash.md) names. Both working trees matched the requested revisions and were clean.

## Result

One domain boundary of an operation needs documentation.
Core's default transaction has a cached zero hash, which Lean's computation from the fields does not reproduce.
The read found no consensus-divergent discrepancy in the documented domains of serialization and the legacy signature hash.
Confidence is high from source inspection, without an executable comparison of Lean and Core.

## Findings

1. **The cached hash of the default transaction differs from its computed transaction ID.**

   **Lean:** `DogeLib/Transaction/Txid.lean:36–37`, `DogeLib/Transaction/Witness.lean:206–208`.
   **Core:** `src/primitives/transaction.cpp:78–81`, `src/primitives/transaction.h:329–331`, `src/primitives/transaction.cpp:70–75`.

   Core's `CTransaction()` initializes its cached hash to zero.
   Consequently, both `GetHash()` and `GetWitnessHash()` return zero for that object.
   Lean always computes the digest from the fields.

   Concrete case: version 1, empty inputs and outputs, lock time 0.
   The base bytes are `01000000000000000000`.
   Their double SHA-256 is `43ec7a579f5561a42a7e9637ad4156672735a658be2752181801f723ba3316d2` in wire order, not zero.

   Lean correctly models `ComputeHash`.
   The missing boundary concerns equivalence with the cached `GetHash` and `GetWitnessHash`.
   Deserialization and conversion from `CMutableTransaction` compute the cache, so they avoid this exception.

   **Severity:** domain-boundary. **Confidence:** high.
   Python `hashlib` independently confirmed the digest.
   The reader did not execute Core's constructor.
   A test at the level of the constructor is necessary, because wire deserialization computes the cache.

## Checked and agreeing

Core paths below are relative to its `src/` directory.
Lean paths are relative to `DogeLib/Transaction/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `transaction.h:26–40` | `Types.lean:51`, `Types.lean:59` | Outpoint fields and null value. |
| `transaction.h:69–72,113–115` | `Types.lean:71`, `Serialization.lean:71` | Input field order. Witness excluded from standalone input serialization. |
| `transaction.h:139–160` | `Types.lean:81`, `LegacySighash.lean:246` | Signed amount bits and null output. |
| `transaction.h:296–299` | `Types.lean:92` | Version and locktime widths. Signed version preserves bits. |
| `serialize.h:66–107,175–190` | `Serialization.lean:95–116` | Fixed widths, little-endian integers, unchanged hash bytes. |
| `serialize.h:220–274` | `Serialization.lean:143–172` | CompactSize canonicality, inclusive `MAX_SIZE`, truncation before canonicality before size rejection. |
| `serialize.h:570–697` | `Serialization.lean:147–197` | Counts, elements and first field error. List and slice readers compared. |
| `transaction.h:211–242` | `Serialization.lean:168` | Base mode reads no optional-data flag, including empty `vin`. |
| `transaction.h:219–230` | `Witness.lean:111` | Empty initial inputs, zero flags, replacement inputs and outputs. |
| `transaction.h:231–242` | `Witness.lean:133`, `Witness.lean:152` | Stack reads precede unknown-flag rejection, which precedes locktime. |
| `script/script.h:647–660`, `transaction.h:371–379` | `Witness.lean:58`, `Witness.lean:93` | Empty stack differs from a stack containing an empty item. |
| `transaction.h:246–272` | `Witness.lean:196` | Extended encoding only for nonempty witness stacks. Empty sections normalize to base encoding. |
| `transaction.cpp:60–75`, `hash.h:21–30,149–169` | `Txid.lean:36`, `Witness.lean:206` | Base txid and witness hash construction, subject to finding 1. |
| `script/interpreter.cpp:1064–1068` | `LegacySighash.lean:88–94` | ANYONECANPAY and low-five-bit mode selection. |
| `script/script.h:502–552` | `LegacySighash.lean:109–137` | Direct pushes, PUSHDATA lengths and failed-read cursor positions. |
| `script/interpreter.cpp:1072–1090` | `LegacySighash.lean:222–238` | Separator removal respects push boundaries. Malformed `4c05aa` serializes as `034c05`. |
| `script/interpreter.cpp:1095–1112` | `LegacySighash.lean:253–274` | Selected script, other scripts blank, conditional sequence zeroing, ANYONECANPAY. |
| `script/interpreter.cpp:1117–1141` | `LegacySighash.lean:283–309` | NONE, SINGLE null outputs, count truncation and `nIn + 1` wrapping. |
| `script/interpreter.cpp:1225–1245` | `LegacySighash.lean:317–341` | Input-bound check first, SINGLE bug value, full 32-bit hash-type suffix, double SHA-256. |
| `script/script.h:570–596` | `LegacySighashReference.lean:54–127` | Boundary-only pattern deletion, repeated matches, malformed suffix retention. |
| `test/sighash_tests.cpp:28–87` | `LegacySighashReference.lean:147–225` | Transaction transformation within documented size bounds. Malformed-script differences from production are documented. |

## Not checked

- No build ran. All automated repository gates, differential comparisons and executable tests of Lean against Core remain **not run**.
- The read did not audit SHA-256 internals or proof bodies. It checked the composition of the double hash and the byte order of the digest.
- Witness signature hashing, the interpreter's preparation of script code, contextual transaction validity and unrelated class methods were outside the declared domains.
- The read did not test allocation failures, C++ undefined behaviour or execution on impractically large objects. It did not treat the documented restrictions of the generic decoders and of sizes as findings.

## After the read

A check against Core at the pin, by the model that prepared this record, confirmed the finding from the source.
The doc comments of `Transaction.txid` and `WitnessTransaction.wtxid` state the boundary.
So do [SOUNDNESS.md](../../SOUNDNESS.md#transactions) and the *Transaction ID* and *Witness hash* rows of [COVERAGE.md](../../COVERAGE.md).

The row for `script/script.h:502–552` agrees only for a script of fewer than 2^31 bytes.
The [Script record](script.md#after-the-read) gives the reason.
