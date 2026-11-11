# Model read: Bounded readers and base serialization

- Reader: GPT-6 Codex, an independent model reviewer, not a human. Exact model version unavailable.
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Serialization/{Bytes,Reader,CompactSize,CountedList,Codec,PackedCodec}.lean` and `DogeLib/Base/{Bytes,ByteSlice}.lean`, against the Core code that the [brief](briefs/readers.md) names.

## Result

The read found one domain-boundary discrepancy, which involves the cursor of Core's stream above 4 GiB.
It found no consensus-divergent discrepancy in the compared definitions.
Confidence is high for ordinary serialization and for the behaviour of the bounded readers, from source inspection without execution.

## Findings

### 1. Core's stream cursor can wrap, but Lean preserves the remainder

- **Lean:** `DogeLib/Serialization/Codec.lean:130`, `DogeLib/Serialization/PackedCodec.lean:107`, `DogeLib/Serialization/Reader.lean:41`.
- **Core:** `src/streams.h:151`, `src/streams.h:342–360`, `src/serialize.h:91–95`.
- **Difference:** Core stores the next read position in an `unsigned int`. With a 32-bit `unsigned int`, a read across offset `2^32` can return the correct value but set the cursor to a wrong position. Lean uses list remainders or natural-number slice offsets. The Lean comments claim agreement with the stream without this restriction on the cursor.
- **Concrete reproducer:** Create a Core stream of `2^32 + 1` bytes that ends in `12 34`. Advance to offset `2^32 − 1` with `ignore(2147483647)` twice, then `ignore(1)`. Read a `uint16_t`. Core returns `0x3412`, sets its cursor to `1`, and leaves `2^32` bytes visible. Lean decodes the corresponding remaining bytes `[0x12, 0x34]` as `0x3412` with an empty remainder.
- **Severity:** Domain-boundary. This difference is an artifact of Core's implementation, not evidence of a consensus difference.
- **Confidence:** High from source inspection on a platform with that integer width. The reader did not execute the reproducer.

## Checked and agreeing

Agreement below excludes the cursor boundary above.
Core paths are relative to `src/`, and Lean paths are relative to `DogeLib/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `ser_writedata8/16/32/64`, `serialize.h:66–84` | `Serialization/Codec.lean:125`, `PackedCodec.lean:115` | Low byte first, exact widths, all unsigned bit patterns. |
| `ser_readdata8/16/32/64`, `serialize.h:85–108` | `Serialization/Codec.lean:120`, `Codec.lean:130`, `PackedCodec.lean:107` | Values, consumed widths, suffixes, short inputs. |
| Unsigned integer overloads, `serialize.h:172–190` | `Serialization/Codec.lean:143`, `PackedCodec.lean:126` | Instances for 8, 16, 32 and 64 bits. |
| `WriteCompactSize`, `serialize.h:220–242` | `Serialization/CompactSize.lean:98`, `CompactSize.lean:145` | Boundaries 253, `2^16`, `2^32`, through `2^64 − 1`. |
| `MAX_SIZE`, `serialize.h:26` | `Serialization/CompactSize.lean:178` | Inclusive maximum `0x02000000`. |
| `ReadCompactSize`, `serialize.h:244–274` | `Serialization/CompactSize.lean:200`, `CompactSize.lean:250`, `CompactSize.lean:282` | Truncation before canonicality before size rejection. |
| Canonicality branches, `serialize.h:249–270` | `Serialization/CompactSize.lean:111`, `CompactSize.lean:152` | Generic decoders explicitly omit `MAX_SIZE`. |
| Vector/prevector writers, `serialize.h:569–589,637–657` | `Serialization/CountedList.lean:123`, `CountedList.lean:178`, `CountedList.lean:202` | Count followed by ordered elements, including empty lists. |
| General vector/prevector readers, `serialize.h:608–630,676–698` | `Serialization/CountedList.lean:247`, `CountedList.lean:304`, `CountedList.lean:341` | Bounded count first, then ordered elements and first error. |
| Byte vector/prevector readers, `serialize.h:592–606,660–674` | `Serialization/CountedList.lean:283`, `CountedList.lean:320`, `CountedList.lean:359` | Empty, exact-length and truncated payloads. Chunking preserves declared results. |
| Pair serialization, `serialize.h:705–717` | `Serialization/Codec.lean:83`, `PackedCodec.lean:86`, `Reader.lean:50`, `Reader.lean:75` | First component before second, first failure propagated. |
| `CDataStream::read/write`, `streams.h:342–385` | `Serialization/Bytes.lean:48`, `Bytes.lean:63`, `Bytes.lean:72`, `Reader.lean:41` | Zero-length reads, exact exhaustion, truncation and appended bytes. |
| Raw blob serialization, `uint256.h:97–107` | `Serialization/Bytes.lean:58`, `Bytes.lean:83` | Exactly 32 bytes, unchanged order. |
| Blob construction and zero, `uint256.cpp:13–18`, `uint256.h:25–28,43–46` | `Base/Bytes.lean:45`, `Bytes.lean:65`, `Bytes.lean:68` | Exact-length domain and all-zero value. |
| Hash display order, `uint256.cpp:21–26` | `Base/Bytes.lean:72`, `Bytes.lean:76` | Byte reversal and exact-length inverse. |
| Stream suffix progression, `streams.h:342–360` | `Base/ByteSlice.lean:41–56` | Slice offsets, empty views, clamped take/drop, and single-byte advance. |

## Not checked

- Core's interpretation of signed integers, and `ReadVarInt` and `WriteVarInt`. The scoped Lean definitions have no counterparts.
- Core's allocation failures, partially modified destination objects, and stream reuse after a failure. Lean's declared result contracts do not include them.
- These definitions use no height, activation or network parameter.
- Proofs and exports, which the brief excluded. The `Proofs.lean` umbrella files contain imports, not executable definitions.
- Builds, differential comparisons, fixtures and all other automated gates: **not run**. The reader changed no file.

## After the read

A check against Core at the pin, by the model that prepared this record, confirmed the finding from the source.
In the record's example the stream holds the bytes of the read, so Core's read is defined and only its remainder is wrong.

A second case exists on a stream below 4 GiB.
There the position plus the size of the read can reach 2^32 only when the read asks for more bytes than remain.
Core narrows the next position to `unsigned int` before it tests for the end of the data (`src/streams.h`, lines 347 to 350).
So the wrapped position can pass that test, and the `memcpy` at line 359 then reads outside the buffer.
That read is unsafe in Core, and Lean returns `truncated`.

The doc comments of `readFixed`, `decodeBitVecLE` and `readBitVecLE` state one bound that excludes both cases.
The bound is that the read position plus the size of the read is below 2^32.
So do [SOUNDNESS.md](../../SOUNDNESS.md#codecs) and the *Reader combinators* row of [COVERAGE.md](../../COVERAGE.md).
