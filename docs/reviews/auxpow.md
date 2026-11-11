# Model read: AuxPoW and header proof of work

- Reader: GPT-6 (Codex, exact runtime version unavailable), an independent model reviewer, not a human
- Date: 2026-11-11
- DogeLib: 865754b. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `DogeLib/Block/{AuxPow,AuxPowCheck,Merkle,Header,ProofOfWork,VersionGate}.lean`, `DogeLib/Work/ProofOfWork.lean`, and the Core counterparts that the [brief](briefs/auxpow.md) names.

## Result

One discrepancy concerns Core's default-constructed transaction and its cached hash.
The read found no consensus divergence for decoded inputs within the documented domains.
Confidence is high for the comparison of control flow, subject to the cryptographic dependencies below, which the read did not test.

## Findings

1. **The hash of the default transaction has an unstated boundary.**

   **Lean:** `DogeLib/Block/AuxPowCheck.lean:184`, `DogeLib/Block/Merkle.lean:112`.
   **Core:** `src/auxpow.cpp:100–106`, `src/auxpow.h:50–53,113`, `src/primitives/transaction.cpp:78–81`, `src/consensus/merkle.cpp:163`.

   Core's default `CTransaction()` caches hash zero.
   Lean computes double SHA-256 from its fields.
   Neither scoped operation documents that it excludes this Core object.

   **Concrete input:** a default `CAuxPow`, with both indices zero, both branches empty, parent Merkle root zero, and strict chain-ID checking disabled.
   Core reports "Aux POW coinbase has no inputs".
   Lean reports `merkleRootIncorrect`.
   Both reject.

   A block that contains that default transaction also has different Merkle roots.
   Core returns zero.
   Lean returns the internal-order hash `43ec7a579f5561a42a7e9637ad4156672735a658be2752181801f723ba3316d2`.

   **Severity:** domain-boundary. **Confidence:** high.
   Core's decoding constructor computes the hash again, so this discrepancy requires a test that constructs the object in memory.
   An ordinary comparison on wire input does not preserve the zero cache.
   Python `hashlib` independently confirmed the digest of `01000000000000000000`.
   The reader did not execute the Core reproducer.

## Checked and agreeing

Core paths below are relative to the `src/` directory of the pinned Core clone.
Lean paths are relative to `DogeLib/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `primitives/pureheader.h:29–52` | `Block/Header.lean:31,56` | Six fields, 80 bytes, little-endian integers, raw version bits. |
| `primitives/pureheader.cpp:20–23` | `Block/Header.lean:66` | Double SHA-256 of pure-header serialization. |
| `primitives/pureheader.h:110–113,129–132,150–155` | `Block/AuxPowCheck.lean:47`, `Block/Header.lean:63`, `Block/VersionGate.lean:39` | Chain ID, AuxPoW bit, legacy versions. Arithmetic signed shift documented. |
| `auxpow.h:80–85,155–160` | `Block/AuxPow.lean:146,154,210` | Payload field order, signed index bits, prefix parsing. |
| `primitives/block.h:37–48` | `Block/AuxPow.lean:171,222` | Payload follows flag. Missing-payload writer exclusion documented. |
| `primitives/transaction.h:210–272` | `Block/AuxPow.lean:131,205` | Both transaction modes, empty witness stacks, optional flags, writer selection. |
| `serialize.h:245–273,677–692` | `Block/AuxPow.lean:139` | Canonical counts, inclusive `MAX_SIZE`, sequential hash reads. |
| `auxpow.cpp:84–106` | `Block/AuxPowCheck.lean:177` | Reject order, branch limit 30, parent-chain test. Cached-hash exception above. |
| `auxpow.cpp:108–158` | `Block/AuxPowCheck.lean:140,190` | First occurrences, duplicate markers, offset ≤20, eight trailing bytes, little-endian size/nonce. |
| `auxpow.cpp:163–187` | `Block/AuxPowCheck.lean:78` | Wrapping UInt32 arithmetic, signed chain-ID conversion, heights 0–30. |
| `auxpow.cpp:189–206` | `Block/AuxPowCheck.lean:58` | Index −1, pair order, arithmetic shifts, empty branch. |
| `consensus/merkle.cpp:46–136` | `Block/Merkle.lean:31,72,85,107` | Root padding and complete-subtree mutation checks. Documented ≤2³¹-leaf domain. |
| `consensus/merkle.cpp:158–165` | `Block/Merkle.lean:111` | Base transaction IDs. Cached-hash exception above. |
| `primitives/pureheader.cpp:25–30` | `Block/ProofOfWork.lean:49` | Scrypt call on 80 header bytes and internal digest order. |
| `pow.cpp:115–132`, `arith_uint256.cpp:204–222,254–260` | `Work/ProofOfWork.lean:30,37,46` | Target sign, zero, overflow, limit, inclusive hash comparison, byte order. |
| `dogecoin.cpp:89–125` | `Block/ProofOfWork.lean:149` | Check order, payload/flag combinations, parent digest against child target. |
| `chainparams.cpp:88–141,233–306,392–437,494–506` | `Block/ProofOfWork.lean:66–121` | Limits, chain ID 98, strictness, effective heights, search links and boundary selection. |
| `validation.cpp:2927–2937` | `Block/ProofOfWork.lean:168,174` | Height-zero parameters, `high-hash`, documented `fCheckPOW=true` domain. |
| `validation.cpp:3068–3086` | `Block/VersionGate.lean:60,73` | Legacy/AuxPoW gates, order and reject reasons. Caller-selected parameters documented. |

## Not checked

- The internals of the SHA-256 and scrypt algorithms. The read compared their call sites and input bytes.
- Core's helpers that generate branches, witness Merkle roots, header setters and unrelated block methods. The scoped Lean definitions have no corresponding operations.
- Proofs and exports, which the brief excluded.
- Builds, differential comparisons and all other automated repository gates: **not run**. The reader changed no file.

## After the read

A check against Core at the pin, by the model that prepared this record, confirmed the finding from the source.
Core's implicit copy constructor copies the cache, so the boundary is the default transaction and every copy of it.
The example needs both indices set to zero, as the record says, because a default `CAuxPow` has `nIndex = -1` and Core rejects that first.
The doc comments of `Transaction.txid`, `WitnessTransaction.wtxid`, `blockMerkleRoot` and `AuxPow.check` state the boundary.
So do [SOUNDNESS.md](../../SOUNDNESS.md#the-auxpow-check) and the *AuxPoW check* and *Merkle root and mutation* rows of [COVERAGE.md](../../COVERAGE.md).
