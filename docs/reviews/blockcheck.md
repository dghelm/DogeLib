# Model read: Block codec, CheckTransaction and CheckBlock

- Reader: GPT-6 (Codex; exact build unavailable), an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: 6ca6373. Core: e0a1c157791544e818c901bd9341896965afbf9d
- Scope: `Transaction/{Check,SigOps}.lean`, `Block/{Block,Check}.lean`, and the specified dependencies, against the pinned Core source.

## Result

No consensus discrepancy found within the documented domains. One documentation discrepancy concerns deserialization and `fChecked`. Confidence is high in the compared validation and codec logic, subject to the exclusions below.

## Findings

1. **Deserialization does not always leave `fChecked` false.**  
   **Lean:** `DogeLib/Block/Check.lean:32`. **Core:** `src/primitives/block.h:74–98`, `src/validation.cpp:2943`.  
   The comment says a block read from a stream has `fChecked` false. Constructors initialize it to false, but `SerializationOp` only reads the header and transactions. Deserializing into an existing checked object preserves true.
   
   **Concrete input:** Start with `b.fChecked = true`, then deserialize a header and an empty transaction vector into `b`. Core’s `CheckBlock(b, state, false, false)` returns true immediately. Lean returns `.length`. This is outside Lean’s explicitly documented false-cache domain, so the finding concerns the explanation, not that restriction.
   
   **Severity:** documentation-only. **Confidence:** high. The ordinary `block.check` operation cannot expose this unless its harness supports object reuse.

## Checked and agreeing

Paths in the Lean column are relative to `DogeLib/`.

| Core construct (file:lines) | Lean definition (file:line) | Notes |
| --- | --- | --- |
| `validation.cpp:527–536`, empty lists and transaction size | `Transaction/Check.lean:141` | Inputs, outputs, then base size. Exactly 1,000,000 bytes passes. |
| `validation.cpp:539–549`, output loop; `amount.h:16–33` | `Transaction/Check.lean:110` | Signed `int64_t` amounts. Negative, individual upper bound, then running sum. `MAX_MONEY = 10^18` is inclusive. |
| Same, addition safety | `Transaction/Check.lean:18` | Integer-model reason holds: before addition both operands are in `[0,10^18]`. Result is nonnegative and at most `2×10^18 < INT64_MAX`. |
| `validation.cpp:551–559`; `primitives/transaction.h:43–51` | `Transaction/Check.lean:125` | Set equivalence is equality of hash and index. Quadratic duplicate search gives the same failure. Flag respected. |
| `primitives/transaction.h:41,354–357` | `Transaction/Check.lean:55` | Null means zero hash **and** index `0xffffffff`. Coinbase means exactly one null input. |
| `validation.cpp:561–574` | `Transaction/Check.lean:152` | Coinbase script length accepts 2 through 100. Otherwise every null prevout fails. Duplicate check precedes both. |
| `validation.cpp:531–570`, transaction failure metadata | `Transaction/Check.lean:86` | All nine reasons match. Scores: 10 for empty inputs, empty outputs and null prevout; 100 otherwise. All codes `0x10`, corruption false. |
| `script/script.h:492–552`, `GetOp`/`GetOp2` | `Transaction/LegacySighash.lean:130` | Direct pushes and PUSHDATA1/2/4 lengths agree. Short length/data stops parsing. Correspondence restricted to scripts shorter than `2^31` bytes. |
| `script/script.cpp:156–177` | `Transaction/SigOps.lean:57` | `ac/ad` count 1, `ae/af` count 20. Push contents do not count. Failed reads preserve the prior count. |
| Same, inaccurate mode | `Transaction/SigOps.lean:70` | Restriction justified: false bypasses the `lastOpcode` branch entirely. No interpreter script-size or opcode-validity checks belong here. |
| `validation.cpp:475–487` | `Transaction/SigOps.lean:78` | Every input script, including coinbase, then every output script. Natural count modulo `2^32` equals Core’s unsigned count. |
| `primitives/block.h:87–91`; `serialize.h:676–692,801–805` | `Block/Block.lean:77`, `:98` | Full header, CompactSize transaction count, exactly that many transactions in order. Shared-pointer reading adds no wire fields. Prefix remainder retained. |
| `serialize.h:244–274` | `Serialization/CompactSize.lean:250` | Canonicality precedes `MAX_SIZE`. `0x02000000` permitted; larger canonical count yields `.read .tooLarge` before reading any transaction. |
| `primitives/transaction.h:210–272` | `Block/AuxPow.lean:131`, `:205` | Base and witness modes agree, including empty input marker, zero flags, empty witness stacks and unknown-flag failure order. |
| `primitives/block.h:37–48`; `auxpow.h:80–84,155–160` | `Block/AuxPow.lean:146`, `:171`, `:210`, `:222` | Header/payload field order agrees. One stream mode reaches the embedded AuxPoW transaction and all block transactions. Missing flagged payload is a documented writer exclusion. |
| `serialize.h:947–951`; `validation.cpp:535,2972` | `Block/Block.lean:133`, `:142` | Both size checks measure base serialization. AuxPoW transaction witnesses are excluded too. `size_t` comparisons with unsigned block-size constants preserve the bounds. |
| `consensus/merkle.cpp:46–136,158–165` | `Block/Merkle.lean:72`, `:85`, `:115` | Empty root zero; singleton unchanged; odd padding agrees. Mutation compares complete aligned subtrees, excluding final padding sweep. Documented count/cache exclusions acknowledged. |
| `validation.cpp:2927–2937`; `dogecoin.cpp:89–125` | `Block/ProofOfWork.lean:149`, `:174` | Flag bypass, height-zero parameters and header rejection agree. Every failure becomes `high-hash`, score 50, code `0x10`, corruption false. |
| `auxpow.cpp:80–206`; `pow.cpp:115–132` | `Block/AuxPowCheck.lean:183`; `Work/ProofOfWork.lean:46` | AuxPoW check order, branch direction, root search, nonce/index arithmetic and target predicates agree. Signed-shift convention is documented. |
| `validation.cpp:2951–2962` | `Block/Check.lean:148` | Root mismatch precedes mutation. Reasons match; both score 100, code `0x10`, corruption true. |
| `validation.cpp:2971–2980` | `Block/Check.lean:151` | Empty/count/base-size checks precede coinbase placement. Count and byte limits are inclusive at 1,000,000. Reasons match; score 100, code `0x10`, corruption false. |
| `validation.cpp:2983–2986`; `consensus/validation.h:35–54` | `Block/Check.lean:118`, `:87–112` | First failing transaction wins. `Invalid` adds zero DoS, preserves reason/code, and sets corruption false. Reported scores agree for an initially valid state. Debug strings are not represented. |
| `validation.cpp:2988–2994`; `primitives/transaction.h:17`; `consensus/consensus.h:19` | `Block/Check.lean:163` | `unsigned int × int` computes unsigned modulo `2^32`, then converts losslessly to `int64_t` for comparison. Lean’s final reduction agrees. Exactly 80,000 passes. |
| `validation.cpp:2943,2996–2997` | `Block/Check.lean:28`, `:142` | False-cache restriction is explicit and appropriate for a stateless call. Successful cache mutation is intentionally unrepresented. |
| All statements of `CheckTransaction` and `CheckBlock` | `Transaction/Check.lean:141`; `Block/Check.lean:142` | No witness-stack data influences validation. Sizes, txids, AuxPoW transaction hashes and sigops use base fields. |

## Not checked

- SHA-256, double-SHA-256 and scrypt primitive implementations, foundational codec implementations, compiler substitutions and proofs. Their use and serialization inputs were inspected.
- Runtime allocation failures, resource exhaustion, reused validation-state behavior and cases outside documented reader/hash domains.
- All builds, tests, differential comparisons and other executable checks were not run, as requested. No files were edited.

## After the read

This section is an addendum, not part of the read.

- The header names the reader as the model named itself. The Codex log of the run gives the model identifier `gpt-6.1-sol`.
- Finding 1 is correct. `CBlock::SerializationOp` reads the header and `vtx`, and it does not assign `fChecked` (`src/primitives/block.h`, lines 87 to 91).
  At the revision of the read, the module documentation of `DogeLib.Block.Check` said that a block from a stream has `fChecked` false.
  It now says that this holds for a read into a new object, and that a read into an object with the member set is outside the definition.
  [SOUNDNESS.md](../../SOUNDNESS.md#block-codec-checktransaction-and-checkblock) and [docs/oracle.md](../oracle.md#transaction-and-block-checks) say the same.
  The Core harness reads each block into a new `CBlock`, and it stops if the member is set before the call.
- The definitions did not change after the read.
