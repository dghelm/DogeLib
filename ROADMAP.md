# Roadmap

This roadmap records completed milestones and next work.
[COVERAGE.md](COVERAGE.md) holds detailed evidence, and [SOUNDNESS.md](SOUNDNESS.md) explains its assumptions and limits.
The reasoning behind the work order is in [design record 0001](docs/design/0001-initial-handoff.md) and [design record 0002](docs/design/0002-btc-verified-reuse.md).
Update the *Status* column when a lane's pull request merges, not when work starts.

**Model project.** Where EthLib and btc-verified differ, DogeLib follows EthLib. That covers architecture, the proof-trust policy, the module system, the writing standard and the soundness documentation. The btc-verified project supplies components, mainly its codecs and packed-codec refinements, which DogeLib adapts to EthLib's structure.

## Work order

| Step | Deliverable | Exit condition | Status |
| --- | --- | --- | --- |
| 0 | Toolchain, build skeleton and checks | Lean `v4.35.0` is pinned. The lakefile has the libraries of ARCHITECTURE.md. EthLib's SHA-256 builds. `lake exe check-decls` runs. `BUILDING.md` lists the commands. | Done in `build/toolchain-selection` |
| 0b | Codec adaptation from btc-verified: codec foundations | btc-verified's codec class, fixed-width integer codecs, byte-buffer lemmas and packed codecs are ported to `v4.35.0` and DogeLib's layout, with provenance recorded | Done in `feat/codec-foundations` |
| 0b | Codec adaptation from btc-verified: CompactSize and counted lists | btc-verified's CompactSize and `CountedList` codecs and their packed forms are ported on top of the codec foundations, with `bv_decide` steps replaced and provenance recorded | CompactSize done in `feat/compactsize`. `CountedList` done in `feat/countedlist`, with Core's bounded vector reader. |
| 1 | Source registry, shared types, contribution policy | Baseline and evidence conventions are explicit | Documents only |
| 2 | Bounded CompactSize reader and proofs | Accepted-prefix relation, bounded round trip, Core comparisons | Reader, relation, soundness and completeness, bounded round trip, and known answers from Core's tests done in `feat/compactsize`. A packed form of the reader is done in `feat/packed-bounded-compactsize`. The comparison with Core's `ReadCompactSize` and `WriteCompactSize` is done in `test/core-harness`. |
| 3 | Raw transaction types and base codecs | Exact field preservation, explicit parse mode, parser obligations | Fixed-length byte strings and `Hash256` done in `feat/fixed-bytes`. Transaction types, base codecs, Core's base-mode reader, the complete reader and the transaction ID done in `feat/transaction-base`. The base-mode records of Core's transaction corpus are known answers (issue #22). The witness-allowed format, as a serialization format only, done in `feat/transaction-witness-format`. The oracle exposes both witness readers, serialization and hashes. The Core comparison covers all 198 corpus records and malformed variants (issue #36). |
| 4 | Legacy hash-plan specification | Declared lower-level modes and special cases are covered | Done in `feat/legacy-sighash`: `legacySignatureHashPlan` for `SIGVERSION_BASE`, Core's `sighash.json` corpus and hand-derived preimages as known answers. The witness v0 digest and the `CheckSig` wrapper are not specified. |
| 5 | Field-by-field preimage construction proved equal to the transaction-transformation reference | Exact plan equality on the recorded domain | Done in `proof/legacy-sighash-reference`. `legacySignatureHashPlan_eq_reference` proves the production plan equal to the `SignatureHashOld` transformation. It needs a fully parsed script code and counts below 2^32. The two differ on a script that ends in a short push. |
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract | Done in `feat/rust-compactsize-refinement` (#51). See [milestone D](#d-the-rust-refinement-path-step-6). |

The steps are units of review, not one pull request each.
Step 6 can start after step 2.

The DigiShield retarget arithmetic is a parallel lane that must not delay the transaction path (design record 0001, section 10).
The `Work` layer specifies the arithmetic as an isolated function, with Core's `get_next_work_*` cases as known answers.
`Work.Consensus` specifies the work-field projection of height-based parameter selection.
`Work.NextWork` specifies `GetNextWorkRequired` on a checked finite view, including minimum-difficulty rules.

`Work.ProofOfWork` specifies Core's compact-target range check and supplied-hash comparison.
Target validity discharges the retarget old-target bound, with numerical bounds proved for every mainnet and testnet parameter selection.
Regtest DigiShield has multiplier one and cannot wrap.
The isolated retarget can wrap with the legacy regtest record, which the normally selected caller never uses at a retarget.
Scrypt, AuxPoW and full header validity are not specified.

The `Block` layer specifies pure 80-byte headers, their double SHA-256 hashes and transaction Merkle roots with complete-subtree mutation detection.
Its codec and structural properties are separate from scrypt, AuxPoW and block validity.
[Block fixture provenance](tests/block/README.md) records the finite known answers.

The word-arithmetic proofs cover division and its dependencies (#47), as well as multiplication, shifts, bit length and low-64-bit extraction (#42).
The compact, constructor and byte-conversion paths and the composed word retarget also have arithmetic equivalence proofs (#50).
[COVERAGE.md](COVERAGE.md#operations) records the operation-level evidence.
[SOUNDNESS.md](SOUNDNESS.md#256-bit-word-division) explains the division domain, zero-divisor exception and source-review boundaries.

`Cryptography.Hash.Sha1` specifies SHA-1 as a prerequisite of legacy Script execution.
`hash_eq_spec` relates the executable function to a separate FIPS 180-4 model for messages shorter than 2^61 bytes.
NIST short, long and Monte Carlo vectors and Core's ten SHA-1 cases check the compiled code.
[COVERAGE.md](COVERAGE.md#operations) records this implemented coverage, independently of the frozen scope in design record 0003.
The SHA-1 oracle operation remains deferred in issue #64.

The Script layer implements stage 1 of [design record 0003](docs/design/0003-legacy-spend-validation.md): the instruction reader and the state of one `EvalScript` call.
`Script.readInstruction` follows `GetOp2`, including the cursor after each failure, and shares its decoder with the legacy signature serializer.
`Script.ExecState` gives the per-call reset and the main-stack hand-off of `VerifyScript`.
The layer has no oracle operation and gives no verdict on a spend.

The Script layer also has the numeric part of stage 2 of [design record 0003](docs/design/0003-legacy-spend-validation.md): `CScriptNum` and `CastToBool` over integers, in `Script.Number`.
`isMinimal_iff_encode_value` shows that Core's minimality test accepts exactly the encodings, and the decode theorems give every result, with the size check first.
[COVERAGE.md](COVERAGE.md#operations) records the evidence and the exclusions.

`Script.evalScript` implements one `EvalScript` call, stages 2b and 2c of [design record 0003](docs/design/0003-legacy-spend-validation.md).
It runs pushes, NOPs, control flow, stack operations, `OP_SIZE`, equality, the numeric and hash opcodes and `OP_CODESEPARATOR`.
It follows Core's errors and check order, also in skipped branches.
Signature opcodes, CLTV and CSV with their flags, and flags outside the seven of the design record give `unsupported`, never a rejection.
On Core's `script_tests.json`, 745 records agree with Core, none disagrees, and 448 are unsupported.

`Script.SignatureCode` implements push encoding and effective script-code preparation for stage 3.
Its proofs cover the push reader round trip below 2^32 bytes and the exact traversal of `FindAndDelete`, including malformed suffixes.
Known answers include all sixteen Core deletion cases and every push-size transition.
Signature encoding and opcode integration remain the next Script work.

Steps 0 and 0b follow design record 0002: the first contributions adopt audited codec foundations and then define Dogecoin's bounded decoding contract. They replace the original plan to build fixed-width encodings and CompactSize from scratch. Design record 0002 preferred a pinned btc-verified dependency first. The decisions below choose an adaptation instead, because btc-verified's toolchain, file structure and trust policy all differ from EthLib's.

## Milestones

### A: a small byte codec (steps 0, 0b and 2)

A Dogecoin-compatible bounded CompactSize reader, separate from the generic canonical decoder. Its contract:

```text
dogeDecode(bytes) = success(value, remainder)
  iff genericDecode(bytes) = success(value, remainder)
      and value <= 0x02000000
```

The distinguishing input `fe 01 00 00 02` encodes `0x02000001`. The generic decoder accepts it, and the Core reader rejects it. Do not replace the decoder inside an unconditional `Codec UInt64` instance while keeping its old laws.

### B: transaction encoding and legacy signing commitments (steps 3–4)

Raw fields preserved without validation, base/no-witness parsing with prefix and complete-input forms kept apart, and a `LegacyHashPlan` that separates preimage construction from hashing. Includes the executable oracle.

The oracle, `dogelib-oracle`, exists ([docs/oracle.md](docs/oracle.md)). The Core harness runs Dogecoin Core's code on the same requests, and CI compares the two ([docs/oracle.md](docs/oracle.md#the-core-harness)).

Oracle format `/4` exposes pure headers, Merkle roots, RIPEMD-160, Hash160 and SHA-1.
The Core comparison covers their committed fixtures and generated boundaries ([format and comparison](docs/oracle.md)).
Format changes require maintainer review.

### C: one meaningful implementation equivalence (step 5)

The field-by-field preimage construction is proved equal to the transaction-transformation reference by `legacySignatureHashPlan_eq_reference`.
The theorem requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
It holds for every input index and hash type on that domain.
The implementation constructs the whole preimage as a byte list before hashing.
An incremental hash sink and measured memory or speed gains are later work.

### D: the Rust refinement path (step 6)

The bounded Rust CompactSize decoder and its extracted Lean model are in `Refinement/Rust/` and `Refinement/Refinement/Rust/` (#51).
`decode_refines` proves complete-result agreement with the independent bounded-reader specification.
[SOUNDNESS.md](SOUNDNESS.md#rust-bounded-compactsize-reader) explains the theorem's domain, complete-result equality and extraction boundaries.
[COVERAGE.md](COVERAGE.md#operations) records its proof and fixture evidence.
[Refinement/Rust/README.md](Refinement/Rust/README.md) gives the regeneration and test commands.

## Release acceptance criteria

From design record 0001, section 9. A first release has:

- A source mapping and explicit input domain for every public operation.
- Codec soundness and completeness properties, with correctly bounded inverses.
- Raw fields that preserve values rejected by later validation.
- Documented lower-level legacy hash modes and special cases.
- At least one nontrivial implementation-equivalence theorem.
- An executable oracle and a reproducible Core comparison harness.
- Independent fixtures, targeted boundary and malformed cases, and minimized mismatches.
- A statement of proof assumptions, execution boundaries, and unsupported areas.
- Validation reports identifying the exact revisions and commands actually run ([report command](BUILDING.md#validation-reports)).

## Decisions

| Decision | Choice | Reason | Confirmed by |
| --- | --- | --- | --- |
| Model project | EthLib | Stronger separation of specification, property and model, and explicit soundness documentation | Maintainer, 2026-11-03 |
| Lean toolchain | `v4.35.0`, EthLib's | Follows the model project and its module system. btc-verified pins `v4.30.0-rc2`. | Step 0 build |
| SHA-256 provider | EthLib | Its `hash_eq_spec` relates the executable code to a separate FIPS 180-4 model. It needs only Lean core, so it is adapted, not required. | Step 0 build |
| Proof-trust policy | EthLib's: standard axioms only, no tactic that trusts compiled code | See SOUNDNESS.md, C2 | Adopted |
| btc-verified reuse form | Adaptation into DogeLib's layout, with provenance, not a dependency | Different toolchain, colocated proofs, and `bv_decide` steps | Step 0b, codec foundations, with Lean core and `Std` only |
| Writing standard | EthLib's `WRITING.md` and checker, with DogeLib vocabulary | Follows the model project | Adopted |
| Oracle record format | JSON Lines, `dogelib-oracle/5`, in [docs/oracle.md](docs/oracle.md) | One request and one response per line, so a harness can keep the oracle open. Hashes in both byte orders, preimages and individual Script calls. | Format `/4`: maintainer, PR #67. Format `/5`: maintainer, PR #74. |
| Core compatibility pin | Dogecoin Core `v1.14.9`, commit `e0a1c15` | The latest Core release on 2026-11-03 | Maintainer, 2026-11-03, issue #5 |
| First signature-proof domain | Script code with no instruction that fails to parse, in a transaction with fewer than 2^32 inputs and 2^32 outputs | `legacySignatureHashPlan_eq_reference` holds on it. On a script that ends in a short push the two forms differ. | Step 5, `proof/legacy-sighash-reference` (#27) |
| Rust refinement tools | Aeneas `d1e177b` and Charon `a58d159` (Adopted in SOURCES.md). Mathlib only in the separate `Refinement` Lake package. No trust-policy exception for Aeneas's axioms | Both tools target Lean `v4.35.0`. EthLib requires Mathlib. EthLib's trust policy allows only the three standard axioms | Maintainer, 2026-11-04, PR #33 |
| Project licence and contributor terms | MIT, in `LICENSE`. A contributor makes a contribution available under the same licence. Material from other projects follows CONTRIBUTING.md. | The most open licence that is compatible with the material DogeLib takes from other projects | Maintainer, 2026-11-04, issue #4 |

## Open decisions

None. A maintainer decision that blocks a lane becomes an issue with the `needs-maintainer` label.

## Deferred work

Deferred work is tracked as GitHub issues with the `deferred` label.
Decisions that only a maintainer can make carry the `needs-maintainer` label.
