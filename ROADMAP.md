# Roadmap

This roadmap is the living plan. The reasoning behind it is in [design record 0001](docs/design/0001-initial-handoff.md) and [design record 0002](docs/design/0002-btc-verified-reuse.md). Update the *Status* column when a lane's pull request merges, not when work starts.

**Model project.** Where EthLib and btc-verified differ, DogeLib follows EthLib. That covers architecture, the proof-trust policy, the module system, the writing standard and the soundness documentation. The btc-verified project supplies components, mainly its codecs and packed-codec refinements, which DogeLib adapts to EthLib's structure.

## Work order

| Step | Deliverable | Exit condition | Status |
| --- | --- | --- | --- |
| 0 | Toolchain, build skeleton and checks | Lean `v4.35.0` is pinned. The lakefile has the libraries of ARCHITECTURE.md. EthLib's SHA-256 builds. `lake exe check-decls` runs. `BUILDING.md` lists the commands. | Done in `build/toolchain-selection` |
| 0b | Codec adaptation from btc-verified: codec foundations | btc-verified's codec class, fixed-width integer codecs, byte-buffer lemmas and packed codecs are ported to `v4.35.0` and DogeLib's layout, with provenance recorded | Done in `feat/codec-foundations` |
| 0b | Codec adaptation from btc-verified: CompactSize and counted lists | btc-verified's CompactSize and `CountedList` codecs and their packed forms are ported on top of the codec foundations, with `bv_decide` steps replaced and provenance recorded | CompactSize done in `feat/compactsize`. `CountedList` done in `feat/countedlist`, with Core's bounded vector reader. |
| 1 | Source registry, shared types, contribution policy | Baseline and evidence conventions are explicit | Documents only |
| 2 | Bounded CompactSize reader and proofs | Accepted-prefix relation, bounded round trip, Core comparisons | Reader, relation, soundness and completeness, bounded round trip, and known answers from Core's tests done in `feat/compactsize`. A packed form of the reader is done in `feat/packed-bounded-compactsize`. The comparison with Core's `ReadCompactSize` and `WriteCompactSize` is done in `test/core-harness`. |
| 3 | Raw transaction types and base codecs | Exact field preservation, explicit parse mode, parser obligations | Fixed-length byte strings and `Hash256` done in `feat/fixed-bytes`. Transaction types, base codecs, Core's base-mode reader, the complete reader and the transaction ID done in `feat/transaction-base`. The base-mode records of Core's transaction corpus are known answers (issue #22). The witness-allowed format, as a serialization format only, done in `feat/transaction-witness-format`. Its oracle operations and comparison with Core are issue #36. |
| 4 | Legacy hash-plan specification | Declared lower-level modes and special cases are covered | Done in `feat/legacy-sighash`: `legacySignatureHashPlan` for `SIGVERSION_BASE`, Core's `sighash.json` corpus and hand-derived preimages as known answers. The witness v0 digest and the `CheckSig` wrapper are not specified. |
| 5 | Streaming preimage implementation and proof | Exact plan equality on the recorded domain | Done in `proof/legacy-sighash-reference`. `legacySignatureHashPlan_eq_reference` proves the production plan equal to the `SignatureHashOld` transformation. It needs a fully parsed script code and counts below 2^32. The two differ on a script that ends in a short push. |
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract | Not started |

The steps are units of review, not one pull request each. Step 6 can start after step 2. The DigiShield retarget arithmetic is a parallel lane that must not delay the transaction path (design record 0001, section 10). The `Work` layer specifies it as an isolated function, with Core's `get_next_work_*` cases as known answers. Parameter selection by height, `GetNextWorkRequired` and header validity are not specified.

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

### C: one meaningful implementation equivalence (step 5)

A streaming preimage constructor proved equal to an independently reviewed transformation specification, over a documented domain. The first domain may require fully parsed script code. That restriction appears in the theorem, in COVERAGE.md, and in the release description.

### D: the Rust refinement path (step 6)

A safe Rust CompactSize decoder extracted through Charon/Aeneas at pinned revisions, proved against DogeLib's independent contract, and exercised on the same fixtures.

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
- Validation reports identifying the exact revisions and commands actually run.

If the Rust refinement is not in the first release, the release says so and makes no Rust verification claim.

## Decisions

| Decision | Choice | Reason | Confirmed by |
| --- | --- | --- | --- |
| Model project | EthLib | Stronger separation of specification, property and model, and explicit soundness documentation | Maintainer, 2026-11-03 |
| Lean toolchain | `v4.35.0`, EthLib's | Follows the model project and its module system. btc-verified pins `v4.30.0-rc2`. | Step 0 build |
| SHA-256 provider | EthLib | Its `hash_eq_spec` relates the executable code to a separate FIPS 180-4 model. It needs only Lean core, so it is adapted, not required. | Step 0 build |
| Proof-trust policy | EthLib's: standard axioms only, no tactic that trusts compiled code | See SOUNDNESS.md, C2 | Adopted |
| btc-verified reuse form | Adaptation into DogeLib's layout, with provenance, not a dependency | Different toolchain, colocated proofs, and `bv_decide` steps | Step 0b, codec foundations, with Lean core and `Std` only |
| Writing standard | EthLib's `WRITING.md` and checker, with DogeLib vocabulary | Follows the model project | Adopted |
| Oracle record format | JSON Lines, `dogelib-oracle/1`, in [docs/oracle.md](docs/oracle.md) | One request and one response per line, so a harness can keep the oracle open. Hashes in both byte orders, and preimages in the response. | Maintainer asked for the proposal, 2026-11-04 |
| Core compatibility pin | Dogecoin Core `v1.14.9`, commit `e0a1c15` | The latest Core release on 2026-11-03 | Maintainer, 2026-11-03, issue #5 |
| Project licence and contributor terms | MIT, in `LICENSE`. A contributor makes a contribution available under the same licence. Material from other projects follows CONTRIBUTING.md. | The most open licence that is compatible with the material DogeLib takes from other projects | Maintainer, 2026-11-04, issue #4 |

## Open decisions

| Decision | Options under consideration | Owner lane |
| --- | --- | --- |
| First signature-proof domain | Fully parsed script code is the candidate | Milestone C |

## Deferred work

Deferred work is tracked as GitHub issues with the `deferred` label.
Decisions that only a maintainer can make carry the `needs-maintainer` label.
