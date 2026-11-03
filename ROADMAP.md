# Roadmap

This roadmap is the living plan. The reasoning behind it is in [design record 0001](docs/design/0001-initial-handoff.md) and [design record 0002](docs/design/0002-btc-verified-reuse.md). Update the *Status* column when a lane's pull request merges, not when work starts.

**Model project.** Where EthLib and btc-verified differ, DogeLib follows EthLib. That covers architecture, the proof-trust policy, the module system, the writing standard and the soundness documentation. The btc-verified project supplies components, mainly its codecs and packed-codec refinements, which DogeLib adapts to EthLib's structure.

## Work order

| Step | Deliverable | Exit condition | Status |
| --- | --- | --- | --- |
| 0 | Toolchain, build skeleton and checks | Lean `v4.35.0` is pinned. The lakefile has the libraries of ARCHITECTURE.md. EthLib's SHA-256 builds. `lake exe check-decls` runs. `BUILDING.md` lists the commands. | Done in `build/toolchain-selection` |
| 0b | Codec adaptation from btc-verified | The selected codecs and packed refinements are ported to `v4.35.0` and DogeLib's layout, with `bv_decide` steps replaced and provenance recorded | Not started |
| 1 | Source registry, shared types, contribution policy | Baseline and evidence conventions are explicit | Documents only |
| 2 | Bounded CompactSize reader and proofs | Accepted-prefix relation, bounded round trip, Core comparisons | Not started |
| 3 | Raw transaction types and base codecs | Exact field preservation, explicit parse mode, parser obligations | Not started |
| 4 | Legacy hash-plan specification | Declared lower-level modes and special cases are covered | Not started |
| 5 | Streaming preimage implementation and proof | Exact plan equality on the recorded domain | Not started |
| 6 | Rust refinement experiment | One extracted implementation matches an independent contract | Not started |

The steps are units of review, not one pull request each. Step 6 can start after step 2. A DigiShield arithmetic module is a reasonable parallel lane that must not delay the transaction path (design record 0001, section 10).

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
| btc-verified reuse form | Adaptation into DogeLib's layout, with provenance, not a dependency | Different toolchain, colocated proofs, and `bv_decide` steps | Pending: step 0b |
| Writing standard | EthLib's `WRITING.md` and checker, with DogeLib vocabulary | Follows the model project | Adopted |

## Open decisions

| Decision | Options under consideration | Owner lane |
| --- | --- | --- |
| Core compatibility pin | Adopt `v1.14.9` / `e0a1c15` or choose another | Maintainers, issue #5 |
| Oracle record format | Not yet proposed | Milestone B |
| First signature-proof domain | Fully parsed script code is the candidate | Milestone C |
| Project license and contributor terms | MIT intended. Recorded in `LICENSE` before the repository becomes public. Third-party material follows CONTRIBUTING.md. | Maintainers, issue #4 |

## Deferred work

Deferred work is tracked as GitHub issues with the `deferred` label.
Decisions that only a maintainer can make carry the `needs-maintainer` label.
