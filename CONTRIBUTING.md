# Contributing

This file sets the rules for contributing to DogeLib.
They apply to every contributor, human or AI.
[AGENTS.md](AGENTS.md) says how to work in this repository: lanes, checks and what to update.
[WRITING.md](WRITING.md) sets the standard for prose.

DogeLib is an executable formal specification of Dogecoin, written in Lean, with proofs about it.
It models what Dogecoin does today, states proposed changes as named revisions of that behavior, and proves that implementations compute what the specification says.
Consensus software gives no second chance to a wrong rule.
A definition that disagrees with Dogecoin can carry correct theorems and still mislead every client that trusts it.
So every definition must be justified by its source, and every claim must say exactly what it covers.

## The bar

Work the way the author of a consensus specification would.

- Read the pinned source, the surrounding definitions and the existing proofs before you write anything.
- Every definition, constant and rule has a source.
  You have read that source.
- If a source is ambiguous or two sources disagree, stop and say so.
  Do not pick one silently.
- Never invent a citation, a commit, a fixture or an expected value.
- Never claim a check passed unless you ran it and saw it pass.
- Keep changes small and on topic.
  Give each pull request one purpose.

When you are not sure, ask.
A question costs minutes.
A plausible guess merged into a consensus specification costs far more.

## One purpose per change

Each change has one primary purpose, and its description says what that purpose requires:

| Purpose | The description says |
| --- | --- |
| Existing behavior | Which pinned Dogecoin behavior the definition captures |
| Proposed revision | Which existing rules change, and under which activation conditions |
| Property or proof | The exact claim, its input domain and its hypotheses |
| Implementation or optimization | The reference definition, and the observable behavior the implementation preserves |
| Conformance | The implementations compared, the input corpus and the limits of the evidence |
| Tooling or documentation | The development problem it solves |

A change can touch several files when they implement one idea.
Leave out unrelated cleanup, and abstractions that nothing uses yet.
A small operation with its definition, proofs and evidence is worth more than many incomplete modules.

Existing consensus, proposed consensus changes and node policy are three separate subjects.
A mempool standardness check must not become a consensus rule by accident.
A proposed improvement must not change the baseline.

## Sources of truth

For existing consensus, the authority is the behavior of Dogecoin Core at the commit pinned in [SOURCES.md](SOURCES.md).
Read its source code and its tests together with the historical rules and independently identified examples.
A published specification or proposal can explain a rule, but it does not override historical compatibility.

Compatibility applies to the specified API or consensus contract, not to every artifact of the C++ code.
A crash, undefined behavior or an unrelated implementation detail is not a protocol requirement.
Document such a case, and decide the intended contract explicitly.

Each public operation documents:

- Its source: repository, commit, file, and function or section.
- Its input domain, the meaning of its output, and its failure behavior.
- The serialization mode, flags, network, activation state or historical era it requires.
- Known differences from the related Bitcoin or Ethereum definitions.
- Each unresolved discrepancy and each deliberately excluded case.

[SOURCES.md](SOURCES.md) is the only registry of pinned revisions, and a reference in a module agrees with it.
A pin change reviews the affected definitions, fixtures and coverage claims in the same change, or in an explicitly linked series.

When two sources disagree, record a minimal reproducer in [SOURCES.md](SOURCES.md) and investigate.
Continue with independent work in the meantime.
Do not normalize the discrepancy away, choose the more convenient source, or describe an unresolved rule as established consensus.
If Core's behavior should change, specify that as a proposed revision.

Core's test corpus is essential evidence, but it is not an exhaustive specification.
A passing comparison does not show equivalence on every input.

## Layout

[ARCHITECTURE.md](ARCHITECTURE.md) gives the Lake libraries, the layers and what each may import.
In short:

- The specification contains protocol types and executable definitions.
  It never imports a proof, an adapter or an extracted implementation.
- Proofs live in their own library and import the definitions they reason about.
- The oracle and any binding-facing code live in the `Exports` library.
- Refinement code relates another implementation to the specification.
- A security or network model is added only when a theorem needs it.

Keep the specification's dependencies small.
Mathematical and probability libraries belong in proofs and models.
Do not create a generic framework to reserve space for future features.

## Lean

### Specification code

- Write the code to be read first and run second.
  The specification must make sense on its own, without reference to an optimized implementation.
- Name things after the source.
  If Dogecoin Core calls a field `nLockTime`, so does the definition, in Lean's casing.
- Write pure, total definitions with explicit, typed errors.
  Avoid `partial` definitions, hidden mutable state, control flow by panic, and IO that the model does not describe.
  An adapter can use IO, and documents its trust boundary in [SOUNDNESS.md](SOUNDNESS.md).
- Put invariants in types, such as fixed lengths and bounds.
- An extracted Rust model is an implementation artifact.
  It never becomes the specification, even when that would make a refinement theorem easier.

### Raw input

Model the wire data before any contextual validity rule.
A raw transaction can represent fields that later validation rejects, including negative amounts.
Keep script bytes and field encodings wherever they affect a commitment.
Do not canonicalize, truncate, pad or substitute a default.

Malformed input is defined relative to the selected API and protocol era.
A stricter decoder can disagree with consensus even when every input it accepts is well formed by a modern standard.

A parser contract states whether the parser consumes a prefix or requires the whole input.
It records the returned value and the remaining bytes or the consumed length.
If a public error category is part of the contract, an implementation proof preserves it.
Otherwise, the contract defines the abstraction under which errors are compared.
Diagnostic text need not become a consensus guarantee.

A round trip needs the right preconditions.
For example, the pinned Core CompactSize reader rejects values above `MAX_SIZE = 0x02000000`, and its writer accepts every 64-bit value:

```text
encode(0x02000001)          = fe 01 00 00 02
generic decode              = success(0x02000001, [])
Core-compatible decode      = failure (above MAX_SIZE)
```

So the round trip holds only for `n <= 0x02000000`.
A theorem over every 64-bit value would describe a different API.
Optional transaction serialization modes need separate treatment for the same reason.

State integer semantics explicitly: range checks, wrapping, signed interpretation, shifts, division and conversion.
Use mathematical integers where they fit, and prove the connection to the machine operation.
Do not assume that a convenient Lean operation matches C++ or Rust on every boundary case.

### Theorem statements

Decide which claim a consumer needs before substantial proof work.
Review the definition, the quantifiers, the input domain, the preconditions and the conclusion.
A reviewer must be able to assess them without reading the tactic script.
That review is part of the ordinary pull request, not a separate process.

Useful obligations include:

- Soundness and completeness of a parser against a separately stated encoding relation.
- Exact serialization and commitment bytes.
- Agreement of an implementation with the reference on accepted and rejected inputs.
- Agreement on returned values, consumed bytes and state effects.
- State invariants under their required context.
- Explicit compatibility relations between named protocol revisions.

Avoid a one-sided claim when equivalence is intended.
A decoder that rejects everything satisfies "every accepted input is valid".
A round trip can also hold when the encoder and the decoder share the same mistake.

When a theorem covers a restricted domain, name the restriction and say how callers establish it.
For example, a signature-preimage theorem can require fully parsed script code.
An end-to-end spending claim then waits for a proof that the interpreter supplies that condition.

Do not weaken a theorem, strengthen its preconditions, redefine its reference operation, or move its conclusion into a hypothesis to finish a proof.
A justified change to the intended contract is allowed.
It appears explicitly in the diff and receives a review of its meaning.

### Proofs

- Do not use `sorry`, `admit` or a new `axiom`, including through a dependency.
  The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.
- Do not use a tactic that trusts compiled code, such as `native_decide`, `bv_decide` or `decide +native`.
  Their results rest on axioms that trust the compiler, not on kernel evaluation.
  The ban is a boundary choice, not a claim that those tactics are unsound.
- Check the elaborated declarations and their transitive dependencies, not only the source text.
  The check reports every extra axiom, and every operation whose compiled behavior differs from its logical definition or cannot be unfolded.
- Record the actual axiom dependencies of each important exported theorem in [SOUNDNESS.md](SOUNDNESS.md).
- Give `unsafe`, `opaque`, `@[extern]`, `@[implemented_by]` and `@[csimp]` explicit treatment in [SOUNDNESS.md](SOUNDNESS.md).
  A proof-backed substitution is reported separately from an unproved one.
- State a cryptographic or network assumption as a named hypothesis or a model parameter.
  Say what it assumes and where, if anywhere, it is discharged.

An exception to these rules is a change to the trust policy in [SOUNDNESS.md](SOUNDNESS.md), reviewed on its own.
It is never an entry in a growing list of exceptions.

Keep the force of a conditional result.
A proof that assumes signature unforgeability does not prove unforgeability.
Two equal hash preimages give equal digests with no assumption about the hash.
A claim that different preimages give different digests needs a different argument.

A harness or a trusted foreign adapter can use facilities that the specification excludes.
It stays separate, and it never transfers an unproved implementation claim into a theorem.
The Lean compiler, the runtime, foreign bindings and extraction tools do not become verified because a theorem checks.
[SOUNDNESS.md](SOUNDNESS.md) describes their role.

### Optimizations and protocol revisions

An optimization preserves the specification.
State the observable relationship, including errors and state effects where they matter.
The implementation can use a different representation, related to the reference by an explicit abstraction relation.

Prove the relationship at the strongest useful boundary.
Equal preimage bytes make equal digests immediate.
A parser refinement preserves the interpretation and the remaining input.

A proof establishes behavior, and a benchmark measures performance.
Report each separately, and claim no improvement without a reproducible measurement.
Termination is not a resource guarantee.
Keep the protocol's resource limits, and state any further bound on input size, work, allocation or recursion that a new operation needs.

A protocol revision changes behavior on purpose.
Give it a name, keep the baseline available, and state its activation and context assumptions.
A soft-fork claim uses the right legacy projection and its state effects.
It does not assume that new and old nodes receive the same encodings.
A local strengthening of a Script rule is not a proof of network convergence or liveness.

Say which implementation a proof covers.
A proof about a Lean implementation covers only that implementation.
Differential testing against Core and a refinement theorem about extracted Rust are different evidence, and are labeled separately.

### Fixtures and comparisons

A fixture pins one input to one declared result.
Prefer pinned Core tests, a primary specification or documented historical data as its source.
Record its provenance, the exact input and expected output, and any context it needs.
Never generate an expected value from the implementation under test and present it as an independent check.

Conformance work covers boundary values, truncation, nonminimal encodings, unexpected modes and rejected inputs, as well as ordinary successes.
Compare the full declared result.
For a randomized comparison, record the seed or save the failing input.
Reduce each discrepancy to a permanent regression case.

Fixtures change only with a reviewed change to a source or its interpretation.
A test runner compares results with the committed expectations, and never overwrites them.

Core's [signature-hash tests](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/sighash_tests.cpp) are a starting corpus and a design reference.
They do not establish equivalence on every input, and they do not replace an analysis of a theorem's domain.

## Coverage and status

[COVERAGE.md](COVERAGE.md) records status per operation and per property.
It keeps executable definitions, unconditional proofs, conditional proofs, comparison evidence, implementation refinements and unsupported cases apart.
"Verified module" says nothing until it says which claims are verified.

Incomplete research can stay in the excluded experimental area when it is useful.
No release target imports it, and it never counts as verification.

Pin the Lean toolchain, the libraries, the reference sources and the extraction tools.
Change an incompatible combination of versions on purpose, in its own change.

## Writing and documentation

Follow [WRITING.md](WRITING.md) for all prose: documentation, doc comments, commit messages and pull request text.
Write for a careful reader who has never seen the file.

- State what the source supports, and no more.
  Keep the hypotheses, the bounds and the force of each claim.
- Describe the library as it is.
  History belongs in commit messages and design records.
- Explain why. The code already says what.
- Draw byte layouts in a fenced `text` block.

Every public declaration has a doc comment.
A theorem's doc comment states its claim in English, with its input domain and preconditions.
Write one sentence per line in Lean comments and in Markdown source, so that a diff shows one sentence per line.

`scripts/check_writing.py` reports patterns that a search can find.
Its findings are advice for a reviewer, not a gate.

## Checks

These gates apply to every pull request:

| Gate | What it requires |
| --- | --- |
| Build | The specification, proof and adapter libraries compile with the pinned toolchain, with warnings as errors |
| Declaration check | No unexpected axiom, and no undocumented logical or runtime substitution |
| Sources and coverage | Changed definitions keep accurate provenance, input domains and status |
| Conformance | Relevant fixtures and boundary comparisons pass |
| Refinement | Changed optimized operations keep their equivalence proofs |
| Soundness | New dependencies, assumptions and execution boundaries are disclosed |

[AGENTS.md](AGENTS.md#checks) lists the command for each gate, which gates exist yet, and which of them CI runs.
A change that adds or changes a check updates that table.
Run the checks that the change affects.
Widen the testing to resolve a concrete risk, not by habit.
A documentation change needs no performance campaign.

Report what you ran, against which revision, and what it printed.
Mark every other check as not run.
Do not infer a pass from a successful compilation, an earlier run or another contributor's intent.

## Branches, commits and pull requests

A reviewer should know in fifteen seconds what the change does and where to look.

### Lanes and branches

Parallel work happens in separate git worktrees called lanes, one branch each.
[AGENTS.md](AGENTS.md#lanes) describes the lane workflow and the `scripts/lane` tool.

A branch name is `<type>/<slug>`, with a type from the list below, such as `feat/compactsize-bounded-reader`.
`main` stays linear.
A lane rebases onto `main`, and never merges `main` into itself.
Pull requests are squash-merged, so the pull request title becomes the commit on `main`.

### Titles

Commit subjects and pull request titles follow [Conventional Commits 1.0.0](https://www.conventionalcommits.org/en/v1.0.0/):

```text
<type>(<scope>): <summary>
```

| Type | Use |
| --- | --- |
| `feat` | New executable behavior: a definition, an operation or an oracle command |
| `fix` | A definition that disagreed with its source now agrees |
| `proof` | New or changed theorems, with no change to executable definitions |
| `perf` | The same results, computed differently, with a preservation proof or a measurement |
| `refactor` | The same behavior, restructured |
| `test` | Fixtures, comparisons and regression cases |
| `docs` | Documentation only |
| `build` | Lake, the toolchain, dependency pins and packaging |
| `ci` | Workflows |
| `chore` | Any other change to no definition, proof or test |

The scope names a layer or an operation in lowercase, such as `compactsize`, `tx`, `sighash`, `sha256`, `oracle` or `rust`.
Leave it out when the change spans the repository.
The summary is an imperative phrase that starts in lowercase, with no final period.
The whole title fits in 72 characters.

A change to a public contract, a theorem statement or a fixture format adds `!` before the colon.
Its commit body ends with a `BREAKING CHANGE:` footer that says what consumers change.

```text
feat(compactsize): add the Core-compatible bounded reader
proof(compactsize): prove the bounded round trip
fix(tx)!: keep output amounts as raw signed values
build: pin Lean v4.35.0
```

### Bodies

The commit body says why, when the subject cannot.
Leave out what the diff already shows.

Write the pull request body for a reviewer who has never seen the change, with the four parts of the [template](.github/pull_request_template.md):

- **Purpose**: the behavior, property or development problem.
- **Contract and sources**: the pinned references, the input domain and the observable behavior.
  State any change to an earlier contract or to theorem hypotheses.
- **Evidence**: the theorems added or changed, with their scope.
  The commands run, with their results and revisions. The checks not run, and why.
- **Remaining boundaries**: unsupported cases, conditional hypotheses, and runtime or extraction trust.

Leave out a part that does not apply.
A new module or a subtle proof deserves one concrete example, with real bytes traced step by step.

### Deferred work

A deferral is complete only when it is tracked.
Record set-aside work as a GitHub issue with the `deferred` label, with enough context to act on it cold.
Reference it where the work was deferred.

## AI contributors

AI contributors meet the same standard of evidence and review.
Report uncertainty, keep the agreed contract, and never claim an execution or a verification that did not happen.
Reviewers assess definitions and theorem statements on their own merits, whatever the confidence of the generated proof.

## Licence

DogeLib's own material is intended to be distributed under the MIT licence.
The repository is private, and the licence is recorded in a `LICENSE` file before it becomes public.
The goal is the most open licence that is compatible with the material DogeLib takes from other projects.
DogeLib does not accept external contributions until the licence and contributor terms are recorded here.

## Material from other projects

Code, proofs, data or text taken from another project keeps its own licence and notices.

- Mark where the material starts and ends, and name its project, commit and licence.
  For a whole adapted file, the module docstring says so.
- Do not remove or reword an upstream notice.
- Keep a copy of each upstream licence that requires one in `LICENSES/`, and state what the adaptation changed.
- Say in the pull request where the material comes from and under which licence.

Material under one of these licences can ship without a further check:

| Licence | Examples in DogeLib |
| --- | --- |
| Public domain | NIST CAVP test vectors |
| CC0 1.0 | EthLib |
| MIT | Values from Dogecoin Core's tests and chain parameters |
| BSD 2-clause or 3-clause | None yet |
| Apache 2.0 | btc-verified |

Each can accompany MIT-licensed material, provided DogeLib meets every condition of its licence.
For Apache 2.0, they include a copy of the licence, a change statement in each modified file, and any upstream `NOTICE` attributions.
The material keeps its own licence. It does not become MIT-licensed.
Material under any other licence, or with no licence, needs a maintainer's decision first.
If its licence is not compatible, the maintainer can direct a clean-room reimplementation, and decides its process separately.

A definition or proof adapted from a Bitcoin-family project is evidence to investigate, not a compatibility proof for Dogecoin.
Audit each one against Dogecoin's rules.
