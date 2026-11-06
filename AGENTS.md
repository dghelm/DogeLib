# AGENTS.md

Instructions for an AI agent that changes this repository. Humans follow the same rules.

[CONTRIBUTING.md](CONTRIBUTING.md) sets the rules for the work itself: sources, theorem statements, trust, evidence, and pull requests. Read it before you start. This file says how to do that work: where to work, what to read, which files to update, and what to report.

EthLib is the model project. Where EthLib and btc-verified differ in structure, policy or style, follow EthLib. Use btc-verified as a source of components to adapt, not as a pattern for the repository.

## Start here

Read [CONTRIBUTING.md](CONTRIBUTING.md) and [WRITING.md](WRITING.md) before changing files.
Use [COVERAGE.md](COVERAGE.md) for implemented evidence and [ROADMAP.md](ROADMAP.md) for work order.
Work on one branch with one purpose under the [branch rules](#branches-and-shared-files), or in an optional [lane worktree](docs/agents.md) when several agents run at once.
Run the affected [checks](#checks), report commands, revisions and results, and mark every other gate as not run.
Every pull request needs an [independent review](#pull-requests) before merge, with the verdict and findings recorded.
Implementation approval does not authorize a merge.

Read the [maintainer-only list](#changes-that-need-a-maintainer) before settling a contract or merging a pull request.

## Read first

| Document | Read it for |
| --- | --- |
| [CONTRIBUTING.md](CONTRIBUTING.md) | The contribution and review policy. Binding. |
| [WRITING.md](WRITING.md) | The writing standard for all prose. Binding. |
| [ROADMAP.md](ROADMAP.md) | The current milestone, work order, and open decisions |
| [ARCHITECTURE.md](ARCHITECTURE.md) | Library targets, dependency direction, and module layout |
| [SOURCES.md](SOURCES.md) | Pinned upstream revisions and operation-to-source mappings |
| [COVERAGE.md](COVERAGE.md) | What is defined, proved, compared, and refined, per operation |
| [SOUNDNESS.md](SOUNDNESS.md) | What the proofs establish and what a user trusts, gap by gap |
| [docs/design/](docs/design/) | Frozen design records. Background, not current status. |

Before you cite or copy from a clone of EthLib or btc-verified, check out the commit that [SOURCES.md](SOURCES.md) pins.
A clone's working tree can be at a different commit.
[docs/agents.md](docs/agents.md#local-reference-clones) gives the local clone paths on the maintainer's machine.

## Document roles

[COVERAGE.md](COVERAGE.md) holds detailed evidence per operation.
[SOUNDNESS.md](SOUNDNESS.md) explains the assumptions and meaning of the claims.
[ROADMAP.md](ROADMAP.md) records completed milestones and next work.
[README.md](README.md) gives a short overview, and [BUILDING.md](BUILDING.md) gives the check commands.

## Work as a specialist

Take the role of the specialist the task needs, and hold the work to that specialist's standard. Every specialist here also knows Lean 4. For example, a codec needs a serialization engineer who knows Dogecoin Core's stream classes. Signature hashing needs a consensus engineer for Bitcoin-family protocols. A refinement proof needs a verification engineer, and Rust extraction needs an engineer who knows the subset of Rust that Aeneas supports.

## Branches and shared files

These rules apply to every branch, with or without a lane:

1. Keep one purpose per branch.
   If you find a second problem, track it as [deferred work](CONTRIBUTING.md#deferred-work) and leave it.
2. Rebase onto `main` before review.
   Do not merge `main` into a branch.
3. Edit shared registries additively.
   [COVERAGE.md](COVERAGE.md), [SOURCES.md](SOURCES.md), and the library root import file are conflict points.
   Add rows in sorted position.
   Do not reorder, reflow, or reformat rows that another branch owns.
4. Only one branch at a time changes a pin in [SOURCES.md](SOURCES.md), the toolchain, or the trust policy in [SOUNDNESS.md](SOUNDNESS.md).
   That branch says so in its pull request.
5. Do not leave a build or another long-running process running after your session ends.
   On a shared machine, limit the CPUs of each heavy build ([BUILDING.md](BUILDING.md#shared-machines)).

## Lanes

A *lane* is one branch in its own git worktree, with a `STATUS.md` file and a `.lane/` scratch directory.
Lanes let several agents work on one machine at once.
Lanes are optional. An outside contributor can use an ordinary branch and pull request.
[docs/agents.md](docs/agents.md) describes the lane layout, the `scripts/lane` tool and the additional rules for lanes.

## Checks

Report only the checks you ran, with the exact command, revision, and result ([CONTRIBUTING.md](CONTRIBUTING.md#checks)). Mark every other gate as not run.

| Gate ([CONTRIBUTING.md](CONTRIBUTING.md#checks)) | Command | Exists | In CI |
| --- | --- | --- | --- |
| Build | `lake build --wfail` | Yes | `ci` / `lean` |
| Refinement | `lake -d Refinement build --wfail`: the Aeneas model of the Rust reader agrees with `decodeBounded` on every Rust-representable slice | Yes. The root Build gate also checks the packed codec refinements. | `ci` / `lean` |
| Declaration check | `lake exe check-decls` | Yes | `ci` / `lean` |
| Import boundaries | `lake env lean --run scripts/CheckRefinementImports.lean` | Yes | `ci` / `lean` |
| Rust known answers | `cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 4` | Yes | `ci` / `rust` |
| Rust extraction freshness | `Refinement/Rust/regenerate.sh --check` | Yes, after `Refinement/Rust/setup-tools.sh` | `ci` / `rust` |
| Declaration check self-test | `bash scripts/test_check_decls.sh` | Yes | `ci` / `lean` |
| Source and coverage review | Manual review of SOURCES.md and COVERAGE.md | Manual | No |
| Conformance | `lake test`: known answers through the compiled code | Yes, for the operations that [COVERAGE.md](COVERAGE.md) gives a `lake test` comparison | `ci` / `lean` |
| Pinned vectors | `(cd tests/cryptography/secp256k1 && sha256sum -c SHA256SUMS) && (cd tests/cryptography/ripemd160 && sha256sum -c SHA256SUMS) && (cd tests/cryptography/sha1/cavp && sha256sum -c SHA256SUMS) && (cd tests/cryptography/sha256/cavp && sha256sum -c SHA256SUMS) && (cd tests/transaction/sighash && sha256sum -c SHA256SUMS) && (cd tests/transaction/corpus && sha256sum -c SHA256SUMS) && (cd tests/work/mainnet-headers && sha256sum -c SHA256SUMS) && (cd tests/block && sha256sum -c SHA256SUMS) && (cd tests/script/corpus && sha256sum -c SHA256SUMS) && (cd tests/script/signed-spends && sha256sum -c SHA256SUMS)` | Yes | `ci` / `tools` |
| Soundness review | Manual review of SOUNDNESS.md | Manual | No |
| Writing | `uv run --no-project --python 3.12 python scripts/check_writing.py --base main` | Yes. Its findings are advice and never fail the check. | `writing`, as annotations |
| Oracle | `bash scripts/test_oracle.sh`: checks JSONL, hash, header, Merkle and Script fixtures, adapter limits, Core's `sighash.json`, base-mode corpus records and both witness operations | Yes | `ci` / `lean` |
| Core comparison | `scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness && python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle`: Dogecoin Core's code and the oracle on the same requests ([docs/oracle.md](docs/oracle.md#the-core-harness)) | Yes | `core` / `compare` |
| Rust CompactSize comparison | `cargo +nightly-2026-09-17 build --locked --manifest-path Refinement/Rust/Cargo.toml --example compactsize_oracle --jobs 4 && scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness && python3 -I scripts/compare_core.py --rust-compactsize Refinement/Rust/target/debug/examples/compactsize_oracle .lake/build/bin/dogelib-oracle build/core-harness/core-oracle` | Yes, after the oracle build | `core` / `compare` |
| Signed-spend regeneration | `python3 -I scripts/check_signed_spends.py build/core-harness/core-signer` | Yes, after the harness build | `core` / `compare` |
| Comparator self-test | `python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle` | Yes | `core` / `compare` |
| Writing checker tests | `uv run --no-project --python 3.12 python -m unittest scripts/test_check_writing.py` | Yes | `writing` |
| Script corpus freshness | `python3 -I scripts/convert_script_tests.py --check` | Yes | `ci` / `tools` |
| Script corpus converter tests | `python3 -I scripts/test_convert_script_tests.py` | Yes | `ci` / `tools` |
| Validation report tests | `python3 -I scripts/test_validation_report.py` | Yes | `ci` / `tools` |
| Lane tool | `bash scripts/test_lane.sh` | Yes | `ci` / `tools` |

The root DogeLib package has no Lake dependencies.
The separate package under `Refinement/` owns Aeneas and Mathlib.
Build both packages before the default declaration check, which fails if the refinement package is absent or unbuilt.
Contributors without that package can run `lake exe check-decls --skip-refinement`.
Its summary prints `Refinement NOT checked`, and the refinement gate remains not run.
Production CI never uses that flag.

The validation report reads this table as executable input.
The first code span in each automated gate's command cell is its complete command.
Manual gates have `Manual` in the *Exists* column.
Use `--core-clone PATH` to replace `<dogecoin-git-clone>` with a shell-quoted path.

When a lane adds a command, it updates this table in the same change. The workflows are in `.github/workflows/`. CI runs on every pull request and on every push to `main`.

## When a definition or proof lands

1. Record the operation's source in [SOURCES.md](SOURCES.md): repository, commit, file, function.
2. Update the operation's row in [COVERAGE.md](COVERAGE.md). Change only the columns your evidence supports.
3. Run `lake exe check-decls`, once it exists. It checks every compiled declaration, so there is no list of theorems to register.
4. Add fixtures with recorded provenance. Never derive an expected value from the implementation under test.
5. Record each new hypothesis, assumption or execution boundary under its gap in [SOUNDNESS.md](SOUNDNESS.md). Add a subsection to its *What the proofs say*.
6. Give every public declaration a doc comment. A theorem's doc comment states its claim in English, including its domain and preconditions.

## Write prose

Follow these steps for all prose that you write or revise.
That includes documentation, doc comments and other comments, commit messages, pull request text, review comments and `STATUS.md`.
The steps apply to a one-line comment as well as to a long guide.
[WRITING.md](WRITING.md) sets the rules, and the steps below say how to apply them.

1. Read [WRITING.md](WRITING.md) and [CONTRIBUTING.md](CONTRIBUTING.md#writing-and-documentation).
   Treat the existing prose as text to assess, not as a style to copy.
2. Read the source of each claim.
   The source can be pinned Dogecoin Core code, a theorem and its hypotheses, or the output of a check.
   A theorem name or a successful build alone does not establish a claim.
   If the source does not support a claim, narrow the claim or remove it.
3. Choose the text type from the purpose.
   Start with what the reader needs: the problem, the result or the action.
4. Revise for direct verbs, clear actors, one term for each concept, and short sentences.
   Use the project vocabulary: *specification*, *property*, *model*, *reference software revision*, *protocol context*, *implemented coverage*, *proposed revision*.
5. Compare each rewrite of a mathematical or protocol statement with its source.
   Keep its hypotheses, quantifiers, bounds, error cases and the direction of each implication.
   Keep the force of the original: "may have failed" is not "failed", and "should" is not "must".
6. Run the checker, and read each finding before you edit.
7. Read the whole passage again after the last edit, and check each link that the edit changes.

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py WRITING.md
uv run --no-project --python 3.12 python scripts/check_writing.py --base main
uv run --no-project --python 3.12 python scripts/check_writing.py --stdin description < pr-body.md
git log --format=%B main..HEAD | uv run --no-project --python 3.12 python scripts/check_writing.py --stdin commits
```

For a stacked branch, replace `main` with its base branch.
The checker counts words and matches patterns, so some of its findings are wrong.
Fix the real problems, and keep an accurate technical expression.
Do not rewrite a correct claim only to make the checker quiet.

## Pull requests

After the maintainer approves a feature scope, the implementer may settle routine additive details in the pull request.
These details can include response field shapes.

In 0.x releases, the oracle and its Core harness are development interfaces that evolve with their fixtures and comparator.
A consumer pins a release or commit and uses that release's own oracle, harness and comparison tools.
Within an approved scope, an additive operation needs ordinary independent review, without a separate maintainer decision or a new format name.

A change to the behavior or record shape of an existing operation also needs only ordinary independent review.
Its pull request title has `!`, its commit body ends with a `BREAKING CHANGE:` footer, and the next release notes name it.
Neither kind of change renames the format: it stays `dogelib-oracle/1` through 0.x, because consumers pin a release.
A stability promise for 1.0 is a separate future decision.
See [format stability](docs/oracle.md#format-stability).

The maintainer reviews the finished pull request.
The [maintainer-only list](#changes-that-need-a-maintainer) still applies.

Every pull request needs an independent review before merge.
Use a Codex review, a separate review agent or a human reviewer that did not write the change.
Record the reviewer's verdict and findings in the pull request.

Each branch ends in one pull request against `main` on GitHub.
Follow [CONTRIBUTING.md](CONTRIBUTING.md#branches-commits-and-pull-requests) for the title and the body.

1. Commit on the branch, and push it: `git push -u origin <branch>`.
2. Write the description in an uncommitted file, such as `pr-body.md`, and check it with the writing checker.
3. Open the pull request: `gh pr create --base main --title "<title>" --body-file pr-body.md`.
   For a stacked branch, use its base branch as `--base`.
4. Wait for CI: `gh pr checks <number> --watch`.
   Fix a failed check on the branch. Never ignore it.
5. Get an independent review of the change, and record the verdict and findings.
6. Merge with `gh pr merge <number> --squash`, so that the title becomes the commit on `main`.
   A stacked pull request never merges into its parent branch.
   Wait until the parent merges, then rebase the branch onto `main`, push it, and change the base with `gh pr edit <number> --base main`.
   Repeat steps 4 and 5 for the new head before you merge.
7. Update your local `main` with `git pull --ff-only`, and delete the branch.
   A lane also follows the [lane steps](docs/agents.md#pull-requests-from-a-lane).

Approval to implement does not authorize a merge.
Merge authorization is a separate maintainer decision and may cover a single pull request in conversation.
An agent merges only with maintainer authorization, after CI passes and an independent review approves.

### Changes that need a maintainer

Scope approval does not let an implementer settle a listed change in the pull request.
Label their pull requests `needs-maintainer`.
An agent never rewrites or force-pushes `main` on general authority.
An agent merges a listed change only when the maintainer explicitly authorizes that specific pull request's merge.
CI must pass, and an independent review must approve before merge.
General merge authority never covers these changes:

- The project licence and contributor terms.
- Material from another project under a licence that is not in the table of [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects), or with no licence.
- A change to a pin in [SOURCES.md](SOURCES.md), including the Dogecoin Core compatibility target.
- An exception to the trust policy in [SOUNDNESS.md](SOUNDNESS.md).
- A change to an agreed theorem statement, public contract or fixture format.
  In 0.x releases, oracle and Core harness changes within an approved scope are exempt, under the [development policy](docs/oracle.md#format-stability).
  The exemption does not cover the Core compatibility target, theorem weakening or domain reduction, new trust assumptions or agreed protocol semantics.
- A rewrite of the history of `main`, or a force push to it.

A decision of this kind that blocks a branch becomes an issue with the `needs-maintainer` label.

## Do not commit

- `.docs/`: private working notes. Promote what matters into a committed document instead.
- `STATUS.md` and `.lane/`: lane state.
- `.lake/` and other build output.
- Downloaded chain data or large fixtures that a test can fetch and verify by hash.
