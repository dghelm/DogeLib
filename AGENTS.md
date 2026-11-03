# AGENTS.md

Instructions for an AI agent that changes this repository. Humans follow the same rules.

[CONTRIBUTING.md](CONTRIBUTING.md) sets the rules for the work itself: sources, theorem statements, trust, evidence, and pull requests. Read it before you start. This file says how to do that work: where to work, what to read, which files to update, and what to report.

EthLib is the model project. Where EthLib and btc-verified differ in structure, policy or style, follow EthLib. Use btc-verified as a source of components to adapt, not as a pattern for the repository.

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

Local reference clones, when present on the machine:

- EthLib: `/home/dgh/dev/ethereum/EthLib`
- btc-verified: `/home/dgh/dev/ProofOfKeags/btc-verified`

Use the commit pinned in [SOURCES.md](SOURCES.md) before you cite or copy from a clone. A clone's working tree can be at a different commit.

## Current state

The build skeleton exists: Lean `v4.35.0`, the `DogeLib` and `Proofs` libraries, and `lake exe check-decls`. [COVERAGE.md](COVERAGE.md) lists the operations that exist, [BUILDING.md](BUILDING.md) gives the commands, and [ROADMAP.md](ROADMAP.md) gives the next steps.

## Work as a specialist

Take the role of the specialist the task needs, and hold the work to that specialist's standard. Every specialist here also knows Lean 4. For example, a codec needs a serialization engineer who knows Dogecoin Core's stream classes. Signature hashing needs a consensus engineer for Bitcoin-family protocols. A refinement proof needs a verification engineer, and Rust extraction needs an engineer who knows the subset of Rust that Aeneas supports.

## Lanes

A *lane* is one unit of parallel work: one purpose, one branch, one git worktree, one `STATUS.md`. Lanes keep concurrent agents from sharing a working tree, a build directory, or a scratch file.

### Layout

```text
DogeLib/                      main checkout; stays on `main` and stays clean
DogeLib-worktrees/
  feat-compactsize-bounded-reader/
    STATUS.md                 lane state (gitignored)
    .lane/                    lane scratch: handoffs, logs, review output (gitignored)
    ...                       an ordinary checkout of the lane branch
  .archive/                   STATUS.md and .lane/ of removed lanes
```

The main checkout is for coordination and integration. Do not edit files or run builds in it while lanes are active.

### Commands

```bash
scripts/lane new feat/compactsize-bounded-reader   # branch from main, create worktree and STATUS.md
scripts/lane new proof/compactsize-bounds --base feat/compactsize-bounded-reader   # stacked lane
scripts/lane list                                  # every lane: state, dirty files, ahead/behind main
scripts/lane rm feat-compactsize-bounded-reader    # archive lane files, remove the clean worktree
```

The branch name is `<type>/<slug>`, using a commit type from [CONTRIBUTING.md](CONTRIBUTING.md#titles). The worktree directory replaces the `/` with `-`. Set `DOGELIB_LANES_DIR` to use a different parent directory.

`scripts/lane rm` refuses a worktree with uncommitted changes. It deletes the branch only when git considers it merged into `main`. A squash-merged branch is not an ancestor of `main`, so the script keeps it and prints the command to delete it.

### Rules

1. Work only inside your lane's worktree. Do not touch another lane's files, branch, or build.
2. Keep one purpose per lane. If you find a second problem, record it under *Deferred* in `STATUS.md` and leave it.
3. Put every lane artifact in `.lane/`: handoff documents, review transcripts, build and test logs, scratch notes. Do not write them next to the repository, in the main checkout, or in a committed path.
4. Keep `STATUS.md` current. Update it when the state changes, before you stop, and before a handoff. Another agent must be able to continue from it alone.
5. Register every long-running process in `STATUS.md` under *Running jobs*: PID, command, log path under `.lane/`, start time. Remove the entry when the process ends. Never detach a build with `nohup`, `setsid`, or `&` so that it outlives the session.
6. Run one heavy build per lane at a time, and limit its CPUs on a shared machine ([BUILDING.md](BUILDING.md#shared-machines)). Each worktree has its own `.lake/` directory. Once the lakefile requires Mathlib, run `lake exe cache get` before the first build in a new worktree.
7. Rebase onto `main` before review. Do not merge `main` into a lane.
8. Edit shared registries additively. [COVERAGE.md](COVERAGE.md), [SOURCES.md](SOURCES.md), and the library root import file are conflict points. Add rows in sorted position. Do not reorder, reflow, or reformat rows another lane owns.
9. Only one lane at a time changes a pin in [SOURCES.md](SOURCES.md), the toolchain, or the trust policy in [SOUNDNESS.md](SOUNDNESS.md). That lane says so in its `STATUS.md` and pull request.

### `STATUS.md`

`scripts/lane new` writes the template. Its *State* line is one of: `active`, `blocked`, `review`, `ready`, `merged`, `abandoned`. `scripts/lane list` reads that line.

## Checks

Report only the checks you ran, with the exact command, revision, and result ([CONTRIBUTING.md](CONTRIBUTING.md#checks)). Mark every other gate as not run.

| Gate ([CONTRIBUTING.md](CONTRIBUTING.md#checks)) | Command | Exists | In CI |
| --- | --- | --- | --- |
| Build | `lake build --wfail` | Yes | `ci` / `lean` |
| Declaration check | `lake exe check-decls` | Yes | `ci` / `lean` |
| Declaration check self-test | `bash scripts/test_check_decls.sh` | Yes | `ci` / `lean` |
| Source and coverage review | Manual review of SOURCES.md and COVERAGE.md | Manual | No |
| Conformance | `lake test`: known answers through the compiled code | Yes, for SHA-256 and double SHA-256 | `ci` / `lean` |
| Pinned vectors | `sha256sum -c SHA256SUMS` in each vendored vector directory | Yes | `ci` / `tools` |
| Refinement | — | No | No |
| Soundness review | Manual review of SOUNDNESS.md | Manual | No |
| Writing | `uv run --no-project --python 3.12 python scripts/check_writing.py --base main` | Yes. Its findings are advice and never fail the check. | `writing`, as annotations |
| Writing checker tests | `uv run --no-project --python 3.12 python -m unittest scripts/test_check_writing.py` | Yes | `writing` |
| Lane tool | `bash scripts/test_lane.sh` | Yes | `ci` / `tools` |

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
uv run --no-project --python 3.12 python scripts/check_writing.py --stdin description < .lane/description.md
git log --format=%B main..HEAD | uv run --no-project --python 3.12 python scripts/check_writing.py --stdin commits
```

For a stacked lane, replace `main` with the base of the lane.
The checker counts words and matches patterns, so some of its findings are wrong.
Fix the real problems, and keep an accurate technical expression.
Do not rewrite a correct claim only to make the checker quiet.

## Pull requests

Each lane ends in one pull request against `main` on GitHub.
Follow [CONTRIBUTING.md](CONTRIBUTING.md#branches-commits-and-pull-requests) for the title and the body.

1. Commit in the lane, and push its branch: `git push -u origin <branch>`.
2. Write the description in `.lane/pr-body.md`, and check it with the writing checker.
3. Open the pull request: `gh pr create --base main --title "<title>" --body-file .lane/pr-body.md`.
   For a stacked lane, use its base branch as `--base`.
4. Wait for CI: `gh pr checks <number> --watch`.
   A failed check is fixed in the lane, never ignored.
5. Get a review of the change.
6. Merge with `gh pr merge <number> --squash`, so that the title becomes the commit on `main`.
   A stacked pull request never merges into its parent branch.
   Wait until the parent merges, then rebase the lane onto `main`, push it, and change the base with `gh pr edit <number> --base main`.
   Repeat steps 4 and 5 for the new head before you merge.
7. Update the main checkout with `git pull --ff-only`, and remove the lane with `scripts/lane rm`.

An agent merges a pull request only with a maintainer's authorization to merge, and only when CI passes and the review approves.
Record the pull request number and its state in `STATUS.md`.

### Changes that need a maintainer

An agent never merges these, even with authorization to merge.
It opens the pull request, labels it `needs-maintainer`, and continues with other work:

- The project licence and contributor terms.
- Material from another project under a licence that is not in the table of [CONTRIBUTING.md](CONTRIBUTING.md#material-from-other-projects), or with no licence.
- A change to a pin in [SOURCES.md](SOURCES.md), including the Dogecoin Core compatibility target.
- An exception to the trust policy in [SOUNDNESS.md](SOUNDNESS.md).
- A change to an agreed theorem statement, public contract or fixture format.
- A rewrite of the history of `main`, or a force push to it.

A decision of this kind that blocks a lane becomes an issue with the `needs-maintainer` label.

## Do not commit

- `.docs/`: private working notes. Promote what matters into a committed document instead.
- `STATUS.md` and `.lane/`: lane state.
- `.lake/` and other build output.
- Downloaded chain data or large fixtures that a test can fetch and verify by hash.
