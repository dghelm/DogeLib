# Running several agents at once

This guide is operational.
It says how to run several agents, or several people, on one machine without interference.
A single contributor does not need it: use an ordinary branch and pull request, as [AGENTS.md](../AGENTS.md#pull-requests) says.

The binding rules stay in [CONTRIBUTING.md](../CONTRIBUTING.md), [WRITING.md](../WRITING.md) and [AGENTS.md](../AGENTS.md).
This guide adds no rule that a pull request must satisfy.

## Lanes

A *lane* is one unit of parallel work: one purpose, one branch, one git worktree, one `STATUS.md`.
Lanes keep concurrent agents from sharing a working tree, a build directory, or a scratch file.

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

The main checkout is for coordination and integration.
Do not edit files or run builds in it while lanes are active.

### Commands

```bash
scripts/lane new feat/compactsize-bounded-reader   # branch from main, create worktree and STATUS.md
scripts/lane new proof/compactsize-bounds --base feat/compactsize-bounded-reader   # stacked lane
scripts/lane list                                  # every lane: state, dirty files, ahead/behind main
scripts/lane rm feat-compactsize-bounded-reader    # archive lane files, remove the clean worktree
```

The branch name is `<type>/<slug>`, using a commit type from [CONTRIBUTING.md](../CONTRIBUTING.md#titles).
The worktree directory replaces the `/` with `-`.
Set `DOGELIB_LANES_DIR` to use a different parent directory.

`scripts/lane rm` refuses a worktree with uncommitted changes.
It deletes the branch only when git considers it merged into `main`.
A squash-merged branch is not an ancestor of `main`, so the script keeps it and prints the command to delete it.

### Rules for lanes

These rules apply when you work in a lane.
They add to the binding rules of [AGENTS.md](../AGENTS.md#branches-and-shared-files):

1. Work only inside your lane's worktree.
   Do not touch another lane's files, branch, or build.
2. Keep one purpose per lane.
   If you find a second problem, record it under *Deferred* in `STATUS.md` and leave it.
3. Put every lane artifact in `.lane/`: handoff documents, review transcripts, build and test logs, scratch notes.
   Do not write them next to the repository, in the main checkout, or in a committed path.
4. Keep `STATUS.md` current.
   Update it when the state changes, before you stop, and before a handoff.
   Another agent must be able to continue from it alone.
5. Register every long-running process in `STATUS.md` under *Running jobs*: PID, command, log path under `.lane/`, start time.
   Remove the entry when the process ends.
   Never detach a build with `nohup`, `setsid`, or `&` so that it outlives the session.
6. Run one heavy build per lane at a time, and limit its CPUs on a shared machine ([shared machines](#shared-machines)).
   Each worktree has its own `.lake/` directory.
   Before you build the optional refinement package in a new worktree, run `lake -d Refinement exe cache get`.
7. A lane can change a pin in [SOURCES.md](../SOURCES.md), the toolchain, or the trust policy.
   Then it says so in its `STATUS.md`, as well as in its pull request.

### `STATUS.md`

`scripts/lane new` writes the template.
Its *State* line is one of: `active`, `blocked`, `review`, `ready`, `merged`, `abandoned`.
`scripts/lane list` reads that line.

### Pull requests from a lane

A lane follows the pull request steps of [AGENTS.md](../AGENTS.md#pull-requests), with these additions:

1. Write the pull request description in `.lane/pr-body.md`.
2. Record the pull request number and its state in `STATUS.md`.
3. After the merge, update the main checkout with `git pull --ff-only`, and remove the lane with `scripts/lane rm`.

## Add known answers

Add test functions and named checks to the appropriate topic module under `tests/KnownAnswers/`.
Keep its check list in alphabetical order.
The driver sums the failure counts from every topic list.
A check in an existing topic needs no change to the driver.

For a separate topic, add a module with its own named check list.
Add its import and list entry to `tests/KnownAnswers.lean`, in alphabetical order.
Put shared fixture readers in `tests/KnownAnswers/Common.lean`.
Keep expected values and their provenance with the test functions.

## Shared machines

On a machine that other builds share, limit the CPUs of each heavy process.
Lake v4.35.0 has no option to limit its parallel jobs, so use `taskset` ([BUILDING.md](../BUILDING.md#shared-machines)):

```bash
taskset -c 0-7 nice -n 19 lake build --wfail
```

Pass `--jobs 4` or a similar limit to `cargo`.

## Local reference clones

These local clones of the reference projects exist on the maintainer's machine:

- EthLib: `/home/dgh/dev/ethereum/EthLib`
- btc-verified: `/home/dgh/dev/ProofOfKeags/btc-verified`

On another machine, clone the projects from the URLs in [SOURCES.md](../SOURCES.md).
A clone's working tree can be at a different commit from the pin.
Before you cite or copy from a clone, check out the commit that [SOURCES.md](../SOURCES.md) pins.
