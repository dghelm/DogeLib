# Releases

This checklist says how to cut a DogeLib release, starting with 0.1.0.
A release identifies one commit of `main`, the evidence for it, and the pins it depends on.
The maintainer decides when to release and creates the tag.

0.1.0 releases the capabilities that are complete on `main`.
[ROADMAP.md](../ROADMAP.md#next-work) lists the work that the release does not wait for.

## 1. Choose the release-candidate commit

1. Select a commit on `main` whose `ci` and `core` workflows passed.
2. Make sure that [COVERAGE.md](../COVERAGE.md), [SOUNDNESS.md](../SOUNDNESS.md) and [README.md](../README.md) describe that commit.
   A documentation fix is a normal pull request, and it gives a new candidate commit.
3. Do not merge other pull requests until the release is tagged, or choose a new candidate after the merge.

## 2. Run the validation workflow

The `validation` workflow runs every automated gate of the [checks table](../AGENTS.md#checks), including both Rust gates and both Core comparisons.
It keeps the report and logs ([BUILDING.md](../BUILDING.md#validation-reports)).
A manual dispatch runs on the head of a branch, not on an arbitrary commit.

1. Make sure that `main` is at the candidate commit:

   ```bash
   git fetch origin && git rev-parse origin/main
   ```

2. Start the workflow on `main`:

   ```bash
   gh workflow run validation.yml --ref main
   ```

3. Wait for the run, and make sure that its head commit is the candidate:

   ```bash
   gh run list --workflow validation.yml --limit 1 --json databaseId,headSha,status,conclusion
   gh run watch <run-id>
   ```

4. Download the artifact `validation-<candidate>`, with the full commit hash, which contains the report and the log directory:

   ```bash
   gh run download <run-id> --name validation-<candidate> --dir build/release/validation-<candidate>
   ```

5. Read the report.
   Every automated gate must pass, or the release waits for a fix.
   The report records only the two manual gates as **not run**: source and coverage review, and soundness review.
   A reviewer does these two reviews on the candidate commit.
   Record their results with the release.

Keep the report and the complete logs with the release.
Do not commit them. The `build/` directory is ignored.

## 3. Record the revisions

The release notes record these revisions.
The report header gives the first three:

- The DogeLib commit.
- The Lean toolchain, from `lean-toolchain`.
- The Dogecoin Core compatibility target, from [SOURCES.md](../SOURCES.md): `v1.14.9`, commit `e0a1c15`.
- The pins of the refinement package: its `lean-toolchain`, Aeneas, Charon and the Rust toolchain, from [SOURCES.md](../SOURCES.md) and [Refinement/Rust/README.md](../Refinement/Rust/README.md).
- The oracle format name, from [docs/oracle.md](oracle.md).

## 4. Write the changelog

Write the changelog as the release notes, in `build/release/release-notes.md`.
Start from the squash-merge titles on `main` since the previous release, or since the first commit for 0.1.0:

```bash
git log --format='%s' <previous-tag>..<candidate>
```

Group the entries by layer, and link each capability to its row in [COVERAGE.md](../COVERAGE.md#operations).
Name each breaking change, from the titles with `!`.
State the boundaries of the release, as the [status in README.md](../README.md#status) gives them.
For example, DogeLib has no ECDSA backend, and it does not specify scrypt or AuxPoW.
Check the notes with the writing checker:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py --stdin description < build/release/release-notes.md
```

## 5. Tag and publish

The maintainer does these steps:

1. Create an annotated tag on the candidate commit, and push it:

   ```bash
   git tag -a v0.1.0 <candidate> -m "DogeLib 0.1.0"
   git push origin v0.1.0
   ```

   A tag push starts the `validation` workflow again, on the tag.
   Keep that report with the release as well.
2. Pack the downloaded report and logs, and publish the release with the notes and that archive:

   ```bash
   tar -czf build/release/validation-<candidate>.tar.gz -C build/release validation-<candidate>
   gh release create v0.1.0 --title "DogeLib 0.1.0" --notes-file build/release/release-notes.md build/release/validation-<candidate>.tar.gz
   ```

At and after 0.1.0, the maintainer sets the compatibility policy for outside consumers of the oracle ([format stability](oracle.md#format-stability)).
