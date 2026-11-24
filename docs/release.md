# Releases

This checklist says how to cut a DogeLib release.
A release identifies one commit of `main`, the evidence for it, and the pins it depends on.
The maintainer decides when to release and creates the tag.
[ROADMAP.md](../ROADMAP.md#next-work) lists open work that a release does not wait for.

## 1. Choose the release-candidate commit

1. Select a commit on `main` whose `ci` and `core` workflows passed.
2. Make sure that [COVERAGE.md](../COVERAGE.md), [SOUNDNESS.md](../SOUNDNESS.md), [README.md](../README.md) and the [release notes](#4-write-the-release-notes) describe that commit.
   A documentation fix is a normal pull request, and it gives a new candidate commit.
3. Do not merge other pull requests until the release is tagged, or choose a new candidate after the merge.

## 2. Run the validation workflow

The `validation` workflow runs the gates that `scripts/release_gates.json` lists under `run`, in that order, including both Rust gates and both Core comparisons.
The manifest lists the automated gates of the [checks table](../AGENTS.md#checks) that a GitHub runner can run.
The report marks each other gate **not run**, with the reason from the manifest.
The workflow keeps the report and logs ([BUILDING.md](../BUILDING.md#validation-reports)).
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
   Every gate that the workflow runs must pass, or the release waits for a fix.
   The report records two kinds of gate as **not run**.
   The two manual gates are source and coverage review, and soundness review.
   A reviewer does these two reviews on the candidate commit.
   The other gates under `not_run` need the maintainer's node, a regtest node, or more time than the workflow has.
   They run outside the workflow, on a contributor's machine, with `scripts/validation_report.py --gates`.
   Record the result of each gate that ran with the release.
   Name each gate that did not run.

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

## 4. Write the release notes

The release notes are a committed file, `docs/release-notes/<version>.md`, such as [0.1.0](release-notes/0.1.0.md).
Write them before you choose the candidate, in the documentation pull request of step 1, so that the candidate commit contains them.
Do not write the candidate's own hash into the notes. The tag and the validation report identify it.

List the merged pull requests since the previous release, or all of them for 0.1.0:

```bash
gh pr list --state merged --limit 200 --json number,title,mergedAt
```

Group the entries by layer, and link each capability to its row in [COVERAGE.md](../COVERAGE.md#operations).
Name each breaking change, from the titles with `!`.
State the boundaries of the release, as the [status in README.md](../README.md#status) gives them.
For example, DogeLib does not specify `ConnectBlock` on testnet and regtest, or chain selection.
Check the notes with the writing checker:

```bash
uv run --no-project --python 3.12 python scripts/check_writing.py docs/release-notes/<version>.md
```

## 5. Tag and publish

The maintainer does these steps:

1. Create an annotated tag on the candidate commit, and push it:

   ```bash
   git tag -a v<version> <candidate> -m "DogeLib <version>"
   git push origin v<version>
   ```

   A tag push starts the `validation` workflow again, on the tag.
   Keep that report with the release as well.
2. Pack the downloaded report and logs, and publish the release with the notes and that archive:

   ```bash
   tar -czf build/release/validation-<candidate>.tar.gz -C build/release validation-<candidate>
   gh release create v<version> --title "DogeLib <version>" --notes-file docs/release-notes/<version>.md build/release/validation-<candidate>.tar.gz
   ```

For 0.x releases, [docs/oracle.md](oracle.md#format-stability) records the oracle compatibility policy for outside consumers.
