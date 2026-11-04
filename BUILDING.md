# Building DogeLib

DogeLib needs [elan](https://github.com/leanprover/elan), which installs the Lean toolchain that `lean-toolchain` pins, `v4.35.0`.
The package has no dependencies beyond Lean core, so no Mathlib cache is needed.

## Build and check

```bash
lake build --wfail
lake exe check-decls
lake test
bash scripts/test_oracle.sh
```

`lake build --wfail` compiles the specification and checks every proof.
An unfinished proof only warns, so `--wfail` turns every warning into an error.

`lake exe check-decls` reads the compiled declarations of the `DogeLib`, `Proofs` and `Exports` libraries.
It requires every `.lean` file under `DogeLib/`, and `DogeLib.lean`, to be reachable from those roots.
It names each unreachable module and fails the check.

It reports any axiom beyond `propext`, `Classical.choice` and `Quot.sound` in the transitive dependencies of safe declarations.
Unsafe declarations are reported as `unsafe` findings.
It also reports any `partial`, `opaque`, `@[extern]`, `@[implemented_by]` or `@[csimp]` declaration.
It also reports a specification definition that reaches an opaque constant, so that the kernel cannot unfold it.

`scripts/check_decls_baseline.txt` lists the findings that exist today.
It is empty, and a new finding is fixed, never added to it.

`lake test` runs known answers through the compiled code.
Four directories hold vendored files, each with a README that gives their provenance:

- `tests/cryptography/sha256/cavp/`: the NIST CAVP vectors, for SHA-256.
- `tests/transaction/sighash/`: Dogecoin Core's signature-hash corpus, for the legacy signature hash.
- `tests/transaction/corpus/`: Dogecoin Core's transaction corpus, for the base-mode reader and codecs and the witness-allowed format.
- `tests/work/mainnet-headers/`: public mainnet headers, for next-work selection across DigiShield activation.

The other known answers, and their provenance, are in `tests/KnownAnswers.lean`.

`bash scripts/test_oracle.sh` builds the oracle, `dogelib-oracle`, and tests it through its standard input and output.
It needs Python 3.10 or later, with only the standard library.
[docs/oracle.md](docs/oracle.md) defines the oracle's record format, and `tests/oracle/README.md` gives the provenance of its fixtures.
Dogecoin Core's own test cases test the compact target encoding and the difficulty retarget.
`tests/KnownAnswers.lean` gives the file and line of each case.

## Comparison with Dogecoin Core

The comparison runs Dogecoin Core's own code on the oracle's requests ([docs/oracle.md](docs/oracle.md#the-core-harness)).
It needs a git clone of Dogecoin Core that contains the pinned commit, and autoconf, automake, libtool, pkg-config and OpenSSL's development files.

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle
python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The build script uses `JOBS` parallel jobs, 8 by default.
It reuses the Core libraries when the build directory's stamp matches the pin, the script, the compilers and the flags.
A first build takes under a minute on 8 cores, and the comparison takes about 20 seconds.

## The declaration check

After a change to the check itself, run its self-test:

```bash
bash scripts/test_check_decls.sh
```

It builds the fixtures in `scripts/CheckDeclsTest`, which contain `sorry` and every other finding on purpose.
The check must report each planted finding and nothing else, pass with a baseline that lists them, and fail on a stale baseline entry.
An isolated fixture requires rejection of an imported unfinished proof.
The self-test also plants an unimported production file and requires a failure that names its module.

## Module boundaries

DogeLib uses the module system of Lean v4.35.0, as EthLib does.
A definition file has this shape:

```lean
module

public import DogeLib.Cryptography.Hash.Sha256

/-! A module docstring. -/

@[expose] public section

-- Definitions and theorems.
```

A public import keeps the names that clients receive through the library roots.
An exposed definition keeps its body visible, so that the reductions client proofs rely on still work.
The proof of a theorem stays private, even inside an exposed section.
EthLib's [`BUILDING.md`](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/BUILDING.md) explains the reasons in more detail.

## A new layer

A new layer under `DogeLib/<Layer>/` needs two root files:

- `DogeLib/<Layer>.lean` imports the layer's specification modules, and `DogeLib.lean` imports it.
- `DogeLib/<Layer>/Proofs.lean` imports the layer's proof modules, and `DogeLib/Proofs.lean` imports it.

Then add `` `DogeLib.<Layer>.Proofs `` to the `roots` of the `Proofs` library in `lakefile.lean`, so that its modules belong to that library.

## Shared machines

Lake v4.35.0 has no option to limit its parallel jobs.
On a machine that other builds share, limit the CPUs of the process instead:

```bash
taskset -c 0-7 nice -n 19 lake build --wfail
```

## Transaction reader benchmark

The benchmark compares `Transaction.readBase` with `Transaction.readBaseSlice` on generated base-mode transactions.
It is an optional executable and does not run in CI or the default build.
Run it on cores 4 to 7, at nice level 10:

```bash
taskset -c 4-7 nice -n 10 lake build bench-transaction-reader
taskset -c 4-7 nice -n 10 .lake/build/bin/bench-transaction-reader
```

The workloads have 500, 1000, 2000, 4000 or 8000 inputs, outputs or bytes per script:

- The input workload has empty scripts and one output.
- The output workload has empty scripts and one input.
- The script workload has one empty-script input and four outputs with scripts of the stated length.

Each point warms the reader once, then reports five parse times and their median in nanoseconds.
Generation and conversion to a list or slice occur before the timer starts.
The timer includes a result check and the lengths of the returned input and output lists.
The benchmark measures successful parsing, without a theorem about runtime cost.

Four shared cores and nice level 10 make absolute times noisy, so compare growth ratios.
Generated bytes measure cost and do not supply independent conformance evidence.
To inspect larger input workloads with the slice reader alone, run:

```bash
taskset -c 4-7 nice -n 10 .lake/build/bin/bench-transaction-reader --slice-large
```

This command measures 4000, 8000, 16000 and 32000 empty-script inputs.

## Validation reports

Produce a report of all automated gates in the [AGENTS.md checks table](AGENTS.md#checks):

```bash
python3 -I scripts/validation_report.py --core-clone <dogecoin-git-clone>
```

The runner needs Python 3.10 or later and only the standard library.
Install the tools required by the selected gates, including `uv` for the writing checks.
On a shared machine, prefix the command with `taskset -c 0-7 nice -n 19`.
The gates run one at a time from the repository root.
The runner executes the table's commands with Bash, so review table edits as code.

The default output is `build/validation/<commit>/report.md`, with the commit shortened to 12 characters.
Use `--output .lane/validation/report.md` to choose another ignored destination.
Each report has an adjacent log directory, which must not exist before the run.
Keep the report and its logs together, and do not commit them.

List the gate names and commands, or select gates by their names:

```bash
python3 -I scripts/validation_report.py --list
python3 -I scripts/validation_report.py --gates build,declaration-check --output .lane/subset/report.md
```

Every gate that the runner skips is **not run**, including manual reviews and the Core comparison without `--core-clone`.
The runner shell-quotes the Core clone path before it replaces the table's placeholder.
Any remaining placeholder also leaves the gate **not run**.
A failed gate does not stop later gates, but makes the runner exit with status 1.

The report records a gate as running before its launch, then records the completed result.
A hard kill can leave a gate marked running/incomplete.
An interrupt stops the gate's process group and records its partial output.
The Writing gate is advisory, and its findings can accompany a zero exit status.

The header records the commit, tree status, toolchain, compiler versions, Core pin, Core stamp, platform and UTC date.
A dirty tree has a warning on the first line, a status log and a separate tracked diff.
The status log lists untracked files, but the diff does not contain their contents.
The runner also saves the final status and tracked diff, and notes a change in tree status.

Each gate records its exact command, exit status, duration, final output lines and full log path.
The Core stamp records existing libraries.
The Core result records whether the harness step and comparison succeeded, possibly with reuse of existing libraries.

The `validation` workflow runs on manual dispatch and tag pushes, and uploads the report and logs even after gate failures.
A report records checks on one machine at one commit.
It is not a proof, and CI results on other commits are separate evidence.
