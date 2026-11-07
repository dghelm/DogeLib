# Building DogeLib

DogeLib needs [elan](https://github.com/leanprover/elan), which installs the Lean toolchain that `lean-toolchain` pins, `v4.35.0`.
The root DogeLib package uses Lean core and has no Lake dependencies.
Downstream projects that require it do not fetch Aeneas or Mathlib.
The optional package under `Refinement/` owns those dependencies and the Rust refinement library.

## Build and check

Build the specification and its proofs without the optional package:

```bash
lake build --wfail
lake exe check-decls --skip-refinement
lake test
bash scripts/test_oracle.sh
```

The explicit `--skip-refinement` flag prints `Refinement NOT checked` in the declaration-check summary.
It does not establish any result for the Rust refinement library.

Use this recommended local sequence for the full production checks.
Fetch the optional package's cache, then build both packages before the default declaration check:

```bash
lake -d Refinement exe cache get
lake build --wfail
lake -d Refinement build --wfail
lake exe check-decls
```

The default declaration check fails if the refinement package is absent, unbuilt or cannot load every requested module.
It names the reason and never silently checks fewer modules.
Production CI uses the default command.
The check inspects the built Refinement oleans.
After local edits, rebuild both packages in this order before running the default declaration check.
This sequence prevents the check from reading stale refinement artifacts.

Do not build Mathlib from source on a shared machine.
Its cached dependency directory occupies about 7.2 GiB per worktree, measured with this toolchain.
Aeneas and extraction tools need additional disk space ([Rust instructions](Refinement/Rust/README.md)).

`lake build --wfail` compiles the specification and checks its proofs.
The separate refinement build checks the generated model and its proof.
An unfinished proof only warns, so `--wfail` turns every warning into an error.

`lake exe check-decls` reads the compiled declarations of `DogeLib`, `Proofs`, `Exports` and `Refinement`.
It requires every `.lean` source under `DogeLib/` and `Refinement/Refinement/`, plus their roots, to be reachable.
It names each unreachable module and fails the check.

It reports any axiom beyond `propext`, `Classical.choice` and `Quot.sound` in the transitive dependencies of safe declarations.
Unsafe declarations are reported as `unsafe` findings.
It also reports any `partial`, `opaque`, `@[extern]`, `@[implemented_by]` or `@[csimp]` declaration.
It also reports a definition that reaches an opaque constant.
Only `Refinement` modules may reach `System.Platform.getNumBits`, which models Rust's platform word size.
Every other opaque dependency remains a finding ([SOUNDNESS.md](SOUNDNESS.md#c1-the-lean-kernel-and-its-axioms)).

`scripts/check_decls_baseline.txt` lists the findings that exist today.
It is empty, and a new finding is fixed, never added to it.

`lake test` runs known answers through the compiled specification.
Eleven directories hold fixture files, each with a README that gives their provenance:

- `tests/block/`: pure-header and Merkle-root known answers.
- `tests/block/mainnet-auxpow-activation-headers/`: public mainnet headers at heights 371320–371340, for the contextual header check around AuxPoW activation.
- `tests/block/mainnet-bip65-headers/`: public mainnet headers at heights 3464739–3464760, for the contextual header check around `BIP65Height`.
- `tests/block/mainnet-bip66-headers/`: public mainnet headers at heights 1032483–1034390, for the contextual header check around `BIP66Height`.
- `tests/cryptography/ripemd160/`: RIPEMD-160 vectors and Hash160 digests checked with hashlib and compiled Core.
- `tests/cryptography/sha1/cavp/`: the NIST CAVP vectors, for SHA-1.
- `tests/cryptography/sha256/cavp/`: the NIST CAVP vectors, for SHA-256.
- `tests/transaction/sighash/`: Dogecoin Core's signature-hash corpus, for the legacy signature hash.
- `tests/transaction/corpus/`: Dogecoin Core's transaction corpus, for the base-mode reader and codecs and the witness-allowed format.
- `tests/work/mainnet-genesis-headers/`: public mainnet headers at heights 0–12, for the median time past near genesis.
- `tests/work/mainnet-headers/`: public mainnet headers, for next-work selection across DigiShield activation.

The other known answers, and their provenance, are in the topic modules under `tests/KnownAnswers/`.

`bash scripts/test_oracle.sh` builds the oracle, `dogelib-oracle`, and tests it through its standard input and output.
It needs Python 3.10 or later, with only the standard library.
[docs/oracle.md](docs/oracle.md) defines the oracle's record format, and `tests/oracle/README.md` gives the provenance of its fixtures.
Dogecoin Core's own test cases test the compact target encoding and the difficulty retarget.
`tests/KnownAnswers/Work.lean` gives the file and line of each case.

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

### Compiled Rust CompactSize comparison

Build the Rust adapter, then compare only CompactSize reader requests through the oracle, Core and compiled Rust:

```bash
cargo +nightly-2026-09-17 build --locked --manifest-path Refinement/Rust/Cargo.toml --example compactsize_oracle --jobs 4
python3 -I scripts/compare_core.py --rust-compactsize Refinement/Rust/target/debug/examples/compactsize_oracle .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

This mode compares 404 requests: seven existing fixtures and 397 boundary, truncation, non-canonical and suffix cases.
It compares every error, successful value, consumed count and remainder.
The Rust crate has no encoder.
The comparator reads the oracle version at runtime and checks the Rust adapter's projection label.
The Core CI job builds the adapter and runs this comparison, with elapsed times in its logs.

## The declaration check

After a change to the check itself, run its self-test:

```bash
bash scripts/test_check_decls.sh
```

It builds the fixtures in `scripts/CheckDeclsTest`, which contain `sorry` and every other finding on purpose.
The check must report each planted finding and nothing else, pass with a baseline that lists them, and fail on a stale baseline entry.
An isolated fixture requires rejection of an imported unfinished proof.
The self-test also plants an unimported production file, and one under `DogeLib/Proposals/`, and requires a failure that names each module.

## Rust refinement

The optional package build checks the committed generated model and its complete-result proof.
CI uses the Mathlib cache in the separate package and caches Aeneas backend artifacts by pin and toolchain.
The `rust` job installs the pinned extraction tools and runs native Rust tests and extraction freshness on every pull request and push to `main`.
Release validation runs both Rust gates.
Run the same checks locally:

```bash
Refinement/Rust/setup-tools.sh
Refinement/Rust/regenerate.sh --check
cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 4
lake env lean --run scripts/CheckRefinementImports.lean
```

The last command rejects Aeneas, Mathlib or `Refinement` in the specification, proof and oracle libraries' transitive imports.
It also rejects `DogeLib.Proposals` in those imports, and the refinement dependencies in the imports of the `Proposals` and `ProposalProofs` libraries.
After a change to the check, run its self-test:

```bash
bash scripts/test_import_boundaries.sh
```

The self-test plants a module under `DogeLib/` that imports `DogeLib.Proposals`, and requires a failure that names the proposal modules.
[Refinement/Rust/README.md](Refinement/Rust/README.md) records the contract, fixtures, pins and regeneration steps.

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
EthLib's [`BUILDING.md`](https://github.com/ethereum/EthLib/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/BUILDING.md) explains the reasons in more detail.

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

## Oracle operation measurements

`scripts/bench_oracle.py` measures three exported operations from a hex request through the serialized response line.
It uses persistent oracle processes and includes request IO, JSON parsing, hex conversion, parsing and response IO.
The complete decoder also serializes and hashes the transaction.
The legacy operation constructs and hashes its preimage.
Python checks responses after the timer stops.

Build both variants from the same commit with identical flags.
For the before variant, use the base commit's `DogeLib/Transaction/Exports/Oracle.lean` file, which selects the list readers.
For the after variant, use the slice readers.
Set `base_commit` to that base commit.
Keep the reader-selection patch and the two binaries under `.lane/`, and restore the committed source after building:

```bash
oracle_source=DogeLib/Transaction/Exports/Oracle.lean
cp "$oracle_source" .lane/oracle-source.lean
trap 'cp .lane/oracle-source.lean "$oracle_source"' EXIT
git show "$base_commit:$oracle_source" > "$oracle_source"
git diff -- "$oracle_source" > .lane/list-reader.patch
taskset -c 4-7 nice -n 10 lake build dogelib-oracle
cp .lake/build/bin/dogelib-oracle .lane/oracle-list
cp .lane/oracle-source.lean "$oracle_source"
taskset -c 4-7 nice -n 10 lake build dogelib-oracle
cp .lake/build/bin/dogelib-oracle .lane/oracle-slice
taskset -c 4-7 nice -n 10 python3 -I scripts/bench_oracle.py .lane/oracle-list .lane/oracle-slice
```

The fixed workloads have 253 or 1000 inputs, 253 or 1000 outputs, or four output scripts of 4096 or 16384 bytes.
Each workload runs through `tx.read_base`, `tx.decode_base` and `sighash.legacy`.
Each process warms once per point, then runs five times with alternating variant order.
The output gives all five elapsed times and their median in nanoseconds.
Generated workloads supply timing evidence only.
The measurements establish neither an asymptotic bound nor a comparison with Core's speed.

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
It installs the pinned Rust extraction tools with `Refinement/Rust/setup-tools.sh`.
It then runs the report with the pinned Core checkout as `--core-clone` and without `--gates`.
So the runner runs every automated gate of the table, including both Rust gates and both Core comparisons.
It records the two manual gates, source and coverage review and soundness review, as not run.
The workflow builds the committed Lean model with the Mathlib cache.

A report records checks on one machine at one commit.
It is not a proof, and CI results on other commits are separate evidence.
