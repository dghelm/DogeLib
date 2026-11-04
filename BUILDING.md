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
It reports any transitive axiom dependency beyond `propext`, `Classical.choice` and `Quot.sound`, and any `partial`, `opaque`, `unsafe`, `@[extern]`, `@[implemented_by]` or `@[csimp]` declaration.
It also reports a specification definition that reaches an opaque constant, so that the kernel cannot unfold it.

`scripts/check_decls_baseline.txt` lists the findings that exist today.
It is empty, and a new finding is fixed, never added to it.

`lake test` runs known answers through the compiled code.
Three directories hold vendored files, each with a README that gives their provenance:

- `tests/cryptography/sha256/cavp/`: the NIST CAVP vectors, for SHA-256.
- `tests/transaction/sighash/`: Dogecoin Core's signature-hash corpus, for the legacy signature hash.
- `tests/transaction/corpus/`: Dogecoin Core's transaction corpus, for the base-mode reader and codecs.

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
taskset -c 0-7 nice -n 10 lake build --wfail
```
