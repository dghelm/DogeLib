import Lake
open Lake DSL System

/-!
Lake build for `DogeLib`.

The root package uses Lean core and has no Lake dependencies.
The optional package under Refinement owns Aeneas and Mathlib.
ARCHITECTURE.md describes the libraries and what each may import.
The layout follows EthLib's `lakefile.lean` at commit `6a93711`.
-/

package «DogeLib» where

/-- The executable specification. It never imports a proof. -/
@[default_target]
lean_lib «DogeLib» where
  -- Lean v4.35.0, Source Files and Modules, section 5.4.
  -- Ordinary importers load public definitions without private proof bodies.
  requiresModuleSystem := true
  precompileModules := true

/-- Theorems about the specification, in a separate library rooted at
`DogeLib/Proofs.lean`, so that the specification never depends on it.
`precompileModules` is off: theorems produce no code.

Each layer's proof tree is also a root, so that its modules belong to
this library rather than to `DogeLib`. -/
@[default_target]
lean_lib «Proofs» where
  requiresModuleSystem := true
  roots := #[`DogeLib.Proofs, `DogeLib.Base.Proofs, `DogeLib.Cryptography.Proofs,
    `DogeLib.Block.Proofs, `DogeLib.Script.Proofs, `DogeLib.Serialization.Proofs, `DogeLib.Transaction.Proofs, `DogeLib.Work.Proofs]
  precompileModules := false

/-- The oracle and its operations, in a separate library rooted at
`DogeLib/Exports.lean`, so that a project that imports the specification
gets no IO code. Each layer's export tree is also a root, so that its
modules belong to this library rather than to `DogeLib`.

`precompileModules` is off. With it on, Lake v4.35.0 reports a build cycle,
because the library's shared object contains the executable's root module.
No module evaluates oracle code during elaboration, and the executable
compiles the code itself. -/
@[default_target]
lean_lib «Exports» where
  requiresModuleSystem := true
  roots := #[`DogeLib.Exports, `DogeLib.Serialization.Exports, `DogeLib.Transaction.Exports,
    `DogeLib.Work.Exports, `DogeLib.Block.Exports, `DogeLib.Cryptography.Exports, `DogeLib.Script.Exports]
  precompileModules := false

/-- The oracle: answers requests in the record format of `docs/oracle.md`,
one JSON object per line on standard input and output. -/
lean_exe «dogelib-oracle» where
  root := `DogeLib.Exports.Main

/-- Checks the compiled declarations of every library: their axioms, and any
construct the kernel cannot unfold or the compiler runs differently. Run it
after `lake build` with `lake exe check-decls`. -/
lean_exe «check-decls» where
  srcDir := "scripts"
  root := `CheckDecls
  supportInterpreter := true
  -- The checker loads private proof bodies to inspect their dependencies.
  allowNonModules := true

/-- Declarations the check must catch, and one module it must pass. Not a
default target: `scripts/test_check_decls.sh` builds and checks it. -/
lean_lib «CheckDeclsTest» where
  srcDir := "scripts"
  roots := #[`CheckDeclsTest, `CheckDeclsForeign, `CheckDeclsForeignSorry]
  -- The classic root checks findings behind ordinary module boundaries.
  allowNonModules := true

/-- Known answers from independent sources, run through the compiled
specification. `lake test` runs it. Lake allows one test driver, so every
known-answer test belongs to `tests/KnownAnswers.lean`. -/
@[test_driver]
lean_exe «known-answers» where
  srcDir := "tests"
  root := `KnownAnswers
  allowNonModules := true

/-- Generated transaction workloads for reader timing, outside the default targets. -/
lean_exe «bench-transaction-reader» where
  srcDir := "scripts"
  root := `BenchTransactionReader
  allowNonModules := true
