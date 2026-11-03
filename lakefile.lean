import Lake
open Lake DSL System

/-!
Lake build for `DogeLib`.

The package is pure Lean, with no dependencies beyond Lean core.
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
  roots := #[`DogeLib.Proofs, `DogeLib.Cryptography.Proofs]
  precompileModules := false

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
  roots := #[`CheckDeclsTest, `CheckDeclsForeign]
  -- The classic root checks findings behind ordinary module boundaries.
  allowNonModules := true
