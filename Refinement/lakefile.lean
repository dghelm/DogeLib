import Lake
open Lake DSL

/-! The optional Rust refinement package owns Aeneas and Mathlib dependencies. -/

require DogeLib from ".."
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "d1e177bb9fdc17fa62e730d524ac905ba19776ed" / "backends/lean"

package «dogelib-refinement» where

/-- The extracted Rust model and its complete-result refinement proof. -/
@[default_target]
lean_lib «Refinement» where
  requiresModuleSystem := true
  precompileModules := false
