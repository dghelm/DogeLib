import Lean

/-! Check that the specification, proofs and oracle do not import the refinement dependencies. -/

open Lean

/-- Load the existing libraries and reject Aeneas or Mathlib in their transitive imports. -/
unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `DogeLib }, { module := `DogeLib.Proofs },
    { module := `DogeLib.Exports }] {} (loadExts := true) (level := .private)
  let forbidden := env.header.modules.filter fun m =>
    [`Aeneas, `AeneasMeta, `Mathlib, `Refinement].any (·.isPrefixOf m.module)
  if forbidden.isEmpty then
    IO.println "import boundaries: DogeLib, Proofs and Exports do not import Aeneas, Mathlib or Refinement"
    return 0
  for m in forbidden do
    IO.eprintln s!"forbidden refinement dependency: {m.module}"
  return 1
