import Lean

/-! Check that the specification, proofs and oracle do not import the refinement dependencies. -/

open Lean

/-- Load the existing libraries and reject Aeneas or Mathlib in their transitive imports. -/
unsafe def main : IO UInt32 := do
  let manifest ← IO.FS.readFile "lake-manifest.json"
  let json ← match Json.parse manifest with
    | .ok json => pure json
    | .error e => throw (IO.userError e)
  let packages ← match json.getObjValAs? (Array Json) "packages" with
    | .ok packages => pure packages
    | .error e => throw (IO.userError e)
  unless packages.isEmpty do
    IO.eprintln "root package dependencies are not empty"
    return 1
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `DogeLib }, { module := `DogeLib.Proofs },
    { module := `DogeLib.Exports }] {} (loadExts := true) (level := .private)
  let forbidden := env.header.modules.filter fun m =>
    [`Aeneas, `AeneasMeta, `Mathlib, `Refinement].any (·.isPrefixOf m.module)
  if forbidden.isEmpty then
    IO.println "import boundaries: the root package has no dependencies; DogeLib, Proofs and Exports do not import refinement dependencies"
    return 0
  for m in forbidden do
    IO.eprintln s!"forbidden refinement dependency: {m.module}"
  return 1
