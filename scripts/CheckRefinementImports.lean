import Lean

/-!
Check the import boundaries of the root package.

The baseline libraries, `DogeLib`, `Proofs` and `Exports`, must not import the refinement dependencies or a proposed revision under `DogeLib.Proposals`.
The proposal libraries, `Proposals` and `ProposalProofs`, must not import the refinement dependencies.
Design record 0007, section 4, sets the boundary for proposals.

With module names as arguments, the check loads those modules as baseline roots instead of the default ones, and skips the proposal roots.
`scripts/test_import_boundaries.sh` uses that form to plant a forbidden import.
-/

open Lean

/-- The module prefixes that the refinement package owns. -/
def refinementPrefixes : List Name := [`Aeneas, `AeneasMeta, `Mathlib, `Refinement]

/-- The roots of the baseline libraries. -/
def baselineRoots : List Name := [`DogeLib, `DogeLib.Proofs, `DogeLib.Exports]

/-- The roots of the proposal libraries. -/
def proposalRoots : List Name := [`DogeLib.Proposals, `DogeLib.Proposals.Proofs]

/-- The modules that `roots` import, directly or transitively, and the roots themselves. -/
partial def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let index : Std.HashMap Name Nat := env.header.moduleNames.foldl (init := {}) fun m n => m.insert n m.size
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | m :: rest =>
      if seen.contains m then go rest seen
      else
        let imports := match index[m]? with
          | some i => (env.header.moduleData[i]!.imports.map (·.module)).toList
          | none => []
        go (imports ++ rest) (seen.insert m)
  return go roots {}

/-- The modules of `closure env roots` with a name under one of `forbidden`. -/
def forbiddenImports (env : Environment) (roots forbidden : List Name) : Array Name :=
  ((closure env roots).toArray.filter fun m => forbidden.any (·.isPrefixOf m)).qsort Name.lt

/-- Load the libraries and reject the forbidden prefixes in their transitive imports. -/
unsafe def main (args : List String) : IO UInt32 := do
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
  let custom := !args.isEmpty
  let roots := if custom then args.map String.toName else baselineRoots
  let loaded := if custom then roots else roots ++ proposalRoots
  let env ← importModules (loaded.toArray.map fun m => { module := m }) {} (loadExts := true) (level := .private)
  let baselineBad := forbiddenImports env roots (refinementPrefixes ++ [`DogeLib.Proposals])
  for m in baselineBad do
    IO.eprintln s!"forbidden import in a baseline library: {m}"
  let proposalBad := if custom then #[] else forbiddenImports env proposalRoots refinementPrefixes
  for m in proposalBad do
    IO.eprintln s!"forbidden refinement dependency in a proposal library: {m}"
  unless baselineBad.isEmpty && proposalBad.isEmpty do
    return 1
  if custom then
    IO.println s!"import boundaries: {roots} import neither refinement dependencies nor DogeLib.Proposals"
  else
    IO.println "import boundaries: the root package has no dependencies; DogeLib, Proofs and Exports import neither refinement dependencies nor DogeLib.Proposals; Proposals and ProposalProofs do not import refinement dependencies"
  return 0
