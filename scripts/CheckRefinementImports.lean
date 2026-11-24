import Lean

/-!
Check the import boundaries of the root package.

The baseline libraries, `DogeLib`, `Proofs` and `Exports`, must not import the refinement dependencies or a proposed revision under `DogeLib.Proposals`.
The proposal libraries, `Proposals`, `ProposalProofs` and `ProposalExports`, must not import the refinement dependencies.
`ProposalExports` is under `DogeLib.Proposals`, so a baseline library that imports it fails the first rule.
Design record 0007, section 4, sets the boundary for proposals, and design record 0011, decision 10, adds `ProposalExports`.
The specification, `DogeLib`, and the export libraries, `Exports` and `ProposalExports`, must not import a module of a proof library.
ARCHITECTURE.md states that the specification builds and links without the proofs.

A module of a proof library has `Proofs` as a component of its name.

With module names as arguments, the check loads those modules as baseline roots instead of the default ones, and skips the proposal roots.
It applies the first rule and the proof rule to those modules.
`scripts/test_import_boundaries.sh` uses that form to plant a forbidden import.
-/

open Lean

/-- The module prefixes that the refinement package owns. -/
def refinementPrefixes : List Name := [`Aeneas, `AeneasMeta, `Mathlib, `Refinement]

/-- The roots of the baseline libraries. -/
def baselineRoots : List Name := [`DogeLib, `DogeLib.Proofs, `DogeLib.Exports]

/-- The roots of the proposal libraries. -/
def proposalRoots : List Name := [`DogeLib.Proposals, `DogeLib.Proposals.Proofs, `DogeLib.Proposals.Exports]

/-- The roots of the specification and of the export libraries, which must not import a proof module. -/
def proofFreeRoots : List Name := [`DogeLib, `DogeLib.Exports, `DogeLib.Serialization.Exports,
  `DogeLib.Transaction.Exports, `DogeLib.Work.Exports, `DogeLib.Block.Exports, `DogeLib.Cryptography.Exports,
  `DogeLib.Script.Exports, `DogeLib.Proposals.Exports]

/-- Whether a module belongs to a proof library: a component of its name is `Proofs`. -/
def isProofModule (m : Name) : Bool := m.components.contains `Proofs

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
  let loaded := if custom then roots else roots ++ proposalRoots ++ proofFreeRoots
  let env ← importModules (loaded.toArray.map fun m => { module := m }) {} (loadExts := true) (level := .private)
  let baselineBad := forbiddenImports env roots (refinementPrefixes ++ [`DogeLib.Proposals])
  for m in baselineBad do
    IO.eprintln s!"forbidden import in a baseline library: {m}"
  let proposalBad := if custom then #[] else forbiddenImports env proposalRoots refinementPrefixes
  for m in proposalBad do
    IO.eprintln s!"forbidden refinement dependency in a proposal library: {m}"
  let proofRoots := if custom then roots else proofFreeRoots
  let proofBad := ((closure env proofRoots).toArray.filter isProofModule).qsort Name.lt
  for m in proofBad do
    IO.eprintln s!"forbidden proof import in the specification or an export library: {m}"
  unless baselineBad.isEmpty && proposalBad.isEmpty && proofBad.isEmpty do
    return 1
  if custom then
    IO.println s!"import boundaries: {roots} import no refinement dependency, no module of DogeLib.Proposals and no proof module"
  else
    IO.println "import boundaries: the root package has no dependencies; DogeLib, Proofs and Exports import neither refinement dependencies nor DogeLib.Proposals; Proposals, ProposalProofs and ProposalExports do not import refinement dependencies; DogeLib, Exports and ProposalExports import no proof module"
  return 0
