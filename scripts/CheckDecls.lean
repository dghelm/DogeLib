import Lean

/-!
# `CheckDecls`

Checks the compiled declarations of DogeLib.

Adapted from EthLib, `scripts/CheckDecls.lean` at commit `6a93711`, dedicated to the public domain under CC0 1.0.
The changes are the default scope, the default modules and this paragraph.

It reads what the kernel accepted, not the source, so no formatting of the source can hide a finding.

Every declaration in scope is checked for:

* an axiom beyond `propext`, `Classical.choice` and `Quot.sound`, followed through every dependency, so `sorry`, `native_decide`, `bv_decide` and `decide +native` are all caught;
* an `axiom` declaration;
* an `unsafe`, `partial` or `opaque` constant, which the kernel cannot unfold;
* `@[extern]` or `@[implemented_by]`, which make the compiled code run something other than the definition;
* a `@[csimp]` theorem that replaces a function in scope.

A definition of the specification is also checked for reaching an opaque constant through the definitions it unfolds to.
`while` reaches `Loop.forIn`, which Lean core defines with `partial`, and `IO` reaches the runtime's primitives.
Such a definition cannot be unfolded either.
Proofs are exempt, because nothing unfolds them.
The `Exports` modules are exempt, because IO belongs there.

Only `Refinement` modules may reach `System.Platform.getNumBits`, the opaque platform word size used to model Rust `usize`.
Every other reachable opaque remains a finding.

A finding is reported once, at the declaration in scope that first brings it in.
A theorem proved by `native_decide` is reported, and the theorems that use it are not.

The baseline lists the findings that exist today, each one to be removed.
Every other finding fails the check.
A baseline entry that is no longer found also fails the check, so the baseline stays an exact list of the findings that exist.
-/

open Lean

namespace CheckDecls

/-- The axioms every declaration may depend on. -/
def allowedAxioms : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]

/-- One finding: its kind, the declaration it is reported at, and what was found. -/
structure Finding where
  kind : String
  decl : Name
  detail : String

/-- The declaration a generated native axiom belongs to: the part of its name before `_native`.
The name is only a claim, so the owner must exist, and something must follow `_native`, as in the names the tactics generate. -/
def nativeOwner? (env : Environment) (a : Name) : Option Name := do
  let cs := a.components
  guard (cs.contains `_native)
  let owner := (cs.takeWhile (· != `_native)).foldl (· ++ ·) .anonymous
  guard (cs.length > owner.components.length + 1 && owner != a)
  -- Module proof bodies give generated axioms a private prefix even for public theorems.
  -- Lean v4.35.0, `Lean.Meta.nativeEqTrue` in Lean/Meta/Native.lean.
  -- Prefer an existing private owner before resolving the corresponding public name.
  let owner := if env.contains owner then owner else privateToUserName owner
  guard (env.contains owner)
  return owner

/-- An axiom that trusts compiled code, rather than a statement the kernel checks.
`native_decide`, `bv_decide` and `decide +native` each add one, named after the declaration that uses it.
An axiom that merely has `_native` in its name, with no such declaration, is an ordinary axiom. -/
def isNativeAxiom (env : Environment) (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.trustCompiler || (nativeOwner? env n).isSome

/-- The module that defines `n`. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  -- Lean v4.35.0 `EnvironmentHeader.moduleNames` maps this array on every call.
  return (← env.header.modules[idx.toNat]?).module

/-- Whether `n` is defined in a module under `scope`. -/
def inScope (env : Environment) (scope : Name) (n : Name) : Bool :=
  (moduleOf? env n).any scope.isPrefixOf

/-- Whether `n` is defined in a proof module, one with a `Proofs` component in its name. -/
def inProofs (env : Environment) (n : Name) : Bool :=
  (moduleOf? env n).any (·.components.contains `Proofs)

/-- Whether `n` is defined in a C export module, one under an `Exports` component. -/
def inExports (env : Environment) (n : Name) : Bool :=
  (moduleOf? env n).any (·.components.contains `Exports)

/-- A compiler auxiliary of a `partial` definition, reported through its parent.
The name is only a claim, so the parent must exist and be the opaque constant a `partial` definition becomes. -/
def isUnsafeRec (env : Environment) (n : Name) : Bool :=
  match n with
  | .str p "_unsafe_rec" => env.find? p |>.any (· matches .opaqueInfo _)
  | _ => false

/-! ## Axioms, followed through every dependency -/

/-- Read-only access to one environment, which is all `Lean.collectAxioms` needs. -/
instance : MonadEnv (ReaderT Environment Id) where
  getEnv := read
  modifyEnv _ := pure ()

/-- Every axiom that some declaration of `decls` depends on, by `Lean.collectAxioms`.
Each module records the axioms of its own constants when it is compiled, so an imported dependency is looked up, not walked again. -/
def axiomsOfAll (env : Environment) (decls : List Name) : Array Name :=
  let all := decls.foldl (init := ({} : NameSet)) fun acc n =>
    (collectAxioms (m := ReaderT Environment Id) n |>.run env).foldl (·.insert ·) acc
  all.toArray


/-- The constants whose axioms `c` inherits.
This is what `Lean.collectAxioms` visits: the type, the value or proof, and the constructors of an inductive type. -/
def axiomChildren (c : ConstantInfo) : Array Name :=
  match c with
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- A memoized `Lean.collectAxioms`.
An inductive type and its constructors refer to each other, so a constant still being visited contributes nothing. -/
partial def axiomsOf (env : Environment) (n : Name) : StateM (NameMap NameSet) NameSet := do
  if let some s := (← get).find? n then return s
  modify (·.insert n {})
  let some c := env.find? n | return {}
  let mut s : NameSet := if c matches .axiomInfo _ then ({} : NameSet).insert n else {}
  for child in axiomChildren c do
    for a in ← axiomsOf env child do
      s := s.insert a
  modify (·.insert n s)
  return s

/-! ## Opaque constants, followed through definitions -/

/-- The functions that report a failure.
Each takes the type and an `Inhabited` instance first, and its value is that instance's `default`.
The arguments after those two are the message, and nothing else. -/
def panicFamily : NameSet :=
  .ofList [``panicCore, ``panic, ``panicWithPos, ``panicWithPosWithDecl]

/-- `e` with the message arguments dropped from every call to the panic family.
The type and the `Inhabited` instance stay: the instance's `default` is the value the kernel sees, so it can block unfolding.
Nothing else is dropped, so a message-building function used for a value, even inside a fallback, is still followed.
`panicWithPos` and `panicWithPosWithDecl` are `panic` applied to a built message, so following them drops that message too. -/
partial def dropPanicMessages (e : Expr) : Expr :=
  e.replace fun t => match t.getAppFn.constName? with
    | some f =>
      if panicFamily.contains f && t.getAppNumArgs ≥ 2 then
        some (mkAppN (.const ``panicCore t.getAppFn.constLevels!) (t.getAppArgs.extract 0 2 |>.map dropPanicMessages))
      else none
    | none => none

/-- The opaque constants `n` reaches through the values of the definitions it unfolds to.
A theorem, an axiom or a type stops the search: none of them blocks a definition from unfolding. -/
partial def opaquesOf (env : Environment) (n : Name) : StateM (NameMap NameSet) NameSet := do
  if let some s := (← get).find? n then return s
  modify (·.insert n {})
  let s ← match env.find? n with
    | some (.opaqueInfo _) => pure (({} : NameSet).insert n)
    | some (.defnInfo v) => do
      let mut s : NameSet := {}
      for child in (dropPanicMessages v.value).getUsedConstants do
        for o in ← opaquesOf env child do
          s := s.insert o
      pure s
    | _ => pure {}
  modify (·.insert n s)
  return s

/-- Whether `c` is a `Repr` or `ToString` instance: output formatting, not specification. -/
def isFormattingType (c : ConstantInfo) : Bool :=
  c.type.getForallBody.getAppFn.constName? |>.any fun h => h == ``Repr || h == ``ToString

/-- Whether `n` is a `Repr` or `ToString` instance, or a function generated for one, such as `instReprFoo.repr`. -/
def isFormatting (env : Environment) (n : Name) (c : ConstantInfo) : Bool :=
  isFormattingType c || (env.find? n.getPrefix).any isFormattingType

/-! ## The check -/

/-- Every `@[csimp]` theorem ever registered, with the function it replaces when it is still the current one.
A superseded replacement may already have been applied to code compiled before it was superseded, so each one counts. -/
def csimpTheorems (env : Environment) : List (Name × Option Name) :=
  let state := Compiler.CSimp.ext.getState env
  let replaces : NameMap Name :=
    state.map.toList.foldl (fun m (_, e) => m.insert e.thmName e.fromDeclName) {}
  state.thmNames.toList.map fun thm => (thm, replaces.find? thm)

/-- The members of `s` that no in-scope child of `c` already carries. -/
def frontier (env : Environment) (scope : Name) (memo : NameMap NameSet)
    (children : Array Name) (s : NameSet) : List Name :=
  let inherited := children.foldl (init := ({} : NameSet)) fun acc child =>
    if inScope env scope child && !(env.find? child |>.any (· matches .axiomInfo _)) then
      ((memo.find? child).getD {}).foldl (·.insert ·) acc
    else acc
  s.toList.filter (!inherited.contains ·)

/-- The inductive type in scope that `n` belongs to, if any: `n` itself, or the nearest prefix of its name.
A constructor, a recursor and the lemmas generated for them, such as `Foo.mk.inj`, all belong to `Foo`. -/
def inductiveOwner? (env : Environment) (scope : Name) : Name → Option Name
  | .anonymous => none
  | n@(.num p _) | n@(.str p _) =>
    if (env.find? n).any (· matches .inductInfo _) && inScope env scope n then some n
    else inductiveOwner? env scope p

/-- Check every declaration in a module under `scope`. -/
def check (env : Environment) (scope : Name) : Array Finding := Id.run do
  let decls := env.constants.toList.filter fun (n, _) => inScope env scope n
  let mut out : Array Finding := #[]
  for (n, c) in decls do
    if let .axiomInfo _ := c then
      unless isNativeAxiom env n do
        out := out.push ⟨"axiom", n, "an axiom declaration"⟩
    if c.isUnsafe && !isUnsafeRec env n then
      out := out.push ⟨"unsafe", n, "an unsafe declaration"⟩
    if let .opaqueInfo _ := c then
      unless isExtern env n do
        let kind := if env.contains (n ++ `_unsafe_rec) then "partial" else "opaque"
        out := out.push ⟨kind, n, s!"a {kind} constant, which the kernel cannot unfold"⟩
    if isExtern env n then
      out := out.push ⟨"extern", n, "an @[extern] declaration"⟩
    if let some impl := Compiler.getImplementedBy? env n then
      out := out.push ⟨"implemented_by", n, s!"compiled as {impl}"⟩
  -- Axioms are reported where they enter the scope, not at every declaration that inherits them.
  -- An unsafe declaration is a finding already, and the kernel never relies on what it depends on.
  let decls := decls.filter fun (_, c) => !c.isUnsafe
  let extra := (axiomsOfAll env (decls.map (·.1))).filter (!allowedAxioms.contains ·)
  let mut foreign : NameSet := {}
  for a in extra do
    if a == ``sorryAx then
      foreign := foreign.insert a
      for (n, c) in decls do
        if c.getUsedConstantsAsSet.contains ``sorryAx then
          out := out.push ⟨"sorry", n, "depends on sorryAx"⟩
    else if let some owner := (nativeOwner? env a).filter (inScope env scope) then
      out := out.push ⟨"native", owner, s!"depends on {a}"⟩
    else if inScope env scope a then
      for (n, c) in decls do
        if n != a && c.getUsedConstantsAsSet.contains a then
          out := out.push ⟨"axioms", n, s!"depends on {a}"⟩
    else
      foreign := foreign.insert a
  -- An axiom from a dependency is rare, so only then is every declaration followed on its own.
  unless foreign.isEmpty do
    let (_, memo) := (decls.forM fun (n, _) => discard (axiomsOf env n)).run {}
    let mut attributed : NameSet := {}
    for (n, c) in decls do
      unless c matches .axiomInfo _ do
        let mine := ((memo.find? n).getD {}).toList.filter foreign.contains
        for a in frontier env scope memo (axiomChildren c) (.ofList mine) do
          -- Direct unfinished proofs keep their existing `sorry` finding.
          unless a == ``sorryAx && c.getUsedConstantsAsSet.contains a do
            out := out.push ⟨"axioms", n, s!"depends on {a}, from a dependency"⟩
          attributed := attributed.insert a
    -- Attribution can fail: an inductive type and its constructors each inherit the axiom from the other, so neither is a frontier.
    -- Detection must not depend on it, so an axiom still unreported is reported where it is used directly.
    -- An inductive type in scope, its constructors, recursors and generated lemmas report through the type.
    for a in foreign do
      unless attributed.contains a do
        let mut at_ : NameSet := {}
        for (n, c) in decls do
          if (axiomChildren c).contains a then
            at_ := at_.insert ((inductiveOwner? env scope n).getD n)
        if at_.isEmpty then
          -- Reached only through other dependencies: report the axiom itself, so it is never lost.
          out := out.push ⟨"axioms", a, "reached from this scope, but no declaration could be named"⟩
        for n in at_ do
          out := out.push ⟨"axioms", n, s!"depends on {a}, from a dependency"⟩
  -- A definition of the specification must unfold, unless it is a C export or formatting.
  -- The function `initialize` generates is reported through the constant it initializes.
  let initFns : NameSet := decls.foldl (init := {}) fun s (n, _) =>
    match getInitFnNameFor? env n with
    | some f => s.insert f
    | none => s
  let spec := decls.filter fun (n, c) =>
    c matches .defnInfo _ && !inProofs env n && !inExports env n && !isFormatting env n c
      && !initFns.contains n
  let (_, opaqueMemo) := (spec.forM fun (n, _) => discard (opaquesOf env n)).run {}
  for (n, c) in spec do
    if let .defnInfo v := c then
      let reached := (opaqueMemo.find? n).getD {}
      let fresh := (frontier env scope opaqueMemo (dropPanicMessages v.value).getUsedConstants reached).filter
        fun o => !(o == `System.Platform.getNumBits && inScope env `Refinement n)
      unless fresh.isEmpty do
        out := out.push ⟨"reaches-opaque", n, s!"unfolds to {fresh.take 3}"⟩
  for (thm, target) in csimpTheorems env do
    if inScope env scope thm || target.any (inScope env scope) then
      out := out.push ⟨"csimp", thm, s!"a @[csimp] theorem replacing {target.getD thm}"⟩
  return out

/-! ## Production module reachability -/

/-- The roots that load every production module.
Both the specification libraries and the Rust refinement library belong to the production check. -/
def defaultModules : List Name := [`DogeLib, `DogeLib.Proofs, `DogeLib.Exports, `Refinement]

/-- The production module namespaces, excluding dependency libraries. -/
def defaultScopes : List Name := [`DogeLib, `Refinement]

/-- Production modules on disk that the imported environment does not contain.
The inventory includes leaf files, even when a library root omits them. -/
def unreachableModules (env : Environment) (includeRefinement : Bool) : IO (Array Name) := do
  let files ← (System.FilePath.walkDir "DogeLib")
  let rustFiles ← if includeRefinement then
    System.FilePath.walkDir "Refinement/Refinement" else pure #[]
  let files := (files.push "DogeLib.lean") ++ rustFiles
  let files := if includeRefinement then files.push "Refinement/Refinement.lean" else files
  let imported : NameSet := env.header.modules.foldl (fun s m => s.insert m.module) {}
  let mut missing := #[]
  for path in files do
    if path.extension == some "lean" then
      let parts := (path.withExtension "").components
      let parts := if parts.head? == some "Refinement" then parts.drop 1 else parts
      let n := parts.foldl (fun n c => Name.str n c) .anonymous
      unless imported.contains n do
        missing := missing.push n
  return missing

/-- Resolve the separate refinement package without fetching its dependencies when it is unbuilt. -/
def refinementSearchPath : IO (Except String System.SearchPath) := do
  unless ← System.FilePath.pathExists "Refinement/lakefile.lean" do
    return .error "refinement package unavailable: Refinement/lakefile.lean is missing"
  unless ← System.FilePath.pathExists "Refinement/.lake/build/lib/lean/Refinement.olean" do
    return .error "refinement package unbuilt: run lake -d Refinement exe cache get, then lake -d Refinement build --wfail"
  try
    let out ← IO.Process.output { cmd := "lake", args := #["-d", "Refinement", "env", "printenv", "LEAN_PATH"] }
    if out.exitCode != 0 then
      return .error s!"refinement package environment unavailable: {out.stderr.trimAscii}"
    return .ok ([System.FilePath.mk "Refinement/.lake/build/lib/lean"] ++ System.SearchPath.parse out.stdout.trimAscii.toString)
  catch e =>
    return .error s!"refinement package environment unavailable: {e}"

/-! ## The baseline -/

/-- The baseline: one `kind declaration` per line, with `#` comments and blank lines ignored. -/
def readBaseline (path : System.FilePath) : IO (List (String × Name)) := do
  let lines ← IO.FS.lines path
  return lines.toList.filterMap fun line =>
    match (line.splitOn "#").head!.splitOn " " |>.filter (· ≠ "") with
    | [kind, decl] => some (kind, decl.toName)
    | _ => none

/-- Entry point: `check-decls [--skip-refinement] [--scope NAME] [--baseline FILE] [Module ...]`.
It is `unsafe` because loading the environment extensions runs their initializers.
The tool itself is not part of the checked scope. -/
unsafe def run (args : List String) : IO UInt32 := do
  let usage := "usage: check-decls [--skip-refinement] [--scope NAME] [--baseline FILE] [Module ...]"
  let rec parse : List String → Name → System.FilePath → List Name → Bool →
      Except String (Name × System.FilePath × List Name × Bool)
    | [], scope, baseline, mods, skip => .ok (scope, baseline, mods.reverse, skip)
    | "--scope" :: s :: rest, _, baseline, mods, skip => parse rest s.toName baseline mods skip
    | "--baseline" :: b :: rest, scope, _, mods, skip => parse rest scope b mods skip
    | "--skip-refinement" :: rest, scope, baseline, mods, _ => parse rest scope baseline mods true
    | a :: rest, scope, baseline, mods, skip =>
      if a.startsWith "--" then .error s!"unknown option {a}" else parse rest scope baseline (a.toName :: mods) skip
  let (scope, baselinePath, mods, skipRefinement) ← match parse args `DogeLib "scripts/check_decls_baseline.txt" [] false with
    | .ok r => pure r
    | .error e => do
      IO.eprintln s!"check-decls: {e}\n{usage}"
      return 2
  let checkProduction := mods.isEmpty && scope == `DogeLib
  if skipRefinement && !checkProduction then
    IO.eprintln "check-decls: --skip-refinement applies only to the default production check"
    return 2
  let checkRefinement := (checkProduction && !skipRefinement) || Name.isPrefixOf `Refinement scope ||
    mods.any (Name.isPrefixOf `Refinement ·)
  let mods := if mods.isEmpty then
    (if skipRefinement then defaultModules.filter (· != `Refinement) else defaultModules) else mods
  if checkProduction then
    unless (← System.FilePath.pathExists "DogeLib.lean") && (← System.FilePath.isDir "DogeLib") do
      IO.eprintln "check-decls: run the default production check from the repository root (DogeLib.lean and DogeLib/ are required)"
      return 2
  let refinementPaths ← if checkRefinement then
    match ← refinementSearchPath with
    | .ok paths => pure paths
    | .error reason => do
      IO.eprintln s!"check-decls: {reason}"
      return 2
    else pure []
  initSearchPath (← findSysroot) refinementPaths
  -- `loadExts := true` is essential: without it the `@[csimp]` table, among others, stays empty.
  -- Lean v4.35.0 `Lean.importModules`: `.private` loads every private proof body.
  -- Exported artifacts alone cannot reveal a theorem's full dependencies.
  enableInitializersExecution
  let env ← try
    importModules (mods.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
      (loadExts := true) (level := .private)
  catch e =>
    IO.eprintln s!"check-decls: cannot import every requested production module: {e}"
    return 2
  if (csimpTheorems env).isEmpty then
    IO.eprintln "check-decls: no @[csimp] theorems visible, so the extensions did not load"
    return 3
  let missing ← if checkProduction then unreachableModules env (!skipRefinement) else pure #[]
  for m in missing do
    IO.eprintln s!"unreachable-module {m}: not imported by the default production roots"
  let baseline ← readBaseline baselinePath
  let scopes := if checkProduction then
    (if skipRefinement then [`DogeLib] else defaultScopes) else [scope]
  let findings := scopes.foldl (fun acc s => acc ++ check env s) #[]
  let isListed (f : Finding) := baseline.contains (f.kind, f.decl)
  let fresh := findings.filter (!isListed ·)
  for f in fresh do
    IO.println s!"{f.kind} {f.decl}: {f.detail}"
  let stale := baseline.filter fun (kind, decl) => !findings.any (fun f => f.kind == kind && f.decl == decl)
  for (kind, decl) in stale do
    IO.println s!"stale baseline entry, no longer found: {kind} {decl}"
  let nDecls := env.constants.toList.countP fun (n, _) => scopes.any (fun s => inScope env s n)
  let scopeLabel := if checkProduction then
    (if skipRefinement then "DogeLib (Refinement NOT checked)" else "DogeLib and Refinement") else toString scope
  IO.println s!"check-decls: {nDecls} declarations under {scopeLabel}, {findings.size} findings, {findings.size - fresh.size} in the baseline, {fresh.size} new, {stale.length} stale"
  return if missing.isEmpty && fresh.isEmpty && stale.isEmpty then 0 else 1

end CheckDecls

unsafe def main (args : List String) : IO UInt32 := CheckDecls.run args
