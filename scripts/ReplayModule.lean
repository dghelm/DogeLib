import LeanChecker

/-!
Replay the declarations of one module into Lean's kernel, for `scripts/replay.sh`.

The module is the value of the environment variable `REPLAY_MODULE`.
leanchecker replays every module whose name starts with its argument, in one process.
This script replays the named module alone.
It fails with the error of the kernel when a declaration does not replay.

The replay itself is `Kernel.Environment.replay` of Lean v4.35.0, called as `replayFromImports` of leanchecker calls it.
That replay does not compare a stored inductive type with the one that the kernel generates (Lean issue 16730).
In a mutual declaration, it sends the kernel the `numParams` of one member only.
So a metaprogram can store a different `numParams` for another member.
The kernel trusts the stored value when it types a projection, and a module that imports it can prove `False` without an axiom.
The replay also skips a stored inductive type that its own `all` field does not list (Lean issue 16688).

So this script keeps the environment that the replay returns, and then requires two things:

* Each part of the module (exported, server and private) stores the same constant as the private part, which the replay reads.
  The one exception is the axiom with the same type, as which the module system exports a theorem or a definition without its value.
* Each constant of the private part that the replay sends to the kernel equals the constant of its name in the replayed environment.

The second check compares every field of each constant, so an inductive type's `numParams`, `numIndices`, `all`, `ctors`, `isRec`, `isReflexive`, `numNested`, `levelParams` and `type` all count.
It follows Lean pull request 16717, which compares each member of `all` after the kernel adds the declaration.
It also covers constructors and recursors, which the replay compares already, and every other kind of constant.
The replay skips a theorem when the imports hold one with its name, type, universe parameters and `all` field.
This check accepts such a theorem with those four fields equal, as the replay does.
The replay skips `unsafe` and `partial` constants, and so does this check.

Adapted from EthLib, `scripts/ReplayModule.lean` at commit `b4070a856`, dedicated to the public domain under CC0 1.0.
The changes are the toolchain version in this comment, the attribution, and the comparison with the replayed environment, which follows `replayFromImports` of Lean v4.35.0 (`src/lean/LeanChecker.lean`, Apache 2.0).
-/

open Lean

/-- Whether the replay sends `ci` to the kernel. `Kernel.Environment.replay` of Lean v4.35.0 skips the rest. -/
def replayed (ci : ConstantInfo) : Bool := !ci.isUnsafe && !ci.isPartial

/-- Why the stored constant `stored`, under the key `name`, differs from the constant of the replayed environment, if it does. -/
def mismatch? (imports : Kernel.Environment) (name : Name) (stored : ConstantInfo)
    (kernel : Option ConstantInfo) : Option String :=
  if stored.name != name then
    some s!"the constant stored under '{name}' is named '{stored.name}'"
  else match kernel, stored with
    | none, _ => some s!"'{name}' is stored, but the replayed environment does not contain it"
    | some k, s =>
      if k == s then none
      else match k, s with
        -- The replay skips a theorem that the imports hold with the same statement (Lean v4.35.0, `replayConstant`).
        | .thmInfo k, .thmInfo s =>
          if (imports.find? name).isSome && k.name == s.name && k.type == s.type &&
              k.levelParams == s.levelParams && k.all == s.all then none
          else some s!"the stored theorem '{name}' differs from the one that the kernel checked"
        | .inductInfo k, .inductInfo s =>
          some s!"the stored inductive type '{name}' differs from the one that the kernel generated, in {inductFields k s}"
        | _, _ => some s!"the stored {kindOf s} '{name}' differs from the one that the kernel generated"
where
  /-- The fields in which two inductive types differ. -/
  inductFields (k s : InductiveVal) : List String :=
    [("levelParams", k.levelParams == s.levelParams), ("type", k.type == s.type),
      ("numParams", k.numParams == s.numParams), ("numIndices", k.numIndices == s.numIndices),
      ("all", k.all == s.all), ("ctors", k.ctors == s.ctors), ("numNested", k.numNested == s.numNested),
      ("isRec", k.isRec == s.isRec), ("isUnsafe", k.isUnsafe == s.isUnsafe),
      ("isReflexive", k.isReflexive == s.isReflexive)].filterMap fun (f, same) => if same then none else some f
  kindOf : ConstantInfo → String
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque constant"
    | .quotInfo _ => "quotient constant"
    | .inductInfo _ => "inductive type"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"

/-- Whether `ci`, stored in the exported or the server part, is the exported form of `full`, stored in the private part.
Lean v4.35.0 exports a theorem, and a definition that is not exposed, as an axiom with its name, universe parameters and type.
The replay checks `full`, and an importer of the axiom gets only that type. -/
def exportedForm (ci : ConstantInfo) (full : Option ConstantInfo) : Bool :=
  match ci, full with
  | .axiomInfo a, some full =>
    (full matches .thmInfo _ || full matches .defnInfo _ || full matches .opaqueInfo _) &&
      a.name == full.name && a.levelParams == full.levelParams && a.type == full.type &&
      a.isUnsafe == full.isUnsafe
  | _, _ => false

/-- Replay `module` against its imports, then compare its stored constants with the replayed environment.
The loading follows `replayFromImports` of Lean v4.35.0. -/
unsafe def replayAndCompare (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private).
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  -- The last ("most private") part subsumes the others.
  let last := parts[parts.size - 1].1
  for name in last.constNames, ci in last.constants do
    if newConstants.contains name then
      throw <| IO.userError s!"'{name}' is stored twice in the module {module}"
    newConstants := newConstants.insert name ci
  -- An importer can read another part, so each part must store what the replay reads,
  -- or the form in which the module system exports a theorem or a definition without its value.
  for (part, _) in parts do
    for name in part.constNames, ci in part.constants do
      unless newConstants[name]? == some ci || exportedForm ci newConstants[name]? do
        throw <| IO.userError s!"'{name}' differs between the parts of the module {module}"
  let imports := env.toKernelEnv
  let kernel ← imports.replay newConstants
  let mut checked := 0
  for (name, ci) in newConstants do
    if replayed ci then
      if let some why := mismatch? imports name ci (kernel.find? name) then
        throw <| IO.userError s!"in the module {module}: {why}"
      checked := checked + 1
  IO.println s!"{module}: {checked} stored constants equal the replayed ones"
  env.freeRegions

#eval show IO Unit from do
  let some name ← IO.getEnv "REPLAY_MODULE" | throw <| IO.userError "REPLAY_MODULE is not set"
  unsafe replayAndCompare name.toName
