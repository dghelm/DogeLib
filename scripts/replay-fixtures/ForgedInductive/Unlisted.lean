import Lean

/-!
A stored inductive type that its own `all` field does not list, from Lean issue 16688.

`bad` has the type `False`, no constructor, and the `all` field `[Z]`.
The kernel replay of Lean v4.35.0 replays `Z` in its place and never adds `bad`, so it accepts the module, and an importer can prove `False` from `bad`.
`scripts/ReplayModule.lean` must reject this module, because the replayed environment does not contain `bad`.
-/

open Lean

inductive Z : Prop

-- `Lean.Kernel.Environment.add`, as in `ForgedInductive`.
elab "kernelAddUnlisted" : term =>
  return mkConst (Name.mkStr (Name.mkNum (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "_private") "Lean")
    "Environment") 0 |>.append `Lean.Kernel.Environment) "add")
def kernelAddUnlisted' : Kernel.Environment → ConstantInfo → Kernel.Environment := kernelAddUnlisted

run_cmd Elab.Command.liftCoreM do
  let v : InductiveVal := {
    name := `bad, levelParams := [], type := mkConst ``False, numParams := 0, numIndices := 0
    all := [`Z], ctors := [], numNested := 0, isRec := false, isUnsafe := false, isReflexive := false }
  setEnv (Environment.ofKernelEnv (kernelAddUnlisted' (← getEnv).toKernelEnv (.inductInfo v)))
