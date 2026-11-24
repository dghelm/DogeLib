import Lean

/-!
A module that stores a changed inductive type, for `scripts/test_replay.sh`, `scripts/test_check_decls.sh` and `scripts/test_check_lean_commands.py`.

It is the module `Forge` of Lean issue 16730, which Marius van der Wijden filed against Lean v4.36.0.
In the mutual declaration of `PA2` and `PB2`, the kernel generates `PB2` with no parameter and one index.
The `run_cmd` below then stores `PB2` again with one parameter and no index, through the private `Lean.Kernel.Environment.add`, which adds a constant without the kernel check.
`ForgedInductive.Use` proves `False` from it with no axiom.

The kernel replay of Lean v4.35.0 accepts this module: it sends the kernel the declaration with the `numParams` of `PA2`, and never compares the stored `PB2` with the one that the kernel generates.
`scripts/ReplayModule.lean` compares them, and must reject this module.
No library imports this file, and no build covers it.
-/

open Lean

mutual
inductive PA2 : Type
  | mk : PA2
inductive PB2 : Bool → Type
  | mk : (b : Bool) → (h : b = false) → PB2 true
end

def px : PB2 true := PB2.mk false rfl

-- `Lean.Kernel.Environment.add` (private, inserts a constant without checking), referenced by name.
elab "kernelAdd" : term =>
  return mkConst (Name.mkStr (Name.mkNum (Name.mkStr (Name.mkStr (Name.mkStr .anonymous "_private") "Lean")
    "Environment") 0 |>.append `Lean.Kernel.Environment) "add")
def kernelAdd' : Kernel.Environment → ConstantInfo → Kernel.Environment := kernelAdd

-- Store `PB2` again with `numParams := 1, numIndices := 0`. The kernel generated 0 and 1.
run_cmd Elab.Command.liftCoreM do
  let some (.inductInfo v) := (← getEnv).find? `PB2 | throwError "no PB2"
  setEnv (Environment.ofKernelEnv (kernelAdd' (← getEnv).toKernelEnv (.inductInfo { v with numParams := 1, numIndices := 0 })))
