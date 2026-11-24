import Lean

/-!
A theorem that the kernel never checked, for `scripts/replay.sh`.

Its type is `False` and its proof is `True.intro`.
The replay must reject it.

Adapted from EthLib, `scripts/ReplayFixture.lean` at commit `b4070a856`, dedicated to the public domain under CC0 1.0.
-/

open Lean Elab Command

set_option debug.skipKernelTC true in
run_cmd liftCoreM <| addDecl <| .thmDecl {
  name := `ReplayFixture.unchecked
  levelParams := []
  type := mkConst ``False
  value := mkConst ``True.intro }
