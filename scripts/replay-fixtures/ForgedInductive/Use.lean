import Lean
import ForgedInductive

/-!
The module `Use` of Lean issue 16730: a proof of `False` with no axiom, from the changed `PB2` of `ForgedInductive`.

`tf` is the field 0 of `px : PB2 true`, as a raw projection.
The kernel checks `tf`, and types the projection from the stored `PB2`.
With one parameter stored, it substitutes the index `true` for the binder `b` of the constructor, so the field `h : b = false` gets the type `true = false`.

The kernel replay of this module alone accepts it, because the replay trusts the imports.
The replay of `ForgedInductive` is the one that must fail.
-/

open Lean Elab Command

run_cmd liftCoreM <| addDecl (.thmDecl {
  name := `tf, levelParams := [],
  type := mkApp3 (.const ``Eq [1]) (.const ``Bool []) (.const ``Bool.true []) (.const ``Bool.false []),
  value := .proj `PB2 0 (.const `px []), all := [`tf] })
#check tf

theorem boom : False := Bool.noConfusion tf
#print axioms boom
