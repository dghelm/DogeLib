module

/-!
# `CheckDeclsForeign`

Declarations from outside the checked scope, as a dependency would provide them.
The fixtures in `CheckDeclsTest` use them, and the check must still see what they bring in.

Adapted from EthLib, `scripts/CheckDeclsForeign.lean` at commit `bb6dfe5`, dedicated to the public domain under CC0 1.0.
`U`, `P`, `Cycle`, `Left` and `Right` are adapted from EthLib commit `1f13f422`, also under CC0 1.0.
-/

@[expose] public section

namespace CheckDeclsForeign

/-- An axiom of a dependency. -/
axiom T : Type

/-- A second axiom of a dependency, used only through `Cycle`, `Right` and `Second`. -/
axiom U : Type

/-- A proposition of a dependency that holds only if its axiom has an element. -/
def P : Prop := Nonempty U

/-- An inductive type of a dependency whose constructor carries its axiom, through `P`.
The type inherits the axiom from its constructor, which takes a proof of `P`. -/
inductive Cycle where
  | mk (h : P)

mutual

/-- An inductive type of a dependency, declared with `Right`, whose own constructor is plain. -/
inductive Left where
  | a

/-- The other type of the declaration, whose constructor carries the axiom through `P`. -/
inductive Right where
  | b (h : P)

end

/-- An opaque constant of a dependency. -/
opaque hiddenNat : Nat

end CheckDeclsForeign
