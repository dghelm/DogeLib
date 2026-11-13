module

public import Lean.Attributes
public import Lean.OriginalConstKind

/-!
# Theorem tags
-/

public section
namespace DogeLib

/-- The kind of a cited theorem. -/
inductive TheoremTag where
  | property
  | modelAgreement
  | refinement
  | characterization
  | witness
  deriving Inhabited, BEq, Repr

/-- `@[theorem_tag kind]` records the kind of a cited theorem. -/
syntax (name := theoremTag) "theorem_tag " ident : attr

open Lean in
initialize
  discard <| registerParametricAttribute (α := TheoremTag) {
    name := `theoremTag
    descr := "the kind of a cited theorem"
    getParam := fun decl stx => do
      unless wasOriginallyTheorem (← getEnv) decl do
        throwError "theorem_tag applies only to a theorem"
      match stx with
      | `(attr| theorem_tag $kind:ident) =>
        match kind.getId with
        | `property => return .property
        | `model_agreement => return .modelAgreement
        | `refinement => return .refinement
        | `characterization => return .characterization
        | `witness => return .witness
        | other => throwError "unknown theorem tag {other}"
      | _ => throwError "unexpected theorem_tag syntax"
  }

end DogeLib
