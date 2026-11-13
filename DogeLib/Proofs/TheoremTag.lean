module

public import Lean.Attributes
public import Lean.OriginalConstKind

/-!
# Theorem tags

The attribute `theorem_tag` labels a theorem that a document cites as evidence, such as COVERAGE.md or SOUNDNESS.md.
A tag says what kind of evidence the theorem is.
A theorem with no tag is internal: a step of another proof.

```text
@[theorem_tag property]
theorem uniformInt_preimages : …
```

The five tags are the constructors of `TheoremTag`.
A statement is a *property* only if it passes two tests.
It is false for at least one plausible wrong definition.
Its proof is more than a simplification of the definition.
A statement that restates a definition as a predicate is a *characterization*.

The attribute checks that the tag is one of the five names and that the declaration is a theorem.
It records the tag in an environment extension, so that a later tool can list the tagged theorems from the compiled library.
It checks nothing else. In particular, it does not show that a tag describes its theorem.

A module that uses the attribute needs `import DogeLib.Proofs.TheoremTag` for the syntax and `meta import DogeLib.Proofs.TheoremTag` for the handler, which Lean runs when it elaborates the theorem.
The initializer below has no name, so this module declares no opaque constant.
-/

public section
namespace DogeLib

/-- The kind of evidence that a cited theorem gives. -/
inductive TheoremTag where
  /-- A consequence of the definitions that their author did not write into them. -/
  | property
  /-- An executable definition equals a separately written model or relation. -/
  | modelAgreement
  /-- Another implementation equals the definition. -/
  | refinement
  /-- A definition restated as a predicate. -/
  | characterization
  /-- A concrete instance or counterexample, often by kernel computation. -/
  | witness
  deriving Inhabited, BEq, Repr

/--
`@[theorem_tag kind]` records the kind of a cited theorem.
`kind` is `property`, `model_agreement`, `refinement`, `characterization` or `witness`.
-/
syntax (name := theoremTag) "theorem_tag " ident : attr

open Lean in
initialize
  discard <| registerParametricAttribute (α := TheoremTag) {
    name := `theoremTag
    descr := "the kind of evidence that a cited theorem gives"
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
        | other => throwError "unknown theorem tag {other}: use property, model_agreement, refinement, characterization or witness"
      | _ => throwError "unexpected theorem_tag syntax"
  }

end DogeLib
