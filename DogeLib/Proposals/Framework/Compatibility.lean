module

public import DogeLib.Proposals.Framework.Script

/-!
# `Proposals.Framework.Compatibility`

The compatibility classes of a proposed revision, and the legacy projection.
Design record 0007, section 8 and decisions 5 and 6, sets the contract.

## Shapes

Let `baseline : κ → β` be a baseline check and `revised : Bool → κ → ρ` its revision, where the `Bool` is `active`.
`κ` holds every other argument: the checker, the flags, the scripts, the network, the view and the times.
`verdictB : β → Verdict` and `verdictR : ρ → Verdict` say whether a result accepts, rejects, or reports an unsupported capability.
`embed : β → ρ` maps a baseline result into the result type of the revision.

| Shape | Statement |
| --- | --- |
| `InactiveEq` | `revised false ctx = embed (baseline ctx)` for every `ctx`. Every result agrees: acceptance, each rejection and each unsupported capability. |
| `RestrictsAcceptance` | For every `active` and `ctx`, if the revision accepts, the baseline accepts. |
| `StrictnessWitness` | One `ctx` where the baseline accepts and the active revision rejects. A change of error, or an unsupported result, is not a witness. |
| `UseWitness` | One `ctx` where the active revision accepts and the predicate `runs` holds. `runs` says that the redefined rule runs. |
| `ExtendsAcceptance` | For every `ctx`, if the baseline accepts, the active revision accepts. |
| `RelaxationWitness` | One `ctx` where the active revision accepts and the baseline rejects. |

## Classes

Every class includes the inactive equality.

- `SoftFork`: restriction of acceptance, a strictness witness and a use witness.
  A revision that rejects every input restricts acceptance, so the two witnesses are required.
- `Relaxation`: a hard fork that only adds acceptance. Extension of acceptance and a relaxation witness.
- `Incompatible`: a strictness witness and a relaxation witness.
- `Unclassified`: the inactive equality only.

## Labels

A theorem about `evalScript`, `verifyScript` or `verifyLegacySpend` is *Script-local*.
A theorem about a header check is *header-local*.
A Script-local soft-fork theorem is not a soft-fork claim about the network.
The full claim also needs block validity, a block-level activation and a legacy projection, as design record 0007, section 8.3, lists.
COVERAGE.md and the documentation of each proposal module use these labels.

## Legacy projection

A `LegacyProjection` has two maps.
One maps each message of the revised protocol to the message that a baseline node receives.
The other maps the chain state of a revised node to that of a baseline node.
A revision that changes no encoding and no state effect has `LegacyProjection.identity`.
A non-identity projection waits for the first proposal that needs one, and that proposal's design record defines it.

DogeLib has no block validity yet, so no block-level or chain-level theorem uses a projection.
The worked example `ExampleVersionVerify` states Script-local theorems with the identity projection.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Script

/-- The verdict of a check: it accepts, it rejects, or it needs a capability that the specification lacks. -/
inductive Verdict where
  /-- The check accepts. -/
  | accepted
  /-- The check rejects, with any error. -/
  | rejected
  /-- The check needs a capability that the specification lacks. The result says nothing about Core's verdict. -/
  | unsupported
  deriving DecidableEq, Repr

/-- The verdict of a baseline `VerifyScript` result. -/
def baselineVerdict : VerifyResult → Verdict
  | .accepted => .accepted
  | .rejected _ => .rejected
  | .unsupported _ => .unsupported

/-- The verdict of a framework `VerifyScript` result. -/
def VerifyOutcome.verdict {ε : Type} : VerifyOutcome ε → Verdict
  | .accepted => .accepted
  | .rejected _ => .rejected
  | .unsupported _ => .unsupported

/-- The verdict of a check that returns `.ok ()` or an error, such as `Block.checkVersion` and `Block.checkBlockHeader`. -/
def verdictOfExcept {ε : Type} : Except ε Unit → Verdict
  | .ok () => .accepted
  | .error _ => .rejected

section

variable {κ β ρ : Type}

/-- The inactive equality: with `active` false, the revision equals the embedded baseline result in every context. -/
def InactiveEq (embed : β → ρ) (baseline : κ → β) (revised : Bool → κ → ρ) : Prop :=
  ∀ ctx, revised false ctx = embed (baseline ctx)

/-- Restriction of acceptance: for every `active` and context, if the revision accepts, the baseline accepts. -/
def RestrictsAcceptance (verdictB : β → Verdict) (verdictR : ρ → Verdict) (baseline : κ → β)
    (revised : Bool → κ → ρ) : Prop :=
  ∀ active ctx, verdictR (revised active ctx) = .accepted → verdictB (baseline ctx) = .accepted

/-- Extension of acceptance: for every context, if the baseline accepts, the active revision accepts. -/
def ExtendsAcceptance (verdictB : β → Verdict) (verdictR : ρ → Verdict) (baseline : κ → β)
    (revised : Bool → κ → ρ) : Prop :=
  ∀ ctx, verdictB (baseline ctx) = .accepted → verdictR (revised true ctx) = .accepted

/-- A strictness witness: a context where the baseline accepts and the active revision rejects. -/
def StrictnessWitness (verdictB : β → Verdict) (verdictR : ρ → Verdict) (baseline : κ → β)
    (revised : Bool → κ → ρ) : Prop :=
  ∃ ctx, verdictB (baseline ctx) = .accepted ∧ verdictR (revised true ctx) = .rejected

/-- A relaxation witness: a context where the active revision accepts and the baseline rejects. -/
def RelaxationWitness (verdictB : β → Verdict) (verdictR : ρ → Verdict) (baseline : κ → β)
    (revised : Bool → κ → ρ) : Prop :=
  ∃ ctx, verdictR (revised true ctx) = .accepted ∧ verdictB (baseline ctx) = .rejected

/-- A use witness: a context where the active revision accepts and the redefined rule runs, as the predicate `runs` states. -/
def UseWitness (verdictR : ρ → Verdict) (revised : Bool → κ → ρ) (runs : κ → Prop) : Prop :=
  ∃ ctx, verdictR (revised true ctx) = .accepted ∧ runs ctx

/-- A soft fork at the level of one check: the inactive equality, restriction of acceptance, a strictness witness and a use witness. -/
structure SoftFork (embed : β → ρ) (verdictB : β → Verdict) (verdictR : ρ → Verdict) (runs : κ → Prop)
    (baseline : κ → β) (revised : Bool → κ → ρ) : Prop where
  /-- With `active` false, the revision equals the baseline. -/
  inactive_eq : InactiveEq embed baseline revised
  /-- Every input that the revision accepts, the baseline accepts. -/
  restricts : RestrictsAcceptance verdictB verdictR baseline revised
  /-- The active revision rejects an input that the baseline accepts. -/
  strict : StrictnessWitness verdictB verdictR baseline revised
  /-- The active revision accepts an input on which the redefined rule runs. -/
  use : UseWitness verdictR revised runs

/-- A relaxation at the level of one check: the inactive equality, extension of acceptance and a relaxation witness. -/
structure Relaxation (embed : β → ρ) (verdictB : β → Verdict) (verdictR : ρ → Verdict)
    (baseline : κ → β) (revised : Bool → κ → ρ) : Prop where
  /-- With `active` false, the revision equals the baseline. -/
  inactive_eq : InactiveEq embed baseline revised
  /-- Every input that the baseline accepts, the active revision accepts. -/
  extends_acceptance : ExtendsAcceptance verdictB verdictR baseline revised
  /-- The active revision accepts an input that the baseline rejects. -/
  relaxed : RelaxationWitness verdictB verdictR baseline revised

/-- An incompatible change at the level of one check: the inactive equality and a witness in each direction. -/
structure Incompatible (embed : β → ρ) (verdictB : β → Verdict) (verdictR : ρ → Verdict)
    (baseline : κ → β) (revised : Bool → κ → ρ) : Prop where
  /-- With `active` false, the revision equals the baseline. -/
  inactive_eq : InactiveEq embed baseline revised
  /-- The active revision rejects an input that the baseline accepts. -/
  strict : StrictnessWitness verdictB verdictR baseline revised
  /-- The active revision accepts an input that the baseline rejects. -/
  relaxed : RelaxationWitness verdictB verdictR baseline revised

/-- An unclassified revision: the inactive equality only. -/
def Unclassified (embed : β → ρ) (baseline : κ → β) (revised : Bool → κ → ρ) : Prop :=
  InactiveEq embed baseline revised

end

/--
A legacy projection, design record 0007, section 8.4.
`message` maps a message of the revised protocol to the message that a baseline node receives.
`state` maps the chain state of a revised node to that of a baseline node.
-/
structure LegacyProjection (Message₁ Message₀ State₁ State₀ : Type) where
  /-- The message that a baseline node receives, such as a block or a transaction. -/
  message : Message₁ → Message₀
  /-- The chain state of a baseline node. -/
  state : State₁ → State₀

/-- The identity projection, for a revision that changes no encoding and no state effect. -/
def LegacyProjection.identity (Message State : Type) : LegacyProjection Message Message State State :=
  { message := id, state := id }

end DogeLib.Proposals.Framework
