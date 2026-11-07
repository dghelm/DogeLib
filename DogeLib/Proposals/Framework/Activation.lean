module

public import DogeLib.Work.Consensus

/-!
# `Proposals.Framework.Activation`

The activation model of a proposed revision.
Design record 0007, section 7 and decision 4, sets the contract.

## Rule level

Each revised definition takes an argument `active : Bool`.
The argument is separate from Core's flag set, so `supportedFlags` and `unsupportedFlagBits` keep their meaning.
A rule-level theorem is stated for both values of `active`, or for every value.
This module defines nothing for the rule level.

## Block level

`Activation` gives each network one activation height, or none.
`Activation.isActive a n h` is true when network `n` has an activation height `h₀` and `h₀ ≤ h`.
The height `h` is the height of the block that contains the transaction, `pindex->nHeight` in `ConnectBlock`.
For a header check, it is the candidate height of design record 0006: the height of the first view entry plus one.

No proposal is active on any network, so there is no default `Activation` value.
A consumer supplies one, and every theorem is stated for every `Activation`.
`DogeLib.Proposals.Framework.Proofs.Activation` proves that the model is false below the activation height and monotone above it.

The model has no version-bit signalling. Design record 0007, section 7.4, says what a signalling model needs.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Work

/-- The block-level activation of one proposed revision: an activation height for each network, or `none` for a network where the revision is never active. -/
structure Activation where
  /-- The first height at which the revision is active on the network, or `none`. -/
  height : WorkNetwork → Option Nat

/-- Whether the revision is active at height `h` on network `n`: the network has an activation height `h₀`, and `h₀ ≤ h`. -/
def Activation.isActive (a : Activation) (n : WorkNetwork) (h : Nat) : Bool :=
  match a.height n with
  | none => false
  | some h₀ => decide (h₀ ≤ h)

end DogeLib.Proposals.Framework
