module

public import DogeLib.Proposals.Framework.Activation

/-!
# Proofs: `Proposals.Framework.Activation`

- `Activation.isActive_iff`: an activation is active at height `h` on network `n` exactly when `n` has an activation height `h₀` and `h₀ ≤ h`.
- `Activation.none_inactive`: an activation with no height on a network is inactive at every height on it.
- `Activation.isActive_lt`: an activation is inactive at every height below its activation height on the network.
- `Activation.isActive_of_le`: an activation is active at its activation height and at every greater height.
- `Activation.isActive_mono`: if an activation is active at height `h` on a network, it is active at every greater height on that network.

The last three give the activation obligation of design record 0007, section 8.3, for the fixed-height model.
The model is false below the activation point, and monotone above it.
These theorems are statements about the definitions. They say nothing about any network.
-/

@[expose] public section

namespace DogeLib.Proposals.Framework

open DogeLib.Work

/-- For every activation `a`, network `n` and height `h`: `a` is active at `h` on `n` exactly when `n` has an activation height at most `h`. -/
theorem Activation.isActive_iff (a : Activation) (n : WorkNetwork) (h : Nat) :
    a.isActive n h = true ↔ ∃ h₀, a.height n = some h₀ ∧ h₀ ≤ h := by
  unfold Activation.isActive
  cases a.height n <;> simp

/-- For every activation `a` with no activation height on network `n`, and every height `h`: `a` is inactive at `h` on `n`. -/
theorem Activation.none_inactive {a : Activation} {n : WorkNetwork} (hn : a.height n = none) (h : Nat) :
    a.isActive n h = false := by
  simp [Activation.isActive, hn]

/-- For every activation `a` with activation height `h₀` on network `n`, and every height `h < h₀`: `a` is inactive at `h` on `n`. -/
theorem Activation.isActive_lt {a : Activation} {n : WorkNetwork} {h₀ h : Nat} (hn : a.height n = some h₀)
    (hlt : h < h₀) : a.isActive n h = false := by
  simp only [Activation.isActive, hn, decide_eq_false_iff_not, Nat.not_le]
  exact hlt

/-- For every activation `a` with activation height `h₀` on network `n`, and every height `h ≥ h₀`: `a` is active at `h` on `n`. -/
theorem Activation.isActive_of_le {a : Activation} {n : WorkNetwork} {h₀ h : Nat} (hn : a.height n = some h₀)
    (hle : h₀ ≤ h) : a.isActive n h = true := by
  simp only [Activation.isActive, hn, decide_eq_true_eq]
  exact hle

/-- For every activation `a`, network `n` and heights `h ≤ h'`: if `a` is active at `h` on `n`, it is active at `h'` on `n`. -/
theorem Activation.isActive_mono {a : Activation} {n : WorkNetwork} {h h' : Nat} (hact : a.isActive n h = true)
    (hle : h ≤ h') : a.isActive n h' = true := by
  obtain ⟨h₀, hn, h₀le⟩ := (Activation.isActive_iff a n h).mp hact
  exact Activation.isActive_of_le hn (Nat.le_trans h₀le hle)

end DogeLib.Proposals.Framework
