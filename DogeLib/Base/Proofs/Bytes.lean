module

public import DogeLib.Base.Bytes

/-!
# Proofs: `Base.Bytes`

Properties of fixed-length byte strings and of `Hash256`.

- `Bytes.ofListExact?_eq_some_iff`: the check accepts a list exactly when it has the length of the type, and returns that list.
- `Bytes.reverse_reverse`: reversing twice gives the original bytes.
- `Hash256.ofDisplayBytes?_displayBytes` and `Hash256.displayBytes_ofDisplayBytes?`: the display order converts to the hash order and back without loss.

Adapted from btc-verified, [`BtcVerified/Serialize/Bytes.lean`](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Bytes.lean),
commit `ecf4f0d`, Copyright 2026 Keagan McClelland, licensed under the Apache License, Version 2.0.
The licence text is in `LICENSES/btc-verified-Apache-2.0.txt`.
The adapted theorems are `Bytes.ofListExact?_eq_some_iff`, `Bytes.val_reverse`, `Bytes.reverse_reverse` and `Bytes.length_val`.
The theorems about `Hash256` are DogeLib's.
The namespace, the module header and the doc comments are DogeLib's.
-/

@[expose] public section

namespace DogeLib.Bytes

/-- A `Bytes n` has `n` bytes. -/
@[simp] theorem length_val {n : Nat} (bs : Bytes n) : bs.val.length = n := bs.property

/-- For every list `bs` and every `out : Bytes n`, `ofListExact? bs = some out` exactly when `bs` has `n` bytes and the bytes of `out` are `bs`. -/
theorem ofListExact?_eq_some_iff {n : Nat} (bs : List UInt8) (out : Bytes n) :
    ofListExact? bs = some out ↔ bs.length = n ∧ out.val = bs := by
  unfold ofListExact?
  split
  · next h =>
    constructor
    · intro he
      simp only [Option.some.injEq] at he
      exact ⟨h, by rw [← he]⟩
    · rintro ⟨-, hv⟩
      exact congrArg some (Subtype.ext hv.symm)
  · next h =>
    constructor
    · intro he; cases he
    · rintro ⟨hl, -⟩; exact absurd hl h

/-- For every `bs : Bytes n`, `ofListExact? bs.val = some bs`. -/
theorem ofListExact?_val {n : Nat} (bs : Bytes n) : ofListExact? bs.val = some bs :=
  (ofListExact?_eq_some_iff bs.val bs).mpr ⟨bs.property, rfl⟩

/-- The bytes of `bs.reverse` are the bytes of `bs`, reversed. -/
@[simp] theorem val_reverse {n : Nat} (bs : Bytes n) : bs.reverse.val = bs.val.reverse := rfl

/-- Reversing twice gives the original bytes. -/
@[simp] theorem reverse_reverse {n : Nat} (bs : Bytes n) : bs.reverse.reverse = bs :=
  Subtype.ext (List.reverse_reverse bs.val)

end DogeLib.Bytes

namespace DogeLib.Hash256

/-- The display bytes of a hash are 32 bytes. -/
theorem length_displayBytes (h : Hash256) : h.displayBytes.length = 32 := by
  rw [displayBytes, List.length_reverse]; exact h.property

/-- Reading the display bytes of a hash gives the hash. -/
theorem ofDisplayBytes?_displayBytes (h : Hash256) : ofDisplayBytes? h.displayBytes = some h := by
  rw [ofDisplayBytes?, displayBytes, List.reverse_reverse]
  exact Bytes.ofListExact?_val h

/-- If `ofDisplayBytes? bs = some h`, then the display bytes of `h` are `bs`. -/
theorem displayBytes_ofDisplayBytes? {bs : List UInt8} {h : Hash256}
    (e : ofDisplayBytes? bs = some h) : h.displayBytes = bs := by
  obtain ⟨-, hv⟩ := (Bytes.ofListExact?_eq_some_iff _ h).mp e
  rw [displayBytes, hv, List.reverse_reverse]

end DogeLib.Hash256
