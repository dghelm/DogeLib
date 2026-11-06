module

/-!
# `CheckDeclsTest.Exports`

An export module: it may reach `IO`, which the specification may not.

Adapted from EthLib, `scripts/CheckDeclsTest/Exports.lean` at commit `bb6dfe5`, dedicated to the public domain under CC0 1.0.
-/

@[expose] public section

namespace CheckDeclsTest.Exports

/-- Reads and writes a mutable reference, as the C exports may. -/
def roundTrip (n : Nat) : IO Nat := do
  let r ← IO.mkRef n
  r.get

end CheckDeclsTest.Exports
