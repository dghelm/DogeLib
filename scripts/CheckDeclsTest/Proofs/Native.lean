module

/-!
# `CheckDeclsTest.Proofs.Native`

A proof module: its `native_decide` is a finding, which a baseline may allow.

Adapted from EthLib, `scripts/CheckDeclsTest/Proofs/Native.lean` at commit `bb6dfe5`, dedicated to the public domain under CC0 1.0.
-/

@[expose] public section

namespace CheckDeclsTest.Proofs.Native

/-- A known answer the compiled code decides. -/
-- Keep the private owner distinct from the public native theorem in `Bad`.
private theorem big : 2 ^ 20 = 1048576 := by native_decide

end CheckDeclsTest.Proofs.Native
