module

public import DogeLib.Block.VersionGate

/-!
# Properties of version gating

The theorems characterize `PureBlockHeader.isLegacy` and `checkVersion` (design record 0004, stage 4b).

- `PureBlockHeader.isLegacy_iff`: a version is legacy exactly when its bits are 1 or 2.
- `PureBlockHeader.isAuxpow_eq_false_of_isLegacy`: a legacy version has a clear AuxPoW flag.
- `checkVersion_eq_ok_iff`, `checkVersion_eq_lateLegacyBlock_iff` and `checkVersion_eq_earlyAuxpowBlock_iff`: the condition for each result.
- `checkVersion_congr_nVersion`: the result depends on the header only through `nVersion`.

The theorems say nothing about which record a caller supplies for a height.
-/

@[expose] public section
namespace DogeLib.Block

/-- For all version bits `v` and `w`, their signed interpretations are equal exactly when the bits are equal. -/
theorem UInt32.toInt32_inj (v w : UInt32) : v.toInt32 = w.toInt32 ↔ v = w := by
  constructor
  · intro h; simpa using congrArg Int32.toUInt32 h
  · rintro rfl; rfl

/--
For every pure header, `isLegacy` holds exactly when the version bits are 1 or 2.
So the chain ID test of Core's `IsLegacy` never changes its result.
-/
theorem PureBlockHeader.isLegacy_iff (h : PureBlockHeader) :
    h.isLegacy = true ↔ h.nVersion = 1 ∨ h.nVersion = 2 := by
  obtain ⟨v, _, _, _, _, _⟩ := h
  have h1 : (1 : Int32) = (1 : UInt32).toInt32 := rfl
  have h2 : (2 : Int32) = (2 : UInt32).toInt32 := rfl
  simp only [isLegacy, signedVersion, chainId, h1, h2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    UInt32.toInt32_inj]
  constructor
  · rintro (hv | ⟨hv, _⟩) <;> simp [hv]
  · rintro (hv | hv)
    · exact .inl hv
    · subst hv; exact .inr ⟨rfl, by decide⟩

/-- For every pure header with a legacy version, the AuxPoW flag is clear. -/
theorem PureBlockHeader.isAuxpow_eq_false_of_isLegacy (h : PureBlockHeader) (hl : h.isLegacy = true) :
    h.isAuxpow = false := by
  rcases (PureBlockHeader.isLegacy_iff h).1 hl with hv | hv <;> (simp only [isAuxpow, hv]; decide)

/--
For every record and pure header, `checkVersion` accepts exactly when both checks pass.
If the record does not allow legacy blocks, the version is not legacy.
If the record allows legacy blocks, the AuxPoW flag is clear.
-/
theorem checkVersion_eq_ok_iff (p : VersionGateParams) (h : PureBlockHeader) :
    checkVersion p h = .ok () ↔
      (p.allowLegacyBlocks = false → h.isLegacy = false) ∧
      (p.allowLegacyBlocks = true → h.isAuxpow = false) := by
  unfold checkVersion
  cases p.allowLegacyBlocks <;> cases h.isLegacy <;> cases h.isAuxpow <;> simp

/-- For every record and pure header, `checkVersion` rejects as `late-legacy-block` exactly when the record does not allow legacy blocks and the version is legacy. -/
theorem checkVersion_eq_lateLegacyBlock_iff (p : VersionGateParams) (h : PureBlockHeader) :
    checkVersion p h = .error .lateLegacyBlock ↔ p.allowLegacyBlocks = false ∧ h.isLegacy = true := by
  unfold checkVersion
  cases p.allowLegacyBlocks <;> cases h.isLegacy <;> cases h.isAuxpow <;> simp

/-- For every record and pure header, `checkVersion` rejects as `early-auxpow-block` exactly when the record allows legacy blocks and the AuxPoW flag is set. -/
theorem checkVersion_eq_earlyAuxpowBlock_iff (p : VersionGateParams) (h : PureBlockHeader) :
    checkVersion p h = .error .earlyAuxpowBlock ↔ p.allowLegacyBlocks = true ∧ h.isAuxpow = true := by
  unfold checkVersion
  cases p.allowLegacyBlocks <;> cases h.isLegacy <;> cases h.isAuxpow <;> simp

/-- For every record and every two pure headers with the same version bits, `checkVersion` gives the same result. -/
theorem checkVersion_congr_nVersion (p : VersionGateParams) (h h' : PureBlockHeader)
    (hv : h.nVersion = h'.nVersion) : checkVersion p h = checkVersion p h' := by
  simp [checkVersion, PureBlockHeader.isLegacy, PureBlockHeader.chainId, PureBlockHeader.signedVersion,
    PureBlockHeader.isAuxpow, hv]

end DogeLib.Block
