module

public import DogeLib.Block.VersionBits
public import DogeLib.Block.ProofOfWork
import DogeLib.Block.Proofs.VersionGate
import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the version-bits walk

The two theorems of design record 0010, section 4:

- `csv_never_lockedIn`: on a header chain from the mainnet genesis in which every header passed `checkBlockHeader`, the version-bits state of CSV and SegWit is never `LOCKED_IN` or `ACTIVE`.
  The proof shows that such a header never signals a deployment, so every period has a zero signal count, and a walk with no signals never leaves the states `DEFINED`, `STARTED` and `FAILED`.
- `versionBits_shortcut`: for a chain with no signals, the shortcut equals the full walk at the last boundary, in the two cases that `versionBitsShortcut` resolves.

The signalling argument rests on the version's top three bits.
`Condition` signals only when they are `001`, and a mainnet header that passes `checkBlockHeader` is legacy, with version 1 or 2, or has the chain ID `0x62`.
In both cases the top three bits are `000`.
-/

public section
namespace DogeLib.Block
open DogeLib.Work

/-- `ThresholdState.notLockedIn s` holds when `s` is neither `LOCKED_IN` nor `ACTIVE`. -/
def ThresholdState.notLockedIn (s : ThresholdState) : Prop :=
  s ≠ .lockedIn ∧ s ≠ .active

/-- A non-locked state is `DEFINED`, `STARTED` or `FAILED`. -/
theorem ThresholdState.notLockedIn_cases {s : ThresholdState} (h : s.notLockedIn) :
    s = .defined ∨ s = .started ∨ s = .failed := by
  cases s <;> simp_all [ThresholdState.notLockedIn]

/-- A non-locked state is not `LOCKED_IN`. -/
theorem ThresholdState.notLockedIn.ne_lockedIn {s : ThresholdState} (h : s.notLockedIn) :
    s ≠ .lockedIn := And.left h

/-- A non-locked state is not `ACTIVE`. -/
theorem ThresholdState.notLockedIn.ne_active {s : ThresholdState} (h : s.notLockedIn) :
    s ≠ .active := And.right h

/-- A version whose top-bits test fails does not signal a deployment. -/
theorem versionBitsCondition_false_of_top (v : UInt32) (dep : Deployment)
    (htop : (v &&& versionBitsTopMask == versionBitsTopBits) = false) :
    versionBitsCondition dep v = false := by
  simp only [versionBitsCondition, htop, Bool.false_and]

/--
A mainnet header version with the chain ID `0x62` does not signal a deployment.
The chain ID fixes the version's top three bits to `000`, so `Condition`'s top-bits test fails.
-/
theorem versionBitsCondition_false_of_chainId (v : UInt32) (dep : Deployment)
    (hc : v.toInt32 >>> 16 = (0x62 : Int32)) : versionBitsCondition dep v = false := by
  refine versionBitsCondition_false_of_top v dep ?_
  have hb : v.toInt32.toBitVec = v.toBitVec := rfl
  have key : v.toBitVec.getLsbD 29 = false := by
    have h2 := congrArg (·.toBitVec.getLsbD 13) hc
    simp only [Int32.toBitVec_shiftRight, BitVec.getLsbD_sshiftRight', hb] at h2
    have hsh : ((Int32.toBitVec 16).smod 32).toNat = 16 := by decide
    have hrhs : (Int32.toBitVec 98).getLsbD 13 = false := by decide
    rw [hsh, hrhs] at h2
    simpa using h2
  rw [Bool.eq_false_iff]
  simp only [ne_eq, beq_iff_eq]
  intro heq
  have h29 : v.toBitVec.getLsbD 29 = true := by
    have := congrArg (·.toBitVec.getLsbD 29) heq
    simpa [versionBitsTopMask, versionBitsTopBits, UInt32.toBitVec_and, BitVec.getLsbD_and] using this
  rw [key] at h29; exact absurd h29 (by decide)

/-- A legacy mainnet header version, 1 or 2, does not signal a deployment: its top three bits are `000`. -/
theorem versionBitsCondition_false_of_oneOrTwo (v : UInt32) (dep : Deployment) (hv : v = 1 ∨ v = 2) :
    versionBitsCondition dep v = false :=
  versionBitsCondition_false_of_top v dep (by rcases hv with h | h <;> subst h <;> decide)

/-- `getAuxPowParams .mainnet 0` has a strict chain ID of `0x62`. -/
theorem mainnet_auxpow_strict :
    (getAuxPowParams .mainnet 0).strictChainId = true ∧
      (getAuxPowParams .mainnet 0).auxpowChainId = (0x62 : Int32) := by
  decide

/-- A header that passes mainnet `checkBlockHeader` is legacy or has the chain ID `0x62`. -/
theorem legacy_or_chainId_of_checkBlockHeader (bh : BlockHeader)
    (h : checkBlockHeader .mainnet bh = .ok ()) :
    bh.pure.isLegacy = true ∨ bh.pure.chainId = (0x62 : Int32) := by
  unfold checkBlockHeader checkAuxPowProofOfWork at h
  obtain ⟨hstrict, hid⟩ := mainnet_auxpow_strict
  rw [hstrict, hid] at h
  by_cases hP : (!bh.pure.isLegacy && true && (bh.pure.chainId != (0x62 : Int32))) = true
  · rw [ite_eq_left hP] at h; exact absurd h (by simp)
  · rw [Bool.not_eq_true] at hP
    simp only [Bool.and_true, Bool.and_eq_false_iff] at hP
    rcases hP with hP | hP
    · exact Or.inl (by simpa using hP)
    · exact Or.inr (by simpa using hP)

/-- A mainnet header that passes `checkBlockHeader` does not signal a deployment. -/
@[theorem_tag property]
theorem versionBitsCondition_false_of_checkBlockHeader (bh : BlockHeader) (dep : Deployment)
    (h : checkBlockHeader .mainnet bh = .ok ()) : versionBitsCondition dep bh.pure.nVersion = false := by
  rcases legacy_or_chainId_of_checkBlockHeader bh h with hl | hc
  · exact versionBitsCondition_false_of_oneOrTwo bh.pure.nVersion dep
      (PureBlockHeader.isLegacy_iff bh.pure |>.1 hl)
  · exact versionBitsCondition_false_of_chainId bh.pure.nVersion dep
      (by simpa [PureBlockHeader.chainId, PureBlockHeader.signedVersion] using hc)

/-- One step of the walk keeps a non-locked state non-locked, when the boundary has no signals and the threshold is positive. -/
theorem thresholdStep_notLockedIn (dep : Deployment) (thr : Nat) (s : ThresholdState)
    (b : PeriodBoundary) (hs : s.notLockedIn) (hc : b.conditionCount = 0) (hthr : 0 < thr) :
    (thresholdStep dep thr s b).notLockedIn := by
  have hval : thresholdStep dep thr s b = .defined ∨ thresholdStep dep thr s b = .started ∨
      thresholdStep dep thr s b = .failed := by
    unfold thresholdStep
    by_cases hlt : b.mtp < dep.startTime
    · rw [ite_eq_left hlt]; exact Or.inl rfl
    · rw [ite_eq_right hlt]
      rcases ThresholdState.notLockedIn_cases hs with h | h | h <;> subst h
      · by_cases hto : dep.timeout ≤ b.mtp <;> simp [hto]
      · by_cases hto : dep.timeout ≤ b.mtp
        · simp [hto]
        · simp [hto, show ¬ (thr ≤ b.conditionCount) from by omega]
      · simp
  rcases hval with h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

/-- A fold over boundaries with no signals, from a non-locked state, stays non-locked. -/
theorem foldl_notLockedIn (dep : Deployment) (thr : Nat) (hthr : 0 < thr) :
    ∀ (bs : List PeriodBoundary) (s : ThresholdState), s.notLockedIn →
      (∀ b ∈ bs, b.conditionCount = 0) → (bs.foldl (thresholdStep dep thr) s).notLockedIn
  | [], s, hs, _ => hs
  | b :: bs, s, hs, hc => by
    rw [List.foldl_cons]
    exact foldl_notLockedIn dep thr hthr bs _
      (thresholdStep_notLockedIn dep thr s b hs (hc b (List.mem_cons_self ..)) hthr)
      (fun x hx => hc x (List.mem_cons_of_mem _ hx))

/-- A walk over boundaries with no signals is never `LOCKED_IN` or `ACTIVE`, when the threshold is positive. -/
theorem walk_notLockedIn (dep : Deployment) (thr : Nat) (hthr : 0 < thr) (bs : List PeriodBoundary)
    (hc : ∀ b ∈ bs, b.conditionCount = 0) : (versionBitsWalk dep thr bs).notLockedIn :=
  foldl_notLockedIn dep thr hthr bs .defined ⟨by decide, by decide⟩ hc

/-- Every boundary of a chain whose headers never signal has a zero signal count. -/
theorem chainBoundaries_conditionCount_zero (chain : List BlockHeader) (dep : Deployment)
    (hpass : ∀ bh ∈ chain, versionBitsCondition dep bh.pure.nVersion = false) :
    ∀ b ∈ chainBoundaries dep minerConfirmationWindow
      (chain.map (fun bh => (⟨bh.pure.nVersion, bh.pure.nTime⟩ : VbEntry))), b.conditionCount = 0 := by
  intro b hb
  simp only [chainBoundaries, List.mem_map, List.mem_range] at hb
  obtain ⟨i, _, rfl⟩ := hb
  simp only [signalCount, List.countP_eq_zero]
  intro e he
  have hsub : e ∈ chain.map (fun bh => (⟨bh.pure.nVersion, bh.pure.nTime⟩ : VbEntry)) := by
    have h1 := List.take_subset minerConfirmationWindow _ he
    exact List.drop_subset (i * minerConfirmationWindow) _ h1
  obtain ⟨bh, hbh, rfl⟩ := List.mem_map.1 hsub
  rw [hpass bh hbh]
  exact Bool.false_ne_true

/--
On a header chain from the mainnet genesis in which every header passed `checkBlockHeader`, the version-bits state of a deployment is never `LOCKED_IN` or `ACTIVE`.
`chain` holds the full headers, oldest first.
The median time of each boundary comes from the chain, so the conclusion holds whatever the times are.
An arbitrary supplied index does not meet the hypothesis.
-/
@[theorem_tag property]
theorem csv_never_lockedIn (chain : List BlockHeader)
    (hpass : ∀ bh ∈ chain, checkBlockHeader .mainnet bh = .ok ()) (dep : Deployment) :
    (versionBitsStateFull dep ruleChangeActivationThreshold
      (chain.map (fun bh => (⟨bh.pure.nVersion, bh.pure.nTime⟩ : VbEntry)))).notLockedIn := by
  refine walk_notLockedIn dep ruleChangeActivationThreshold (by decide) _ ?_
  exact chainBoundaries_conditionCount_zero chain dep
    (fun bh hbh => versionBitsCondition_false_of_checkBlockHeader bh dep (hpass bh hbh))

/--
For a chain with no signals, the shortcut resolves the last boundary to the full walk's state.
`bs` are the earlier boundaries and `b` is the last, the aligned boundary.
In case 1 the median is below the start time, and in case 2 it is at or after the timeout.
-/
@[theorem_tag property]
theorem versionBits_shortcut (dep : Deployment) (thr : Nat) (hthr : 0 < thr)
    (bs : List PeriodBoundary) (b : PeriodBoundary) (s : ThresholdState)
    (hc : ∀ x ∈ bs ++ [b], x.conditionCount = 0) (hsc : versionBitsShortcut dep b.mtp = some s) :
    versionBitsWalk dep thr (bs ++ [b]) = s := by
  have hprev : (versionBitsWalk dep thr bs).notLockedIn :=
    walk_notLockedIn dep thr hthr bs (fun x hx => hc x (List.mem_append_left _ hx))
  rw [versionBitsWalk, List.foldl_append]
  show thresholdStep dep thr (versionBitsWalk dep thr bs) b = s
  unfold versionBitsShortcut at hsc
  unfold thresholdStep
  by_cases hlt : b.mtp < dep.startTime
  · rw [ite_eq_left hlt] at hsc ⊢
    exact Option.some.inj hsc
  · rw [ite_eq_right hlt] at hsc ⊢
    by_cases hto : dep.timeout ≤ b.mtp
    · rw [ite_eq_left hto] at hsc
      have hs : s = .failed := (Option.some.inj hsc).symm
      subst hs
      rcases ThresholdState.notLockedIn_cases hprev with h | h | h <;> rw [h] <;> simp [hto]
    · rw [ite_eq_right hto] at hsc; exact absurd hsc (by simp)

end DogeLib.Block
