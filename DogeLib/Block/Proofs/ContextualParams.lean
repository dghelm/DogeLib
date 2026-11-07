module

public import DogeLib.Block.ContextualParams

/-!
# Properties of contextual parameters and checkpoints

The theorems characterize `getContextualParams` and `lastCheckpoint` (design record 0006, stage 2).

- `getContextualParams_mainnet`, `_testnet` and `_regtest`: the record that the search selects at every UInt32 height.
- `allowLegacyBlocks_getConsensus`: the selected `fAllowLegacyBlocks` is false exactly from the AuxPoW activation height of the network.
- `ContextualParams.bipHeights_records`, `bip65Height_getConsensus` and `bip66Height_getConsensus`: every record of a network has the same `BIP65Height` and `BIP66Height`.
- `getContextualParams_eq_work`: the search selects the record with the effective height that `Work.consensusTree` selects.
- `checkpointHeights_sorted`: each checkpoint table has strictly increasing heights.
- `lastCheckpoint_eq`, `lastCheckpoint_eq_some_iff` and `lastCheckpoint_eq_none_iff`: the greatest table height in the known set, or `none`.

The theorems are about the transcribed records and tables.
A transcription mistake would make them claims about the wrong values (SOUNDNESS.md, A1).
-/

@[expose] public section
namespace DogeLib.Block

/-! ## Records by height -/

/-- At every UInt32 height, the mainnet search selects `consensus` below 145000, `digishieldConsensus` below 371337, and `auxpowConsensus` from 371337. -/
theorem getContextualParams_mainnet (height : UInt32) :
    getContextualParams .mainnet height =
      if height < 145000 then mainnetContextualParams
      else if height < 371337 then mainnetDigishieldContextualParams
      else mainnetAuxpowContextualParams := by
  simp only [getContextualParams, contextualTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/--
At every UInt32 height, the testnet search selects `consensus` below 145000, `digishieldConsensus` below 157500, `minDifficultyConsensus` below 158100, and `auxpowConsensus` from 158100.
-/
theorem getContextualParams_testnet (height : UInt32) :
    getContextualParams .testnet height =
      if height < 145000 then testnetContextualParams
      else if height < 157500 then testnetDigishieldContextualParams
      else if height < 158100 then testnetMinDifficultyContextualParams
      else testnetAuxpowContextualParams := by
  simp only [getContextualParams, contextualTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-- At every UInt32 height, the regtest search selects `consensus` below 10, `digishieldConsensus` below 20, and `auxpowConsensus` from 20. -/
theorem getContextualParams_regtest (height : UInt32) :
    getContextualParams .regtest height =
      if height < 10 then regtestContextualParams
      else if height < 20 then regtestDigishieldContextualParams
      else regtestAuxpowContextualParams := by
  simp only [getContextualParams, contextualTree, ParamsTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/--
For every network and UInt32 height, the selected `fAllowLegacyBlocks` is false exactly when the height is at least the AuxPoW activation height.
The activation heights are 371337 on mainnet, 158100 on testnet and 20 on regtest (D14, lines 135, 298 and 432).
Below them, the selected field is true.
-/
theorem allowLegacyBlocks_getConsensus (network : Work.WorkNetwork) (height : UInt32) :
    (getContextualParams network height).allowLegacyBlocks = false ↔
      match network with
      | .mainnet => 371337 ≤ height
      | .testnet => 158100 ≤ height
      | .regtest => 20 ≤ height := by
  cases network <;>
    simp only [getContextualParams_mainnet, getContextualParams_testnet, getContextualParams_regtest] <;>
    repeat (any_goals (first
      | (split <;> try dsimp only)
      | (simp only [mainnetContextualParams, mainnetDigishieldContextualParams, mainnetAuxpowContextualParams,
          testnetContextualParams, testnetDigishieldContextualParams, testnetMinDifficultyContextualParams,
          testnetAuxpowContextualParams, regtestContextualParams, regtestDigishieldContextualParams,
          regtestAuxpowContextualParams, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat,
          Bool.true_eq_false, false_iff, true_iff, Nat.not_le] at *; omega)))

/-! ## `BIP65Height` and `BIP66Height` -/

/--
For every network, every record of its tree has the `BIP65Height` and `BIP66Height` of the height-zero record.
Each Core record is a copy of the previous one, and no copy changes either field (design record 0006, item 3).
-/
theorem ContextualParams.bipHeights_records (network : Work.WorkNetwork) :
    ∀ r ∈ (contextualTree network).records,
      r.2.bip65Height = (getContextualParams network 0).bip65Height ∧
        r.2.bip66Height = (getContextualParams network 0).bip66Height := by
  cases network <;> decide

/--
For every network and UInt32 height, the selected `BIP65Height` is 3464751 on mainnet, 1854705 on testnet and 1351 on regtest (D14, lines 86, 246 and 390).
-/
theorem bip65Height_getConsensus (network : Work.WorkNetwork) (height : UInt32) :
    (getContextualParams network height).bip65Height =
      match network with
      | .mainnet => 3464751
      | .testnet => 1854705
      | .regtest => 1351 := by
  cases network <;>
    simp only [getContextualParams_mainnet, getContextualParams_testnet, getContextualParams_regtest] <;>
    repeat (any_goals (first | rfl | (split <;> try dsimp only)))

/--
For every network and UInt32 height, the selected `BIP66Height` is 1034383 on mainnet, 708658 on testnet and 1251 on regtest (D14, lines 87, 247 and 391).
-/
theorem bip66Height_getConsensus (network : Work.WorkNetwork) (height : UInt32) :
    (getContextualParams network height).bip66Height =
      match network with
      | .mainnet => 1034383
      | .testnet => 708658
      | .regtest => 1251 := by
  cases network <;>
    simp only [getContextualParams_mainnet, getContextualParams_testnet, getContextualParams_regtest] <;>
    repeat (any_goals (first | rfl | (split <;> try dsimp only)))

/-! ## Agreement with the work projection -/

/--
For every network and UInt32 height, the contextual search and `Work.ConsensusTree.getConsensus` select a record with the same effective height.
So the contextual projection selects the same Core record as the work projection.
-/
theorem getContextualParams_eq_work (network : Work.WorkNetwork) (height : UInt32) :
    ((contextualTree network).getConsensus height).1 = ((Work.consensusTree network).getConsensus height).1 := by
  cases network <;>
    simp only [contextualTree, Work.consensusTree, ParamsTree.getConsensus, Work.ConsensusTree.getConsensus] <;>
    repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-! ## Checkpoints -/

/-- For every network, the heights of the checkpoint table increase strictly, so the list order is the key order of Core's `std::map`. -/
theorem checkpointHeights_sorted (network : Work.WorkNetwork) :
    (checkpointHeights network).Pairwise (· < ·) := by
  cases network <;> decide

/-- Let `l` be a strictly increasing list of natural numbers, and `p` a predicate.
The first element of `l.reverse` that satisfies `p` is the greatest element of `l` that satisfies `p`. -/
theorem find?_reverse_eq_max?_filter (l : List Nat) (p : Nat → Bool) (hl : l.Pairwise (· < ·)) :
    l.reverse.find? p = (l.filter p).max? := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.pairwise_cons] at hl
    rw [List.reverse_cons, List.find?_append, ih hl.2, List.filter_cons]
    cases hp : p a
    · simp [hp]
    · cases hm : (t.filter p).max? with
      | none =>
        rw [List.max?_eq_none_iff] at hm
        simp [hp, hm]
      | some m =>
        have hmem : m ∈ t := (List.mem_filter.mp (List.max?_mem hm)).1
        have hlt : a < m := hl.1 m hmem
        simp [hp, List.max?_cons, hm, Nat.max_eq_right (Nat.le_of_lt hlt)]

/--
For every network, enabled flag and list of known heights, `lastCheckpoint` is `none` when checkpoints are disabled.
Otherwise it is the greatest table height in the known list, or `none` if the list contains no table height.
-/
theorem lastCheckpoint_eq (network : Work.WorkNetwork) (enabled : Bool) (known : List Nat) :
    lastCheckpoint network enabled known =
      if enabled then ((checkpointHeights network).filter (fun h => known.contains h)).max? else none := by
  unfold lastCheckpoint
  split
  · rw [← find?_reverse_eq_max?_filter _ _ (checkpointHeights_sorted network), checkpointHeights,
      ← List.map_reverse, List.find?_map]
    rfl
  · rfl

/--
For every network, flag, known list and height `h`, `lastCheckpoint` returns `h` exactly when three conditions hold.
Checkpoints are enabled, `h` is a table height in the known list, and no greater table height is in the known list.
-/
theorem lastCheckpoint_eq_some_iff (network : Work.WorkNetwork) (enabled : Bool) (known : List Nat) (h : Nat) :
    lastCheckpoint network enabled known = some h ↔
      enabled = true ∧ h ∈ checkpointHeights network ∧ h ∈ known ∧
        ∀ h' ∈ checkpointHeights network, h' ∈ known → h' ≤ h := by
  rw [lastCheckpoint_eq]
  cases enabled
  · simp
  · simp only [ite_true, List.max?_eq_some_iff, List.mem_filter, List.contains_iff_mem, true_and]
    constructor
    · rintro ⟨⟨hm, hk⟩, hmax⟩
      exact ⟨hm, hk, fun h' hm' hk' => hmax h' ⟨hm', hk'⟩⟩
    · rintro ⟨hm, hk, hmax⟩
      exact ⟨⟨hm, hk⟩, fun h' ⟨hm', hk'⟩ => hmax h' hm' hk'⟩

/--
For every network, flag and known list, `lastCheckpoint` returns `none` exactly in two cases.
Checkpoints are disabled, or the known list contains no table height.
In both cases, check 4 of `ContextualCheckBlockHeader` cannot reject.
-/
theorem lastCheckpoint_eq_none_iff (network : Work.WorkNetwork) (enabled : Bool) (known : List Nat) :
    lastCheckpoint network enabled known = none ↔
      enabled = false ∨ ∀ h ∈ checkpointHeights network, h ∉ known := by
  rw [lastCheckpoint_eq]
  cases enabled
  · simp
  · simp [List.max?_eq_none_iff, List.filter_eq_nil_iff]

end DogeLib.Block
