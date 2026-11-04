module

public import DogeLib.Work.Consensus

/-! Properties of the work projection of Core's consensus tree search. -/

@[expose] public section

namespace DogeLib.Work

/-- At every UInt32 height, the mainnet search selects the legacy work fields below 145000 and DigiShield fields from 145000. -/
theorem getConsensus_mainnet (height : UInt32) :
    getConsensus .mainnet height =
      if height < 145000 then mainnetWorkParams else mainnetDigishieldWorkParams := by
  simp only [getConsensus, consensusTree, ConsensusTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-- At every UInt32 height, testnet selects legacy fields below 145000, DigiShield fields up to 157499, and minimum-difficulty permission from 157500. -/
theorem getConsensus_testnet (height : UInt32) :
    getConsensus .testnet height =
      if height < 145000 then testnetWorkParams
      else if height < 157500 then testnetDigishieldWorkParams
      else testnetMinDifficultyWorkParams := by
  simp only [getConsensus, consensusTree, ConsensusTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

/-- At every UInt32 height, regtest selects legacy work fields below 10 and DigiShield fields from 10. -/
theorem getConsensus_regtest (height : UInt32) :
    getConsensus .regtest height =
      if height < 10 then regtestWorkParams else regtestDigishieldWorkParams := by
  simp only [getConsensus, consensusTree, ConsensusTree.getConsensus]
  repeat (any_goals (first | rfl | (exfalso; simp only [UInt32.lt_iff_toNat_lt, UInt32.reduceToNat] at *; omega) | (split <;> try dsimp only)))

end DogeLib.Work
