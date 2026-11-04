module

public import DogeLib.Work.ArithUint256Bytes
public import DogeLib.Work.Consensus
public import DogeLib.Work.Proofs.ArithUint256Words

/-! # Arithmetic meaning of grouped byte reads and network powLimit literals -/

@[expose] public section

namespace DogeLib.Work.ArithUint256

/-- Every four-byte read fits exactly in a word, for every byte array and group index. -/
theorem Words.readLE32_toNat (bs : TargetBytes) (i : Fin 8) :
    (Words.readLE32 bs i).toNat =
      (bs ⟨4 * i.val, by omega⟩).toNat +
      256 * (bs ⟨4 * i.val + 1, by omega⟩).toNat +
      65536 * (bs ⟨4 * i.val + 2, by omega⟩).toNat +
      16777216 * (bs ⟨4 * i.val + 3, by omega⟩).toNat := by
  have h0 := (bs ⟨4 * i.val, by omega⟩).toNat_lt
  have h1 := (bs ⟨4 * i.val + 1, by omega⟩).toNat_lt
  have h2 := (bs ⟨4 * i.val + 2, by omega⟩).toNat_lt
  have h3 := (bs ⟨4 * i.val + 3, by omega⟩).toNat_lt
  simp only [Words.readLE32, UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega)]

/-- For every 32-byte input, the eight grouped reads equal the independent radix-256 interpretation. -/
theorem Words.uintToArith256_value (bs : TargetBytes) :
    Words.value (Words.uintToArith256 bs) = evalBytes 32 bs := by
  simp only [Words.value, Words.eval, Words.uintToArith256, Words.readLE32_toNat, evalBytes,
    Fin.val_zero, Fin.succ, Fin.zero_eta, Nat.reduceMod, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.reduceMul]
  omega

/-- For every 32-byte input, word conversion agrees with its arithmetic byte interpretation. -/
theorem Words.uintToArith256_toArith (bs : TargetBytes) :
    Words.toArith (Words.uintToArith256 bs) = ofTargetBytes bs := by
  simp only [Words.toArith, ofTargetBytes, Words.uintToArith256_value]

/-- Core's mainnet literal converts to the existing pre-DigiShield powLimit. -/
theorem mainnet_powLimit_literal :
    (targetBytesOfHex mainnetPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some mainnetWorkParams.powLimit := by decide +kernel

/-- Core copies the mainnet powLimit into its DigiShield and AuxPoW records. -/
theorem mainnet_digishield_powLimit_literal :
    (targetBytesOfHex mainnetPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some mainnetDigishieldWorkParams.powLimit := by decide +kernel

/-- Core's testnet literal converts to the existing base powLimit. -/
theorem testnet_powLimit_literal :
    (targetBytesOfHex mainnetPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some testnetWorkParams.powLimit := by decide +kernel

/-- Core copies the testnet powLimit into its DigiShield record. -/
theorem testnet_digishield_powLimit_literal :
    (targetBytesOfHex mainnetPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some testnetDigishieldWorkParams.powLimit := by decide +kernel

/-- Core copies the testnet powLimit into its minimum-difficulty and AuxPoW records. -/
theorem testnet_minDifficulty_powLimit_literal :
    (targetBytesOfHex mainnetPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some testnetMinDifficultyWorkParams.powLimit := by decide +kernel

/-- Core's regtest literal converts to the existing base powLimit. -/
theorem regtest_powLimit_literal :
    (targetBytesOfHex regtestPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some regtestWorkParams.powLimit := by decide +kernel

/-- Core copies the regtest powLimit into its DigiShield and AuxPoW records. -/
theorem regtest_digishield_powLimit_literal :
    (targetBytesOfHex regtestPowLimitHex).map (Words.toArith ∘ Words.uintToArith256) =
      some regtestDigishieldWorkParams.powLimit := by decide +kernel

end DogeLib.Work.ArithUint256
