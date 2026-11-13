module

public import DogeLib.Transaction.SigOps
public import DogeLib.Transaction.Proofs.ScanOps
public import DogeLib.Proofs.TheoremTag
meta import DogeLib.Proofs.TheoremTag

/-!
# Properties of the legacy count of signature operations

`Script.getSigOpCount_le` bounds the count of a script by 20 times its length.
Core counts in `unsigned int`, and the bound shows when that type holds the count without a wrap.
-/

@[expose] public section

namespace DogeLib.Transaction

/-- One opcode adds at most `MAX_PUBKEYS_PER_MULTISIG = 20` signature operations. -/
theorem opcodeSigOps_le (opcode : UInt8) : opcodeSigOps opcode ≤ 20 := by
  unfold opcodeSigOps maxPubkeysPerMultisig
  split
  · omega
  · split <;> omega

/-- The instructions that `scanOps` reads from `bs` add at most 20 signature operations for each byte of `bs`. -/
theorem scanOps_sigOps_le (bs : List UInt8) :
    (((scanOps bs).1.map fun o => opcodeSigOps o.1)).sum ≤ 20 * bs.length := by
  rw [scanOps]
  split
  · simp
  · rename_i o b r h
    have hlt := readOp_rest_length h
    have ih := scanOps_sigOps_le r
    have ho := opcodeSigOps_le o
    simp only [List.map_cons, List.sum_cons]
    omega
termination_by bs.length
decreasing_by exact readOp_rest_length ‹_›

/--
For every script, `Script.getSigOpCount` is at most 20 times the number of its bytes.
Each instruction has at least one byte and adds at most 20.
So a script of fewer than `2^32 / 20` bytes, about 214 million, has a count below `2^32`, and Core's `unsigned int` holds it without a wrap.
-/
@[theorem_tag property]
theorem Script.getSigOpCount_le (s : Script) : s.getSigOpCount ≤ 20 * s.bytes.val.length :=
  scanOps_sigOps_le s.bytes.val

end DogeLib.Transaction
