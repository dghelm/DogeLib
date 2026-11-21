module

public import DogeLib.Proposals.RelativeLockTime.Proofs.Block
public import DogeLib.Proposals.RelativeLockTime.Proofs.CheckSequence
public import DogeLib.Proposals.RelativeLockTime.Proofs.OpcodeWitnesses
public import DogeLib.Proposals.RelativeLockTime.Proofs.SequenceLocks
public import DogeLib.Proposals.RelativeLockTime.Proofs.SequenceWitnesses
public import DogeLib.Proposals.RelativeLockTime.Proofs.SoftFork
public import DogeLib.Proposals.RelativeLockTime.Proofs.Witnesses

/-!
# `DogeLib.Proposals.RelativeLockTime.Proofs`

The theorems of the proposed revision `RelativeLockTime` (design record 0012), for its three rules: BIP 113, BIP 112 and BIP 68.
`DogeLib.Proposals.RelativeLockTime.Proofs.SoftFork` has the block-level soft-fork theorem.
-/
