module

public import DogeLib.Proposals.RelativeLockTime.Proofs.OpcodeWitnesses

/-!
# Proofs: `Proposals.RelativeLockTime`, witnesses of the sequence locks of BIP 68

The strictness witness and the use witness of design record 0012, section 9.3, for the rule of BIP 68.
Both witnesses are block-level: each is one call of `validateBlock` and of the revision on one block, on a coin set with one coin.

## The witness blocks

Both blocks are made blocks at height 145,000 on the made view of `DogeLib.Proposals.RelativeLockTime.Proofs.Witnesses`.
Neither is a block of mainnet. Each has the header and the context of the witness block of the cutoff, and spends one coin of `fundingTx` with a transaction of version 2.

| Block | Height of the coin | Sequence | Height lock | Revision |
| --- | --- | --- | --- | --- |
| `lockBlock` | 144,999 | 2 | `144999 + 2 ≤ 145000` fails: one block short. | Rejected: `RevisionError.sequenceLocks 1`. |
| `opcodeBlock 2` | 1 | 1 | `1 + 1 ≤ 145000` holds. | Accepted. |

The baseline has no sequence lock, and without the CSV flag the script `01 01 b2` of the coin leaves a true item. So `validateBlock` accepts `lockBlock`.
The transaction test runs before the script check, so the revision rejects `lockBlock` with the error of the sequence lock.

- `sequence_strict`: `validateBlock` accepts `lockBlock` on `lockCoins`, and the active revision rejects it with `RevisionError.sequenceLocks 1`.
- `sequence_use`: the active revision accepts `opcodeBlock 2` on `opcodeCoins`, and the rule runs (`RunsSequenceLock`).
- `sequence_softFork`: the framework's `SoftFork` for the revision and `validateBlock`, with these two witnesses. Block-level.

The kernel evaluates each check of `validateBlock` alone with `decide +kernel`.
The transaction test reads the median time past of the view, which `witnessRevision` holds as a value.
Both witnesses have a height lock. A time lock reads the median time past of an ancestor, which the kernel does not evaluate (`List.mergeSort`), so the known answers of `lake test` cover time locks.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/-- The coin set of the strictness witness: the output of `fundingTx`, at height 144,999. -/
def lockCoins : CoinSet := CoinSet.empty.addTx fundingTx 144999

/-- The spending transaction of the strictness witness: version 2, one input that spends output 0 of `fundingTx` with an empty `scriptSig` and the sequence 2, one output of 0 with an empty script, and lock time 0. -/
def lockSpendTx : Transaction :=
  { version := 2
    inputs := ⟨[{ prevout := ⟨fundingTx.txid, 0⟩, scriptSig := emptyScript, sequence := 2 }], by decide⟩
    outputs := ⟨[{ value := 0, scriptPubKey := emptyScript }], by decide⟩
    lockTime := 0 }

/-- The block of the strictness witness: `witnessHeader`, the coinbase `witnessCoinbase 0` and `lockSpendTx`. -/
def lockBlock : Block :=
  { header := witnessHeader
    vtx := ⟨[⟨witnessCoinbase 0, [WitnessStack.empty], rfl⟩, ⟨lockSpendTx, [WitnessStack.empty], rfl⟩], by simp⟩ }

/-- The arguments of the strictness witness: `lockBlock` on `lockCoins`, in the witness context, without the proof-of-work check and the Merkle check, and with an unavailable verifier. -/
def lockArgs : BlockArgs :=
  { verify := witnessVerifier
    fCheckPOW := false
    fCheckMerkleRoot := false
    ctx := witnessContext
    coins := lockCoins
    block := lockBlock }

/-- The revision on the arguments of the strictness witness is the outcome of the four checks, and then of `connectBlockWith`. -/
theorem lock_revisedValidate :
    revisedValidate true lockArgs =
      validateEmbedding.afterChecks
        (checksBeforeConnect false false witnessContext (lockTimeArgs true witnessContext lockBlock) lockBlock)
        (fun _ => connectBlockWith connectEmbedding witnessRevision true true
          (connectContextOf witnessContext lockBlock) lockArgs.coins lockBlock) := by
  rw [← witnessRevision_eq]
  rfl

/-- On `lockBlock`, the active revision passes `csvActive` true and the median time past 1,395,094,000. -/
theorem lock_lockTimeArgs : lockTimeArgs true witnessContext lockBlock = (true, 1395094000) := by
  simp [lockTimeArgs, show applicable witnessContext lockBlock = true from witness_applicable 0,
    witness_medianTimePast]

/-- The four checks before `ConnectBlock` on `lockBlock` are the result of the body check, for every pair of lock-time arguments. -/
theorem lock_checks (args : Bool × Int) (hcb : checkBlock WorkNetwork.mainnet false false lockBlock = .ok ()) :
    checksBeforeConnect false false witnessContext args lockBlock =
      checkStep .contextualBody
        (contextualCheckBlockBody witnessContext.height args.2 args.1 witnessContext.segwitActive lockBlock)
        fun _ => .ok () :=
  checksBeforeConnect_eq_body (b := lockBlock) witness_not_genesis witness_contextualHeader hcb

/-! ## The checks of the witness block

Each theorem of this section is one evaluation by the kernel.
-/

set_option maxRecDepth 1000000 in
/-- `checkBlock` accepts `lockBlock`, without the proof-of-work check and the Merkle check. -/
theorem lock_checkBlock : checkBlock WorkNetwork.mainnet false false lockBlock = .ok () :=
  eq_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- The body check accepts `lockBlock` with the lock-time arguments of the baseline. -/
theorem lock_body_baseline :
    contextualCheckBlockBody witnessContext.height (baselineLockTimeArgs witnessContext).2
      (baselineLockTimeArgs witnessContext).1 witnessContext.segwitActive lockBlock = .ok () :=
  eq_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- The body check accepts `lockBlock` with `csvActive` true and the median time past of the view. Every lock time is 0. -/
theorem lock_body_revised :
    contextualCheckBlockBody witnessContext.height (1395094000 : Int) true witnessContext.segwitActive lockBlock =
      .ok () :=
  eq_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- `connectBlock` accepts `lockBlock` on `lockCoins`: the baseline has no sequence lock, and `0xb2` is `OP_NOP3`. -/
theorem lock_connect_baseline :
    ∃ r, connectBlock witnessVerifier true (connectContextOf witnessContext lockBlock) lockArgs.coins lockBlock =
      .ok r :=
  exists_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/--
`connectBlockWith` with the active revision rejects `lockBlock`.
Transaction 1 fails the sequence locks: its input has a height lock of 2 blocks on a coin at height 144,999, and the block is at height 145,000.
-/
theorem lock_connect_strict :
    connectBlockWith connectEmbedding witnessRevision true true (connectContextOf witnessContext lockBlock)
        lockArgs.coins lockBlock = .rejected (.inr (.sequenceLocks 1)) :=
  BlockOutcome.eq_rejected_of_rejection? (by decide +kernel)

/-! ## The witnesses -/

/--
The strictness witness of the rule of BIP 68. Block-level.
The block `lockBlock` on `lockCoins` is accepted by `validateBlock`.
The active revision rejects it with `RevisionError.sequenceLocks 1`: transaction 1 fails the sequence locks, Core's `bad-txns-nonfinal` of `ConnectBlock`.
The transaction has version 2, and its input has the sequence 2: a height lock of 2 blocks.
The coin is at height 144,999 and the block is at height 145,000, so the lock is one block short.
-/
theorem sequence_strict :
    (∃ r, baselineValidate lockArgs = .ok r) ∧
      revisedValidate true lockArgs = .rejected (.inr (.sequenceLocks 1)) := by
  constructor
  · obtain ⟨r, hr⟩ := lock_connect_baseline
    refine ⟨r, ?_⟩
    show validateBlock witnessVerifier false false witnessContext lockArgs.coins lockBlock = .ok r
    rw [validateBlock_eq_checks, lock_checks _ lock_checkBlock, lock_body_baseline]
    simp only [checkStep, hr]
  · rw [lock_revisedValidate, lock_checks _ lock_checkBlock, lock_lockTimeArgs, lock_body_revised,
      lock_connect_strict]
    rfl

/--
The use witness of the rule of BIP 68. Block-level.
The active revision accepts the block `opcodeBlock 2` on `opcodeCoins` (`opcode_use`).
The rule runs on the block (`RunsSequenceLock`): the block is applicable, and its second transaction has version 2 and an input with the sequence 1.
That sequence has bits 31 and 22 clear, so it is a height lock of one block.
The coin is at height 1 and the block is at height 145,000, so the lock is met.
-/
theorem sequence_use : (∃ r, revisedValidate true (opcodeArgs 2) = .ok r) ∧ RunsSequenceLock (opcodeArgs 2) := by
  refine ⟨opcode_use.1, opcode_applicable _, spendTx 2, ?_, spendTx_not_coinBase, by decide, ?_⟩
  · exact List.mem_cons_of_mem _ (List.Mem.head _)
  · exact ⟨{ prevout := ⟨fundingTx.txid, 0⟩, scriptSig := emptyScript, sequence := 1 }, List.Mem.head _,
      by decide, by decide, by decide⟩

/--
The revision is a soft fork of `validateBlock` at the level of one block, in the sense of the framework's `SoftFork`, with the witnesses of the sequence locks.
The embedding is `embedBaseline`, and the use predicate is `RunsSequenceLock`.

Block-level: the statement is about one block on a supplied coin set and view, for mainnet rules.
It is not a soft-fork claim about the network, and it says nothing about fork choice, convergence or liveness.
-/
theorem sequence_softFork :
    SoftFork embedBaseline baselineVerdict BlockOutcome.verdict RunsSequenceLock baselineValidate revisedValidate where
  inactive_eq := cutoff_softFork.inactive_eq
  restricts := cutoff_softFork.restricts
  strict := by
    obtain ⟨⟨r, hb⟩, hr⟩ := sequence_strict
    exact ⟨lockArgs, by rw [hb]; rfl, by rw [hr]; rfl⟩
  use := by
    obtain ⟨⟨r, hr⟩, hruns⟩ := sequence_use
    exact ⟨opcodeArgs 2, by rw [hr]; rfl, hruns⟩

end DogeLib.Proposals.RelativeLockTime
