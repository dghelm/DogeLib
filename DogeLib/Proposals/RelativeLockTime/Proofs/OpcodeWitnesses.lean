module

public import DogeLib.Proposals.RelativeLockTime.Proofs.Witnesses

/-!
# Proofs: `Proposals.RelativeLockTime`, witnesses of the opcode of BIP 112

The strictness witness and the use witness of design record 0012, section 9.3, for the rule of BIP 112.
The revision is partial: it has that rule and the rule of BIP 113 (`DogeLib.Proposals.RelativeLockTime`).
Both witnesses are block-level: each is one call of `validateBlock` and of the revision on one block, on a coin set with one coin.

## The witness block

`opcodeBlock version` is a made block at height 145,000 on the made view of `DogeLib.Proposals.RelativeLockTime.Proofs.Witnesses`.
It is not a block of mainnet. It has the header and the context of the witness block of the cutoff.

- The coin set is `opcodeCoins`: the outputs of `fundingTx` at height 1.
  That transaction has one output of 0 with the script `01 01 b2`: a push of the operand 1, then opcode `0xb2`.
  The script is `operandScript [1] []`.
- The block has two transactions. The first is the coinbase of the witness block of the cutoff, with lock time 0.
  The second is `spendTx version`: it has the version `version`, lock time 0, and one input that spends the coin with an empty `scriptSig` and the sequence 1. It has one output of 0 with an empty script.

The block has no proof of work and no Merkle root, so both witnesses clear `fCheckPOW` and `fCheckMerkleRoot`.
The other checks of `validateBlock` run. No script has a signature opcode, so the verifier is never called.

Without the CSV flag, `0xb2` is `OP_NOP3`, and the script leaves the true item `01`.
With the flag, the opcode compares the operand 1 with the sequence 1 of the input (`sequenceSatisfied`).

| Version | Baseline flags | Revised flags |
| --- | --- | --- |
| 1 | Accepted. | `CheckSequence` fails for a version below 2: `UNSATISFIED_LOCKTIME`. The second run without the flag accepts, so the class is that of `non-mandatory-script-verify-flag`. |
| 2 | Accepted. | Accepted: bit 31 of the sequence is clear, both type bits are clear, and 1 is at most 1. |

- `opcode_strict`: with version 1, `validateBlock` accepts the block, and the active revision rejects it with the script error `UNSATISFIED_LOCKTIME` of input 0 of transaction 1, which is not mandatory.
- `opcode_use`: with version 2, the active revision accepts the block, and the rule runs (`RunsOpcode`).
- `opcode_softFork`: the framework's `SoftFork` for the partial revision and `validateBlock`, with these two witnesses. Block-level.

The witnesses are at the block level, as stage 2 of design record 0012 asks.
The kernel evaluates each check of `validateBlock` alone with `decide +kernel`, including the transaction hashes and both runs of the script.
Each evaluation is a theorem of its own.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/-- The script of the spent coin: `operandScript [1] []`, the bytes `01 01 b2`. -/
def opcodeScriptPubKey : Transaction.Script := ⟨⟨operandScript [1] [], by decide⟩⟩

/-- The transaction that created the spent coin: one output of 0 with the script `opcodeScriptPubKey`. It is not a coinbase. -/
def fundingTx : Transaction :=
  { version := 1
    inputs := ⟨[{ prevout := ⟨Hash256.zero, 0⟩, scriptSig := emptyScript, sequence := 0xffffffff }], by decide⟩
    outputs := ⟨[{ value := 0, scriptPubKey := opcodeScriptPubKey }], by decide⟩
    lockTime := 0 }

/-- The coin set of the witnesses: the output of `fundingTx`, at height 1. -/
def opcodeCoins : CoinSet := CoinSet.empty.addTx fundingTx 1

/-- The spending transaction: the version `version`, one input that spends output 0 of `fundingTx` with an empty `scriptSig` and the sequence 1, one output of 0 with an empty script, and lock time 0. -/
def spendTx (version : UInt32) : Transaction :=
  { version
    inputs := ⟨[{ prevout := ⟨fundingTx.txid, 0⟩, scriptSig := emptyScript, sequence := 1 }], by decide⟩
    outputs := ⟨[{ value := 0, scriptPubKey := emptyScript }], by decide⟩
    lockTime := 0 }

/-- The witness block of the opcode: `witnessHeader`, the coinbase `witnessCoinbase 0` and `spendTx version`. -/
def opcodeBlock (version : UInt32) : Block :=
  { header := witnessHeader
    vtx := ⟨[⟨witnessCoinbase 0, [WitnessStack.empty], rfl⟩, ⟨spendTx version, [WitnessStack.empty], rfl⟩], by simp⟩ }

/-- The arguments of a witness: the block `opcodeBlock version` on `opcodeCoins`, in the witness context, without the proof-of-work check and the Merkle check, and with an unavailable verifier. -/
def opcodeArgs (version : UInt32) : BlockArgs :=
  { verify := witnessVerifier
    fCheckPOW := false
    fCheckMerkleRoot := false
    ctx := witnessContext
    coins := opcodeCoins
    block := opcodeBlock version }

/-- The baseline on the arguments of a witness is `validateBlock` on their parts. -/
theorem opcode_baselineValidate (version : UInt32) :
    baselineValidate (opcodeArgs version) =
      validateBlock witnessVerifier false false witnessContext (opcodeArgs version).coins (opcodeBlock version) :=
  rfl

/-- The revision on the arguments of a witness is the outcome of the four checks, and then of `connectBlockWith`. -/
theorem opcode_revisedValidate (version : UInt32) :
    revisedValidate true (opcodeArgs version) =
      ValidateEmbedding.baseline.afterChecks
        (checksBeforeConnect false false witnessContext (lockTimeArgs true witnessContext (opcodeBlock version))
          (opcodeBlock version))
        (fun _ => connectBlockWith ConnectEmbedding.baseline (blockRevision witnessVerifier) true true
          (connectContextOf witnessContext (opcodeBlock version)) (opcodeArgs version).coins (opcodeBlock version)) :=
  rfl

/-- The block `opcodeBlock version` is applicable, for every version: its view is not empty, and its header does not have the genesis hash. -/
theorem opcode_applicable (version : UInt32) : applicable witnessContext (opcodeBlock version) = true :=
  witness_applicable 0

/-- On `opcodeBlock version`, the active revision passes `csvActive` true and the median time past 1,395,094,000. -/
theorem opcode_lockTimeArgs (version : UInt32) :
    lockTimeArgs true witnessContext (opcodeBlock version) = (true, 1395094000) := by
  simp [lockTimeArgs, opcode_applicable, witness_medianTimePast]

/-- The four checks before `ConnectBlock` on `opcodeBlock version` are the result of the body check, for every pair of lock-time arguments. -/
theorem opcode_checks (version : UInt32) (args : Bool × Int)
    (hcb : checkBlock WorkNetwork.mainnet false false (opcodeBlock version) = .ok ()) :
    checksBeforeConnect false false witnessContext args (opcodeBlock version) =
      checkStep .contextualBody
        (contextualCheckBlockBody witnessContext.height args.2 args.1 witnessContext.segwitActive
          (opcodeBlock version)) fun _ => .ok () :=
  checksBeforeConnect_eq_body (b := opcodeBlock version) witness_not_genesis witness_contextualHeader hcb

/-! ## The checks of the witness block

Each theorem of this section is one evaluation by the kernel.
-/

set_option maxRecDepth 1000000 in
/-- `checkBlock` accepts `opcodeBlock 1` and `opcodeBlock 2`, without the proof-of-work check and the Merkle check. -/
theorem opcode_checkBlock :
    checkBlock WorkNetwork.mainnet false false (opcodeBlock 1) = .ok () ∧
      checkBlock WorkNetwork.mainnet false false (opcodeBlock 2) = .ok () :=
  ⟨eq_ok_of_isOk (by decide +kernel), eq_ok_of_isOk (by decide +kernel)⟩

set_option maxRecDepth 1000000 in
/-- The body check accepts `opcodeBlock 1` with the lock-time arguments of the baseline. -/
theorem opcode_body_baseline :
    contextualCheckBlockBody witnessContext.height (baselineLockTimeArgs witnessContext).2
      (baselineLockTimeArgs witnessContext).1 witnessContext.segwitActive (opcodeBlock 1) = .ok () :=
  eq_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- The body check accepts `opcodeBlock 1` and `opcodeBlock 2` with `csvActive` true and the median time past of the view. Every lock time is 0. -/
theorem opcode_body_revised :
    contextualCheckBlockBody witnessContext.height (1395094000 : Int) true witnessContext.segwitActive
        (opcodeBlock 1) = .ok () ∧
      contextualCheckBlockBody witnessContext.height (1395094000 : Int) true witnessContext.segwitActive
        (opcodeBlock 2) = .ok () :=
  ⟨eq_ok_of_isOk (by decide +kernel), eq_ok_of_isOk (by decide +kernel)⟩

set_option maxRecDepth 1000000 in
/-- `connectBlock` accepts `opcodeBlock 1` on the coin set of the witnesses: without the CSV flag, `0xb2` is `OP_NOP3`. -/
theorem opcode_connect_baseline :
    ∃ r, connectBlock witnessVerifier true (connectContextOf witnessContext (opcodeBlock 1)) (opcodeArgs 1).coins
      (opcodeBlock 1) = .ok r :=
  exists_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/--
`connectBlockWith` with the active revision rejects `opcodeBlock 1`.
Input 0 of transaction 1 fails with `UNSATISFIED_LOCKTIME`, and the second run, without the flags that are not mandatory, accepts.
-/
theorem opcode_connect_strict :
    connectBlockWith ConnectEmbedding.baseline (blockRevision witnessVerifier) true true
        (connectContextOf witnessContext (opcodeBlock 1)) (opcodeArgs 1).coins (opcodeBlock 1) =
      .rejected (.script 1 0 false .unsatisfiedLocktime) :=
  BlockOutcome.eq_rejected_of_rejection? (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- `connectBlockWith` with the active revision accepts `opcodeBlock 2`. -/
theorem opcode_connect_use :
    ∃ r, connectBlockWith ConnectEmbedding.baseline (blockRevision witnessVerifier) true true
      (connectContextOf witnessContext (opcodeBlock 2)) (opcodeArgs 2).coins (opcodeBlock 2) = .ok r :=
  BlockOutcome.exists_ok_of_isOk (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- The coin set of the witnesses has the coin of output 0 of `fundingTx`: an amount of 0 with the script `opcodeScriptPubKey`, at height 1, not from a coinbase. -/
theorem opcode_coin :
    (opcodeArgs 2).coins.coin ⟨fundingTx.txid, 0⟩ = some ⟨⟨0, opcodeScriptPubKey⟩, 1, false⟩ :=
  eq_of_beq (by decide +kernel)

/-- `spendTx 2` is not a coinbase. -/
theorem spendTx_not_coinBase : (spendTx 2).isCoinBase = false := by decide +kernel

/-! ## The witnesses -/

/--
The strictness witness of the rule of BIP 112. Block-level.
The block `opcodeBlock 1` on `opcodeCoins` is accepted by `validateBlock`.
The active revision rejects it: input 0 of transaction 1 fails with `UNSATISFIED_LOCKTIME`, and the failure is not mandatory.
The spending transaction has version 1, and `OP_CHECKSEQUENCEVERIFY` fails for a version below 2.
The class of the failure is that of Core's `non-mandatory-script-verify-flag`: the second run, without the CSV flag, accepts.
-/
theorem opcode_strict :
    (∃ r, baselineValidate (opcodeArgs 1) = .ok r) ∧
      revisedValidate true (opcodeArgs 1) = .rejected (.connect (.script 1 0 false .unsatisfiedLocktime)) := by
  have hcb := opcode_checkBlock.1
  constructor
  · obtain ⟨r, hr⟩ := opcode_connect_baseline
    refine ⟨r, ?_⟩
    rw [opcode_baselineValidate, validateBlock_eq_checks, opcode_checks _ _ hcb, opcode_body_baseline]
    simp only [checkStep, hr]
  · rw [opcode_revisedValidate, opcode_checks _ _ hcb, opcode_lockTimeArgs, opcode_body_revised.1,
      opcode_connect_strict]
    rfl

/--
The use witness of the rule of BIP 112. Block-level.
The active revision accepts the block `opcodeBlock 2` on `opcodeCoins`.
The rule runs on the block (`RunsOpcode`): the block is applicable, and its second transaction spends a coin with the script `operandScript [1] []`, whose operand 1 is not negative and has bit 31 clear.
The spending transaction has version 2 and the sequence 1, so `OP_CHECKSEQUENCEVERIFY` executes and passes.
-/
theorem opcode_use : (∃ r, revisedValidate true (opcodeArgs 2) = .ok r) ∧ RunsOpcode (opcodeArgs 2) := by
  obtain ⟨r, hconn⟩ := opcode_connect_use
  refine ⟨⟨r, ?_⟩, opcode_applicable _, spendTx 2, ?_, spendTx_not_coinBase, ?_⟩
  · rw [opcode_revisedValidate, opcode_checks _ _ opcode_checkBlock.2, opcode_lockTimeArgs, opcode_body_revised.2,
      hconn]
    rfl
  · exact List.mem_cons_of_mem _ (List.Mem.head _)
  · exact ⟨{ prevout := ⟨fundingTx.txid, 0⟩, scriptSig := emptyScript, sequence := 1 }, List.Mem.head _,
      ⟨⟨0, opcodeScriptPubKey⟩, 1, false⟩, opcode_coin, [1], [], by decide, rfl, by decide +kernel,
      by decide +kernel⟩

/--
The revision with the rules of BIP 113 and BIP 112 is a soft fork of `validateBlock` at the level of one block, in the sense of the framework's `SoftFork`, with the witnesses of the opcode.
The embedding is `ValidateEmbedding.ofBaseline` with the baseline error types, and the use predicate is `RunsOpcode`.

Block-level: the statement is about one block on a supplied coin set and view, for mainnet rules.
It is not a soft-fork claim about the network, and it says nothing about fork choice, convergence or liveness.
The revision is partial, so this is not the target `relativeLockTime_softFork` of design record 0012, which is about the three rules together.
-/
theorem opcode_softFork :
    SoftFork (ValidateEmbedding.baseline.ofBaseline ConnectEmbedding.baseline id id) baselineVerdict
      BlockOutcome.verdict RunsOpcode baselineValidate revisedValidate where
  inactive_eq := cutoff_softFork.inactive_eq
  restricts := cutoff_softFork.restricts
  strict := by
    obtain ⟨⟨r, hb⟩, hr⟩ := opcode_strict
    exact ⟨opcodeArgs 1, by rw [hb]; rfl, by rw [hr]; rfl⟩
  use := by
    obtain ⟨⟨r, hr⟩, hruns⟩ := opcode_use
    exact ⟨opcodeArgs 2, by rw [hr]; rfl, hruns⟩

end DogeLib.Proposals.RelativeLockTime
