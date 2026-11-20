module

public import DogeLib.Proposals.RelativeLockTime.Proofs.Cutoff
public import DogeLib.Work.Proofs.MedianTimePast

/-!
# Proofs: `Proposals.RelativeLockTime`, witnesses of the lock-time cutoff

The strictness witness and the use witness of design record 0012, section 9.3, for the rule of BIP 113.
The revision is partial: it has that rule alone (`DogeLib.Proposals.RelativeLockTime`).
Both witnesses are block-level: each is one call of `validateBlock` and of the revision on one block, with an empty coin set.

## The witness block

`witnessBlock lockTime` is a made block at height 145,000 on a made view. It is not a block of mainnet.

- The view has eleven entries, at heights 144,999 down to 144,989. Each has the time 1,395,094,000 and the `nBits` `0x1b267eeb`.
  So the median time past of the view is 1,395,094,000 (`witness_medianTimePast`).
- The header has version 1, a zero `hashPrevBlock`, the time 1,395,094,002 and the `nBits` `0x1b22012d`.
  That value is what `nextWorkRequired` gives for the view, and the kernel checks it (`witness_nextWork`).
  The adjusted time is the time of the block.
- The block has one transaction, a coinbase with the `scriptSig` `51 51`, sequence 0, one output of 0 with an empty script, and the lock time `lockTime`.

The block has no proof of work and no Merkle root, so both witnesses clear `fCheckPOW` and `fCheckMerkleRoot`.
The other checks of `validateBlock` run.
The block has no script to run, so the verifier is never called.
`validateBlock` does not read `hashPrevBlock` at this height: the subsidy of height 145,000 does not depend on it.

| Lock time | Baseline cutoff 1,395,094,002 | Revised cutoff 1,395,094,000 |
| --- | --- | --- |
| 1,395,094,000 | Below the cutoff: final. | Not below the cutoff, and the sequence is not final: `bad-txns-nonfinal`. |
| 1,395,093,999 | Below the cutoff: final. | Below the cutoff: final. |

- `cutoff_strict`: with the lock time 1,395,094,000, `validateBlock` accepts the block, and the active revision rejects it with `bad-txns-nonfinal` of `ContextualCheckBlock`.
- `cutoff_use`: with the lock time 1,395,093,999, the active revision accepts the block, and the rule runs (`RunsCutoff`).
- `cutoff_softFork`: the framework's `SoftFork` for the revision with this rule and `validateBlock`. Block-level.

## How the kernel computes the witnesses

The kernel evaluates each check of `validateBlock` alone with `decide +kernel`, including the hash of the header.
Two computations need a proof in the place of an evaluation.
Both use a definition of Lean core by well-founded recursion, which the kernel does not unfold across a module boundary.

- The median time past sorts with `List.mergeSort`. `witness_medianTimePast` uses `medianTimePast_mem`: the median is the time of a view entry, and every entry has one time.
- The subsidy below height 145,000 draws from a Mersenne Twister on a `Vector`. The witness block is at height 145,000, where the subsidy is a fixed amount.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/-- The time of each entry of the witness view. -/
def witnessTime : UInt32 := 1395094000

/-- The predecessor of the witness block: height 144,999. -/
def witnessPrev : BlockIndex := ⟨144999, witnessTime, 0x1b267eeb⟩

/-- The ten ancestors of the predecessor: heights 144,998 down to 144,989, each with the time and the `nBits` of the predecessor. -/
def witnessAncestors : List BlockIndex := (List.range 10).map fun i => ⟨144998 - i, witnessTime, 0x1b267eeb⟩

/-- The coinbase `scriptSig` of the witness block: `OP_1 OP_1`, two bytes. -/
def witnessScriptSig : Transaction.Script := ⟨⟨[0x51, 0x51], by decide⟩⟩

/-- The empty script. -/
def emptyScript : Transaction.Script := ⟨⟨[], by decide⟩⟩

/-- A coinbase with version 1, sequence 0, one output of 0 with an empty script, and the lock time `lockTime`. -/
def witnessCoinbase (lockTime : UInt32) : Transaction :=
  { version := 1
    inputs := ⟨[{ prevout := OutPoint.null, scriptSig := witnessScriptSig, sequence := 0 }], by decide⟩
    outputs := ⟨[{ value := 0, scriptPubKey := emptyScript }], by decide⟩
    lockTime }

/-- The header of the witness block: version 1, zero hashes, the time `witnessTime + 2`, the `nBits` that the view requires, and no AuxPoW payload. -/
def witnessHeader : BlockHeader := ⟨⟨1, Hash256.zero, Hash256.zero, 1395094002, 0x1b22012d, 0⟩, none⟩

/-- The witness block: `witnessHeader` and the one transaction `witnessCoinbase lockTime`. -/
def witnessBlock (lockTime : UInt32) : Block :=
  { header := witnessHeader
    vtx := ⟨[⟨witnessCoinbase lockTime, [WitnessStack.empty], rfl⟩], by simp⟩ }

/-- The context of the witness block: the view of eleven entries, the adjusted time `witnessTime + 2`, no checkpoint, and no active version-bits state. -/
def witnessContext : ValidateContext :=
  { view := witnessPrev :: witnessAncestors
    adjustedTime := 1395094002
    lastCheckpointHeight := none
    csvActive := false
    segwitActive := false
    prevMedianTimePast := 0
    bip34Ancestor := none }

/-- An unavailable verifier. The witness block has no script, so no check calls it. -/
def witnessVerifier : SignatureVerifier := fun _ _ _ => none

/-- The arguments of a witness: the witness block with `lockTime` on the empty coin set, without the proof-of-work check and the Merkle check, and with an unavailable verifier. -/
def witnessArgs (lockTime : UInt32) : BlockArgs :=
  { verify := witnessVerifier
    fCheckPOW := false
    fCheckMerkleRoot := false
    ctx := witnessContext
    coins := CoinSet.empty
    block := witnessBlock lockTime }

/-- The verdict of a `validateBlock` result: a rejection when the error has a reject reason of Core, and unsupported otherwise. -/
def baselineVerdict : Except ValidateError ConnectResult → Verdict :=
  verdictOfBlockResult fun e => e.rejectReason.isSome

/-! ## Results from Boolean tests -/

/-- A result with `isOk` true and the value type `Unit` is `ok ()`. -/
theorem eq_ok_of_isOk {ε : Type} {x : Except ε Unit} (h : x.isOk = true) : x = .ok () := by
  cases x <;> simp_all [Except.isOk, Except.toBool]

/-- A result with `isOk` true is `ok` of some value. -/
theorem exists_ok_of_isOk {ε α : Type} {x : Except ε α} (h : x.isOk = true) : ∃ a, x = .ok a := by
  cases x <;> simp_all [Except.isOk, Except.toBool]

/-- A result that passes the test "an `ok` with the value `a`" is `ok a`. -/
theorem eq_ok_of_test {ε α : Type} [DecidableEq α] {x : Except ε α} {a : α}
    (h : (match x with | .ok v => decide (v = a) | .error _ => false) = true) : x = .ok a := by
  cases x <;> simp_all

/-- A result that passes the test "an `error` with the value `e`" is `error e`. -/
theorem eq_error_of_test {ε α : Type} [DecidableEq ε] {x : Except ε α} {e : ε}
    (h : (match x with | .error v => decide (v = e) | .ok _ => false) = true) : x = .error e := by
  cases x <;> simp_all

/-! ## The checks of the witness block -/

/-- The median time past of the witness view is the time of its entries: 1,395,094,000. -/
theorem witness_medianTimePast : medianTimePast witnessContext.view = .ok 1395094000 := by
  have hok : (medianTimePast (witnessPrev :: witnessAncestors)).isOk = true := by decide +kernel
  obtain ⟨m, hm⟩ := exists_ok_of_isOk hok
  obtain ⟨entry, hmem, htime⟩ := medianTimePast_mem witnessPrev witnessAncestors m hm
  have hall : ∀ e ∈ witnessPrev :: witnessAncestors, e.getBlockTime = 1395094000 := by decide +kernel
  rw [hall entry (List.mem_of_mem_take hmem)] at htime
  rw [← htime] at hm
  exact hm

/-- The view of the witness context requires the `nBits` of the witness header, for a block with the time of that header. -/
theorem witness_nextWork :
    nextWorkRequired .mainnet (witnessPrev :: witnessAncestors) witnessHeader.pure.nTime = .ok 0x1b22012d :=
  eq_ok_of_test (by decide +kernel)

/-- The header of the witness block does not have the hash of the mainnet genesis block. -/
theorem witness_not_genesis :
    (some witnessHeader.pure.getHash == genesisHash? WorkNetwork.mainnet) = false := by
  decide +kernel

/-- `contextualCheckBlockHeader` accepts the header of the witness block on the witness view. -/
theorem witness_contextualHeader :
    contextualCheckBlockHeader WorkNetwork.mainnet witnessHeader.pure witnessContext.view
      witnessContext.adjustedTime witnessContext.lastCheckpointHeight = .ok () := by
  refine (contextualCheck_eq_ok_iff _ _ witnessPrev witnessAncestors _ _).mpr
    ⟨1395094000, 0x1b22012d, witness_medianTimePast, witness_nextWork, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro checkpoint h
    cases h
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The witness block is applicable, for every lock time: its view is not empty, and its header does not have the genesis hash. -/
theorem witness_applicable (lockTime : UInt32) : applicable witnessContext (witnessBlock lockTime) = true := by
  have hg := witness_not_genesis
  unfold applicable
  change (!witnessContext.view.isEmpty && !(some witnessHeader.pure.getHash == genesisHash? WorkNetwork.mainnet)) =
    true
  rw [hg]
  rfl

/-- On the witness block, the active revision passes `csvActive` true and the median time past 1,395,094,000. -/
theorem witness_lockTimeArgs (lockTime : UInt32) :
    lockTimeArgs true witnessContext (witnessBlock lockTime) = (true, 1395094000) := by
  simp [lockTimeArgs, witness_applicable, witness_medianTimePast]

/-- The four checks before `ConnectBlock` on the witness block are the result of the body check, for every pair of lock-time arguments. -/
theorem witness_checks (lockTime : UInt32) (args : Bool × Int)
    (hcb : checkBlock WorkNetwork.mainnet false false (witnessBlock lockTime) = .ok ()) :
    checksBeforeConnect false false witnessContext args (witnessBlock lockTime) =
      checkStep .contextualBody
        (contextualCheckBlockBody witnessContext.height args.2 args.1 witnessContext.segwitActive
          (witnessBlock lockTime)) fun _ => .ok () :=
  checksBeforeConnect_eq_body (b := witnessBlock lockTime) witness_not_genesis witness_contextualHeader hcb

/-! ## The witnesses -/

set_option maxRecDepth 1000000 in
/--
The strictness witness of the rule of BIP 113. Block-level.
The witness block with the lock time 1,395,094,000 is accepted by `validateBlock`.
The active revision rejects it with `bad-txns-nonfinal` of `ContextualCheckBlock`.
The lock time is the median time past of the view, and it is below the time of the block.
-/
theorem cutoff_strict :
    (∃ r, baselineValidate (witnessArgs 1395094000) = .ok r) ∧
      revisedValidate true (witnessArgs 1395094000) = .rejected (.contextualBody .nonFinal) := by
  have hcb : checkBlock WorkNetwork.mainnet false false (witnessBlock 1395094000) = .ok () :=
    eq_ok_of_isOk (by decide +kernel)
  constructor
  · have hbody : contextualCheckBlockBody witnessContext.height (baselineLockTimeArgs witnessContext).2
        (baselineLockTimeArgs witnessContext).1 witnessContext.segwitActive (witnessBlock 1395094000) = .ok () :=
      eq_ok_of_isOk (by decide +kernel)
    obtain ⟨r, hr⟩ := exists_ok_of_isOk (x := connectBlock witnessVerifier true
      (connectContextOf witnessContext (witnessBlock 1395094000)) CoinSet.empty (witnessBlock 1395094000))
      (by decide +kernel)
    refine ⟨r, ?_⟩
    show validateBlock witnessVerifier false false witnessContext CoinSet.empty (witnessBlock 1395094000) = .ok r
    rw [validateBlock_eq_checks, witness_checks _ _ hcb, hbody]
    simp only [checkStep, hr]
  · have hbody : contextualCheckBlockBody witnessContext.height (1395094000 : Int) true witnessContext.segwitActive
        (witnessBlock 1395094000) = .error .nonFinal :=
      eq_error_of_test (by decide +kernel)
    unfold revisedValidate validateBlockWithActive
    change ValidateEmbedding.baseline.afterChecks
      (checksBeforeConnect false false witnessContext (lockTimeArgs true witnessContext (witnessBlock 1395094000))
        (witnessBlock 1395094000)) _ = _
    rw [witness_checks _ _ hcb, witness_lockTimeArgs, hbody]
    rfl

set_option maxRecDepth 1000000 in
/--
The use witness of the rule of BIP 113. Block-level.
The active revision accepts the witness block with the lock time 1,395,093,999, which is below the median time past of the view.
The rule runs on the block (`RunsCutoff`): the block is applicable, and its coinbase has a time lock time and a sequence that is not final.
-/
theorem cutoff_use :
    (∃ r, revisedValidate true (witnessArgs 1395093999) = .ok r) ∧ RunsCutoff (witnessArgs 1395093999) := by
  have hcb : checkBlock WorkNetwork.mainnet false false (witnessBlock 1395093999) = .ok () :=
    eq_ok_of_isOk (by decide +kernel)
  have hbody : contextualCheckBlockBody witnessContext.height (1395094000 : Int) true witnessContext.segwitActive
      (witnessBlock 1395093999) = .ok () :=
    eq_ok_of_isOk (by decide +kernel)
  obtain ⟨r, hr⟩ := exists_ok_of_isOk (x := connectBlock witnessVerifier true
    (connectContextOf witnessContext (witnessBlock 1395093999)) CoinSet.empty (witnessBlock 1395093999))
    (by decide +kernel)
  refine ⟨⟨r, ?_⟩, witness_applicable _, witnessCoinbase 1395093999, ?_, ?_, ?_⟩
  · have hconn : connectBlockWith ConnectEmbedding.baseline (blockRevision witnessVerifier) true true
        (connectContextOf witnessContext (witnessBlock 1395093999)) CoinSet.empty (witnessBlock 1395093999) =
          .ok r := by
      rw [connectBlockWith_congr_revision ConnectEmbedding.baseline (rev₁ := blockRevision witnessVerifier)
        (rev₂ := .baseline id id witnessVerifier) true
        (fun _ _ _ _ _ _ _ _ _ => rfl) rfl (fun _ _ _ _ _ _ => rfl), connectBlockWith_ofBaseline, hr]
      rfl
    unfold revisedValidate validateBlockWithActive
    change ValidateEmbedding.baseline.afterChecks
      (checksBeforeConnect false false witnessContext (lockTimeArgs true witnessContext (witnessBlock 1395093999))
        (witnessBlock 1395093999))
      (fun _ => connectBlockWith ConnectEmbedding.baseline (blockRevision witnessVerifier) true true
        (connectContextOf witnessContext (witnessBlock 1395093999)) CoinSet.empty (witnessBlock 1395093999)) = _
    rw [witness_checks _ _ hcb, witness_lockTimeArgs, hbody, hconn]
    rfl
  · simp [witnessArgs, witnessBlock, Block.transactions]
  · decide
  · decide

/--
The revision with the rule of BIP 113 is a soft fork of `validateBlock` at the level of one block, in the sense of the framework's `SoftFork`.
The embedding is `ValidateEmbedding.ofBaseline` with the baseline error types, and the use predicate is `RunsCutoff`.

Block-level: the statement is about one block on a supplied coin set and view, for mainnet rules.
It is not a soft-fork claim about the network, and it says nothing about fork choice, convergence or liveness.
The revision is partial, so this is not the target `relativeLockTime_softFork` of design record 0012, which is about the three rules together.
-/
theorem cutoff_softFork :
    SoftFork (ValidateEmbedding.baseline.ofBaseline ConnectEmbedding.baseline id id) baselineVerdict
      BlockOutcome.verdict RunsCutoff baselineValidate revisedValidate where
  inactive_eq := fun a =>
    relativeLockTime_inactive_eq ValidateEmbedding.baseline ConnectEmbedding.baseline a.verify a.fCheckPOW
      a.fCheckMerkleRoot a.ctx a.coins a.block
  restricts := fun active a h => by
    obtain ⟨r, hr⟩ := BlockOutcome.verdict_eq_accepted_iff.mp h
    have hb : baselineValidate a = .ok r := relativeLockTime_restricts hr
    rw [hb]
    rfl
  strict := by
    obtain ⟨⟨r, hb⟩, hr⟩ := cutoff_strict
    exact ⟨witnessArgs 1395094000, by rw [hb]; rfl, by rw [hr]; rfl⟩
  use := by
    obtain ⟨⟨r, hr⟩, hruns⟩ := cutoff_use
    exact ⟨witnessArgs 1395093999, by rw [hr]; rfl, hruns⟩

end DogeLib.Proposals.RelativeLockTime
