module

public import DogeLib.Base.Proofs.ByteArray
public import DogeLib.Cryptography.Proofs.Hash.Hash160
public import DogeLib.Script.MultisigRecovery
public import DogeLib.Script.Proofs.SignatureCode
public import DogeLib.Script.Proofs.SignatureEncoding
public import DogeLib.Script.Proofs.Verify
public import DogeLib.Transaction.Proofs.LegacySighashCommitment

/-!
# Proofs: `Script.MultisigRecovery`

The worked property target of design record 0003, section 7: the multisig redeem script with a time-locked recovery key.
The theorems hold for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16`, and for the 2-of-3 instance.

## The branch predicates

`OrdinaryBranch` and `RecoveryBranch` are the two cases of section 7 over the stack `S` that `scriptSig` leaves below the redeem script.
They state each condition explicitly:

- the stack suffix, `[dummy, sig1, ..., sigk, sel]` or `[sigR, sel]`, and the selector's `castToBool` value
- `SigEncodingOk` and `KeyEncodingOk` on the pairs that Core reaches, in Core's order (`multisigVisits`)
- for the ordinary branch, an empty dummy under `NULLDUMMY`, and ordered matching (`OrderedMatch`) under `sigAccepted`
- for the recovery branch, a lock time from 1,000,000 to below 500,000,000, a nonfinal sequence, and `sigAccepted` against `R`

`sigAccepted` is the answer `some true` of `transactionChecker` for the input.
By `sigAccepted_iff`, it means that the key passes `isValidPubKey` and `verify` returns `some true` on the signature without its hash-type byte and the legacy digest.
`checkSignatureEncoding_ok_iff` and `checkPubKeyEncoding_ok_iff` prove that the encoding predicates are exactly the checks of `DogeLib.Script.SignatureEncoding`.

## The theorems

`MultisigRecoverySpend` collects the hypotheses: the flags, and the template and key sizes.
It also holds the P2SH commitment to the exact redeem bytes, a push-only `scriptSig`, and its final stack `S ++ [redeem]`.

- `multisigRecovery_sound`: acceptance implies one of the branches. It assumes no stack bound and no totality of `verify`.
- `multisigRecovery_ordinary_complete`, `multisigRecovery_recovery_complete`: each branch suffices for acceptance, under a stack bound on `S`, and for the ordinary branch a decided answer on every visited pair.
- `multisigRecovery_accepted_iff`, `multisigRecovery_twoOfThree_accepted_iff`: the equivalence, for a verifier that decides every request.
- `multisigRecovery_ordinary_unsupported`, `multisigRecovery_recovery_unsupported`: an undecided reached call gives `unsupported`.
- `multisigRecovery_lockTime_lt`, `multisigRecovery_accepted_lockTime_lt`: under `CHECKLOCKTIMEVERIFY`, a lock time below 1,000,000 cannot pass the recovery branch.
- `multisigRecovery_lockTime_ge_threshold`, `multisigRecovery_finalSequence`: under `CHECKLOCKTIMEVERIFY`, a false selector gives `UNSATISFIED_LOCKTIME` before any signature check in two more cases. They are a lock time of at least 500,000,000, and a sequence of `0xffffffff` at every lock time.
- `verifyLegacySpend_scriptSig_rejected`, `verifyLegacySpend_scriptSig_unsupported`: a failed `scriptSig` evaluation passes through.

## The reference digest

Every checker call of both branches hashes the digest of `legacyReferencePlan`, Core's `SignatureHashOld` transformation.

- `ordinaryCode_scanOps`, `recoveryCode_scanOps`: for every signature list, every instruction of each branch's script code parses. That property is the parsed-script hypothesis of design record 0003, stage 3.
- `transactionChecker_verify_reference`, `sigAccepted_iff_reference`: for any `InputContext` and fully parsed script code, the checker passes the reference digest to `verify`.
- `MultisigRecoverySpend.sigAccepted_ordinary_iff_reference`, `MultisigRecoverySpend.sigAccepted_recovery_iff_reference`, `MultisigRecoverySpend.checkSig_ordinary_reference`, `MultisigRecoverySpend.checkSig_recovery_reference`: the two compose under `MultisigRecoverySpend`.
- `MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits`, `MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits`: with ALL and without ANYONECANPAY, an accepted signature also verifies against the reference digest of every transaction with the same `legacyAllFields`. The result is invariance under equal fields. It says nothing about changed fields, and does not say that such a transaction passes the template.

## Resource bounds

The template discharges the redeem-script size (`multisigRecoveryScript_length`: `34 n + 47` bytes), the push sizes (33 bytes at most) and the opcode count (at most `n + 7`).
The 520-byte element limit on the push of the redeem script follows from the successful `scriptSig` evaluation, and restricts `n` to at most 13.
The stack bound on `S` remains a hypothesis of the converses: `S.length + n + 1 ≤ 1000` for the ordinary branch, and `S.length + 2 ≤ 1000` for the recovery branch.

## What the theorems do not say

They hold relative to the verifier parameter `verify`.
They do not establish unforgeability, private-key ownership, distinct signers or hash collision resistance.

Duplicate keys are allowed, and a match against duplicates does not mean distinct authorization.
The P2SH composition uses the exact supplied redeem script. A different redeem script with the same digest needs a separate hash-commitment argument.
Every hash type that the flags admit is allowed, including NONE, SINGLE and ANYONECANPAY.
A claim that recovery cannot enter a chain before a height or time needs transaction-finality and chain-context results.

These theorems are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction


/--
The signature encoding predicate of section 7 (D3, lines 197 to 211).
A nonempty signature is strict DER under `DERSIG`, `LOW_S` or `STRICTENC`.
Under `LOW_S` it also passes `checkLowS`, including its overflow case.
Under `STRICTENC` it also has a defined hash type.
The empty signature always passes.
-/
def SigEncodingOk (flags : UInt32) (sig : List UInt8) : Prop :=
  sig ≠ [] →
    ((hasFlag flags ScriptFlags.derSig = true ∨ hasFlag flags ScriptFlags.lowS = true ∨
        hasFlag flags ScriptFlags.strictEnc = true) → isValidSignatureEncoding sig = true) ∧
      (hasFlag flags ScriptFlags.lowS = true → checkLowS sig.dropLast = true) ∧
      (hasFlag flags ScriptFlags.strictEnc = true → isDefinedHashtypeSignature sig = true)

/-- The public-key encoding predicate of section 7 (D3, lines 214 to 224): under `STRICTENC`, a compressed or uncompressed key shape. -/
def KeyEncodingOk (flags : UInt32) (key : List UInt8) : Prop :=
  hasFlag flags ScriptFlags.strictEnc = true → isCompressedOrUncompressedPubKey key = true

/-- `transactionChecker` for the input of `ctx` answers `some true` for `sig` and `key` with the script code `code`. -/
def sigAccepted (ctx : InputContext) (verify : SignatureVerifier) (code sig key : List UInt8) : Bool :=
  (transactionChecker ctx.tx ctx.index verify).checkSig sig key code == some true

/--
The pairs that the matching loop of `OP_CHECKMULTISIG` visits (D3, lines 963 to 992), when `R` decides each visited pair.
The lists are in Core's order, nearest the stack top first, as in `multisigLoop`.
-/
def multisigVisits {α β : Type} (R : α → β → Bool) : List α → List β → List (α × β)
  | [], _ => []
  | _ :: _, [] => []
  | a :: as, b :: bs =>
    let rest := if R a b then as else a :: as
    (a, b) :: if bs.length < rest.length then [] else multisigVisits R rest bs

/-- The script code of the ordinary branch: the redeem script with every signature push removed, nearest the stack top first (D3, lines 952 to 961). `sigs` is in push order. -/
def ordinaryCode (redeem : List UInt8) (sigs : List (List UInt8)) : List UInt8 :=
  effectiveScriptCode redeem 0 sigs.reverse

/-- The script code of the recovery branch: the redeem script with the push of `sigR` removed (D3, lines 891 to 896). -/
def recoveryCode (redeem sigR : List UInt8) : List UInt8 := effectiveScriptCode redeem 0 [sigR]

/--
The ordinary branch of section 7 for the stack `S` below the redeem script.
`S` is `below ++ dummy :: sigs ++ [sel]`, with `k` signatures in push order and a true selector.
Every pair that Core visits, top first, passes both encoding predicates.
With `NULLDUMMY` the dummy is empty.
The signatures pair in order with a subsequence of the keys under `sigAccepted`.
-/
def OrdinaryBranch (ctx : InputContext) (verify : SignatureVerifier) (flags : UInt32) (k : Nat)
    (keys : List (List UInt8)) (recovery : List UInt8) (S : List (List UInt8)) : Prop :=
  ∃ below dummy sigs sel, S = below ++ dummy :: sigs ++ [sel] ∧ sigs.length = k ∧ castToBool sel = true ∧
    (∀ p ∈ multisigVisits (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys recovery) sigs))
        sigs.reverse keys.reverse, SigEncodingOk flags p.1 ∧ KeyEncodingOk flags p.2) ∧
    (hasFlag flags ScriptFlags.nullDummy = true → dummy = []) ∧
    OrderedMatch (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys recovery) sigs)) sigs keys

/--
The recovery branch of section 7 for the stack `S` below the redeem script.
`S` is `below ++ [sigR, sel]` with a false selector.
The transaction's lock time is at least 1,000,000 and below 500,000,000, and the input's sequence is not `0xffffffff`.
`sigR` and the recovery key pass the encoding predicates, and the checker accepts `sigR` against the recovery key.
-/
def RecoveryBranch (ctx : InputContext) (verify : SignatureVerifier) (flags : UInt32) (k : Nat)
    (keys : List (List UInt8)) (recovery : List UInt8) (S : List (List UInt8)) : Prop :=
  ∃ below sigR sel, S = below ++ [sigR, sel] ∧ castToBool sel = false ∧
    recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
    ctx.input.sequence ≠ sequenceFinal ∧
    SigEncodingOk flags sigR ∧ KeyEncodingOk flags recovery ∧
    sigAccepted ctx verify (recoveryCode (multisigRecoveryScript k keys recovery) sigR) sigR recovery = true


/-- The visits of a nonempty matching: the first pair, then the visits of the rest unless the early exit applies. -/
theorem multisigVisits_cons {α β : Type} (R : α → β → Bool) (a : α) (as : List α) (b : β) (bs : List β) :
    multisigVisits R (a :: as) (b :: bs) =
      (a, b) :: if bs.length < (if R a b then as else a :: as).length then []
        else multisigVisits R (if R a b then as else a :: as) bs := rfl

/-- One step of `greedyMatch` on two nonempty lists. -/
theorem greedyMatch_cons {α β : Type} (R : α → β → Bool) (a : α) (as : List α) (b : β) (bs : List β) :
    greedyMatch R (a :: as) (b :: bs) =
      if bs.length < (if R a b then as else a :: as).length then false
        else greedyMatch R (if R a b then as else a :: as) bs := rfl

/-- One step of `multisigLoop` on two nonempty lists whose first pair has the decided answer `v`. -/
theorem multisigLoop_cons {α β ε : Type} {check : α → β → Except ε Bool} {a : α} {as : List α} {b : β}
    {bs : List β} {v : Bool} (h : check a b = .ok v) :
    multisigLoop check (a :: as) (b :: bs) =
      if bs.length < (if v then as else a :: as).length then .ok false
        else multisigLoop check (if v then as else a :: as) bs := by
  simp only [multisigLoop, h]

/--
For every check function and relation `R`: if `check` answers `.ok (R a b)` on every pair that `multisigVisits R` lists, `multisigLoop` returns `greedyMatch R`.
Only the visited pairs need an answer, unlike `multisigLoop_ok`.
-/
theorem multisigLoop_visits_ok {α β ε : Type} {check : α → β → Except ε Bool} {R : α → β → Bool}
    {sigs : List α} {keys : List β} (h : ∀ p ∈ multisigVisits R sigs keys, check p.1 p.2 = .ok (R p.1 p.2)) :
    multisigLoop check sigs keys = .ok (greedyMatch R sigs keys) := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> rfl
  | cons b bs ih =>
    cases sigs with
    | nil => rfl
    | cons a as =>
      have hab := h (a, b) (by simp [multisigVisits])
      rw [multisigLoop_cons hab, greedyMatch_cons]
      rw [multisigVisits_cons] at h
      generalize (if R a b = true then as else a :: as) = rest at h ⊢
      by_cases hl : bs.length < rest.length
      · simp [hl]
      · simp only [hl, ite_false] at h ⊢
        exact ih fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- For every check function and relation `R` that agrees with every decided answer of `check`: if `multisigLoop` returns `r`, every visited pair has a decided answer, and `greedyMatch R` is `r`. -/
theorem multisigLoop_ok_visits {α β ε : Type} {check : α → β → Except ε Bool} {R : α → β → Bool}
    (hR : ∀ a b v, check a b = .ok v → v = R a b) {sigs : List α} {keys : List β} {r : Bool}
    (h : multisigLoop check sigs keys = .ok r) :
    (∀ p ∈ multisigVisits R sigs keys, ∃ v, check p.1 p.2 = .ok v) ∧ greedyMatch R sigs keys = r := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> (simp [multisigLoop] at h; simp [multisigVisits, greedyMatch, h])
  | cons b bs ih =>
    cases sigs with
    | nil => simp [multisigLoop] at h; simp [multisigVisits, greedyMatch, h]
    | cons a as =>
      cases hab : check a b with
      | error e => simp [multisigLoop, hab] at h
      | ok v =>
        have hv := hR a b v hab
        subst hv
        rw [multisigLoop_cons hab] at h
        rw [greedyMatch_cons, multisigVisits_cons]
        generalize (if R a b = true then as else a :: as) = rest at h ⊢
        by_cases hl : bs.length < rest.length
        · simp only [hl, ite_true, Except.ok.injEq] at h ⊢
          refine ⟨fun p hp => ?_, h⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
          subst hp; exact ⟨_, hab⟩
        · simp only [hl, ite_false] at h ⊢
          obtain ⟨h1, h2⟩ := ih h
          refine ⟨fun p hp => ?_, h2⟩
          rcases List.mem_cons.mp hp with hp | hp
          · subst hp; exact ⟨_, hab⟩
          · exact h1 p hp

/-- For every check function and relation `R`: if `check` answers `.ok (R a b)` on the visits before the pair `p`, and gives the error `e` on `p`, `multisigLoop` returns `e`. -/
theorem multisigLoop_visits_error {α β ε : Type} {check : α → β → Except ε Bool} {R : α → β → Bool}
    {sigs : List α} {keys : List β} {pre post : List (α × β)} {p : α × β} {e : ε}
    (hv : multisigVisits R sigs keys = pre ++ p :: post)
    (hpre : ∀ q ∈ pre, check q.1 q.2 = .ok (R q.1 q.2)) (hp : check p.1 p.2 = .error e) :
    multisigLoop check sigs keys = .error e := by
  induction keys generalizing sigs pre with
  | nil => cases sigs <;> simp [multisigVisits] at hv
  | cons b bs ih =>
    cases sigs with
    | nil => simp [multisigVisits] at hv
    | cons a as =>
      cases pre with
      | nil =>
        simp only [multisigVisits, List.nil_append, List.cons.injEq] at hv
        obtain ⟨rfl, -⟩ := hv
        simp [multisigLoop, hp]
      | cons q pre =>
        simp only [List.cons_append, multisigVisits_cons, List.cons.injEq] at hv
        obtain ⟨hq0, hv⟩ := hv
        subst hq0
        have hq := hpre (a, b) (by simp)
        rw [multisigLoop_cons hq]
        generalize (if R a b = true then as else a :: as) = rest at hv ⊢
        by_cases hl : bs.length < rest.length
        · simp [hl] at hv
        · simp only [hl, ite_false] at hv ⊢
          exact ih hv (fun q hq => hpre q (List.mem_cons_of_mem _ hq))

/-- For every flag set and signature: `checkSignatureEncoding` passes exactly when `SigEncodingOk` holds. -/
theorem checkSignatureEncoding_ok_iff (flags : UInt32) (sig : List UInt8) :
    checkSignatureEncoding sig flags = .ok () ↔ SigEncodingOk flags sig := by
  rw [checkSignatureEncoding_eq, SigEncodingOk]
  by_cases h0 : sig = []
  · simp [h0]
  · simp only [h0, ite_false]
    cases hd : hasFlag flags ScriptFlags.derSig <;> cases hl : hasFlag flags ScriptFlags.lowS <;>
      cases hs : hasFlag flags ScriptFlags.strictEnc <;> cases hv : isValidSignatureEncoding sig <;>
      cases hc : checkLowS sig.dropLast <;> cases hh : isDefinedHashtypeSignature sig <;> simp [h0]

/-- For every flag set and key: `checkPubKeyEncoding` passes exactly when `KeyEncodingOk` holds. -/
theorem checkPubKeyEncoding_ok_iff (flags : UInt32) (key : List UInt8) :
    checkPubKeyEncoding key flags = .ok () ↔ KeyEncodingOk flags key := by
  unfold checkPubKeyEncoding KeyEncodingOk
  cases hasFlag flags ScriptFlags.strictEnc <;> cases isCompressedOrUncompressedPubKey key <;> simp

/-- For every checker, flag set, script code and opcode: the pair check of `OP_CHECKMULTISIG` returns `v` exactly when both encoding predicates hold and the checker answers `some v`. -/
theorem multisigCheck_eq_ok_iff {c : SignatureChecker} {flags : UInt32} {code : List UInt8} {op : UInt8}
    {sig key : List UInt8} {v : Bool} :
    multisigCheck c flags code op sig key = .ok v ↔
      SigEncodingOk flags sig ∧ KeyEncodingOk flags key ∧ c.checkSig sig key code = some v := by
  rw [← checkSignatureEncoding_ok_iff, ← checkPubKeyEncoding_ok_iff]
  unfold multisigCheck
  cases checkSignatureEncoding sig flags <;> cases checkPubKeyEncoding key flags <;>
    cases c.checkSig sig key code <;> simp

/--
For every input context, verifier and script code shorter than 2^64 bytes, `sigAccepted` holds exactly when two conditions hold.
The key passes `isValidPubKey`.
`verify` returns `some true` on the signature without its last byte, the key, and the legacy digest with that last byte as the hash type.
-/
theorem sigAccepted_iff (ctx : InputContext) (verify : SignatureVerifier) {code : List UInt8}
    (hc : code.length < 2 ^ 64) (sig key : List UInt8) :
    sigAccepted ctx verify code sig key = true ↔
      isValidPubKey key = true ∧ ∃ s hashType, sig = s ++ [hashType] ∧
        verify s key (legacySignatureHash ⟨⟨code, hc⟩⟩ ctx.tx ctx.index hashType.toUInt32) = some true := by
  unfold sigAccepted
  cases hk : isValidPubKey key
  · simp [transactionChecker_invalidKey _ _ _ _ _ hk]
  · rcases List.eq_nil_or_concat sig with rfl | ⟨s, b, rfl⟩
    · simp [transactionChecker_emptySig _ _ _ _ hk]
    · rw [List.concat_eq_append, transactionChecker_verify _ _ _ _ _ hk hc]
      constructor
      · intro h; exact ⟨rfl, s, b, rfl, by simpa using h⟩
      · rintro ⟨-, s', b', he, hv⟩
        obtain ⟨rfl, hb⟩ := List.append_inj' he rfl
        simp only [List.cons.injEq, and_true] at hb
        subst hb
        simpa using hv



/-- For every script and cursor whose bytes start with an opcode above `OP_PUSHDATA4`: the reader reads that one byte, pushes nothing, and moves the cursor by one. -/
theorem readInstruction_op {s : List UInt8} {pc : Nat} {op : UInt8} {rest : List UInt8}
    (hd : s.drop pc = op :: rest) (hop : 0x4e < op) :
    readInstruction s pc = .instruction ⟨op, [op], [], pc + 1⟩ := by
  apply readInstruction_eq_instruction_iff.mpr
  have hn : 78 < op.toNat := UInt8.lt_iff_toNat_lt.mp hop
  have h1 : ¬op < 0x4c := fun h => by have := UInt8.lt_iff_toNat_lt.mp h; simp at this; omega
  have h2 : ¬op ≤ 0x4e := fun h => by have := UInt8.le_iff_toNat_le.mp h; simp at this; omega
  have h3 : op ≠ 0x4c := by rintro rfl; simp at hn
  have h4 : op ≠ 0x4d := by rintro rfl; simp at hn
  have h5 : op ≠ 0x4e := by rintro rfl; simp at hn
  refine ⟨[], rest, ⟨?_, ?_⟩, rfl, by simpa using hd, rfl⟩
  · simp [lengthFieldWidth, h3, h4, h5]
  · simp [pushSize, h1, h2]

/-- For data of fewer than 76 bytes, `CScript() << data` is the length byte and the data. -/
theorem pushEncoding_small {d : List UInt8} (hl : d.length < 76) : pushEncoding d = d.length.toUInt8 :: d := by
  simp [pushEncoding, pushHeader, hl]

private theorem small_facts : ∀ n, n < 76 →
    n.toUInt8 < 0x4c ∧ n.toUInt8 ≤ 0x4e ∧ isDisabled n.toUInt8 = false ∧ n.toUInt8.toNat = n ∧ ¬(0x60 : UInt8) < n.toUInt8 := by
  decide

/-- For every script and cursor whose bytes start with `pushEncoding d` for `d` of fewer than 76 bytes: the reader pushes `d` and moves the cursor past the push. -/
theorem readInstruction_push {s : List UInt8} {pc : Nat} {d rest : List UInt8}
    (hd : s.drop pc = pushEncoding d ++ rest) (hl : d.length < 76) :
    readInstruction s pc = .instruction ⟨d.length.toUInt8, pushEncoding d, d, pc + (d.length + 1)⟩ := by
  obtain ⟨h1, h2, -, h4, -⟩ := small_facts d.length hl
  apply readInstruction_eq_instruction_iff.mpr
  refine ⟨[], rest, ⟨?_, ?_⟩, by simp [pushEncoding_small hl], hd, by simp [pushEncoding_small hl]⟩
  · have : d.length.toUInt8 ≠ 0x4c ∧ d.length.toUInt8 ≠ 0x4d ∧ d.length.toUInt8 ≠ 0x4e := by
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> rw [h] at h1 <;> exact absurd h1 (by decide)
    simp [lengthFieldWidth, this.1, this.2.1, this.2.2]
  · simp [pushSize, h1, h4]

variable {checker : Option SignatureChecker} {flags : UInt32} {script : List UInt8}

/-- A direct push opcode does not count. -/
theorem countOp_small {n : Nat} (h : n < 76) (k : Nat) : countOp n.toUInt8 k = k := by
  simp [countOp, (small_facts n h).2.2.2.2]

/--
For every state in an executing branch at a cursor where the direct pushes of `keys` start: the loop pushes `keys` in order and moves past them.
It gives `STACK_SIZE` when the stacks would exceed 1,000 items. The opcode count is unchanged.
-/
theorem evalLoop_pushes_exec : ∀ (keys : List (List UInt8)) (s : ExecState) (tail : List UInt8),
    (∀ P ∈ keys, P.length < 76) → script.drop s.pc = (keys.map pushEncoding).flatten ++ tail →
    s.fExec = true → s.opCount ≤ maxOpsPerScript → s.stack.length + s.altstack.length ≤ maxStackItems →
    evalLoop checker flags script s =
      if maxStackItems < s.stack.length + s.altstack.length + keys.length then .rejected .stackSize
      else evalLoop checker flags script
        { s with pc := s.pc + ((keys.map pushEncoding).flatten).length, stack := s.stack ++ keys }
  | [], s, tail, _, _, _, _, hl => by simp [Nat.not_lt.mpr hl]
  | P :: ks, s, tail, hk, hd, hx, hc, hl => by
    have hP := hk P (by simp)
    obtain ⟨-, h2, h3, -, -⟩ := small_facts P.length hP
    have hd' : script.drop s.pc = pushEncoding P ++ ((ks.map pushEncoding).flatten ++ tail) := by
      simpa using hd
    rw [evalLoop_instruction (readInstruction_push hd' hP)]
    rw [evalInstruction_exec hx (by simp [maxScriptElementSize]; omega) (by rw [countOp_small hP]; exact hc) h3]
    rw [execOpcode_push h2]
    simp only [countOp_small hP, List.length_append, List.length_singleton]
    by_cases ho : maxStackItems < s.stack.length + 1 + s.altstack.length
    · have : maxStackItems < s.stack.length + s.altstack.length + (ks.length + 1) := by omega
      simp [ho, this]
    · simp only [ho, ite_false]
      have hpc : s.pc + (P.length + 1) ≤ script.length := by
        have := congrArg List.length hd'; simp [pushEncoding_small hP] at this; omega
      rw [evalLoop_pushes_exec ks { s with stack := s.stack ++ [P], pc := s.pc + (P.length + 1) } tail
        (fun Q hQ => hk Q (by simp [hQ]))
        (by
          have := hd'
          simp only [pushEncoding_small hP] at this ⊢
          rw [← List.drop_drop, this]; simp)
        hx hc (by simp; omega)]
      simp only [List.length_append, List.append_assoc, List.singleton_append,
        List.map_cons, List.flatten_cons, pushEncoding_small hP, List.length_cons]
      have e1 : s.stack.length + ([] : List (List UInt8)).length + 1 + s.altstack.length + ks.length =
          s.stack.length + s.altstack.length + (ks.length + 1) := by simp; omega
      rw [List.length_nil] at e1 ⊢
      rw [e1, Nat.add_assoc (s.pc)]

/-- For every state in a skipped branch within the stack limit, at a cursor where the direct pushes of `keys` start: the loop moves past them and changes nothing else. -/
theorem evalLoop_pushes_skip : ∀ (keys : List (List UInt8)) (s : ExecState) (tail : List UInt8),
    (∀ P ∈ keys, P.length < 76) → script.drop s.pc = (keys.map pushEncoding).flatten ++ tail →
    s.fExec = false → s.opCount ≤ maxOpsPerScript → s.WithinStackLimit →
    evalLoop checker flags script s =
      evalLoop checker flags script { s with pc := s.pc + ((keys.map pushEncoding).flatten).length }
  | [], s, tail, _, _, _, _, _ => by simp
  | P :: ks, s, tail, hk, hd, hx, hc, hl => by
    have hP := hk P (by simp)
    obtain ⟨h1, -, h3, -, -⟩ := small_facts P.length hP
    have hd' : script.drop s.pc = pushEncoding P ++ ((ks.map pushEncoding).flatten ++ tail) := by
      simpa using hd
    have hlt : P.length.toUInt8 < 0x63 ∨ 0x68 < P.length.toUInt8 := by
      left; exact UInt8.lt_trans h1 (by decide)
    rw [evalLoop_instruction (readInstruction_push hd' hP)]
    rw [evalInstruction_skipped hx hlt (by simp [maxScriptElementSize]; omega)
      (by rw [countOp_small hP]; exact hc) h3 hl]
    simp only [countOp_small hP]
    rw [evalLoop_pushes_skip ks { s with pc := s.pc + (P.length + 1) } tail
        (fun Q hQ => hk Q (by simp [hQ]))
        (by
          have := hd'
          simp only [pushEncoding_small hP] at this ⊢
          rw [← List.drop_drop, this]; simp)
        hx hc hl]
    simp only [List.map_cons, List.flatten_cons, List.length_append, pushEncoding_small hP, List.length_cons]
    congr 2; omega

/-- One executed instruction without pushed bytes, or one opcode from `OP_IF` to `OP_ENDIF`. -/
theorem evalLoop_op {s : ExecState} {op : UInt8} {rest : List UInt8} (hd : script.drop s.pc = op :: rest)
    (hop : 0x4e < op) (hx : s.fExec = true ∨ (0x63 ≤ op ∧ op ≤ 0x68))
    (hc : countOp op s.opCount ≤ maxOpsPerScript) (hdis : isDisabled op = false) :
    evalLoop checker flags script s =
      match execOpcode checker script flags s.fExec { s with opCount := countOp op s.opCount } op [] (s.pc + 1) with
      | .next t => if maxStackItems < t.stack.length + t.altstack.length then .rejected .stackSize
        else evalLoop checker flags script { t with pc := s.pc + 1 }
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u := by
  rw [evalLoop_instruction (readInstruction_op hd hop)]
  have hx' : ((s.fExec || (decide (0x63 ≤ op) && decide (op ≤ 0x68))) = true) := by
    rcases hx with h | ⟨h1, h2⟩ <;> simp_all
  simp only [evalInstruction, List.length_nil, Nat.not_lt_zero, ite_false, Nat.not_lt.mpr hc, hdis,
    Bool.false_eq_true]
  have hf : ({ s with opCount := countOp op s.opCount } : ExecState).fExec = s.fExec := rfl
  rw [hf]
  simp only [hx', ite_true]
  cases execOpcode checker script flags s.fExec { s with opCount := countOp op s.opCount } op [] (s.pc + 1) with
  | next t => by_cases h : maxStackItems < t.stack.length + t.altstack.length <;> simp [h]
  | rejected e => rfl
  | unsupported u => rfl

/-- One skipped instruction without pushed bytes, outside `OP_IF` to `OP_ENDIF`. -/
theorem evalLoop_op_skip {s : ExecState} {op : UInt8} {rest : List UInt8} (hd : script.drop s.pc = op :: rest)
    (hop : 0x4e < op) (hx : s.fExec = false) (hr : op < 0x63 ∨ 0x68 < op)
    (hc : countOp op s.opCount ≤ maxOpsPerScript) (hdis : isDisabled op = false) (hl : s.WithinStackLimit) :
    evalLoop checker flags script s =
      evalLoop checker flags script { s with opCount := countOp op s.opCount, pc := s.pc + 1 } := by
  rw [evalLoop_instruction (readInstruction_op hd hop), evalInstruction_skipped hx hr (by simp) hc hdis hl]

/-- For `1 ≤ k ≤ 16`, `OP_k` is a small-integer opcode that is not a push, not disabled and not counted, outside `OP_IF` to `OP_ENDIF`, with the value `k`. -/
theorem smallIntOpcode_facts : ∀ k, k < 17 → 1 ≤ k →
    0x4e < smallIntOpcode k ∧ 0x51 ≤ smallIntOpcode k ∧ smallIntOpcode k ≤ 0x60 ∧ smallIntOpcode k < 0x63 ∧
      isDisabled (smallIntOpcode k) = false ∧ (smallIntOpcode k).toNat = 0x50 + k ∧
      ¬(0x60 : UInt8) < smallIntOpcode k := by
  decide

/-- The bytes after the key pushes. -/
def redeemTail (n : Nat) (recovery : List UInt8) : List UInt8 :=
  [smallIntOpcode n, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75] ++ pushEncoding recovery ++ [0xac, 0x68]

/-- The redeem script as `OP_IF`, `OP_k`, the key pushes and `redeemTail`. -/
theorem multisigRecoveryScript_eq (k : Nat) (keys : List (List UInt8)) (recovery : List UInt8) :
    multisigRecoveryScript k keys recovery =
      0x63 :: smallIntOpcode k :: ((keys.map pushEncoding).flatten ++ redeemTail keys.length recovery) := by
  simp [multisigRecoveryScript, redeemTail, recoveryLockTimePush]

/-- The bytes of the redeem script from a cursor after the key pushes. -/
theorem multisigRecoveryScript_drop {k : Nat} {keys : List (List UInt8)} {recovery : List UInt8} {p j : Nat}
    (h : p = 2 + ((keys.map pushEncoding).flatten).length + j) :
    (multisigRecoveryScript k keys recovery).drop p = (redeemTail keys.length recovery).drop j := by
  subst h
  rw [multisigRecoveryScript_eq, show 2 + ((keys.map pushEncoding).flatten).length + j =
    (((keys.map pushEncoding).flatten).length + j) + 1 + 1 by omega]
  simp only [List.drop_succ_cons, List.drop_append]
  simp

/-- Dropping the 34 bytes of a 33-byte push. -/
theorem pushEncoding_drop {R l : List UInt8} (hR : R.length = 33) : (pushEncoding R ++ l).drop 34 = l := by
  rw [pushEncoding_small (by omega), List.cons_append, List.drop_succ_cons, List.drop_left' hR]

/-- The key pushes of 33-byte keys have 34 bytes each. -/
theorem keys_flatten_length {keys : List (List UInt8)} (hkeys : ∀ P ∈ keys, P.length = 33) :
    ((keys.map pushEncoding).flatten).length = 34 * keys.length := by
  induction keys with
  | nil => rfl
  | cons P ks ih =>
    have hP := hkeys P (by simp)
    simp [pushEncoding_small (show P.length < 76 by omega), hP, ih (fun Q hQ => hkeys Q (by simp [hQ]))]
    omega

/-- For 33-byte keys and recovery key, the redeem script has `34 n + 47` bytes, where `n` is the number of keys: 149 bytes for 2-of-3. -/
theorem multisigRecoveryScript_length {k : Nat} {keys : List (List UInt8)} {recovery : List UInt8}
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : recovery.length = 33) :
    (multisigRecoveryScript k keys recovery).length = 34 * keys.length + 47 := by
  rw [multisigRecoveryScript_eq]
  simp [redeemTail, keys_flatten_length hkeys, pushEncoding_small (show recovery.length < 76 by omega), hR]

/--
Take any checker, a supported flag set, and a stack `S1 ++ [sel]` with a true selector and at most 998 items in `S1`.
The redeem script runs `OP_IF` and pushes `k`, the keys and `n`. It then runs `OP_CHECKMULTISIG` on that stack.
It gives `STACK_SIZE` when the pushes exceed 1,000 items.
-/
theorem evalScript_redeem_true {c : SignatureChecker} {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16)
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33)
    {S1 : List (List UInt8)} {sel : List UInt8} (hsel : castToBool sel = true)
    (hS : S1.length + 2 ≤ maxStackItems) :
    evalScript (some c) flags (multisigRecoveryScript k keys R) (S1 ++ [sel]) =
      if maxStackItems < S1.length + keys.length + 2 then .rejected .stackSize
      else
        match checkMultisigStep c (multisigRecoveryScript k keys R) flags
          ⟨S1 ++ [ScriptNum.encode k] ++ keys ++ [ScriptNum.encode keys.length], [],
            2 + ((keys.map pushEncoding).flatten).length + 1, 0, [true], 2⟩ 0xae with
        | .next t => if maxStackItems < t.stack.length + t.altstack.length then .rejected .stackSize
          else evalLoop (some c) flags (multisigRecoveryScript k keys R)
            { t with pc := 2 + ((keys.map pushEncoding).flatten).length + 2 }
        | .rejected e => .rejected e
        | .unsupported u => .unsupported u := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := smallIntOpcode_facts k (by omega) hk1
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := smallIntOpcode_facts keys.length (by omega) (by omega)
  have hlen := multisigRecoveryScript_length (k := k) hkeys hR
  have hsz : ¬maxScriptSize < (multisigRecoveryScript k keys R).length := by
    rw [hlen]; simp [maxScriptSize]; omega
  have hf' : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  unfold evalScript
  simp only [hf', hsz, ite_false]
  -- OP_IF
  rw [evalLoop_op (op := 0x63) (by simp [ExecState.init, multisigRecoveryScript_eq]; rfl) (by decide)
    (Or.inl rfl) (by simp [countOp, ExecState.init, maxOpsPerScript]) (by decide)]
  simp only [ExecState.init, ExecState.fExec, List.contains_nil, Bool.not_false]
  rw [execOpcode_if (rest := S1) (x := sel) rfl]
  simp only [hsel, List.length_nil, Nat.add_zero, show ¬maxStackItems < S1.length by omega, ite_false,
    List.nil_append, Nat.zero_add, show countOp 99 0 = 1 from rfl]
  -- OP_k
  rw [evalLoop_op (op := smallIntOpcode k) (by simp [multisigRecoveryScript_eq]; rfl) k1
    (Or.inl rfl) (by simp [countOp, k7, maxOpsPerScript]) k5]
  simp only [ExecState.fExec, List.contains_cons, List.contains_nil, Bool.or_false]
  rw [execOpcode_smallInteger (Or.inr ⟨k2, k3⟩)]
  simp only [k6, countOp, k7, ite_false, List.length_append, List.length_singleton, List.length_nil,
    Nat.add_zero, show ¬maxStackItems < S1.length + 1 by omega]
  have e1 : ((80 + k : Nat) : Int) - 80 = (k : Int) := by omega
  rw [e1]
  -- the key pushes
  rw [evalLoop_pushes_exec keys _ (redeemTail keys.length R) (fun P hP => by have := hkeys P hP; omega)
    (by simp [multisigRecoveryScript_eq]) rfl (by simp [maxOpsPerScript]) (by simp; omega)]
  simp only [List.length_append, List.length_singleton, List.length_nil, Nat.add_zero]
  by_cases ho : maxStackItems < S1.length + 1 + keys.length
  · simp [ho, show maxStackItems < S1.length + keys.length + 2 by omega]
  simp only [ho, ite_false]
  -- OP_n
  rw [evalLoop_op (op := smallIntOpcode keys.length)
    (by rw [multisigRecoveryScript_drop (j := 0) (by simp <;> omega)]; rfl) n1
    (Or.inl rfl) (by simp [countOp, n7, maxOpsPerScript]) n5]
  simp only [ExecState.fExec, List.contains_cons, List.contains_nil, Bool.or_false]
  rw [execOpcode_smallInteger (Or.inr ⟨n2, n3⟩)]
  have e2 : ((80 + keys.length : Nat) : Int) - 80 = (keys.length : Int) := by omega
  simp only [n6, e2, countOp, n7, ite_false, List.length_append, List.length_singleton, List.length_nil,
    Nat.add_zero]
  by_cases ho2 : maxStackItems < S1.length + 1 + keys.length + 1
  · simp [ho2, show maxStackItems < S1.length + keys.length + 2 by omega]
  simp only [ho2, ite_false, show ¬maxStackItems < S1.length + keys.length + 2 by omega]
  -- OP_CHECKMULTISIG
  rw [evalLoop_op (op := 0xae)
    (by rw [multisigRecoveryScript_drop (j := 1) (by simp <;> omega)]; try rfl) (by decide)
    (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
  simp only [ExecState.fExec, List.contains_cons, List.contains_nil, Bool.or_false]
  rw [execOpcode_checkMultisig (Or.inl rfl)]
  simp only [countOp, show (0x60 : UInt8) < 0xae by decide, ite_true]

/-- After `OP_CHECKMULTISIG` in the ordinary branch, the rest of the redeem script succeeds: `OP_ELSE` skips the recovery branch and `OP_ENDIF` closes it, adding 5 to the opcode count. -/
theorem evalLoop_redeem_ordinaryTail {c : SignatureChecker} {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33) {t : ExecState}
    (hv : t.vfExec = [true]) (hl : t.WithinStackLimit) (hc : t.opCount + 5 ≤ maxOpsPerScript) :
    evalLoop (some c) flags (multisigRecoveryScript k keys R)
        { t with pc := 2 + ((keys.map pushEncoding).flatten).length + 2 } =
      .ok { t with pc := (multisigRecoveryScript k keys R).length, vfExec := [], opCount := t.opCount + 5 } := by
  have hlen := multisigRecoveryScript_length (k := k) hkeys hR
  have hL := keys_flatten_length hkeys
  have hR' : R.length < 76 := by omega
  -- OP_ELSE
  rw [evalLoop_op (op := 0x67) (by rw [multisigRecoveryScript_drop (j := 2) (by simp <;> omega)]; try rfl)
    (by decide) (Or.inr ⟨by decide, by decide⟩) (by simp [countOp]; omega) (by decide)]
  rw [execOpcode_else (v := []) (b := true) (by simpa using hv)]
  simp only [countOp, show (0x60 : UInt8) < 0x67 by decide, ite_true, Bool.not_true]
  simp only [ExecState.WithinStackLimit] at hl
  simp only [Nat.not_lt.mpr hl, ite_false, List.nil_append]
  -- the skipped lock-time push
  have hlp : ([0x40, 0x42, 0x0f] : List UInt8).length < 76 := by decide
  rw [evalLoop_instruction (readInstruction_push (d := [0x40, 0x42, 0x0f])
    (by rw [multisigRecoveryScript_drop (j := 3) (by simp <;> omega)]; rfl) hlp)]
  rw [evalInstruction_skipped (by rfl) (Or.inl (by dsimp only; decide)) (by dsimp only; decide)
    (by dsimp only; simp [countOp]; omega) (by dsimp only; decide)
    (by simpa [ExecState.WithinStackLimit] using hl)]
  simp only [countOp, show ¬(0x60 : UInt8) < (List.length [(0x40 : UInt8), 0x42, 0x0f]).toUInt8 by decide, ite_false]
  -- OP_CHECKLOCKTIMEVERIFY, OP_DROP, skipped
  rw [evalLoop_op_skip (op := 0xb1) (by rw [multisigRecoveryScript_drop (j := 7) (by simp <;> omega)]; try rfl)
    (by decide) rfl (Or.inr (by decide)) (by simp [countOp]; omega) (by decide)
    (by simpa [ExecState.WithinStackLimit] using hl)]
  rw [evalLoop_op_skip (op := 0x75) (by rw [multisigRecoveryScript_drop (j := 8) (by simp <;> omega)]; try rfl)
    (by decide) rfl (Or.inr (by decide)) (by simp [countOp]; omega) (by decide)
    (by simpa [ExecState.WithinStackLimit] using hl)]
  simp only [countOp, show (0x60 : UInt8) < 0xb1 by decide, show (0x60 : UInt8) < 0x75 by decide, ite_true]
  -- the skipped push of R
  rw [evalLoop_instruction (readInstruction_push (d := R) (rest := [0xac, 0x68])
    (by rw [multisigRecoveryScript_drop (j := 9) (by simp <;> omega)]; simp [redeemTail]) hR')]
  rw [evalInstruction_skipped (by rfl) (Or.inl (by dsimp only; rw [hR]; decide))
    (by dsimp only; simp [maxScriptElementSize]; omega)
    (by dsimp only; rw [hR]; simp [countOp]; omega) (by dsimp only; rw [hR]; decide)
    (by simpa [ExecState.WithinStackLimit] using hl)]
  simp only [hR, countOp, show ¬(0x60 : UInt8) < (33 : Nat).toUInt8 by decide, ite_false]
  -- OP_CHECKSIG, skipped
  rw [evalLoop_op_skip (op := 0xac) (by rw [multisigRecoveryScript_drop (j := 43) (by simp <;> omega)]; simp only [redeemTail, List.cons_append, List.drop_succ_cons, List.nil_append]; rw [pushEncoding_drop hR])
    (by decide) rfl (Or.inr (by decide)) (by simp [countOp]; omega) (by decide)
    (by simpa [ExecState.WithinStackLimit] using hl)]
  -- OP_ENDIF
  rw [evalLoop_op (op := 0x68) (by rw [multisigRecoveryScript_drop (j := 44) (by simp <;> omega)]; simp only [redeemTail, List.cons_append, List.drop_succ_cons, List.nil_append]; rw [show 35 = 34 + 1 from rfl, ← List.drop_drop, pushEncoding_drop hR]; rfl)
    (by decide) (Or.inr ⟨by decide, by decide⟩) (by simp [countOp]; omega) (by decide)]
  rw [execOpcode_endif (v := []) (b := false) rfl]
  simp only [countOp, show (0x60 : UInt8) < 0xac by decide, show (0x60 : UInt8) < 0x68 by decide, ite_true,
    Nat.not_lt.mpr hl, ite_false]
  rw [evalLoop_atEnd (by simp [hlen, hL]; omega)]
  simp only [ite_true, EvalResult.ok.injEq, ExecState.mk.injEq, true_and, and_true]
  simp [hlen, hL]; omega

/-- The operand `40 42 0f` decodes to 1,000,000 in five bytes. -/
theorem decode_lockTimeOperand : ScriptNum.decode [0x40, 0x42, 0x0f] false lockTimeNumSize = .ok 1000000 := by
  rfl

/--
Take any checker, a supported flag set with `CHECKLOCKTIMEVERIFY`, and a stack `S1 ++ [sel]` with a false selector and at most 998 items in `S1`.
The redeem script skips the multisig branch and calls `checkLockTime 1000000`.
On `some true` it drops the operand, pushes `R` and runs `OP_CHECKSIG` on `S1 ++ [R]`.
-/
theorem evalScript_redeem_false {c : SignatureChecker} {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hcltv : hasFlag flags ScriptFlags.checkLockTimeVerify = true)
    (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16)
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33)
    {S1 : List (List UInt8)} {sel : List UInt8} (hsel : castToBool sel = false)
    (hS : S1.length + 2 ≤ maxStackItems) :
    evalScript (some c) flags (multisigRecoveryScript k keys R) (S1 ++ [sel]) =
      match c.checkLockTime 1000000 with
      | none => .unsupported .checkLockTimeVerify
      | some false => .rejected .unsatisfiedLocktime
      | some true =>
        match checkSigStep c (multisigRecoveryScript k keys R) flags
          ⟨S1 ++ [R], [], 2 + ((keys.map pushEncoding).flatten).length + 43, 0, [true], 6⟩ 0xac with
        | .next t => if maxStackItems < t.stack.length + t.altstack.length then .rejected .stackSize
          else .ok { t with pc := (multisigRecoveryScript k keys R).length, vfExec := [], opCount := 7 }
        | .rejected e => .rejected e
        | .unsupported u => .unsupported u := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := smallIntOpcode_facts k (by omega) hk1
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := smallIntOpcode_facts keys.length (by omega) (by omega)
  have hlen := multisigRecoveryScript_length (k := k) hkeys hR
  have hL := keys_flatten_length hkeys
  have hR' : R.length < 76 := by omega
  have hsz : ¬maxScriptSize < (multisigRecoveryScript k keys R).length := by
    rw [hlen]; simp [maxScriptSize]; omega
  have hf' : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  have hl0 : S1.length ≤ maxStackItems := by omega
  unfold evalScript
  simp only [hf', hsz, ite_false]
  -- OP_IF
  rw [evalLoop_op (op := 0x63) (by simp [ExecState.init, multisigRecoveryScript_eq]; rfl) (by decide)
    (Or.inl rfl) (by simp [countOp, ExecState.init, maxOpsPerScript]) (by decide)]
  simp only [ExecState.init, ExecState.fExec, List.contains_nil, Bool.not_false]
  rw [execOpcode_if (rest := S1) (x := sel) rfl]
  simp only [hsel, List.length_nil, Nat.add_zero, Nat.not_lt.mpr hl0, ite_false,
    List.nil_append, Nat.zero_add, show countOp 99 0 = 1 from rfl]
  have hwl : ∀ (s : ExecState), s.stack = S1 → s.altstack = [] → s.WithinStackLimit := by
    intro s h1 h2; simp [ExecState.WithinStackLimit, h1, h2]; omega
  -- the skipped multisig branch
  rw [evalLoop_op_skip (op := smallIntOpcode k) (by simp [multisigRecoveryScript_eq]; rfl) k1 rfl (Or.inl k4)
    (by simp [countOp, k7, maxOpsPerScript]) k5 (hwl _ rfl rfl)]
  rw [evalLoop_pushes_skip keys _ (redeemTail keys.length R) (fun P hP => by have := hkeys P hP; omega)
    (by simp [multisigRecoveryScript_eq]) rfl (by simp [countOp, k7, maxOpsPerScript]) (hwl _ rfl rfl)]
  rw [evalLoop_op_skip (op := smallIntOpcode keys.length)
    (by rw [multisigRecoveryScript_drop (j := 0) (by simp <;> omega)]; try rfl) n1 rfl (Or.inl n4)
    (by simp [countOp, k7, n7, maxOpsPerScript]) n5 (hwl _ rfl rfl)]
  rw [evalLoop_op_skip (op := 0xae)
    (by rw [multisigRecoveryScript_drop (j := 1) (by simp <;> omega)]; try rfl) (by decide) rfl (Or.inr (by decide))
    (by simp [countOp, k7, n7, maxOpsPerScript]) (by decide) (hwl _ rfl rfl)]
  simp only [countOp, k7, n7, ite_false, show (0x60 : UInt8) < 0xae by decide, ite_true]
  -- OP_ELSE
  rw [evalLoop_op (op := 0x67) (by rw [multisigRecoveryScript_drop (j := 2) (by simp <;> omega)]; try rfl)
    (by decide) (Or.inr ⟨by decide, by decide⟩) (by simp [countOp, maxOpsPerScript]) (by decide)]
  rw [execOpcode_else (v := []) (b := false) rfl]
  simp only [countOp, show (0x60 : UInt8) < 0x67 by decide, ite_true, Bool.not_false, List.nil_append,
    List.length_nil, Nat.add_zero, Nat.not_lt.mpr hl0, ite_false]
  -- the lock-time push
  rw [evalLoop_pushes_exec [[0x40, 0x42, 0x0f]] _ (0xb1 :: 0x75 :: (pushEncoding R ++ [0xac, 0x68])) (by decide)
    (by rw [multisigRecoveryScript_drop (j := 3) (by simp <;> omega)]; rfl) rfl (by simp [maxOpsPerScript])
    (by simp; omega)]
  simp only [List.length_singleton, List.length_nil, Nat.add_zero, show ¬maxStackItems < S1.length + 1 by omega,
    ite_false]
  -- OP_CHECKLOCKTIMEVERIFY
  rw [evalLoop_op (op := 0xb1) (by rw [multisigRecoveryScript_drop (j := 7) (by simp [pushEncoding, pushHeader] <;> omega)]; try rfl)
    (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
  simp only [ExecState.fExec, List.contains_cons, List.contains_nil, Bool.or_false]
  rw [execOpcode_cltv_checked hcltv (rest := S1) (top := [0x40, 0x42, 0x0f]) rfl decode_lockTimeOperand
    (by decide)]
  cases hlt : c.checkLockTime 1000000 with
  | none => rfl
  | some b =>
    cases b with
    | false => rfl
    | true =>
      simp only [countOp, show (0x60 : UInt8) < 0xb1 by decide, ite_true, List.length_append,
        List.length_singleton, List.length_nil, Nat.add_zero, show ¬maxStackItems < S1.length + 1 by omega, ite_false]
      -- OP_DROP
      rw [evalLoop_op (op := 0x75) (by rw [multisigRecoveryScript_drop (j := 8) (by simp [pushEncoding, pushHeader] <;> omega)]; try rfl)
        (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
      rw [execOpcode_drop (rest := S1) (x := [0x40, 0x42, 0x0f]) rfl]
      simp only [countOp, show (0x60 : UInt8) < 0x75 by decide, ite_true, List.length_nil, Nat.add_zero,
        Nat.not_lt.mpr hl0, ite_false]
      -- the push of R
      rw [evalLoop_pushes_exec [R] _ [0xac, 0x68] (by simp; omega)
        (by rw [multisigRecoveryScript_drop (j := 9) (by simp [pushEncoding, pushHeader] <;> omega)]; simp [redeemTail]) rfl
        (by simp [maxOpsPerScript]) (by simp; omega)]
      simp only [List.length_singleton, List.length_nil, Nat.add_zero, show ¬maxStackItems < S1.length + 1 by omega,
        ite_false]
      -- OP_CHECKSIG
      rw [evalLoop_op (op := 0xac)
        (by rw [multisigRecoveryScript_drop (j := 43) (by simp [pushEncoding, pushHeader, hR] <;> omega)]; simp only [redeemTail, List.cons_append, List.drop_succ_cons, List.nil_append]; rw [pushEncoding_drop hR])
        (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
      rw [execOpcode_checkSig (Or.inl rfl)]
      simp only [countOp, show (0x60 : UInt8) < 0xac by decide, ite_true]
      have hR1 : (([R].map pushEncoding).flatten).length = 34 := by simp [pushEncoding_small hR', hR]
      have hlp : (([[0x40, 0x42, 0x0f]].map pushEncoding).flatten).length = 4 := rfl
      simp only [hR1, hlp]
      rw [show 1 + 1 + ((keys.map pushEncoding).flatten).length + 1 + 1 + 1 + 4 + 1 + 1 + 34 =
        2 + ((keys.map pushEncoding).flatten).length + 43 by omega]
      cases hcs : checkSigStep c (multisigRecoveryScript k keys R) flags
          ⟨S1 ++ [R], [], 2 + ((keys.map pushEncoding).flatten).length + 43, 0, [true], 6⟩ 0xac with
      | rejected e => rfl
      | unsupported u => rfl
      | next t =>
        obtain ⟨hp, ho, hb, hv, ha⟩ := checkSigStep_frame hcs
        simp only at hp ho hb hv ha
        by_cases hov : maxStackItems < t.stack.length + t.altstack.length
        · simp [hov]
        simp only [hov, ite_false]
        -- OP_ENDIF
        rw [evalLoop_op (op := 0x68) (by rw [multisigRecoveryScript_drop (j := 44) (by simp <;> omega)]; simp only [redeemTail, List.cons_append, List.drop_succ_cons, List.nil_append]; rw [show 35 = 34 + 1 from rfl, ← List.drop_drop, pushEncoding_drop hR]; rfl)
          (by decide) (Or.inr ⟨by decide, by decide⟩) (by simp [countOp, ho, maxOpsPerScript]) (by decide)]
        rw [execOpcode_endif (v := []) (b := true) (by simpa using hv)]
        simp only [countOp, show (0x60 : UInt8) < 0x68 by decide, ite_true, hov, ite_false]
        rw [evalLoop_atEnd (by simp [hlen, hL]; omega)]
        simp only [ite_true, EvalResult.ok.injEq, ExecState.mk.injEq, true_and]
        refine ⟨?_, by omega⟩
        simp [hlen, hL]; omega

section
variable {flags : UInt32}

/-- The true-top check of a stack that ends with `boolBytes b` is `b`. -/
theorem trueTop_boolBytes (S : List (List UInt8)) (b : Bool) : trueTop (S ++ [boolBytes b]) = b := by
  cases b <;> simp [trueTop, boolBytes, castToBool, castToBoolLoop]

/-- A count from 0 to 16 decodes to itself in four bytes, and `getint` keeps it. -/
theorem decode_encode_small {n : Nat} (h : n ≤ 16) :
    ScriptNum.decode (ScriptNum.encode n) false = .ok n ∧ ScriptNum.getint n = n := by
  refine ⟨ScriptNum.decode_encode_default false (by omega), (ScriptNum.getint_eq_self_iff _).mpr ⟨by omega, by omega⟩⟩

/--
The ordinary branch on `below ++ dummy :: sigs ++ [sel]` with `k` signatures, a true selector and room for the pushes, once the matching loop returns.
A result `b` gives `SIG_NULLDUMMY` for a nonempty dummy under `NULLDUMMY`, and otherwise acceptance exactly when `b` holds.
An error of the loop is a rejection or an unsupported result with the same value.
-/
theorem finishEval_redeem_ordinary {c : SignatureChecker} {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16)
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33)
    {below sigs : List (List UInt8)} {dummy sel : List UInt8} (hsel : castToBool sel = true)
    (hsigs : sigs.length = k) (hS : below.length + 1 + sigs.length + keys.length + 2 ≤ maxStackItems) :
    (∀ b, multisigLoop (multisigCheck c flags (ordinaryCode (multisigRecoveryScript k keys R) sigs) 0xae)
        sigs.reverse keys.reverse = .ok b →
      finishEval (evalScript (some c) flags (multisigRecoveryScript k keys R) (below ++ dummy :: sigs ++ [sel])) =
        if hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty then .rejected .sigNullDummy
        else if b then .accepted else .rejected .evalFalse) ∧
    (∀ r, multisigLoop (multisigCheck c flags (ordinaryCode (multisigRecoveryScript k keys R) sigs) 0xae)
        sigs.reverse keys.reverse = .error r →
      (∃ e, r = .rejected e ∧
        finishEval (evalScript (some c) flags (multisigRecoveryScript k keys R) (below ++ dummy :: sigs ++ [sel])) =
          .rejected e) ∨
      (∃ u, r = .unsupported u ∧
        finishEval (evalScript (some c) flags (multisigRecoveryScript k keys R) (below ++ dummy :: sigs ++ [sel])) =
          .unsupported u)) := by
  have hS1 : (below ++ dummy :: sigs).length + 2 ≤ maxStackItems := by simp; omega
  have heq : below ++ dummy :: sigs ++ [sel] = (below ++ dummy :: sigs) ++ [sel] := rfl
  rw [heq, evalScript_redeem_true hf hk1 hkn hn hkeys hR hsel hS1]
  have hno : ¬maxStackItems < (below ++ dummy :: sigs).length + keys.length + 2 := by simp; omega
  simp only [hno, ite_false]
  obtain ⟨dn, gn⟩ := decode_encode_small hn
  obtain ⟨dk, gk⟩ := decode_encode_small (show k ≤ 16 by omega)
  have hcount := checkMultisigStep_counted (c := c) (script := multisigRecoveryScript k keys R) (flags := flags)
    (op := 0xae)
    (s := ⟨below ++ dummy :: sigs ++ [ScriptNum.encode k] ++ keys ++ [ScriptNum.encode keys.length], [],
      2 + ((keys.map pushEncoding).flatten).length + 1, 0, [true], 2⟩)
    (keys := keys.reverse) (sigs := sigs.reverse) (below := below.reverse) (dummy := dummy)
    (by simp) dn (by simpa using gn) dk (by simpa [hsigs] using gk) (by simp [maxPubKeysPerMultisig]; omega)
    (by simp; omega) (by simp [maxOpsPerScript]; omega)
  rw [hcount]
  have htail := fun (b : Bool) => evalLoop_redeem_ordinaryTail (c := c) (flags := flags) (k := k) hkeys hR
    (t := ⟨below ++ [boolBytes b], [], 2 + ((keys.map pushEncoding).flatten).length + 1, 0, [true],
      2 + keys.length⟩) rfl (by simp [ExecState.WithinStackLimit]; omega) (by simp [maxOpsPerScript]; omega)
  refine ⟨fun b hb => ?_, fun r hr => ?_⟩
  · rw [show ordinaryCode (multisigRecoveryScript k keys R) sigs =
      effectiveScriptCode (multisigRecoveryScript k keys R) 0 sigs.reverse from rfl] at hb
    simp only [] at hb ⊢
    rw [hb]
    by_cases hd : (hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty) = true
    · simp [hd, finishEval]
    · simp only [hd, ite_false, Bool.false_eq_true, show (0xae : UInt8) ≠ 0xaf by decide]
      simp only [List.reverse_reverse, List.length_reverse]
      rw [htail b]
      have hb1 : ¬maxStackItems < below.length + 1 := by omega
      cases b <;> simp [finishEval, trueTop_boolBytes, hb1]
  · rw [show ordinaryCode (multisigRecoveryScript k keys R) sigs =
      effectiveScriptCode (multisigRecoveryScript k keys R) 0 sigs.reverse from rfl] at hr
    simp only [] at hr ⊢
    rw [hr]
    have hne := multisigLoop_multisigCheck_error hr
    cases r with
    | next t => exact absurd rfl (hne t)
    | rejected e => exact .inl ⟨e, rfl, rfl⟩
    | unsupported u => exact .inr ⟨u, rfl, rfl⟩

/-- A successful `OP_CHECKSIG` step shortens the main stack. -/
theorem checkSigStep_stack_length {c : SignatureChecker} {script : List UInt8} {s t : ExecState} {op : UInt8}
    (h : checkSigStep c script flags s op = .next t) : t.stack.length < s.stack.length := by
  unfold checkSigStep at h
  split at h
  · rename_i key sig rest heq
    have hl := congrArg List.length heq
    simp only [List.length_reverse, List.length_cons] at hl
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (injection h with h; subst h; simp; omega)
  · cases h

/-- For the operand 1,000,000, `lockTimeSatisfied` holds exactly when the lock time is at least 1,000,000 and below 500,000,000 and the sequence is not final. -/
theorem lockTimeSatisfied_recovery (lockTime sequence : UInt32) :
    lockTimeSatisfied lockTime sequence 1000000 = true ↔
      recoveryLockTime ≤ lockTime.toNat ∧ lockTime.toNat < lockTimeThreshold ∧ sequence ≠ sequenceFinal := by
  rw [lockTimeSatisfied_iff]
  simp only [recoveryLockTime, lockTimeThreshold, sequenceFinal]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨Or.inl ⟨h2, by omega⟩, by omega, h3⟩

/--
The recovery branch over `transactionChecker` on `S1 ++ [sel]` with a false selector.
It gives `UNSATISFIED_LOCKTIME` unless the lock-time conditions hold.
Otherwise it gives the result of `OP_CHECKSIG` on `S1 ++ [R]`, with the true-top check.
-/
theorem finishEval_redeem_recovery (ctx : InputContext) (verify : SignatureVerifier) {k : Nat}
    {keys : List (List UInt8)} {R : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hcltv : hasFlag flags ScriptFlags.checkLockTimeVerify = true)
    (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16)
    (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33)
    {S1 : List (List UInt8)} {sel : List UInt8} (hsel : castToBool sel = false)
    (hS : S1.length + 2 ≤ maxStackItems) :
    finishEval (evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags
        (multisigRecoveryScript k keys R) (S1 ++ [sel])) =
      if recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
          ctx.input.sequence ≠ sequenceFinal then
        match checkSigStep (transactionChecker ctx.tx ctx.index verify) (multisigRecoveryScript k keys R) flags
          ⟨S1 ++ [R], [], 2 + ((keys.map pushEncoding).flatten).length + 43, 0, [true], 6⟩ 0xac with
        | .next t => if trueTop t.stack then .accepted else .rejected .evalFalse
        | .rejected e => .rejected e
        | .unsupported u => .unsupported u
      else .rejected .unsatisfiedLocktime := by
  rw [evalScript_redeem_false hf hcltv hk1 hkn hn hkeys hR hsel hS,
    transactionChecker_checkLockTime verify ctx.getElem?_index]
  by_cases hl : recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
      ctx.input.sequence ≠ sequenceFinal
  · rw [(lockTimeSatisfied_recovery _ _).mpr hl]
    simp only [hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
    cases hcs : checkSigStep (transactionChecker ctx.tx ctx.index verify) (multisigRecoveryScript k keys R) flags
        ⟨S1 ++ [R], [], 2 + ((keys.map pushEncoding).flatten).length + 43, 0, [true], 6⟩ 0xac with
    | next t =>
      have h1 := checkSigStep_stack_length hcs
      have h2 := (checkSigStep_frame hcs).2.2.2.2
      simp only [List.length_append, List.length_singleton] at h1 h2
      have hno : ¬maxStackItems < t.stack.length + t.altstack.length := by rw [h2]; simp; omega
      simp [hno, finishEval]
    | rejected e => rfl
    | unsupported u => rfl
  · simp only [hl, ↓reduceIte]
    have : lockTimeSatisfied ctx.tx.lockTime ctx.input.sequence 1000000 = false := by
      cases h : lockTimeSatisfied ctx.tx.lockTime ctx.input.sequence 1000000
      · rfl
      · exact absurd ((lockTimeSatisfied_recovery _ _).mp h) hl
    rw [this]; rfl


/-- A HASH160 digest has 20 bytes. -/
theorem hash160_toList_length (m : ByteArray) : (Cryptography.Hash.hash160 m).toList.length = 20 := by
  rw [ByteArray.toList_eq_data_toList, Array.length_toList]
  exact Cryptography.Hash.Hash160.size_hash m

/-- For every checker and supported flag set: on a stack of exactly 1,000 items, the P2SH template gives `STACK_SIZE` at its push of the digest. -/
theorem evalScript_p2shTemplate_overflow {c : SignatureChecker} {h x : List UInt8} {S : List (List UInt8)}
    (hf : unsupportedFlagBits flags = 0) (hh : h.length = 20) (hS1 : S.length + 1 ≤ maxStackItems)
    (hS2 : maxStackItems < S.length + 2) :
    evalScript (some c) flags ([0xa9, 0x14] ++ h ++ [0x87]) (S ++ [x]) = .rejected .stackSize := by
  have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  have h2 : ¬maxScriptSize < ([0xa9, 0x14] ++ h ++ [0x87] : List UInt8).length := by simp [hh, maxScriptSize]
  unfold evalScript
  simp only [h1, h2, ite_false]
  rw [evalLoop_op (op := 0xa9) (by simp [ExecState.init]; rfl) (by decide) (Or.inl rfl)
    (by simp [countOp, ExecState.init, maxOpsPerScript]) (by decide)]
  simp only [execOpcode, hashTop, ExecState.init]
  simp only [show ¬(0xa9 : UInt8) ≤ 0x4e by decide, ite_false, show ¬((0xa9 : UInt8) = 0x4f ∨ 0x51 ≤ (0xa9 : UInt8) ∧ (0xa9 : UInt8) ≤ 0x60) by decide,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.reverse_reverse,
    List.length_append, List.length_singleton, List.length_nil, Nat.add_zero, show ¬maxStackItems < S.length + 1 by omega]
  have hpe : pushEncoding h = 0x14 :: h := by rw [pushEncoding_small (by omega), hh]; rfl
  rw [evalLoop_pushes_exec [h] _ [0x87] (by simp; omega) (by simp [hpe]) rfl
    (by simp [countOp, maxOpsPerScript]) (by simp; omega)]
  simp [show maxStackItems < S.length + 1 + 1 by omega]

/-- For every checker and flag set: a successful `scriptSig` evaluation whose final stack is `S ++ [redeem]` leaves at most 999 items in `S`. -/
theorem scriptSig_stack_bound {c : SignatureChecker} {ss redeem : List UInt8} {s : ExecState}
    {S : List (List UInt8)} (hss : evalScript (some c) flags ss [] = .ok s) (hS : s.stack = S ++ [redeem]) :
    S.length + 1 ≤ maxStackItems := by
  obtain ⟨-, -, -, hl⟩ := evalScript_ok hss
  have hne : ss ≠ [] := by
    rintro rfl
    unfold evalScript at hss
    split at hss
    · cases hss
    · rw [evalLoop_atEnd (by simp [ExecState.init])] at hss
      simp [ExecState.init] at hss
      subst hss
      simp [] at hS
  have := hl hne
  simp only [ExecState.WithinStackLimit, hS, List.length_append, List.length_singleton] at this
  omega

/--
Take any checker, a supported flag set with `P2SH`, and a push-only `scriptSig` whose final stack is `S ++ [redeem]`.
The spend against the P2SH commitment to `redeem` is `redeem` on `S` with the true-top check.
That holds when `S` has at most 998 items. Otherwise the template gives `STACK_SIZE`.
-/
theorem verifyScript_p2shScriptPubKey {c : SignatureChecker} {ss redeem : List UInt8} {s : ExecState}
    {S : List (List UInt8)} (hf : unsupportedFlagBits flags = 0) (hp : hasFlag flags ScriptFlags.p2sh = true)
    (hpush : isPushOnly ss = true) (hss : evalScript (some c) flags ss [] = .ok s) (hS : s.stack = S ++ [redeem]) :
    verifyScript c flags ss (p2shScriptPubKey redeem) =
      if S.length + 2 ≤ maxStackItems then finishEval (evalScript (some c) flags redeem S)
      else .rejected .stackSize := by
  have hS1 := scriptSig_stack_bound hss hS
  by_cases h2 : S.length + 2 ≤ maxStackItems
  · simp only [h2, ↓reduceIte]
    exact verifyScript_p2sh_hash hf hp (hash160_toList_length _) hpush hss hS h2 rfl
  · simp only [h2, ↓reduceIte]
    have hov := evalScript_p2shTemplate_overflow (c := c) (x := redeem) hf (hash160_toList_length ⟨redeem.toArray⟩) hS1
      (by omega)
    rw [← hS] at hov
    have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
    simp only [verifyScript, h1, ite_false, hss, p2shScriptPubKey]
    rw [hov]

/-- On an empty stack, the redeem script gives `UNBALANCED_CONDITIONAL` at its `OP_IF`. -/
theorem evalScript_redeem_nil {c : SignatureChecker} {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33)
    (hn : keys.length ≤ 16) :
    evalScript (some c) flags (multisigRecoveryScript k keys R) [] = .rejected .unbalancedConditional := by
  have hlen := multisigRecoveryScript_length (k := k) hkeys hR
  have hsz : ¬maxScriptSize < (multisigRecoveryScript k keys R).length := by
    rw [hlen]; simp [maxScriptSize]; omega
  have hf' : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  unfold evalScript
  simp only [hf', hsz, ite_false]
  rw [evalLoop_op (op := 0x63) (by simp [ExecState.init, multisigRecoveryScript_eq]; rfl) (by decide)
    (Or.inl rfl) (by simp [countOp, ExecState.init, maxOpsPerScript]) (by decide)]
  simp only [ExecState.init, ExecState.fExec, List.contains_nil, Bool.not_false]
  rw [execOpcode_if_empty (Or.inl rfl) rfl]

end

section

/--
The hypotheses of the section 7 theorems for one legacy input that spends a P2SH output of the template.
Each field is one hypothesis that section 7 names. `S` is the stack that `scriptSig` leaves below the redeem script.
-/
structure MultisigRecoverySpend (ctx : InputContext) (prevScriptPubKey : Transaction.Script) (flags : UInt32)
    (verify : SignatureVerifier) (k : Nat) (keys : List (List UInt8)) (recovery : List UInt8)
    (S : List (List UInt8)) : Prop where
  /-- The flag set has only supported bits. -/
  supported : unsupportedFlagBits flags = 0
  /-- `SCRIPT_VERIFY_P2SH` is set. -/
  p2sh : hasFlag flags ScriptFlags.p2sh = true
  /-- `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY` is set. -/
  cltv : hasFlag flags ScriptFlags.checkLockTimeVerify = true
  /-- At least one signature is required. -/
  one_le_k : 1 ≤ k
  /-- At most as many signatures as keys. -/
  k_le_n : k ≤ keys.length
  /-- At most 16 keys, so that `OP_n` encodes the key count. -/
  n_le : keys.length ≤ 16
  /-- Every key has 33 bytes. -/
  keys_length : ∀ P ∈ keys, P.length = 33
  /-- The recovery key has 33 bytes. -/
  recovery_length : recovery.length = 33
  /-- The previous output is the P2SH commitment to these exact redeem-script bytes. -/
  commitment : prevScriptPubKey.bytes.val = p2shScriptPubKey (multisigRecoveryScript k keys recovery)
  /-- The input's `scriptSig` is push-only. -/
  pushOnly : isPushOnly ctx.input.scriptSig.bytes.val = true
  /-- The `scriptSig` evaluation succeeds, and its final stack is `S` with the exact redeem script on top. -/
  scriptSig : ∃ s, evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags
    ctx.input.scriptSig.bytes.val [] = .ok s ∧ s.stack = S ++ [multisigRecoveryScript k keys recovery]

variable {ctx : InputContext} {prevScriptPubKey : Transaction.Script} {flags : UInt32}
  {verify : SignatureVerifier} {k : Nat} {keys : List (List UInt8)} {R : List UInt8} {S : List (List UInt8)}

/-- Under `MultisigRecoverySpend`, `S` has at most 999 items. -/
theorem MultisigRecoverySpend.stack_bound (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) :
    S.length + 1 ≤ maxStackItems := by
  obtain ⟨s, hss, hS⟩ := h.scriptSig
  exact scriptSig_stack_bound hss hS

/-- Under `MultisigRecoverySpend`, the spend is the redeem script on `S` with the true-top check when `S` has at most 998 items, and `STACK_SIZE` otherwise. -/
theorem MultisigRecoverySpend.eq (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      if S.length + 2 ≤ maxStackItems then
        finishEval (evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags
          (multisigRecoveryScript k keys R) S)
      else .rejected .stackSize := by
  obtain ⟨s, hss, hS⟩ := h.scriptSig
  rw [verifyLegacySpend_eq, h.commitment]
  exact verifyScript_p2shScriptPubKey h.supported h.p2sh h.pushOnly hss hS

/-- A decided answer of `transactionChecker` is the value of `sigAccepted`. -/
theorem sigAccepted_of_checkSig {ctx : InputContext} {verify : SignatureVerifier} {code sig key : List UInt8}
    {v : Bool} (h : (transactionChecker ctx.tx ctx.index verify).checkSig sig key code = some v) :
    v = sigAccepted ctx verify code sig key := by
  cases v <;> simp [sigAccepted, h]

/-- Soundness for a true selector: if the spend accepts with `S = S1 ++ [sel]` and `castToBool sel`, the ordinary branch holds. -/
theorem multisigRecovery_sound_ordinary (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    {S1 : List (List UInt8)} {sel : List UInt8} (hSe : S = S1 ++ [sel]) (hsel : castToBool sel = true)
    (hS2 : S.length + 2 ≤ maxStackItems)
    (hacc : finishEval (evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags
      (multisigRecoveryScript k keys R) (S1 ++ [sel])) = .accepted) :
    OrdinaryBranch ctx verify flags k keys R S := by
  have hS1 : S1.length + 2 ≤ maxStackItems := by subst hSe; simp at hS2; omega
  have hn := h.n_le
  have hkn := h.k_le_n
  have hk16 : k ≤ 16 := by omega
  have htrue := evalScript_redeem_true (c := transactionChecker ctx.tx ctx.index verify) (flags := flags)
    h.supported h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length hsel hS1
  by_cases ho : maxStackItems < S1.length + keys.length + 2
  · rw [htrue] at hacc; simp [ho, finishEval] at hacc
  by_cases hshort : S1.length < k + 1
  · rw [htrue] at hacc; simp only [ho, ↓reduceIte] at hacc
    obtain ⟨dn, gn⟩ := decode_encode_small h.n_le
    obtain ⟨dk, gk⟩ := decode_encode_small hk16
    have hsc := (checkMultisigStep_sigCount (c := transactionChecker ctx.tx ctx.index verify)
      (script := multisigRecoveryScript k keys R) (flags := flags) (op := 0xae)
      (s := ⟨S1 ++ [ScriptNum.encode k] ++ keys ++ [ScriptNum.encode keys.length], [],
        2 + ((keys.map pushEncoding).flatten).length + 1, 0, [true], 2⟩)
      (keys := keys.reverse) (rest := S1.reverse) (by simp) dn (by simpa using gn)
      (by simp [maxPubKeysPerMultisig]; omega) (by simp [maxOpsPerScript]; omega)).2.2 k dk
      (by rw [gk, gn]; omega) (by rw [gk]; simp; omega)
    rw [hsc] at hacc; cases hacc
  obtain ⟨below, dummy, sigs, rfl, hlen⟩ : ∃ below dummy sigs, S1 = below ++ dummy :: sigs ∧ sigs.length = k := by
    refine ⟨S1.take (S1.length - (k + 1)), ?_⟩
    have hd : (S1.drop (S1.length - (k + 1))).length = k + 1 := by simp; omega
    match hm : S1.drop (S1.length - (k + 1)), hd with
    | dummy :: sigs, hd' =>
      exact ⟨dummy, sigs, by rw [← hm, List.take_append_drop], by simpa using hd'⟩
  have hbound : below.length + 1 + sigs.length + keys.length + 2 ≤ maxStackItems := by simp at ho; omega
  have hres := finishEval_redeem_ordinary (c := transactionChecker ctx.tx ctx.index verify) (flags := flags)
    (dummy := dummy) h.supported h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length hsel hlen hbound
  rw [show below ++ dummy :: sigs ++ [sel] = below ++ dummy :: sigs ++ [sel] from rfl] at hacc
  cases hloop : multisigLoop (multisigCheck (transactionChecker ctx.tx ctx.index verify) flags
      (ordinaryCode (multisigRecoveryScript k keys R) sigs) 0xae) sigs.reverse keys.reverse with
  | error r =>
    rcases hres.2 r hloop with ⟨e, -, he⟩ | ⟨u, -, hu⟩
    · rw [he] at hacc; cases hacc
    · rw [hu] at hacc; cases hacc
  | ok b =>
    rw [hres.1 b hloop] at hacc
    have hnd : (hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty) = false := by
      cases hx : (hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty) <;> simp_all
    rw [hnd] at hacc
    have hb : b = true := by cases b <;> simp_all
    subst hb
    obtain ⟨hvis, hg⟩ := multisigLoop_ok_visits
      (R := sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
      (fun a b v hv => sigAccepted_of_checkSig (multisigCheck_eq_ok_iff.mp hv).2.2) hloop
    refine ⟨below, dummy, sigs, sel, hSe, hlen, hsel, fun p hp => ?_, fun hn => ?_, ?_⟩
    · obtain ⟨v, hv⟩ := hvis p hp
      exact ⟨(multisigCheck_eq_ok_iff.mp hv).1, (multisigCheck_eq_ok_iff.mp hv).2.1⟩
    · cases dummy with
      | nil => rfl
      | cons _ _ => simp [hn] at hnd
    · exact orderedMatch_reverse.mp ((greedyMatch_iff _ _ _).mp hg)

/--
`OP_CHECKSIG` on `below ++ [sigR, R]`.
It checks the signature encoding, then the key encoding.
It then asks the checker about `sigR`, `R` and the script code without the push of `sigR`.
-/
theorem checkSigStep_recovery {c : SignatureChecker} {script : List UInt8} {s : ExecState}
    {below : List (List UInt8)} {sigR R : List UInt8} (hs : s.stack = below ++ [sigR, R]) :
    checkSigStep c script flags s 0xac =
      match checkSignatureEncoding sigR flags, checkPubKeyEncoding R flags with
      | .error e, _ => .rejected e
      | .ok (), .error e => .rejected e
      | .ok (), .ok () =>
        match c.checkSig sigR R (effectiveScriptCode script s.beginCodeHash [sigR]) with
        | none => .unsupported (.signatureOpcode 0xac)
        | some b => .next { s with stack := below ++ [boolBytes b] } := by
  cases hse : checkSignatureEncoding sigR flags with
  | error e => exact checkSigStep_sigEncoding hs hse
  | ok u =>
    cases u
    cases hke : checkPubKeyEncoding R flags with
    | error e => exact checkSigStep_keyEncoding hs hse hke
    | ok u =>
      cases u
      rw [checkSigStep_checked hs hse hke]
      cases c.checkSig sigR R (effectiveScriptCode script s.beginCodeHash [sigR]) <;> rfl

/-- Soundness for a false selector: if the spend accepts with `S = S1 ++ [sel]` and `castToBool sel = false`, the recovery branch holds. -/
theorem multisigRecovery_sound_recovery (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    {S1 : List (List UInt8)} {sel : List UInt8} (hSe : S = S1 ++ [sel]) (hsel : castToBool sel = false)
    (hS2 : S.length + 2 ≤ maxStackItems)
    (hacc : finishEval (evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags
      (multisigRecoveryScript k keys R) (S1 ++ [sel])) = .accepted) :
    RecoveryBranch ctx verify flags k keys R S := by
  have hS1 : S1.length + 2 ≤ maxStackItems := by subst hSe; simp at hS2; omega
  rw [finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
    h.recovery_length hsel hS1] at hacc
  by_cases hl : recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
      ctx.input.sequence ≠ sequenceFinal
  rotate_left
  · simp only [hl, ↓reduceIte] at hacc; cases hacc
  simp only [hl, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at hacc
  rcases List.eq_nil_or_concat S1 with rfl | ⟨below, sigR, rfl⟩
  · rw [checkSigStep_underflow (by simp)] at hacc; cases hacc
  rw [checkSigStep_recovery (below := below) (sigR := sigR) (R := R) (by simp)] at hacc
  cases hse : checkSignatureEncoding sigR flags with
  | error e => simp [hse] at hacc
  | ok u =>
    cases hke : checkPubKeyEncoding R flags with
    | error e => simp [hse, hke] at hacc
    | ok u' =>
      simp only [hse, hke] at hacc
      cases hcs : (transactionChecker ctx.tx ctx.index verify).checkSig sigR R
          (effectiveScriptCode (multisigRecoveryScript k keys R) 0 [sigR]) with
      | none => simp [hcs] at hacc
      | some b =>
        simp only [hcs, trueTop_boolBytes] at hacc
        have hb : b = true := by cases b <;> simp_all
        subst hb
        refine ⟨below, sigR, sel, by simp [hSe], hsel, hl.1, hl.2.1, hl.2.2,
          (checkSignatureEncoding_ok_iff _ _).mp hse, (checkPubKeyEncoding_ok_iff _ _).mp hke, ?_⟩
        simp [sigAccepted, recoveryCode, hcs]

/--
**Soundness.** Under `MultisigRecoverySpend`, if `verifyLegacySpend` accepts, the ordinary branch or the recovery branch holds for `S`.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.

No stack bound on `S` is assumed, and no totality of `verify`.
Acceptance implies that every stack check passed and that every reached checker call was decided.
`OrdinaryBranch` and `RecoveryBranch` state the encoding predicates, `NULLDUMMY`, ordered matching and the lock-time conditions explicitly.

The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, at most 591, below 10,000.
Every push in it has at most 33 payload bytes, executed or skipped.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
-/
theorem multisigRecovery_sound (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hacc : verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted) :
    OrdinaryBranch ctx verify flags k keys R S ∨ RecoveryBranch ctx verify flags k keys R S := by
  rw [h.eq] at hacc
  by_cases hS2 : S.length + 2 ≤ maxStackItems
  rotate_left
  · simp only [hS2, ↓reduceIte] at hacc; cases hacc
  simp only [hS2, ↓reduceIte] at hacc
  rcases List.eq_nil_or_concat S with rfl | ⟨S1, sel, hSe⟩
  · rw [evalScript_redeem_nil h.supported h.keys_length h.recovery_length h.n_le] at hacc; cases hacc
  rw [List.concat_eq_append] at hSe
  rw [hSe] at hacc
  cases hsel : castToBool sel
  · exact .inr (multisigRecovery_sound_recovery h hSe hsel hS2 hacc)
  · exact .inl (multisigRecovery_sound_ordinary h hSe hsel hS2 hacc)

/-- The effective script code is never longer than the script. -/
theorem effectiveScriptCode_length_le (script : List UInt8) (pc : Nat) (sigs : List (List UInt8)) :
    (effectiveScriptCode script pc sigs).length ≤ script.length := by
  unfold effectiveScriptCode
  suffices ∀ (code : List UInt8), code.length ≤ script.length →
      (sigs.foldl (fun code sig => (Transaction.findAndDelete code (pushEncoding sig)).1) code).length ≤
        script.length from this _ (by simp)
  induction sigs with
  | nil => intro code h; exact h
  | cons sig sigs ih =>
    intro code h
    exact ih _ (Nat.le_trans (Transaction.findAndDelete_length_le _ _) h)

/-- For a verifier that decides every request, `transactionChecker` decides every request with a script code shorter than 2^64 bytes. -/
theorem transactionChecker_checkSig_ne_none {tx : Transaction} {nIn : UInt32} {verify : SignatureVerifier}
    (hverify : ∀ s k d, verify s k d ≠ none) {sig key code : List UInt8} (hc : code.length < 2 ^ 64) :
    (transactionChecker tx nIn verify).checkSig sig key code ≠ none := by
  cases hk : isValidPubKey key
  · simp [transactionChecker_invalidKey _ _ _ _ _ hk]
  · rcases List.eq_nil_or_concat sig with rfl | ⟨s, b, rfl⟩
    · simp [transactionChecker_emptySig _ _ _ _ hk]
    · rw [List.concat_eq_append, transactionChecker_verify _ _ _ _ _ hk hc]
      exact hverify _ _ _

/--
**Converse, ordinary branch.** Under `MultisigRecoverySpend`, with `S.length + n + 1 ≤ 1000`, the spend accepts when these hold:

- `S` is `below ++ dummy :: sigs ++ [sel]`, with `k` signatures in push order and a true selector
- every pair that Core visits, top first, passes `SigEncodingOk` and `KeyEncodingOk`
- under `NULLDUMMY`, the dummy is empty
- the signatures pair in order with a subsequence of the keys under `sigAccepted`
- the checker decides every visited pair

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.

The stack bound covers the pushes of `k`, the keys and `n`.
Totality is assumed only on the visited pairs.
`multisigRecovery_ordinary_unsupported` gives the result when a visited pair is undecided.

The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, at most 591, below 10,000.
Every push in it has at most 33 payload bytes, executed or skipped.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
-/
theorem multisigRecovery_ordinary_complete (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + keys.length + 1 ≤ maxStackItems)
    {below sigs : List (List UInt8)} {dummy sel : List UInt8} (hSe : S = below ++ dummy :: sigs ++ [sel])
    (hlen : sigs.length = k) (hsel : castToBool sel = true)
    (henc : ∀ p ∈ multisigVisits (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
        sigs.reverse keys.reverse, SigEncodingOk flags p.1 ∧ KeyEncodingOk flags p.2)
    (hnull : hasFlag flags ScriptFlags.nullDummy = true → dummy = [])
    (hmatch : OrderedMatch (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs)) sigs keys)
    (htotal : ∀ p ∈ multisigVisits (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
        sigs.reverse keys.reverse,
      (transactionChecker ctx.tx ctx.index verify).checkSig p.1 p.2 (ordinaryCode (multisigRecoveryScript k keys R) sigs)
        ≠ none) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted := by
  have hk1 := h.one_le_k
  have hkn := h.k_le_n
  have hS2 : S.length + 2 ≤ maxStackItems := by omega
  rw [h.eq]
  simp only [hS2, ↓reduceIte]
  have hbound : below.length + 1 + sigs.length + keys.length + 2 ≤ maxStackItems := by
    subst hSe; simp at hS; omega
  have hres := finishEval_redeem_ordinary (c := transactionChecker ctx.tx ctx.index verify) (flags := flags)
    (dummy := dummy) h.supported h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length hsel hlen hbound
  have hloop := multisigLoop_visits_ok (check := multisigCheck (transactionChecker ctx.tx ctx.index verify) flags
      (ordinaryCode (multisigRecoveryScript k keys R) sigs) 0xae)
    (R := sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
    (sigs := sigs.reverse) (keys := keys.reverse) fun p hp => by
      obtain ⟨he1, he2⟩ := henc p hp
      cases hv : (transactionChecker ctx.tx ctx.index verify).checkSig p.1 p.2
          (ordinaryCode (multisigRecoveryScript k keys R) sigs) with
      | none => exact absurd hv (htotal p hp)
      | some v => exact multisigCheck_eq_ok_iff.mpr ⟨he1, he2, by rw [hv, ← sigAccepted_of_checkSig hv]⟩
  have hg : greedyMatch (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
      sigs.reverse keys.reverse = true := (greedyMatch_iff _ _ _).mpr (orderedMatch_reverse.mpr hmatch)
  rw [hg] at hloop
  rw [hSe, hres.1 true hloop]
  have hnd : (hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty) = false := by
    cases hf : hasFlag flags ScriptFlags.nullDummy
    · rfl
    · simp [hnull hf]
  simp [hnd]

/--
**Converse, recovery branch.** Under `MultisigRecoverySpend`, with `S.length + 2 ≤ 1000`, the spend accepts when the recovery branch holds:

- `S` is `below ++ [sigR, sel]`, with a false selector
- the lock time is at least 1,000,000 and below 500,000,000
- the input's sequence is not `0xffffffff`
- `sigR` and `R` pass the encoding predicates
- `sigAccepted` holds for `sigR` against `R`

`sigAccepted` is an answer `some true`, so no totality hypothesis is needed.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.

The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, at most 591, below 10,000.
Every push in it has at most 33 payload bytes, executed or skipped.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
-/
theorem multisigRecovery_recovery_complete (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + 2 ≤ maxStackItems) (hb : RecoveryBranch ctx verify flags k keys R S) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted := by
  obtain ⟨below, sigR, sel, hSe, hsel, hl1, hl2, hl3, hse, hke, hacc⟩ := hb
  rw [h.eq]
  simp only [hS, ↓reduceIte]
  have hS1 : (below ++ [sigR]).length + 2 ≤ maxStackItems := by subst hSe; simp at hS ⊢; omega
  rw [hSe, show below ++ [sigR, sel] = (below ++ [sigR]) ++ [sel] by simp,
    finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
      h.recovery_length hsel hS1]
  simp only [hl1, hl2, hl3, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  rw [checkSigStep_recovery (below := below) (sigR := sigR) (R := R) (by simp),
    (checkSignatureEncoding_ok_iff _ _).mpr hse, (checkPubKeyEncoding_ok_iff _ _).mpr hke]
  have hcs : (transactionChecker ctx.tx ctx.index verify).checkSig sigR R
      (effectiveScriptCode (multisigRecoveryScript k keys R) 0 [sigR]) = some true := by
    simpa [sigAccepted, recoveryCode] using hacc
  simp only [hcs, trueTop_boolBytes, ↓reduceIte]

/--
**The equivalence of section 7.** Under `MultisigRecoverySpend`, the spend accepts exactly when the ordinary branch or the recovery branch holds for `S`.
It assumes `S.length + n + 1 ≤ 1000` and a verifier that decides every request.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.

The totality of `verify` is assumed here only to state both directions at once.
`multisigRecovery_sound` needs no totality.
The converses need it only on the reached calls.

The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, at most 591, below 10,000.
Every push in it has at most 33 payload bytes, executed or skipped.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
-/
theorem multisigRecovery_accepted_iff (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + keys.length + 1 ≤ maxStackItems) (hverify : ∀ s key d, verify s key d ≠ none) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted ↔
      OrdinaryBranch ctx verify flags k keys R S ∨ RecoveryBranch ctx verify flags k keys R S := by
  refine ⟨multisigRecovery_sound h, ?_⟩
  rintro (⟨below, dummy, sigs, sel, hSe, hlen, hsel, henc, hnull, hmatch⟩ | hr)
  · refine multisigRecovery_ordinary_complete h hS hSe hlen hsel henc hnull hmatch fun p _ =>
      transactionChecker_checkSig_ne_none hverify ?_
    have := effectiveScriptCode_length_le (multisigRecoveryScript k keys R) 0 sigs.reverse
    have hl := multisigRecoveryScript_length (k := k) h.keys_length h.recovery_length
    have := h.n_le
    simp only [ordinaryCode]; omega
  · have := h.one_le_k; have := h.k_le_n
    exact multisigRecovery_recovery_complete h (by omega) hr

/--
**The `none` case, ordinary branch.** Under `MultisigRecoverySpend`, the spend is `unsupported (.signatureOpcode 0xae)` when these hold:

- `S.length + n + 1 ≤ 1000`
- `S` has the ordinary shape with `k` signatures and a true selector
- every visit before the pair `p` passes both encoding predicates and is decided
- `p` passes both encoding predicates, and the checker answers `none` on `p`

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem multisigRecovery_ordinary_unsupported
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + keys.length + 1 ≤ maxStackItems)
    {below sigs : List (List UInt8)} {dummy sel : List UInt8} (hSe : S = below ++ dummy :: sigs ++ [sel])
    (hlen : sigs.length = k) (hsel : castToBool sel = true)
    {pre post : List (List UInt8 × List UInt8)} {p : List UInt8 × List UInt8}
    (hvis : multisigVisits (sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs))
        sigs.reverse keys.reverse = pre ++ p :: post)
    (hpre : ∀ q ∈ pre, SigEncodingOk flags q.1 ∧ KeyEncodingOk flags q.2 ∧
      (transactionChecker ctx.tx ctx.index verify).checkSig q.1 q.2 (ordinaryCode (multisigRecoveryScript k keys R) sigs)
        ≠ none)
    (hp : SigEncodingOk flags p.1 ∧ KeyEncodingOk flags p.2)
    (hnone : (transactionChecker ctx.tx ctx.index verify).checkSig p.1 p.2
      (ordinaryCode (multisigRecoveryScript k keys R) sigs) = none) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .unsupported (.signatureOpcode 0xae) := by
  have hk1 := h.one_le_k
  have hkn := h.k_le_n
  have hS2 : S.length + 2 ≤ maxStackItems := by omega
  rw [h.eq]
  simp only [hS2, ↓reduceIte]
  have hbound : below.length + 1 + sigs.length + keys.length + 2 ≤ maxStackItems := by
    subst hSe; simp at hS; omega
  have hres := finishEval_redeem_ordinary (c := transactionChecker ctx.tx ctx.index verify) (flags := flags)
    (dummy := dummy) h.supported h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length hsel hlen hbound
  have hpe : multisigCheck (transactionChecker ctx.tx ctx.index verify) flags
      (ordinaryCode (multisigRecoveryScript k keys R) sigs) 0xae p.1 p.2 = .error (.unsupported (.signatureOpcode 0xae)) := by
    simp [multisigCheck, (checkSignatureEncoding_ok_iff _ _).mpr hp.1, (checkPubKeyEncoding_ok_iff _ _).mpr hp.2,
      hnone]
  have hloop := multisigLoop_visits_error hvis (fun q hq => by
      obtain ⟨he1, he2, ht⟩ := hpre q hq
      cases hv : (transactionChecker ctx.tx ctx.index verify).checkSig q.1 q.2
          (ordinaryCode (multisigRecoveryScript k keys R) sigs) with
      | none => exact absurd hv ht
      | some v => exact multisigCheck_eq_ok_iff.mpr ⟨he1, he2, by rw [hv, ← sigAccepted_of_checkSig hv]⟩) hpe
  rw [hSe]
  rcases hres.2 _ hloop with ⟨e, he, -⟩ | ⟨u, hu, hr⟩
  · cases he
  · cases hu; exact hr

/--
**The `none` case, recovery branch.** Under `MultisigRecoverySpend`, the spend is `unsupported (.signatureOpcode 0xac)` when these hold:

- `S.length + 2 ≤ 1000`
- `S` is `below ++ [sigR, sel]`, with a false selector
- the lock-time conditions and both encoding predicates hold
- the checker answers `none` on `sigR`, `R` and the recovery script code

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem multisigRecovery_recovery_unsupported
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + 2 ≤ maxStackItems) {below : List (List UInt8)} {sigR sel : List UInt8}
    (hSe : S = below ++ [sigR, sel]) (hsel : castToBool sel = false)
    (hl1 : recoveryLockTime ≤ ctx.tx.lockTime.toNat) (hl2 : ctx.tx.lockTime.toNat < lockTimeThreshold)
    (hl3 : ctx.input.sequence ≠ sequenceFinal) (hse : SigEncodingOk flags sigR) (hke : KeyEncodingOk flags R)
    (hnone : (transactionChecker ctx.tx ctx.index verify).checkSig sigR R
      (recoveryCode (multisigRecoveryScript k keys R) sigR) = none) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .unsupported (.signatureOpcode 0xac) := by
  rw [h.eq]
  simp only [hS, ↓reduceIte]
  have hS1 : (below ++ [sigR]).length + 2 ≤ maxStackItems := by subst hSe; simp at hS ⊢; omega
  rw [hSe, show below ++ [sigR, sel] = (below ++ [sigR]) ++ [sel] by simp,
    finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
      h.recovery_length hsel hS1]
  simp only [hl1, hl2, hl3, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  rw [checkSigStep_recovery (below := below) (sigR := sigR) (R := R) (by simp),
    (checkSignatureEncoding_ok_iff _ _).mpr hse, (checkPubKeyEncoding_ok_iff _ _).mpr hke]
  simp only [recoveryCode] at hnone
  simp only [hnone]

/--
**Corollary of section 7.** Under `MultisigRecoverySpend`, which includes the `CHECKLOCKTIMEVERIFY` flag, assume `S.length + 2 ≤ 1000` and a false selector.
Then a transaction with lock time below 1,000,000 gives `UNSATISFIED_LOCKTIME`, before any signature check.
So it cannot pass the recovery branch.

Without the `CHECKLOCKTIMEVERIFY` flag, this exclusion does not hold: `OP_CHECKLOCKTIMEVERIFY` is then `OP_NOP2`.
The known answer `CLTV clear, lock time 0` in `tests/KnownAnswers/Script.lean` accepts such a spend.
A claim that recovery cannot enter a chain before a height or time also needs transaction-finality and chain-context results.
They are outside this module.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem multisigRecovery_lockTime_lt (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + 2 ≤ maxStackItems) {S1 : List (List UInt8)} {sel : List UInt8} (hSe : S = S1 ++ [sel])
    (hsel : castToBool sel = false) (hlt : ctx.tx.lockTime.toNat < recoveryLockTime) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .rejected .unsatisfiedLocktime := by
  rw [h.eq]
  simp only [hS, ↓reduceIte]
  have hS1 : S1.length + 2 ≤ maxStackItems := by subst hSe; simp at hS; omega
  rw [hSe, finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
      h.recovery_length hsel hS1]
  have hl : ¬(recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
      ctx.input.sequence ≠ sequenceFinal) := fun h' => by omega
  simp only [hl, ↓reduceIte]

/--
**Corollary of section 7, time-based lock time.** Under `MultisigRecoverySpend`, which includes the `CHECKLOCKTIMEVERIFY` flag, assume `S.length + 2 ≤ 1000` and a false selector.
Then a transaction with lock time at least 500,000,000 (`LOCKTIME_THRESHOLD`) gives `UNSATISFIED_LOCKTIME`, before any signature check.
Such a lock time is a time, and the operand 1,000,000 is a height, so the two types differ.

Without the `CHECKLOCKTIMEVERIFY` flag, this exclusion does not hold: `OP_CHECKLOCKTIMEVERIFY` is then `OP_NOP2`.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem multisigRecovery_lockTime_ge_threshold
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + 2 ≤ maxStackItems) {S1 : List (List UInt8)} {sel : List UInt8} (hSe : S = S1 ++ [sel])
    (hsel : castToBool sel = false) (hge : lockTimeThreshold ≤ ctx.tx.lockTime.toNat) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .rejected .unsatisfiedLocktime := by
  rw [h.eq]
  simp only [hS, ↓reduceIte]
  have hS1 : S1.length + 2 ≤ maxStackItems := by subst hSe; simp at hS; omega
  rw [hSe, finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
      h.recovery_length hsel hS1]
  have hl : ¬(recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
      ctx.input.sequence ≠ sequenceFinal) := fun h' => by omega
  simp only [hl, ↓reduceIte]

/--
**Corollary of section 7, final sequence.** Under `MultisigRecoverySpend`, which includes the `CHECKLOCKTIMEVERIFY` flag, assume `S.length + 2 ≤ 1000` and a false selector.
Then an input whose sequence is `0xffffffff` (`SEQUENCE_FINAL`) gives `UNSATISFIED_LOCKTIME`, before any signature check, at every lock time.

Without the `CHECKLOCKTIMEVERIFY` flag, this exclusion does not hold: `OP_CHECKLOCKTIMEVERIFY` is then `OP_NOP2`.

The hypotheses are the fields of `MultisigRecoverySpend`:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, with `n` keys of 33 bytes and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem multisigRecovery_finalSequence
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hS : S.length + 2 ≤ maxStackItems) {S1 : List (List UInt8)} {sel : List UInt8} (hSe : S = S1 ++ [sel])
    (hsel : castToBool sel = false) (hseq : ctx.input.sequence = sequenceFinal) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .rejected .unsatisfiedLocktime := by
  rw [h.eq]
  simp only [hS, ↓reduceIte]
  have hS1 : S1.length + 2 ≤ maxStackItems := by subst hSe; simp at hS; omega
  rw [hSe, finishEval_redeem_recovery ctx verify h.supported h.cltv h.one_le_k h.k_le_n h.n_le h.keys_length
      h.recovery_length hsel hS1]
  have hl : ¬(recoveryLockTime ≤ ctx.tx.lockTime.toNat ∧ ctx.tx.lockTime.toNat < lockTimeThreshold ∧
      ctx.input.sequence ≠ sequenceFinal) := fun h' => h'.2.2 hseq
  simp only [hl, ↓reduceIte]

/--
Under `MultisigRecoverySpend`, which includes the `CHECKLOCKTIMEVERIFY` flag: an accepted spend with lock time below 1,000,000 takes the ordinary branch.
No stack bound or totality hypothesis is needed.
-/
theorem multisigRecovery_accepted_lockTime_lt
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S)
    (hlt : ctx.tx.lockTime.toNat < recoveryLockTime)
    (hacc : verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted) :
    OrdinaryBranch ctx verify flags k keys R S := by
  rcases multisigRecovery_sound h hacc with ho | ⟨_, _, _, _, _, hl, _⟩
  · exact ho
  · omega

/-- For every supported flag set: if the `scriptSig` evaluation rejects with `e`, the spend rejects with `e`. -/
theorem verifyLegacySpend_scriptSig_rejected {e : ScriptError} (hf : unsupportedFlagBits flags = 0)
    (hss : evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags ctx.input.scriptSig.bytes.val [] =
      .rejected e) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .rejected e := by
  have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  simp only [verifyLegacySpend, verifyScript, h1, ite_false, hss]

/-- For every supported flag set: if the `scriptSig` evaluation is unsupported with `u`, the spend is unsupported with `u`. -/
theorem verifyLegacySpend_scriptSig_unsupported {u : Unsupported} (hf : unsupportedFlagBits flags = 0)
    (hss : evalScript (some (transactionChecker ctx.tx ctx.index verify)) flags ctx.input.scriptSig.bytes.val [] =
      .unsupported u) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .unsupported u := by
  have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  simp only [verifyLegacySpend, verifyScript, h1, ite_false, hss]

/-! ## The reference digest -/

/-- For every opcode above `OP_PUSHDATA4` and every fully parsed tail, the opcode followed by the tail parses completely. -/
theorem scanOps_cons_opcode {op : UInt8} (h : 0x4e < op) {t : List UInt8} (ht : (scanOps t).2 = []) :
    (scanOps (op :: t)).2 = [] := by
  rw [show op :: t = [op] ++ t from rfl, scanOps_append_snd (scanOps_opcode h)]
  exact ht

/-- For 33-byte keys and every fully parsed tail, the key pushes followed by the tail parse completely. -/
theorem keys_scanOps {keys : List (List UInt8)} (hkeys : ∀ P ∈ keys, P.length = 33) {t : List UInt8}
    (ht : (scanOps t).2 = []) : (scanOps ((keys.map pushEncoding).flatten ++ t)).2 = [] := by
  induction keys with
  | nil => simpa using ht
  | cons P ks ih =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    rw [scanOps_append_snd (scanOps_pushEncoding P (by rw [hkeys P (by simp)]; decide))]
    exact ih (fun Q hQ => hkeys Q (by simp [hQ]))

/-- For `1 ≤ n ≤ 16` and a 33-byte recovery key, the bytes after the key pushes parse completely. -/
theorem redeemTail_scanOps {n : Nat} {recovery : List UInt8} (h1 : 1 ≤ n) (hn : n ≤ 16) (hR : recovery.length = 33) :
    (scanOps (redeemTail n recovery)).2 = [] := by
  have hop := (smallIntOpcode_facts n (by omega) h1).1
  have e : redeemTail n recovery = smallIntOpcode n :: 0xae :: 0x67 ::
      ([0x03, 0x40, 0x42, 0x0f] ++ (0xb1 :: 0x75 :: (pushEncoding recovery ++ [0xac, 0x68]))) := by
    simp [redeemTail]
  have hpush : readOp [0x03, 0x40, 0x42, 0x0f] = .op 0x03 [0x03, 0x40, 0x42, 0x0f] [] := rfl
  rw [e]
  refine scanOps_cons_opcode hop (scanOps_cons_opcode (by decide) (scanOps_cons_opcode (by decide) ?_))
  rw [scanOps_append_snd (scanOps_bytes hpush)]
  refine scanOps_cons_opcode (by decide) (scanOps_cons_opcode (by decide) ?_)
  rw [scanOps_append_snd (scanOps_pushEncoding recovery (by rw [hR]; decide))]
  exact scanOps_cons_opcode (by decide) (scanOps_cons_opcode (by decide) (by rw [scanOps_nil]))

/-- For `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes and a 33-byte recovery key, every instruction of the template parses. -/
theorem multisigRecoveryScript_scanOps {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33)
    (hR : R.length = 33) : (scanOps (multisigRecoveryScript k keys R)).2 = [] := by
  rw [multisigRecoveryScript_eq]
  exact scanOps_cons_opcode (by decide) (scanOps_cons_opcode (smallIntOpcode_facts k (by omega) hk1).1
    (keys_scanOps hkeys (redeemTail_scanOps (by omega) hn hR)))

/-- For `n ≤ 16` keys of 33 bytes and a 33-byte recovery key, the template has at most 2^32 bytes. -/
theorem multisigRecoveryScript_length_le {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33) :
    (multisigRecoveryScript k keys R).length ≤ 2 ^ 32 := by
  rw [multisigRecoveryScript_length hkeys hR]
  omega

/--
For `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes, a 33-byte recovery key and every signature list `sigs`:
every instruction of the script code of the ordinary branch parses.
-/
theorem ordinaryCode_scanOps {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33)
    (hR : R.length = 33) (sigs : List (List UInt8)) :
    (scanOps (ordinaryCode (multisigRecoveryScript k keys R) sigs)).2 = [] :=
  effectiveScriptCode_scanOps _ 0 _ (by simpa using multisigRecoveryScript_scanOps hk1 hkn hn hkeys hR)
    (multisigRecoveryScript_length_le hn hkeys hR)

/--
For `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes, a 33-byte recovery key and every signature `sigR`:
every instruction of the script code of the recovery branch parses.
-/
theorem recoveryCode_scanOps {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hk1 : 1 ≤ k) (hkn : k ≤ keys.length) (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33)
    (hR : R.length = 33) (sigR : List UInt8) :
    (scanOps (recoveryCode (multisigRecoveryScript k keys R) sigR)).2 = [] :=
  effectiveScriptCode_scanOps _ 0 _ (by simpa using multisigRecoveryScript_scanOps hk1 hkn hn hkeys hR)
    (multisigRecoveryScript_length_le hn hkeys hR)

/-- For `n ≤ 16` keys of 33 bytes and a 33-byte recovery key, the script code of the ordinary branch is shorter than 2^64 bytes. -/
theorem ordinaryCode_length_lt {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33) (sigs : List (List UInt8)) :
    (ordinaryCode (multisigRecoveryScript k keys R) sigs).length < 2 ^ 64 := by
  have := effectiveScriptCode_length_le (multisigRecoveryScript k keys R) 0 sigs.reverse
  have := multisigRecoveryScript_length_le (k := k) hn hkeys hR
  simp only [ordinaryCode]
  omega

/-- For `n ≤ 16` keys of 33 bytes and a 33-byte recovery key, the script code of the recovery branch is shorter than 2^64 bytes. -/
theorem recoveryCode_length_lt {k : Nat} {keys : List (List UInt8)} {R : List UInt8}
    (hn : keys.length ≤ 16) (hkeys : ∀ P ∈ keys, P.length = 33) (hR : R.length = 33) (sigR : List UInt8) :
    (recoveryCode (multisigRecoveryScript k keys R) sigR).length < 2 ^ 64 := by
  have := effectiveScriptCode_length_le (multisigRecoveryScript k keys R) 0 [sigR]
  have := multisigRecoveryScript_length_le (k := k) hn hkeys hR
  simp only [recoveryCode]
  omega

/--
The checker's answer on `s ++ [hashType]` is `verify` on `s`, the key and the digest of `legacyReferencePlan`, Core's `SignatureHashOld` transformation.
It holds for every input context, verifier, signature bytes `s` and hash-type byte, under two hypotheses:

- the key passes `isValidPubKey`
- the script code is shorter than 2^64 bytes, and all its instructions parse

The input context gives the bounds on the numbers of inputs and outputs.
-/
theorem transactionChecker_verify_reference (ctx : InputContext) (verify : SignatureVerifier)
    (s : List UInt8) (hashType : UInt8) {key code : List UInt8} (hk : isValidPubKey key = true)
    (hc : code.length < 2 ^ 64) (hParse : (scanOps code).2 = []) :
    (transactionChecker ctx.tx ctx.index verify).checkSig (s ++ [hashType]) key code =
      verify s key (legacyReferencePlan ⟨⟨code, hc⟩⟩ ctx.tx ctx.index hashType.toUInt32).digest := by
  rw [transactionChecker_verify _ _ _ _ _ hk hc,
    legacySignatureHash_eq_reference _ _ _ _ hParse ctx.inputs_lt ctx.outputs_lt]

/--
Take any input context and verifier, and a script code shorter than 2^64 bytes whose instructions all parse.
Then `sigAccepted` holds for `sig` and `key` exactly when these hold:

- the key passes `isValidPubKey`
- `sig` is `s ++ [hashType]`
- `verify` returns `some true` on `s`, the key, and the digest of `legacyReferencePlan` with `hashType` as the hash type
-/
theorem sigAccepted_iff_reference (ctx : InputContext) (verify : SignatureVerifier) {code : List UInt8}
    (hc : code.length < 2 ^ 64) (hParse : (scanOps code).2 = []) (sig key : List UInt8) :
    sigAccepted ctx verify code sig key = true ↔
      isValidPubKey key = true ∧ ∃ s hashType, sig = s ++ [hashType] ∧
        verify s key (legacyReferencePlan ⟨⟨code, hc⟩⟩ ctx.tx ctx.index hashType.toUInt32).digest = some true := by
  have e : ∀ h, legacySignatureHash ⟨⟨code, hc⟩⟩ ctx.tx ctx.index h =
      (legacyReferencePlan ⟨⟨code, hc⟩⟩ ctx.tx ctx.index h).digest := fun h =>
    legacySignatureHash_eq_reference _ _ _ h hParse ctx.inputs_lt ctx.outputs_lt
  rw [sigAccepted_iff ctx verify hc]
  simp only [e]

/--
**The reference digest, ordinary branch.** Under `MultisigRecoverySpend`, for every signature list `sigs`:
`sigAccepted` with the script code of the ordinary branch holds for `sig` and `key` exactly when these hold:

- the key passes `isValidPubKey`
- `sig` is `s ++ [hashType]`
- `verify` returns `some true` on `s`, the key, and the digest of `legacyReferencePlan` for the script code, the input and `hashType`

`legacyReferencePlan` is Core's `SignatureHashOld` transformation.
So every checker call of the ordinary branch, in `OrdinaryBranch` and `multisigVisits`, hashes the reference digest.

The hypotheses used are the template sizes of `MultisigRecoverySpend`: `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes and a 33-byte recovery key `R`.
They give the parsed-script hypothesis of `legacySignatureHash_eq_reference` for every signature list.
The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem MultisigRecoverySpend.sigAccepted_ordinary_iff_reference
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigs : List (List UInt8))
    (sig key : List UInt8) :
    sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs) sig key = true ↔
      isValidPubKey key = true ∧ ∃ s hashType, sig = s ++ [hashType] ∧
        verify s key (legacyReferencePlan
          ⟨⟨ordinaryCode (multisigRecoveryScript k keys R) sigs,
            ordinaryCode_length_lt h.n_le h.keys_length h.recovery_length sigs⟩⟩
          ctx.tx ctx.index hashType.toUInt32).digest = some true :=
  sigAccepted_iff_reference ctx verify _
    (ordinaryCode_scanOps h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length sigs) sig key

/--
**The reference digest, recovery branch.** Under `MultisigRecoverySpend`, for every signature `sigR`:
`sigAccepted` with the script code of the recovery branch holds for `sig` and `key` exactly when these hold:

- the key passes `isValidPubKey`
- `sig` is `s ++ [hashType]`
- `verify` returns `some true` on `s`, the key, and the digest of `legacyReferencePlan` for the script code, the input and `hashType`

`legacyReferencePlan` is Core's `SignatureHashOld` transformation.
So the checker call of `RecoveryBranch` hashes the reference digest.

The hypotheses used are the template sizes of `MultisigRecoverySpend`: `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes and a 33-byte recovery key `R`.
The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem MultisigRecoverySpend.sigAccepted_recovery_iff_reference
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigR sig key : List UInt8) :
    sigAccepted ctx verify (recoveryCode (multisigRecoveryScript k keys R) sigR) sig key = true ↔
      isValidPubKey key = true ∧ ∃ s hashType, sig = s ++ [hashType] ∧
        verify s key (legacyReferencePlan
          ⟨⟨recoveryCode (multisigRecoveryScript k keys R) sigR,
            recoveryCode_length_lt h.n_le h.keys_length h.recovery_length sigR⟩⟩
          ctx.tx ctx.index hashType.toUInt32).digest = some true :=
  sigAccepted_iff_reference ctx verify _
    (recoveryCode_scanOps h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length sigR) sig key

/--
**The checker call, ordinary branch.** Under `MultisigRecoverySpend`, take any signature list `sigs`, signature bytes `s` and hash-type byte, and a key that passes `isValidPubKey`.
With the script code of the ordinary branch, the checker's answer on `s ++ [hashType]` is `verify` on `s`, the key and the digest of `legacyReferencePlan`.

The hypotheses used are the template sizes of `MultisigRecoverySpend`: `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes and a 33-byte recovery key `R`.
The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem MultisigRecoverySpend.checkSig_ordinary_reference
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigs : List (List UInt8))
    (s : List UInt8) (hashType : UInt8) {key : List UInt8} (hk : isValidPubKey key = true) :
    (transactionChecker ctx.tx ctx.index verify).checkSig (s ++ [hashType]) key
        (ordinaryCode (multisigRecoveryScript k keys R) sigs) =
      verify s key (legacyReferencePlan
        ⟨⟨ordinaryCode (multisigRecoveryScript k keys R) sigs,
          ordinaryCode_length_lt h.n_le h.keys_length h.recovery_length sigs⟩⟩
        ctx.tx ctx.index hashType.toUInt32).digest :=
  transactionChecker_verify_reference ctx verify s hashType hk _
    (ordinaryCode_scanOps h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length sigs)

/--
**The checker call, recovery branch.** Under `MultisigRecoverySpend`, take any signature `sigR`, signature bytes `s` and hash-type byte, and a key that passes `isValidPubKey`.
With the script code of the recovery branch, the checker's answer on `s ++ [hashType]` is `verify` on `s`, the key and the digest of `legacyReferencePlan`.

The hypotheses used are the template sizes of `MultisigRecoverySpend`: `1 ≤ k ≤ n ≤ 16`, `n` keys of 33 bytes and a 33-byte recovery key `R`.
The input context gives an input index that selects an input, and fewer than 2^32 inputs and outputs.
-/
theorem MultisigRecoverySpend.checkSig_recovery_reference
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigR s : List UInt8)
    (hashType : UInt8) {key : List UInt8} (hk : isValidPubKey key = true) :
    (transactionChecker ctx.tx ctx.index verify).checkSig (s ++ [hashType]) key
        (recoveryCode (multisigRecoveryScript k keys R) sigR) =
      verify s key (legacyReferencePlan
        ⟨⟨recoveryCode (multisigRecoveryScript k keys R) sigR,
          recoveryCode_length_lt h.n_le h.keys_length h.recovery_length sigR⟩⟩
        ctx.tx ctx.index hashType.toUInt32).digest :=
  transactionChecker_verify_reference ctx verify s hashType hk _
    (recoveryCode_scanOps h.one_le_k h.k_le_n h.n_le h.keys_length h.recovery_length sigR)

/-! ## The 2-of-3 instance of section 7 -/

/-- For 33-byte keys `P1`, `P2`, `P3` and `R`, the 2-of-3 template has the bytes of section 7, 149 in all. -/
theorem multisigRecoveryScript_twoOfThree {P1 P2 P3 R : List UInt8} (h1 : P1.length = 33) (h2 : P2.length = 33)
    (h3 : P3.length = 33) (hR : R.length = 33) :
    multisigRecoveryScript 2 [P1, P2, P3] R =
      [0x63, 0x52, 0x21] ++ P1 ++ [0x21] ++ P2 ++ [0x21] ++ P3 ++
        [0x53, 0xae, 0x67, 0x03, 0x40, 0x42, 0x0f, 0xb1, 0x75, 0x21] ++ R ++ [0xac, 0x68] ∧
      (multisigRecoveryScript 2 [P1, P2, P3] R).length = 149 := by
  have e : ∀ {P : List UInt8}, P.length = 33 → pushEncoding P = 0x21 :: P := fun hP => by
    rw [pushEncoding_small (by omega), hP]; rfl
  refine ⟨?_, ?_⟩
  · simp [multisigRecoveryScript, e h1, e h2, e h3, e hR, smallIntOpcode, recoveryLockTimePush]
  · rw [multisigRecoveryScript_length (by simp; omega) hR]; rfl

/--
**The 2-of-3 equivalence.** `multisigRecovery_accepted_iff` for `k = 2` and the keys `[P1, P2, P3]`.
It assumes `MultisigRecoverySpend`, at most 996 items in `S` and a verifier that decides every request.
Then the spend accepts exactly when the ordinary branch or the recovery branch holds.
In the ordinary branch, `S` ends with `[dummy, sig1, sig2, sel]`.
Core visits the signatures `[sig2, sig1]` against the keys `[P3, P2, P1]`.
-/
theorem multisigRecovery_twoOfThree_accepted_iff {P1 P2 P3 : List UInt8}
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify 2 [P1, P2, P3] R S)
    (hS : S.length ≤ 996) (hverify : ∀ s key d, verify s key d ≠ none) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = .accepted ↔
      OrdinaryBranch ctx verify flags 2 [P1, P2, P3] R S ∨ RecoveryBranch ctx verify flags 2 [P1, P2, P3] R S :=
  multisigRecovery_accepted_iff h (by simp [maxStackItems]; omega) hverify


/-! ## Accepted ALL-only signatures under equal committed fields -/

/--
**Commitment, ordinary branch.** Under `MultisigRecoverySpend`, take any signature list `sigs`, and a signature `s ++ [hashType]` that `sigAccepted` accepts for `key` with the script code of the ordinary branch.
Let the hash type be `IsAllOnly`: ALL, without ANYONECANPAY.
Take any transaction `tx'` with the same `legacyAllFields` as `ctx.tx`.
Then `verify` returns `some true` on `s`, the key and the reference digest of `tx'` at the same input index.

So the accepted result is invariant over transactions with the same committed fields, whatever their scriptSigs.
The theorem says nothing about a transaction whose fields differ. `verify := fun _ _ _ => some true` satisfies its conclusion for every digest.
The commitment of the preimage to those fields is `legacyReferencePlan_allOnly_commits`.
A claim that the signature binds the fields also needs cryptographic and verifier assumptions, which DogeLib does not make.

The theorem does not say that `tx'` passes the template. A different scriptSig of input `ctx.index` changes the execution, and `tx'` is not an `InputContext` here.
The theorem applies to each pair that Core reaches in `multisigVisits`.
-/
theorem MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigs : List (List UInt8))
    (s key : List UInt8) (hashType : UInt8) (hh : HashType.IsAllOnly hashType.toUInt32)
    (hacc : sigAccepted ctx verify (ordinaryCode (multisigRecoveryScript k keys R) sigs) (s ++ [hashType]) key = true)
    (tx' : Transaction) (hf : legacyAllFields ctx.tx = legacyAllFields tx') :
    verify s key (legacyReferencePlan
      ⟨⟨ordinaryCode (multisigRecoveryScript k keys R) sigs,
        ordinaryCode_length_lt h.n_le h.keys_length h.recovery_length sigs⟩⟩
      tx' ctx.index hashType.toUInt32).digest = some true := by
  obtain ⟨_, s0, ht0, hsig, hv⟩ := (h.sigAccepted_ordinary_iff_reference sigs _ key).mp hacc
  obtain ⟨rfl, hht⟩ := List.append_inj' hsig rfl
  cases hht
  rw [← legacyReferencePlan_eq_of_allFields _ _ _ _ _ hh hf]
  exact hv

/--
**Commitment, recovery branch.** Under `MultisigRecoverySpend`, take any signature `sigR`, and a signature `s ++ [hashType]` that `sigAccepted` accepts for `key` with the script code of the recovery branch.
Let the hash type be `IsAllOnly`: ALL, without ANYONECANPAY.
Take any transaction `tx'` with the same `legacyAllFields` as `ctx.tx`.
Then `verify` returns `some true` on `s`, the key and the reference digest of `tx'` at the same input index.

The result is invariance only. The theorem says nothing about a transaction whose fields differ, and a signature-binding claim also needs cryptographic and verifier assumptions.
The theorem does not say that `tx'` passes the template. A different scriptSig of input `ctx.index` changes the execution, and `tx'` is not an `InputContext` here.
-/
theorem MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits
    (h : MultisigRecoverySpend ctx prevScriptPubKey flags verify k keys R S) (sigR : List UInt8)
    (s key : List UInt8) (hashType : UInt8) (hh : HashType.IsAllOnly hashType.toUInt32)
    (hacc : sigAccepted ctx verify (recoveryCode (multisigRecoveryScript k keys R) sigR) (s ++ [hashType]) key = true)
    (tx' : Transaction) (hf : legacyAllFields ctx.tx = legacyAllFields tx') :
    verify s key (legacyReferencePlan
      ⟨⟨recoveryCode (multisigRecoveryScript k keys R) sigR,
        recoveryCode_length_lt h.n_le h.keys_length h.recovery_length sigR⟩⟩
      tx' ctx.index hashType.toUInt32).digest = some true := by
  obtain ⟨_, s0, ht0, hsig, hv⟩ := (h.sigAccepted_recovery_iff_reference sigR _ key).mp hacc
  obtain ⟨rfl, hht⟩ := List.append_inj' hsig rfl
  cases hht
  rw [← legacyReferencePlan_eq_of_allFields _ _ _ _ _ hh hf]
  exact hv

end

end DogeLib.Script
