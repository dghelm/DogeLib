module

public import DogeLib.Script.Proofs.CheckerExtension
public import DogeLib.Script.Proofs.CoreVerifier
public import DogeLib.Script.Proofs.MultisigRecovery

/-!
# Proofs: the fixed digest of `SIGHASH_SINGLE`

Core's `SignatureHash` returns the fixed digest `one` when the hash type is SINGLE and the input index is at least the number of outputs (D3, lines 1231 to 1236).
`ReachesFixedDigest` in `DogeLib.Transaction.Proofs.LegacySighash` is that condition, and `legacyOne` is the digest.
A signature check on that digest reads no part of the transaction.
This module states that fact for a whole legacy spend.

## The transaction-free checker

`fixedDigestChecker verify` is a `SignatureChecker` without a transaction.
It answers a signature check only when the signature is empty, the key fails `isValidPubKey`, or the hash type is SINGLE.
For a SINGLE hash type it asks `verify` about the digest `legacyOne`.
Every other signature check is unavailable, and so is every lock-time and sequence check.

- `transactionChecker_extends_fixedDigestChecker`: for a transaction with at most `nIn` outputs, `transactionChecker` gives every answer of `fixedDigestChecker`.
- `verifyLegacySpend_eq_fixedDigest`: for such an input, when `verifyScript` with `fixedDigestChecker` is decided, `verifyLegacySpend` gives the same result.
  The second result has no transaction, so the first does not depend on the transaction or on the index.
- `verifyLegacySpend_fixedDigest_congr`: two such inputs with the same `scriptSig` and the same previous `scriptPubKey` give the same result.

The hypothesis that the call with `fixedDigestChecker` is decided covers every script, including `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIGVERIFY`, `OP_CODESEPARATOR` and a signature push that `FindAndDelete` removes.
It fails when a reached signature check has a valid key and a nonempty signature with another hash type.
It also fails when `OP_CHECKLOCKTIMEVERIFY` or `OP_CHECKSEQUENCEVERIFY` reaches the checker.
The theorems say nothing about such a spend.

## Templates

For three templates the call with `fixedDigestChecker` is decided, when every signature satisfies `HasSingleHashType` and `verify` decides every request on `legacyOne`.
`coreVerifier` decides every request (`coreVerifier_some`).

- `verifyLegacySpend_p2pkh_fixedDigest`: Pay to Public Key Hash, `p2pkhScriptPubKey`, with a `scriptSig` that pushes a signature and a key.
- `verifyLegacySpend_multisig_fixedDigest`: bare `m`-of-`n` multisig, `multisigScript`, with a `scriptSig` that pushes a dummy item and `m` signatures.
- `verifyLegacySpend_p2shMultisig_fixedDigest`: the same script as a P2SH redeem script, with a `scriptSig` that also pushes the redeem script.

Each `scriptSig` is `pushScript` of its items: one `CScript() << item` push for each item.
The theorems do not require that the key hash matches, that a signature verifies, or that the spend is accepted.

## What the theorems do not say

They hold relative to the verifier parameter `verify`.
They do not say that a signature for `legacyOne` exists for a key, or that one is hard to compute.
They compare two results of the Lean definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-! ## The transaction-free checker -/

/--
The signature is empty, or its last byte is a SINGLE hash type: `HashType.isSingle` holds for the byte zero-extended to 32 bits.
The bytes `0x03` and `0x83` are SINGLE, and so is every other byte whose low five bits are 3, such as `0x23`.
-/
def HasSingleHashType (sig : List UInt8) : Prop :=
  ∀ hashType, sig.getLast? = some hashType → HashType.isSingle hashType.toUInt32 = true

/--
A signature checker without a transaction, for the fixed digest `legacyOne`.

A signature check follows `transactionChecker` in its first two steps: a key that fails `isValidPubKey` gives `false`, and so does an empty signature.
Take a signature whose last byte is a SINGLE hash type, and a script code shorter than 2^64 bytes.
The answer is `verify` on the signature without that byte, the key and `legacyOne`.
Every other signature check is unavailable.
The lock-time and sequence checks are always unavailable.

The checker is a device of the theorems in this module. It is not a model of a Core class.
-/
def fixedDigestChecker (verify : SignatureVerifier) : SignatureChecker where
  checkSig sig pubKey code :=
    if !isValidPubKey pubKey then some false
    else match sig.getLast? with
      | none => some false
      | some hashType =>
        if HashType.isSingle hashType.toUInt32 && decide (code.length < 2 ^ 64) then
          verify sig.dropLast pubKey legacyOne
        else none
  checkLockTime _ := none
  checkSequence _ := none

/--
For every transaction and input index `nIn` with at most `nIn` outputs, and every verifier:
`transactionChecker` gives the answer of `fixedDigestChecker` on every request that `fixedDigestChecker` answers.
-/
theorem transactionChecker_extends_fixedDigestChecker {tx : Transaction} {nIn : UInt32} (verify : SignatureVerifier)
    (hout : tx.outputs.val.length ≤ nIn.toNat) :
    (transactionChecker tx nIn verify).Extends (fixedDigestChecker verify) := by
  refine ⟨fun sig key code b hb => ?_, fun n b hb => (by simp [fixedDigestChecker] at hb),
    fun n b hb => (by simp [fixedDigestChecker] at hb)⟩
  simp only [fixedDigestChecker] at hb
  cases hk : isValidPubKey key
  · simp only [hk, Bool.not_false, ↓reduceIte, Option.some.injEq] at hb
    rw [transactionChecker_invalidKey _ _ _ _ _ hk, hb]
  · rcases List.eq_nil_or_concat sig with rfl | ⟨s, x, rfl⟩
    · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.getLast?_nil, Option.some.injEq] at hb
      rw [transactionChecker_emptySig _ _ _ _ hk, hb]
    · simp only [hk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.concat_eq_append,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, List.dropLast_concat] at hb
      split at hb
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        rw [List.concat_eq_append, transactionChecker_checkSig_fixed _ _ hk hcond.2 (.inr ⟨hcond.1, hout⟩), hb]
      · cases hb

/--
Take a verifier that decides every request on the digest `legacyOne`, and a signature with `HasSingleHashType`.
For every key and every script code shorter than 2^64 bytes, `fixedDigestChecker` answers the signature check.
-/
theorem fixedDigestChecker_checkSig_ne_none {verify : SignatureVerifier} (hv : ∀ s k, verify s k legacyOne ≠ none)
    {sig : List UInt8} (hs : HasSingleHashType sig) (key : List UInt8) {code : List UInt8}
    (hc : code.length < 2 ^ 64) : (fixedDigestChecker verify).checkSig sig key code ≠ none := by
  simp only [fixedDigestChecker]
  split
  · simp
  · split
    · simp
    · rename_i hashType hl
      simp only [hs hashType hl, hc, decide_true, Bool.and_self, ↓reduceIte]
      exact hv _ _

/--
Take an input context with at most `index` outputs, a previous `scriptPubKey`, a flag set and a verifier.
Assume that, when the flag set is supported, `verifyScript` with `fixedDigestChecker` is decided on the input's `scriptSig`.
Then `verifyLegacySpend` gives the same result.
The right side reads the transaction only through the bytes of `scriptSig`.
A flag set with an unsupported bit gives the same unsupported result on both sides.
-/
theorem verifyLegacySpend_eq_fixedDigest {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier} (hout : ctx.tx.outputs.val.length ≤ ctx.index.toNat)
    (hdec : unsupportedFlagBits flags = 0 →
      (verifyScript (fixedDigestChecker verify) flags ctx.input.scriptSig.bytes.val
        prevScriptPubKey.bytes.val).Decided) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      verifyScript (fixedDigestChecker verify) flags ctx.input.scriptSig.bytes.val prevScriptPubKey.bytes.val := by
  rw [verifyLegacySpend_eq]
  by_cases hf : unsupportedFlagBits flags = 0
  · rcases verifyScript_checker_extends (transactionChecker_extends_fixedDigestChecker verify hout) flags
        ctx.input.scriptSig.bytes.val prevScriptPubKey.bytes.val with ⟨u, hu⟩ | he
    · exact absurd hu ((hdec hf).ne_unsupported u)
    · exact he
  · rw [verifyScript_unsupportedFlags hf, verifyScript_unsupportedFlags hf]

/--
Take input contexts `ctx` and `ctx'` with the same `scriptSig`, a previous `scriptPubKey`, a flag set and a verifier.
Assume that each context has at most as many outputs as its index.
Assume that, when the flag set is supported, `verifyScript` with `fixedDigestChecker` is decided on that `scriptSig`.
Then `verifyLegacySpend` gives the same result for `ctx` and for `ctx'`.
The two transactions can differ in every other part: the version, the outpoints, the sequences, the other inputs, the outputs and the lock time.
The two indices can differ.
-/
theorem verifyLegacySpend_fixedDigest_congr {ctx ctx' : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier} (hss : ctx.input.scriptSig = ctx'.input.scriptSig)
    (hout : ctx.tx.outputs.val.length ≤ ctx.index.toNat) (hout' : ctx'.tx.outputs.val.length ≤ ctx'.index.toNat)
    (hdec : unsupportedFlagBits flags = 0 →
      (verifyScript (fixedDigestChecker verify) flags ctx.input.scriptSig.bytes.val
        prevScriptPubKey.bytes.val).Decided) :
    verifyLegacySpend ctx prevScriptPubKey flags verify = verifyLegacySpend ctx' prevScriptPubKey flags verify := by
  rw [verifyLegacySpend_eq_fixedDigest hout hdec, verifyLegacySpend_eq_fixedDigest hout' (hss ▸ hdec), hss]

/-! ## Pushes -/

/-- The script that pushes each item with `CScript() << item` (`pushEncoding`), in order. -/
def pushScript (items : List (List UInt8)) : List UInt8 := (items.map pushEncoding).flatten

/-- For every length, the push header starts with a push opcode: a byte of at most `OP_PUSHDATA4` (`0x4e`). -/
theorem pushHeader_opcode_le (n : Nat) : ∃ o lf, pushHeader n = o :: lf ∧ o ≤ 0x4e := by
  unfold pushHeader
  split
  · rename_i h
    exact ⟨_, _, rfl, (by decide : ∀ n, n < 76 → n.toUInt8 ≤ 0x4e) n h⟩
  · split
    · exact ⟨_, _, rfl, by decide⟩
    · split
      · exact ⟨_, _, rfl, by decide⟩
      · exact ⟨_, _, rfl, by decide⟩

/-- A push opcode, a byte of at most `0x4e`, does not count as an operation and is not disabled. -/
theorem pushOpcode_facts (op : UInt8) (h : op ≤ 0x4e) : (∀ k, countOp op k = k) ∧ isDisabled op = false := by
  have := forall_byte_of_forall_lt (fun op => op ≤ 0x4e → ¬(0x60 : UInt8) < op ∧ isDisabled op = false)
    (by decide +kernel) op h
  exact ⟨fun k => by simp [countOp, this.1], this.2⟩

variable {checker : Option SignatureChecker} {flags : UInt32} {script : List UInt8}

/--
Take a checker, a flag set and a script shorter than 2^32 bytes.
Take a state in an executing branch, at a cursor where `pushScript items` starts.
The loop gives a rejection, or it continues after the pushes with `items` added to the main stack.
-/
theorem evalLoop_pushScript (hlen : script.length < 2 ^ 32) :
    ∀ (items : List (List UInt8)) (s : ExecState) (tail : List UInt8),
      script.drop s.pc = pushScript items ++ tail → s.fExec = true →
      (∃ e, evalLoop checker flags script s = .rejected e) ∨
        evalLoop checker flags script s =
          evalLoop checker flags script
            { s with pc := s.pc + (pushScript items).length, stack := s.stack ++ items }
  | [], s, tail, _, _ => .inr (by simp [pushScript])
  | P :: ks, s, tail, hd, hx => by
    have hd' : script.drop s.pc = pushEncoding P ++ (pushScript ks ++ tail) := by
      simpa [pushScript] using hd
    have hP : P.length < 2 ^ 32 := by
      have := congrArg List.length hd'
      simp only [List.length_drop, List.length_append, pushEncoding] at this
      omega
    obtain ⟨o, lf, hh, henc⟩ := pushHeader_encoding P hP
    obtain ⟨o', lf', hh', ho⟩ := pushHeader_opcode_le P.length
    rw [hh] at hh'
    obtain ⟨rfl, rfl⟩ := List.cons.inj hh'
    obtain ⟨hcount, hdis⟩ := pushOpcode_facts o ho
    have hb : pushEncoding P = o :: lf ++ P := by simp [pushEncoding, hh]
    have hread : readInstruction script s.pc =
        .instruction ⟨o, pushEncoding P, P, s.pc + (pushEncoding P).length⟩ :=
      readInstruction_eq_instruction_iff.mpr ⟨lf, pushScript ks ++ tail, henc, hb, hd', rfl⟩
    rw [evalLoop_instruction hread]
    by_cases hp : maxScriptElementSize < P.length
    · exact .inl ⟨.pushSize, by rw [evalInstruction_pushSize hp]⟩
    by_cases hc : maxOpsPerScript < s.opCount
    · exact .inl ⟨.opCount, by rw [evalInstruction_opCount (Nat.not_lt.mp hp) (by rw [hcount]; exact hc)]⟩
    rw [evalInstruction_exec hx (Nat.not_lt.mp hp) (by rw [hcount]; exact Nat.not_lt.mp hc) hdis,
      execOpcode_push ho]
    dsimp only
    by_cases hst : maxStackItems < (s.stack ++ [P]).length + s.altstack.length
    · exact .inl ⟨.stackSize, by simp only [hst, ↓reduceIte]⟩
    · simp only [hst, ↓reduceIte]
      have hd'' : script.drop (s.pc + (pushEncoding P).length) = pushScript ks ++ tail := by
        rw [← List.drop_drop, hd', List.drop_left]
      rcases evalLoop_pushScript hlen ks
          { s with opCount := countOp o s.opCount, stack := s.stack ++ [P], pc := s.pc + (pushEncoding P).length }
          tail hd'' hx with ⟨e, he⟩ | he
      · exact .inl ⟨e, he⟩
      · refine .inr ?_
        rw [he]
        simp only [hcount, pushScript, List.map_cons, List.flatten_cons, List.length_append, List.append_assoc,
          List.singleton_append, Nat.add_assoc]

/--
For every checker, supported flag set, list of items and stack: `pushScript items` gives a rejection, or it succeeds with `items` added to the stack.
The result is never unsupported.
-/
theorem evalScript_pushScript (hf : unsupportedFlagBits flags = 0) (items stack : List (List UInt8)) :
    (∃ e, evalScript checker flags (pushScript items) stack = .rejected e) ∨
      ∃ s, evalScript checker flags (pushScript items) stack = .ok s ∧ s.stack = stack ++ items := by
  unfold evalScript
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i hsz
    have hlen : (pushScript items).length < 2 ^ 32 := by simp only [maxScriptSize] at hsz; omega
    rcases evalLoop_pushScript (checker := checker) (flags := flags) hlen items (ExecState.init stack) []
        (by simp [ExecState.init]) rfl with ⟨e, he⟩ | he
    · exact .inl ⟨e, he⟩
    · refine .inr ?_
      rw [he, evalLoop_atEnd (by simp [ExecState.init])]
      simp [ExecState.init]

/-! ## Steps that are decided -/

/-- For every check function and lists: an error of `multisigLoop` is an error of `check` on a signature and a key of the lists. -/
theorem multisigLoop_error_mem {α β ε : Type} {check : α → β → Except ε Bool} {sigs : List α} {keys : List β}
    {e : ε} (h : multisigLoop check sigs keys = .error e) : ∃ a ∈ sigs, ∃ b ∈ keys, check a b = .error e := by
  induction keys generalizing sigs with
  | nil => cases sigs <;> cases h
  | cons b bs ih =>
    cases sigs with
    | nil => cases h
    | cons a as =>
      simp only [multisigLoop] at h
      split at h
      · rename_i e' he
        cases h
        exact ⟨a, by simp, b, by simp, he⟩
      · rename_i ok _
        have hsub : ∀ x ∈ (if ok = true then as else a :: as), x ∈ a :: as := by
          intro x hx
          split at hx
          · exact List.mem_cons_of_mem a hx
          · exact hx
        revert h hsub
        generalize (if ok = true then as else a :: as) = rest
        intro h hsub
        by_cases hl : bs.length < rest.length
        · simp [hl] at h
        · simp only [hl, ite_false] at h
          obtain ⟨x, hx, y, hy, hxy⟩ := ih h
          exact ⟨x, hsub x hx, y, List.mem_cons_of_mem _ hy, hxy⟩

/-- For every checker that answers the signature check of `sig` and `key` on `code`: `multisigCheck` gives no unsupported error on that pair. -/
theorem multisigCheck_ne_unsupported {c : SignatureChecker} {code sig key : List UInt8} {op : UInt8}
    (hc : c.checkSig sig key code ≠ none) (u : Unsupported) :
    multisigCheck c flags code op sig key ≠ .error (.unsupported u) := by
  unfold multisigCheck
  split
  · simp
  · split
    · simp
    · cases h : c.checkSig sig key code with
      | none => exact absurd h hc
      | some b => simp

/--
Take a checker, a script, a flag set, an opcode, and a state whose stack ends with `sig` and `key`.
If the checker answers the signature check of `sig` and `key` on the script code of the step, `checkSigStep` is not unsupported.
-/
theorem checkSigStep_ne_unsupported {c : SignatureChecker} {s : ExecState} {op : UInt8}
    {rest : List (List UInt8)} {sig key : List UInt8} (hs : s.stack = rest ++ [sig, key])
    (hc : c.checkSig sig key (effectiveScriptCode script s.beginCodeHash [sig]) ≠ none) (u : Unsupported) :
    checkSigStep c script flags s op ≠ .unsupported u := by
  simp only [checkSigStep, hs, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  split
  · simp
  · split
    · simp
    · cases h : c.checkSig sig key (effectiveScriptCode script s.beginCodeHash [sig]) with
      | none => exact absurd h hc
      | some b =>
        dsimp only
        split
        · split <;> simp
        · simp

/-! ## Pay to Public Key Hash -/

/-- The Pay to Public Key Hash (P2PKH) output script for the 20 bytes `h`: `OP_DUP OP_HASH160 <h> OP_EQUALVERIFY OP_CHECKSIG`. -/
def p2pkhScriptPubKey (h : List UInt8) : List UInt8 := [0x76, 0xa9, 0x14] ++ h ++ [0x88, 0xac]

/--
Take a checker, a supported flag set, 20 bytes `h`, a signature `sig` and a key `key`.
Assume that the checker answers the signature check of `sig` and `key` on every script code of at most 10,000 bytes.
Then the P2PKH script on the stack `[sig, key]` is decided.
-/
theorem evalScript_p2pkh_decided {c : SignatureChecker} {h sig key : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (hh : h.length = 20)
    (hc : ∀ code, code.length ≤ maxScriptSize → c.checkSig sig key code ≠ none) :
    (evalScript (some c) flags (p2pkhScriptPubKey h) [sig, key]).Decided := by
  have hlen : (p2pkhScriptPubKey h).length = 25 := by simp [p2pkhScriptPubKey, hh]
  have hsz : ¬maxScriptSize < (p2pkhScriptPubKey h).length := by rw [hlen]; decide
  have hpush : pushEncoding h = 0x14 :: h := by rw [pushEncoding_small (by omega), hh]; rfl
  have hd23 : (p2pkhScriptPubKey h).drop 23 = [0x88, 0xac] :=
    List.drop_left' (l₁ := 0x76 :: 0xa9 :: 0x14 :: h) (by simp [hh])
  have hd24 : (p2pkhScriptPubKey h).drop 24 = [0xac] := by
    rw [show 24 = 23 + 1 from rfl, ← List.drop_drop, hd23]; rfl
  unfold evalScript
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte, hsz]
  -- OP_DUP
  rw [evalLoop_op (op := 0x76) (rest := 0xa9 :: 0x14 :: (h ++ [0x88, 0xac])) (by simp [p2pkhScriptPubKey, ExecState.init])
    (by decide) (Or.inl rfl) (by simp [countOp, ExecState.init, maxOpsPerScript]) (by decide)]
  rw [execOpcode_dup (rest := [sig]) (x := key) rfl]
  simp only [ExecState.init, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    show ¬maxStackItems < 0 + 1 + 1 + 1 + 0 by decide, ↓reduceIte, Nat.zero_add]
  -- OP_HASH160
  rw [evalLoop_op (op := 0xa9) (rest := 0x14 :: (h ++ [0x88, 0xac])) (by simp [p2pkhScriptPubKey])
    (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
  rw [execOpcode_hash160 (rest := [sig, key]) (x := key) rfl]
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    show ¬maxStackItems < 0 + 1 + 1 + 1 + 0 by decide, ↓reduceIte]
  -- the push of `h`
  rw [evalLoop_instruction (readInstruction_push (d := h) (rest := [0x88, 0xac])
    (by simp [p2pkhScriptPubKey, hpush]) (by omega))]
  rw [evalInstruction_exec rfl (by simp [maxScriptElementSize, hh]) (by simp [hh, countOp, maxOpsPerScript])
      (by simp [hh, isDisabled]),
    execOpcode_push (by simp [hh])]
  simp only [hh, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
    show ¬maxStackItems < 0 + 1 + 1 + 1 + 1 + 0 by decide, ↓reduceIte]
  -- OP_EQUALVERIFY
  rw [evalLoop_op (op := 0x88) (rest := [0xac]) hd23
    (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
  by_cases heq : (Cryptography.Hash.hash160 ⟨key.toArray⟩).toList = h
  · rw [heq, execOpcode_equalVerify_eq (rest := [sig, key]) (x := h) rfl]
    simp only [List.length_cons, List.length_nil, show ¬maxStackItems < 0 + 1 + 1 + 0 by decide, ↓reduceIte]
    -- OP_CHECKSIG
    rw [evalLoop_op (op := 0xac) (rest := []) hd24
      (by decide) (Or.inl rfl) (by simp [countOp, maxOpsPerScript]) (by decide)]
    rw [execOpcode_checkSig (Or.inl rfl)]
    cases hstep : checkSigStep c (p2pkhScriptPubKey h) flags _ 0xac with
    | next t =>
      dsimp only
      split
      · trivial
      · rw [evalLoop_atEnd (by simp [hlen])]
        split <;> trivial
    | rejected e => trivial
    | unsupported u =>
      refine absurd hstep (checkSigStep_ne_unsupported (rest := []) rfl (hc _ ?_) u)
      exact Nat.le_trans (effectiveScriptCode_length_le _ _ _) (Nat.not_lt.mp hsz)
  · rw [execOpcode_equalVerify_ne (rest := [sig, key]) rfl heq]
    trivial

/--
Take an input context with at most `index` outputs, a flag set, 20 bytes `h`, a signature `sig` and a key `key`.
Take a verifier that decides every request on `legacyOne`.
Assume that `scriptSig` pushes `sig` and then `key`, and that the previous `scriptPubKey` is the P2PKH script of `h`.
Assume also that `sig` satisfies `HasSingleHashType`.
Then `verifyLegacySpend` is `verifyScript` with `fixedDigestChecker`, which has no transaction.
The statement does not assume that the HASH160 digest of `key` is `h`, or that the signature verifies.
-/
theorem verifyLegacySpend_p2pkh_fixedDigest {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier} {h sig key : List UInt8}
    (hv : ∀ s k, verify s k legacyOne ≠ none) (hout : ctx.tx.outputs.val.length ≤ ctx.index.toNat)
    (hss : ctx.input.scriptSig.bytes.val = pushScript [sig, key])
    (hspk : prevScriptPubKey.bytes.val = p2pkhScriptPubKey h) (hh : h.length = 20)
    (hsig : HasSingleHashType sig) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      verifyScript (fixedDigestChecker verify) flags (pushScript [sig, key]) (p2pkhScriptPubKey h) := by
  rw [verifyLegacySpend_eq_fixedDigest hout, hss, hspk]
  intro hf
  rw [hss, hspk]
  have hnot : isPayToScriptHash (p2pkhScriptPubKey h) = false := by simp [isPayToScriptHash, p2pkhScriptPubKey, hh]
  refine verifyScript_decided hf ?_ (fun s hs => ?_) (fun s redeem rest _ _ ht _ => by rw [hnot] at ht; cases ht)
  · rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf [sig, key] [] with
      ⟨e, he⟩ | ⟨s, he, -⟩ <;> rw [he] <;> trivial
  · rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf [sig, key] [] with
      ⟨e, he⟩ | ⟨s', he, hst⟩
    · rw [he] at hs; cases hs
    · rw [he] at hs
      cases hs
      rw [hst]
      exact evalScript_p2pkh_decided hf hh fun code hcode =>
        fixedDigestChecker_checkSig_ne_none hv hsig key (by simp only [maxScriptSize] at hcode; omega)

/-! ## Multisig -/

/--
The `m`-of-`n` multisig script for the keys `keys`, where `n` is the number of keys: `OP_m <keys> OP_n OP_CHECKMULTISIG`.
It is meaningful for `1 ≤ m ≤ n ≤ 16`.
-/
def multisigScript (m : Nat) (keys : List (List UInt8)) : List UInt8 :=
  smallIntOpcode m :: (pushScript keys ++ [smallIntOpcode keys.length, 0xae])

/--
Take a checker, a supported flag set, `n` keys, a dummy item and `m` signatures `sigs` in push order, with `1 ≤ m ≤ n ≤ 16`.
Assume that the checker answers the signature check of each signature of `sigs` with every key, on every script code of at most 10,000 bytes.
Then the multisig script on the stack `dummy :: sigs` is decided.
-/
theorem evalScript_multisigScript_decided {c : SignatureChecker} {m : Nat} {keys sigs : List (List UInt8)}
    {dummy : List UInt8} (hf : unsupportedFlagBits flags = 0) (hm1 : 1 ≤ m) (hmn : m ≤ keys.length)
    (hn : keys.length ≤ 16) (hsigs : sigs.length = m)
    (hc : ∀ sig ∈ sigs, ∀ key code, code.length ≤ maxScriptSize → c.checkSig sig key code ≠ none) :
    (evalScript (some c) flags (multisigScript m keys) (dummy :: sigs)).Decided := by
  obtain ⟨k1, k2, k3, -, k5, k6, k7⟩ := smallIntOpcode_facts m (by omega) hm1
  obtain ⟨n1, n2, n3, -, n5, n6, n7⟩ := smallIntOpcode_facts keys.length (by omega) (by omega)
  obtain ⟨dn, gn⟩ := decode_encode_small hn
  obtain ⟨dm, gm⟩ := decode_encode_small (show m ≤ 16 by omega)
  unfold evalScript
  simp only [hf, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · trivial
  rename_i hsz
  have hlen : (multisigScript m keys).length = 1 + (pushScript keys).length + 2 := by
    simp [multisigScript]; omega
  have hlt : (multisigScript m keys).length < 2 ^ 32 := by simp only [maxScriptSize] at hsz; omega
  have hdn : (multisigScript m keys).drop (1 + (pushScript keys).length) = [smallIntOpcode keys.length, 0xae] :=
    List.drop_left' (l₁ := smallIntOpcode m :: pushScript keys) (by simp; omega)
  have hdc : (multisigScript m keys).drop (1 + (pushScript keys).length + 1) = [0xae] := by
    rw [← List.drop_drop, hdn]; rfl
  -- OP_m
  rw [evalLoop_op (op := smallIntOpcode m) (rest := pushScript keys ++ [smallIntOpcode keys.length, 0xae])
    (by simp [multisigScript, ExecState.init]) k1 (Or.inl rfl) (by simp [countOp, k7, ExecState.init]) k5]
  rw [execOpcode_smallInteger (Or.inr ⟨k2, k3⟩)]
  simp only [ExecState.init, List.length_append, List.length_cons, List.length_nil, hsigs,
    show ¬maxStackItems < m + 1 + 0 + 1 + 0 by simp only [maxStackItems]; omega, ↓reduceIte, Nat.zero_add]
  -- the key pushes
  rcases evalLoop_pushScript (checker := some c) (flags := flags) hlt keys
      ⟨dummy :: sigs ++ [ScriptNum.encode ((smallIntOpcode m).toNat - 0x50 : Int)], [], 1, 0, [],
        countOp (smallIntOpcode m) 0⟩
      [smallIntOpcode keys.length, 0xae] (by simp [multisigScript]) rfl with ⟨e, he⟩ | he
  · rw [he]; trivial
  rw [he]
  dsimp only
  -- OP_n
  rw [evalLoop_op (op := smallIntOpcode keys.length) (rest := [0xae])
    hdn n1 (Or.inl rfl) (by simp [countOp, n7, k7]) n5]
  rw [execOpcode_smallInteger (Or.inr ⟨n2, n3⟩)]
  dsimp only
  split
  · trivial
  -- OP_CHECKMULTISIG
  rw [evalLoop_op (op := 0xae) (rest := [])
    hdc (by decide) (Or.inl rfl) (by simp [countOp, n7, k7, maxOpsPerScript]) (by decide)]
  rw [execOpcode_checkMultisig (Or.inl rfl)]
  have e1 : (((smallIntOpcode m).toNat : Int) - 0x50) = (m : Int) := by rw [k6]; omega
  have e2 : (((smallIntOpcode keys.length).toNat : Int) - 0x50) = (keys.length : Int) := by rw [n6]; omega
  rw [checkMultisigStep_counted (keys := keys.reverse) (sigs := sigs.reverse) (below := []) (dummy := dummy)
    (nTop := ScriptNum.encode keys.length) (mTop := ScriptNum.encode m) (by simp [e1, e2]) dn
    (by simpa using gn) dm (by simpa [hsigs] using gm) (by simp [maxPubKeysPerMultisig]; omega)
    (by simp; omega) (by simp [countOp, n7, k7, maxOpsPerScript]; omega)]
  cases hL : multisigLoop (multisigCheck c flags (effectiveScriptCode (multisigScript m keys) _ sigs.reverse) 0xae)
      sigs.reverse keys.reverse with
  | error r =>
    dsimp only
    obtain ⟨sig, hsig, key, -, hck⟩ := multisigLoop_error_mem hL
    cases r with
    | next t => exact absurd rfl (multisigLoop_multisigCheck_error hL t)
    | rejected e => trivial
    | unsupported u =>
      refine absurd hck (multisigCheck_ne_unsupported (hc sig (by simpa using hsig) key _ ?_) u)
      exact Nat.le_trans (effectiveScriptCode_length_le _ _ _) (Nat.not_lt.mp hsz)
  | ok b =>
    dsimp only
    by_cases hd : (hasFlag flags ScriptFlags.nullDummy && !dummy.isEmpty) = true
    · simp only [hd, ↓reduceIte]
      trivial
    · simp only [hd, Bool.false_eq_true, ↓reduceIte, show (0xae : UInt8) ≠ 0xaf by decide]
      split
      · trivial
      · rw [evalLoop_atEnd (by simp [hlen])]
        split <;> trivial

/-- The multisig script is not the P2SH template: its first byte is `OP_m`, not `OP_HASH160`. -/
theorem isPayToScriptHash_multisigScript {m : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 16) (keys : List (List UInt8)) :
    isPayToScriptHash (multisigScript m keys) = false := by
  obtain ⟨-, -, k3, -⟩ := smallIntOpcode_facts m (by omega) hm1
  have hne : smallIntOpcode m ≠ 0xa9 := by
    intro h; rw [h] at k3; exact absurd k3 (by decide)
  simp [isPayToScriptHash, multisigScript, hne]

/--
Take an input context with at most `index` outputs, a flag set, `n` keys, a dummy item and `m` signatures, with `1 ≤ m ≤ n ≤ 16`.
Take a verifier that decides every request on `legacyOne`.
Assume that `scriptSig` pushes the dummy item and then the signatures, and that the previous `scriptPubKey` is the multisig script.
Assume also that each signature satisfies `HasSingleHashType`.
Then `verifyLegacySpend` is `verifyScript` with `fixedDigestChecker`, which has no transaction.
The statement does not assume that a signature verifies.
-/
theorem verifyLegacySpend_multisig_fixedDigest {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier} {m : Nat} {keys sigs : List (List UInt8)} {dummy : List UInt8}
    (hv : ∀ s k, verify s k legacyOne ≠ none) (hout : ctx.tx.outputs.val.length ≤ ctx.index.toNat)
    (hss : ctx.input.scriptSig.bytes.val = pushScript (dummy :: sigs))
    (hspk : prevScriptPubKey.bytes.val = multisigScript m keys) (hm1 : 1 ≤ m) (hmn : m ≤ keys.length)
    (hn : keys.length ≤ 16) (hsigs : sigs.length = m) (hsingle : ∀ sig ∈ sigs, HasSingleHashType sig) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      verifyScript (fixedDigestChecker verify) flags (pushScript (dummy :: sigs)) (multisigScript m keys) := by
  rw [verifyLegacySpend_eq_fixedDigest hout, hss, hspk]
  intro hf
  rw [hss, hspk]
  have hnot := isPayToScriptHash_multisigScript hm1 (by omega) keys
  refine verifyScript_decided hf ?_ (fun s hs => ?_) (fun s redeem rest _ _ ht _ => by rw [hnot] at ht; cases ht)
  · rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf (dummy :: sigs) [] with
      ⟨e, he⟩ | ⟨s, he, -⟩ <;> rw [he] <;> trivial
  · rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf (dummy :: sigs) [] with
      ⟨e, he⟩ | ⟨s', he, hst⟩
    · rw [he] at hs; cases hs
    · rw [he] at hs
      cases hs
      rw [hst]
      exact evalScript_multisigScript_decided hf hm1 hmn hn hsigs fun sig hsig key code hcode =>
        fixedDigestChecker_checkSig_ne_none hv (hsingle sig hsig) key
          (by simp only [maxScriptSize] at hcode; omega)

/--
Take an input context with at most `index` outputs, a flag set, `n` keys, a dummy item and `m` signatures, with `1 ≤ m ≤ n ≤ 16`.
Take a verifier that decides every request on `legacyOne`.
Assume that `scriptSig` pushes the dummy item, the signatures and then the multisig script.
Assume that the previous `scriptPubKey` is the P2SH commitment to that script.
Assume also that each signature satisfies `HasSingleHashType`.
Then `verifyLegacySpend` is `verifyScript` with `fixedDigestChecker`, which has no transaction.
With `P2SH` clear, the redeem script does not run, and the statement still holds.
-/
theorem verifyLegacySpend_p2shMultisig_fixedDigest {ctx : InputContext} {prevScriptPubKey : Transaction.Script}
    {flags : UInt32} {verify : SignatureVerifier} {m : Nat} {keys sigs : List (List UInt8)} {dummy : List UInt8}
    (hv : ∀ s k, verify s k legacyOne ≠ none) (hout : ctx.tx.outputs.val.length ≤ ctx.index.toNat)
    (hss : ctx.input.scriptSig.bytes.val = pushScript (dummy :: sigs ++ [multisigScript m keys]))
    (hspk : prevScriptPubKey.bytes.val = p2shScriptPubKey (multisigScript m keys)) (hm1 : 1 ≤ m)
    (hmn : m ≤ keys.length) (hn : keys.length ≤ 16) (hsigs : sigs.length = m)
    (hsingle : ∀ sig ∈ sigs, HasSingleHashType sig) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      verifyScript (fixedDigestChecker verify) flags (pushScript (dummy :: sigs ++ [multisigScript m keys]))
        (p2shScriptPubKey (multisigScript m keys)) := by
  rw [verifyLegacySpend_eq_fixedDigest hout, hss, hspk]
  intro hf
  rw [hss, hspk]
  have hstack : ∀ s, evalScript (some (fixedDigestChecker verify)) flags
      (pushScript (dummy :: sigs ++ [multisigScript m keys])) [] = .ok s →
      s.stack = dummy :: sigs ++ [multisigScript m keys] := by
    intro s hs
    rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf
        (dummy :: sigs ++ [multisigScript m keys]) [] with ⟨e, he⟩ | ⟨s', he, hst⟩
    · rw [he] at hs; cases hs
    · rw [he] at hs; cases hs; simpa using hst
  refine verifyScript_decided hf ?_ (fun s hs => ?_) (fun s redeem rest hs _ _ hr => ?_)
  · rcases evalScript_pushScript (checker := some (fixedDigestChecker verify)) hf
        (dummy :: sigs ++ [multisigScript m keys]) [] with ⟨e, he⟩ | ⟨s, he, -⟩ <;> rw [he] <;> trivial
  · rw [hstack s hs, p2shScriptPubKey,
      evalScript_p2shTemplate hf (hash160_toList_length _) (by simp [hsigs]; omega)]
    trivial
  · rw [hstack s hs] at hr
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.cons.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    exact evalScript_multisigScript_decided hf hm1 hmn hn hsigs fun sig hsig key code hcode =>
      fixedDigestChecker_checkSig_ne_none hv (hsingle sig hsig) key
        (by simp only [maxScriptSize] at hcode; omega)

/-- `coreVerifier` decides every request, so it satisfies the verifier hypothesis of the template theorems. -/
theorem coreVerifier_legacyOne_ne_none (s k : List UInt8) : coreVerifier s k legacyOne ≠ none := by
  simp [coreVerifier]

end DogeLib.Script
