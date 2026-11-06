module

public import DogeLib.Script.Verify
public import DogeLib.Script.Proofs.Eval
public import DogeLib.Transaction.Proofs.Serialization

/-!
# Proofs: `Script.Verify`

## The templates

- `isPushOnly_iff`: `isPushOnly` holds exactly when, at every instruction boundary, the reader does not stop on a short push, and every instruction it reads has an opcode of at most `OP_16`.
- `isPayToScriptHash_iff`: the P2SH template is `OP_HASH160`, a push of 20 bytes `h`, and `OP_EQUAL`.
- `evalScript_p2shTemplate`: the template replaces the top item `x` by `[1]` when the HASH160 digest of `x` is `h`, and by `[]` otherwise.
  It needs room for two more stack items. No property of the hash function is assumed.
- `evalScript_p2shTemplate_nil`: on an empty stack the template gives `INVALID_STACK_OPERATION`.

## `VerifyScript`

- `verifyScript_unsupportedFlags`: a flag outside `supportedFlags` gives `unsupported`, before any evaluation.
- `hasFlag_sigPushOnly_eq_false`, `hasFlag_cleanStack_eq_false`, `hasFlag_witness_eq_false`: a supported flag set has none of these bits, so Core's branches for them are unreachable.
- `verifyScript_noP2sh`: without `P2SH`, or without the template, the result is the two evaluations followed by the true-top check.
- `verifyScript_p2sh_saved_ne_nil`: Core's assert at D3 line 1469 holds. When the template accepts, the final stack of `scriptSig` is not empty.
- `verifyScript_p2sh`: with `P2SH`, the template, a push-only `scriptSig` whose final stack is `S ++ [redeem]`, and a `scriptPubKey` that accepts, the result is the evaluation of `redeem` on `S` with the true-top check.
- `verifyScript_p2sh_notPushOnly`: the same request with a `scriptSig` that is not push-only gives `SIG_PUSHONLY`.
- `verifyScript_p2sh_hash`, `verifyScript_p2sh_hash_ne`: the P2SH composition from the digest of the supplied `redeem`.
  When it equals the template's 20 bytes, the result is that of `redeem` on `S`. Otherwise it is `EVAL_FALSE`.
  These say nothing about any other redeem script with the same digest.

## The lock-time opcodes over a transaction

- `execOpcode_cltv_transaction`: with `transactionChecker` for an `InputContext`, a nonnegative operand is accepted exactly when Core's three conditions on the lock time and the input's sequence hold, and otherwise gives `UNSATISFIED_LOCKTIME`. The state is unchanged.
- `execOpcode_csv_transaction`: the same for `OP_CHECKSEQUENCEVERIFY`, Core's four conditions on the version and the input's sequence, for an operand with bit 31 clear.

## The spend predicate

- `verifyLegacySpend_eq`: `verifyLegacySpend` is `verifyScript` with `transactionChecker` on the input's `scriptSig`.
- `InputContext.ofDecoded`: the input context of an input of a transaction that `decodeBaseComplete` read. The reader gives the count bounds. `verifyLegacySpend_ofDecoded` unfolds the spend predicate on it.

These theorems are statements about the definitions. They do not say that the definitions match Core.
-/

@[expose] public section

namespace DogeLib.Script

open DogeLib.Transaction

/-! ## `IsPushOnly` -/

/-- The condition of `isPushOnly` at one cursor: the reader does not stop on a short push, and an instruction has an opcode of at most `OP_16`. -/
def PushOnlyAt (script : List UInt8) (pc : Nat) : Prop :=
  (∀ o p q, readInstruction script pc ≠ .truncated o p q) ∧
    ∀ i, readInstruction script pc = .instruction i → i.opcode ≤ 0x60

/-- At the end of the script, the loop of `isPushOnly` holds. -/
theorem isPushOnlyFrom_atEnd {script : List UInt8} {pc : Nat} (h : readInstruction script pc = .atEnd) :
    isPushOnlyFrom script pc = true := by
  rw [isPushOnlyFrom]
  split <;> simp_all

/-- At a short push, the loop of `isPushOnly` fails. -/
theorem isPushOnlyFrom_truncated {script : List UInt8} {pc : Nat} {o : UInt8} {p : ShortPart} {c : Nat}
    (h : readInstruction script pc = .truncated o p c) : isPushOnlyFrom script pc = false := by
  rw [isPushOnlyFrom]
  split <;> simp_all

/-- After an instruction, the loop of `isPushOnly` checks its opcode and continues at the cursor after it. -/
theorem isPushOnlyFrom_instruction {script : List UInt8} {pc : Nat} {i : Instruction}
    (h : readInstruction script pc = .instruction i) :
    isPushOnlyFrom script pc = (decide (i.opcode ≤ 0x60) && isPushOnlyFrom script i.next) := by
  rw [isPushOnlyFrom]
  split <;> (try simp_all) <;> rfl

/-- For every script and boundary `pc`: the loop from `pc` holds exactly when `PushOnlyAt` holds at every boundary at or after `pc`. -/
theorem isPushOnlyFrom_iff {script : List UInt8} {pc : Nat} (hpc : IsBoundary script pc) :
    isPushOnlyFrom script pc = true ↔ ∀ q, IsBoundary script q → pc ≤ q → PushOnlyAt script q := by
  match hr : readInstruction script pc with
  | .atEnd =>
    have hend := readInstruction_atEnd_iff.mp hr
    rw [isPushOnlyFrom_atEnd hr]
    simp only [true_iff]
    intro q hq hle
    have := hq.le_length
    have hq' : q = pc := by omega
    subst hq'
    exact ⟨fun _ _ _ h => (by rw [hr] at h; cases h), fun _ h => (by rw [hr] at h; cases h)⟩
  | .truncated o p c =>
    rw [isPushOnlyFrom_truncated hr]
    simp only [Bool.false_eq_true, false_iff]
    exact fun hall => (hall pc hpc (Nat.le_refl _)).1 o p c hr
  | .instruction i =>
    have hprog := readInstruction_progress hr
    have hnext : IsBoundary script i.next := .step hpc hr
    rw [isPushOnlyFrom_instruction hr]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [isPushOnlyFrom_iff hnext]
    constructor
    · rintro ⟨hop, hall⟩ q hq hle
      rcases hq.eq_or_next_le hpc hle with rfl | ⟨j, hj, hjn⟩
      · exact ⟨fun _ _ _ h => (by rw [hr] at h; cases h),
          fun j h => (by rw [hr] at h; cases h; exact hop)⟩
      · rw [← readInstruction_instruction_unique hr hj] at hjn
        exact hall q hq hjn
    · intro hall
      refine ⟨(hall pc hpc (Nat.le_refl _)).2 i hr, fun q hq hle => hall q hq (by omega)⟩
termination_by script.length - pc

/--
For every script: `isPushOnly` holds exactly when, at every instruction boundary, `readInstruction` does not stop on a short push, and every instruction it reads has an opcode of at most `OP_16` (`0x60`).
This is Core's loop of `GetOp` calls (D48, lines 241 to 252).
-/
theorem isPushOnly_iff (script : List UInt8) :
    isPushOnly script = true ↔
      ∀ pc, IsBoundary script pc →
        (∀ o p q, readInstruction script pc ≠ .truncated o p q) ∧
        (∀ i, readInstruction script pc = .instruction i → i.opcode ≤ 0x60) := by
  rw [isPushOnly, isPushOnlyFrom_iff .start]
  exact ⟨fun h q hq => h q hq (Nat.zero_le _), fun h q hq _ => h q hq⟩

/-! ## The P2SH template -/

/-- For every script: `isPayToScriptHash` holds exactly when the script is `OP_HASH160`, the push opcode `0x14`, 20 bytes `h`, and `OP_EQUAL`. -/
theorem isPayToScriptHash_iff (script : List UInt8) :
    isPayToScriptHash script = true ↔ ∃ h : List UInt8, h.length = 20 ∧ script = [0xa9, 0x14] ++ h ++ [0x87] := by
  constructor
  · intro hs
    simp only [isPayToScriptHash, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨hl, h0⟩, h1⟩, h22⟩ := hs
    match script, hl with
    | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22],
      _ =>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h22
      subst h0 h1 h22
      exact ⟨[a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21], rfl, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    simp [isPayToScriptHash, hh]

private theorem read0 (h : List UInt8) :
    readInstruction (0xa9 :: 0x14 :: (h ++ [0x87])) 0 = .instruction ⟨0xa9, [0xa9], [], 1⟩ := by
  simp [readInstruction, readOp, lengthFieldWidth]

private theorem read1 (h : List UInt8) (hh : h.length = 20) :
    readInstruction (0xa9 :: 0x14 :: (h ++ [0x87])) 1 = .instruction ⟨0x14, 0x14 :: h, h, 22⟩ := by
  rw [readInstruction_eq_instruction_iff]
  refine ⟨[], [0x87], ⟨by simp [lengthFieldWidth], ?_⟩, rfl, by simp, by simp [hh]⟩
  simp [pushSize, hh]

private theorem read22 (h : List UInt8) (hh : h.length = 20) :
    readInstruction (0xa9 :: 0x14 :: (h ++ [0x87])) 22 = .instruction ⟨0x87, [0x87], [], 23⟩ := by
  have : (0xa9 :: 0x14 :: (h ++ [0x87]) : List UInt8).drop 22 = [0x87] := by simp [hh]
  unfold readInstruction; rw [this]; simp [readOp, lengthFieldWidth]

/--
For every checker, supported flag set, 20 bytes `h`, item `x` and stack `S` with at most 998 items:
the template `OP_HASH160 <h> OP_EQUAL` on `S ++ [x]` succeeds with the stack `S ++ [b]`.
`b` is `[1]` when the HASH160 digest of `x` is `h`, and `[]` otherwise (D3, lines 712 to 738 and 847 to 871).
The statement assumes no property of the hash function.
-/
theorem evalScript_p2shTemplate {c : SignatureChecker} {flags : UInt32} {h x : List UInt8} {S : List (List UInt8)}
    (hf : unsupportedFlagBits flags = 0) (hh : h.length = 20) (hS : S.length + 2 ≤ 1000) :
    evalScript (some c) flags ([0xa9, 0x14] ++ h ++ [0x87]) (S ++ [x]) =
      .ok ⟨S ++ [boolBytes ((Cryptography.Hash.hash160 ⟨x.toArray⟩).toList == h)], [], 23, 0, [], 2⟩ := by
  simp only [List.cons_append, List.nil_append]
  have hS1 : ¬1000 < S.length + 1 := by omega
  have hS2 : ¬1000 < S.length + 1 + 1 := by omega
  have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  have h2 : ¬maxScriptSize < (0xa9 :: 0x14 :: (h ++ [0x87]) : List UInt8).length := by simp [hh, maxScriptSize]
  unfold evalScript
  simp only [h1, h2, ↓reduceIte]
  rw [evalLoop_instruction (s := ExecState.init _) (read0 h)]
  simp [evalInstruction, execOpcode, hashTop, countOp, isDisabled, ExecState.fExec, ExecState.init, maxStackItems,
    maxScriptElementSize, maxOpsPerScript, hS1]
  rw [evalLoop_instruction (read1 h hh)]
  simp [evalInstruction, execOpcode, countOp, isDisabled, ExecState.fExec, maxStackItems,
    maxScriptElementSize, maxOpsPerScript, hh, hS2]
  rw [evalLoop_instruction (read22 h hh)]
  simp [evalInstruction, execOpcode, countOp, isDisabled, ExecState.fExec, maxStackItems,
    maxScriptElementSize, maxOpsPerScript, hS1]
  rw [evalLoop_atEnd (by simp [hh])]
  simp

/-- For every checker, supported flag set and script that `isPayToScriptHash` accepts: on an empty stack the script gives `INVALID_STACK_OPERATION`, from its `OP_HASH160`. -/
theorem evalScript_p2shTemplate_nil {c : SignatureChecker} {flags : UInt32} {spk : List UInt8}
    (hf : unsupportedFlagBits flags = 0) (ht : isPayToScriptHash spk = true) :
    evalScript (some c) flags spk [] = .rejected .invalidStackOperation := by
  obtain ⟨h, hh, rfl⟩ := (isPayToScriptHash_iff spk).mp ht
  simp only [List.cons_append, List.nil_append]
  have h1 : ¬unsupportedFlagBits flags ≠ 0 := by simp [hf]
  have h2 : ¬maxScriptSize < (0xa9 :: 0x14 :: (h ++ [0x87]) : List UInt8).length := by simp [hh, maxScriptSize]
  unfold evalScript
  simp only [h1, h2, ↓reduceIte]
  rw [evalLoop_instruction (s := ExecState.init _) (read0 h)]
  simp [evalInstruction, execOpcode, hashTop, countOp, isDisabled, ExecState.fExec, ExecState.init,
    maxScriptElementSize, maxOpsPerScript]

/-! ## `VerifyScript` -/

/-- For every checker, scripts and flag set with a bit outside `supportedFlags`: the result is unsupported, before any evaluation. -/
theorem verifyScript_unsupportedFlags {c : SignatureChecker} {flags : UInt32} {ss spk : List UInt8}
    (h : unsupportedFlagBits flags ≠ 0) :
    verifyScript c flags ss spk = .unsupported (.flags (unsupportedFlagBits flags)) := by
  simp [verifyScript, h]

/-- For every supported flag set and every flag outside `supportedFlags`: the flag is clear. -/
private theorem flagOutside_eq_false {flags flag : UInt32} (hf : unsupportedFlagBits flags = 0)
    (h : flag &&& ~~~supportedFlags = flag) : hasFlag flags flag = false := by
  have : flags &&& flag = (flags &&& ~~~supportedFlags) &&& flag := by
    rw [UInt32.and_assoc, UInt32.and_comm (~~~supportedFlags), h]
  unfold unsupportedFlagBits at hf
  simp [hasFlag, this, hf]

/-- For every supported flag set: `SCRIPT_VERIFY_SIGPUSHONLY` is clear, so the check at D3 lines 1419 to 1421 is unreachable. -/
theorem hasFlag_sigPushOnly_eq_false {flags : UInt32} (hf : unsupportedFlagBits flags = 0) :
    hasFlag flags ScriptFlags.sigPushOnly = false := by
  exact flagOutside_eq_false hf (by decide)

/-- For every supported flag set: `SCRIPT_VERIFY_CLEANSTACK` is clear, so the check at D3 lines 1505 to 1513 is unreachable. -/
theorem hasFlag_cleanStack_eq_false {flags : UInt32} (hf : unsupportedFlagBits flags = 0) :
    hasFlag flags ScriptFlags.cleanStack = false := by
  exact flagOutside_eq_false hf (by decide)

/-- For every supported flag set: `SCRIPT_VERIFY_WITNESS` is clear, so the witness branches of D3 lines 1440 to 1454, 1484 to 1499 and 1515 to 1523 are unreachable. -/
theorem hasFlag_witness_eq_false {flags : UInt32} (hf : unsupportedFlagBits flags = 0) :
    hasFlag flags ScriptFlags.witness = false := by
  exact flagOutside_eq_false hf (by decide)

/--
For every checker, flag set and pair of scripts, when `P2SH` is clear or `scriptPubKey` is not the template:
the result is `scriptSig` on the empty stack, then `scriptPubKey` on its final stack, then the true-top check.
The first evaluation's rejection or unsupported result passes through.
-/
theorem verifyScript_noP2sh {c : SignatureChecker} {flags : UInt32} {ss spk : List UInt8}
    (h : hasFlag flags ScriptFlags.p2sh = false ∨ isPayToScriptHash spk = false) :
    verifyScript c flags ss spk =
      match evalScript (some c) flags ss [] with
      | .ok s => finishEval (evalScript (some c) flags spk s.stack)
      | .rejected e => .rejected e
      | .unsupported u => .unsupported u := by
  have hp : (hasFlag flags ScriptFlags.p2sh && isPayToScriptHash spk) = false := by
    rcases h with h | h <;> simp [h]
  by_cases hf : unsupportedFlagBits flags ≠ 0
  · rw [verifyScript_unsupportedFlags hf, evalScript_unsupportedFlags hf]
  · unfold verifyScript
    simp only [hf, ↓reduceIte]
    cases h1 : evalScript (some c) flags ss [] with
    | ok s =>
      cases h2 : evalScript (some c) flags spk s.stack with
      | ok t => cases ht : trueTop t.stack <;> simp [finishEval, hp, h2, ht]
      | rejected e => simp [finishEval, h2]
      | unsupported u => simp [finishEval, h2]
    | rejected e => rfl
    | unsupported u => rfl

/--
Core's assert at D3 line 1469 holds: for every checker, supported flag set and template `scriptPubKey`, and every state `s`, if `scriptPubKey` succeeds on the stack of `s`, that stack is not empty.
In `verifyScript`, `s` is the final state of `scriptSig`, so the branch for an empty saved stack is unreachable.
-/
theorem verifyScript_p2sh_saved_ne_nil {c : SignatureChecker} {flags : UInt32} {spk : List UInt8}
    {s t : ExecState} (hf : unsupportedFlagBits flags = 0) (ht : isPayToScriptHash spk = true)
    (hpk : evalScript (some c) flags spk s.stack = .ok t) :
    s.stack ≠ [] := by
  intro hnil
  rw [hnil, evalScript_p2shTemplate_nil hf ht] at hpk
  cases hpk

/--
For every checker and supported flag set with `P2SH`, every template `scriptPubKey` and every push-only `scriptSig`:
if `scriptSig` ends with the stack `S ++ [redeem]`, and `scriptPubKey` on that stack succeeds with a true top item, then the result is `redeem` evaluated on `S`, followed by the true-top check (D3, lines 1457 to 1481).
-/
theorem verifyScript_p2sh {c : SignatureChecker} {flags : UInt32} {ss spk redeem : List UInt8}
    {S : List (List UInt8)} {s t : ExecState} (hf : unsupportedFlagBits flags = 0)
    (hp : hasFlag flags ScriptFlags.p2sh = true) (ht : isPayToScriptHash spk = true) (hpush : isPushOnly ss = true)
    (hs : evalScript (some c) flags ss [] = .ok s) (hS : s.stack = S ++ [redeem])
    (hpk : evalScript (some c) flags spk s.stack = .ok t) (htop : trueTop t.stack = true) :
    verifyScript c flags ss spk = finishEval (evalScript (some c) flags redeem S) := by
  rw [hS] at hpk
  simp [verifyScript, hf, hs, hpk, htop, hp, ht, hpush, hS]

/--
For every checker and supported flag set with `P2SH`, and every template `scriptPubKey`:
a `scriptSig` that is not push-only gives `SIG_PUSHONLY` when both evaluations succeed and the top item is true (D3, lines 1460 and 1461).
-/
theorem verifyScript_p2sh_notPushOnly {c : SignatureChecker} {flags : UInt32} {ss spk : List UInt8}
    {s t : ExecState} (hf : unsupportedFlagBits flags = 0) (hp : hasFlag flags ScriptFlags.p2sh = true)
    (ht : isPayToScriptHash spk = true) (hpush : isPushOnly ss = false)
    (hs : evalScript (some c) flags ss [] = .ok s) (hpk : evalScript (some c) flags spk s.stack = .ok t)
    (htop : trueTop t.stack = true) :
    verifyScript c flags ss spk = .rejected .sigPushOnly := by
  simp [verifyScript, hf, hs, hpk, htop, hp, ht, hpush]

/--
For every checker and supported flag set with `P2SH`, 20 bytes `h`, and push-only `scriptSig` that ends with the stack `S ++ [redeem]`, where `S` has at most 998 items:
if the HASH160 digest of `redeem` is `h`, the result for the template of `h` is `redeem` evaluated on `S`, followed by the true-top check.
The hypothesis is about the supplied `redeem` only.
-/
theorem verifyScript_p2sh_hash {c : SignatureChecker} {flags : UInt32} {ss h redeem : List UInt8}
    {S : List (List UInt8)} {s : ExecState} (hf : unsupportedFlagBits flags = 0)
    (hp : hasFlag flags ScriptFlags.p2sh = true) (hh : h.length = 20) (hpush : isPushOnly ss = true)
    (hs : evalScript (some c) flags ss [] = .ok s) (hS : s.stack = S ++ [redeem]) (hlen : S.length + 2 ≤ 1000)
    (hhash : (Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList = h) :
    verifyScript c flags ss ([0xa9, 0x14] ++ h ++ [0x87]) = finishEval (evalScript (some c) flags redeem S) := by
  have ht : isPayToScriptHash ([0xa9, 0x14] ++ h ++ [0x87]) = true := (isPayToScriptHash_iff _).mpr ⟨h, hh, rfl⟩
  have hpk := evalScript_p2shTemplate (c := c) (x := redeem) hf hh hlen
  rw [← hS] at hpk
  refine verifyScript_p2sh hf hp ht hpush hs hS hpk ?_
  simp [trueTop, hhash, boolBytes, castToBool, castToBoolLoop]

/--
For every checker and supported flag set with `P2SH`, 20 bytes `h`, and `scriptSig` that ends with the stack `S ++ [redeem]`, where `S` has at most 998 items:
if the HASH160 digest of `redeem` is not `h`, the result for the template of `h` is `EVAL_FALSE` (D3, lines 1434 and 1435).
-/
theorem verifyScript_p2sh_hash_ne {c : SignatureChecker} {flags : UInt32} {ss h redeem : List UInt8}
    {S : List (List UInt8)} {s : ExecState} (hf : unsupportedFlagBits flags = 0) (hh : h.length = 20)
    (hs : evalScript (some c) flags ss [] = .ok s) (hS : s.stack = S ++ [redeem]) (hlen : S.length + 2 ≤ 1000)
    (hhash : (Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList ≠ h) :
    verifyScript c flags ss ([0xa9, 0x14] ++ h ++ [0x87]) = .rejected .evalFalse := by
  have hpk := evalScript_p2shTemplate (c := c) (x := redeem) hf hh hlen
  rw [← hS] at hpk
  have hb : ((Cryptography.Hash.hash160 ⟨redeem.toArray⟩).toList == h) = false := by simpa using hhash
  simp only [List.cons_append, List.nil_append] at hpk ⊢
  simp [verifyScript, hf, hs, hpk, trueTop, hb, boolBytes, castToBool, castToBoolLoop]

/-! ## The lock-time opcodes over a transaction -/

/-- The input that an `InputContext` selects is the list entry at its index. -/
theorem InputContext.getElem?_index (ctx : InputContext) : ctx.tx.inputs.val[ctx.index.toNat]? = some ctx.input := by
  simp [InputContext.input, ctx.index_lt]

/--
For every input context, verifier, flag set with `CHECKLOCKTIMEVERIFY`, and state whose top item decodes in five bytes to `n ≥ 0`:
with `transactionChecker`, `OP_CHECKLOCKTIMEVERIFY` leaves the state unchanged exactly when `n` and the transaction's lock time lie on the same side of 500,000,000, `n` is at most the lock time, and the input's sequence is not `0xffffffff`.
Otherwise it gives `UNSATISFIED_LOCKTIME` (D3, lines 386 and 387 and 1274 to 1308).
-/
theorem execOpcode_cltv_transaction {ctx : InputContext} {verify : SignatureVerifier} {script : List UInt8}
    {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {top : List UInt8} {n : Int}
    (hf : hasFlag flags ScriptFlags.checkLockTimeVerify = true) (hs : s.stack = rest ++ [top])
    (hd : ScriptNum.decode top false lockTimeNumSize = .ok n) (hn : 0 ≤ n) :
    execOpcode (some (transactionChecker ctx.tx ctx.index verify)) script flags fExec s 0xb1 pushed next =
      if ((ctx.tx.lockTime.toNat < 500000000 ∧ n < 500000000) ∨
            (500000000 ≤ ctx.tx.lockTime.toNat ∧ 500000000 ≤ n)) ∧
          n ≤ ctx.tx.lockTime.toNat ∧ ctx.input.sequence ≠ 0xffffffff
      then .next s else .rejected .unsatisfiedLocktime := by
  rw [execOpcode_cltv_checked hf hs hd hn, transactionChecker_checkLockTime verify ctx.getElem?_index]
  simp only [← lockTimeSatisfied_iff]
  cases lockTimeSatisfied ctx.tx.lockTime ctx.input.sequence n <;> simp

/--
For every input context, verifier, flag set with `CHECKSEQUENCEVERIFY`, and state whose top item decodes in five bytes to `n ≥ 0` with bit 31 clear, with `m v = v &&& 0x40ffff`:
with `transactionChecker`, `OP_CHECKSEQUENCEVERIFY` leaves the state unchanged exactly when the version, read as `uint32_t`, is at least 2, bit 31 of the input's sequence is clear, `m n` and `m sequence` are both below `0x400000` or both at least `0x400000`, and `m n ≤ m sequence`.
Otherwise it gives `UNSATISFIED_LOCKTIME` (D3, lines 422 and 423 and 1310 to 1353).
-/
theorem execOpcode_csv_transaction {ctx : InputContext} {verify : SignatureVerifier} {script : List UInt8}
    {flags : UInt32} {fExec : Bool} {s : ExecState} {pushed : List UInt8} {next : Nat}
    {rest : List (List UInt8)} {top : List UInt8} {n : Int}
    (hf : hasFlag flags ScriptFlags.checkSequenceVerify = true) (hs : s.stack = rest ++ [top])
    (hd : ScriptNum.decode top false lockTimeNumSize = .ok n) (hn : 0 ≤ n)
    (hb : n.toNat &&& 0x80000000 = 0) :
    execOpcode (some (transactionChecker ctx.tx ctx.index verify)) script flags fExec s 0xb2 pushed next =
      if 2 ≤ ctx.tx.version.toNat ∧ ctx.input.sequence.toNat &&& 0x80000000 = 0 ∧
          ((ctx.input.sequence.toNat &&& 0x40ffff < 0x400000 ∧ n.toNat &&& 0x40ffff < 0x400000) ∨
            (0x400000 ≤ ctx.input.sequence.toNat &&& 0x40ffff ∧ 0x400000 ≤ n.toNat &&& 0x40ffff)) ∧
          n.toNat &&& 0x40ffff ≤ ctx.input.sequence.toNat &&& 0x40ffff
      then .next s else .rejected .unsatisfiedLocktime := by
  rw [execOpcode_csv_checked hf hs hd hn hb, transactionChecker_checkSequence verify ctx.getElem?_index]
  simp only [← sequenceSatisfied_iff]
  cases sequenceSatisfied ctx.tx.version ctx.input.sequence n <;> simp

/-! ## The spend predicate -/

/-- For every input context, previous-output script, flag set and verifier: `verifyLegacySpend` is `verifyScript` with `transactionChecker` for the input, on its exact `scriptSig`. -/
theorem verifyLegacySpend_eq (ctx : InputContext) (prevScriptPubKey : Transaction.Script) (flags : UInt32)
    (verify : SignatureVerifier) :
    verifyLegacySpend ctx prevScriptPubKey flags verify =
      verifyScript (transactionChecker ctx.tx ctx.index verify) flags ctx.input.scriptSig.bytes.val
        prevScriptPubKey.bytes.val := rfl

/--
The input context of input `index` of a transaction `tx` that `decodeBaseComplete` read from `bs`.
The caller supplies an index below the number of inputs.
The reader gives the bounds on the numbers of inputs and outputs: a successful read has at most `MAX_SIZE` of each (`Transaction.readBase_eq_ok_iff`).
-/
def InputContext.ofDecoded {bs : List UInt8} {tx : Transaction} (hRead : Transaction.decodeBaseComplete bs = .ok tx)
    (index : UInt32) (hIndex : index.toNat < tx.inputs.val.length) : InputContext :=
  have hb : tx.WithinMaxSize :=
    ((Transaction.readBase_eq_ok_iff bs tx []).mp ((Transaction.decodeBaseComplete_eq_ok_iff bs tx).mp hRead)).2
  ⟨tx, index, hIndex, hb.inputs_lt, hb.outputs_lt⟩

/-- The transaction of `InputContext.ofDecoded` is the transaction that the reader returned. -/
theorem InputContext.ofDecoded_tx {bs : List UInt8} {tx : Transaction}
    (hRead : Transaction.decodeBaseComplete bs = .ok tx) (index : UInt32) (hIndex : index.toNat < tx.inputs.val.length) :
    (InputContext.ofDecoded hRead index hIndex).tx = tx := rfl

/-- The index of `InputContext.ofDecoded` is the supplied index. -/
theorem InputContext.ofDecoded_index {bs : List UInt8} {tx : Transaction}
    (hRead : Transaction.decodeBaseComplete bs = .ok tx) (index : UInt32) (hIndex : index.toNat < tx.inputs.val.length) :
    (InputContext.ofDecoded hRead index hIndex).index = index := rfl

/--
Take a transaction that `decodeBaseComplete` read and an index below its number of inputs.
The spend predicate on `InputContext.ofDecoded` is `verifyScript` with `transactionChecker` for that index.
It runs on the input's `scriptSig` and the previous-output script.
-/
theorem verifyLegacySpend_ofDecoded {bs : List UInt8} {tx : Transaction}
    (hRead : Transaction.decodeBaseComplete bs = .ok tx) (index : UInt32) (hIndex : index.toNat < tx.inputs.val.length)
    (prevScriptPubKey : Transaction.Script) (flags : UInt32) (verify : SignatureVerifier) :
    verifyLegacySpend (InputContext.ofDecoded hRead index hIndex) prevScriptPubKey flags verify =
      verifyScript (transactionChecker tx index verify) flags (tx.inputs.val[index.toNat]'hIndex).scriptSig.bytes.val
        prevScriptPubKey.bytes.val := rfl

end DogeLib.Script
