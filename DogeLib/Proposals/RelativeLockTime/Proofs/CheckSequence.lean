module

public import DogeLib.Proposals.Framework.Proofs.Script
public import DogeLib.Proposals.Framework.Proofs.Compatibility
public import DogeLib.Proposals.RelativeLockTime

/-!
# Proofs: `Proposals.RelativeLockTime`, the opcode of BIP 112 in one spend

The Script-local theorems of design record 0012, section 9.2, for `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY`.
Each is about one input and its scripts. None is a claim about a block, a chain or the network.
Every theorem holds for every signature checker or verifier, and none assumes a property of it.

`withCsvFlag f` is the flag set `f` with the CSV flag added.

## The flag

- `hasFlag_withCsvFlag`, `hasFlag_withCsvFlag_csv`, `unsupportedFlagBits_withCsvFlag`: the added flag changes no other flag and no unsupported bit.
- `withCsvFlag_and_not_notMandatory`, `withCsvFlag_and_notMandatory`: the flag is in `standardNotMandatoryVerifyFlags`, so the second script check of a block removes it.

## Restriction

- `execOpcode_withCsvFlag_of_ne`, `evalInstruction_withCsvFlag_of_ne`: the flag changes no instruction other than `0xb2`.
- `csvFlagStep_restricts`: the baseline step with `withCsvFlag f` restricts the baseline step with `f`.
- `csvFlag_verifyScript_soft_fork_local`, `csvFlag_soft_fork_local`: if `verifyScript` or `verifyLegacySpend` accepts with `withCsvFlag f`, it accepts with `f`.

## Characterization

Design record 0012, section 9.2, leaves the exact domain of `csv_accepted_iff` to stage 2. The domain is:

- `scriptPubKey` is `operandScript b S`: the push `L b₁ … b_L` of the operand bytes `b`, then `0xb2`, then the script `S`.
  The push byte `L` is the length of `b`: `OP_0` for the empty operand, and a direct push otherwise.
- The operand has at most 5 bytes. It decodes as Core's `CScriptNum(…, false, 5)` does: `n = ScriptNum.value b`, without the minimal requirement.
  The domain excludes `OP_1NEGATE`, `OP_1` to `OP_16` and the `OP_PUSHDATA` forms as the operand push.
  It also excludes an operand of more than five bytes, whose decode fails with `UNKNOWN_ERROR`.
- `S` has no instruction `0xb2`, read from its start, and neither has `scriptSig`.
  So the only `0xb2` that the evaluation reads is the second instruction of `scriptPubKey`, at the top level.
- The flag set `f` has the CSV flag clear. It is otherwise arbitrary, and so is the checker.

`scriptPubKey` starts with a byte from 0 to 5, so it is never the P2SH template, and no redeem script runs.
The domain has no P2SH case: a redeem script of the form `operandScript b S` is outside it.

- `csv_verifyScript_accepted_iff`: in that domain, `verifyScript` accepts with `withCsvFlag f` exactly when it accepts with `f`, `0 ≤ n`, and bit 31 of `n` is set or the checker's `checkSequence n` holds.
- `csv_accepted_iff`: the same for `verifyLegacySpend`, where the last condition is `sequenceSatisfied version sequence n` for the version of the transaction and the sequence of the input.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Proposals.Framework

variable {ε ε₀ υ υ₀ : Type}

/-! ## The flag -/

/-- For all 32-bit values: `(f ||| c) &&& g` is `(f &&& g) ||| (c &&& g)`. -/
theorem or_and_distrib (f c g : UInt32) : (f ||| c) &&& g = (f &&& g) ||| (c &&& g) := by
  rw [← UInt32.toBitVec_inj]
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or]
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, Bool.and_or_distrib_right]

/-- For every flag set `f` and every flag `g` whose bits exclude the CSV flag: `withCsvFlag f` has `g` exactly when `f` has it. -/
theorem hasFlag_withCsvFlag (f : UInt32) {g : UInt32} (hg : ScriptFlags.checkSequenceVerify &&& g = 0) :
    hasFlag (withCsvFlag f) g = hasFlag f g := by
  simp only [hasFlag, withCsvFlag, or_and_distrib, hg, UInt32.or_zero]

/-- For every flag set `f`: `withCsvFlag f` has the CSV flag. -/
theorem hasFlag_withCsvFlag_csv (f : UInt32) : hasFlag (withCsvFlag f) ScriptFlags.checkSequenceVerify = true := by
  simp only [hasFlag, withCsvFlag, or_and_distrib, UInt32.and_self, bne_iff_ne, ne_eq, UInt32.or_eq_zero_iff, not_and]
  intro _
  decide

/-- For every flag set `f`: `withCsvFlag f` has the unsupported bits of `f`. The CSV flag is in `supportedFlags`. -/
theorem unsupportedFlagBits_withCsvFlag (f : UInt32) : unsupportedFlagBits (withCsvFlag f) = unsupportedFlagBits f := by
  simp only [unsupportedFlagBits, withCsvFlag, or_and_distrib]
  rw [show ScriptFlags.checkSequenceVerify &&& ~~~supportedFlags = 0 by decide, UInt32.or_zero]

/-- For every flag set `f`: without the flags that are not mandatory, `withCsvFlag f` is `f` without them. -/
theorem withCsvFlag_and_not_notMandatory (f : UInt32) :
    withCsvFlag f &&& ~~~standardNotMandatoryVerifyFlags = f &&& ~~~standardNotMandatoryVerifyFlags := by
  rw [withCsvFlag, or_and_distrib,
    show ScriptFlags.checkSequenceVerify &&& ~~~standardNotMandatoryVerifyFlags = 0 by decide, UInt32.or_zero]

/-- For every flag set `f`: `withCsvFlag f` has a flag that is not mandatory, the CSV flag. -/
theorem withCsvFlag_and_notMandatory (f : UInt32) :
    (withCsvFlag f &&& standardNotMandatoryVerifyFlags != 0) = true := by
  rw [withCsvFlag, or_and_distrib,
    show ScriptFlags.checkSequenceVerify &&& standardNotMandatoryVerifyFlags = ScriptFlags.checkSequenceVerify by
      decide]
  simp only [bne_iff_ne, ne_eq, UInt32.or_eq_zero_iff, not_and]
  intro _
  decide

/-- A flag set with no flag that is not mandatory is unchanged when those flags are removed. -/
theorem and_not_notMandatory_of_none {f : UInt32} (h : (f &&& standardNotMandatoryVerifyFlags != 0) = false) :
    f &&& ~~~standardNotMandatoryVerifyFlags = f := by
  have h0 : f &&& standardNotMandatoryVerifyFlags = 0 := by simpa using h
  rw [← UInt32.toBitVec_inj] at h0 ⊢
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_not] at h0 ⊢
  ext i hi
  have := congrArg (fun v => v[i]) h0
  simp only [BitVec.getElem_and] at this
  simp only [BitVec.getElem_and, BitVec.getElem_not]
  cases hf : f.toBitVec[i] <;> simp_all

/-! ## One instruction -/

/--
For every checker, script, flag set `f`, branch flag, state, pushed bytes and next cursor, and every opcode other than `0xb2`:
`execOpcode` gives the same result with `withCsvFlag f` and with `f`.
-/
theorem execOpcode_withCsvFlag_of_ne {checker : Option SignatureChecker} {script : List UInt8} (f : UInt32)
    (fExec : Bool) (s : ExecState) {op : UInt8} (hop : op ≠ 0xb2) (pushed : List UInt8) (next : Nat) :
    execOpcode checker script (withCsvFlag f) fExec s op pushed next =
      execOpcode checker script f fExec s op pushed next := by
  have he := hasFlag_withCsvFlag f (g := ScriptFlags.strictEnc) (by decide)
  have hd := hasFlag_withCsvFlag f (g := ScriptFlags.derSig) (by decide)
  have hl := hasFlag_withCsvFlag f (g := ScriptFlags.lowS) (by decide)
  have hn := hasFlag_withCsvFlag f (g := ScriptFlags.nullDummy) (by decide)
  have ht := hasFlag_withCsvFlag f (g := ScriptFlags.checkLockTimeVerify) (by decide)
  have hs : ∀ sig, checkSignatureEncoding sig (withCsvFlag f) = checkSignatureEncoding sig f :=
    fun sig => checkSignatureEncoding_flags_congr sig hd hl he
  have hk : ∀ key, checkPubKeyEncoding key (withCsvFlag f) = checkPubKeyEncoding key f :=
    fun key => checkPubKeyEncoding_flags_congr key he
  have hsig : ∀ c s op, checkSigStep c script (withCsvFlag f) s op = checkSigStep c script f s op := by
    intro c s op
    unfold checkSigStep
    split
    · rw [hs, hk]
    · rfl
  have hcheck : ∀ c code op, multisigCheck c (withCsvFlag f) code op = multisigCheck c f code op := by
    intro c code op
    funext sig key
    simp only [multisigCheck, hs, hk]
  have hmul : ∀ c s op, checkMultisigStep c script (withCsvFlag f) s op = checkMultisigStep c script f s op := by
    intro c s op
    simp only [checkMultisigStep, hcheck, hn]
  simp only [execOpcode, hsig, hmul, ht]
  split
  · rfl
  · split
    · rfl
    · split <;> first | rfl | exact absurd rfl hop

/--
For every checker, script, flag set `f`, state and instruction whose opcode is not `0xb2`:
the step gives the same result with `withCsvFlag f` and with `f`.
-/
theorem evalInstruction_withCsvFlag_of_ne {checker : Option SignatureChecker} {script : List UInt8} (f : UInt32)
    (s : ExecState) {i : Instruction} (hop : i.opcode ≠ 0xb2) :
    evalInstruction checker script (withCsvFlag f) s i = evalInstruction checker script f s i := by
  simp only [evalInstruction, execOpcode_withCsvFlag_of_ne f _ _ hop]

/--
For every checker, script, flag set `f`, branch flag, state, opcode, pushed bytes and next cursor:
if `execOpcode` succeeds with `withCsvFlag f`, it succeeds with `f`, with the same state.
For `0xb2`, a successful `OP_CHECKSEQUENCEVERIFY` leaves the state unchanged, as `OP_NOP3` does.
-/
theorem execOpcode_withCsvFlag_next {checker : Option SignatureChecker} {script : List UInt8} {f : UInt32}
    {fExec : Bool} {s t : ExecState} {op : UInt8} {pushed : List UInt8} {next : Nat}
    (h : execOpcode checker script (withCsvFlag f) fExec s op pushed next = .next t) :
    execOpcode checker script f fExec s op pushed next = .next t := by
  by_cases hop : op = 0xb2
  · subst hop
    cases hf : hasFlag f ScriptFlags.checkSequenceVerify with
    | true =>
      rw [← h]
      exact (execOpcode_flags_congr (fun flag hmem => by
        simp only [evalFlags, List.mem_cons, List.mem_nil_iff, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hasFlag_withCsvFlag f (by decide)
        · exact hasFlag_withCsvFlag f (by decide)
        · exact hasFlag_withCsvFlag f (by decide)
        · exact hasFlag_withCsvFlag f (by decide)
        · exact hasFlag_withCsvFlag f (by decide)
        · rw [hasFlag_withCsvFlag_csv, hf]) _ _ _ _ _).symm
    | false =>
      rw [execOpcode_nop3 hf]
      cases checker with
      | none => rw [execOpcode_csv (hasFlag_withCsvFlag_csv f)] at h; cases h
      | some c =>
        have h' : checkSequenceStep c s = .next t := by
          simpa [execOpcode, hasFlag_withCsvFlag_csv] using h
        rw [checkSequenceStep_next h']
  · rw [← execOpcode_withCsvFlag_of_ne f _ _ hop]
    exact h

/--
For every checker, script, flag set `f`, state and instruction:
if the step succeeds with `withCsvFlag f`, it succeeds with `f`, with the same state.
-/
theorem evalInstruction_withCsvFlag_next {checker : Option SignatureChecker} {script : List UInt8} {f : UInt32}
    {s t : ExecState} {i : Instruction} (h : evalInstruction checker script (withCsvFlag f) s i = .next t) :
    evalInstruction checker script f s i = .next t := by
  simp only [evalInstruction] at h ⊢
  by_cases h1 : maxScriptElementSize < i.pushed.length
  · simp [h1] at h
  by_cases h2 : maxOpsPerScript < countOp i.opcode s.opCount
  · simp [h1, h2] at h
  by_cases h3 : isDisabled i.opcode = true
  · simp [h1, h2, h3] at h
  simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true] at h ⊢
  generalize ({ s with opCount := countOp i.opcode s.opCount } : ExecState) = s' at h ⊢
  by_cases hx : (s'.fExec || decide (99 ≤ i.opcode) && decide (i.opcode ≤ 104)) = true
  · simp only [hx, ↓reduceIte] at h ⊢
    cases hE : execOpcode checker script (withCsvFlag f) s'.fExec s' i.opcode i.pushed i.next with
    | next u =>
      rw [hE] at h
      rw [execOpcode_withCsvFlag_next hE]
      exact h
    | rejected e => rw [hE] at h; cases h
    | unsupported u => rw [hE] at h; cases h
  · simp only [hx] at h ⊢
    exact h

/-! ## Restriction -/

/--
The target `csvFlagStep_restricts` of design record 0012, section 9.2.
For every checker and flag set `f`, the baseline step with `f` and the CSV flag restricts the baseline step with `f` (`Restricts`).
A successful step with the flag is a successful step without it, with the same state.
For all error maps and maps of unsupported reasons.
-/
theorem csvFlagStep_restricts (embed₁ : ScriptError → ε) (embedU₁ : Unsupported → υ) (embed₀ : ScriptError → ε₀)
    (embedU₀ : Unsupported → υ₀) (checker : Option SignatureChecker) (f : UInt32) :
    Restricts (baselineStep embed₁ embedU₁ checker (withCsvFlag f)) (baselineStep embed₀ embedU₀ checker f) := by
  intro script s i t h
  unfold baselineStep at h ⊢
  cases hE : evalInstruction checker script (withCsvFlag f) s i with
  | next u =>
    rw [hE] at h
    simp only [StepOutcome.ofBaseline, StepOutcome.next.injEq] at h
    subst h
    rw [evalInstruction_withCsvFlag_next hE]
    rfl
  | rejected e => rw [hE] at h; cases h
  | unsupported u => rw [hE] at h; cases h

/--
For every checker `c`, flag set `f`, `scriptSig` and `scriptPubKey`:
if `verifyScript` accepts with `f` and the CSV flag, it accepts with `f`.
The P2SH evaluation is included. Script-local.
-/
theorem csvFlag_verifyScript_soft_fork_local {c : SignatureChecker} {f : UInt32} {scriptSig scriptPubKey : List UInt8}
    (h : verifyScript c (withCsvFlag f) scriptSig scriptPubKey = .accepted) :
    verifyScript c f scriptSig scriptPubKey = .accepted := by
  have h1 : verifyScriptWith (ε := ScriptError) (υ := Unsupported) id id
      (baselineStep id id (some c) (withCsvFlag f)) (withCsvFlag f) scriptSig scriptPubKey = .accepted := by
    rw [verifyScriptWith_baseline, h]
    rfl
  rw [verifyScriptWith_flags_congr _ (unsupportedFlagBits_withCsvFlag f) (hasFlag_withCsvFlag f (by decide))] at h1
  exact verifyScript_of_restricts (ε₀ := ScriptError) (υ₀ := Unsupported) id id
    (csvFlagStep_restricts id id id id (some c) f) scriptSig scriptPubKey h1

/--
The target `csvFlag_soft_fork_local` of design record 0012, section 9.2. Script-local.
If `verifyLegacySpend` accepts an input with `f` and the CSV flag, it accepts the input with `f`.
For every input context, previous `scriptPubKey`, flag set `f` and verifier.
The statement also holds for a flag set outside `supportedFlags`, where neither call accepts.
-/
theorem csvFlag_soft_fork_local {ctx : InputContext} {prevScriptPubKey : Transaction.Script} {f : UInt32}
    {verify : SignatureVerifier} (h : verifyLegacySpend ctx prevScriptPubKey (withCsvFlag f) verify = .accepted) :
    verifyLegacySpend ctx prevScriptPubKey f verify = .accepted :=
  csvFlag_verifyScript_soft_fork_local h

/-! ## Reading the operand script -/

/-- Let `b` have at most 75 bytes. For every `S`, the first instruction of `operandScript b S` pushes `b`, and the next cursor is `b.length + 1`. -/
theorem readInstruction_operandScript_zero {b S : List UInt8} (hb : b.length < 0x4c) :
    readInstruction (operandScript b S) 0 =
      .instruction ⟨b.length.toUInt8, b.length.toUInt8 :: b, b, b.length + 1⟩ := by
  have hnat : b.length.toUInt8.toNat = b.length := ScriptNum.toUInt8_toNat_of_lt (by omega)
  have hop : b.length.toUInt8 < 0x4c := by
    rw [UInt8.lt_iff_toNat_lt, hnat]; exact hb
  have hw : lengthFieldWidth b.length.toUInt8 = 0 := by
    have h1 : b.length.toUInt8 ≠ 0x4c := fun h => by rw [h] at hop; exact absurd hop (by decide)
    have h2 : b.length.toUInt8 ≠ 0x4d := fun h => by rw [h] at hop; exact absurd hop (by decide)
    have h3 : b.length.toUInt8 ≠ 0x4e := fun h => by rw [h] at hop; exact absurd hop (by decide)
    simp [lengthFieldWidth, h1, h2, h3]
  simp only [readInstruction, operandScript, List.drop_zero, List.cons_append, readOp, hop, ↓reduceIte,
    readPush, hnat, List.length_append, List.length_cons]
  have hlt : ¬(b.length + (S.length + 1) < b.length) := by omega
  simp only [hlt, ↓reduceIte]
  simp only [Nat.toUInt8] at hw
  simp [hw]

/-- For every `b` and `S`, the instruction at `b.length + 1` of `operandScript b S` is `0xb2`, and the next cursor is `b.length + 2`. -/
theorem readInstruction_operandScript_csv (b S : List UInt8) :
    readInstruction (operandScript b S) (b.length + 1) =
      .instruction ⟨csvOpcode, [csvOpcode], [], b.length + 2⟩ := by
  have h : (operandScript b S).drop (b.length + 1) = csvOpcode :: S := by
    simp [operandScript]
  simp only [readInstruction, h, readOp, csvOpcode]
  simp [lengthFieldWidth]

/-- Facts about the push opcode of an operand of at most five bytes. -/
private theorem lengthByte_facts {n : Nat} (hn : n ≤ 5) :
    n.toUInt8 ≤ 0x4e ∧ (∀ k, countOp n.toUInt8 k = k) ∧ isDisabled n.toUInt8 = false ∧ n.toUInt8 ≠ 0xa9 := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with h | h | h | h | h | h <;>
    subst h <;> refine ⟨by decide, fun k => by simp [countOp], by decide, by decide⟩

/--
Let `b` have at most five bytes. This holds for every checker, flag set and stack `stk`.
The push of `b` at the start of `operandScript b S` gives `STACK_SIZE` above 1,000 items, and otherwise pushes `b`.
-/
private theorem evalInstruction_operand {checker : Option SignatureChecker} {flags : UInt32} {b S : List UInt8}
    (hb : b.length ≤ 5) (stk : List (List UInt8)) :
    evalInstruction checker (operandScript b S) flags (ExecState.init stk)
        ⟨b.length.toUInt8, b.length.toUInt8 :: b, b, b.length + 1⟩ =
      if maxStackItems < stk.length + 1 then .rejected .stackSize
      else .next { ExecState.init stk with stack := stk ++ [b] } := by
  obtain ⟨hpush, hcount, hdis, -⟩ := lengthByte_facts hb
  rw [evalInstruction_exec (by rfl) (by simp [maxScriptElementSize]; omega)
    (by simp [hcount, ExecState.init, maxOpsPerScript]) hdis]
  simp only [hcount, execOpcode_push hpush]
  simp [ExecState.init]

/--
Opcode `0xb2` without the CSV flag, in a state whose branch executes, with opcode count 0 and at most 1,000 stack items.
The step only counts the opcode, for every checker, script and cursor `n`.
-/
private theorem evalInstruction_nop3 {checker : Option SignatureChecker} {flags : UInt32} {script : List UInt8}
    {s : ExecState} (hf : hasFlag flags ScriptFlags.checkSequenceVerify = false) (n : Nat) (hx : s.fExec = true)
    (hc : s.opCount = 0) (hl : s.stack.length + s.altstack.length ≤ maxStackItems) :
    evalInstruction checker script flags s ⟨csvOpcode, [csvOpcode], [], n⟩ = .next { s with opCount := 1 } := by
  have hcount : countOp 0xb2 s.opCount = 1 := by simp [countOp, hc]
  simp only [csvOpcode]
  rw [evalInstruction_exec hx (by simp [maxScriptElementSize]) (by simp [hcount, maxOpsPerScript])
    (show isDisabled 0xb2 = false by decide)]
  simp only [hcount, execOpcode_nop3 hf]
  simp [Nat.not_lt.mpr hl]

/--
Opcode `0xb2` with the CSV flag and the checker `c`, in a state whose branch executes, with opcode count 0 and at most 1,000 stack items.
The top item `b` has at most five bytes, and `n = ScriptNum.value b`.
The step follows `OP_CHECKSEQUENCEVERIFY` (SOURCES.md, D3, lines 402 to 427): `NEGATIVE_LOCKTIME` for `n < 0`, a NOP for bit 31 of `n`, and the checker otherwise.
-/
private theorem evalInstruction_csv {c : SignatureChecker} {flags : UInt32} {script : List UInt8} {s : ExecState}
    {rest : List (List UInt8)} {b : List UInt8} (hf : hasFlag flags ScriptFlags.checkSequenceVerify = true) (n : Nat)
    (hx : s.fExec = true) (hc : s.opCount = 0) (hs : s.stack = rest ++ [b]) (hb₅ : b.length ≤ 5)
    (hl : s.stack.length + s.altstack.length ≤ maxStackItems) :
    evalInstruction (some c) script flags s ⟨csvOpcode, [csvOpcode], [], n⟩ =
      if ScriptNum.value b < 0 then .rejected .negativeLocktime
      else if (ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0 then .next { s with opCount := 1 }
      else match c.checkSequence (ScriptNum.value b) with
        | none => .unsupported .checkSequenceVerify
        | some true => .next { s with opCount := 1 }
        | some false => .rejected .unsatisfiedLocktime := by
  have hcount : countOp 0xb2 s.opCount = 1 := by simp [countOp, hc]
  have hdec : ScriptNum.decode b false lockTimeNumSize = .ok (ScriptNum.value b) := by
    simp [ScriptNum.decode, lockTimeNumSize, Nat.not_lt.mpr hb₅]
  have hs' : ({ s with opCount := 1 } : ExecState).stack = rest ++ [b] := hs
  simp only [csvOpcode]
  rw [evalInstruction_exec hx (by simp [maxScriptElementSize]) (by simp [hcount, maxOpsPerScript])
    (show isDisabled 0xb2 = false by decide)]
  simp only [hcount]
  by_cases hneg : ScriptNum.value b < 0
  · rw [execOpcode_csv_negative hf hs' hdec hneg]
    simp [hneg]
  · by_cases hbit : (ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0
    · rw [execOpcode_csv_disabled hf hs' hdec (by omega) hbit]
      simp [hneg, hbit, Nat.not_lt.mpr hl]
    · rw [execOpcode_csv_checked hf hs' hdec (by omega) (by simpa using hbit)]
      simp only [hneg, hbit, ↓reduceIte]
      rcases c.checkSequence (ScriptNum.value b) with _ | _ | _ <;> simp [Nat.not_lt.mpr hl]

/-! ## One evaluation of the operand script -/

/-- The baseline steps with `withCsvFlag f` and with `f` agree on every instruction whose opcode is not `0xb2`. -/
theorem baselineStep_withCsvFlag_of_ne (embed : ScriptError → ε) (embedU : Unsupported → υ)
    (checker : Option SignatureChecker) (f : UInt32) (script : List UInt8) (s : ExecState) (i : Instruction)
    (hop : isCsvOpcode i.opcode = false) :
    baselineStep embed embedU checker (withCsvFlag f) script s i = baselineStep embed embedU checker f script s i := by
  have hne : i.opcode ≠ 0xb2 := by
    intro h
    simp [isCsvOpcode, csvOpcode, h] at hop
  simp only [baselineStep, evalInstruction_withCsvFlag_of_ne f s hne]

/--
The evaluation of `operandScript b S`, for an operand of at most 5 bytes, an `S` without `0xb2` and a flag set `f` with the CSV flag clear.
The loop with `withCsvFlag f` succeeds with `t` exactly when the loop with `f` succeeds with `t`, `0 ≤ n`, and bit 31 of `n` is set or `c.checkSequence n` holds.
-/
private theorem evalScriptWith_operand_iff {c : SignatureChecker} {f : UInt32}
    (hf : hasFlag f ScriptFlags.checkSequenceVerify = false) {b S : List UInt8} (hb₅ : b.length ≤ 5)
    (hS : opcodeFree isCsvOpcode S = true) (stk : List (List UInt8)) (t : ExecState) :
    evalScriptWith (ε := ScriptError) (υ := Unsupported) id id (baselineStep id id (some c) (withCsvFlag f)) f
        (operandScript b S) stk = .ok t ↔
      evalScriptWith (ε := ScriptError) (υ := Unsupported) id id (baselineStep id id (some c) f) f
          (operandScript b S) stk = .ok t ∧
        0 ≤ ScriptNum.value b ∧ ((ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0 ∨
          c.checkSequence (ScriptNum.value b) = some true) := by
  have hb : b.length < 0x4c := by omega
  unfold evalScriptWith
  by_cases hfl : unsupportedFlagBits f ≠ 0
  · simp [hfl]
  simp only [hfl, ↓reduceIte]
  by_cases hz : Script.maxScriptSize < (operandScript b S).length
  · simp [hz]
  simp only [hz, ↓reduceIte]
  have h0 : readInstruction (operandScript b S) (ExecState.init stk).pc = _ :=
    readInstruction_operandScript_zero (S := S) hb
  rw [evalLoopWith_instruction h0, evalLoopWith_instruction h0]
  simp only [baselineStep, evalInstruction_operand hb₅]
  by_cases hl : maxStackItems < stk.length + 1
  · simp [hl, StepOutcome.ofBaseline]
  simp only [hl, ↓reduceIte, StepOutcome.ofBaseline]
  -- The state before `0xb2`.
  have h1 : readInstruction (operandScript b S)
      ({ ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 } : ExecState).pc = _ :=
    readInstruction_operandScript_csv b S
  rw [evalLoopWith_instruction h1, evalLoopWith_instruction h1]
  have hlen : ({ ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 } : ExecState).stack.length +
      ({ ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 } : ExecState).altstack.length ≤
        maxStackItems := by
    simp [ExecState.init]; omega
  have hnop := evalInstruction_nop3 (checker := some c) (script := operandScript b S)
    (s := { ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 }) hf (b.length + 2) rfl rfl hlen
  have hcsv := evalInstruction_csv (c := c) (script := operandScript b S)
    (s := { ExecState.init stk with stack := stk ++ [b], pc := b.length + 1 }) (rest := stk) (b := b)
    (hasFlag_withCsvFlag_csv f) (b.length + 2) rfl rfl rfl hb₅ hlen
  simp only [baselineStep, hnop, hcsv, StepOutcome.ofBaseline]
  -- The rest of the script has no `0xb2`.
  have hfree : opcodeFreeFrom isCsvOpcode (operandScript b S) (b.length + 2) = true := by
    have he : operandScript b S = (b.length.toUInt8 :: b ++ [csvOpcode]) ++ S := by simp [operandScript]
    have hlen : (b.length.toUInt8 :: b ++ [csvOpcode]).length + 0 = b.length + 2 := by simp
    rw [he, ← hlen, opcodeFreeFrom_append]
    exact hS
  have hcongr := evalLoopWith_congr (embed := (id : ScriptError → ScriptError))
    (step₁ := baselineStep (υ := Unsupported) id id (some c) (withCsvFlag f))
    (step₂ := baselineStep id id (some c) f)
    (fun s i hi => baselineStep_withCsvFlag_of_ne id id (some c) f (operandScript b S) s i hi)
    { ExecState.init stk with stack := stk ++ [b], opCount := 1, pc := b.length + 2 } hfree
  by_cases hneg : ScriptNum.value b < 0
  · simp [hneg]; omega
  · rw [ite_eq_right hneg]
    by_cases hbit : (ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0
    · rw [ite_eq_left hbit]
      simp only
      rw [hcongr]
      constructor
      · intro h; exact ⟨h, by omega, .inl hbit⟩
      · intro h; exact h.1
    · rw [ite_eq_right hbit]
      rcases hcs : c.checkSequence (ScriptNum.value b) with _ | _ | _
      · simp [hbit]
      · simp [hbit]
      · simp only
        rw [hcongr]
        constructor
        · intro h; exact ⟨h, by omega, .inr trivial⟩
        · intro h; exact h.1

/-! ## The characterization -/

/--
The characterization of the opcode for `verifyScript`. Script-local.
This holds for every checker `c` and every flag set `f` with the CSV flag clear.
Let the operand `b` have at most 5 bytes, and let `n = ScriptNum.value b`, its decode without the minimal requirement.
Let `scriptSig` and `S` have no instruction `0xb2`, and let `scriptPubKey` be `operandScript b S`: the push of `b`, `0xb2`, then `S`.
Then `verifyScript` accepts with `f` and the CSV flag exactly when three conditions hold.
It accepts with `f`. `0 ≤ n` holds. Bit 31 of `n` is set, or `c.checkSequence n` is `some true`.
-/
theorem csv_verifyScript_accepted_iff (c : SignatureChecker) {f : UInt32}
    (hf : hasFlag f ScriptFlags.checkSequenceVerify = false) {scriptSig b S : List UInt8} (hb₅ : b.length ≤ 5)
    (hsig : opcodeFree isCsvOpcode scriptSig = true) (hS : opcodeFree isCsvOpcode S = true) :
    verifyScript c (withCsvFlag f) scriptSig (operandScript b S) = .accepted ↔
      verifyScript c f scriptSig (operandScript b S) = .accepted ∧
        0 ≤ ScriptNum.value b ∧ ((ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0 ∨
          c.checkSequence (ScriptNum.value b) = some true) := by
  obtain ⟨-, -, -, ha9⟩ := lengthByte_facts hb₅
  have hp : isPayToScriptHash (operandScript b S) = false := by
    simp [isPayToScriptHash, operandScript, ha9]
  rw [← VerifyOutcome.ofBaseline_eq_accepted (embed := (id : ScriptError → ScriptError))
      (embedU := (id : Unsupported → Unsupported)) (r := verifyScript c (withCsvFlag f) _ _),
    ← VerifyOutcome.ofBaseline_eq_accepted (embed := (id : ScriptError → ScriptError))
      (embedU := (id : Unsupported → Unsupported)) (r := verifyScript c f _ _),
    ← verifyScriptWith_baseline, ← verifyScriptWith_baseline,
    verifyScriptWith_flags_congr _ (unsupportedFlagBits_withCsvFlag f) (hasFlag_withCsvFlag f (by decide)),
    verifyScriptWith_accepted_iff hp, verifyScriptWith_accepted_iff hp]
  rw [evalScriptWith_congr (step₂ := baselineStep id id (some c) f)
    (fun s i hi => baselineStep_withCsvFlag_of_ne id id (some c) f scriptSig s i hi) f [] hsig]
  constructor
  · rintro ⟨hu, s, t, hs, ht, htop⟩
    obtain ⟨ht', hr⟩ := (evalScriptWith_operand_iff hf hb₅ hS s.stack t).mp ht
    exact ⟨⟨hu, s, t, hs, ht', htop⟩, hr⟩
  · rintro ⟨⟨hu, s, t, hs, ht, htop⟩, hr⟩
    exact ⟨hu, s, t, hs, (evalScriptWith_operand_iff hf hb₅ hS s.stack t).mpr ⟨ht, hr⟩, htop⟩

/--
The target `csv_accepted_iff` of design record 0012, section 9.2. Script-local.
This holds for every input, previous `scriptPubKey`, verifier, and flag set `f` with the CSV flag clear.
Let the operand `b` have at most 5 bytes, and let `n = ScriptNum.value b`.
Let the input's `scriptSig` and `S` have no instruction `0xb2`, and let the previous `scriptPubKey` be `operandScript b S`.
Then `verifyLegacySpend` accepts with `f` and the CSV flag exactly when three conditions hold.
It accepts with `f`. `0 ≤ n` holds. Bit 31 of `n` is set, or `sequenceSatisfied version sequence n` holds, for the version of the input's transaction and the sequence of the input.
-/
theorem csv_accepted_iff (ctx : InputContext) (prevScriptPubKey : Transaction.Script) {f : UInt32}
    (hf : hasFlag f ScriptFlags.checkSequenceVerify = false) (verify : SignatureVerifier) {b S : List UInt8}
    (hb₅ : b.length ≤ 5) (hsig : opcodeFree isCsvOpcode ctx.input.scriptSig.bytes.val = true)
    (hS : opcodeFree isCsvOpcode S = true) (hprev : prevScriptPubKey.bytes.val = operandScript b S) :
    verifyLegacySpend ctx prevScriptPubKey (withCsvFlag f) verify = .accepted ↔
      verifyLegacySpend ctx prevScriptPubKey f verify = .accepted ∧
        0 ≤ ScriptNum.value b ∧ ((ScriptNum.value b).toNat &&& sequenceLockTimeDisableFlag ≠ 0 ∨
          sequenceSatisfied ctx.tx.version ctx.input.sequence (ScriptNum.value b) = true) := by
  have hcheck : (transactionChecker ctx.tx ctx.index verify).checkSequence (ScriptNum.value b) =
      some (sequenceSatisfied ctx.tx.version ctx.input.sequence (ScriptNum.value b)) := by
    simp [transactionChecker, InputContext.input, List.getElem?_eq_getElem ctx.index_lt]
  unfold verifyLegacySpend
  rw [hprev, csv_verifyScript_accepted_iff _ hf hb₅ hsig hS, hcheck]
  simp

end DogeLib.Proposals.RelativeLockTime
