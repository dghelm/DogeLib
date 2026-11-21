module

public import DogeLib.Proposals.Framework.Proofs.Chain
public import DogeLib.Proposals.RelativeLockTime.Proofs.SequenceWitnesses

/-!
# Proofs: `Proposals.RelativeLockTime`, the block-level soft fork

The block-level targets of design record 0012, section 9.3, that join the three rules.
`DogeLib.Proposals.RelativeLockTime.Proofs.Block` has the inactive equality, the activation, the restriction and the untouched block.

- `relativeLockTime_strict`: three strictness witnesses, one for each rule.
- `relativeLockTime_use`: three use witnesses, one for each rule.
- `relativeLockTime_softFork`: the framework's `SoftFork` for the revision and `validateBlock`, with the witnesses of each rule.
- `relativeLockTime_chain`: a list of blocks that the revised connection accepts is accepted by `connectChain`, to the same final coin set. For connection alone.
- `relativeLock_enforced`: in an accepted applicable block, a spend of a coin whose script starts with a height operand and `OP_CHECKSEQUENCEVERIFY` is at least that many blocks above the coin.
- `relativeLock_enforced_time`: the time form, for an operand with bit 22 set, with median times past in the place of heights.

## Label

Every theorem here is *block-level*.
It is about `validateBlock` or `connectBlock` for one block on a supplied coin set and view, or about a list of blocks through `connectChain`.
It holds for mainnet rules, and for every signature verifier.
It is not a soft-fork claim about the network, and it says nothing about fork choice, convergence or liveness.
The revision is active on no network (`csv_never_lockedIn` for the deployment of the pin).

## Hypotheses and where Core enforces them

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The block is applicable. | `relativeLock_enforced`, `relativeLock_enforced_time` | It is a limit of the revision (design record 0012, section 5). Core reaches the code of the rules only with a predecessor. |
| The spent `scriptPubKey` is `operandScript b S`, and `S` and the `scriptSig` have no instruction `0xb2`. | `relativeLock_enforced`, `relativeLock_enforced_time` | Not a rule. It is the form of script that the theorem is about, as in `csv_accepted_iff`. |
| The operand has bit 31 clear. | `relativeLock_enforced`, `relativeLock_enforced_time` | Not a rule. With bit 31 set the opcode is a NOP. Bit 22 selects the height form or the time form. |

`relativeLockTime_chain` has no hypothesis on the contexts or the views of the blocks.
A list with an unlinked context or a wrong view is still covered: the conclusion is about `connectChain` on the same contexts.
-/

@[expose] public section

namespace DogeLib.Proposals.RelativeLockTime

open DogeLib.Block DogeLib.Script DogeLib.Transaction DogeLib.Work DogeLib.Proposals.Framework

/-! ## The witnesses and the soft fork -/

/--
The target `relativeLockTime_strict` of design record 0012, section 9.3. Block-level.
Three contexts where `validateBlock` accepts a block and the active revision rejects it, one for each rule, each with the error of its rule:

1. BIP 113: `bad-txns-nonfinal` of `ContextualCheckBlock` (`cutoff_strict`).
2. BIP 112: `UNSATISFIED_LOCKTIME` of input 0 of transaction 1, a failure that is not mandatory (`opcode_strict`).
3. BIP 68: `RevisionError.sequenceLocks 1` (`sequence_strict`).
-/
theorem relativeLockTime_strict :
    ((∃ r, baselineValidate (witnessArgs 1395094000) = .ok r) ∧
        revisedValidate true (witnessArgs 1395094000) = .rejected (.inl (.contextualBody .nonFinal))) ∧
      ((∃ r, baselineValidate (opcodeArgs 1) = .ok r) ∧
        revisedValidate true (opcodeArgs 1) =
          .rejected (.inl (.connect (.script 1 0 false .unsatisfiedLocktime)))) ∧
      ((∃ r, baselineValidate lockArgs = .ok r) ∧
        revisedValidate true lockArgs = .rejected (.inr (.sequenceLocks 1))) :=
  ⟨cutoff_strict, opcode_strict, sequence_strict⟩

/--
The target `relativeLockTime_use` of design record 0012, section 9.3. Block-level.
Three contexts where the active revision accepts a block and a rule runs, one for each rule:

1. BIP 113: a time lock time below the median cutoff (`RunsCutoff`, `cutoff_use`).
2. BIP 112: an executed `0xb2` with a satisfied operand (`RunsOpcode`, `opcode_use`).
3. BIP 68: a version 2 input with a met height lock of one block (`RunsSequenceLock`, `sequence_use`).

The second and the third context are one block.
-/
theorem relativeLockTime_use :
    ((∃ r, revisedValidate true (witnessArgs 1395093999) = .ok r) ∧ RunsCutoff (witnessArgs 1395093999)) ∧
      ((∃ r, revisedValidate true (opcodeArgs 2) = .ok r) ∧ RunsOpcode (opcodeArgs 2)) ∧
      ((∃ r, revisedValidate true (opcodeArgs 2) = .ok r) ∧ RunsSequenceLock (opcodeArgs 2)) :=
  ⟨cutoff_use, opcode_use, sequence_use⟩

/--
The target `relativeLockTime_softFork` of design record 0012, section 9.3. Block-level.
The revision `RelativeLockTime`, with the rules of BIP 113, BIP 112 and BIP 68, is a soft fork of `validateBlock` at the level of one block, in the sense of the framework's `SoftFork`.
The statement holds with the use predicate of each rule: `RunsCutoff`, `RunsOpcode` and `RunsSequenceLock`.

Each `SoftFork` has four parts, for `revisedValidate` and `baselineValidate`:

- With `active` false, the revision equals the embedded result of `validateBlock` (`relativeLockTime_inactive_eq`).
- For every `active` and every context, a block that the revision accepts, `validateBlock` accepts (`relativeLockTime_restricts`).
- A strictness witness of the rule (`relativeLockTime_strict`).
- A use witness of the rule (`relativeLockTime_use`).

A context holds the verifier, the two check flags, the view, the times, the coin set and the block.
The statement is about one block on a supplied coin set and view, for mainnet rules.
It is not a soft-fork claim about the network, and it says nothing about fork choice, convergence or liveness.
-/
theorem relativeLockTime_softFork :
    SoftFork embedBaseline baselineVerdict BlockOutcome.verdict RunsCutoff baselineValidate revisedValidate ∧
      SoftFork embedBaseline baselineVerdict BlockOutcome.verdict RunsOpcode baselineValidate revisedValidate ∧
      SoftFork embedBaseline baselineVerdict BlockOutcome.verdict RunsSequenceLock baselineValidate revisedValidate :=
  ⟨cutoff_softFork, opcode_softFork, sequence_softFork⟩

/-! ## A list of blocks -/

/--
The entries of the revised connection of a list of blocks.
Each block has the view of its predecessor and its context.
Its revision is `blockRevision` on that view, and it is active when the activation is active on mainnet at the height of the context.
-/
def chainEntries (verify : SignatureVerifier) (a : Activation) (l : List (List BlockIndex × ConnectContext × Block)) :
    List (BlockRevision ScriptError Unsupported ConnectRejection ConnectReason × Bool × ConnectContext × Block) :=
  l.map fun entry => (blockRevision verify entry.1, a.isActive .mainnet entry.2.1.height, entry.2.1, entry.2.2)

/--
The target `relativeLockTime_chain` of design record 0012, section 9.3. Block-level, for connection alone.
Take a list of blocks, each with the view of its predecessor and its context.
If the revised connection (`connectChainWith` on `chainEntries`) accepts the list from a coin set, `connectChain` accepts the blocks with their contexts from that set, to the same final coin set.
For every activation, embedding, verifier, flag `fJustCheck` and coin set.

The statement covers the script flag of BIP 112 and the sequence locks of BIP 68.
`connectChain` runs no body check, so the cutoff of BIP 113 has the one-block target `relativeLockTime_restricts` alone.
The statement needs no hypothesis on `csvActive` of a context: with that field true, neither side accepts a block that reaches the test of the field.
-/
theorem relativeLockTime_chain {E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason}
    {verify : SignatureVerifier} (a : Activation) {fJustCheck : Bool}
    {l : List (List BlockIndex × ConnectContext × Block)} {s final : CoinSet}
    (h : connectChainWith E fJustCheck s (chainEntries verify a l) = .ok final) :
    connectChain verify fJustCheck s (l.map fun entry => (entry.2.1, entry.2.2)) = .ok final := by
  have h2 := connectChainWith_restricts (verify := verify) (fun entry hmem => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hmem
    exact ⟨fun ictx spk hacc => spend_restricts hacc, scriptFlags_p2sh _ _⟩) h
  simpa [chainEntries, List.map_map, Function.comp_def] using h2

/-! ## The enforced lock -/

/-- A value masked with bit 22 is 0 or `2^22`. -/
theorem and_typeFlag (x : Nat) :
    x &&& sequenceLockTimeTypeFlag = 0 ∨ x &&& sequenceLockTimeTypeFlag = sequenceLockTimeTypeFlag := by
  have h : sequenceLockTimeTypeFlag = 2 ^ 22 := by decide
  rw [h]
  cases hb : x.testBit 22 with
  | false =>
    left
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : 22 = i
    · subst hi; simp [hb]
    · simp [hi]
  | true =>
    right
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow]
    by_cases hi : 22 = i
    · subst hi; simp [hb]
    · simp [hi]

/-- A value masked with `0x0040ffff` is the sum of its bit 22 and its low 16 bits. -/
theorem and_mask_split (x : Nat) :
    x &&& (sequenceLockTimeTypeFlag ||| sequenceLockTimeMask) =
      (x &&& sequenceLockTimeTypeFlag) + (x &&& sequenceLockTimeMask) := by
  have hm : sequenceLockTimeMask = 2 ^ 16 - 1 := by decide
  have hlt : x &&& sequenceLockTimeMask < 2 ^ 22 := by
    rw [hm, Nat.and_two_pow_sub_one_eq_mod]
    have := Nat.mod_lt x (show 0 < 2 ^ 16 by decide)
    omega
  rw [Nat.and_or_distrib_left]
  rcases and_typeFlag x with h | h
  · rw [h]; simp
  · rw [h]
    exact (Nat.two_pow_add_eq_or_of_lt (i := 22) hlt 1).symm

/--
`CheckSequence` for a height operand.
Let `sequenceSatisfied version sequence n` hold, and let `n` have bit 22 clear.
Then the version is at least 2, the sequence has bits 31 and 22 clear, and the low 16 bits of `n` are at most those of the sequence.
-/
theorem sequenceSatisfied_height {version sequence : UInt32} {n : Int}
    (h : sequenceSatisfied version sequence n = true) (h22 : n.toNat &&& sequenceLockTimeTypeFlag = 0) :
    2 ≤ version.toNat ∧ sequence.toNat &&& sequenceLockTimeDisableFlag = 0 ∧
      sequence.toNat &&& sequenceLockTimeTypeFlag = 0 ∧
        n.toNat &&& sequenceLockTimeMask ≤ sequence.toNat &&& sequenceLockTimeMask := by
  simp only [sequenceSatisfied, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_mask_split, h22] at h
  obtain ⟨⟨⟨hv, hd⟩, hor⟩, hle⟩ := h
  have hflag : sequenceLockTimeTypeFlag = 4194304 := rfl
  have hn : n.toNat &&& sequenceLockTimeMask ≤ 65535 := Nat.and_le_right
  rcases and_typeFlag sequence.toNat with hs | hs
  · exact ⟨hv, hd, hs, by omega⟩
  · omega

/-- `connectScriptFlags` has the CSV flag clear, at every height. -/
theorem connectScriptFlags_csv (height : Nat) :
    hasFlag (connectScriptFlags height) ScriptFlags.checkSequenceVerify = false := by
  unfold connectScriptFlags
  split <;> split <;> decide

/-- When `lookupInputs` succeeds, the coin of the input at each position is at that position. -/
theorem lookupInputs_coin {s : CoinSet} {inputs : List TxIn} {coins : List Coin}
    (h : lookupInputs s inputs = some coins) {j : Nat} {input : TxIn} (hin : inputs[j]? = some input) {coin : Coin}
    (hcoin : s.coin input.prevout = some coin) : coins[j]? = some coin := by
  induction inputs generalizing coins j with
  | nil => simp at hin
  | cons i rest ih =>
    unfold lookupInputs at h
    split at h
    · cases h
    · rename_i c0 hc0
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, rfl⟩ := h
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hin
        subst hin
        rw [hcoin] at hc0
        simp [Option.some.inj hc0]
      | succ k =>
        simp only [List.getElem?_cons_succ] at hin ⊢
        exact ih htail hin

/--
`CheckSequence` for a time operand.
Let `sequenceSatisfied version sequence n` hold, and let `n` have bit 22 set.
Then the version is at least 2, the sequence has bit 31 clear and bit 22 set, and the low 16 bits of `n` are at most those of the sequence.
-/
theorem sequenceSatisfied_time {version sequence : UInt32} {n : Int}
    (h : sequenceSatisfied version sequence n = true) (h22 : n.toNat &&& sequenceLockTimeTypeFlag ≠ 0) :
    2 ≤ version.toNat ∧ sequence.toNat &&& sequenceLockTimeDisableFlag = 0 ∧
      sequence.toNat &&& sequenceLockTimeTypeFlag ≠ 0 ∧
        n.toNat &&& sequenceLockTimeMask ≤ sequence.toNat &&& sequenceLockTimeMask := by
  have hn22 : n.toNat &&& sequenceLockTimeTypeFlag = sequenceLockTimeTypeFlag := by
    rcases and_typeFlag n.toNat with h0 | h1
    · exact absurd h0 h22
    · exact h1
  simp only [sequenceSatisfied, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    and_mask_split, hn22] at h
  obtain ⟨⟨⟨hv, hd⟩, hor⟩, hle⟩ := h
  have hflag : sequenceLockTimeTypeFlag = 4194304 := rfl
  have hs16 : sequence.toNat &&& sequenceLockTimeMask ≤ 65535 := Nat.and_le_right
  rcases and_typeFlag sequence.toNat with hs | hs
  · omega
  · exact ⟨hv, hd, by omega, by omega⟩

/--
What an accepted applicable block ran for one spend of a coin with the script of `csv_accepted_iff`.
Under the conditions of `relativeLock_enforced` without those on the type bit of the operand:
the view is not empty, `sequenceSatisfied` holds for the version, the sequence and the operand, and `sequenceLocks` accepted the transaction with a list of coins that has the coin at the position of the input.
-/
theorem enforced_checks {ρ' μ' : Type} {V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ'}
    {E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason} {verify : SignatureVerifier}
    {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E (blockRevision verify ctx.view) true fCheckPOW fCheckMerkleRoot ctx s b = .ok r)
    (happ : applicable ctx b = true) {i : Nat} {tx : Transaction} (hi : b.transactions[i]? = some tx)
    (hcb : tx.isCoinBase = false) {j : Nat} {input : TxIn} (hin : tx.inputs.val[j]? = some input) {coin : Coin}
    (hcoin : (coinsBefore s ctx.height b.transactions i).coin input.prevout = some coin) {bytes S : List UInt8}
    (hb : bytes.length ≤ 5) (hsig : opcodeFree isCsvOpcode input.scriptSig.bytes.val = true)
    (hS : opcodeFree isCsvOpcode S = true) (hscript : coin.out.scriptPubKey.bytes.val = operandScript bytes S)
    (h31 : (ScriptNum.value bytes).toNat &&& sequenceLockTimeDisableFlag = 0) :
    ctx.view ≠ [] ∧ sequenceSatisfied tx.version input.sequence (ScriptNum.value bytes) = true ∧
      ∃ coins, sequenceLocks true ctx.view ctx.height i tx coins = .ok () ∧ coins[j]? = some coin := by
  have hview : ctx.view ≠ [] := by
    intro hnil
    simp [applicable, hnil] at happ
  have hg : (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) = false := by
    cases hgen : (some b.header.pure.getHash == genesisHash? WorkNetwork.mainnet) with
    | false => rfl
    | true => rw [not_applicable_of_genesis hgen] at happ; cases happ
  obtain ⟨coins, hl, htest, hscripts⟩ :=
    connectBlockWith_ok_inv (validateBlockWithActive_ok_connect h) hg i tx hi hcb
  have hj : coins[j]? = some coin := lookupInputs_coin hl hin hcoin
  obtain ⟨ictx, hic, hacc⟩ := checkInputScriptsWith_ok_inv hscripts j coin hj
  obtain ⟨htx, hinp⟩ := inputContext?_some (by simpa using hic)
  have hinput : ictx.input = input := by
    rw [hin] at hinp
    exact (Option.some.inj hinp).symm
  have hspend : verifyLegacySpend ictx coin.out.scriptPubKey (withCsvFlag (connectScriptFlags ctx.height)) verify =
      .accepted := accepted_of_ofBaseline_accepted hacc
  obtain ⟨-, -, hor⟩ := (csv_accepted_iff ictx coin.out.scriptPubKey (connectScriptFlags_csv _) verify hb
    (by rw [hinput]; exact hsig) hS hscript).mp hspend
  rcases hor with hor | hor
  · exact absurd h31 hor
  · rw [htx, hinput] at hor
    exact ⟨hview, hor, coins, txTest_eq_ok_iff.mp htest, hj⟩

/--
The target `relativeLock_enforced` of design record 0012, section 9.3, in its height form. Block-level.
Suppose that the active revision accepts an applicable block.
Take an input of a transaction of the block that is not a coinbase, and the coin that it spends in the set just before its transaction (`coinsBefore`).
Let the script of the coin be `operandScript bytes S`: a push of an operand of at most 5 bytes, then opcode `0xb2`, then `S`.
Let `S` and the `scriptSig` of the input have no instruction `0xb2`.
Let the operand `n = ScriptNum.value bytes` have bits 31 and 22 clear, and let `d` be its low 16 bits.
Then the height of the block is at least the height of the coin plus `d`.

The proof joins two rules.
The opcode of BIP 112 bounds the sequence of the input: it has bits 31 and 22 clear, the version is at least 2, and `d` is at most its low 16 bits (`csv_accepted_iff`).
The sequence lock of BIP 68 then bounds the depth of the coin (`sequenceLocks_iff`).
For every pair of embeddings, verifier, pair of flags, context and coin set.
`relativeLock_enforced_time` is the time form, for an operand with bit 22 set.
-/
theorem relativeLock_enforced {ρ' μ' : Type} {V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ'}
    {E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason} {verify : SignatureVerifier}
    {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E (blockRevision verify ctx.view) true fCheckPOW fCheckMerkleRoot ctx s b = .ok r)
    (happ : applicable ctx b = true) {i : Nat} {tx : Transaction} (hi : b.transactions[i]? = some tx)
    (hcb : tx.isCoinBase = false) {j : Nat} {input : TxIn} (hin : tx.inputs.val[j]? = some input) {coin : Coin}
    (hcoin : (coinsBefore s ctx.height b.transactions i).coin input.prevout = some coin) {bytes S : List UInt8}
    (hb : bytes.length ≤ 5) (hsig : opcodeFree isCsvOpcode input.scriptSig.bytes.val = true)
    (hS : opcodeFree isCsvOpcode S = true) (hscript : coin.out.scriptPubKey.bytes.val = operandScript bytes S)
    (h31 : (ScriptNum.value bytes).toNat &&& sequenceLockTimeDisableFlag = 0)
    (h22 : (ScriptNum.value bytes).toNat &&& sequenceLockTimeTypeFlag = 0) :
    coin.height + ((ScriptNum.value bytes).toNat &&& sequenceLockTimeMask) ≤ ctx.height := by
  obtain ⟨hview, hsat, coins, hok, hj⟩ := enforced_checks h happ hi hcb hin hcoin hb hsig hS hscript h31
  obtain ⟨hv, hd, ht, hle⟩ := sequenceSatisfied_height hsat h22
  have hlock := sequenceLocks_height_lock hview hv hok hin hj hd ht
  omega

/--
The time form of the target `relativeLock_enforced` of design record 0012, section 9.3. Block-level.
Take the conditions of `relativeLock_enforced`, with one change: the operand `n` has bit 31 clear and bit 22 set. Let `d` be its low 16 bits.
Then the view of the context has a median time past `median`, which is that of the predecessor of the block.
The ancestor of the coin has a median time past `t` (`ancestorMedianTimePast`): the ancestor at height `max (c - 1) 0`, for the height `c` of the coin.
And `t + 512 * d ≤ median`.

The statement has the shape of the height form, with median times past in the place of heights.
For every pair of embeddings, verifier, pair of flags, context and coin set.
-/
theorem relativeLock_enforced_time {ρ' μ' : Type} {V : ValidateEmbedding ConnectRejection ConnectReason ρ' μ'}
    {E : ConnectEmbedding ScriptError Unsupported ConnectRejection ConnectReason} {verify : SignatureVerifier}
    {fCheckPOW fCheckMerkleRoot : Bool} {ctx : ValidateContext} {s : CoinSet} {b : Block} {r : ConnectResult}
    (h : validateBlockWithActive V E (blockRevision verify ctx.view) true fCheckPOW fCheckMerkleRoot ctx s b = .ok r)
    (happ : applicable ctx b = true) {i : Nat} {tx : Transaction} (hi : b.transactions[i]? = some tx)
    (hcb : tx.isCoinBase = false) {j : Nat} {input : TxIn} (hin : tx.inputs.val[j]? = some input) {coin : Coin}
    (hcoin : (coinsBefore s ctx.height b.transactions i).coin input.prevout = some coin) {bytes S : List UInt8}
    (hb : bytes.length ≤ 5) (hsig : opcodeFree isCsvOpcode input.scriptSig.bytes.val = true)
    (hS : opcodeFree isCsvOpcode S = true) (hscript : coin.out.scriptPubKey.bytes.val = operandScript bytes S)
    (h31 : (ScriptNum.value bytes).toNat &&& sequenceLockTimeDisableFlag = 0)
    (h22 : (ScriptNum.value bytes).toNat &&& sequenceLockTimeTypeFlag ≠ 0) :
    ∃ median t, medianTimePast ctx.view = .ok median ∧
      ancestorMedianTimePast ctx.view ctx.height coin.height = .ok t ∧
        t + 512 * (((ScriptNum.value bytes).toNat &&& sequenceLockTimeMask : Nat) : Int) ≤ median := by
  obtain ⟨hview, hsat, coins, hok, hj⟩ := enforced_checks h happ hi hcb hin hcoin hb hsig hS hscript h31
  obtain ⟨hv, hd, ht, hle⟩ := sequenceSatisfied_time hsat h22
  obtain ⟨median, t, hmed, hanc, hlock⟩ := sequenceLocks_time_lock hview hv hok hin hj hd ht
  exact ⟨median, t, hmed, hanc, by omega⟩

end DogeLib.Proposals.RelativeLockTime
