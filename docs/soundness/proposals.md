# Soundness: Proposed Revisions

This file states what the proposal-framework, block-level, example, and `RelativeLockTime` proofs establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [COVERAGE.md](../../COVERAGE.md#proposed-revisions) for proposal coverage.

- **Scope**: Script and block proposal frameworks, `ExampleVersionVerify`, `ExampleFaultyLocktime`, and the public proposal `RelativeLockTime` (BIP 68, BIP 112, and BIP 113).
- **Specification modules**: `DogeLib.Proposals.Framework.*`, `ExampleVersionVerify`, `ExampleFaultyLocktime`, and `RelativeLockTime`.
- **Proof modules**: `DogeLib.Proposals.Framework.Proofs`, `ExampleVersionVerify.Proofs`, `ExampleFaultyLocktime.Proofs`, and `RelativeLockTime.Proofs` (under `DogeLib.Proposals.Proofs`).
- **Key boundaries**: All proposal theorems are Script-local or single-block claims on supplied state, not network-level soft-fork, fork-choice, or liveness proofs.
  DogeLib takes no position on the activation of any proposal, and no proposal has a default activation height.

## Proposed revisions: the framework

`DogeLib.Proposals.Framework` holds the framework of [design record 0007](../design/0007-proposed-revisions.md) for proposed revisions.
It belongs to the `Proposals` and `ProposalProofs` libraries, and no baseline library imports it ([ARCHITECTURE.md](../../ARCHITECTURE.md#proposed-revisions)).
These framework theorems are generic and state no property of a specific revision.
See [`RelativeLockTime`](#proposed-revisions-relativelocktime) for the public proposal and [the worked example](#proposed-revisions-the-worked-example) and [the deliberately faulty example](#proposed-revisions-the-deliberately-faulty-example) for framework tests.

`Framework.Script` copies `evalLoop`, `evalScript` and `verifyScript` as `evalLoopWith`, `evalScriptWith` and `verifyScriptWith`.
Each copy takes an instruction step `step` in place of `evalInstruction`.
It also takes an error map `embed : ScriptError → ε` for the errors that the loop and `VerifyScript` produce themselves.
`evalScriptWith` and `verifyScriptWith` also take a map of unsupported reasons `embedU : Unsupported → υ` for the reason `Unsupported.flags` that they produce themselves.
`baselineStep embed embedU checker flags` is `evalInstruction checker script flags` with its errors mapped by `embed` and its unsupported reasons mapped by `embedU`.
A proposal with its own unsupported reasons `U` uses `υ = Unsupported ⊕ U` and `embedU = Sum.inl`, as it uses `ScriptError ⊕ E` for its errors.

The agreement theorems hold for every error map, map of unsupported reasons, checker, flag set, script, state and stack:

- `evalLoopWith_baseline`: `evalLoopWith embed (baselineStep embed embedU checker flags)` equals `evalLoop checker flags`, with the error mapped by `embed` and the unsupported reason mapped by `embedU`.
- `evalScriptWith_baseline`: the same for `evalScript`.
- `verifyScriptWith_baseline`: `verifyScriptWith embed embedU (baselineStep embed embedU (some c) flags) flags` equals `verifyScript c flags`, with the error mapped by `embed` and the unsupported reason mapped by `embedU`.

`Restricts step₁ step₀` holds when every successful step of `step₁` is a successful step of `step₀` with the same state.
For all steps with `Restricts step₁ step₀`, and all error maps and maps of unsupported reasons of the two steps:

- `evalLoopWith_restricts` and `evalScriptWith_restricts`: if the loop or the evaluation with `step₁` succeeds with the final state `t`, then the one with `step₀` succeeds with `t`.
- `verifyScriptWith_restricts`: if `verifyScriptWith` with `step₁` accepts, then `verifyScriptWith` with `step₀` accepts, for the same flags and scripts. The P2SH evaluation is included.
- `verifyScript_of_restricts`: if `step₁` restricts the baseline step for `c` and `flags`, and `verifyScriptWith` with `step₁` and `flags` accepts, then `verifyScript c flags` accepts.

The restriction theorems are Script-local.
The conclusion is about one call of `verifyScript`, not about a block or a chain.

`opcodeFreeFrom O script pc` holds when no instruction from `pc` to the end has an opcode in `O`.
It counts an instruction in a branch that does not execute.
Let two steps agree at every instruction whose opcode is outside `O`:

- `evalLoopWith_congr` and `evalScriptWith_congr`: the two loops, or the two evaluations, give the same result on a script part with no instruction in `O`.
- `verifyScriptWith_congr`: the two `VerifyScript` calls give the same result when `scriptSig`, `scriptPubKey` and every possible P2SH redeem script have no instruction in `O`.
  The theorem takes the redeem-script condition as a hypothesis about each top item of a final stack of `scriptSig`.

`Framework.Activation` defines `Activation`, one optional activation height for each `WorkNetwork`, and `Activation.isActive`.
For every activation, network and height, `Activation.isActive_lt` and `Activation.isActive_of_le` prove that it is false below the activation height and true from it.
`Activation.isActive_mono` proves that it is monotone in the height, and `Activation.none_inactive` that a network without a height is never active.
No proposal is active on any network, so the library defines no `Activation` value.

`Framework.Compatibility` defines the shapes of design record 0007, section 8.1, for a baseline check `baseline : κ → β` and a revision `revised : Bool → κ → ρ`.
`Verdict` classifies a result as accepted, rejected or unsupported.
A strictness witness and a relaxation witness need a rejection, so a change to an unsupported result is not a witness.
`inactiveEq_verifyScriptWith` and `restrictsAcceptance_verifyScriptWith` derive the inactive equality and restriction of acceptance of a `VerifyScript` revision from properties of its step.
`LegacyProjection.identity` is the projection of a revision that keeps encodings and state effects.

No block-level or chain-level theorem uses a projection yet.
The worked example states Script-local theorems with the identity projection.
[The block level](#proposed-revisions-the-block-level) states the block-level theorems, which keep the coin set and the changes of an accepted block.

The framework adds no axiom, hypothesis or trust assumption.
A proposal's theorems are about DogeLib's definitions, and they inherit the gaps of the baseline definitions that they reuse.
By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `VerifyOutcome.verdict_ofBaseline` |
| `propext` | `Activation.none_inactive`, `Activation.isActive_lt`, `Activation.isActive_of_le`, `baselineVerdict_eq_accepted`, `VerifyOutcome.verdict_eq_accepted` |
| `propext`, `Quot.sound` | `evalLoopWith_baseline`, `evalScriptWith_baseline`, `verifyScriptWith_baseline`, `evalLoopWith_restricts`, `evalScriptWith_restricts`, `verifyScriptWith_restricts`, `verifyScript_of_restricts`, `evalLoopWith_congr`, `evalScriptWith_congr`, `verifyScriptWith_congr`, `Activation.isActive_iff`, `Activation.isActive_mono`, `inactiveEq_verifyScriptWith`, `restrictsAcceptance_verifyScriptWith` |

## Proposed revisions: the block level

`Framework.Block` holds the block level of a proposed revision ([design record 0011](../design/0011-mainnet-ranges.md), section 10.1).
`connectBlockWith` and `validateBlockWith` are copies of `connectBlock` and `validateBlock`.
Each takes a `BlockRevision` and a value of `active`.
`connectBlockWith` and `validateBlockWithActive` take `active` as an argument. `validateBlockWith` takes an `Activation` and reads it at the height of the block.

A `BlockRevision` has four parts, and each takes `active` ([design record 0012](../design/0012-relative-lock-time.md), section 6.3):

| Part | Baseline value |
| --- | --- |
| `spend`, the spend check of one input | `verifyLegacySpend` |
| `scriptFlags`, the script flags of a block at a height (extension E1) | `connectScriptFlags` |
| `txTest`, a test of one transaction that is not a coinbase, after the lookup of its inputs (extension E2) | Accepts every transaction |
| `lockTimeArgs`, the two lock-time arguments of `contextualCheckBlockBody` (extension E3) | `csvActive` and the median time past of the context |

A revision of Script sets `spend` alone, and the three other parts have their baseline values.
The count of signature operations, the amounts, the coin set and the header checks are the baseline's.
`connectBlockWith` keeps the result `csvActive` of `connectBlock` for a context whose `csvActive` is true.
That field is the version-bits state of the pin, and no revision reads it as its activation.

A result is a `BlockOutcome`: an acceptance with the coin set and the changes, a rejection, or an unsupported result.
An embedding gives the maps of the baseline errors and of the script results into the types of the outcome.
A baseline error that `isRejection` marks as a rejection of Core becomes a rejection, and a result outside the model becomes an unsupported result.
*The embedded result* of a baseline call is its result through those maps.
The transaction test returns an outcome of the same types, so a revision can add its own rejections and unsupported reasons (extension E4).

Every theorem is block-level: it is about one block on a supplied coin set and chain view.
Each holds for every verifier, embedding, context, coin set and block, and none assumes a property of the verifier.

- `connectBlockWith_baseline` and `validateBlockWith_baseline`: with the baseline revision and the baseline error types, each definition equals `connectBlock` or `validateBlock`.
  `connectBlockWith_ofBaseline` and `validateBlockWith_ofBaseline` state the same agreement as the embedded result, for every embedding.
  So the comparisons of `block.validate` with Core apply to the copies with the baseline revision.
  A change to the baseline that a copy does not follow fails the build.
- `validateBlockWith_inactive`: take a revision with `BlockRevision.InactiveBaseline`.
  With `active` false, its spend check equals the embedded result of `verifyLegacySpend`, and its three other parts have their baseline values.
  At a height where the activation is inactive, `validateBlockWith` equals the embedded result of `validateBlock`: each acceptance, each rejection and each result outside the model.
  `validateBlockWith_inactive_of_lt` and `validateBlockWith_inactive_of_none` give the cases of a height below the activation height, and of no activation height.
- `connectBlockWith_restricts`: take a revision, a value of `active` and a context, with the script flags `f` of the revision at the height.
  Let the spend check under `f` accept only inputs that `verifyLegacySpend` accepts under `connectScriptFlags`.
  Let `f` and `connectScriptFlags` agree on `SCRIPT_VERIFY_P2SH`, which the count of signature operations reads.
  If `connectBlockWith` accepts a block on a coin set, `connectBlock` accepts it on that set, with the same coin set and the same changes.
  The baseline has no transaction test, so the theorem has no condition on `txTest`.
- `validateBlockWith_restricts`: the same for `validateBlock`, with a condition on the lock-time cutoff.
  When the contextual header check of the block passes, the cutoff of the revision is at most the cutoff of the baseline.
  The cutoff is `lockTimeCutoff`: the median time past with `csvActive` true, and the time of the block otherwise.
  The hypotheses read the first run of each script check, and the theorem says nothing about the reason of a rejection.
- `validateBlockWith_congr`: take a revision whose spend check is `verifyScriptWith` with a step that equals the baseline step on every instruction with an opcode outside a set `O`.
  Let its script flags, its transaction test and its lock-time arguments agree with the baseline on the block.
  Take a block with `BlockUntouched O`: no `scriptSig`, no spent `scriptPubKey` and no P2SH redeem script of a spend holds an instruction with an opcode in `O`.
  Then `validateBlockWith` equals the embedded result of `validateBlock`, for every value of `active`.
  The equality covers both runs of each script check.

`Framework.Proofs.LockTime` has the rule-level facts behind the cutoff condition.
`isFinalTx_mono` shows that a transaction that is final at a cutoff is final at every later cutoff.
`contextualCheckBlockBody_csv_restricts` takes a median time past that is at most the time of the block. A body that accepts with `csvActive` true then accepts with `csvActive` false.

Core enforces that hypothesis in `ContextualCheckBlockHeader`, with the reason `time-too-old` (D33, line 3104).
`validateBlock` runs that check before the body check, so `validateBlockWith_restricts` can use its result and assumes nothing about the times.
A header with the genesis hash skips that check.

`BlockUntouched` states three conditions for each input of a transaction that is not a coinbase.
The spent `scriptPubKey` belongs to the coin of the outpoint in the coin set just before the transaction.
So an earlier transaction of the block can have created that coin.
The redeem-script condition applies to a pay-to-script-hash `scriptPubKey` with a push-only `scriptSig`.
It covers the top item of the stack that the baseline evaluation of `scriptSig` leaves, under every flag set.
An instruction in a branch that does not execute counts, as in `opcodeFree`.
A list of candidate blocks from another program is a trusted premise: the theorem says nothing about a block that the program wrongly leaves out.

The examples have block-level instances for their `blockRevision`.
`example_block_inactive`, `example_block_restricts` and `example_block_congr` are the three theorems for `ExampleVersionVerify`, with the opcode `0xb9`.
`block_inactive` and `block_congr` hold for both variants of `ExampleFaultyLocktime`, with the opcode `0xb3`, and `corrected_block_restricts` holds for the corrected variant.
The faulty variant has no restriction theorem, because its spend check accepts a spend that `verifyLegacySpend` rejects.

The theorems do not say:

- That a revision is a soft fork of the network. A restriction theorem covers one block on one coin set. The statement for a chain needs an induction, and the full claim needs a legacy projection (design record 0007, section 8.3).
- Anything about a list of blocks beyond `connectChainWith_restricts`: a list that the revised connection accepts is accepted by `connectChain`, to the same final coin set. The statement is for connection alone, and it does not require that the list is a chain.
- Anything about a revision of the count of signature operations, of the amounts or of a header check. Those parts are the baseline's.
- Anything about Core. No Core behaviour exists for an example, so no comparison supports its revised verdict. [The lock-time cutoff of `RelativeLockTime`](#proposed-revisions-relativelocktime) has a comparison with Core's dormant code, under its own label.
- That the proposal executable computes these definitions correctly beyond its test. The agreement theorems are about the Lean definitions, and `dogelib-proposal-oracle` is compiled code ([docs/oracle.md](../oracle.md#the-proposal-executable)).

The proof of `validateBlockWith_ofBaseline` does not unfold `validateBlock` with the `unfold` tactic.
The kernel compares a definition with its unfolded body by reduction.
For `validateBlock` it then reduces the test of the genesis hash, which does not end in practical time.
`validateBlock_value` states that `validateBlock` equals its stored value, which the term elaborator `definition_value%` reads from the environment.
The kernel checks `validateBlock_value` as it checks every theorem, and the two sides are one term.
The elaborator is not trusted: a wrong value would fail that check.

The block level adds no axiom, hypothesis or trust assumption.
By `#print axioms` with Lean `v4.35.0`, each theorem named in this subsection depends on `propext`, `Classical.choice` and `Quot.sound` alone.

## Proposed revisions: the worked example

`DogeLib.Proposals.ExampleVersionVerify` is the worked example of [design record 0007](../design/0007-proposed-revisions.md), section 10.
It is not a proposal for Dogecoin, and no network activates it.
Decision 9 keeps it in the `Proposals` library as a permanent test of the framework.

The example redefines `OP_NOP10` (`0xb9`).
With `active` true and the opcode in an executing branch, `exampleStep` runs the baseline `evalInstruction` and then `versionCheck` on its successful state.
`versionCheck` rejects an empty stack, an operand of more than five bytes and a negative operand.
It also rejects an operand above the transaction version, read as an unsigned 32-bit value.
Without a transaction context it reports an unsupported capability.
It never pops the operand, and it returns the state that it receives or fails.

What the proofs say. Every theorem is Script-local: it is about one call of `evalScript`, `verifyScript` or `verifyLegacySpend`, not about a block or a chain.

- `exampleStep_restricts`: for every `active`, context, checker, flag set, baseline error map and baseline map of unsupported reasons, the example step restricts the baseline step.
- `example_inactive_eq`, `example_evalScript_inactive_eq`, `example_spend_inactive_eq`: with `active` false, each revised definition equals the baseline result with the error and the unsupported reason under `Sum.inl`. This holds for every other argument. Every result agrees, including each rejection and each unsupported capability.
- `example_soft_fork_local`: for every `active`, input, previous `scriptPubKey`, flag set and verifier, if the revised spend predicate accepts, `verifyLegacySpend` accepts. `example_verifyScript_soft_fork_local` states the same for `verifyScript`, including P2SH.
- `example_eq_of_no_nop10`: for every `active` and context, the revision equals the baseline on scripts without an instruction `0xb9`. The condition covers `scriptSig`, `scriptPubKey` and every redeem script that the P2SH evaluation can take. So a baseline comparison also applies to the revision on those scripts.
- `example_strict`: a concrete spend with version 1 and the previous `scriptPubKey` `01 02 b9`, which `verifyLegacySpend` accepts and the active revision rejects with `versionTooLow`.
- `example_use`: the same spend with version 2, which the active revision accepts. Its `scriptPubKey` lies in `RunsRule`, so `OP_NOP10` runs at the top level.
- `example_softFork`: the four results above in the framework's `SoftFork` structure, over `SpendArgs`.
- `example_accepted_iff`, `example_spend_accepted_iff`: let `scriptPubKey` be the push of an operand `b` of at most five bytes, then `OP_NOP10`, then a script `S`. Let `scriptSig` and `S` have no instruction `0xb9`. Then the active revision with a context accepts exactly when the baseline accepts and `0 ≤ ScriptNum.value b ≤ version`, for every checker and flag set.
- `example_step_state`, `example_evalScript_state`: a successful revised step or evaluation is a baseline success with the projected state. `example_soft_fork_projected`: an accepted input projects to an input that the baseline accepts. `projection` is the identity.

The example adds no axiom and no trust assumption.
It inherits the gaps of the baseline definitions that it reuses: the `SignatureVerifier` hypothesis of `transactionChecker` and the unsupported flag set of `verifyScript`.
It has these boundaries:

- **Unsupported reason.** The unsupported reasons of the example are `Unsupported ⊕ ExampleUnsupported`, with the baseline reasons under `Sum.inl`. A missing context reports `Sum.inr ExampleUnsupported.missingContext`. By the definition of `exampleStep` and of the framework, no baseline reason maps to `Sum.inr`, but no theorem states that. A missing context stays unsupported, never a rejection.
- **Order of the context check.** Section 10.1 lists the missing context fifth. The definition checks it after the negative operand and before the version comparison, which reads the context. That order matches `checkLockTimeStep` with a checker whose `checkLockTime` returns `none`. The baseline `OP_CHECKLOCKTIMEVERIFY` without a checker differs: it reports unsupported before it reads the stack.
- **Error order.** The baseline step checks the stack size before `versionCheck` runs. A caller's initial stack of more than 1,000 items gives `STACK_SIZE` before the example's own error (section 10.2). A known answer checks that case. The order changes an error, never acceptance.
- **Characterization domain.** `example_accepted_iff` covers an operand pushed by `OP_0` or a direct push of one to five bytes. It does not cover `OP_1NEGATE`, `OP_1` to `OP_16`, the `OP_PUSHDATA` forms or a longer operand. It also excludes a second `OP_NOP10`, even in a branch that does not execute.
- **Witnesses.** `example_strict` and `example_use` are computed by the kernel with `decide +kernel`. The spends contain no signature opcode, so no digest is computed.
- **Evidence.** The known answers in `tests/KnownAnswers/Proposals/ExampleVersionVerify.lean` have results derived by hand from section 10.1. No other implementation of the rule exists, so there is no comparison.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `projection_eq_identity` |
| `propext` | `readInstruction_operandScript_nop10` |
| `propext`, `Quot.sound` | `versionCheck_next`, `exampleStep_false`, `exampleStep_restricts`, `exampleStep_eq_of_not_nop10`, `example_evalScript_inactive_eq`, `example_inactive_eq`, `example_spend_inactive_eq`, `example_inactiveEq`, `example_verifyScript_soft_fork_local`, `example_soft_fork_local`, `example_restrictsAcceptance`, `example_evalScript_eq_of_no_nop10`, `example_eq_of_no_nop10`, `example_step_state`, `example_evalScript_state`, `example_soft_fork_projected`, `toNat_lengthByte`, `readInstruction_operandScript_zero`, `readInstruction_append`, `opcodeFreeFrom_append`, `example_strict`, `example_use`, `example_softFork` |
| `propext`, `Classical.choice`, `Quot.sound` | `example_accepted_iff`, `example_spend_accepted_iff` |

## Proposed revisions: the deliberately faulty example

`DogeLib.Proposals.ExampleFaultyLocktime` is an invented rule with a deliberate fault, and its corrected variant.
It is not a proposal for Dogecoin, and no network activates it.
It is the worked example of [docs/in-practice.md](../in-practice.md), and a test that the framework refutes a false soft-fork claim.

The rule redefines `OP_NOP4` (`0xb3`), a NOP at the pin (D3, lines 429 to 435).
With `active` true and the opcode in an executing branch, `lockStep` runs the baseline `evalInstruction` and then `checkLockTimeStep` on its successful state.
That step has the checks and errors of `OP_CHECKLOCKTIMEVERIFY` with its flag set, and the checker answers the lock-time comparison.
After a successful check, `Variant.faulty` pops the operand, and `Variant.corrected` keeps the state.

What the proofs say. Every theorem is Script-local: it is about one call of `verifyScript` or `verifyLegacySpend`, not about a block or a chain.

- `lockStep_false`, `revisedVerifyScript_inactive_eq`, `revisedSpend_inactive_eq`, `inactiveEq`: with `active` false, each variant equals the baseline result with the error map `id`. This holds for every other argument, and every result agrees.
- `faultyStep_pops`, `faultyStep_not_restricts`: take the checker of lock time 2 and no flags. At `OP_NOP4`, the faulty step succeeds with the stack `[1]`, and the baseline step succeeds with `[1, 2]`. So the faulty step does not restrict the baseline step.
- `faulty_counterexample`: one concrete spend, `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL` with lock time 2 and sequence `0xfffffffe`. `verifyLegacySpend` rejects it with `EVAL_FALSE`, and the active faulty revision accepts it.
- `faulty_counterexample_short`: the same results for `OP_1 OP_0 OP_NOP4` (`51 00 b3`) in the same context. The faulty rule reads the empty operand as 0 and pops it, so the final stack is `[1]`. The baseline leaves `[1, ""]`. The planted-fault search of design record 0009, section 8.1, finds this script among its shortest violations.
- `faulty_not_restrictsAcceptance`, `faulty_not_softFork`: the faulty spend predicate does not restrict acceptance, so it is not a `SoftFork` for any use predicate.
- `faulty_strict`, `faulty_incompatible`: the faulty spend predicate also rejects a spend that the baseline accepts, so it is `Incompatible`.
- `correctedStep_restricts`: for every `active`, checker, flag set, baseline error map and baseline map of unsupported reasons, the corrected step restricts the baseline step.
- `corrected_soft_fork_local`, `corrected_verifyScript_soft_fork_local`, `corrected_restrictsAcceptance`: if the corrected revision accepts, the baseline accepts, for every `active` and other argument. The P2SH evaluation is included.
- `corrected_counterexample`, `corrected_strict`, `corrected_use`, `corrected_softFork`: the corrected revision rejects the counterexample as the baseline does. The witnesses and the four results above give the framework's `SoftFork`, with the use predicate `RunsRule`.

The example adds no axiom and no trust assumption.
It inherits the gaps of the baseline definitions that it reuses, as the worked example does.
It has these boundaries:

- **Unsupported reason.** Without a checker, an executed `OP_NOP4` with `active` true reports `Unsupported.checkLockTimeVerify`. That constructor's documentation describes `OP_CHECKLOCKTIMEVERIFY`, so the label is a stand-in. A spend always has a checker. The example keeps the baseline type of unsupported reasons with the map `id`. The proposal replay maps each revised result back to a baseline result.
- **Flags.** `DISCOURAGE_UPGRADABLE_NOPS` lies outside the supported flags, so every call with it is unsupported in both variants and in the baseline.
- **Witnesses.** The kernel evaluates every concrete spend and step with `decide +kernel`. The spends contain no signature opcode, so no digest is computed.
- **Evidence.** The known answers in `tests/KnownAnswers/Proposals/ExampleFaultyLocktime.lean` have results derived by hand. No implementation of the rule exists, so there is no comparison of the rule. The baseline verdicts of the counterexample and of the lock-time spend `01 02 b3 75 51` agree with the Core harness, by the commands in docs/in-practice.md.

By `#print axioms` with Lean `v4.35.0`, every theorem of the example depends on `propext` and `Quot.sound` only.
The theorems are `lockStep_false`, `lockCheck_corrected_next`, `correctedStep_restricts`, `revisedVerifyScript_inactive_eq`, `revisedSpend_inactive_eq`, `inactiveEq`, `corrected_verifyScript_soft_fork_local`, `corrected_soft_fork_local`, `corrected_restrictsAcceptance`, `faultyStep_pops`, `faultyStep_not_restricts`, `faulty_counterexample`, `faulty_counterexample_short`, `faulty_not_restrictsAcceptance`, `faulty_not_softFork`, `faulty_strict`, `faulty_incompatible`, `corrected_counterexample`, `corrected_strict`, `corrected_use` and `corrected_softFork`.

## Proposed revisions: `RelativeLockTime`

`DogeLib.Proposals.RelativeLockTime` is a proposed revision with a public proposal for Dogecoin ([design record 0012](../design/0012-relative-lock-time.md)).
Design record 0012 covers the rules of BIP 68, BIP 112 and BIP 113, which discussion 3509 of `dogecoin/dogecoin` proposed to activate (SOURCES.md, P1 to P4).
The revision has the three rules.
Its block-level claim is `relativeLockTime_softFork`, and the list below states it with its parts.
DogeLib takes no position on the activation of these rules.

The rule of BIP 113 replaces the lock-time cutoff of `IsFinalTx` in `ContextualCheckBlock` (D110, lines 3127 to 3140).
The baseline cutoff is the time of the block, and the revised cutoff is the median time past of the predecessor.
The revision defines no second body check.
Its `lockTimeArgs` pass `csvActive` true and `Work.medianTimePast` of the view to the baseline `contextualCheckBlockBody`, which holds Core's branch for an active CSV state.
The revised rule applies when `active` is true and the block is *applicable*.
An applicable block has a view that is not empty, and a header without the hash of the mainnet genesis block.
For every other block the arguments are those of the baseline.

The rule of BIP 112 turns opcode `0xb2` from `OP_NOP3` into `OP_CHECKSEQUENCEVERIFY`.
Core's `ConnectBlock` does that with one script flag (D114, lines 1906 to 1911), and the baseline evaluator already has both branches of the opcode (D3, lines 392 to 427).
The revision defines no second opcode. Its `scriptFlags` add `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` to `connectScriptFlags` when `active` is true, and its spend check is `verifyLegacySpend`.
The flag is not mandatory, so the second script run of a failed input has no CSV flag, as in Core's `CheckInputs` (D101, lines 1488 to 1512).
`scriptFlags` does not read the block. `relativeLockTime_eq_of_not_applicable` shows that the revision still equals the baseline on a block that is not applicable.

The rule of BIP 68 gives the sequence of an input the meaning of a relative lock time.
Core's `ConnectBlock` runs `SequenceLocks` on each transaction that is not a coinbase, with `LOCKTIME_VERIFY_SEQUENCE` only in an active CSV state (D114, lines 309 to 384, 1906 to 1911 and 1948 to 1959).
The baseline has no definition of that test. The revision defines it as `sequenceLocks`, with unbounded integers, and runs it as the transaction test of the block layer.
The test applies to a transaction whose version is at least 2 as an unsigned value. Let `n` be the low 16 bits of a sequence with bit 31 clear, and `c` the height of the spent coin.
With bit 22 clear the lock is met when `c + n` is at most the height of the block.
With bit 22 set it is met when `t + 512 * n` is at most the median time past of the predecessor, where `t` is the median time past of the ancestor at height `max (c - 1) 0`.
A transaction with a lock that is not met gets `RevisionError.sequenceLocks`, Core's `bad-txns-nonfinal` of `ConnectBlock`.

The test reads ancestor times in the view of the predecessor, which the revision takes as an argument. `revisedValidate` passes the view of its context.
The ancestor at height `a` is the view entry at depth `height - 1 - a`, and its median is `Work.medianTimePast` of the view from that entry.
The test has three results outside the model, and none is a rejection:

- `heightOutOfDomain`: an input with a lock spends a coin at a height of at least `2^31 - 65535`. Core computes `c + n - 1` from the left in `int`, and the sum `c + 65535` then does not fit.
- `coinAboveBlock`: a time lock reads a coin above the block. For a coin one block above, Core reads the median of the block itself, and for a higher coin it dereferences a null pointer (D114, line 348).
- `ancestorOutsideView`: the view does not give a median that the test reads. The first entry of the view is not at the height below the block, or the view is too short at the predecessor or at the ancestor of a time lock.

So the revision gives no verdict on those inputs, where Core has one or has undefined behaviour.

- `relativeLockTime_inactive_eq`: with `active` false, the revision equals the embedded result of `validateBlock`, for every context.
  `relativeLockTime_activation` gives the same equality for `validateBlockWith` where an activation is inactive at the height of the block.
- `relativeLockTime_restricts`: if the revision accepts a block, `validateBlock` accepts it, with the same coin set and the same changes.
  The theorem holds for every `active` and every context, on an applicable block or not. It covers the three rules.
  A result outside the model is not an acceptance, so the theorem says nothing about a block with such a result.
- `relativeLockTime_eq_of_untouched`: take a context with `csvActive` false, and a block with three properties.
  It has no cutoff transaction. No transaction that is not a coinbase has both a version of at least 2 and an input whose sequence has bit 31 clear. No script of a spend holds an instruction `0xb2`.
  Then the revision equals the embedded result of `validateBlock`.
  A cutoff transaction has a time lock time from the median cutoff to below the block time, and an input whose sequence is not `SEQUENCE_FINAL`.
  The scripts of a spend are its `scriptSig`, the spent `scriptPubKey` and a P2SH redeem script.
  `contextualBody_eq_of_cutoff_untouched` states the first part for the body check alone.
- `cutoff_strict` and `cutoff_use`: two made blocks at height 145,000 on a made view.
  `validateBlock` accepts the first, and the active revision rejects it with `bad-txns-nonfinal`.
  The active revision accepts the second, whose coinbase has a time lock time below the median cutoff and a sequence that is not final.
- `cutoff_softFork`: the framework's `SoftFork` for the revision and `validateBlock`, from the statements above. It is block-level.
- `csvFlagStep_restricts`, `csvFlag_soft_fork_local`: for every checker, verifier and flag set, a step or a spend that succeeds with the CSV flag added succeeds without it. A successful step has the same state. Script-local.
- `csv_accepted_iff`: the characterization of the opcode for one input. Script-local.
  Its domain is a `scriptPubKey` that pushes an operand `n` of at most 5 bytes with a direct push, runs `0xb2`, and then runs a script without `0xb2`.
  The `scriptSig` has no `0xb2`, and the flag set has the CSV flag clear.
  With the flag added, the spend is accepted exactly when it is accepted without the flag, `0 ≤ n`, and bit 31 of `n` is set or `sequenceSatisfied version sequence n` holds.
  The domain has no P2SH case and no other push form of the operand.
- `opcode_strict` and `opcode_use`: two made blocks at height 145,000 that spend a coin with the script `01 01 b2`, with the sequence 1.
  With transaction version 1, `validateBlock` accepts the block, and the active revision rejects it with `UNSATISFIED_LOCKTIME`, as a failure that is not mandatory.
  With version 2, the active revision accepts the block.
- `opcode_softFork`: the framework's `SoftFork` with those two witnesses. It is block-level.
- `sequenceLocks_inactive`, `sequenceLocks_iff`: the rule for one transaction, on a supplied view and supplied coins.
  With `active` false, or with a version below 2, the test accepts.
  Take `active` true, a version of at least 2 and a result that is not outside the model. The test accepts exactly when the view is empty, or each input with bit 31 clear meets its lock.
  The case of an empty view is the block without a predecessor. Design record 0012, section 5, makes the revision inactive for such a block, so the test accepts every transaction there, and the characterization names the case.
  `sequenceLocks_iff_of_view` states the characterization without that case, for a view that is not empty.
- `sequenceLocks_fits`, `inputLock_fits`: the sums of `CalculateSequenceLocks` fit `int` and `int64_t`.
  The first theorem takes a result of `calculateSequenceLocks` from Core's start, and bounds the pair after the last input.
  The second takes a result of `inputLock` for one input, and bounds its term, with the sum before the subtraction of 1.
  Neither has a separate hypothesis on the heights: a result implies the height bound, because `heightOutOfDomain` excludes the coin heights at which a sum can overflow.
- `sequence_strict` and `sequence_use`: two made blocks at height 145,000.
  The first spends a coin at height 144,999 with the sequence 2, from a transaction of version 2. `validateBlock` accepts it, and the active revision rejects it with `RevisionError.sequenceLocks`.
  The second is the block of `opcode_use`: its input has a met height lock of one block on a coin at height 1.
- `relativeLockTime_softFork`: the block-level claim of design record 0012, section 9.3.
  The revision is a soft fork of `validateBlock` at the level of one block, in the sense of the framework's `SoftFork`, with the use predicate of each of the three rules.
  Its parts are the inactive equality, the restriction, three strictness witnesses (`relativeLockTime_strict`) and three use witnesses (`relativeLockTime_use`).
- `relativeLockTime_chain`: take a list of blocks, each with the view of its predecessor and its context.
  If the revised connection accepts the list from a coin set, `connectChain` accepts it from that set, to the same final coin set. For every activation.
  The statement is about `connectBlock` alone, so it covers the flag and the sequence locks, and not the cutoff.
  It does not require that the contexts or the views are those of one chain.
- `relativeLock_enforced`: suppose that the active revision accepts an applicable block.
  Take an input of a transaction that is not a coinbase, which spends a coin whose script is a push of an operand of at most 5 bytes, then `0xb2`, then a script without `0xb2`. Let the `scriptSig` have no `0xb2`.
  Let the operand have bits 31 and 22 clear, with the low 16 bits `d`. Then the height of the block is at least the height of the coin plus `d`.
  The opcode bounds the sequence of the input, and the sequence lock bounds the depth of the coin.
  The coin is that of the set just before the transaction, so it can be a coin that the same block created.
- `relativeLock_enforced_time`: the time form, for an operand with bit 31 clear and bit 22 set.
  The view has a median time past `m`, and the ancestor of the coin at height `max (c - 1) 0` has a median time past `t`. Then `t + 512 * d ≤ m`.

| Hypothesis | Used by | Where Core enforces it |
| --- | --- | --- |
| The median time past of the predecessor is below the time of the block. | `lockTimeCutoff_le` | `ContextualCheckBlockHeader`, `time-too-old` (D33, line 3104). `validateBlock` runs it first, so `relativeLockTime_restricts` does not assume it. |
| The block is applicable. | The revised rule, `relativeLock_enforced`, `relativeLock_enforced_time` | It is part of the definition. The two theorems about an enforced lock assume it, because no rule runs on another block. So do helper theorems that state what the active rule computes, such as `lockTimeArgs_of_headerPassed`, `txTest_of_sequence_untouched` and `enforced_checks`. The inactive equality, the activation, the restriction, the soft fork, the list of blocks and the untouched block do not assume it. Core reads the median only with a predecessor (D110, line 3135). |
| `csvActive` of the context is false. | `relativeLockTime_eq_of_untouched` | The field is the version-bits state of the pin. `csv_never_lockedIn` shows that it is never active on a mainnet header chain whose headers passed `checkBlockHeader`. No theorem shows that the real chain meets that hypothesis. |
| The height bound of the sequence locks: a coin height below `2^31 - 65535`. | `sequenceLocks_fits`, `inputLock_fits` | Not enforced as a rule. A coin height is at most the height of a block of its chain, and mainnet heights are far below the bound. The definition returns `heightOutOfDomain` above it. Each theorem assumes a result of the definition, which implies the bound. |
| The height of a coin is at most the height of the block. | Time locks of `sequenceLocks` | Not enforced as a rule. It holds for a coin set that a replay built. A supplied coin set can break it, and the result is then `coinAboveBlock`. Core has a defined result for a coin one block above, which the revision does not give. |
| The view is the view of the predecessor, down to the ancestors that the time locks read. | `sequenceLocks` | Core walks its own block index. The revision returns `ancestorOutsideView` when the view is too short or starts at another height. No definition checks that the times of the view are those of the real chain: the view is an input, as for `validateBlock`. |
| The result of the sequence locks is not outside the model. | `sequenceLocks_iff` | The three reasons are limits of the specification. Core has no such result. |
| The domain of `validateBlock` and `connectBlock` (design record 0010, section 3). | Every block-level theorem | As in that record. The revision adds no sum of amounts. |

`Work.medianTimePast` returns an adapter error for a view that is invalid or too short, and `lockTimeArgs` then gives the arguments of the baseline.
No result of `validateBlockWithActive` reads that case: `contextualCheckBlockHeader` computes the same median first, and returns the adapter error (`lockTimeArgs_of_headerPassed`).
`block.contextual_check_body` of the proposal executable runs the body check alone, and it returns `unsupported` for such a view.

The witnesses are computed by the kernel with `decide +kernel`, one check of `validateBlock` at a time.
Two computations use a proof in the place of an evaluation.
Each uses a definition of Lean core by well-founded recursion, which the kernel does not unfold across a module boundary.
`witness_medianTimePast` uses `medianTimePast_mem`, because the median sorts with `List.mergeSort`. Every entry of the made view has one time.
The witness blocks are at height 145,000, where the subsidy is a fixed amount. Below that height the subsidy runs a Mersenne Twister on a `Vector`.
The opcode witnesses have no signature opcode, so no check calls the verifier.
The transaction test reads the median time past of the view, so `witnessRevision` holds its value, and `witnessRevision_eq` proves that the revision on the witness view is that revision.
Both witnesses of the sequence locks have a height lock. No witness in the kernel has a time lock, and the known answers of `lake test` cover time locks.

The targets add no axiom and no trust assumption: each depends on `propext`, `Classical.choice` and `Quot.sound` alone.

The theorems do not say:

- That a lock with `n` equal to 0 always passes. For a time lock that needs a median time past that does not decrease along the view, which no theorem here states.
- Anything about a block on which the sequence locks give a result outside the model. The restriction reads accepted blocks alone.
- That `relativeLock_enforced` holds without its conditions. On a block that is not applicable, or for another form of script, no check of the rule need run.
- Anything about the opcode under `SCRIPT_VERIFY_MINIMALDATA` or `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS`. Those flags are outside `supportedFlags`, and `ConnectBlock` at the pin sets neither.
- That the revision is a soft fork of the network. `relativeLockTime_softFork` covers one block on a supplied coin set and view, for mainnet rules, and `relativeLockTime_chain` covers the connection of a supplied list of blocks. Neither says anything about fork choice, reorganization, convergence or liveness.
- That the rule is right for Dogecoin, or that any network activates it. The revision has no default activation.
- Anything about a signalling mechanism. The activation is one height on mainnet (design record 0012, section 5).
- Anything about a block that an empty candidate list leaves out. The list is the output of a script, and it is a trusted premise of a count.

The revision adds no axiom and no trust assumption.
By `#print axioms` with Lean `v4.35.0`, each theorem named in this subsection depends on `propext`, `Classical.choice` and `Quot.sound` alone.

The comparison of the rule with Core's own code uses a harness input that no theorem supports ([the forced CSV state](oracle-and-harness.md#per-operation-oracle-and-harness-boundaries)).
