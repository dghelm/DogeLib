# Proposed revisions

**Status:** Proposed.
The maintainer has not adopted this record.
Section 13 lists the decisions that adoption needs.

**Date:** 2026-11-07
**Companions:** [Contribution policy](../../CONTRIBUTING.md), [sources](../../SOURCES.md), [architecture](../../ARCHITECTURE.md), [coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [design record 0001](0001-initial-handoff.md) and [design record 0006](0006-contextual-header-validation.md).

## 1. Purpose and boundary

DogeLib specifies Dogecoin Core at the pin in [SOURCES.md](../../SOURCES.md).
The project vocabulary calls that specification the *baseline*, and it calls behaviour intentionally different from the baseline a *proposed revision* ([SOURCES.md](../../SOURCES.md)).
This record proposes how DogeLib states a proposed revision, how a revision is gated, and how its compatibility with the baseline is proved.
The central case is a soft fork: every input that the revision accepts, the baseline also accepts.

The record builds on four rules of [CONTRIBUTING.md](../../CONTRIBUTING.md):

- A change with the purpose *proposed revision* says which existing rules change, and under which activation conditions.
- Existing consensus, proposed consensus changes and node policy are three separate subjects.
- A proposed improvement must not change the baseline. If Core's behaviour should change, the change is specified as a proposed revision.
- A protocol revision has a name, keeps the baseline available and states its activation and context assumptions. A soft-fork claim uses the right legacy projection and its state effects.

It also keeps the labelling rule of [design record 0001](0001-initial-handoff.md), section 10.
A local spending-rule theorem stays labelled as local until the block, activation and legacy-projection obligations are established.
Section 8 gives those obligations a precise form.

The record is a design.
It adds no Lean code, and every theorem in section 11 is a target, not a result.
DogeLib is a specification library for Dogecoin Core.
The record does not argue for any proposal, and its worked example (section 10) is not a proposal for Dogecoin.

The record excludes these subjects:

- Fork choice, chain selection, networking and peer behaviour.
- The politics of activation: who signals, which threshold to choose, and when to deploy.
- The merits of any specific proposal, such as the candidates in the long-term direction of design record 0001.
- Node policy. A change to standardness is policy, not a proposed revision of consensus.
- A version-bit signalling model. Section 7.4 says what it would take.
- Block validity. DogeLib has no specification of a full block, and section 8.3 lists what the full soft-fork claim needs from one.
- Implementation refinement and Rust extraction of a proposal.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The line ranges identify the inspected source:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [interpreter.cpp, lines 344–435](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L344-L435) | `OP_NOP`, `OP_CHECKLOCKTIMEVERIFY`, `OP_CHECKSEQUENCEVERIFY` and the other NOPs in `EvalScript`. |
| C2 | [validation.cpp, lines 1889–1917](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1889-L1917) | The Script flags that `ConnectBlock` selects for a block. |
| C3 | [validation.cpp, lines 3002–3008](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3002-L3008) | `IsWitnessEnabled`. |
| C4 | [chainparams.cpp, lines 83–121](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L83-L121), [lines 243–277](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L243-L277), [lines 388–418](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L388-L418) | Per network: `BIP34Height`, `BIP65Height`, `BIP66Height`, the version-bit window and threshold, the three deployments, and `fStrictChainId`. |
| C5 | [consensus/params.h, lines 16–35 and 59–61](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/params.h#L16-L61) | `DeploymentPos`, `BIP9Deployment` and the version-bit fields. |
| C6 | [versionbits.h, lines 10–26](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/versionbits.h#L10-L26), [versionbits.cpp, lines 24–106 and 143–160](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/versionbits.cpp#L24-L160) | The version-bit constants, the threshold states, `GetStateFor` and `Condition`. |
| C7 | [pureheader.h, lines 22–26 and 110–113](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.h#L22-L113) | `VERSION_AUXPOW`, `VERSION_CHAIN_START` and `GetChainId`. |
| C8 | [dogecoin.cpp, lines 89–99](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp#L89-L99) | The chain ID check of `CheckAuxPowProofOfWork`. |
| C9 | [policy/policy.h, lines 84–93](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/policy/policy.h#L84-L93), [interpreter.h, line 71](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.h#L71) | `STANDARD_SCRIPT_VERIFY_FLAGS` and `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS`. |

The registry already records these files as D3 (`interpreter.cpp`), D33 and D36 (`validation.cpp`), D14 (`chainparams.cpp`), D15 (`consensus/params.h`), D10 (`pureheader.h`), D6 (`dogecoin.cpp`) and D25 (`interpreter.h`).
`versionbits.h`, `versionbits.cpp` and `policy/policy.h` have no identifier.
A lane that cites them adds one, without a change to any pin.
The findings come from source inspection, without a Core comparison run.

## 3. How Core gates its rule changes

The pinned source uses four mechanisms to turn a rule on.
Each one informs the activation model of section 7.

**Always on.**
`ConnectBlock` sets `SCRIPT_VERIFY_P2SH` for every block, with the comment "BIP16 has been enabled since inception" [C2, lines 1889–1894].

**Fixed heights.**
`ConnectBlock` sets `SCRIPT_VERIFY_DERSIG` from `BIP66Height` and `SCRIPT_VERIFY_CHECKLOCKTIMEVERIFY` from `BIP65Height` [C2, lines 1896–1904].
It compares the height of the block with the fields of `GetConsensus(0)`, the record at height zero.
`ContextualCheckBlockHeader` uses the same two heights for its version thresholds, and `ContextualCheckBlock` uses `BIP34Height` (design record 0006, section 3).
The heights are 1,034,383 for BIP66 and 3,464,751 for BIP65 on mainnet [C4, lines 86–87].

**Parameter records by height.**
The record tree of `GetConsensus` switches DigiShield and AuxPoW on at fixed heights, through `nHeightEffective` (design record 0006, item 3).
`Work.getConsensus` and `Block.getAuxPowParams` already specify that search.

**Version-bit deployments (BIP9).**
`ConnectBlock` sets `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` when `VersionBitsState` of the CSV deployment is `THRESHOLD_ACTIVE` [C2, lines 1906–1910].

`GetStateFor` walks back in periods of `nMinerConfirmationWindow` blocks [C6, versionbits.cpp lines 24–106].
It compares the median time past of each period's last block with the start time and the timeout.
A deployment moves from `DEFINED` to `STARTED` at the start time, and to `FAILED` at the timeout.
It moves from `STARTED` to `LOCKED_IN` when at least `nRuleChangeActivationThreshold` blocks of a period meet `Condition`.
`LOCKED_IN` always becomes `ACTIVE` one period later, and `ACTIVE` and `FAILED` are terminal.
`Condition` requires the top three bits of `nVersion` to be `001` and the deployment's bit to be set [C6, versionbits.cpp lines 153–156].

The source settles three facts about the deployments at the pin:

1. On mainnet, the CSV window starts on 1 May 2016 and times out on 1 May 2017 [C4, lines 104–106].
   The window is 10,080 blocks and the threshold is 9,576 [C4, lines 96–97].
2. The SegWit deployment has `nTimeout = 0` on mainnet and testnet [C4, lines 109–111 and 265–267].
   `IsWitnessEnabled` returns `false` on every network, whatever the version-bit state [C3].
   So `ConnectBlock` never sets `SCRIPT_VERIFY_WITNESS` or `SCRIPT_VERIFY_NULLDUMMY` [C2, lines 1913–1917].
3. On a network with `fStrictChainId`, no block that passes `CheckAuxPowProofOfWork` meets `Condition`.
   The check requires every non-legacy block to have `nVersion >> 16` equal to `nAuxpowChainId`, which is `0x0062` [C8, C4 line 120].
   Then bits 29 to 31 of `nVersion` are zero, so the top bits are not `001` [C7].
   A legacy block has version 1 or 2, and does not meet `Condition` either.
   `fStrictChainId` is true on mainnet and regtest, and false on testnet [C4, lines 121, 277 and 418].

Fact 3 is an inference from the source, and no theorem states it yet.
It means that no version-bit deployment of the pinned code can reach `LOCKED_IN` on mainnet or regtest.
Section 11 lists it as a target, because a later signalling model needs it.

The NOPs are the opcodes that earlier soft forks redefined.
`OP_NOP1` and `OP_NOP4` to `OP_NOP10` do nothing in consensus [C1, lines 429–435].
`OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` act as `OP_NOP2` and `OP_NOP3` when their flags are clear [C1, lines 350–358 and 392–400].
With `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS`, each NOP fails instead.
That flag is in `STANDARD_SCRIPT_VERIFY_FLAGS`, which is node policy, not consensus [C9].

DogeLib does not support that flag (`DogeLib.Script.supportedFlags`).
The supported flags still include `STRICTENC`, `LOW_S` and `NULLDUMMY`, which design record 0003 identifies as policy only at this pin.
`ConnectBlock` sets neither `STRICTENC` nor `LOW_S`, and it sets `NULLDUMMY` only in the witness branch, which never runs [C2, lines 1894–1917].
So the theorems of this record cover every flag set that DogeLib supports.
A consensus reading of a theorem also needs a justification of the selected flags for the network and the activation context.

## 4. Options for location and dependency direction

A proposal needs Lean definitions, theorems about them, and theorems that relate them to the baseline.
The baseline must never import a proposal.
Then a consumer of the specification gets no proposal code, and no proposal can change a baseline result.

**Option L1: a namespace in the specification library.**
Proposal modules live under `DogeLib/Proposals/` and the library root `DogeLib.lean` imports them.
Every consumer of `DogeLib` then compiles every proposal, and a baseline module can import a proposal without any check that fails.
This option breaks the rule that a proposal must not change the baseline, unless a separate check enforces it.

**Option L2: separate Lake libraries in the root package.**
The root package gains a library `Proposals`, rooted at `DogeLib.Proposals`, and a library `ProposalProofs` for the theorems about it.
They follow the pattern of `Proofs`, whose roots are the proof tree of each layer ([ARCHITECTURE.md](../../ARCHITECTURE.md#lake-libraries)).
`Proposals` may import `DogeLib`, and `ProposalProofs` may import `Proposals`, `DogeLib` and `Proofs`.
No baseline library imports either of them.

**Option L3: a separate Lake package.**
Proposals live in their own package under `Proposals/`, as the refinement code does under `Refinement/`.
The package boundary enforces the direction, and the package can take dependencies that the root package excludes.
It also needs its own build, CI job and search path in `check-decls`, as the refinement package does.

**Option L4: a separate repository.**
A proposal repository pins a DogeLib release.
The boundary is strong, but a baseline change and the proposals that depend on it can no longer be reviewed together.

**Recommendation: option L2.**
It keeps proposals in the same review and the same declaration check as the baseline, without a second package.
It enforces the direction with two checks that DogeLib already has:

1. `scripts/CheckRefinementImports.lean` loads `DogeLib`, `DogeLib.Proofs` and `DogeLib.Exports`, and rejects any transitive import under a forbidden prefix.
   Stage 1 adds the prefix `DogeLib.Proposals` to that list.
   A baseline module that imports a proposal then fails the *Import boundaries* gate.
2. `lake exe check-decls` reports a file under `DogeLib/` that its default roots do not reach (`unreachableModules`).
   Stage 1 adds the two proposal roots to `defaultModules`, so that every proposal declaration is checked for axioms and substitutions.

Option L3 stays available for a proposal that needs a dependency the root package excludes, such as Mathlib.
That move would need a maintainer decision, because it changes the package structure.

### 4.1 Layout

```text
DogeLib/Proposals.lean                          root of the Proposals library
DogeLib/Proposals/Framework/Activation.lean     the activation model (section 7)
DogeLib/Proposals/Framework/Script.lean         the Script loop with a step parameter (section 6)
DogeLib/Proposals/Framework/Proofs/             agreement and restriction theorems
DogeLib/Proposals/<Name>/                       the definitions of one proposal
DogeLib/Proposals/<Name>/Proofs/                its theorems, in ProposalProofs
tests/KnownAnswers/Proposals/                   known answers of proposals
```

A proposal may import another proposal when it builds on it.
The import shows that dependency, and the dependent proposal states the composite revision in its documentation.

The lane that adds the libraries also adds a *Proposed revisions* section to [ARCHITECTURE.md](../../ARCHITECTURE.md), and a separate section to COVERAGE.md.
A proposal never gets a row in the baseline tables of COVERAGE.md.

## 5. Naming and identity of a proposal

A proposal is a Lean namespace and module tree `DogeLib.Proposals.<Name>`.
`<Name>` describes the rule in UpperCamelCase, such as `ExampleVersionVerify`.
It does not name a person, a company or a release.

A proposal can have an external document, such as a Dogecoin improvement proposal or a BIP.
That document is a source, and SOURCES.md records it like any other source.
The record gives the repository or URL, an exact revision or a content digest, and the date.
Stage 1 adds a table of proposal documents to SOURCES.md, with identifiers `P1`, `P2` and so on.

The Lean definition is the object of every DogeLib claim about the proposal.
The external document explains the rule, but it does not override the Lean definition.
The module documentation lists each difference from the document that the author knows.
A disagreement between the two follows the rule for sources that disagree in [CONTRIBUTING.md](../../CONTRIBUTING.md#sources-of-truth): it is recorded and investigated, not resolved silently.

A proposal has no version number of its own.
A change to the rules of a proposal is a change to its public contract, so its pull request title has `!`.
If two versions of a rule must exist at the same time, the second one gets its own name, such as `<Name>V2`.

## 6. How a revision changes behaviour

A revision needs a revised version of a baseline definition, such as `evalScript`.
The baseline definition must stay as it is.
There are three ways to build the revised definition.

**Option M1: copy and modify.**
The proposal copies the affected baseline definitions and changes the copy.
No baseline file changes.
Each proposal then carries its own copy of the evaluator, and its soft-fork theorem must relate two large definitions.

**Option M2: a step parameter in the proposal library.**
The framework module `DogeLib.Proposals.Framework.Script` defines `evalLoopWith`, `evalScriptWith` and `verifyScriptWith`.
They have the same structure as the baseline `evalLoop`, `evalScript` and `verifyScript`, but take the instruction step as a parameter.
An agreement theorem proves that each one, with the baseline step `evalInstruction`, equals its baseline definition.
A proposal then supplies only its step.

**Option M3: extension points in the baseline.**
The baseline `execOpcode` takes a parameter for the NOPs, and the baseline instance keeps them as NOPs.
The proposal library needs no copy of the loop.
But every baseline definition and theorem above `execOpcode` changes its signature, which is a change to the baseline specification.

**Recommendation: option M2.**
It changes no baseline file.
The agreement theorem pins the framework copy to the baseline, so a later change to `evalLoop` that the framework does not follow fails to build.
The copied code is small: `evalLoop` and `evalScript` together have about 20 lines, and `verifyScript` about 20 more (`DogeLib.Script.Eval` and `DogeLib.Script.Verify`).

### 6.1 Restriction

The framework makes the soft-fork theorem of a Script revision a consequence of one property of its step.
Let `step₀` be the baseline step and `step₁` a revised step.
`step₁` *restricts* `step₀` when every successful revised step is a successful baseline step with the same state:

```text
Restricts step₁ step₀  :=
  ∀ script s i t, step₁ script s i = next t → step₀ script s i = next t
```

The step takes the script, because the signature opcodes read it.
A restricting step can reject, or report a capability as unsupported, where the baseline step succeeds.
It cannot succeed where the baseline step fails, and it cannot change the state of a success.

The framework then proves, once for every proposal, that restriction lifts through the loop and through `VerifyScript`:

- If `evalLoopWith step₁` returns `ok t`, then `evalLoopWith step₀` returns `ok t`, by induction on the distance from the cursor to the end of the script.
- `verifyScriptWith` runs the loop on `scriptSig`, on `scriptPubKey` and on a P2SH redeem script. Each run starts from the final stack of an earlier run. From the same start, a later revised run can still reject where the baseline run succeeds. But each successful revised run gives the same successful baseline state, so acceptance lifts.

The equal final state matters.
Suppose that a step succeeds in both versions but leaves a different stack.
Then the lift fails at the next evaluation, so the restriction property excludes that case.

### 6.2 Errors

The baseline `StepResult.rejected` carries a `ScriptError`, and a proposal cannot add a constructor to the baseline type.
The framework loop is generic in the error type.
A proposal uses a sum of `ScriptError` and its own error type, and the agreement theorem maps baseline results through the left injection.
`Restricts` reads only the successful results, so it does not depend on the error type.

## 7. Activation model

### 7.1 Rule level: an explicit Boolean

Each revised definition takes an argument `active : Bool`, separate from Core's flag set.
The flag set stays Core's, and `supportedFlags` keeps its meaning.
A proposal does not take a free bit of the flag set, because a later Core release can assign that bit.
`unsupportedFlagBits` would also report the bit as unsupported.

Every theorem at the rule level is stated for both values of `active`, or for every value.
So it holds at every height and in every protocol context, whatever activation mechanism a later layer chooses.

### 7.2 Block level: a fixed height

A block-level composition maps the context of a block to `active`, as `ConnectBlock` maps a height to flags [C2].
The recommended model is one activation height for each network, or none:

```text
structure Activation where
  height : WorkNetwork → Option Nat      -- none: never active on that network

def Activation.isActive (a : Activation) (n : WorkNetwork) (h : Nat) : Bool :=
  match a.height n with
  | none    => false
  | some h₀ => h₀ ≤ h
```

The height is the height of the block that contains the transaction, `pindex->nHeight` in `ConnectBlock`.
For a header check, it is the candidate height of design record 0006: the height of the first view entry plus one.

No network has activated any proposal.
So a proposal has no default `Activation` value.
A consumer supplies one, and every theorem is stated for every `Activation`.
The model is monotone: if a rule is active at height `h`, it is active at every greater height on the same network.

### 7.3 Why not signalling first

The fixed-height model matches the BIP65 and BIP66 gates of the pinned code [C2].
It needs no chain data beyond the height, which design record 0006 already supplies.
A signalling model would delay the first proposal by a full state machine.
Also, fact 3 of section 3 shows that Core's version-bit condition cannot hold on mainnet at the pin.

### 7.4 What signalling would need later

A later record can add an activation that follows `VersionBitsState`.
The rule-level theorems do not change, because they quantify over `active`.
The record would need these parts:

1. A view of ancestors that holds `nVersion`.
   `Work.BlockIndex` holds only `nHeight`, `nTime` and `nBits`, because no header check reads an ancestor's version (design record 0006, section 5).
2. The median time past at each period boundary. Stage 1 of design record 0006 adds `Work.medianTimePast`.
3. The state machine of `GetStateFor` [C6].
   A finite view needs a seed state for its first period, as Core's cache gives one.
4. A theorem that `ACTIVE` is terminal along a chain, so that the activation stays monotone.
5. A Dogecoin bit layout.
   Fact 3 of section 3 shows that the top-bit rule of BIP9 conflicts with the chain ID rule.
   The choice of another layout is a protocol decision outside DogeLib.

## 8. Compatibility classes and theorem shapes

### 8.1 Rule-level shapes

Let `B` be a baseline check and `R active` its revision.
Each check has an acceptance result: `accepted` for `verifyScript`, and `.ok ()` for `checkVersion`, `checkBlockHeader` and the contextual check of design record 0006.
Write `ctx` for every other argument: the checker, the flags, the scripts, the network, the view and the times.

Every proposal proves the *inactive equality*:

```text
inactive_eq :  ∀ ctx,  R false ctx = embed (B ctx)
```

`embed` is the injection of section 6.2.
The equality covers every result: acceptance, each rejection and each unsupported capability.

A *soft fork* at that level also proves *restriction of acceptance*:

```text
soft_fork :  ∀ active ctx,  R active ctx = accepted  →  B ctx = accepted
```

A revision that rejects every input satisfies `soft_fork`.
So a soft-fork proposal also proves two *witnesses*:

- A *strictness witness*: one context where the baseline accepts and the active revision rejects. It shows a proper reduction of acceptance through a concrete rejection. A change of rejection errors, or of acceptance into an unsupported result, does not show that.
- A *use witness*: one context where the active revision accepts and the redefined rule runs. Without it, the revision could reject every use of the rule.

A *characterization* states exactly when the active revision accepts, for a named class of inputs.
It is the proposal's main property, and its statement is reviewed before the proof, as [CONTRIBUTING.md](../../CONTRIBUTING.md#theorem-statements) requires.

### 8.2 Levels where checks exist

The shapes apply at each level where DogeLib has a baseline check:

| Level | Baseline | Context | Status of a soft-fork claim |
| --- | --- | --- | --- |
| One Script evaluation | `evalScript` | Checker, flags, script, stack | Available through `Restricts` (section 6.1). |
| One input | `verifyScript`, `verifyLegacySpend` | Checker or `InputContext`, flags, `scriptSig`, `scriptPubKey` | Available. The worked example targets this level. |
| One transaction | None | None | Not available. DogeLib has no `CheckTransaction` and no transaction-level Script loop. |
| One header | `checkVersion`, `checkBlockHeader`, and the contextual check of design record 0006 | Network, header, view, adjusted time, checkpoint height | Available for a revision of a header check, with the candidate height as the activation height. |
| One block, one chain | None | None | Not available (section 8.3). |

A theorem at the Script or input level is *Script-local*.
A theorem at the header level is *header-local*.
COVERAGE.md and the module documentation use those labels, as the rule of design record 0001 requires.

### 8.3 The full soft-fork claim

A full soft-fork claim says that every chain that revised nodes accept, baseline nodes also accept.
It needs three obligations that design record 0001 names:

1. **Block.** A specification of block validity.
   It composes the input checks with the block's flags, and with the header, transaction and block checks.
   DogeLib has none of `ConnectBlock`, `CheckTransaction`, `ContextualCheckBlock` or a UTXO set.
   Design record 0006 excludes `ContextualCheckBlock`.
   The block-level step from a Script-local theorem is then a conjunction over inputs, with the same flags on both sides.
2. **Activation.** A theorem that the block-level map from context to `active` is false below the activation point, and monotone above it.
   For the fixed-height model of section 7.2, both facts follow from the definition.
3. **Legacy projection.** A statement of what a baseline node receives, and a proof that the state effects agree.

With those parts, the claim has this shape:

```text
∀ act state block,
  revisedBlockValid act state block →
    baselineBlockValid (π state) (π block) ∧
    π (revisedApply act state block) = baselineApply (π state) (π block)
```

An induction along the chain then gives the claim for chains.
The claim is about validity only.
It says nothing about convergence or liveness of the network, as [CONTRIBUTING.md](../../CONTRIBUTING.md#optimizations-and-protocol-revisions) states.
DogeLib cannot state this claim today, because none of `revisedBlockValid`, `baselineBlockValid` or `baselineApply` exists.

### 8.4 Legacy projection

Design record 0001 did not define the term.
The record proposes this candidate definition.

A *legacy projection* for a revision is a pair of functions `π`.
One maps each message of the revised protocol, such as a block or a transaction, to the message that a baseline node receives.
The other maps the chain state of a revised node to that of a baseline node.
The full claim of section 8.3 uses both.

A revision that changes no encoding and no state effect has the identity as its projection.
A NOP redefinition is such a revision: the transaction bytes are the same, and a successful step leaves the same state (section 6.1).
SegWit is the standard example of a revision with another projection: a baseline node receives a block without witness data.

The record recommends the identity projection for every revision that keeps encodings and state effects.
A non-identity projection waits for the first proposal that needs one, and that proposal's record defines it.

### 8.5 Other classes

A revision that is not a soft fork is labelled by what it is, and gets no soft-fork theorem:

- A *relaxation* (a hard fork that only adds acceptance) proves `B ctx = accepted → R true ctx = accepted`, and a witness where only the revision accepts.
- An *incompatible change* proves a witness in each direction.
- An *unclassified* revision has the inactive equality only.

Every class keeps the inactive equality.

## 9. Evidence

No Core behaviour exists for a proposal, so a Core comparison cannot show that a proposal is correct.
It can still show agreement where the proposal must equal the baseline:

- **Before activation.** The inactive equality makes every baseline comparison apply to the revision with `active = false`, with the same limits.
- **Outside the redefined rule.** A congruence theorem says that the active revision equals the baseline on every script with no instruction that the revision redefines. The baseline comparison then applies to those scripts too.

Both arguments are theorems about DogeLib's definitions, together with the existing comparison evidence of the baseline.
No additional comparison run is needed for them.

Where the redefined rule runs, the evidence is:

1. The characterization and the witnesses of section 8.1.
2. Known answers through the compiled code, with expected values derived by hand from the proposal's text.
3. Vectors from the pinned external document, when it has any, with their provenance.
4. Mutations on each side of every new rejection.

A value that DogeLib computes is never an expected value for DogeLib.
A comparison with another implementation of a proposal, such as a patched Core build at a pinned commit, is a separate kind of evidence.
COVERAGE.md labels it as a comparison with that implementation, never as a Core comparison.

**Oracle.**
The record recommends no proposal operation in the oracle during 0.x.
The `Exports` library stays baseline-only, and the import check of section 4 enforces that.
A later decision can add a `ProposalExports` library with operations under a `proposal.<name>.` prefix, under the [development policy](../oracle.md#format-stability).
That decision is useful once a proposal has an independent implementation to compare.

**Known answers.**
Proposal known answers go in a topic module under `tests/KnownAnswers/Proposals/`, with their own named check list.
The `known-answers` executable may import `Proposals`, because it is not a baseline library.

## 10. Worked example

The example exercises the framework from end to end at the input level, with existing infrastructure only.
No one proposes it for Dogecoin, and its name says so.

### 10.1 The rule

The proposal `DogeLib.Proposals.ExampleVersionVerify` redefines `OP_NOP10` (`0xb9`) in the shape of `OP_CHECKLOCKTIMEVERIFY`.
With `active` true and the opcode executed, it checks in this order:

1. An empty stack gives `INVALID_STACK_OPERATION`.
2. The top item is a five-byte `CScriptNum` without the minimal requirement, as for `OP_CHECKLOCKTIMEVERIFY`. A failed decode gives `UNKNOWN_ERROR`.
3. A negative operand gives the proposal error `negativeOperand`.
4. The transaction's version, read as an unsigned 32-bit value, must be at least the operand. Otherwise the proposal error is `versionTooLow`.
5. Without a transaction context, the result is unsupported, as for the lock-time opcodes without a checker.

The opcode never pops its operand.
With `active` false, or in a branch that does not execute, `OP_NOP10` stays a NOP.

The rule reads the transaction through a proposal context, not through `SignatureChecker`.
The baseline checker type does not change.
`verifyLegacySpend` already holds the transaction in `InputContext`, and the revised spend predicate builds the proposal context from it.

### 10.2 The step

The revised step runs the baseline `evalInstruction` first.
Suppose that the result is `next t`, the instruction is `OP_NOP10`, the branch executes and `active` is true.
Then the step applies the checks of section 10.1 to `t`.
Every other result passes unchanged.

The baseline NOP changes only the opcode count, so the stack of `t` is the stack before the instruction.
The checks either return `next t` or fail.
So the step restricts the baseline step by construction, and the soft-fork theorem follows from section 6.1.

The order of errors has one difference from an implementation inside Core's `switch`.
The baseline step checks the stack size after the opcode.
A caller's initial stack of more than 1,000 items can therefore give `STACK_SIZE` before the example's own error.
After the first instruction, the stack size check of the previous instruction excludes that case.
The difference changes an error, never acceptance.

### 10.3 Targets

| Target | Statement |
| --- | --- |
| `exampleStep_restricts` | The example step restricts the baseline step, for every `active`, context and flag set. |
| `example_inactive_eq` | With `active` false, the revised `verifyScript` equals the embedded baseline result, for every checker, flags and scripts. |
| `example_soft_fork_local` | If the revised spend predicate accepts an input, `verifyLegacySpend` accepts it with the same flags and verifier. Script-local. |
| `example_eq_of_no_nop10` | If neither script, nor the P2SH redeem script, contains an instruction with opcode `0xb9`, the revised result equals the embedded baseline result for every `active`. |
| `example_strict` | A known transaction and scripts exist that the baseline accepts and the active revision rejects with `versionTooLow`. |
| `example_use` | A known transaction and scripts exist that the active revision accepts with an executed `OP_NOP10`. |
| `example_accepted_iff` | Let a script be a push of `n`, then `OP_NOP10`, then a script `S`. The active revision accepts exactly when the baseline accepts and `0 ≤ n ≤ version`, with `n` the decoded operand. |

The record leaves the exact domain of `example_accepted_iff` to stage 2.
That domain must state how the operand decodes, and whether `S` can reach `OP_NOP10` again.

Known answers cover each step of section 10.1 and both sides of the version comparison.
They also cover a negative operand, a six-byte operand, an operand in a branch that does not execute, and `active` false.

## 11. Theorem targets of the framework

The names below are proposals.
Each theorem states its domain and hypotheses in its doc comment.

| Target | Statement |
| --- | --- |
| `evalLoopWith_baseline` | `evalLoopWith` with the baseline step equals `evalLoop`, for every checker, flags, script and state. |
| `evalScriptWith_baseline`, `verifyScriptWith_baseline` | The same for `evalScript` and `verifyScript`. |
| `evalLoopWith_restricts` | If `step₁` restricts `step₀` and `evalLoopWith step₁` returns `ok t`, then `evalLoopWith step₀` returns `ok t`. |
| `verifyScriptWith_restricts` | If `step₁` restricts `step₀` and `verifyScriptWith step₁` accepts, then `verifyScriptWith step₀` accepts. |
| `evalLoopWith_congr` | Two steps that agree on every instruction whose opcode lies outside a set `O` give equal results on a script with no instruction in `O`. |
| `Activation.isActive_mono` | If an activation is active at height `h` on a network, it is active at every greater height on that network. |
| `Activation.none_inactive` | An activation with no height on a network is inactive at every height on it. |
| `checkBlockHeader_not_versionBitsCondition` | On mainnet and regtest, a header that `Block.checkBlockHeader` accepts does not meet Core's `Condition` for any deployment bit (section 3, fact 3). |

The last target is a baseline property, and it belongs to the `Proofs` library.
It needs a definition of `Condition`, which stage 1 adds to the baseline only if the maintainer accepts it there (decision 11).

No target assumes a cryptographic property.
The framework adds no axiom and no trust assumption.
A proposal's theorems are about DogeLib's definitions, and SOUNDNESS.md records no gap for a proposal beyond those of the baseline definitions that it reuses.

## 12. Stages and exit conditions

### Stage 1: the framework

The stage adds the `Proposals` and `ProposalProofs` libraries, the `Activation` model and the framework Script loop.
It extends the import check and the roots of `check-decls`, and it adds the sections of ARCHITECTURE.md, COVERAGE.md and SOURCES.md.

The stage exits with these results:

- The framework targets of section 11, except `checkBlockHeader_not_versionBitsCondition` unless decision 11 accepts it.
- A self-test of the import check: a planted import of `DogeLib.Proposals` into a baseline module fails the check.
- `lake exe check-decls` reaches every proposal module.

### Stage 2: the worked example

The stage adds `ExampleVersionVerify`, its targets of section 10.3 and its known answers.

The stage exits with these results:

- Every target of section 10.3, with `example_soft_fork_local` labelled Script-local in COVERAGE.md.
- Known answers through the compiled code, with hand-derived expected values.

### Later work

The full soft-fork claim of section 8.3 waits for a record that scopes block validity.
A signalling activation waits for a record that follows section 7.4.
Neither is part of this scope.

## 13. Decisions

**Date:** none yet. **Decision maker:** Maintainer.
Each proposal below is open:

| Number | Topic | Proposal | Status |
| --- | --- | --- | --- |
| 1 | Location | Option L2: the libraries `Proposals` and `ProposalProofs` in the root package, rooted under `DogeLib.Proposals` (section 4). Option L3 stays available for a proposal that needs an excluded dependency. | Open |
| 2 | Enforcement | Add the prefix `DogeLib.Proposals` to the import check of `scripts/CheckRefinementImports.lean`, and add the proposal roots to `check-decls` (section 4). | Open |
| 3 | Revised definitions | Option M2: a Script loop with a step parameter in the proposal library, pinned to the baseline by agreement theorems. No baseline file changes (section 6). | Open |
| 4 | Activation | An explicit `active : Bool` at the rule level, and one optional activation height per network at the block level, with no default value. No signalling model now (section 7). | Open |
| 5 | Compatibility classes | Inactive equality for every proposal. A soft fork adds restriction of acceptance, a strictness witness and a use witness. The labels Script-local and header-local, and the classes relaxation, incompatible and unclassified (section 8). | Open |
| 6 | Legacy projection | The candidate definition of section 8.4, with the identity for revisions that keep encodings and state effects. A non-identity projection waits for the first proposal that needs one. | Open |
| 7 | Identity | `DogeLib.Proposals.<Name>` with a descriptive name, external documents in a SOURCES.md table with identifiers `P1` on, and a separate COVERAGE.md section. The Lean definition is the object of every claim (section 5). | Open |
| 8 | Oracle | No proposal operation in 0.x. `Exports` stays baseline-only. A later decision can add a `ProposalExports` library (section 9). | Open |
| 9 | Worked example | `ExampleVersionVerify` on `OP_NOP10`, kept in the `Proposals` library as a permanent test of the framework, with documentation that says it is not a proposal (section 10). | Open |
| 10 | Errors | A generic error type in the framework loop. A proposal uses the sum of `ScriptError` and its own errors (section 6.2). | Open |
| 11 | Version-bit condition | Add Core's `Condition` to the baseline with the theorem `checkBlockHeader_not_versionBitsCondition`, or defer both to a signalling record (section 11). | Open |

## 14. Remaining risks

| Risk | Mitigation |
| --- | --- |
| A baseline module imports a proposal, and a proposal changes a baseline result. | The import check of decision 2, and its self-test in stage 1. |
| The framework copy of the loop differs from the baseline loop. | The agreement theorems of section 11. A change to the baseline loop that the copy does not follow fails the build. |
| A soft-fork theorem holds for a revision that rejects everything, or that changes nothing. | The strictness and use witnesses of section 8.1, and the characterization. |
| A Script-local theorem is reported as a soft-fork proof of the network. | The labels of section 8.2 in COVERAGE.md and in the module documentation. Section 8.3 lists the missing obligations. |
| An external document disagrees with the Lean definition. | The list of known differences in the module documentation, and the rule for disagreeing sources (section 5). |
| A proposal takes a free flag bit that a later Core release assigns. | The explicit `active` argument of section 7.1. |
| The example's error order differs from a Core implementation for a caller's stack above 1,000 items. | Section 10.2 states the difference. It changes an error, not acceptance. A real proposal states its own order in its text. |
| Fact 3 of section 3 is wrong, so a version-bit deployment can lock in on mainnet at the pin. | The fact is an inference from source inspection. Decision 11 proposes a theorem for it. The fixed-height model does not depend on it. |
| A proposal needs a dependency that the root package excludes. | Option L3, under a separate maintainer decision. |

There is no pin change, trust-policy exception or fixture-format change in this record.
Adoption of the record does not establish any target theorem, and it does not authorize the merge of a later implementation.
