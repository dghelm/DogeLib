# DogeLib in practice

This guide shows how to use DogeLib for security work on Dogecoin and to check a proposed revision of its rules.
Each section has a worked example.
A theorem, a known answer or a command that you can run supports each example.
[SOUNDNESS.md](../SOUNDNESS.md) states what each theorem assumes, and [COVERAGE.md](../COVERAGE.md) lists the evidence for each operation.

The guide describes methods, not a plan of work.
It does not report a new finding.

## Two questions

Security work on a consensus rule asks two different questions:

1. Does the implementation behave as the specification says?
2. Does the specified behaviour give the safety property that we want?

DogeLib answers the first question with three kinds of evidence:

- Comparisons with Dogecoin Core run the oracle and Core's own code at the pinned revision on the same requests ([docs/oracle.md](oracle.md#the-core-harness)).
- Known answers from independent sources run through the compiled specification (`lake test`).
- Refinement theorems relate another implementation to the specification, such as `decode_refines` for the Rust CompactSize reader ([SOUNDNESS.md](../SOUNDNESS.md#rust-bounded-compactsize-reader)).

These kinds of evidence compare two descriptions of the same rule.
So agreement between Lean and Core is a compatibility claim, not a safety property.
Lean and Core can agree on a rule that is unsafe.

The second question needs a property that you state independently of the rule.
For example, `multisigRecovery_sound_coreVerifier` states a property of the multisig-with-recovery template.
Under the hypotheses of `MultisigRecoverySpend`, an accepted spend satisfies the ordinary branch or the recovery branch ([worked property](../SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
The [README](../README.md#try-it) runs one signed spend of that template through the oracle, and Core's recorded verdict for it is also `OK`.
The comparison answers the first question for that spend.
The theorem answers the second question for every spend in its domain.

The three activities give different information when they fail:

| Activity | Question | A failure means |
| --- | --- | --- |
| Comparison with Core | Do Lean and Core give the same result on this input? | A disagreement to investigate: the Lean model, the C++ code, the harness or an assumption can be wrong |
| Property check | Does this behaviour satisfy the stated property? | The property is false for this input, or its input domain needs a correction |
| Lean proof | Does the property hold on every input in its domain? | Nothing by itself: a proof attempt that does not succeed is not evidence of a bug |

The sections below apply these activities to a proposed revision, to a known property of the baseline and to a comparison with Core.

## Vetting a proposed soft fork: a planted fault

A *soft fork* only restricts acceptance: every input that the revised rules accept, the baseline rules also accept.
[Design record 0007](design/0007-proposed-revisions.md) gives DogeLib's framework for this claim.
This section applies the framework to an invented rule with a deliberate fault.
The rule is in `DogeLib.Proposals.ExampleFaultyLocktime`, and it is not a proposal for Dogecoin.

### The rule

At the pin, `OP_NOP4` (`0xb3`) does nothing.
Core's `EvalScript` gives an error for it only with the flag `SCRIPT_VERIFY_DISCOURAGE_UPGRADABLE_NOPS` (SOURCES.md D3, `src/script/interpreter.cpp`, lines 429 to 435).
`OP_CHECKLOCKTIMEVERIFY` is `OP_NOP2`, and `OP_CHECKSEQUENCEVERIFY` is `OP_NOP3`, so `OP_NOP4` is free.

The invented rule makes `OP_NOP4` a lock-time check with the checks and errors of `OP_CHECKLOCKTIMEVERIFY` (D3, lines 360 to 390).
The module has two variants of the rule:

- `Variant.faulty` pops the operand after a successful check. This pop is the planted fault.
- `Variant.corrected` keeps the operand on the stack, as `OP_CHECKLOCKTIMEVERIFY` does.

Both variants take `active : Bool`.
With `active` false, or in a branch that does not execute, `OP_NOP4` stays a NOP.

### The counterexample

The counterexample is the previous `scriptPubKey` `51 52 b3 51 87`, that is, `OP_1 OP_2 OP_NOP4 OP_1 OP_EQUAL`.
The spending transaction has `nLockTime` 2 and one input with `nSequence` `0xfffffffe` and an empty `scriptSig`.
The flags are 0, so the flag that discourages upgradable NOPs is clear.

The operand 2 and the lock time 2 both lie below 500,000,000, 2 ≤ 2, and the sequence is not final.
So the lock-time check passes.
The stacks list their items from the bottom to the top:

| Step | Baseline: `OP_NOP4` is a NOP | Faulty rule |
| --- | --- | --- |
| `OP_1`, `OP_2` | `[1, 2]` | `[1, 2]` |
| `OP_NOP4` | `[1, 2]` | The check passes and pops 2: `[1]` |
| `OP_1` | `[1, 2, 1]` | `[1, 1]` |
| `OP_EQUAL` | `[1, false]` | `[true]` |
| Result | Rejected with `EVAL_FALSE` | Accepted |

The faulty rule accepts a spend that the baseline rejects, so it is not a soft fork.

`faulty_counterexample` proves both results for the Lean definitions:

```lean
theorem faulty_counterexample :
    baselineSpend (spendArgs 2 counterexampleScript) = .rejected .evalFalse ∧
      revisedSpend .faulty true (spendArgs 2 counterexampleScript) = .accepted
```

The baseline verdict is Core's verdict too.
The commands below send the counterexample, and a lock-time spend that the next subsection uses, to the oracle and to the Core harness:

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
tx=0100000001$(printf '00%.0s' $(seq 32))ffffffff00feffffff0002000000
for script in 5152b35187 0102b37551; do
  printf '{"id":"%s","op":"script.verify_legacy","tx_hex":"%s","input_index":0,"prevout_script_hex":"%s","flags":0,"checker":"transaction"}\n' \
    "$script" "$tx" "$script"
done > requests.jsonl
.lake/build/bin/dogelib-oracle < requests.jsonl
build/core-harness/core-oracle < requests.jsonl
```

`tx` is the spending transaction: version 1, one input with a null outpoint, no outputs and lock time 2.
Both programs reject `5152b35187` with `EVAL_FALSE` and accept `0102b37551` with `OK`.
The oracle has no operation for a proposal (design record 0007, section 9).
The test executable `proposal-replay` runs the revised rule on the same requests, and Core never runs it:

```bash
lake build proposal-replay
.lake/build/bin/proposal-replay ExampleFaultyLocktime faulty --active < requests.jsonl
```

The active faulty rule accepts `5152b35187` and rejects `0102b37551` with `INVALID_STACK_OPERATION`.
The campaign uses this program to search for the counterexample without the hand-written case ([docs/oracle.md](oracle.md#the-planted-proposal-search)).

### The theorems that refute the claim

The framework gives the soft-fork requirement a precise form.
`RestrictsAcceptance` says that for every `active` and every input, if the revision accepts, the baseline accepts.
`SoftFork` needs that property and three more, which the next subsection lists.

These theorems in `DogeLib.Proposals.ExampleFaultyLocktime.Proofs.Witnesses` refute the claim for the faulty rule:

- `faulty_not_restrictsAcceptance`: the faulty spend predicate does not restrict acceptance. The counterexample is the witness.
- `faulty_not_softFork`: for every use predicate, the faulty spend predicate is not a `SoftFork` of `verifyLegacySpend`.
- `faulty_incompatible`: the faulty rule is an `Incompatible` change. It also rejects a spend that the baseline accepts (`faulty_strict`), so it changes acceptance in both directions.

The fault is visible before any script runs.
`Restricts step₁ step₀` says that every successful step of `step₁` is a successful step of `step₀` with the same state.
A restricting step can reject where the baseline step succeeds, but it cannot change the state of a success.
The faulty step succeeds at `OP_NOP4` with the stack `[1]`, and the baseline step succeeds with `[1, 2]` (`faultyStep_pops`).
So `faultyStep_not_restricts` proves that the faulty step does not restrict the baseline step.

### The corrected rule

The corrected rule keeps the operand.
`correctedStep_restricts` proves that its step restricts the baseline step, for every `active`, checker and flag set.
The framework theorem `verifyScript_of_restricts` then lifts that step property through `scriptSig`, `scriptPubKey` and the P2SH redeem script.

`corrected_softFork` proves the four requirements of `SoftFork` for the corrected spend predicate.
Each requirement of a soft fork has a statement in the framework and a theorem in the example:

| Requirement | Framework statement | Theorem for the corrected rule |
| --- | --- | --- |
| Before activation, the results equal the baseline results | `InactiveEq`: with `active` false, every result equals the baseline result, including each rejection and each unsupported result | `inactiveEq .corrected` |
| If the revision accepts, the baseline accepts | `RestrictsAcceptance`, for every `active` and input | `corrected_restrictsAcceptance` |
| After activation, the rule is enforced | `StrictnessWitness`: an input that the baseline accepts and the active revision rejects | `corrected_strict`: `0102b37551` with lock time 1 gives `UNSATISFIED_LOCKTIME` |
| The intended construction works | `UseWitness`: an input that the active revision accepts, on which the redefined rule runs | `corrected_use`: `0102b37551` with lock time 2 is accepted |

The two witnesses are necessary.
A rule that rejects every input satisfies `RestrictsAcceptance`, so it is safe only because it cannot be used.
The use witness excludes that case.
The faulty rule also breaks the usual lock-time construction `<n> OP_NOP4 OP_DROP`.
It rejects `0102b37551` with lock time 2, because the pop leaves an empty stack for `OP_DROP` (a known answer in `tests/KnownAnswers/Proposals/ExampleFaultyLocktime.lean`).

Activation has two levels in the framework.
At the rule level, each theorem holds for every value of `active`, so it holds whatever the activation mechanism is.
At the block level, `Activation` gives each network one activation height or none.
`Activation.isActive_lt` and `Activation.isActive_mono` prove that the activation is false below that height and monotone above it ([SOUNDNESS.md](../SOUNDNESS.md#proposed-revisions-the-framework)).
The example defines no `Activation` value, because no network activates it.

### What the example establishes

Every theorem of the example is *Script-local*: it is about one call of `verifyScript` or `verifyLegacySpend`.
A soft-fork claim about the network also needs block validity and a legacy projection, which DogeLib does not have (design record 0007, section 8.3).

The known answers run both variants through the compiled code on 13 `verifyScript` cases and 4 spends.
A person derived each expected result by hand from Core's rules.
`lake test` prints this line for them:

```text
ExampleFaultyLocktime: 13 verifyScript cases and 4 spend cases, 0 failures
```

The module is also a test of the framework: if a change to the framework stops it from refuting the faulty rule, the build fails.

## A property that the baseline violates: the duplicate Merkle leaf

The first question asks whether DogeLib agrees with Core.
A safety property can fail even where the two agree.
The Merkle root of a block's transactions is an example.

A reader can expect that two different lists of transaction IDs give different Merkle roots, unless double SHA-256 has a collision.
Core's Merkle tree does not have this property.
When a level has an odd number of hashes, Core pairs the last hash with itself.
So the lists `[A, B, C]` and `[A, B, C, C]` have the same root, with no collision.

The equal roots are a known historical issue, CVE-2012-2459, and they are not a finding of DogeLib.
The comment at the top of Core's `src/consensus/merkle.cpp` describes it (D42).

### The theorem

`computeMerkleRoot_duplicate_last` in `DogeLib.Block.Proofs.Merkle` states the property for the Lean definitions:

```lean
theorem computeMerkleRoot_duplicate_last (pre : List Hash256) (last : Hash256) (ne : pre ≠ [])
    (even : pre.length % 2 = 0) :
    computeMerkleRoot (pre ++ [last, last]) = ⟨(computeMerkleRoot (pre ++ [last])).root, true⟩
```

For every nonempty prefix of even length, the list with its last leaf repeated has the same root, and it sets the mutation flag.
The proof uses two lemmas of the same module:

- `merkleLevel_duplicate_last`: the next level is the same before and after the duplication of the unpaired last leaf.
- `merkleMutated_of_equal`: an equal aligned pair of leaves sets the mutation flag.

### The known answer and the comparison

`tests/block/merkle.json` comes from the deterministic cases of Core's `merkle_tests.cpp` (D43).
Python `hashlib` computed its roots independently of DogeLib ([tests/block/README.md](../tests/block/README.md#deterministic-merkle-cases)).
Its rows with `count` 3 have 3 leaves (`mutation` 0) and 4 leaves (`mutation` 1).
Both rows have the root `967096e98e166e9f3eacbc287fdd6e177dc9de06795a47051b882abcfa35ee92` in display order.
The first row has `mutated` false, and the second has `mutated` true.
`lake test` checks both rows through the compiled code.

The oracle operation `merkle.compute` gives the same result for any leaves.
With the Core harness of the previous section, these commands send two requests to both programs:

```bash
a=$(printf '11%.0s' $(seq 32)); b=$(printf '22%.0s' $(seq 32)); c=$(printf '33%.0s' $(seq 32))
printf '{"id":"abc","op":"merkle.compute","leaves_hex":["%s","%s","%s"]}\n' "$a" "$b" "$c" > merkle.jsonl
printf '{"id":"abcc","op":"merkle.compute","leaves_hex":["%s","%s","%s","%s"]}\n' "$a" "$b" "$c" "$c" >> merkle.jsonl
.lake/build/bin/dogelib-oracle < merkle.jsonl
build/core-harness/core-oracle < merkle.jsonl
```

Both programs return the internal-order root `cacd895c5e82f37a37b6f4923c214ca6089e5f7b075b9fca7e11e782a0f3f5e6` for both requests.
They return `mutated` false for `abc` and true for `abcc`.
So Lean and Core agree, and the agreement shows nothing about the safety of the rule.

### What protects the block

Core does not make the roots different.
Instead, `CheckBlock` rejects a block whose computation sets the mutation flag, with the reason `bad-txns-duplicate` (D90, `src/validation.cpp`, lines 2951 to 2962).
DogeLib does not specify `CheckBlock`, so no DogeLib theorem states that a validator rejects such a block.
A model of block validity could state that property and prove it.

The theorem above is about one duplicated leaf.
Core's comment gives a second shape, in which the last two leaves of six repeat.
`computeMerkleRoot_duplicate_last` does not cover that shape.

## Comparing with Core and reading a disagreement

[BUILDING.md](../BUILDING.md#comparison-with-dogecoin-core) gives the commands of the full comparison, and [docs/oracle.md](oracle.md#the-comparison) describes its streams:

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle
python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

`scripts/compare_core.py` sends the same requests to both programs and requires their responses to agree.
`scripts/test_compare_core.py` checks that the comparison can fail.

Wrappers around the oracle stand in for the programs, and the self-test runs the comparison once for each mutation.
A mutation changes the responses or the behaviour of the wrapper on the Core side, on the oracle side or on both sides.
Some mutations change one response field, and others drop, add or corrupt a response, change the format version, exit early or stop answering.
Each mutation must fail the comparison with the failure code that it targets, such as `MISMATCH`, `EXIT` or `TIMEOUT`.
Run the self-test to see the report of a disagreement.

### What a disagreement can mean

A disagreement shows that two programs differ on one input.
It does not say which program is wrong.
Investigate each of these causes:

- The Lean model is wrong, for example because it makes a consensus quirk of Core regular. Compare the definition with the source that SOURCES.md records for it.
- Core's C++ code does something that the source review of the definition missed, for example undefined behaviour or an integer wrap.
- The harness is wrong. It converts JSON to Core's types, and it can transcribe Core's code (see below).
- The request violates a precondition that Core's callers maintain. Core can assert, or behave differently, on such an input.
- The operation is unsupported in Lean. The oracle reports `unsupported`, and the comparator counts that request separately, as neither agreement nor disagreement.
- The disagreement comes from undefined behaviour or an unrelated detail of the C++ code. CONTRIBUTING.md says that such a case "is not a protocol requirement", and that you document it and "decide the intended contract explicitly" ([sources of truth](../CONTRIBUTING.md#sources-of-truth)). A correction of the model there is not automatically a proposed revision.

### Transcriptions in the harness

For most operations, the harness calls Core's own function.
`block.contextual_check` and `block.header_sequence` are different.
For these operations the harness runs transcriptions that call Core's helpers, option H2 of design records 0006 and 0008:

- `block.contextual_check` transcribes `ContextualCheckBlockHeader` ([evidence](oracle.md#contextual-header-comparison-evidence)).
- `block.header_sequence` transcribes `AcceptBlockHeader`, the index part of `AddToBlockIndex` and the loop of `ProcessNewBlockHeaders` ([evidence](oracle.md#header-sequence-comparison-evidence)).

A transcription can have a mistake that the specification shares.
It can also have a mistake that Core does not have.
So a disagreement on these operations is not evidence of a Core bug.
Before you report a suspected Core bug there, replay the input against the production function in `src/validation.cpp`, or against a node.
Also check whether a later Core release changes the behaviour, because the pin is Core v1.14.9.

## What a theorem does and does not establish

A theorem establishes a claim about the Lean definitions, under its hypotheses and on its input domain:

- A theorem about a model is not a theorem about the compiled C++ code. The link to Core is source review and finite comparison ([SOUNDNESS.md](../SOUNDNESS.md#a1-a-wrong-definition)).
- A finite comparison covers its requests and no other inputs. It never becomes a proof for all inputs.
- A statement about a signature preimage, such as "the preimage commits to the lock time", is not a cryptographic security claim. A security claim also needs an assumption about the hash and the signature scheme, and DogeLib has no such theorem ([SOUNDNESS.md](../SOUNDNESS.md#a4-idealisations)).
- A Script-local theorem about a proposal is not a claim about the network (design record 0007, section 8.3).

## Further directions

These directions are not implemented, and none of them has an approved scope:

- **Signed-spend campaigns.** A generator could mutate a signed spend in two modes. One mode signs the spend again, so execution should stay successful. The other mode keeps the signature, so it tests what the signature commits to.
- **Replay and shrinking.** The comparator could save each failing request with both responses and both revisions. A command could then replay the request and reduce it to a small input that still fails.
- **Resource bounds for proposals.** A proposal record could state a bound on the work of validation, such as the number of bytes hashed. The bound would be a claim beside compatibility, strictness and use.
- **Transaction and UTXO validation.** A model of `CheckTransaction`, of the UTXO set and of value accounting could state properties such as "no block spends one outpoint twice". Properties of this kind, the class of CVE-2018-17144, need such a model, because per-input Script verification does not describe them. At the pin, `CheckBlock` calls `CheckTransaction` with its duplicate-input check enabled (D90, lines 551 to 559 and 2984).
