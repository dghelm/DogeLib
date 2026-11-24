# Architecture

This document describes the intended structure of DogeLib.
It follows EthLib's [`ARCHITECTURE.md`](https://github.com/ethereum/EthLib/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/ARCHITECTURE.md).
Where EthLib and btc-verified differ, DogeLib follows EthLib.
[BUILDING.md](BUILDING.md) says how to build it.

## Three kinds of content

DogeLib holds three kinds of Lean code, and they answer different questions.

A **specification** says what Dogecoin computes.
It is executable, pure and total, and it follows its source by definition.
Clients and other Lean projects import it, and the oracle runs it.

A **property** says what a specification guarantees.
Round trips of encodings, the rejection of malformed input, exact commitment bytes and agreement between two definitions are all properties.
They are stated about the specification itself, the same definitions that the compiled code is built from. [SOUNDNESS.md](SOUNDNESS.md#gap-b-does-the-code-that-runs-match-the-definitions), Gap B, lists what a user trusts between those definitions and the running code.

A **model** says why the protocol is secure, or how a network of nodes behaves.
It is abstract where the specification is concrete: a hash becomes a random oracle, and a network becomes an adversary that schedules messages.
A model connects to the specification by a refinement theorem, which says that the concrete definition is an instance of the abstract one.
Without that theorem, the security proof is about a different object than the one clients run.
DogeLib has no model yet. One is added when a concrete theorem needs it.

Each kind depends only on the kinds before it.
A specification never imports a property or a model, and a property never imports a model.

A fourth kind of code relates another implementation to the specification:
a refinement theorem about a packed codec, a streaming preimage constructor, or extracted Rust.
The implementation never becomes the specification.

## Lake libraries

| Library | Contents | `precompileModules` |
| --- | --- | --- |
| `DogeLib` | The specification | On |
| `Proofs` | Properties, rooted at each layer's `Proofs` tree | Off |
| `Exports` | The oracle, `dogelib-oracle`, and later binding-facing code | Off: with it on, Lake reports a build cycle, because the library contains the executable's root module |
| `Proposals` | Proposed revisions of the baseline and the framework that states them, rooted at `DogeLib.Proposals` | Off |
| `ProposalProofs` | Properties of the proposed revisions, rooted at `DogeLib.Proposals.Proofs` and each proof tree under `DogeLib/Proposals/` | Off |
| `ProposalExports` | The operations of the proposal executable, `dogelib-proposal-oracle`, rooted at `DogeLib.Proposals.Exports` | Off |
| `Refinement` | Extracted Rust implementation models and their refinement proofs. Imports the pinned Aeneas backend and Mathlib. | Off |
| `check-decls` | An executable that checks the axioms and substitutions of every compiled declaration | — |
| `dogelib-proposal-oracle` | The proposal executable: every operation of `dogelib-oracle`, plus `block.validate` and `block.contextual_check_body` with the argument `revision`. It names only proposed revisions (`RelativeLockTime`). Its entry point is `scripts/ProposalOracle.lean`, and its other definitions are in `ProposalExports`. | — |
| `ProposalExamples` | Test-only. The two examples of the proposal framework, `ExampleFaultyLocktime` and `ExampleVersionVerify`, with their theorems and the revisions of `proposal-test-oracle`, rooted at `ProposalExamples` under `tests/` | Off |
| `proposal-test-oracle` | The test build of the proposal executable: the code of `dogelib-proposal-oracle`, whose argument `revision` also names the two examples. Its entry point is `tests/ProposalTestOracle.lean`. | — |
| `proposal-replay` | A test executable that answers `script.verify_legacy` requests with the example `ExampleFaultyLocktime`, for the campaign's planted-fault search. It imports `Exports`, `Proposals` and `ProposalExamples`, and no library imports it. | — |

Each library uses the Lean module system (`requiresModuleSystem := true`), as EthLib does.
Proofs live in their own library, so the specification builds and links without them.
The oracle lives in `Exports`, so a Lean project that imports the specification gets no IO adapter.
[docs/oracle.md](docs/oracle.md) defines its record format.

The `Refinement` library belongs to a separate Lake package under `Refinement/`, which requires DogeLib, Aeneas and Mathlib.
The root DogeLib package has no Lake dependencies.
The specification, `Proofs` and `Exports` import neither dependency, and neither do `Proposals`, `ProposalProofs` and `ProposalExports`.
The specification, `Exports` and `ProposalExports` import no module of a proof library.
`scripts/CheckRefinementImports.lean` checks those transitive import boundaries.
Heavy mathematical and probabilistic dependencies stay outside the specification.

## Layout

```text
DogeLib/<Layer>/<Module>             the specification
DogeLib/<Layer>/Proofs/<Module>      theorems about it
DogeLib/<Layer>/Exports/             the oracle adapter for that layer
Refinement/                         optional Lake package
Refinement/Refinement/              extracted Lean models and refinement proofs
Refinement/Rust/                     Rust sources and extraction scripts
tests/<layer>/                       fixtures with recorded provenance
tests/KnownAnswers.lean              the driver that `lake test` runs
tests/KnownAnswers/                  known answers by topic and shared fixture readers
tests/KnownAnswers/Proposals/        known answers of the proposed-revisions library
tests/ProposalReplay.lean            the test executable proposal-replay
tests/ProposalExamples/              the test-only examples of the proposal framework
tests/ProposalTestOracle.lean        the test executable proposal-test-oracle
harness/core/                        the Dogecoin Core harness: Core's code on the oracle's requests
scripts/                             repository tools and checks
DogeLib/Proposals/Framework/        the framework for proposed revisions
DogeLib/Proposals/Framework/Proofs/ its theorems
DogeLib/Proposals/<Name>/           the definitions of one proposed revision
DogeLib/Proposals/<Name>/Proofs/    its theorems
DogeLib/Proposals/Exports/          the operations of the proposal executable
scripts/ProposalOracle.lean         the entry point of dogelib-proposal-oracle
```

A new layer adds its proof root to the `Proofs` library and, if it has an adapter, its export root to `Exports`.

`DogeLib/Proofs/TheoremTag.lean` belongs to the `Proofs` library and to no layer.
It defines the attribute `theorem_tag`, which labels a theorem that a document cites as evidence.
The five tags are `property`, `model_agreement`, `refinement`, `characterization` and `witness`.
A proof module imports it with `import` and `meta import`, because Lean runs the attribute when it elaborates the theorem.
A theorem with no tag is unclassified. The theorems of earlier modules have no tags yet.

## Layers

Bottom-up. Each layer imports only the layers above it in this list.

| Layer | Responsibility |
| --- | --- |
| `Base` | Bytes, fixed-width field meanings, endianness, hash representations |
| `Serialization` | Codecs, prefix decoders, CompactSize, counted lists, packed representations |
| `Cryptography` | SHA-1, SHA-256, double SHA-256, HMAC-SHA-256, PBKDF2-HMAC-SHA-256, RIPEMD-160 and Hash160, secp256k1 curve arithmetic, ECDSA verification on scalars, and libsecp256k1's public-key parser |
| `Work` | Proof-of-work arithmetic: 256-bit targets and word models, compact encoding, difficulty retargets, next-work selection, median time past, block proof, and work parameters |
| `Transaction` | Raw transaction types, base and witness-allowed serialization, transaction IDs, legacy signature hashing, `CheckTransaction`, and the legacy signature-operation count |
| `Block` | Pure and full block headers with the AuxPoW payload and check, header proof of work, version gating, contextual parameters, checkpoints, and contextual header validation. Block hashes, transaction Merkle roots, the block-index model, single-step and sequence header acceptance, and chain work. Mainnet block subsidy (with Boost 1.70.0's `mt19937` and `uniform_int`), version bits, block serialization, `CheckBlock`, and `ContextualCheckBlock`. The coin set, `CheckTxInputs`, signature-operation cost, `ConnectBlock`, and `validateBlock` for mainnet blocks. |
| `Script` | The instruction reader of the Script interpreter, the state of one `EvalScript` call, Script numbers (`CScriptNum`) and the truth value of a stack item. The interpreter's errors and flags, and one `EvalScript` call for the opcodes of stages 2 to 4, including the numeric, hash, signature and lock-time opcodes. The encoding checks of signatures and public keys, the signature checker that the evaluator takes as a parameter, and `coreVerifier`, Core's `CPubKey::Verify`. `VerifyScript` without a witness, and the spend predicate of one legacy input. |

`Cryptography.Inverse` and `Cryptography.Jacobian` support `Cryptography.Secp256k1.Field`, `Curve` and `Ecdsa`.
These specification modules adapt EthLib's arithmetic with Lean core as their only external dependency.
`Ecdsa.verify` consumes coordinates, scalars and `Base.Hash256` directly.
`Cryptography.Secp256k1.PubKey` holds `parsePubKey`, the byte-level key parser of libsecp256k1, written from Core's source.
The curve layer has no Script dependency.
The proof library adds one kernel-checked ECDSA known answer and no Mathlib dependency.

`Script` imports `Transaction`, because the interpreter and the legacy signature serializer share one instruction reader, `Transaction.readOp`.
`Script.Eval` also imports the hash definitions of `Cryptography` for the hash opcodes.
`Script.Signature` imports `Transaction.legacySignatureHash` for `transactionChecker`. It takes the elliptic-curve check as a parameter and does no elliptic-curve arithmetic.
`Transaction` never imports `Script`.

`Script.CoreVerifier` imports `Cryptography.Secp256k1.PubKey` and `Script.Signature`.
It composes `isValidPubKey`, `parsePubKey`, `parseDerLax` and `Ecdsa.verify` into `coreVerifier`, an instance of the verifier parameter of `transactionChecker`.

`Script.Number` imports no other layer.
`Script.SignatureEncoding` imports only the errors and flags of `Script`. It checks bytes and does no elliptic-curve arithmetic.
`Script` has a proof root and an export root.
`DogeLib/Script/Exports/` adapts `script.read_op`, `script.eval`, `pubkey.verify`, and `script.verify_legacy` to the [oracle format](docs/oracle.md).

Ledger, Rules and Models layers are added when their work begins.

## Proposed revisions

The baseline is the specification of Dogecoin Core at the pin in [SOURCES.md](SOURCES.md).
A *proposed revision* is behaviour intentionally different from the baseline.
[Design record 0007](docs/design/0007-proposed-revisions.md) sets how DogeLib states one and proves its compatibility with the baseline.

Proposed revisions live in three libraries of the root package, `Proposals`, `ProposalProofs` and `ProposalExports`, under `DogeLib.Proposals`.
`Proposals` may import `DogeLib`.
`ProposalProofs` may import `Proposals`, `DogeLib` and `Proofs`.
`ProposalExports` may import `Proposals`, `Exports` and `DogeLib` ([design record 0011](docs/design/0011-mainnet-ranges.md), decision 10).
No module of `DogeLib`, `Proofs` or `Exports` imports one of the three.
So a consumer of the specification gets no proposal code, and no proposal can change a baseline result.

The three libraries hold only proposed revisions.
The examples of the framework are in the test-only library `ProposalExamples`, which no baseline or proposal library imports.
Two checks enforce this direction:

- `scripts/CheckRefinementImports.lean` rejects `DogeLib.Proposals` in the transitive imports of the baseline libraries, and `ProposalExamples` in those of the baseline and proposal libraries. `scripts/test_import_boundaries.sh` plants such an import, of `DogeLib.Proposals` and of `DogeLib.Proposals.Exports` in a baseline module, and of `ProposalExamples` in a proposal module, and requires the failure. It also plants an import of a proof module in a specification module.
- `lake exe check-decls` loads `DogeLib.Proposals`, `DogeLib.Proposals.Proofs` and `DogeLib.Proposals.Exports` among its default roots. It checks every proposal declaration, and it reports a proposal file that the roots do not reach. The test declaration check runs the same check on `ProposalExamples`.

`DogeLib.Proposals.Framework` holds four parts:

- `Framework.Script`: copies of `evalLoop`, `evalScript` and `verifyScript` that take the instruction step as a parameter. They also take the proposal's error type and type of unsupported reasons. Agreement theorems in `ProposalProofs` prove that each copy, with the baseline step, equals its baseline definition. A change to the baseline loop that the copy does not follow fails the build.
- `Framework.Activation`: the activation model. A revised definition takes `active : Bool`, and a block-level `Activation` gives each network one activation height or none.
- `Framework.Compatibility`: the compatibility classes of design record 0007, section 8, and the legacy projection.
- `Framework.Block`: the block level of a proposed revision (design record 0011, section 10.1, and extensions E1 to E4 of design record 0012, section 6.3). `BlockRevision` parameterizes four parts: the spend check, script flags (E1), a non-coinbase transaction test (E2), and `ContextualCheckBlock` lock-time arguments (E3). The outcome types of `txTest` and `connectBlockWith` carry the revision's rejections and unsupported reasons (E4). `connectBlockWith` and `validateBlockWith` return `BlockOutcome` through embedding maps of the baseline errors. Agreement theorems prove that each copy, with the baseline revision, equals its baseline definition.

A proposal lives under `DogeLib.Proposals.<Name>`, and `DogeLib/Proposals.lean` imports it.
Its proof tree is a root of `ProposalProofs`, and `DogeLib/Proposals/Proofs.lean` imports it.
A proposal never gets a row in the baseline tables of [COVERAGE.md](COVERAGE.md), and `dogelib-oracle` has no proposal operation.

The proposal executable `dogelib-proposal-oracle` answers `block.validate` and `block.contextual_check_body` with the argument `revision` ([docs/oracle.md](docs/oracle.md#the-proposal-executable)).
For `block.validate`, `Block.Exports.blockValidateWith` takes an optional hook that adds `revised` to each block record and changes nothing else.
For `block.contextual_check_body`, `ProposalExports` adds `revised` from `contextualBodyWith` without changing the baseline response.
`Exports` defines no hook and names no proposal, and `ProposalExports` supplies each named revision (`RelativeLockTime`).
The test build `proposal-test-oracle` runs the same code with the two test-only examples of `ProposalExamples` added to its revisions.

### Operation boundary: block-level proposals

- Boundary:
  - `Proposals.Framework.Block` runs proposed consensus revisions over the baseline `Block` validation steps.
  - Each named proposal in `Proposals` supplies a `BlockRevision` and error embeddings.
  - No baseline library (`DogeLib`, `Proofs`, or `Exports`) imports `Proposals`, `ProposalProofs`, or `ProposalExports`.
- Owns:
  - `Proposals.Framework` owns `BlockRevision`, `SpendCheck`, `TxTest`, `BlockOutcome`, `ConnectEmbedding`, `ValidateEmbedding`, `Activation`, and `VerifyOutcome`.
  - Baseline `Block`, `Transaction`, and `Script` own `Block`, `Transaction`, `CoinSet`, `Coin`, `ValidateContext`, `ConnectContext`, `ConnectResult`, `InputContext`, `ScriptError`, and `Unsupported`.
- Operations:
  - The spend check evaluates one legacy transaction input against its spent output script and script flags.
  - The script-flags hook returns the verification flags for one block height and activation state.
  - The transaction test checks each non-coinbase transaction after input lookup and before signature-operation counts.
  - The lock-time hook supplies `csvActive` and the median time past to `ContextualCheckBlock`.
  - Baseline defaults leave each unoverridden part identical to the baseline `Block` specification.
- Laws:
  - With the baseline revision, block connection and block validation equal the embedded baseline results for every context and embedding.
  - With `active` false, a revision whose four parts match baseline defaults equals the embedded baseline result.
  - When a revision restricts spend acceptance and matches the P2SH flag, baseline connection accepts every block that revised connection accepts. The resulting coin set and changes match.
  - Under those two connection conditions and a non-greater lock-time cutoff when contextual header checks pass, baseline validation accepts every revised-accepted block.
  - When every entry of a block list meets those two connection conditions, baseline connection accepts any list that revised connection accepts. Both reach the same final coin set.
  - When a revision agrees outside an opcode set and its other hooks match the baseline, a block whose spends are untouched (`BlockUntouched`) gives the embedded baseline outcome. Each spend's `scriptSig`, its spent `scriptPubKey` and, for a pay-to-script-hash spend with a push-only `scriptSig`, its redeem script hold no opcode of the set. The spent coin is in the supplied coin set or created earlier in the block.
  - `ProposalProofs` proves these generic theorems for every signature verifier and embedding. Each proposal proves its own hypotheses.
- Failure:
  - `BlockOutcome` separates acceptance, consensus rejection, and unsupported results outside the model.
  - Embedding maps send baseline rejections to `rejected` and baseline out-of-model or adapter errors to `unsupported`.
  - An unsupported result is never a rejection and says nothing about Dogecoin Core's verdict.
  - When a script check fails and its flags include a non-mandatory flag, it runs again without those flags. If the second run accepts, the rejection is not mandatory, and if it rejects, the rejection is mandatory. Either rejection keeps the error of the first run. If the second run is unsupported, the result is that unsupported result. A failure with no non-mandatory flag is a mandatory rejection at once.
- Guarantees:
  - In an accepted non-genesis block, each non-coinbase transaction found its inputs in the coin set before it. It also passed the transaction test and the script loop.
  - Block-level theorems cover one block (or a supplied list of blocks for connection alone) on a supplied chain view and coin set.
  - They make no claim about chain selection, fork choice, convergence, liveness, or network-wide soft-fork safety.
- Assumes:
  - Every block-level revision inherits the mainnet-only scope and trust boundaries of baseline `Block` validation ([SOUNDNESS.md](SOUNDNESS.md#summary)).
  - The baseline context field `csvActive` keeps its baseline error when true. Revisions set lock-time rules through their own hooks.
  - Signature-operation counts, amount arithmetic, coin-set updates, and header checks follow the baseline without modification.
- Readings:
  - The transaction test runs after input lookup and before signature-operation counts, as in Core's `SequenceLocks` placement ([D114][d114-seqlocks]).
  - The lock-time cutoff selects median time past when `csvActive` is true and block `nTime` otherwise ([D110][d110-cutoff]).
  - Non-mandatory script failures recheck with non-mandatory flags cleared, as in Core's `CheckInputs` ([D114][d114-checkinputs]).

[d110-cutoff]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3128-L3136
[d114-seqlocks]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1948-L1959
[d114-checkinputs]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1462-L1518

### Public proposals

`DogeLib.Proposals.RelativeLockTime` is the proposed revision of [design record 0012](docs/design/0012-relative-lock-time.md): the rules of BIP 68, BIP 112, and BIP 113.
Its transaction test, the sequence locks of BIP 68, is in `DogeLib/Proposals/RelativeLockTime/SequenceLocks.lean`.
Its theorems are under `DogeLib/Proposals/RelativeLockTime/Proofs/`, and its known answers are in `tests/KnownAnswers/Proposals/RelativeLockTime.lean`, `RelativeLockTimeOpcode.lean`, and `RelativeLockTimeSequence.lean`.
DogeLib takes no position on the activation of this proposal.

### Test-only framework examples

The two examples of the framework live in the test-only `ProposalExamples` library under `tests/`, outside the production proposal libraries.
No baseline or proposal library imports `ProposalExamples`, and `dogelib-proposal-oracle` refuses both examples.
The test declaration check (`lake exe check-decls --scope ProposalExamples ...`) checks their declarations, and the second kernel replay (`scripts/replay.sh tests/ProposalExamples`) replays their modules ([AGENTS.md](AGENTS.md#checks)).

- `ProposalExamples.ExampleVersionVerify` is the worked example of design record 0007, section 10. It is not a proposal for Dogecoin. Decision 9 keeps it as a permanent test of the framework.
- `ProposalExamples.ExampleFaultyLocktime` is an invented rule with a deliberate fault, and its corrected variant. It is not a proposal for Dogecoin. It teaches compatibility refutation in [docs/in-practice.md](docs/in-practice.md) and serves as the planted fault for `proposal-replay`.
- `proposal-test-oracle` (`tests/ProposalTestOracle.lean`) runs `dogelib-proposal-oracle`'s code with both examples added for proposal-oracle and short-range impact tests.

## Adopted upstream code

Adapted code follows this layout and the module system. It does not keep the layout of the project it came from.
The btc-verified project keeps definitions, proofs and packed instances in one file, and its generic codec module imports Mathlib.
An adaptation splits those into the specification and `Proofs` libraries.
Each adapted file names its origin and commit in its module docstring and keeps any notice that the upstream terms require.

## Status vocabulary

A module never receives a single "verified" status.
[COVERAGE.md](COVERAGE.md) records each kind of evidence separately for each operation. The kinds are an executable definition, theorems with their hypotheses, comparison evidence, and a proved implementation refinement.
