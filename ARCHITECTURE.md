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
| `Refinement` | Extracted Rust implementation models and their refinement proofs. Imports the pinned Aeneas backend and Mathlib. | Off |
| `check-decls` | An executable that checks the axioms and substitutions of every compiled declaration | — |

Each library uses the Lean module system (`requiresModuleSystem := true`), as EthLib does.
Proofs live in their own library, so the specification builds and links without them.
The oracle lives in `Exports`, so a Lean project that imports the specification gets no IO adapter.
[docs/oracle.md](docs/oracle.md) defines its record format.

The `Refinement` library belongs to a separate Lake package under `Refinement/`, which requires DogeLib, Aeneas and Mathlib.
The root DogeLib package has no Lake dependencies.
The specification, `Proofs` and `Exports` import neither dependency.
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
harness/core/                        the Dogecoin Core harness: Core's code on the oracle's requests
scripts/                             repository tools and checks
```

A new layer adds its proof root to the `Proofs` library and, if it has an adapter, its export root to `Exports`.

## Layers

Bottom-up. Each layer imports only the layers above it in this list.

| Layer | Responsibility |
| --- | --- |
| `Base` | Bytes, fixed-width field meanings, endianness, hash representations |
| `Serialization` | Codecs, prefix decoders, CompactSize, counted lists, packed representations |
| `Cryptography` | SHA-1, SHA-256, double SHA-256, HMAC-SHA-256, RIPEMD-160 and Hash160, and later secp256k1 and signature encodings |
| `Work` | Proof-of-work arithmetic: 256-bit targets, their compact encoding, and the difficulty retarget |
| `Transaction` | Raw transaction types, base serialization, transaction IDs, legacy signature hashing |
| `Block` | Pure block headers, full headers with the AuxPoW payload and their codec, block hashes and transaction Merkle roots |
| `Script` | The instruction reader of the Script interpreter, the state of one `EvalScript` call, Script numbers (`CScriptNum`) and the truth value of a stack item. The interpreter's errors and flags, and one `EvalScript` call for the opcodes of stages 2 to 4, including the numeric, hash, signature and lock-time opcodes. The encoding checks of signatures and public keys, and the signature checker that the evaluator takes as a parameter. `VerifyScript` without a witness, and the spend predicate of one legacy input. |

`Script` imports `Transaction`, because the interpreter and the legacy signature serializer share one instruction reader, `Transaction.readOp`, and later stages hash with `Transaction.legacySignatureHash`.
`Script.Eval` also imports the hash definitions of `Cryptography` for the hash opcodes.
`Script.Signature` imports `Transaction.legacySignatureHash` for `transactionChecker`. It takes the elliptic-curve check as a parameter and does no elliptic-curve arithmetic.
`Transaction` never imports `Script`.

`Script.Number` imports no other layer.
`Script.SignatureEncoding` imports only the errors and flags of `Script`. It checks bytes and does no elliptic-curve arithmetic.
`Script` has a proof root and an export root.
`DogeLib/Script/Exports/` adapts instruction reading and one `EvalScript` call to the [oracle format](docs/oracle.md).

Ledger, Rules and Models layers are added when their work begins.

## Adopted upstream code

Adapted code follows this layout and the module system. It does not keep the layout of the project it came from.
The btc-verified project keeps definitions, proofs and packed instances in one file, and its generic codec module imports Mathlib.
An adaptation splits those into the specification and `Proofs` libraries.
Each adapted file names its origin and commit in its module docstring and keeps any notice that the upstream terms require.

## Status vocabulary

A module never receives a single "verified" status.
[COVERAGE.md](COVERAGE.md) records each kind of evidence separately for each operation. The kinds are an executable definition, theorems with their hypotheses, comparison evidence, and a proved implementation refinement.
