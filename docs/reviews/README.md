# Model reads

A *model read* is a comparison of the Lean definitions of one area with the source code of Dogecoin Core, by an AI model.
The model reads the source on both sides, line by line, and reports each place where the two disagree.
It executes nothing: no build, no test and no comparison with compiled Core.

A model read is not a review by a person, and it is not a proof.
A model can miss a difference, and it can report a difference that does not exist.
The [Script record](script.md#after-the-read) shows one finding whose stated mechanism a later check corrected.
[SOUNDNESS.md](../../SOUNDNESS.md#a1-a-wrong-definition) describes the gap that a read helps to narrow (A1).

## Records

Each record gives the reader, the date, the DogeLib and Core revisions, the scope, the findings, and what the read compared and did not compare.
Line numbers in a record refer to those revisions.
All seven reads are by GPT-6 through Codex, on 2026-11-11, at DogeLib `865754b` and Core `e0a1c157791544e818c901bd9341896965afbf9d`:

| Area | Record | Brief | Findings |
| --- | --- | --- | --- |
| Script evaluation and verification | [script.md](script.md) | [briefs/script.md](briefs/script.md) | 3 domain boundaries |
| AuxPoW and header proof of work | [auxpow.md](auxpow.md) | [briefs/auxpow.md](briefs/auxpow.md) | 1 domain boundary |
| Difficulty retarget, next work and chain work | [retarget.md](retarget.md) | [briefs/retarget.md](briefs/retarget.md) | None |
| Transactions, serialization and legacy signature hashing | [sighash.md](sighash.md) | [briefs/sighash.md](briefs/sighash.md) | 1 domain boundary |
| Bounded readers and base serialization | [readers.md](readers.md) | [briefs/readers.md](briefs/readers.md) | 1 domain boundary |
| Contextual header validation and header sequences | [headerseq.md](headerseq.md) | [briefs/headerseq.md](briefs/headerseq.md) | None |
| Cryptography: secp256k1 verification and hashes | [crypto.md](crypto.md) | [briefs/crypto.md](briefs/crypto.md) | 4 domain boundaries |

No read found a consensus-divergent discrepancy.
Each finding is a *domain boundary*: an input outside the domain on which a definition corresponds to Core.
The AuxPoW and transaction records report the same boundary, Core's default-constructed transaction.
The section *After the read* of a record says where the repository states each boundary.
That section is not part of the read.

## Run a read again

Each file in [briefs/](briefs/) is the prompt that produced one record.
The only change is that `<DogeLib clone>` and `<Dogecoin Core clone>` replace the local paths.

1. Check out DogeLib and Dogecoin Core at the revisions to compare.
2. Put the two paths and the DogeLib revision in the brief.
3. Give the brief to a model that did not write the definitions, with read-only access to both clones.
4. Record its last message as the record.

## When a record becomes stale

A record describes the Lean files of its scope at its DogeLib revision.
Any later change to a definition in that scope invalidates the record for that definition.
A pull request that changes a covered definition must say so in its description.
The pull request must then include a new read, or mark the record as stale at its top.
A change to doc comments only does not make a record stale.
