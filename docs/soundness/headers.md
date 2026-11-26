# Soundness: Block Headers, AuxPoW, and Header Sequences

This file states what the header, Merkle-root, AuxPoW, contextual-header, and header-sequence proofs establish, under which hypotheses, and what remains unproved.
See [SOUNDNESS.md](../../SOUNDNESS.md) for the trust model and Gaps A to D, and [docs/coverage/blocks.md](../coverage/blocks.md) for per-operation evidence.

- **Scope**: Pure and full header codecs, transaction Merkle roots, `CAuxPow::check`, header proof of work, version gating, contextual header checks, and `processNewBlockHeaders`.
- **Specification modules**: `DogeLib.Block.Header`, `Merkle`, `AuxPow`, `AuxPowCheck`, `ProofOfWork`, `VersionGate`, `ContextualParams`, `ContextualCheck`, and `HeaderSequence`.
- **Proof modules**: `DogeLib.Block.Proofs.*` for those modules.
- **Key boundaries**: Adjusted time, checkpoint flags, and initial block indexes are caller inputs, and no theorem establishes hash collision resistance (A4, D1).
  Source correspondence to Core's header checks and little-endian, arithmetic-shift host assumptions remain A1 claims.

## Pure headers and transaction Merkle roots

`PureBlockHeader.decode_encode` preserves every raw field and arbitrary trailing bytes.
`decode_sound` identifies the consumed prefix as the returned header's encoding.
`encode_length` establishes exactly 80 bytes, and `getHash_val` identifies their double SHA-256 digest.
These claims cover the pure header even when its version sets the AuxPoW bit.
Core's full `CBlockHeader` then carries an AuxPoW payload, which the full header codec of the next subsection reads (D41).

[Header proof of work](#header-proof-of-work) covers scrypt proof of work and `CheckAuxPowProofOfWork`.
[Contextual header validation](#contextual-header-validation) gives the theorems about `ContextualCheckBlockHeader`, and [version gating](#version-gating) those about the version checks.

[The AuxPoW check](#the-auxpow-check) covers `CAuxPow::check` alone.

`computeMerkleRoot_nil` and `computeMerkleRoot_singleton` cover empty and one-leaf lists.
`merkleLevel_duplicate_last` equates the next levels before and after explicit duplication of an odd level's final leaf.
Its prefix-length hypothesis establishes that the final leaf is unpaired.
`merkleMutated_of_equal` detects any equal aligned leaf pair after an even-length prefix.

`computeMerkleRoot_duplicate_last` combines the two for a nonempty even-length prefix `pre` and a leaf `last`.
The leaves `pre ++ [last, last]` have the root of `pre ++ [last]` and set the mutation flag.
The theorem states the duplicate-leaf shape of CVE-2012-2459 that the comment in D42 describes, and it needs no hash collision.
`checkBlock_rejects_merkleDuplication` states what `checkBlock` does with a duplicated transaction list ([`CheckBlock`](blocks.md#block-codec-checktransaction-and-checkblock)).

`merkleMutated_iff` characterizes the recursive flag through equal pairs here or among complete parent subtrees.
The complete-level operation discards an unpaired final subtree.
Thus synthetic nodes from padding never enter mutation detection.
Core's leaf pass checks complete subtree pairs, and its final sweep never updates `mutated` (D42).
This source review does not prove an all-input equivalence to Core's C++.

The Core compatibility domain has at most 2^31 leaves.
At exactly 2^31 leaves, the final sweep stops at `count == 1 << 31` (D42, lines 94-102).
With 2^31 + 1 leaves, the sweep pads the unsigned 32-bit `count` to 2^32, which wraps to zero at line 112.
The propagation loop increments `level` to 32 at line 125, then evaluates `(uint32_t)1 << 32` at line 115.
C++ leaves that shift undefined.
The Lean definitions remain total on every finite list and add no rejection rule.

`blockMerkleRoot` takes its leaves from `Transaction.txid`, and Core takes them from the cached `GetHash` (D42, line 163).
The two differ only for a default-constructed `CTransaction()` or a copy of it, as [Transactions](transactions.md#transactions) states.

`tests/block/README.md` records the independent fixtures and the limits of their provenance (A1, B1, D3).
The later header expectations rely on successor commitments or an independent hashlib computation, not Core output.
The isolated fetched blocks have no authenticated chain connection.
Finite comparisons and structural theorems do not establish collision resistance or transaction validity.
The checked header codec, length, digest and Merkle structural proofs depend on `propext` and `Quot.sound`, by `#print axioms`.
The declaration check inspects all declarations under the unchanged standard-axiom policy (C1, C2).

## Transaction lists with one Merkle root

The `hashMerkleRoot` of a header does not fix the transaction list of the block alone.
The root holds neither the number of leaves nor the depth of the tree.
A transaction ID and an inner node are both double SHA-256 digests, and nothing marks which one a digest is.
Two ambiguities are known, and `DogeLib.Block.Proofs.MerkleLeafList` states both, with what excludes them.

The first ambiguity is the duplication of CVE-2012-2459, which `MerkleDuplication.root_eq_and_mutated` states.
The second is a transaction of 64 bytes at an inner node, CVE-2017-12842.
An inner node is the digest of the 64 bytes of its two children.

`blockMerkleRoot_inner_transaction` takes transactions `t`, `a` and `b`, where the base serialization of `t` is the ID of `a` followed by the ID of `b`.
Then `[t]` has the Merkle root of `[a, b]`, and `[t]` does not set the mutation flag.
`[a, b]` sets the flag exactly when the two IDs are equal.
The theorem assumes nothing about the hash.
The known answer `merkleInnerTransaction` of `lake test` gives made transactions with that hypothesis, and `checkTransaction` accepts all three.

`transactions_eq_of_merkleRoot_eq` takes two transaction lists `cx :: xs` and `cy :: ys`, with these hypotheses:

- `cx` and `cy` are coinbases: `Transaction.isCoinBase`, which is Core's `CTransaction::IsCoinBase` (D4, lines 354 to 357), one input with the null outpoint.
- The two lists have the same `blockMerkleRoot` root.
- Neither list sets the mutation flag.

The theorem concludes one of three statements:

1. The two lists are equal, as lists of `Transaction` values.
2. `MerkleCollision`: two different inputs of the two trees have the same double SHA-256 digest.
3. `CoinbaseAtInnerNode`: the base serialization of one coinbase is the 64 bytes of two nodes of the other tree.

Statements 2 and 3 are local to the two lists.
An input of a tree (`MerkleInput`) is the base serialization of one of its transactions.
The 64 bytes of two nodes of one level below the root are also an input.
A list of `n` transactions has fewer than `n + 4 * n * n` inputs.
A statement that some two byte strings collide, with no relation to the lists, holds for every hash with a fixed output length.
Such a statement would make the theorem say nothing, so no theorem here uses it.

Statement 3 is a condition on two digests, not a collision.
It names the coinbase `c` and two nodes `l` and `r` of one level of the other tree, with `l ++ r` as the serialization of `c`.
Bytes 4 to 40 of that serialization are the input count 1, the 32 zero bytes of the null hash and the index `ff ff ff ff`.
So the digest `l` ends with the byte 1 and 27 zero bytes.
The digest `r` starts with 5 zero bytes and `ff ff ff ff`.
The statement fixes 37 bytes, which are 296 bits, of two digests of inputs of that tree (`encodesInnerNode_coinbase_pattern`).

The theorem keeps statement 3, for this reason.
Suppose that one tree has more levels than the other.
Then the coinbase of the lower tree has the digest of an inner node of the higher tree.
Either the two inputs of that digest are a collision, or the serialization of the coinbase is the 64 bytes of the two children.

A coinbase of 64 bytes is well formed, so the serialization does not exclude the second case.
That case has one 64-byte string and no second one, so it gives no collision.
To leave statement 3 out, the theorem would need a further assumption about SHA-256.

DogeLib does not assume that statement 2 or statement 3 is false, and it adds no hypothesis about SHA-256.
A reader who concludes that the two lists are equal assumes two things about these lists (A4).
No two different inputs of the two trees have the same digest, and no two digests of one tree hold the start of a coinbase.
Neither assumption follows from the fixed output length of the hash.
`not_merkleCollision_singleton` and `not_encodesInnerNode_singleton` prove both statements false for lists of one transaction.

`transactions_eq_or_encodesInnerNode` is the theorem without the coinbase hypotheses.
Its third statement is `EncodesInnerNode`: the serialization of the first transaction of one list is the 64 bytes of two nodes of the other tree.
That statement holds for `[t]` and `[a, b]` above, by `encodesInnerNode_of_encode`, so the two theorems cannot conclude statement 1 or 2 alone.
The coinbase hypotheses add the condition on the digests.

For the made transactions of `lake test`, `t` is not a coinbase and the six inputs have six digests.
So the conclusion of `transactions_eq_of_merkleRoot_eq` fails for that pair, which lacks one coinbase hypothesis.
That result is a compiled known answer, not a theorem.

Without the mutation flags, `[A, B, C]` and `[A, B, C, C]` have one root and are not equal.
No theorem states that the conclusion fails for such a pair.
The conclusion is an equality of `Transaction` values, because the base codec is injective on every `Transaction` (`encode_injective`).
A caller that reads a list from bytes applies the theorem to the values that its reader returned.

`checkBlock_transactions_eq_of_merkleRoot_eq` carries the result to blocks.
Let `checkBlock` accept a block with the Merkle check.
Let a second list start with a coinbase, have the `hashMerkleRoot` of the header as its root, and not set the mutation flag.
Then the list is the transaction list of the block, apart from statements 2 and 3 for that list and the list of the block.

`checkBlock` gives the three hypotheses for the block, by `checkBlock_ok_merkle`.
Core's tests are at D106, lines 2951 to 2962, 2976 and 2977.
`checkBlock_transactions_unique` states the same for two accepted blocks whose headers have one `hashMerkleRoot`.
These theorems are about `checkBlock`, and they do not show that Core's `CheckBlock` has the property.

At the pin, no rule of Core rejects a transaction because it has 64 bytes.
`CheckTransaction` tests the size only against the upper bound `MAX_BLOCK_BASE_SIZE` (D106, lines 535 and 536).
The only test of the total size in `IsStandardTx` is that the weight is below `MAX_STANDARD_TX_WEIGHT` (D118, lines 71 to 75).
It also bounds the size of each `scriptSig` from above, at 1650 bytes (line 86).
Neither function has a test that rejects a size of 64 bytes.

The pin has no file `src/consensus/tx_verify.cpp`, and `CheckTransaction` is in `src/validation.cpp`.
This record is a reading of those functions.
DogeLib makes no claim about which transactions the mainnet chain holds.

By `#print axioms`, `transactions_eq_of_merkleRoot_eq`, `transactions_eq_or_encodesInnerNode`, `merkleRoot_eq_levels`, `blockMerkleRoot_inner_transaction` and `isCoinBase_encode_pattern` depend on `propext` and `Quot.sound`.
`checkBlock_transactions_eq_of_merkleRoot_eq` and `checkBlock_transactions_unique` depend on `propext`, `Classical.choice` and `Quot.sound`.

## Full headers and the AuxPoW payload

`BlockHeader.read` follows `CBlockHeader::SerializationOp` (D41) and the payload fields of `CMerkleTx` and `CAuxPow` (D54).
The read mode of the embedded transaction is a parameter, `TxReadMode`.
Design record 0004, section 4.6, gives the witness-allowed mode for Core's network, disk and raw RPC paths at the pin.
That conclusion comes from source inspection, and a caller that picks the mode chooses which Core path it models.

`read_auxpow_isSome` shows that a decoded header has a payload exactly when its flag is set, in each mode and for every input.
So the two mismatch rejections of `CheckAuxPowProofOfWork` cannot follow from decoded bytes.
`read_pure` and `encode_take` show that the first 80 bytes are the pure header in the 80-byte codec.

The round trips `read_encode_allowWitness` and `read_encode_base` take three hypotheses.
The payload is present exactly when the flag is set.
Both branches and the transaction counts are within `MAX_SIZE`.
In the witness-allowed mode, the transaction has witness data, or an input, or no output.
`noInputsExample_not_roundTrip` shows a transaction outside that shape.

Base mode returns the base projection, because its writer drops every witness stack.
`baseProjection_eq` gives the projection as the header itself when no transaction has witness data.

These round trips are canonicality over encoder output only.
No theorem says that every accepted byte string is the encoding of its result.
In the witness-allowed mode that claim is false.

Core accepts an extended encoding whose stacks are all empty, and its writer then emits the base form (D4, lines 214 to 263).
`extendedEmptyStacks_read` gives two such byte strings that read as one header with different lengths.
The reader keeps this acceptance and does not reject the extended form.
`extendedEmptyStacks_read_base` shows that base mode reads the same extended bytes as a different transaction, with 35 bytes left over.

`read_extends` shows that bytes appended to an accepted input stay in the remainder, in each mode.
With the round-trip hypotheses, `read_take_encode_allowWitness` and `read_take_encode_base` follow: the reader rejects every proper prefix of an encoding.
No theorem says which error the reader reports.

The mainnet fixtures come from a third-party explorer, Blockchair, on 2026-11-06.
An independent Python parser checks each block against Core's checkpoint hash, the explorer's separately decoded fields and the block's own Merkle root (`tests/block/README.md`).
The checkpoint fixes only the 80-byte pure header, because the block hash does not cover the payload (D41, D40).
The pinned Core harness reads these full headers in both transaction modes and compares all decoded fields, consumption and remainder.
It also checks their proof of work, as the [fixture report](../../tests/block/core-header-pow.json) records.

By `#print axioms`, the round trips and truncation theorems depend on `propext`, `Classical.choice` and `Quot.sound`, and the other codec theorems on `propext` and `Quot.sound`.
The two concrete examples are checked by kernel reduction with `rfl`.

## The AuxPoW check

`AuxPow.check` follows `CAuxPow::check` (D55, lines 80 to 161) statement by statement.
Its helpers follow `CheckMerkleBranch` (lines 189 to 206), `getExpectedIndex` (lines 163 to 187), `GetChainId` (D10) and `std::search`.
Each `return error` of the source has one constructor of `AuxPowCheckError`, which names its line, and `check` returns the first failing test.
The source review, not a theorem, connects these definitions to Core.

`check` takes `fStrictChainId` as a Boolean, because it reads no other field of the parameter record.
Which record a caller selects, and so which value it passes, is outside this operation.
The block hash and the chain ID are arguments: `CheckAuxPowProofOfWork` passes the merge-mined header's own hash and its own chain ID (C7 of design record 0004).

The Merkle test of `check` uses `Transaction.txid`, and Core uses the cached `GetHash` (D55, line 100).
A default-constructed `CAuxPow` holds `CTransaction()`, whose cached hash is zero ([Transactions](transactions.md#transactions)).
A payload with that transaction or a copy of it is outside the domain of `check`.
For example, take a default `CAuxPow` and set both indices to zero, with both branches empty, a zero parent Merkle root and `fStrictChainId` false.
Core reports that the coinbase has no inputs, and `check` reports `merkleRootIncorrect`.
Both reject, and Core computes the cache for every payload that it decodes.

`AuxPow.check_eq_ok_iff` characterizes acceptance for every payload and every argument.
`AuxPow.check_ok_binding` restates it as equalities of hashes and script bytes.

The parent's `hashMerkleRoot` is the left fold of the transaction ID along the coinbase branch.
The first input's script contains the chain root with its bytes reversed, first at an offset that `MarkerCondition` allows.
The eight bytes after it encode `2^h` and a nonce, and `nChainIndex` is `getExpectedIndex` of that nonce, the chain ID and `h`.
The chain root is `checkMerkleBranch` of the block hash along the chain branch at `nChainIndex`.

These equalities concern computed hashes only.
No theorem says that another header, transaction or branch cannot reach the same hashes.
That claim needs collision resistance of double SHA-256, which DogeLib does not model.
No theorem says that work cannot be reused across chains, or that two chains cannot share a slot.

`findSubseq?_eq_some_iff` and `searchChainRoot_eq_ok_iff` state the search over first occurrences, as `std::search` returns them.
For every index other than −1, `checkMerkleBranch_eq_fold` takes the side of step `k` from bit `min k 31` of the index.
`getExpectedIndex_eq` gives the closed form modulo 2^32 for `h < 32`, and `getExpectedIndex_mod64` proves the source comment's claim that 64-bit arithmetic gives the same result, for `h ≤ 32`.

C++11 leaves the right shift of a negative `int` implementation-defined (S1, 5.8 paragraph 3).
`GetChainId` shifts the signed version, and `CheckMerkleBranch` shifts a negative `nChainIndex`.
DogeLib uses the arithmetic shift in both places, as GCC and Clang do.

For `nChainIndex`, the choice cannot change acceptance: `AuxPow.check_ok_chainIndex_lt` shows that `check` rejects every negative `nChainIndex`.
It can change which error a rejected payload reports.
For the chain ID, the choice decides the chain ID of a header whose version is negative, and so it can change the result.
A Core comparison of such headers assumes a compiler with the arithmetic shift.

`getExpectedIndex` takes its shift modulo 32 when `h ≥ 32`, where Core's `1 << h` is undefined.
`check` calls it only with `h ≤ 30`, so the difference never reaches `check`.

The known answers in `tests/block/check-auxpow.json` have two kinds of input.
The 26 `check_auxpow` cases transcribe the construction of Core's test (D56, lines 186 to 323) into an independent Python builder.
Their expected Booleans come from the `BOOST_CHECK` assertions.

The Core harness reconstructs all 26 cases with Core's own classes and requires exact serialized byte agreement.
It also requires Core verdicts and arguments to match those records.
This closes the deferred byte-transcription check of stage 3 from pull request #99.

The 16 boundary cases take their expectations from the author's reading of D55, and the comparator checks Core's verdict on each payload.
Both implementations also accept the six historical mainnet payloads with their own child hashes and mainnet strictness.
These finite checks do not establish all-input equivalence with Core.
[The comparison report](../comparison-evidence.md#header-proof-of-work-evidence) describes the streams and mutation seed.

By `#print axioms`, the search and `getExpectedIndex_mod64` theorems depend on `propext` and `Quot.sound`, and the others on `propext`, `Classical.choice` and `Quot.sound`.

## Header proof of work

`checkAuxPowProofOfWork` follows `CheckAuxPowProofOfWork` (D6, lines 89 to 125) in source order, with one `CheckPowError` constructor for each `return error`.
`checkBlockHeader` follows `CheckBlockHeader` with `fCheckPOW` true (D33, lines 2927 to 2937): the predicate on the height-zero record of a network.
`PureBlockHeader.powHash` is `GetPoWHash` (D40, lines 25 to 30): the scrypt digest of the 80 encoded header bytes.
The source review, not a theorem, connects these definitions to Core.

`checkAuxPowProofOfWork_iff` characterizes acceptance for every parameter record and every full header.
A header that is not legacy, under `fStrictChainId`, must carry `nAuxpowChainId`.

Without a payload, the flag must be clear and the header's own digest must satisfy `checkProofOfWork` with its `nBits`.
With a payload, the flag must be set.
The digest of the 80 parent bytes, including the parent's `nBits`, must satisfy `checkProofOfWork` with the `nBits` of the merge-mined header.
`AuxPow.check` must also accept, with the merge-mined header's hash and chain ID.

The theorem keeps both flag mismatches, and `checkAuxPowProofOfWork_read` shows that a header from `BlockHeader.read` reaches neither.
`powHash_eq` and `powHash_eq_spec` relate the digest to `scrypt_1024_1_1_256` and to the RFC 7914 model, as [Dogecoin's scrypt digest](cryptography.md#dogecoins-scrypt-digest) describes.

The record carries `nAuxpowChainId`, `fStrictChainId` and the retarget fields of the Core record, of which only `powLimit` is read.
`checkAuxPowProofOfWork_congr` shows that the result depends on the record only through those three fields.

`ParamsTree.getConsensus` repeats the search of `GetConsensus` (D14, lines 494 to 506) over the AuxPoW projection of each network's records.
`getAuxPowParams_eq_work` shows that it selects the same effective height and retarget fields as `Work.getConsensus`, at every UInt32 height.
`checkAuxPowProofOfWork_getAuxPowParams` proves that, in each network, every selected record gives the result of the height-zero record.
So `CheckBlockHeader`, which reads the height-zero record, and the disk reads, which read the record of the block's height, agree on every header.
The theorem is about the transcribed records.
A transcription mistake in D14 would make it a claim about the wrong records (A1).

`checkBlockHeader` takes the network as an argument.
DogeLib does not model the selection of `Params()`. [Contextual header validation](#contextual-header-validation) and [the block codec section](blocks.md#block-codec-checktransaction-and-checkblock) cover `ContextualCheckBlockHeader` and `CheckBlock`.
A valid AuxPoW header before activation passes `checkBlockHeader`, as it passes Core's `CheckBlockHeader`.
Only [version gating](#version-gating) rejects it.

The equalities concern computed digests only, with no cryptographic claim, as for [the AuxPoW check](#the-auxpow-check).
A comparison with Core keeps the execution assumptions of design record 0004, section 6.
They are a little-endian host without padding between the header fields, an arithmetic right shift and the generic scrypt variant.

`lake test` runs `checkBlockHeader` on mainnet headers through the compiled code (B1).
Chain acceptance supplies the expected acceptance of the six AuxPoW checkpoint headers and 315 pre-AuxPoW headers.

Each expected rejection of a mutation is argued from D6's order of checks.
Where it depends on a changed digest failing its target, a random 256-bit digest would pass with probability about target / 2^256.
That probability is about 2^-20 for the initial target of the header at height 1, and about 2^-33 at heights 3000 and 4000.
For every other target here it is below 2^-41.
No theorem relies on that argument.

The `block.check_pow` comparison checks all 321 headers against Core's `CheckAuxPowProofOfWork` and its real selected parameters.
The [fixture report](../../tests/block/core-header-pow.json) records the byte identities, network, parameters and Core verdicts.
The [comparison](../comparison-evidence.md#header-proof-of-work-evidence) also changes parent and child targets, nonces and version bits.
Lean diagnostics stay outside the compared verdict.

The Core harness ports `mineBlock` and `auxpow_pow` and mines their nonces again on every comparison.
It checks the 12 predicate assertions, 11 mining assertions and two version/hash assertions against the source test.
The [comparison records](../../tests/block/auxpow-pow.json) preserve the exact components and Core verdicts.
Lean and Core replay all 12 predicate cases on those bytes, including the two flag/payload mismatches.

Those mismatches use the oracle's split-input form because `checkAuxPowProofOfWork_read` excludes them for a decoded full header.
The ten serializable cases also run through the full-header reader.
These checks close the runtime-mined comparison item of design record 0004, section 7.
These checks add finite evidence and no theorem or trust-policy exception.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.ProofOfWork` |
| --- | --- |
| None | `getAuxPowParams_mainnet`, `getAuxPowParams_regtest` |
| `propext`, `Quot.sound` | `PureBlockHeader.powHash_eq`, `getAuxPowParams_testnet`, `getAuxPowParams_eq_work` |
| `propext`, `Classical.choice`, `Quot.sound` | `PureBlockHeader.powHash_eq_spec`, `checkAuxPowProofOfWork_iff`, `checkAuxPowProofOfWork_read`, `checkAuxPowProofOfWork_congr`, `checkAuxPowProofOfWork_getAuxPowParams`, `checkBlockHeader_eq` |

## Version gating

`checkVersion` follows the two version checks at the start of `ContextualCheckBlockHeader` (D33, lines 3072 to 3086), in source order.
With `fAllowLegacyBlocks` false, a legacy version is rejected as `late-legacy-block`.
With `fAllowLegacyBlocks` true, a set AuxPoW flag is rejected as `early-auxpow-block`.
`PureBlockHeader.isLegacy` is Core's `IsLegacy` (D10, lines 150 to 155): version 1, or version 2 with chain ID zero.
The source review, not a theorem, connects these definitions to Core.

`checkVersion_eq_ok_iff` and the two rejection theorems characterize the result for every record and every pure header.
`PureBlockHeader.isLegacy_iff` shows that a version is legacy exactly when its bits are 1 or 2.
So the chain ID test of `IsLegacy` never changes its result.
A legacy version has a clear AuxPoW flag, so at most one of the two checks can reject a header.

The record is an argument that carries only `fAllowLegacyBlocks`.
Core takes the record from `GetConsensus` at the height of the new header (D14, lines 494 to 506).
`getContextualParams` models that selection ([contextual parameters and checkpoints](#contextual-parameters-and-checkpoints)).
`checkVersion` does not call it, and no theorem says which record a caller should pass.

The oracle adapter projects the field from the D14 parameter trees and compares 207 boundaries with Core's actual selected records.
A caller that passes the wrong record gets the result of the wrong era.
The known answers state the record that Core selects on each side of each activation height, from D14.

The operation covers only these two checks.
It omits the rest of `ContextualCheckBlockHeader`: `nBits` against `GetNextWorkRequired`, the checkpoints, the time checks and the rejection of outdated versions.
So an accepted result of `checkVersion` does not mean that Core accepts the header in context.
[Contextual header validation](#contextual-header-validation) composes all seven checks.

By `#print axioms`, `PureBlockHeader.isLegacy_iff` depends on `propext`, and the other theorems on `propext` and `Quot.sound`.

## Contextual parameters and checkpoints

`getContextualParams` repeats the search of `GetConsensus` (D14, lines 494 to 506) over a projection of each network's records.
The projection keeps `fAllowLegacyBlocks`, `BIP65Height` and `BIP66Height` (D15, lines 51, 53 and 82).
`getContextualParams_mainnet`, `_testnet` and `_regtest` give the selected record at every UInt32 height.
`allowLegacyBlocks_getConsensus` shows that the selected `fAllowLegacyBlocks` is false exactly from height 371337 on mainnet, 158100 on testnet and 20 on regtest.
`getContextualParams_eq_work` shows that the search selects the effective height that `Work.getConsensus` selects.

`ContextualParams.bipHeights_records` shows that every record of a network's tree has the `BIP65Height` and `BIP66Height` of the height-zero record.
Design record 0006, item 3, gives the reason in Core: each record is a copy of the previous one, and no copy changes these fields.
`bip65Height_getConsensus` and `bip66Height_getConsensus` give the selected values at every UInt32 height.
The theorems are about the transcribed records.
A transcription mistake in D14 would make them claims about the wrong records (A1).
The known answers compare 23 selected records with values copied from D14, each with its line.

`lastCheckpoint` follows `GetLastCheckpoint` (D67, lines 18 to 30) and the `fCheckpointsEnabled` test of `ContextualCheckBlockHeader` (D33, line 3093).
It walks the network's table from the greatest height down, and returns the first height in the known list.
`checkpointHeights_sorted` shows that the heights of each table increase strictly, so the walk follows the key order of Core's `std::map`.
`lastCheckpoint_eq` shows that the result is `none` when checkpoints are disabled.
Otherwise the result is the greatest table height in the known list, or `none` if the list has no table height.
`lastCheckpoint_eq_some_iff` and `lastCheckpoint_eq_none_iff` state the same result as conditions.

The flag and the known list are inputs that a node computes from its own state: the option `-checkpoints` and the block index.
No theorem says that a caller supplies the values that a node would compute.
Core's `GetLastCheckpoint` returns the block-index entry of a checkpoint hash, and check 4 reads the `nHeight` of that entry.
`lastCheckpoint` returns the table key instead.
The two agree unless the block index holds a block with a checkpoint hash at another height.
To exclude that case needs collision resistance of double SHA-256, which DogeLib does not model (A4).

The known answers compare ten of the 43 table hashes with the double SHA-256 of independent pure headers.
The tables are also compared with D9 by their sizes and end heights.
The oracle's `block.check_version` selects `fAllowLegacyBlocks` with `getContextualParams` and its `toVersionGateParams` projection.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.ContextualParams` |
| --- | --- |
| None | `ContextualParams.bipHeights_records`, `checkpointHeights_sorted` |
| `propext`, `Quot.sound` | `getContextualParams_mainnet`, `getContextualParams_testnet`, `getContextualParams_regtest`, `allowLegacyBlocks_getConsensus`, `bip65Height_getConsensus`, `bip66Height_getConsensus`, `getContextualParams_eq_work` |
| `propext`, `Classical.choice`, `Quot.sound` | `find?_reverse_eq_max?_filter`, `lastCheckpoint_eq`, `lastCheckpoint_eq_some_iff`, `lastCheckpoint_eq_none_iff` |

## Contextual header validation

`DogeLib.Block.ContextualCheck` specifies `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
`contextualCheckBlockHeader` runs Core's seven checks in source order and returns the first failure.
It composes `checkVersion`, `Work.nextWorkRequired`, `Work.medianTimePast`, `getContextualParams` and `lastCheckpoint` without a change to them.
The source review, not a theorem, connects the composition to Core.

The function first checks its domain, and returns an adapter error outside it.
The domain is a nonempty view on which `medianTimePast` and `nextWorkRequired` succeed, with an adjusted time of at most `INT64_MAX - 7200`.
Core's callers always pass a predecessor, so the empty view is outside the domain.

On a view that is too short, Core computes a different median or fails an assertion.
So the function rejects such a view with an adapter error.
Above `INT64_MAX - 7200`, Core's sum `nAdjustedTime + 2 * 60 * 60` overflows `int64_t`, which is undefined behaviour (design record 0006, decision 9).
The domain checks run before check 1.
So an input outside the domain never gets a Core rejection, even when Core would reject it at an earlier check.

Check 3 compares `nBits` with the required value as raw 32-bit values, as D33 line 3089 does.
So another compact encoding of the same target fails.
Checks 5 and 6 compare widened `Int` times.
On the domain, no value overflows `int64_t`, so these comparisons equal Core's.
Check 7 uses `PureBlockHeader.getBaseVersion`, the remainder of the signed version by 256 that truncates toward zero, as C++ `%` does (D10, lines 88 to 95).
The reject reason prints that value as the eight hexadecimal digits of its 32-bit pattern, as Core's `%08x` does (D71).

The theorems in `Block.Proofs.ContextualCheck` hold for every network, header, adjusted time and last checkpoint:

- `contextualCheck_eq_ok_iff`: on a view `prev :: rest`, the function accepts exactly when the input is in the domain and the seven conditions hold.
  Each condition is stated over the inputs, the median, the required value and the record at the candidate height.
- `contextualCheck_eq_lateLegacyBlock_iff` and the six other `contextualCheck_eq_*_iff` theorems give one rejection each.
  The function returns the rejection exactly when the input is in the domain, all earlier conditions hold and the condition of that check fails.
  For `bad-version`, the error carries `getBaseVersion`.
- `contextualCheck_nil`, `contextualCheck_of_medianTimePast_error`, `contextualCheck_of_nextWorkRequired_error` and `contextualCheck_of_adjustedTime` give the adapter error outside the domain.
- `contextualCheck_congr_header`: two headers with the same `nVersion`, `nTime` and `nBits` give the same result.
- `contextualCheck_adjustedTime_mono`: an acceptance stays an acceptance for every greater adjusted time up to `INT64_MAX - 7200`.
- `contextualCheck_no_checkpoint`: with no last checkpoint, the function never returns `bad-fork-prior-to-checkpoint`.
- `contextualCheck_congr_prefix`: two views that pass `validateWorkView`, start with the same predecessor and agree on their first `contextualViewDepth` entries give the same result.
  The depth is the greater of 11 and `retargetInterval params h + 1`, where `h` is the predecessor height and `params` is the work record at the candidate height.
  `contextualViewDepth_eq` gives its values for a predecessor height below 2147483647.
  On mainnet and testnet, the depth is 241 below candidate height 145000 and 11 from it.
  On regtest, it is 14401 below candidate height 10 and 11 from it.
- `contextualCheck_complete`: a view that passes `validateWorkView` and reaches height 0, with an adjusted time in the domain, gives only Core rejections, never an adapter error.
- `badVersion_iff`: let `b` be the signed remainder of `nVersion` by 256.
  Check 7 rejects exactly when `b` is below 3 from `BIP66Height`, or below 4 from `BIP65Height`, with each network's heights.

These theorems establish the behaviour of DogeLib's definitions.
`block.contextual_check` compares the compiled specification with Core's `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
The harness calls that function on index entries that it builds from the request.
It compares `valid` and the first `reject_reason`, excluding Lean diagnostics.
The [comparison stream](../comparison-evidence.md#contextual-header-comparison-evidence) includes 2231 real mainnet candidates, hand-derived boundaries and 500 mutations with seed `20261109`.
The comparison gives finite evidence, not an equivalence theorem with compiled Core.

The in-memory index is an evidence boundary (A1).
The harness sets the height, time, bits and predecessor of each entry, and a mistake there gives Core a context other than the request's.
Hand-derived expected verdicts and reasons provide a separate check.

The harness fills Core's block-index map with each known table hash at its table height.
It refuses short views before calling Core, where a short median walk would otherwise give a different value.
Neither the harness nor the oracle establishes the caller-supplied context.

Three inputs are execution boundaries.
The caller supplies them, and no theorem says that a caller supplies the values that a node would compute:

- **The adjusted time.** Core passes `GetAdjustedTime()`, the system time plus a peer offset (D72, lines 34 to 37).
  By default the offset is at most 70 minutes in either direction (D73, line 13).
  The function takes the adjusted time as an `Int64` and does not model the clock or the peers.
- **The last known checkpoint.** Core reads `fCheckpointsEnabled` and the checkpoint hashes in its block index `mapBlockIndex` (D33, lines 3093 to 3100, and D67).
  The function takes the resulting height, and `contextualCheckBlockHeaderWithCheckpoints` derives it from the enabled flag and the known table heights with `lastCheckpoint`.
  The [checkpoint subsection](#contextual-parameters-and-checkpoints) explains why the table key stands for the `nHeight` of the block-index entry.
- **The link from the header to the view.** No check reads a hash, so the function cannot check that the view is the chain of the header's `hashPrevBlock`.
  Core's `AcceptBlockHeader` finds `pindexPrev` by that hash before the call (D33, lines 3205 to 3267).
  A caller that passes the view of another chain gets the result for that chain.
  `acceptBlockHeader` builds the view from the index by `hashPrevBlock`, so it has no such boundary ([one step](#one-step-acceptblockheader)).

`lake test` runs the compiled function on the five mainnet fixtures: heights 0–12, 144719–145030, 371320–371340, 1032483–1034390 and 3464739–3464760.
Two public Electrum servers returned the same bytes for the three ranges under `tests/block`.
At AuxPoW heights, the servers return each header with its AuxPoW payload, and the fixtures keep only the 80-byte pure headers.
The test checks every predecessor link, the checkpoint at 371337 and the hashes in the comments on `BIP66Height` and `BIP65Height` (D14, lines 85 to 87).
The hash in the comment on `BIP66Height` identifies the block at 1032483, 1900 blocks below that height, so that fixture starts at 1032483.

Chain acceptance gives the expected result for 2231 real candidates.
Hand-derived mutations of the real headers cover each rejection on both sides of its boundary and the order of the checks.
Synthetic views cover the minimum-difficulty rules of testnet and the version thresholds of testnet and regtest.
They also cover another encoding of the same target on mainnet and a median of times out of order.
Their required `nBits` values are derived by hand from D17 and D6.
These checks do not run Core, and they do not establish proof of work, AuxPoW validity or equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.ContextualCheck` |
| --- | --- |
| `propext` | `bind_unit_eq_ok`, `bind_unit_eq_error`, `checkDiffbits_eq_ok_iff`, `checkDiffbits_eq_error_iff`, `checkTimeTooOld_eq_error_iff`, `checkTimeTooNew_eq_error_iff`, `checkBaseVersion_eq_error_iff` |
| `propext`, `Quot.sound` | `checkVersion_mapError_eq_ok_iff`, `checkVersion_mapError_eq_error_iff`, `checkCheckpoint_eq_ok_iff`, `checkCheckpoint_eq_error_iff`, `checkTimeTooOld_eq_ok_iff`, `checkTimeTooNew_eq_ok_iff`, `contextualChecks_isRejection`, `contextualViewDepth_eq`, `badVersion_iff` |
| `propext`, `Classical.choice`, `Quot.sound` | `checkBaseVersion_eq_ok_iff`, `contextualChecks_eq_ok_iff`, `contextualCheck_nil`, `contextualCheck_of_medianTimePast_error`, `contextualCheck_of_nextWorkRequired_error`, `contextualCheck_of_adjustedTime`, `contextualCheck_eq_contextualChecks`, `contextualCheck_eq_iff_contextualChecks`, `contextualCheck_eq_ok_iff`, the seven `contextualCheck_eq_*_iff` rejection theorems, `contextualCheck_congr_header`, `contextualCheck_adjustedTime_mono`, `contextualCheck_no_checkpoint`, `contextualCheck_congr_prefix`, `contextualCheck_complete` |

## The block-index model

`DogeLib.Block.HeaderSequence` specifies the part of Core's block index that `AcceptBlockHeader` reads (design record 0008, stage 1).
`HeaderIndex` holds the entries of `mapBlockIndex` (D69, lines 169 and 170) as an association list, and the members of `gFailedBlocks` (D33, line 180) as a list.
Each `IndexEntry` holds the pure header, the height and the hash of its predecessor (D18, lines 164 to 171).
It also holds the two failure flags and a flag for the validity level `BLOCK_VALID_SCRIPTS` (D18, lines 136, 146 and 147).
Stage 4 adds `chainWork`, Core's `nChainWork` (D18, line 183), which [chain work](work.md#chain-work) describes.

The other definitions read the list only through `HeaderIndex.lookup`, so a later lane can change the representation behind that interface.
Source review, not a theorem, connects the model to Core's `CBlockIndex`.

`WellFormed` states the conditions of design record 0008, section 5.5:

- Each key is the double SHA-256 of the pure header of its entry.
- A predecessor hash equals the header's `hashPrevBlock`, and the index has an entry under it one height below.
- An entry at height 0 without a predecessor has the genesis hash of the network (D9, lines 160, 320 and 450).
- Each height is below 2147483647.
- Each member of the failed list has an entry with `BLOCK_FAILED_VALID`, as Core asserts (D33, line 3244).

An entry without a predecessor above height 0 is an *anchor*.
Core's index has no anchor, because it always reaches the genesis block.
An anchor lets a fixture or a consumer start the index at a recent block.
Where the contextual check needs an entry below an anchor, `contextualCheckBlockHeader` returns an adapter error, not a Core verdict.

`ancestorView` walks the predecessor links from an entry and collects the height, time and `nBits` of each entry.
It stops after `contextualViewDepth` entries or at an entry without a predecessor.
`contextualViewDepth` moved from `Block.Proofs.ContextualCheck` to `Block.ContextualCheck` without a change, because the specification now uses it.
`lastCheckpointInIndex` follows `GetLastCheckpoint` (D67, lines 18 to 30) over the index.
It returns the `nHeight` of the entry that it finds, which check 4 compares (D33, line 3098), not the key of the table.
`Checkpoint.blockHash?` and `genesisHash?` read Core's `uint256S` literals (D22, lines 151 to 156) with the existing transcription of `SetHex` (D11).

The theorems in `Block.Proofs.HeaderSequence` hold for every network:

- `ancestorWalk_valid`: in a well-formed index, every walk from an entry passes `validateWorkView`.
- `ancestorView_congr_chain`: in a well-formed index, `contextualCheckBlockHeader` gives the same result on the `ancestorView` of an entry as on its `ancestorChain`.
  `ancestorChain` is the whole chain of predecessors in the index, and the equality holds for every header, adjusted time and last checkpoint.
- `ancestorView_congr`: the target of design record 0008, section 11, with the hypothesis that the chain reaches height 0.
  Such a chain has no anchor, so it is the chain of `pprev` links that Core walks.
  The proof does not use the hypothesis, and `ancestorView_congr_chain` is the general form.
- `lastCheckpointInIndex_eq`: suppose that each table hash in the index belongs to an entry at its table height.
  Then `lastCheckpointInIndex` equals `lastCheckpoint` of design record 0006 on the table heights whose hashes the index has.
  The hypothesis is the hash commitment assumption of [the checkpoint subsection](#contextual-parameters-and-checkpoints), stated for one index.
  No theorem discharges it, because that needs collision resistance of double SHA-256 (A4).
  The theorem also takes `WellFormed`, as section 11 of the record requires, and its proof does not use it.
- `HeaderIndex.lookup_insert_self` and `HeaderIndex.lookup_insert_of_ne`: a lookup after an insertion finds the inserted entry under its key, and the earlier entry under another key.

These theorems establish the behaviour of DogeLib's definitions.
The index is an input.
No theorem says that its anchors, failure flags, validity flags and failed list are the state that a node holds.

`WellFormed` is a hypothesis.
Stage 2 adds its executable form, `checkWellFormed`, and the sequence of stage 3 runs that check before the first header.
Stage 1 builds the view from an entry, but the caller still chooses the entry.
[The step of stage 2](#one-step-acceptblockheader) finds the entry by the header's `hashPrevBlock`, and so removes the link boundary of [contextual header validation](#contextual-header-validation).

`lake test` builds an index from each of the five mainnet fixtures.
The first header of each fixture is the genesis entry or an anchor, and no entry has a failure flag.
The expected view of each entry lists the fixture records from that height down, by their position in the fixture.
Its length is the depth that `contextualViewDepth_eq` gives, or the number of records down to the anchor if that is smaller.

The expected last checkpoint is the table height of D9 in the range of each fixture: 0, 145000, 371337 or none.
The expected verdict of the contextual check comes from chain acceptance and D33.
A candidate with fewer than 11 entries above an anchor gives `shortView`, and a candidate below the last checkpoint gives `bad-fork-prior-to-checkpoint`.
An anchor at 144720 gives `nextWork missingAncestor` at the retarget 144960.
These known-answer checks do not run Core.
The [header-sequence comparison](../comparison-evidence.md#header-sequence-comparison-evidence) supplies separate finite evidence from Core's `AcceptBlockHeader`.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| None | `HeaderIndex.insert_failedBlocks` |
| `propext` | `HeaderIndex.lookup_insert_of_ne` |
| `propext`, `Quot.sound` | `ancestorWalk_length_le`, `ancestorWalk_take` |
| `propext`, `Classical.choice`, `Quot.sound` | `HeaderIndex.lookup_insert_self`, `ancestorWalk_valid`, `ancestorWalk_eq_ancestorChain`, `ancestorView_congr_chain`, `ancestorView_congr`, `lastCheckpointInIndex_eq` |

## One step: `acceptBlockHeader`

`acceptBlockHeader` in `DogeLib.Block.HeaderSequence` specifies Core's `AcceptBlockHeader` (D33, lines 3205 to 3267) on the block-index model (design record 0008, stage 2).
It takes a `HeaderContext`, an index and a full header, and returns the index after the step and the hash or an error.
For the genesis hash of the network, it skips steps 1 to 6, as Core does at line 3212.
For any other hash, it runs the steps of the record's section 3.1 in Core's order and returns at the first failure:

1. A known hash returns its entry, or `duplicate` when the entry has `failedValid` or `failedChild` (lines 3214 to 3222).
2. `checkBlockHeader`, as `CheckBlockHeader` with `fCheckPOW` true (lines 3224 and 3225, and lines 2927 to 2937).
3. The index must have `hashPrevBlock` (lines 3229 to 3231).
4. The predecessor must have no failure flag (lines 3233 and 3234).
5. `contextualCheckBlockHeader` on `ancestorView` of the predecessor and on `lastCheckpointInIndex` (lines 3238 and 3239).
6. Unless the predecessor has `scriptsValid`, no member of the failed list may be an ancestor of the predecessor (lines 3241 to 3256).
   A failure marks the entries from the predecessor down to that member with `failedChild`, without the member, and then rejects.
7. `addToBlockIndex`, the index part of `AddToBlockIndex` (lines 2755 to 2788), without `nTimeMax`, `pindexBestHeader` and the dirty set.
   Stage 4 adds the chain work of the new entry (line 2780), which [chain work](work.md#chain-work) describes.

`HeaderRejection` has one constructor for each rejection, and `rejectReason`, `dosScore` and `rejectCode` give Core's reason, score and code.
The scores and codes come from `state.DoS` and `state.Invalid` at each line (D84, lines 12 to 19 and 35 to 53).
Source review, not a theorem, connects the step and these observables to Core.

The step has these adapter errors, which are not Core verdicts:

- `heightOutOfRange`: the predecessor is at `maxPrevHeight`, 2147483646, or above, so the candidate would be at height 2147483647 (decision 17).
  The ordinary branch checks it after step 4 and before step 5.
  The genesis branch also checks it when `addToBlockIndex` would link the genesis header to an entry at that height, where Core has no check.
  Every entry of a well-formed index then stays below 2147483647.
- `adjustedTimeOutOfRange` and `contextual`: the adapter errors of `contextualCheckBlockHeader` at step 5, such as `shortView` or `nextWork missingAncestor` below an anchor.
- `notWellFormed`: the step never returns it.
  `checkWellFormed` is the executable form of `WellFormed` (`checkWellFormed_iff`), and the sequence of stage 3 runs it before the first header.

The step makes three choices where Core's source gives no behaviour on the model's domain:

- Core's `GetAncestor` fails its assertion on `pprev` when a walk passes below an anchor (D35, line 131).
  `ancestorHashAt` ends the walk at an anchor, and `isAncestorInIndex` then finds no ancestor (the record's section 5.3).
- Core visits `gFailedBlocks` in address order (D33, line 180).
  `failedAncestor?` visits the failed list in list order (decision 5).
  `failedAncestor_verdict_perm` proves that, on a well-formed index, the order changes no verdict, except that a `failedAncestor` rejection can name another member.
It says nothing about the resulting index.
  The marks can also differ.
- Core's `AddToBlockIndex` inserts the new entry and then searches for `hashPrevBlock` (D33, lines 2770 and 2772).
  `addToBlockIndex` searches the input index.
  The two differ only for a header whose `hashPrevBlock` is its own hash, a fixed point of double SHA-256.
  Core links that genesis entry to itself at height 1, and the model inserts a root at height 0 (`accept_genesis_insert`).
  Design record 0008, section 13.1, accepts this difference, because a self-link would break `WellFormed` and `wellFormed_preserved`.

The theorems in `Block.Proofs.HeaderSequence` hold for every network and context.
Each target of the record's section 11 takes an index that satisfies `WellFormed`, as the record requires, even when its proof does not use it:

- `accept_known`: a known hash other than genesis whose entry has no failure flag is accepted with the input index.
  When its entry has a failure flag, the step returns `duplicate` with the input index.
  No proof-of-work check runs (item 6).
- `accept_genesis_known`: with an entry under the genesis hash, the step accepts and returns the input index, even when the entry has a failure flag (item 1).
- `accept_genesis_insert`: without that entry, and without an entry under the header's `hashPrevBlock`, the step inserts an entry with no predecessor, height 0 and no flags.
  Its chain work is `blockProof` of its `nBits` (stage 4, as section 13.1 of the record says).
- `accept_genesis_parent`: without that entry, but with an entry under `hashPrevBlock`, the step links the new entry to it or returns `heightOutOfRange`.
- `accept_eq_ok_iff`: an unknown hash other than genesis is accepted exactly when five conditions hold.
  Step 2 passes, and the predecessor exists without a flag below `maxPrevHeight`.
  The contextual check accepts, and the predecessor has `scriptsValid` or no member of the failed list is its ancestor.
- `accept_eq_error_iff`: for a hash other than genesis, each rejection occurs exactly when its condition fails and the conditions of all earlier steps hold.
  It combines `accept_eq_duplicate_iff`, `accept_eq_highHash_iff`, `accept_eq_prevBlockNotFound_iff`, `accept_eq_prevBlockInvalid_iff`, `accept_eq_contextual_iff` and `accept_eq_failedAncestor_iff`.
  `accept_eq_heightOutOfRange_iff` is its companion: `heightOutOfRange` occurs exactly when steps 1 to 4 pass and the predecessor is at height 2147483646.
- `accept_ok_insert` and `accept_link`: an acceptance of an unknown hash other than genesis inserts one entry.
  The entry has the predecessor `hashPrevBlock`, the predecessor's height plus one and no flags.
  `accept_ok_insert` also gives its chain work, the predecessor's chain work plus `blockProof` of its `nBits`.
  The failed list does not change.
- `accept_error_index`: an adapter error, or a rejection other than `failedAncestor`, returns the input index.
  `failedAncestor` changes only `failedChild`, on the keys of `failedChildPath`, and keeps the failed list.
- `wellFormed_preserved`: each step maps a well-formed index to a well-formed index.
- `failedAncestor_verdict_perm`: with a permutation of the failed list, the two verdicts are equal, or both are `failedAncestor`. The resulting indexes can differ.
- `checkWellFormed_iff`: `checkWellFormed` returns true exactly when the index satisfies `WellFormed`.

Design record 0008, section 13.1, replaces the target `accept_genesis` with `accept_genesis_known`, `accept_genesis_insert` and `accept_genesis_parent`.
The original target said that the genesis entry gets no predecessor and height 0.
`addToBlockIndex` follows Core and links the genesis header to an entry under its `hashPrevBlock` when the index has one.
For the real genesis header, that entry needs a header that hashes to zero, and for another header a collision with the genesis hash.
`WellFormed` does not exclude it, and no theorem can exclude it without a cryptographic assumption.
So `accept_genesis_insert` states the hypothesis that the index lacks `hashPrevBlock`, and `accept_genesis_parent` covers the other case.

These theorems establish the behaviour of DogeLib's definitions.
The index, its anchors, failure flags, validity flags and failed list, the adjusted time and the checkpoint option are inputs.
No theorem says that they are the state and the context that a node holds.

`lake test` runs the step through the compiled code:

- The regtest fixture (D83): the first header of each of its 33 cases with headers.
  Each step uses the request's index, failed list, adjusted time and checkpoint option.
  `checkWellFormed` accepts every index.
  The expected verdict, reason, DoS score, reject code, adapter error, added entries and marks are the fixture's hand-derived values.
  For a case with several headers, the first step is accepted when the fixture fails at a later position.
  It then adds the first entry of the fixture's `added` list.
- 23 mainnet steps with real headers, from the pure fixtures and from the full fixtures D80–D82.
  The expected acceptances come from chain acceptance, and each other result comes from hand derivation from D33 and the record.
  Each expected hash is a literal from the fixture READMEs, the chain parameters or an independent `hashlib` computation, or the `hashPrevBlock` field of the next fixture header.
  No expected hash comes from `PureBlockHeader.getHash`, which derives only the keys of the input index.
  A fork at 144990 below an anchor at checkpoint 145000 gives `bad-fork-prior-to-checkpoint` with checkpoints enabled, with DoS 100 and code `0x43`.
  With checkpoints disabled, the step accepts it.
  A raised anchor at 144720 gives `nextWork missingAncestor` at the retarget 144960.
  The AuxPoW header at 371337 passes step 2 with its payload.
  The header at `BIP66Height` with base version 2 gives `high-hash`.
  Its payload commits to the real header's hash, and step 2 runs before check 7.
- Two synthetic steps with the mined regtest headers: a predecessor at 2147483646 gives `heightOutOfRange`, and one at 2147483645 gives `shortView`.
  Five cases of `checkWellFormed` accept and reject small indexes.

These known-answer checks do not run Core.
The [header-sequence comparison](../comparison-evidence.md#header-sequence-comparison-evidence) supplies separate finite evidence from Core's `AcceptBlockHeader`.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| None | `markFailedChild_failedBlocks`, `HeaderIndex.lookup_withFailed` |
| `propext` | `HeaderStepError.ofContextual_eq_rejection_iff`, `HeaderStepError.ofContextual_ne_heightOutOfRange` |
| `propext`, `Quot.sound` | `addToBlockIndex_of_unknown`, `ancestorWalk_withFailed`, `ancestorHashAt_withFailed`, `isAncestorInIndex_withFailed` |
| `propext`, `Classical.choice`, `Quot.sound` | `checkWellFormed_iff`, `accept_known`, `accept_genesis_known`, `accept_genesis_insert`, `accept_genesis_parent`, `accept_ok_hash`, `accept_eq_ok_iff`, `accept_unknown_ok`, `accept_ok_insert`, `accept_link`, the six `accept_eq_*_iff` rejection theorems, `accept_eq_heightOutOfRange_iff`, `accept_eq_error_iff`, `lookup_markFailedChild`, `accept_error_index_other`, `accept_error_failedAncestor`, `accept_error_index`, `HeaderIndex.lookup_insert`, `wellFormed_insert`, `wellFormed_addToBlockIndex`, `wellFormed_of_shape`, `wellFormed_markFailedChild`, `wellFormed_preserved`, `contextualCheckInIndex_withFailed`, `failedAncestor_verdict_perm` |

## The sequence: `processNewBlockHeaders`

`processNewBlockHeaders` in `DogeLib.Block.HeaderSequence` specifies Core's `ProcessNewBlockHeaders` (D33, lines 3270 to 3286) on the block-index model (design record 0008, stage 3).
It first tests `checkWellFormed`, and returns the adapter error `notWellFormed` at position 0 when the index fails it.
It then runs `acceptBlockHeader` on each header in order, with one `HeaderContext` for the whole call, and stops at the first error (lines 3274 to 3282).

The result holds the index after the last step that ran.
So the entries of the earlier headers stay, and so do the marks of a rejection at step 6.
On success, the result holds the hash of the last header, or `none` for an empty list.
On failure, it holds a `HeaderSequenceError`: the position of the failing header and the error of its step.
`composeSequence` combines the results of two lists, as section 7.2 of the record states.
Source review, not a theorem, connects the loop to Core's.

The function makes these choices where it differs from Core's code or leaves part of it out:

- It does not require that a header links to the header before it, and neither does Core's function.
  The `headers` message handler checks the count limit of 2000 and the links before it calls the function (D74, lines 2390 to 2475).
  Design record 0008, decision 10, keeps these peer checks outside the model.
- Core sets `ppindex` after each accepted header, so after a failure it points to the last accepted entry.
  A failure of the model holds no hash.
  The `headers` handler returns without reading `ppindex` after a rejection (D74, lines 2459 to 2467).
- `NotifyHeaderTip` (line 3284) changes no state that the model holds.

Three inputs are execution boundaries.
No theorem says that a caller supplies the values that a node holds:

- **The adjusted time.** Core reads `GetAdjustedTime()` once for each header, so the clock can advance during a call (item 11 of the record).
  The model takes one value for the whole call (decision 6).
  `process_adjustedTime_mono` covers one later value for the whole call.
  No theorem covers a value that changes between two headers.
- **The checkpoint option.** `checkpointsEnabled` stands for `fCheckpointsEnabled` (D69), as in [contextual header validation](#contextual-header-validation).
  The last checkpoint itself comes from the index at each step.
  So a checkpoint block that an earlier header of the call adds counts for the later headers.
- **The initial index.** Its anchors, failure flags, validity flags, failed list and the chain work of each supplied entry are inputs.
  `checkWellFormed` checks the conditions of `WellFormed`, but no theorem says that the index is the state that a node holds.
  `WellFormed` does not constrain chain work, so a supplied entry can carry any value.

The theorems in `Block.Proofs.HeaderSequence` hold for every network and context.
Each target takes an index that satisfies `WellFormed`, as section 11 of the record requires, even when its proof does not use it:

- `process_append`: processing `xs ++ ys` gives `composeSequence xs.length` of the result of `xs` and the result of `ys` from the index after `xs`.
  The theorem needs no height budget.
- `process_error_suffix`: if processing `xs` fails, processing `xs ++ ys` fails with the same position, the same error and the same index.
- `process_prefix_ok`: if processing `xs ++ ys` succeeds, processing `xs` succeeds.
- `process_linear`: the linear case of option S3, design record 0008, section 5.2.
  Let the headers link in order from the entry `tip` (`LinksFrom`), with `tip.height + n < 2147483647`.
  Let the index have none of their hashes, let the hashes be distinct, and let none be the genesis hash.
  Let `tip` have no failure flag, and let no member of the failed list be `tip` or an ancestor of it.
  Then the sequence succeeds exactly when each header passes step 2 and the contextual check.
  The check of the header at position `i` runs on `linearView` of the `i` earlier headers, newest first.
  `ancestorView` of `tip` in the input index follows them.
  Its last checkpoint is `lastCheckpointInIndex` of the index after the earlier headers, `addHeaders index (headers.take i)`.
- `process_height`: in the same setting, a success puts the entry of the header at position `i` at height `tip.height + i + 1`, with the predecessor `hashPrevBlock`.
- `process_no_failure`: from an index without failure flags and with an empty failed list, no step returns `duplicate`, `prevBlockInvalid` or `failedAncestor`.
  The result index has no failure flag and an empty failed list (item 19).
- `process_adjustedTime_mono`: if the sequence accepts with one adjusted time, it gives the same result with every later adjusted time up to `maxAdjustedTime`.
- `process_complete`: take an index without anchors, an adjusted time of at most `maxAdjustedTime`, and `n` headers.
  If every height in the index plus `n` is below 2147483647, and `n` is at most 2147483647, the sequence returns no adapter error.

Two hypotheses read the record's wording in a specific way:

- `process_linear` reads "their hashes are unknown" as unknown when each step runs: the input index lacks them, and they are distinct.
  A later header with the hash of an earlier header would be a known header, accepted without its checks.
  Such a list needs a fixed point or a cycle of double SHA-256, and no theorem excludes it without a cryptographic assumption.
- `process_complete` also takes `n ≤ 2147483647`.
  The record states its budget as every height in the index below `2147483647 − n`, which holds for every `n` when the index has no entry.
  From the empty index, the header at position `k` gets height `k`, with genesis at position 0.
  So the header at position 2147483647 is the first that can get `heightOutOfRange`.
  A list of 2147483648 or more valid headers reaches it, and `n ≤ 2147483647` excludes exactly those lists (design record 0008, section 13.2).

The proof module defines `LinksFrom`, `linearView`, `addHeaders`, `linkedEntry` and `LinearSetting` for these statements.
The specification does not use them.

`lake test` runs the sequence through the compiled code:

- The regtest fixture (D83): all 34 cases in full, each with the request's index, failed list, adjusted time, checkpoint option and headers.
  The fixture derives every expected field by hand.
  The fields are the outcome, failure position, reason, DoS score, reject code, adapter error, marks, added entries in insertion order and last hash.
  Stage 4 adds the chain work of each added entry.
- 14 mainnet sequences with real headers, from the pure fixtures and from the full fixtures D80–D82.
  Each call uses the latest header time of its list as the adjusted time.
  The expected acceptances come from chain acceptance, and each other result comes from hand derivation from D33 and the record.
  Each sequence ends below the last record of its fixture.
  So each expected hash is the `hashPrevBlock` field of the next fixture header, or a pinned literal, never a value of `PureBlockHeader.getHash`.
  - The genesis range from an empty index inserts the genesis entry and extends it to height 11.
    An empty list accepts with no hash and no change.
  - From the anchor 144719, 300 headers cross the retarget at 144960, DigiShield at 145000 and the checkpoint 145000, which enters the index during the call.
  - With the genesis range in the same index, the header at height 11 follows the headers up to 145000, on a branch below that checkpoint.
    With checkpoints enabled, it fails check 4 at position 271 with `bad-fork-prior-to-checkpoint`, DoS 100 and code `0x43`, and the 271 earlier entries stay.
    With checkpoints disabled, the call accepts all 272 headers.
  - An anchor without history gives `shortView` at position 0.
    A raised anchor at 144720 gives `nextWork missingAncestor` at the retarget, position 229, and the earlier entries stay.
  - The headers across 371337, `BIP66Height` and `BIP65Height` are accepted, and the checkpoint 371337 enters during its call.
    A version change at each activation height gives `high-hash` at its position: step 2 runs before the contextual check.

These known-answer checks do not run Core.
The [header-sequence comparison](../comparison-evidence.md#header-sequence-comparison-evidence) supplies separate finite evidence from Core's `AcceptBlockHeader`.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| `propext` | `composeSequence_of_error` |
| `propext`, `Quot.sound` | `lookup_addToBlockIndex_of_some`, `lookup_addHeaders_of_some`, `contextualViewDepth_antitone` |
| `propext`, `Classical.choice`, `Quot.sound` | `processSteps_eq_compose`, `processSteps_append`, `wellFormed_processSteps`, `processNewBlockHeaders_of_wellFormed`, `processNewBlockHeaders_of_not_wellFormed`, `process_append`, `process_error_suffix`, `process_prefix_ok`, `accept_ok_index`, `processSteps_ok_index`, `linearView_cons`, `ancestorView_congr_walk`, `ancestorWalk_insert_fresh`, `ancestorHashAt_insert_fresh`, `isAncestorInIndex_linked`, the `LinearSetting` theorems `foundPrev`, `unknownHead`, `addToBlockIndex_eq`, `next`, `accept_ok_iff`, `ancestorWalk_linked`, `steps_ok_iff`, `walk` and `lookup_addHeaders`, `process_linear`, `process_height`, `lookup_addToBlockIndex`, `accept_no_failure`, `process_no_failure`, `accept_adjustedTime_mono`, `processSteps_adjustedTime_mono`, `process_adjustedTime_mono`, `ancestorWalk_last_zero`, `accept_complete`, `processSteps_complete`, `process_complete` |
