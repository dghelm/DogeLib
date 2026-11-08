# Soundness

This document says what the proofs of DogeLib establish, and what a user of DogeLib trusts on top of them.

No formal verification is absolute.
A proof links a Lean definition to a theorem. Both are assumed to match something outside Lean: the Dogecoin behavior, the code that runs, and what the client needs.
Each of those links is an assumption, and this document names them one by one.
It follows the structure of EthLib's [`SOUNDNESS.md`](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/SOUNDNESS.md), which follows s2n-bignum's.
The current EthLib pin `bb6dfe5` expands that document with coverage that DogeLib does not adopt.

[COVERAGE.md](COVERAGE.md) lists the definitions and their theorems.
Each section states the mitigations that exist today, and the policy for definitions that are not written yet.
A lane that adds a definition, a theorem, an execution path or a dependency updates the affected rows in the same change.

## Ways to use DogeLib

Each way of using DogeLib trusts a different set of things, so the summary table marks which risks apply to which use.
There are four uses:

- **P**: a Lean proof that imports the specification.
- **R**: a Lean program that runs the specification, such as the oracle.
- **I**: an implementation that is proved to refine the specification, such as extracted Rust.
- **F**: a client that compares against the fixtures in `tests/`.

## Summary

The risks fall into four gaps, one per link in the chain from Dogecoin behavior to client.
Gap A asks whether the definition says what Dogecoin does and what the client needs.
Gap B asks whether the code that runs matches the definitions.
Gap C asks whether the proof itself is sound.
Gap D asks whether the use of DogeLib holds together.

| ID | Risk | Mitigation in place | Applies to |
|----|------|---------------------|------------|
| A1 | A definition does not match the pinned Dogecoin behavior | Source mappings, independent known answers and comparisons with pinned Core guard against a wrong definition. Lean model equivalence still requires source review. See [A1](#a1-a-wrong-definition) and [operation evidence](COVERAGE.md#operations). | P R I F |
| A2 | A theorem holds only under a hypothesis | Policy: each conditional theorem lists its hypotheses here and in `COVERAGE.md` | P I |
| A3 | Timing reveals secret data | None: no constant-time claim | R I |
| A4 | A security theorem idealises a primitive | None: no security theorem yet | P |
| A5 | A rule depends on a protocol context that the definition does not model | Policy: each operation records its mode, network and era in `SOURCES.md` | P R I F |
| B1 | The Lean compiler, the C compiler or the Lean runtime is wrong | Known answers and Core comparisons exercise the compiled specification on finite inputs. They do not prove compiler or runtime correctness. See [B1](#b1-the-compilers-and-the-runtime) and [operation evidence](COVERAGE.md#operations). | R |
| B2 | Lean core runs code other than its definitions | Lean core is a declared baseline | R |
| B3 | Elaboration runs native code | None yet | P |
| B4 | The oracle's IO adapter or a foreign boundary is wrong | Oracle fixtures and Core comparisons check adapter results on the recorded inputs, and the declaration check includes `Exports`. See [B4](#b4-the-oracle-and-foreign-boundaries) for the trusted conversions and harness boundaries. | R F |
| B5 | This repository substitutes compiled code | `lake exe check-decls` fails on any new substitution | R |
| B6 | Extraction or the Rust toolchain is wrong | `decode_refines` relates the extracted Rust reader model to `decodeBounded`. Charon, Aeneas, library models, the Rust compiler and runtime remain trusted. See [B6](#b6-extraction-and-the-rust-toolchain). | I |
| C1 | The Lean kernel or its axioms are unsound | `lake exe check-decls` rejects transitive axiom dependencies outside the allowed set, including imported unfinished proofs. Kernel soundness and axiom consistency remain trusted. | P I |
| C2 | A proof trusts compiled code | `lake exe check-decls` fails on any use | P I |
| C3 | A declaration reached the environment unchecked | No kernel replay. The declaration check requires every production module to be reachable from its default roots. | P I |
| D1 | A client misuses an operation, such as a prefix decoder where complete consumption is required | Policy: each public operation documents its input domain and consumption contract | R I |
| D2 | A dependency changes | Source and toolchain pins constrain dependency changes. The root package has no Lake dependencies, while the separate refinement package owns Aeneas and Mathlib. See [D2](#d2-dependency-changes). | P R I |
| D3 | The fixtures are wrong | Each fixture records its provenance. The NIST CAVP files, Wycheproof P1363 records and Core's `sighash.json` are pinned by digest, and CI checks the pins. Core's test cases are copied into `tests/KnownAnswers/` topic modules with their file and line. | F |

## What the proofs say

Each operation with a theorem has a subsection here.
It says what is proved, under which hypotheses and over which input domain, and what is not proved.
[COVERAGE.md](COVERAGE.md) gives the per-operation status. This section explains its meaning and limits.

### SHA-1

`Sha1.hash_eq_spec` equates `Sha1.hash` with `Sha1.Spec.hash` for every whole-byte message with `message.size < 2 ^ 61`.
`Sha1.hash_size` gives twenty output bytes for every message.
The definition is total beyond that bound, where its encoded bit length wraps modulo 2^64.
The theorem makes no FIPS compatibility claim on those longer messages.
`hash_eq_spec` depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.
`hash_size` depends on `propext` and `Quot.sound`.

The model uses 32-bit bit vectors and five named working variables.
Its round function, constants, schedule recurrence, block recursion and digest restate FIPS 180-4 §6.1.2 separately from the executable SHA-1 definitions.
The executable code reuses SHA-256's padding, big-endian reader, Ch and Maj.
The model reuses SHA-256's independent padding and input-word model, because FIPS 180-4 §5.1.1 and §5.2.1 prescribe both for SHA-1.
`f_toBitVec` relates the reused Ch and Maj to independent bit-vector expressions.
A reader must still compare this model with FIPS and pinned Core's `CSHA1` (A1).

The Core source review covers the portable `Transform` body and its `Round`, `f1`, `f2`, `f3` and `left` helpers.
The ARMv8 and experimental AVX2 bodies are outside that source review.

`lake test` checks 65 short and 64 long NIST messages and 100 Monte Carlo checkpoints through compiled `Sha1.hash`.
The Monte Carlo procedure makes 100,000 hash calls, following SHAVS §6.4.
The same test checks Core's ten SHA-1 cases, including two million-byte messages.
[Fixture provenance](tests/cryptography/sha1/cavp/README.md) records the NIST files and checksums.
Core cases come from `sha1_testvectors` and `LongTestString` at the pinned revision.
These finite tests do not prove compiled-code equivalence to Core (B1).

SHA-1 has [broken collision resistance](https://csrc.nist.gov/News/2017/Research-Results-on-SHA-1-Collisions).
The functional equality theorem establishes no collision-resistance, preimage-resistance or other security property.
No cryptographic assumption enters the theorem.

### SHA-256

`hash_eq_spec` says that `hash` equals `Spec.hash` on every message shorter than 2^61 bytes.
`Spec.hash` restates FIPS 180-4 over 32-bit bit vectors, with separate padding, schedule, round and block definitions.
The model shares the round constants `K` with the executable code.
The theorem depends on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` with Lean `v4.35.0`.

The theorem does not show that `Spec.hash` matches FIPS 180-4.
A reader checks that by comparing the model with the standard (A1).
`lake test` runs the 129 byte-oriented NIST CAVP vectors through the compiled `hash` (B1).
The vectors come from NIST, not from the code under test, and `tests/cryptography/sha256/cavp/README.md` records their provenance.
They test the compiled code only on those inputs.

The SHA-256 definition and proof adapt EthLib at commit `6a93711`.
The current pin `bb6dfe5` restructures them in `d59f0e3a`, which DogeLib has not ported.

### HMAC-SHA-256

`Hmac.hmac_eq_spec` equates the executable with a separate list model for every byte-array key and message.
The model adapts verified-garbage's `Spec/Hmac.lean` at the pin, under BSD-3-Clause, and retains its bit-vector byte representation.
Its hash is a parameter, instantiated with DogeLib's executable SHA-256 through byte conversions.
`fromBytes_toBytes` and `toBytes_fromBytes` prove both conversion round trips.
The executable and structural lemmas adapt EthLib's HMAC files at the pin.
The existing DogeLib SHA-256 API requires no algorithm changes to those files.

`Hmac.hmac_eq_fips` replaces the executable hash with the FIPS 180-4 model.
Its hypotheses require `key.size < 2^61` and `64 + message.size < 2^61`.
The inner hash input has `64 + message.size` bytes, and the outer input has 96 bytes.
A key longer than 64 bytes is hashed before zero padding.
The bound on the key admits that hash input.
Both theorems state algorithm equalities, with no cryptographic assumption or security conclusion.

`hmac_eq_spec` and the conversion round trips depend on `propext` and `Quot.sound`.
`hmac_eq_fips` also depends on `Classical.choice`, by `#print axioms` on Lean `v4.35.0`.

A reader must compare the list model with RFC 2104 §2 and FIPS 198-1 §4 (A1).
The Lean compiler, C compiler and runtime remain trusted (B1), including Lean core's byte-array operations (B2).
`lake test` compares the compiled executable with all seven RFC 4231 HMAC-SHA-256 cases.
Case 5 fixes only the first 16 bytes, and cases 6 and 7 exercise 131-byte keys.
No theorem or test here establishes agreement with compiled Core or constant-time behaviour (A3).

### PBKDF2-HMAC-SHA-256

`Pbkdf2.pbkdf2_eq_spec` equates the executable with the separate list model for every password, salt, natural iteration count and output length.
The equality includes `none` above `(2^32 - 1) * 32` output bytes.
Zero iterations uses `U₁`, and zero output bytes returns an empty result.
Those cases extend RFC 8018 §5.2, which requires positive iterations and output length.
For an admitted output length, `nb_lt` bounds the number of blocks below 2^32.
Thus the four-byte block indices do not wrap during derivation.

The model adapts verified-garbage's `Spec/Pbkdf2.lean` at the pin, under BSD-3-Clause, with its list and bit-vector representation unchanged.
The generic block lemmas adapt `Proof/Pbkdf2/Whole/Common.lean` at the same pin.
`Spec.iterate_congr` adapts `Proof/Pbkdf2/Memory.lean` at that pin.
The HMAC instance uses executable SHA-256, as `Hmac.hmac_eq_spec` does.

`pbkdf2_eq_fips` replaces that hash with the FIPS 180-4 model under `password.size < 2^61` and `64 + salt.size + 4 < 2^61`.
Those bounds admit the long-key hash and the first inner hash with salt and four counter bytes.
Every later HMAC message has 32 bytes, and each outer hash input has 96 bytes.
The corollary covers all natural counts and lengths, including rejection and both zero extensions.
It assumes no cryptographic property and proves no security claim.

`pbkdf2_eq_spec`, `pbkdf2_eq_fips` and `block_eq_fips` depend on `propext`, `Classical.choice` and `Quot.sound`.
`iterate_eq_spec`, `blocks_eq_spec`, `Spec.iterate_congr` and `nb_lt` depend on `propext` and `Quot.sound`, by `#print axioms` on Lean `v4.35.0`.
A reader must compare the list model with RFC 8018 §5.2 (A1).
The Lean compiler, C compiler, runtime and Lean core byte-array operations remain trusted (B1, B2).
The executable uses whole-message HMAC and makes no constant-time or resource-bound claim (A3).
No runtime substitution or trust-policy exception is added.

`lake test` compares both complete 64-byte RFC 7914 §11 outputs through compiled code, including the 80,000-iteration case.
It also checks prefixes of the first vector and the zero-count, empty-output and oversized-output branches.
The RFC errata search, read on 2026-11-06, has no correction to those vectors.
No theorem or test here establishes agreement with compiled Core.

### Scrypt RFC 7914 model

`Cryptography.Hash.Scrypt.Spec` adapts verified-garbage's `Spec/Scrypt.lean` at the pin, under BSD-3-Clause.
It retains lists of `BitVec 8`, 32-bit words, and the quadratic ROMix reference fill.
The PBKDF2 model uses DogeLib's executable SHA-256 through HMAC.
The general scrypt definition has no FIPS-based equality theorem.
`Pbkdf2.pbkdf2_eq_fips` remains a separate result with password and salt bounds.
For Dogecoin's parameters, `powHash_eq_fips` states the digest with the FIPS 180-4 model, as the [next subsection](#dogecoins-scrypt-digest) describes.

`blockMix_eq` expresses the output as the even-indexed `Y` blocks followed by the odd-indexed blocks, for every byte list and natural block parameter.
`serialize_length`, `salsa_length` and `yAt_length` give 64-byte outputs.
`blockMix_length` and `repeat_blockMix_length` preserve `128 * r` bytes under that input-length hypothesis.
These structural lemmas adapt VG's `Proof/Scrypt/BlockMix.lean` and the length lemmas of `Proof/Scrypt/RoMix.lean`.
They do not prove agreement with the RFC or Core (A1).

`fillLoop_eq` relates sequential array fill to the reference list of iterates, for every step function, count, initial state and initial array.
It equates both the stored states and the final state.
`fill_eq_spec` specializes it to BlockMix and an empty array.
The generic theorem applies to an implementation that stores whole states as array elements.
It provides no flattening theorem for a flat word array or commutation theorem for a conversion between state types.
Each of these two theorems, `blockMix_eq`, and the five length lemmas above depends on `propext` and `Quot.sound`, by `#print axioms`.

The component operations are total outside their RFC length domains.
Word reads supply zero for missing bytes, XOR truncates, and natural subtraction saturates at zero.
The top-level `scrypt` checks the published parameter bounds and delegates the output upper bound to PBKDF2.
The [errata review](tests/cryptography/scrypt/README.md#errata) records the retained parameter bound and Integerify interpretation (A1).
The model introduces no cryptographic hypothesis and makes no side-channel or resource-bound claim (A3).

The compiled known answers compare complete RFC 7914 outputs for Salsa20/8, BlockMix, ROMix and the `N = 16` scrypt case.
The [test cost report](tests/cryptography/scrypt/README.md#test-cost) distinguishes those passes from timed-out optional cases.
These comparisons rely on the compiler and runtime (B1), and are not kernel digest proofs (C2).
This model has no Core comparison or full header proof-of-work claim.
The [next subsection](#dogecoins-scrypt-digest) relates Dogecoin's executable to it.

### Dogecoin's scrypt digest

`Scrypt.scrypt_1024_1_1_256` follows Core's `scrypt_1024_1_1_256_sp_generic` and `xor_salsa8` (D61, lines 121–218).
Its input type, `Bytes 80`, admits exactly 80 bytes.
`powHash_eq_spec` runs `Spec.scrypt` on every such input, as password and salt, with N = 1024, r = 1, p = 1 and 32 output bytes.
It states that the model returns `some` of the executable's digest bytes.
The theorem has no hypothesis.
The model's HMAC uses DogeLib's executable SHA-256, as `Pbkdf2.pbkdf2_eq_spec` does.

`powHash_eq_fips` restates the digest with HMAC over the FIPS 180-4 SHA-256 model.
It writes scrypt out as its three steps for p = 1.
They are PBKDF2 to 128 bytes, scryptROMix with r = 1 and N = 1024, and PBKDF2 to 32 bytes.
It uses `Pbkdf2.pbkdf2_eq_fips` twice. The password has 80 bytes and the salts have 80 and 128 bytes, far below its bounds.
It does not restate `Spec.scrypt` with a second hash instance, so it adds no model definition.

The proof crosses the representation in these lemmas:

- `doubleRound_toBitVec`: the executable runs the 32 statements of each double round in Core's order.
  `step_comm` shows that two steps commute when neither writes a word that the other reads or writes.
  `columnsCore_eq` and `rowsCore_eq` sort Core's interleaved quarter-rounds into the RFC order of `Spec.doubleRound`.
  A reader compares the executable's statements with Core's text, but not Core's order with the RFC order.
- `xorSalsa8_toBitVec` and `blockMix_toModel`: `xor_salsa8(&X[0], &X[16])` and `xor_salsa8(&X[16], &X[0])` equal the model's `blockMix 1` under `toModel`, which serializes `X[0..31]` as little-endian words.
- `fill_flat`: the flat scratchpad `V` holds the words of the states that `fillLoop` stores whole, so `fillLoop_eq` gives the model's reference fill.
- `index_eq` and `integerify_toModel`: `32 * (X[16] & 1023)` in 32-bit arithmetic is 32 times Integerify of the model state modulo 1024.
- `flat_getElem!_lo` and `flat_getElem!_hi`: each `!` read of the scratchpad in the second loop is in bounds, so its default value is never used.
- `decode_toModel` and `encode_toBytes`: `le32dec` and `le32enc` convert between the 128 PBKDF2 bytes and the word state.
- `pbkdf2_some`: PBKDF2 with one iteration returns `some` for 128 and 32 output bytes, so the executable's `getD` defaults are never used.

`powHash_eq_spec` and `powHash_eq_fips` depend on `propext`, `Classical.choice` and `Quot.sound`, by `#print axioms` on Lean `v4.35.0`.
No theorem evaluates a scrypt digest in the kernel (C2).
The theorems relate two DogeLib definitions.
A reader must still compare the executable with D61 and the model with RFC 7914 (A1).
They say nothing about memory layout, so the little-endian and no-padding assumption of design record 0004, section 6, still applies to any comparison with Core.
They also cover only the generic Core variant, not the SSE2 variant.

`lake test` runs the five header and digest pairs of Core's `scrypt_hashtest` (D62) through the compiled executable, with the expected digests reversed from display order.
With `DOGELIB_SCRYPT_MODEL` set, it also runs the first pair through the compiled model.
The [test report](tests/cryptography/scrypt/README.md#dogecoin-header-digests) records the cost.
These runs rely on the compiler and runtime (B1).
`scrypt.hash` compares the five exact output digests and seeded header mutations with generic Core scrypt.

[Header proof of work](#header-proof-of-work) composes the digest with `checkProofOfWork` and `CheckAuxPowProofOfWork`.
The executable makes no constant-time or resource-bound claim (A3).

### Double SHA-256

`Sha256d.hash` is `CHash256` of Dogecoin Core (SOURCES.md, D8): SHA-256 applied to the SHA-256 digest of the message.
`size_hash` says that the digest has 32 bytes.
`hash_eq_spec` says that `Sha256d.hash` equals the FIPS 180-4 model applied twice, on every message shorter than 2^61 bytes.
The inner digest has 32 bytes, so the outer application needs no hypothesis of its own.
`hash_eq_spec` depends on `propext`, `Classical.choice` and `Quot.sound`, and `size_hash` on `propext` and `Quot.sound`, by `#print axioms`.

`lake test` checks the compiled `Sha256d.hash` against four values that Dogecoin Core asserts.
They are the genesis merkle root and the genesis block hashes of the main, test and regression-test networks.
The bytes to hash are derived by hand from `src/chainparams.cpp`, and the derivation is in `tests/KnownAnswers/Genesis.lean`.

Neither theorem says how Dogecoin orders the bytes of a hash for display, or which bytes it hashes.
Those belong to the definitions of the objects that are hashed.

### Pure headers and transaction Merkle roots

`PureBlockHeader.decode_encode` preserves every raw field and arbitrary trailing bytes.
`decode_sound` identifies the consumed prefix as the returned header's encoding.
`encode_length` establishes exactly 80 bytes, and `getHash_val` identifies their double SHA-256 digest.
These claims cover the pure header even when its version sets the AuxPoW bit.
Core's full `CBlockHeader` then carries an AuxPoW payload, which the full header codec of the next subsection reads (D41).

[Header proof of work](#header-proof-of-work) covers scrypt proof of work and `CheckAuxPowProofOfWork`.
No theorem establishes contextual header validity beyond [version gating](#version-gating).

[The AuxPoW check](#the-auxpow-check) covers `CAuxPow::check` alone.

`computeMerkleRoot_nil` and `computeMerkleRoot_singleton` cover empty and one-leaf lists.
`merkleLevel_duplicate_last` equates the next levels before and after explicit duplication of an odd level's final leaf.
Its prefix-length hypothesis establishes that the final leaf is unpaired.
`merkleMutated_of_equal` detects any equal aligned leaf pair after an even-length prefix.

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

`tests/block/README.md` records the independent fixtures and the limits of their provenance (A1, B1, D3).
The later header expectations rely on successor commitments or an independent hashlib computation, not Core output.
The isolated fetched blocks have no authenticated chain connection.
Finite comparisons and structural theorems do not establish collision resistance or transaction validity.
The checked header codec, length, digest and Merkle structural proofs depend on `propext` and `Quot.sound`, by `#print axioms`.
The declaration check inspects all declarations under the unchanged standard-axiom policy (C1, C2).

### Full headers and the AuxPoW payload

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
It also checks their proof of work, as the [fixture report](tests/block/core-header-pow.json) records.

By `#print axioms`, the round trips and truncation theorems depend on `propext`, `Classical.choice` and `Quot.sound`, and the other codec theorems on `propext` and `Quot.sound`.
The two concrete examples are checked by kernel reduction with `rfl`.

### The AuxPoW check

`AuxPow.check` follows `CAuxPow::check` (D55, lines 80 to 161) statement by statement.
Its helpers follow `CheckMerkleBranch` (lines 189 to 206), `getExpectedIndex` (lines 163 to 187), `GetChainId` (D10) and `std::search`.
Each `return error` of the source has one constructor of `AuxPowCheckError`, which names its line, and `check` returns the first failing test.
The source review, not a theorem, connects these definitions to Core.

`check` takes `fStrictChainId` as a Boolean, because it reads no other field of the parameter record.
Which record a caller selects, and so which value it passes, is outside this operation.
The block hash and the chain ID are arguments: `CheckAuxPowProofOfWork` passes the merge-mined header's own hash and its own chain ID (C7 of design record 0004).

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
`checkMerkleBranch_eq_fold` takes the side of step `k` from bit `min k 31` of the index.
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
[The comparison report](docs/oracle.md#header-proof-of-work-evidence) describes the streams and mutation seed.

By `#print axioms`, the search and `getExpectedIndex_mod64` theorems depend on `propext` and `Quot.sound`, and the others on `propext`, `Classical.choice` and `Quot.sound`.

### Header proof of work

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
`powHash_eq` and `powHash_eq_spec` relate the digest to `scrypt_1024_1_1_256` and to the RFC 7914 model, as [Dogecoin's scrypt digest](#dogecoins-scrypt-digest) describes.

The record carries `nAuxpowChainId`, `fStrictChainId` and the retarget fields of the Core record, of which only `powLimit` is read.
`checkAuxPowProofOfWork_congr` shows that the result depends on the record only through those three fields.

`ParamsTree.getConsensus` repeats the search of `GetConsensus` (D14, lines 494 to 506) over the AuxPoW projection of each network's records.
`getAuxPowParams_eq_work` shows that it selects the same effective height and retarget fields as `Work.getConsensus`, at every UInt32 height.
`checkAuxPowProofOfWork_getAuxPowParams` proves that, in each network, every selected record gives the result of the height-zero record.
So `CheckBlockHeader`, which reads the height-zero record, and the disk reads, which read the record of the block's height, agree on every header.
The theorem is about the transcribed records.
A transcription mistake in D14 would make it a claim about the wrong records (A1).

`checkBlockHeader` takes the network as an argument.
DogeLib does not model the selection of `Params()` or the other checks of `CheckBlock` and `ContextualCheckBlockHeader`, except `checkVersion`.
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
The [fixture report](tests/block/core-header-pow.json) records the byte identities, network, parameters and Core verdicts.
The [comparison](docs/oracle.md#header-proof-of-work-evidence) also changes parent and child targets, nonces and version bits.
Lean diagnostics stay outside the compared verdict.

The Core harness ports `mineBlock` and `auxpow_pow` and mines their nonces again on every comparison.
It checks the 12 predicate assertions, 11 mining assertions and two version/hash assertions against the source test.
The [comparison records](tests/block/auxpow-pow.json) preserve the exact components and Core verdicts.
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

### Version gating

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

### Contextual parameters and checkpoints

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

### Contextual header validation

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
  `contextualViewDepth_eq` gives its values.
  On mainnet and testnet, the depth is 241 below candidate height 145000 and 11 from it.
  On regtest, it is 14401 below candidate height 10 and 11 from it.
- `contextualCheck_complete`: a view that passes `validateWorkView` and reaches height 0, with an adjusted time in the domain, gives only Core rejections, never an adapter error.
- `badVersion_iff`: let `b` be the signed remainder of `nVersion` by 256.
  Check 7 rejects exactly when `b` is below 3 from `BIP66Height`, or below 4 from `BIP65Height`, with each network's heights.

These theorems establish the behaviour of DogeLib's definitions.
`block.contextual_check` compares the compiled specification with H2 of design record 0006.
The harness transcribes D33, lines 3066 to 3119, and calls Core's helpers for each compared value.
It compares `valid` and the first `reject_reason`, excluding Lean diagnostics.
The [comparison stream](docs/oracle.md#contextual-header-comparison-evidence) includes 2231 real mainnet candidates, hand-derived boundaries and 500 mutations with seed `20261109`.
The comparison gives finite evidence, not an equivalence theorem with compiled Core.

The H2 transcription is an evidence boundary (A1).
A mistake in its branch order or reject strings could make a wrong specification agree with the harness.
Independent source review compares it line by line with D33.
Hand-derived expected verdicts and reasons provide a separate check.

The harness links `checkpoints.cpp`, owns its block-index map, and inserts each known table hash with its table height.
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

### The block-index model

`DogeLib.Block.HeaderSequence` specifies the part of Core's block index that `AcceptBlockHeader` reads (design record 0008, stage 1).
`HeaderIndex` holds the entries of `mapBlockIndex` (D69, lines 169 and 170) as an association list, and the members of `gFailedBlocks` (D33, line 180) as a list.
Each `IndexEntry` holds the pure header, the height and the hash of its predecessor (D18, lines 164 to 171).
It also holds the two failure flags and a flag for the validity level `BLOCK_VALID_SCRIPTS` (D18, lines 136, 146 and 147).
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
These checks do not run Core, and the Core comparison is stage 5 of the record.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| None | `HeaderIndex.insert_failedBlocks` |
| `propext` | `HeaderIndex.lookup_insert_of_ne` |
| `propext`, `Quot.sound` | `ancestorWalk_length_le`, `ancestorWalk_take` |
| `propext`, `Classical.choice`, `Quot.sound` | `HeaderIndex.lookup_insert_self`, `ancestorWalk_valid`, `ancestorWalk_eq_ancestorChain`, `ancestorView_congr_chain`, `ancestorView_congr`, `lastCheckpointInIndex_eq` |

### One step: `acceptBlockHeader`

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
7. `addToBlockIndex`, the index part of `AddToBlockIndex` (lines 2755 to 2788), without chain work, `nTimeMax`, `pindexBestHeader` and the dirty set.

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
  `failedAncestor_verdict_perm` proves that the verdict does not depend on that order, but the marks can differ.
- Core's `AddToBlockIndex` inserts the new entry and then searches for `hashPrevBlock` (D33, lines 2770 and 2772).
  `addToBlockIndex` searches the input index.
  The two differ only for a header whose `hashPrevBlock` is its own hash, a fixed point of double SHA-256.
  Core links that genesis entry to itself at height 1, and the model inserts a root at height 0 (`accept_genesis_insert`).
  Design record 0008, section 13.1, accepts this difference, because a self-link would break `WellFormed` and `wellFormed_preserved`.

The theorems in `Block.Proofs.HeaderSequence` hold for every network and context.
Each target of the record's section 11 takes an index that satisfies `WellFormed`, as the record requires, even when its proof does not use it:

- `accept_known`: a known hash other than genesis is accepted with the input index.
  When its entry has a failure flag, the step returns `duplicate` with the input index.
  No proof-of-work check runs (item 6).
- `accept_genesis_known`: with an entry under the genesis hash, the step accepts and returns the input index, even when the entry has a failure flag (item 1).
- `accept_genesis_insert`: without that entry, and without an entry under the header's `hashPrevBlock`, the step inserts an entry with no predecessor, height 0 and no flags.
- `accept_genesis_parent`: without that entry, but with an entry under `hashPrevBlock`, the step links the new entry to it or returns `heightOutOfRange`.
- `accept_eq_ok_iff`: an unknown hash other than genesis is accepted exactly when five conditions hold.
  Step 2 passes, and the predecessor exists without a flag below `maxPrevHeight`.
  The contextual check accepts, and the predecessor has `scriptsValid` or no member of the failed list is its ancestor.
- `accept_eq_error_iff`: for a hash other than genesis, each rejection occurs exactly when its condition fails and the conditions of all earlier steps hold.
  It combines `accept_eq_duplicate_iff`, `accept_eq_highHash_iff`, `accept_eq_prevBlockNotFound_iff`, `accept_eq_prevBlockInvalid_iff`, `accept_eq_contextual_iff` and `accept_eq_failedAncestor_iff`.
  `accept_eq_heightOutOfRange_iff` is its companion: `heightOutOfRange` occurs exactly when steps 1 to 4 pass and the predecessor is at height 2147483646.
- `accept_ok_insert` and `accept_link`: an acceptance of an unknown hash other than genesis inserts one entry.
  The entry has the predecessor `hashPrevBlock`, the predecessor's height plus one and no flags.
  The failed list does not change.
- `accept_error_index`: an adapter error, or a rejection other than `failedAncestor`, returns the input index.
  `failedAncestor` changes only `failedChild`, on the keys of `failedChildPath`, and keeps the failed list.
- `wellFormed_preserved`: each step maps a well-formed index to a well-formed index.
- `failedAncestor_verdict_perm`: with a permutation of the failed list, the two results are equal, or both are `failedAncestor`.
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

These checks do not run Core, and the Core comparison is stage 5 of the record.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| None | `markFailedChild_failedBlocks`, `HeaderIndex.lookup_withFailed` |
| `propext` | `HeaderStepError.ofContextual_eq_rejection_iff`, `HeaderStepError.ofContextual_ne_heightOutOfRange` |
| `propext`, `Quot.sound` | `addToBlockIndex_of_unknown`, `ancestorWalk_withFailed`, `ancestorHashAt_withFailed`, `isAncestorInIndex_withFailed` |
| `propext`, `Classical.choice`, `Quot.sound` | `checkWellFormed_iff`, `accept_known`, `accept_genesis_known`, `accept_genesis_insert`, `accept_genesis_parent`, `accept_ok_hash`, `accept_eq_ok_iff`, `accept_unknown_ok`, `accept_ok_insert`, `accept_link`, the six `accept_eq_*_iff` rejection theorems, `accept_eq_heightOutOfRange_iff`, `accept_eq_error_iff`, `lookup_markFailedChild`, `accept_error_index_other`, `accept_error_failedAncestor`, `accept_error_index`, `HeaderIndex.lookup_insert`, `wellFormed_insert`, `wellFormed_addToBlockIndex`, `wellFormed_of_shape`, `wellFormed_markFailedChild`, `wellFormed_preserved`, `contextualCheckInIndex_withFailed`, `failedAncestor_verdict_perm` |

### The sequence: `processNewBlockHeaders`

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
- **The initial index.** Its anchors, failure flags, validity flags and failed list are inputs.
  `checkWellFormed` checks the conditions of `WellFormed`, but no theorem says that the index is the state that a node holds.

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

These checks do not run Core, and the Core comparison is stage 5 of the record.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Block.Proofs.HeaderSequence` |
| --- | --- |
| `propext` | `composeSequence_of_error` |
| `propext`, `Quot.sound` | `lookup_addToBlockIndex_of_some`, `lookup_addHeaders_of_some`, `contextualViewDepth_antitone` |
| `propext`, `Classical.choice`, `Quot.sound` | `processSteps_eq_compose`, `processSteps_append`, `wellFormed_processSteps`, `processNewBlockHeaders_of_wellFormed`, `processNewBlockHeaders_of_not_wellFormed`, `process_append`, `process_error_suffix`, `process_prefix_ok`, `accept_ok_index`, `processSteps_ok_index`, `linearView_cons`, `ancestorView_congr_walk`, `ancestorWalk_insert_fresh`, `ancestorHashAt_insert_fresh`, `isAncestorInIndex_linked`, the `LinearSetting` theorems `foundPrev`, `unknownHead`, `addToBlockIndex_eq`, `next`, `accept_ok_iff`, `ancestorWalk_linked`, `steps_ok_iff`, `walk` and `lookup_addHeaders`, `process_linear`, `process_height`, `lookup_addToBlockIndex`, `accept_no_failure`, `process_no_failure`, `accept_adjustedTime_mono`, `processSteps_adjustedTime_mono`, `process_adjustedTime_mono`, `ancestorWalk_last_zero`, `accept_complete`, `processSteps_complete`, `process_complete` |

### RIPEMD-160 and Hash160

`Ripemd160.hash` adapts EthLib's executable definition at `6a93711`, as SOURCES.md records.
The current pin `bb6dfe5` adds bounds hypotheses in `4f798a14`, which DogeLib has not ported.
Its UInt32 arithmetic wraps, and its eight-byte length suffix reduces the bit length modulo 2^64.
Source inspection compares the tables, round functions, constants, padding and digest order with Core's `CRIPEMD160` at the compatibility pin.
This inspection is not a Lean equivalence proof.

For every message, `hash_size` proves a twenty-byte digest.
The padding theorems prove whole blocks, minimal zero padding, preservation of message bytes, the delimiter, zero bytes and the length-byte suffix.
The suffix theorem identifies `lengthBytes message.size`, without separately proving a mathematical decoding theorem for those bytes.
The constant theorems check integer square-root and cube-root inequalities.
The table theorems check that each sixteen-step group includes every word index.
Fourteen kernel-checked fixed-vector theorems cover eight published messages and six selected padding boundaries.

No theorem equates `Ripemd160.hash` with a separate model of RIPEMD-160.

`Hash160.hash_eq_composition` states the defining composition: executable RIPEMD-160 applied to executable SHA-256.
It holds for every message and does not establish independent functional correctness of the composition.
`Hash160.size_hash` proves a twenty-byte digest for every message.
Neither operation has a theorem about collision resistance, preimage resistance or constant-time execution.

With Lean `v4.35.0`, `#print axioms` reports `propext` and `Quot.sound` for both digest-size theorems and `hash_eq_composition`.
The RIPEMD-160 padding theorems use the same axioms, with `Classical.choice` also used by `pad_length_suffix`.
Both constant theorems use `propext` and `Quot.sound`, and the table theorems use only `propext`.
The fourteen fixed-vector theorems use all three standard axioms.

`lake test` checks nine author vectors and ten Core RIPEMD-160 vectors, including both million-byte Core messages.
It also checks twelve Hash160 digests produced by hashlib and independently matched by compiled Core `CHash160`.
Some author and Core records share an input and digest.
The fixture README records provenance, versions, encodings and checksums.
These comparisons cover the recorded inputs, and do not prove equality to Core on every message.
The compiler and runtime boundaries remain those of Gap B.

### Secp256k1 curve and ECDSA scalar verification

`Cryptography.Secp256k1.Ecdsa.verify` checks a point, a `Hash256` digest and natural R and S.
It rejects infinity, off-curve points and scalars outside `1 ≤ r, s < n`.
It reads the digest bytes big-endian in storage order and reduces the result modulo `n`.
It computes `u1 G + u2 Q` in Jacobian coordinates, converts to affine coordinates, and compares `x mod n` with R.
It rejects a result at infinity.
The scalar predicate `isLowS` is separate and does not restrict `verify`.

The arithmetic adapts EthLib at `bb6dfe55198243682bc2eaf94611af2dbce1be6f` without changes to its formulas (SOURCES.md E7 to E11).
The source argument for Core's verification equation is design record 0005, section 4.3.
That argument requires parsed points and scalars, and is not an equivalence theorem about the arithmetic implementation or Core's compiled code.
No general theorem here proves primality, the group law, inverses, square roots, scalar multiplication or the Jacobian formulas.
EthLib's Mathlib-dependent proofs are outside this adaptation.
No theorem states that SEC 1 signing produces a signature that this verifier accepts.

There is no unforgeability or constant-time claim.

`Ecdsa.wycheproof_p1363_1` kernel-checks one accepted verification on the stated coordinates, digest, R and S.
`lake test` checks 234 scalar pairs against independent Wycheproof expectations (W1).
Eighteen other P1363 records have signatures of a different length and check only the fixture boundary.
The fixture README records their provenance and the distinction.
These finite checks establish no all-input correctness claim.
`#print axioms` reports `propext`, `Classical.choice` and `Quot.sound` for `Ecdsa.wycheproof_p1363_1`.

Four theorems relate `verify` to Core's final test, `secp256k1_ecdsa_sig_verify` (SOURCES.md D60, lines 207 to 275):

- `verify_r_zero` and `verify_s_zero`: a zero R or S gives `false`, as Core's lines 216 to 218 do.
- `verify_of_valid`: for `0 < r < n`, `0 < s < n` and a key on the curve other than infinity, `verify` is the test on `Point.mulAdd u1 G u2 Q`. It gives `false` at infinity and otherwise compares `x mod n` with R.
- `xmod_eq_iff`: for `x < p` and `r < n`, `x mod n = r` holds exactly when `x = r`, or `r + n < p` and `x = r + n`. Core tests those two cases in Jacobian coordinates (lines 244 to 272), so on an affine `x` the two tests agree.

The [public-key parser and Core's verifier](#secp256k1-public-key-parser-and-cores-verifier) connect `verify` to Script.
No foreign code decides a scalar verification in the Lean specification.
Compiled evaluation still depends on the compiler and runtime (B1 and B2).

### Secp256k1 public-key parser and Core's verifier

`Cryptography.Secp256k1.parsePubKey` is `secp256k1_ec_pubkey_parse` of the libsecp256k1 copy in Core at the pin (SOURCES.md D5, D52, D58 and D59).
It is written from that source, not adapted from EthLib, and it accepts the hybrid encodings `06` and `07`.
It omits the subgroup test, which returns true outside libsecp256k1's exhaustive-test build because the cofactor of secp256k1 is 1.
`Script.coreVerifier` is `CPubKey::Verify` (D50, lines 168 to 186) on a 64-bit build.
It runs Core's steps in order: `isValidPubKey`, `parsePubKey`, the empty-signature test, `parseDerLax`, S normalization and `Ecdsa.verify`.
The theorems are in `DogeLib.Cryptography.Proofs.Secp256k1.PubKey` and `DogeLib.Script.Proofs.CoreVerifier`.

For every input:

- `parsePubKey_valid`: a parsed key is a point on the curve other than infinity.
- `parsePubKey_hybrid_even` and `parsePubKey_hybrid_odd`: a hybrid key parses as the `04` key with the same coordinates. The result stays only when the parity of `y` matches the first byte.
- `isValidPubKey_of_parsePubKey`: a parsed key passes `isValidPubKey`.
- `coreVerifier_some`: `coreVerifier` always answers `some`. `transactionChecker_coreVerifier_some`: so does every `checkSig` request of `transactionChecker` with a script code shorter than 2^64 bytes.
- `coreVerifier_invalidKey`, `coreVerifier_badPoint`, `coreVerifier_emptySig` and `coreVerifier_badDer`: Core's first four steps give `some false`.
- `coreVerifier_eq_verify`: otherwise the result is `Ecdsa.verify` on the parsed point, the digest, R and `normalizeS S`.
- `parseDerLax_lt`: the lax parser stores scalars below `n`, for every size of `size_t`. `normalizeS_le_half`: after normalization S is at most half the order, so the high-S test of `secp256k1_ecdsa_verify` never rejects. `normalizeS_lt`: the normalized S is below `n`, and zero only when S is.
- `coreVerifier_normalize`: two signatures that parse to `(r, s)` and `(r, n − s)` give the same result for every key and digest.
- `coreVerify_valid`: on the request of `coreVerifier_eq_verify`, R and the normalized S are below `n` and the point passes the key test. With `verify_r_zero`, `verify_s_zero` and `verify_of_valid`, `coreVerifier` then rejects a zero R or S, as Core does, and otherwise computes the test on `Point.mulAdd`.
- `hashToInt_legacyOne`: the fixed digest one of `SIGHASH_SINGLE` gives `e = 2^248`, the value that Core's storage-order read gives.
- `multisigRecovery_sound_coreVerifier`: the soundness direction of the worked property with `coreVerifier`, with no verifier hypothesis.

These theorems leave one step of the agreement with Core unproved.

**Arithmetic agreement with Core (design record 0005, section 4.3).**

Take R and S in `[1, n − 1]`, a key `Q` from `parsePubKey` and the digest scalar `e`.
Then `Point.mulAdd (e · s⁻¹) G (r · s⁻¹) Q`, with `Fn.inv`, must be the affine form of Core's `secp256k1_ecmult` result `u1 G + u2 Q` (D60, lines 220 to 227).
This includes the case in which that result is the point at infinity.
A proof needs the group law, correct Jacobian formulas, a correct `Fn.inv` and the primality of `n`.
Each of these needs Mathlib (design record 0005, decision 3), so until a proof exists, this step is an A1 claim.
The comparison obligation has finite evidence from 598 dedicated `pubkey.verify` inputs, all with agreeing verdicts:

- 464 Wycheproof bitcoin cases, with Core as the verdict source because Core normalizes high S.
- Four Core-signed inputs and two reversed digest-one inputs.
- 20 key and signature parser boundaries.
- 36 constructed infinity cases, all rejected.
- 24 constructed verification points with `x ∈ [n,p)`, all accepted, and 24 changed-S cases, all rejected. Another 24 mismatched-R cases retain x above `n` and reject.

The [fixture notes](tests/cryptography/secp256k1/README.md) record their provenance and constructions.
The comparison also gives agreeing verdicts on all 925 Script corpus records and 159 eligible transaction inputs.
These include the 44 records and 60 inputs that require signature verification.
The 2,000 legacy transaction mutations give 1,956 agreeing verdicts and 44 unsupported flags.

These checks close the comparison obligation of stage 3.
They do not prove that `mulAdd` agrees with `secp256k1_ecmult` on every scalar and point, or compare intermediate points.
The group-arithmetic and inverse claim remains unproved.

`decompress` relies on `Fp.sqrt`, which returns a root only after it checks the square.
No theorem says that it finds a root whenever `x^3 + 7` is a square.
That needs Euler's criterion, and the known answers are its present evidence.

The claim covers a 64-bit build of Core, because `parseDerLax` fixes `sizeof(size_t)` at 8 bytes.
A 32-bit build can differ only on a signature of at least 2^24 bytes (design record 0005, section 3).

`lake test` checks the parser on libsecp256k1's own `ec_pubkey_parse_pointtest` at the pin (D57).
The test tries 23 points with every first byte and every length from 3 to 65, and its formulas give the expectations.
`lake test` also runs 11 `coreVerifier` hand cases and both Core corpora with `coreVerifier`, as [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker) states.
These finite checks establish no all-input correctness claim.
The oracle's `transaction` checker uses `coreVerifier`, and `pubkey.verify` calls `Script.coreVerify` for one signature ([docs/oracle.md](docs/oracle.md#public-key-verification)).
The Core harness answers the same requests with Core's `CPubKey::Verify`.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `modulus_lt_two_mul`, `secp256k1Order_eq`, `secp256k1Order_eq_half` | None |
| `hashToInt_legacyOne` | `propext` |
| `parseDerLax_nil`, `normalizeS_le_half`, `normalizeS_sub` | `propext`, `Quot.sound` |
| `Fp.neg_mul_neg`, `decompress_valid`, `parsePubKey_valid`, `parsePubKey_hybrid_even`, `parsePubKey_hybrid_odd`, `isValidPubKey_of_parsePubKey`, `verify_r_zero`, `verify_s_zero`, `xmod_eq_iff`, `verify_of_valid`, the `coreVerifier_*` theorems, `coreVerify_valid`, `laxStore_lt`, `parseDerLaxWith_lt`, `parseDerLax_lt`, `normalizeS_lt`, `transactionChecker_coreVerifier_some`, `multisigRecovery_sound_coreVerifier` | `propext`, `Classical.choice`, `Quot.sound` |

### Codecs

A codec has an encoder `encode : α → List UInt8` and a prefix decoder `decode : List UInt8 → Option (α × List UInt8)`.
The class `LawfulCodec` in `DogeLib.Serialization.Proofs.Codec` states two laws:

- `decode_encode`: for every value `a` and all bytes `rest`, `decode (encode a ++ rest) = some (a, rest)`.
- `decode_canonical`: for all bytes `bs`, if `decode bs = some (a, rest)`, then `bs = encode a ++ rest`.

The laws hold with no hypothesis for the codecs of `UInt8`, `UInt16`, `UInt32` and `UInt64` (`instLawfulCodecUInt8` to `instLawfulCodecUInt64`).
They also hold for the little-endian codec of `BitVec (8 * n)`, for every `n` (`lawfulCodec_bitVecCodecLE`).
They hold for a pair of lawful codecs (`instLawfulCodecProd`).
`LawfulCodec.ofEquiv` proves them for a codec carried along two functions, under the hypothesis that the functions are inverse to each other.
Each fixed-width instance discharges that hypothesis by `rfl`.
`encode_injective` follows from the round trip for every lawful codec.

The laws also hold for the codec of byte strings of a fixed length `n`, for every `n` (`instLawfulCodecBytes`), and so for `Hash256`, which is `Bytes 32`.
`decodeBytes_eq_none_iff` says that this decoder rejects exactly the inputs with fewer than `n` bytes.

A decoder that satisfies these laws rejects every input that does not start with a canonical encoding.
The laws do not say which values a Dogecoin rule accepts.
For example, Core's CompactSize reader rejects some canonical encodings, so `CompactSize.decodeBounded` is not a codec and has its own contract (see *CompactSize*).
A decoder returns a remainder, and a client that needs the whole input consumed checks that the remainder is empty (D1).

The byte order of the integer codecs follows Core's `ser_writedata16` to `ser_writedata64` and `ser_readdata16` to `ser_readdata64`, by a reading of the source code (A1).
`lake test` checks the compiled list and packed codecs against fields of the main-network genesis header and the genesis coinbase.
Their bytes are hexadecimal literals whose double SHA-256 is the digest that Core asserts, and their values are the arguments of `CreateGenesisBlock` (SOURCES.md, D9).
These known answers cover `UInt8` to `UInt64`, pairs, truncated input, and slices that start at a nonzero offset.
They are not a comparison with Core on other inputs.

### Packed codecs

A packed codec encodes into a `ByteArray` and decodes from a `ByteSlice`.
The class `LawfulPackedCodec` in `DogeLib.Serialization.Proofs.PackedCodec` states its agreement with a list codec:

- `toList_encodeInto`: for every value `a` and buffer `acc`, the bytes of `encodeInto a acc` are the bytes of `acc` followed by `encode a`.
- `abstractParse_decodeSlice`: for every slice `s`, the packed decoder fails exactly when `decode s.toList` fails.
  If both succeed, they return the same value, and the bytes of the remaining slice equal the remainder of `decode`.

Agreement holds with no hypothesis for the packed codecs of `UInt8` to `UInt64` (`instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`).
It also holds for the packed little-endian codec of `BitVec (8 * n)`, for every `n` (`lawfulPackedCodec_packedBitVecLE`).
It holds for a pair of agreeing packed codecs (`instLawfulPackedCodecProd`), and for every transport (`LawfulPackedCodec.ofEquiv`).
It holds for the packed codec of `Bytes n`, for every `n` (`instLawfulPackedCodecBytes`).
`LawfulPackedCodec.toList_encode` and `LawfulPackedCodec.abstractParse_decode` give the same agreement for a whole byte array.

The agreement theorems are about the Lean definitions of the packed codecs.
The compiled packed codecs run core's `@[extern]` implementations of `ByteArray.push` and `ByteArray.get`, and advance slices without copying.
`ByteSlice.toList`, the abstraction function of the agreement laws, copies the bytes in view through `ByteArray.extract`, which runs `ByteArray.copySlice`.
The packed decoder of byte lists also calls it to read its bytes.
The tests call `toList` to compare results, so they run that copy too.
No theorem covers these implementations (B1, B2).

### Axioms of the codec theorems

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `Bytes.length_val` | None |
| `LawfulCodec.ofEquiv`, `LawfulPackedCodec.ofEquiv`, `encode_injective`, `setWidth_setWidth_eq_self`, `instLawfulCodecBytes`, `decodeBytes_encode`, `decodeBytes_canonical`, `Bytes.encode_length`, `Bytes.ofListExact?_eq_some_iff`, `Bytes.ofListExact?_val`, `Bytes.val_reverse`, `Bytes.reverse_reverse`, `Hash256.length_displayBytes`, `Hash256.ofDisplayBytes?_displayBytes`, `Hash256.displayBytes_ofDisplayBytes?` | `propext` |
| `instLawfulCodecProd`, `instLawfulCodecUInt8` to `instLawfulCodecUInt64`, `lawfulCodec_bitVecCodecLE`, `decodeBitVecLE_encodeBitVecLE`, `decodeBitVecLE_canonical`, `instLawfulPackedCodecProd`, `toList_pushBitVecLE`, `LawfulPackedCodec.toList_encode`, `ByteArray.toList_eq_data_toList`, `decodeBytes_eq_none_iff`, `toList_pushBytes` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecUInt8` to `instLawfulPackedCodecUInt64`, `abstractParse_readBitVecLE`, `LawfulPackedCodec.abstractParse_decode`, `LawfulPackedCodec.abstractParse_decode_toByteArray`, `ByteSlice.toList_of_uncons_some`, `ByteSlice.toList_drop`, `instLawfulPackedCodecBytes`, `abstractParse_readBytes` | `propext`, `Classical.choice`, `Quot.sound` |

The source files are adapted from btc-verified at commit `ecf4f0d`. None of them uses `bv_decide` (C2).

### Packed base-mode transaction reader

`Transaction.readBaseSlice` implements the base-mode prefix reader over `ByteSlice`.
`Transaction.abstractRead_readBaseSlice` states, for every slice `s`:

```lean
abstractRead (Transaction.readBaseSlice s) = Transaction.readBase s.toList
```

The equality preserves every error, every transaction field and every remainder byte.
It has no success hypothesis or bound on the input slice.
The theorem composes complete-result agreement for fixed fields, reader combinators, bounded vectors and script bytes.

The bounded vector theorem assumes complete-result agreement of the element readers.
Its loop theorem covers every element count and every array accumulator.
The script reader checks `s.size` before it copies the consumed bytes.
The list reader remains the specification.

`lake test` exercises the slice reader on the genesis coinbase, signed fields, every proper genesis prefix and count errors at each field.
It compares complete base-mode results on the 159 base-mode and 39 witness-format corpus records.
These comparisons use nonzero slice offsets with bytes outside both bounds.
A base-mode read of a witness-format record does not establish witness parsing.

The benchmark in BUILDING.md measures generated workloads separately from this conformance evidence.
There is no theorem about execution time, allocation or stack use.
Core's compiled byte-array operations remain trusted (B1, B2).

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `abstractRead_readFixedSlice`, `abstractRead_readPairSlice`, `abstractRead_readMapSlice`, `CountedList.abstractRead_readElemsBoundedSliceLoop` | `propext` |
| `CountedList.abstractRead_decodeBoundedSlice`, `CountedList.abstractRead_readBytesSlice`, `CountedList.abstractRead_decodeBoundedBytesSlice`, `OutPoint.abstractRead_readSlice`, `Script.abstractRead_readSlice`, `TxIn.abstractRead_readSlice`, `TxOut.abstractRead_readSlice`, `Transaction.abstractRead_readBaseSlice` | `propext`, `Classical.choice`, `Quot.sound` |

### CompactSize

`DogeLib.Serialization.CompactSize` defines two decoders of the CompactSize format.
`decode` is the generic canonical decoder, and `decodeBounded` is Core's `ReadCompactSize` (SOURCES.md, D1).
The theorems are in `DogeLib.Serialization.Proofs.CompactSize`.

The generic codec `CompactSize.codec` satisfies both codec laws on every `UInt64` (`lawfulCodec`, from `decode_encode` and `decode_canonical`).
The packed codec `CompactSize.packedCodec` agrees with it on every value and every slice (`lawfulPackedCodec`).
`encode_length_le` says that an encoding has at most 9 bytes.
`encode_head` says that an encoding starts with a byte that is `0x00` only for the value 0.

Two relations state the accepted bytes without reference to a decoder.
`CanonicalCompactSizePrefix bytes value rest` lists the four forms.
For each form it gives the marker, the number of payload bytes, the little-endian value of the payload, and the smallest value.
`rest` is the bytes after the encoding.
`ValidCompactSizePrefix` adds `value ≤ 0x02000000`.
Each of these theorems holds for all bytes, values and remainders:

- `decode_eq_some_iff`: `decode bytes = some (value, rest)` exactly when `CanonicalCompactSizePrefix bytes value rest`.
- `decodeBounded_eq_ok_iff_valid`: `decodeBounded bytes = ok (value, rest)` exactly when `ValidCompactSizePrefix bytes value rest`.
- `decodeBounded_eq_ok_iff_decode`: `decodeBounded bytes = ok (value, rest)` exactly when `decode bytes = some (value, rest)` and `value ≤ 0x02000000`.
- `decodeBounded_eq_error_tooLarge_iff`: `decodeBounded bytes` is the error `tooLarge` exactly when `decode` accepts `bytes` with a value above `0x02000000`.
- `decodeBounded_encode`: for every `n ≤ 0x02000000` and all bytes `rest`, `decodeBounded (encode n ++ rest) = ok (n, rest)`.

The bound of the round trip is necessary.
`decodeBounded_encode_maxSize_succ` says that `decodeBounded (encode 0x02000001)` is `tooLarge`, and `decode_maxSize_succ` that `decode` accepts the same bytes, `fe 01 00 00 02`.

No theorem says which inputs give the errors `truncated` and `nonCanonical`.
The known answers check these errors on Core's `noncanonical` cases and on truncated inputs.
The order of Core's checks comes from a reading of `ReadCompactSize` (A1).
The relations are a second statement of the format, written from the same reading of D1, so a misreading of Core can be in both.
The known answers guard against that on the inputs they cover.

`lake test` runs Core's `compactsize` sweep of the powers of two up to `MAX_SIZE` and the cases of its `noncanonical` test (D20) through the compiled code.
The expected results are Core's assertions, or derived from D1 and from `CDataStream::read` (D21).
Core itself does not run, so this is not a Core comparison.

The packed codec runs core's `ByteArray.push` and `ByteArray.get`, as the other packed codecs do (B2).

`decodeBoundedSlice` is Core's reader over a `ByteSlice`.
`abstractRead_decodeBoundedSlice` compares it with `decodeBounded` on the bytes of each slice.
On every slice, it gives the same error, or the same value and remainder bytes.
`abstractRead` is the `Except` counterpart of `abstractParse`.
`lake test` runs the bounded cases through it at offset 3 of a buffer.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `maxSize_toNat` | None |
| `encode_maxSize_succ`, `encodeFixedWidth_length`, `abstractRead_error`, `abstractRead_ok` | `propext` |
| `lawfulCodec`, `decode_encode`, `decode_canonical`, `encode_length_le`, `encode_head`, `toUInt8_lt_fd`, `toUInt8_ne_zero`, `toList_encodeInto`, `readCanonical_toOption`, `decodeBounded_eq_error_tooLarge_iff`, `decode_maxSize_succ`, `decodeBounded_maxSize_succ`, `decodeBounded_encode_maxSize_succ` | `propext`, `Quot.sound` |
| `abstractRead_readPayloadSlice`, `abstractRead_readCanonicalSlice`, `abstractRead_decodeBoundedSlice`, `lawfulPackedCodec`, `abstractParse_decodeSlice`, `decode_eq_some_iff`, `decodeBounded_eq_ok_iff_decode`, `decodeBounded_eq_ok_iff_valid`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

Upstream proves two small facts in `decode_encode` and `encode_head` with `bv_decide`.
Here `toUInt8_lt_fd` and `toUInt8_ne_zero` prove them: each converts the bytes to natural numbers and closes the goal with `omega` (C2).
### Rust bounded CompactSize reader

`Refinement.Rust.CompactSize.decode_refines` compares the extracted Rust model `DogeLibRust.decode` with `CompactSize.decodeBounded`.
For every Rust-representable byte slice, the abstraction equals `some` of the specification's complete result.
The abstraction preserves `truncated`, `nonCanonical`, `tooLarge`, the decoded value and the remainder after the consumed count.
It maps a Rust panic or divergence to `none`, so the theorem also excludes those outcomes.
The theorem has no acceptance precondition.

`consumed_bounds` says that a successful consumed count is at most the input length and belongs to 1, 3, 5 or 9.
Both theorems hold on 32- and 64-bit platforms.
Their proofs do not select a platform word size.
B6 records the slice representation and extraction boundaries.

The Rust integration tests run the 20 bounded cases from `tests/KnownAnswers/Serialization.lean` and Core's 52-value power-of-two sweep.
The expected values and errors come from Core's assertions and a reading of D1 and D21.
These tests run the compiled Rust reader, without running Core or the generated Lean model.

By `#print axioms` with Lean `v4.35.0`:

| Declaration | Axioms |
| --- | --- |
| `DogeLibRust.join`, `DogeLibRust.decode`, `Refinement.Rust.CompactSize.abstractResult`, `Refinement.Rust.CompactSize.decode_refines`, `Refinement.Rust.CompactSize.consumed_bounds` | `propext`, `Classical.choice`, `Quot.sound` |

### Counted lists

`DogeLib.Serialization.CountedList` defines a counted list: a CompactSize count, then that many elements.
A `CountedList α` is a list with fewer than `2 ^ 64` elements.
As for CompactSize, there are two decoders.
`CountedList.decode` is the generic decoder, and `decodeBounded` is Core's `Unserialize_impl` for vectors (SOURCES.md, D1).
The theorems are in `DogeLib.Serialization.Proofs.CountedList`.

For every lawful element codec, the codec of counted lists satisfies both codec laws on every counted list (`instLawfulCodecCountedList`, from `decode_encode` and `decode_canonical`).
`decode_eq_some_iff` says that `decode` accepts exactly a count read by `CompactSize.decode`, followed by that many elements.
For every packed element codec that agrees with its codec, the packed codec of counted lists agrees with the codec (`instLawfulPackedCodecCountedList`).
The packed codec of byte lists does not call the element codec for each byte, and agrees with the same codec (`instLawfulPackedCodecCountedListBytes`).
Its decoder reads the bytes with `ByteSlice.toList`, so the compiled decoder runs `ByteArray.copySlice` (B2).
Its encoder appends each byte with `ByteArray.push`.

`decodeBounded` takes an element reader `elem`.
Its contract assumes that `elem` accepts exactly what the element codec accepts: `(elem bs).toOption = Codec.decode bs` for all bytes `bs`.
`readByte_toOption` discharges the assumption for `readByte` and `UInt8`.
Under the assumption, and for all bytes, counted lists and remainders:

- `decodeBounded_eq_ok_iff`: `decodeBounded elem bs = ok (cl, rest)` exactly when `decode bs = some (cl, rest)` and `cl` has at most `0x02000000` elements.
- `decodeBounded_encode`: if the element codec is also lawful and `cl` has at most `0x02000000` elements, then `decodeBounded elem (encode cl ++ rest) = ok (cl, rest)`.

Two theorems need no assumption on `elem`.
`decodeBounded_of_count_error` says that an error of Core's count reader is the error of the list reader.
So a count above `MAX_SIZE` is `tooLarge`, and no element is read.
`decodeBoundedBytes_eq` says that the block read of bytes, `decodeBoundedBytes`, is `decodeBounded readByte` on every input, including its errors.

No theorem says which error an element failure gives.
It is the error of `elem`, and a later layer that defines an element reader states it.
Core grows a vector in blocks of about 5 MB, and the definitions do not.
A reading of D1 and D21 says that the blocks change neither the elements read nor the error (A1).

`lake test` runs the two scripts of the genesis coinbase through the generic, packed and bounded decoders, at nonzero offsets.
It also runs short inputs for each error of the bounded reader.
The expected results are Core's bytes (D9), or derived from D1 and D21.
Core itself does not run, so this is not a Core comparison.

`decode`, `decodeSlice` and `decodeBounded` read the elements with loop forms: `decodeElemsLoop`, `readElemsLoop` and `readElemsBoundedLoop`.
Each one calls itself in tail position and keeps the values read so far in an array.
`decodeElemsLoop_nil`, `readElemsLoop_nil` and `readElemsBoundedLoop_nil` prove that each returns what the recursive form returns, including every failure and error.
So every theorem about `decodeElems`, `readElems` and `readElemsBounded` holds for the readers.

These theorems are about results, not about stack use. Stack use is an observation of the compiled code (B1).
In one manual run of the `lake test` driver, the recursive forms overflowed the stack at 16,000,000 elements, and the loop forms read 16,000,000.
In `lake env lean --run`, the recursive forms overflowed at 5,000,000.
An element reader that itself recurses deeply can still use more stack, and `MAX_SIZE` itself (33,554,432 elements) was not run.
CI reads lists of 3,000,000 elements through the three readers, which checks results, not stack use.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_toOption` | None |
| `ofList?_eq_some`, `val_of_ofList?`, `decodeElems_encodeElems`, `toList_pushElems`, `readElemsBounded_readByte`, `readElemsBoundedLoop_eq`, `readElemsBoundedLoop_nil` | `propext` |
| `decodeElemsLoop_eq`, `decodeElemsLoop_nil`, `readElemsLoop_eq`, `readElemsLoop_nil`, `instLawfulCodecCountedList`, `decode_encode`, `decode_canonical`, `decode_eq_some_iff`, `decodeElems_length`, `decodeElems_canonical`, `abstractParse_readElems`, `encode_uint8`, `decode_uint8_cons`, `decode_uint8_nil`, `encodeElems_uint8`, `decodeElems_uint8`, `decodeBounded_eq_ok_iff_parts`, `decodeBounded_of_count_error`, `readByte_toOption`, `decodeBoundedBytes_eq`, `decodeBoundedBytes_maxSize_succ`, `decode_maxSize_succ` | `propext`, `Quot.sound` |
| `instLawfulPackedCodecCountedList`, `instLawfulPackedCodecCountedListBytes`, `abstractParse_readByteList`, `decodeBounded_eq_ok_iff`, `decodeBounded_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream file uses no `bv_decide` (C2).

### Transactions

`DogeLib.Transaction` defines the fields of a transaction and its base serialization, the format without witness data (SOURCES.md, D4).
The types keep the raw bits of every field and check nothing.
`TxOut.value` and `Transaction.version` are the bits of Core's `int64_t` and `int32_t`.
`TxOut.toInt_amount` and `Transaction.toInt_signedVersion` say that the signed values are their two's-complement readings.
The theorems are in `DogeLib.Transaction.Proofs` and `DogeLib.Serialization.Proofs.Reader`.

Each codec is the codec of the tuple of its fields, carried to the structure by `Codec.ofEquiv`.
So the codec laws (`instLawfulCodecOutPoint` to `instLawfulCodecTransaction`) and the packed agreement (`instLawfulPackedCodecOutPoint` to `instLawfulPackedCodecTransaction`) follow by composition.
The codec reads counts with the generic CompactSize decoder, so it is not Core's reader.

`Transaction.readBase` is Core's `UnserializeTransaction` with `SERIALIZE_TRANSACTION_NO_WITNESS`.
It is built from readers of the fields with `readFixed`, `readPair`, `readMap` and `CountedList.decodeBounded`.
`ReaderAgrees c r P` says that the reader `r` accepts exactly what the codec `c` accepts with a value that satisfies `P`, with the same value and remainder.
Each construction preserves it (`readFixed_agrees`, `readPair_agrees`, `readMap_agrees`, `CountedList.decodeBounded_agrees`).
`Transaction.WithinMaxSize` says that the number of inputs, the number of outputs and the length of each script are at most `0x02000000`.
For all bytes, transactions and remainders:

- `Transaction.readBase_eq_ok_iff`: `readBase bs = ok (tx, rest)` exactly when the codec decodes `bs` as `(tx, rest)` and `tx.WithinMaxSize`.
- `Transaction.readBase_encode`: for every `tx` with `WithinMaxSize`, `readBase (encode tx ++ rest) = ok (tx, rest)`.
- `Transaction.decodeBaseComplete_eq_ok_iff`: the complete reader returns `tx` exactly when `readBase` returns `tx` with no remainder.

`Transaction.txid_val` says that the bytes of the transaction ID are the double SHA-256 digest of the base serialization.
So `txid` never takes the fallback branch of `digestToHash256`.
This says nothing about which values a digest can take.

These theorems relate the reader to the codec, and the codec to a reading of D4 (A1).
No theorem classifies every error against an independent Core error relation, or proves that the order of reads is Core's.
`lake test` checks the errors and their order on short inputs.
It also reads the genesis coinbase, whose ID must be the merkle root that Core asserts (D9).
Core itself does not run.

`lake test` also runs the base-mode records of Core's `tx_valid.json` and `tx_invalid.json` (D28, D29): 159 transactions.
For each one, `readBase` reads the whole transaction and `decodeBaseComplete` accepts it.
The codec writes the same bytes again, and the packed codec reads the same transaction.
Core's own tests check scripts, not these four properties, so these are DogeLib's checks on Core's bytes.

A record is in base mode when byte 4, the first byte of its input count, is not `00`. Then Core never reads a flags byte (D4, lines 219 to 230).
The 39 other records use the witness-allowed format, which the next section covers.

`readBase` is the base mode only.
Without `SERIALIZE_TRANSACTION_NO_WITNESS`, Core reads an empty input list as a marker and then a flags byte (A5).
A transaction with no inputs, `01000000 00 01 …`, has a different reading in that mode.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `TxOut.toInt_amount`, `Transaction.toInt_signedVersion` | None |
| `ReaderAgrees.congr`, `readFixed_agrees`, `readMap_agrees` | `propext` |
| `readPair_agrees`, `CountedList.readElemsBounded_eq_ok_iff_of_agrees`, `CountedList.readByte_agrees`, `instLawfulCodecOutPoint`, `instLawfulCodecScript`, `instLawfulCodecTxIn`, `instLawfulCodecTxOut`, `instLawfulCodecTransaction`, `OutPoint.read_agrees`, `Transaction.decodeBaseComplete_eq_ok_iff`, `digestToHash256_val`, `Transaction.txid_val` | `propext`, `Quot.sound` |
| `CountedList.decodeBounded_agrees`, `CountedList.decodeBoundedBytes_agrees`, `instLawfulPackedCodecOutPoint` to `instLawfulPackedCodecTransaction`, `Script.read_agrees`, `TxIn.read_agrees`, `TxOut.read_agrees`, `Transaction.readBase_agrees`, `Transaction.readBase_eq_ok_iff`, `Transaction.readBase_encode`, `Transaction.decodeBaseComplete_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The upstream files use no `bv_decide` (C2).

### Transactions: the witness-allowed format

`DogeLib.Transaction.Witness` models the format that Core reads and writes without `SERIALIZE_TRANSACTION_NO_WITNESS` (D4, lines 211 to 272).
It models a serialization format only.
At the pinned commit, `IsWitnessEnabled` returns false on every network (`src/validation.cpp`, lines 3002 to 3008, D36).
`ConnectBlock` uses that function, so it never enables `SCRIPT_VERIFY_WITNESS` (lines 1913 to 1917).
Separately, `ContextualCheckBlock` checks `DEPLOYMENT_SEGWIT` through versionbits directly for witness commitments (lines 3163 to 3181).
Without a checked commitment, it rejects witness data as `unexpected-witness` (lines 3183 to 3187).

The deployment timeout is 0 on main and test, and 999999999999 on regtest (`src/chainparams.cpp`, lines 111, 267 and 408, D9).
Thus main and test reject blocks with witness data.
Regtest's deployment parameters do not enable witness script verification.
No definition or theorem here says that a transaction in this format is valid, or that a network accepts it.

`WitnessTransaction` holds a `Transaction` and one `WitnessStack` per input. Its field `witnesses_length` requires the count.
`Transaction.readAllowWitness` follows Core's order of reads.
It reads the version and the input list, then the flags byte if that list is empty.
Then come the lists, the stacks, the check of the other flag bits, and the lock time.
`WitnessTransaction.WithinMaxSize` adds the bounds of each stack, its item count and each item's length, to `Transaction.WithinMaxSize`.

- `Transaction.readAllowWitness_eq_readBase`: suppose the first input list of the bytes is not empty.
  Then the reader returns what `readBase` returns, with an empty stack per input, and the same error.
- `WitnessTransaction.readAllowWitness_encode`: for every `w` with `WithinMaxSize`, `readAllowWitness (w.encode ++ rest) = ok (w, rest)`, if `w` has witness data, or an input, or no output.
- `noInputsExample_not_roundTrip`: a transaction with no inputs, one output and no witness data is not read back. The complete reader reports 7 bytes left over.
- `Transaction.readAllowWitness_flags_zero`: a zero input count and zero flags give a transaction with no inputs and no outputs.
- `readAllowWitness_flags_two`, `readAllowWitness_flags_three`: two complete transactions with flags `02` and `03` fail with `unknownOptionalData`.
- `readStacks_length`: the reader finds one stack per input, so its last check never fails.
- `WitnessTransaction.wtxid_of_hasWitness_false`: without witness data, the witness hash is the transaction ID.

No theorem says which error the reader reports.
`lake test` checks the error order on hand-built inputs, with expected results from a reading of D4.
The lists and stacks fail first, the other flag bits next, and the lock time last.

`lake test` also reads and writes again the 39 witness-format records of Core's corpus.
Each of them has witness data, so the writer uses the extended form.
`lake test` does not run Core.
`bash scripts/test_oracle.sh` checks both hashes against Python hashlib on all 198 corpus records, including the 39 with witness data.
`scripts/compare_core.py` compares both witness operations with pinned Core, including those 39 records and their malformed variants.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readElemsBounded_length`, `WitnessStack.isEmpty_iff` | `propext` |
| `instLawfulCodecWitnessStack`, `readStacks_length`, `Transaction.readAllowWitness_eq_readBase`, `noInputsExample_not_roundTrip`, `readAllowWitness_flags_two`, `readAllowWitness_flags_three`, `WitnessTransaction.wtxid_of_hasWitness_false` | `propext`, `Quot.sound` |
| `WitnessStack.read_agrees`, `WitnessTransaction.readAllowWitness_encode`, `Transaction.readAllowWitness_flags_zero` | `propext`, `Classical.choice`, `Quot.sound` |

### Legacy signature hash

`DogeLib.Transaction.LegacySighash` specifies Core's `SignatureHash` with `SIGVERSION_BASE` (SOURCES.md, D3).
`legacySignatureHashPlan` returns a `LegacyHashPlan`: the fixed digest `legacyOne`, or the bytes to hash with double SHA-256.
The preimage is written field by field after `CTransactionSignatureSerializer`, not by transforming a transaction and serializing it.
The theorems are in `DogeLib.Transaction.Proofs.LegacySighash`, except `readOp_rest_length`, `readPush_op_append` and `readOp_op_append`. Those are in the specification module, because `scanOps` and `findAndDelete` need them to terminate.
For every script code, transaction, input index and hash type:

- `legacySignatureHashPlan_eq_fixedDigest_iff`: the plan is `fixedDigest legacyOne` exactly when `nIn` is at least the number of inputs. With SINGLE, it is also `legacyOne` when `nIn` is at least the number of outputs.
- `legacySignatureHashPlan_eq_hashBytes`: otherwise the plan is `hashBytes (legacyPreimage …)`.
- `legacyPreimage_eq`: the preimage is a body, then the 4 bytes of the hash type. The body depends on the hash type only through its ANYONECANPAY, NONE and SINGLE flags. `HashType.flags_eq_of_and` says that the flags depend only on the bits `0x9f`.
- `scriptCodeBytes_eq_encode`: when no instruction parse failed and no instruction is `OP_CODESEPARATOR`, the script code is written as the ordinary encoding of the script.
- `readOp_eq_op_iff` and `readOp_eq_stop_iff`: `readOp` reads an instruction exactly when the bytes start with an opcode, its length field and its data. The field has the width that the opcode requires, and the data has the size that they give. It stops exactly on a short push or the empty script.

Two plans that are equal give equal digests for any hash function, so no collision assumption is needed for that equality.
No theorem says anything about which digests a plan can produce.

These theorems relate parts of the definition to each other. That the definition is Core's rests on a reading of D3 and D24 (A1) and on the known answers.
`lake test` runs all 500 records of Core's `sighash.json` (D26), which give digests only.
No record reaches the fixed digest. The generator in `sighash_tests.cpp` (D2, line 104) gives a SINGLE transaction as many outputs as inputs.

Hand-derived preimages cover the fixed digest, the other cases, and scripts that end in a short push, which the corpus does not contain.
Core itself does not run.

The definition makes three choices where Core's types decide the result.
`nIn`, the input count, the output count and `nIn + 1` are reduced modulo 2^32, as Core's `unsigned int` variables are.
That changes the result only for a transaction with 2^32 inputs or outputs, or for SINGLE with `nIn = 0xffffffff`.
The script-code count is computed in `Nat`. A `CScript` cannot hold 2^32 bytes, so that case has no Core counterpart.

Not specified: the `SIGVERSION_WITNESS_V0` branch.
The caller of `legacySignatureHash` prepares the script code. Core's interpreter passes the script after the last executed `OP_CODESEPARATOR`, with the signature removed by `FindAndDelete`.
A theorem about a supplied script code says nothing about that preparation (A5).
[Script signature-code preparation](#script-signature-code-preparation) specifies the preparation, and [the checker](#script-signature-opcodes-and-the-checker) specifies `TransactionSignatureChecker::CheckSig`, which takes the hash type from the last byte of a signature.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readPush_stop` | None |
| `readPush_op_append`, `readOp_op_append`, `readOp_stop_nil`, `lengthFieldWidth_of_gt`, `lengthFieldWidth_of_lt`, `pushSize_of_gt` | `propext` |
| `readPush_eq_op_iff`, `readPush_eq_stop_iff` | `propext`, `Quot.sound` |
| `readOp_cons_eq`, `readOp_eq_op_iff`, `readOp_eq_stop_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `readOp_rest_length`, `readOp_stop_prefix`, `scanOps_prefix`, `scanOps_eq_of_complete`, `legacySignatureHashPlan_eq_fixedDigest_iff`, `legacySignatureHashPlan_eq_hashBytes`, `legacyPreimage_eq`, `HashType.flags_eq_of_and`, `LegacyHashPlan.digest_fixedDigest`, `LegacyHashPlan.digest_hashBytes_val` | `propext`, `Quot.sound` |
| `scriptCodeBytes_eq_encode` | `propext`, `Classical.choice`, `Quot.sound` |

### Legacy signature hash: transformation reference

`DogeLib.Transaction.LegacySighashReference` defines the same commitment a second way.
`legacyReferencePlan` follows `SignatureHashOld` (SOURCES.md, D2), Core's copy of the old `SignatureHash`.
It copies the transaction and removes the separators from the script code with `findAndDelete` (D24).
Then it blanks scripts, sequences and outputs, and serializes the copy with the base codec.

The production plan constructs the whole preimage as a byte list, field by field, before hashing.
An incremental hash sink is later work.
The two definitions share `readOp`, `Script.empty`, `TxOut.null`, `legacyOne`, the hash-type flags and the field codecs.

`legacySignatureHashPlan_eq_reference` says that the two plans are equal, for every input index and every hash type, under three hypotheses:

- No instruction of the script code fails to parse: `(scanOps sc.bytes.val).2 = []`.
- The transaction has fewer than 2^32 inputs.
- The transaction has fewer than 2^32 outputs.

`legacySignatureHash_eq_reference` gives the equality of the digests.
The equality is between two Lean definitions. It says nothing about memory use or speed, and nothing about C++ object code.

`DogeLib.Transaction.Proofs.LegacySighashReader` connects successful Core-compatible reads to these equalities.
`Transaction.WithinMaxSize.inputs_lt` and `Transaction.WithinMaxSize.outputs_lt` turn the reader bound `0x02000000` into the required strict bound 2^32.
`Transaction.readBase_eq_ok_iff` supplies `WithinMaxSize` for a successful base read.
`Transaction.decodeBaseComplete_eq_ok_iff` supplies the base read with an empty remainder for a successful complete read.
`Transaction.readAllowWitness_withinMaxSize` supplies the same bounds on `w.tx` after a successful witness-allowed read.
Its private helper `readSections_withinMaxSize` covers the ordinary input list, the lists after nonzero flags, and the zero-flags branch with empty lists.

For each reader, `legacySignatureHashPlan_eq_reference_of_readBase`, `legacySignatureHashPlan_eq_reference_of_decodeBaseComplete` and `legacySignatureHashPlan_eq_reference_of_readAllowWitness` equate the plans.
The corresponding digest theorems are `legacySignatureHash_eq_reference_of_readBase`, `legacySignatureHash_eq_reference_of_decodeBaseComplete` and `legacySignatureHash_eq_reference_of_readAllowWitness`.
Each corollary holds for every input index and hash type, including fixed-digest cases.
The caller must still establish `hParse`: `(scanOps sc.bytes.val).2 = []`.
A successful transaction read does not establish this condition on the supplied script code.

The witness-reader corollaries apply `SIGVERSION_BASE` hashing to `w.tx`, the base fields only.
They establish nothing about segregated witness or consensus acceptance of witness data.

Each hypothesis is needed for a reason.
The production serializer reduces the counts modulo 2^32, and `SignatureHashOld` does not.

Take a script that ends in a short push.
The serializer writes its bytes up to the cursor of the failed `GetOp`, and omits the unread rest. `FindAndDelete` keeps the rest.
`legacyPlans_differ_shortPush` shows this on the script `4c 05 aa`.
So for such a script the two Core functions commit to different bytes, and only the production function is consensus code.

`lake test` runs Core's 500 corpus records and the hand-derived preimages through both plans.
Every corpus script parses fully, so the corpus does not test the difference.

Core's `FindAndDelete` counts the copies it removes in an `int`, and `findAndDelete` counts them in a `Nat`.
The Core compatibility of `findAndDelete` excludes a count that overflows an `int`.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `take_one_set_zero` | None |
| `CountedList.encodeElems_eq_flatten`, `CountedList.encode_eq_flatten`, `readOp_separator`, `readOp_cons_opcode` | `propext` |
| `dropMatches_length_le`, `findAndDeleteLoop_length_le`, `findAndDelete_length_le`, `referenceInputs_length_le`, `referenceOutputs_length_le`, `TxIn.encode_eq`, `Transaction.encode_eq`, `Script.encode_eq`, `scanOps_of_op`, `scanOps_of_stop`, `dropMatches_nil`, `dropMatches_separator_cons`, `dropMatches_separator_of_ne`, `findAndDeleteLoop_of_op`, `findAndDeleteLoop_of_stop`, `findAndDeleteLoop_separator_cons`, `legacyPlans_differ_shortPush` | `propext`, `Quot.sound` |
| `findAndDeleteLoop_separator`, `keptBytes_length_add`, `findAndDelete_separator`, `encode_referenceScriptCode`, `referenceSequencedInputs_map_encode`, `encode_referenceInputs`, `encode_referenceOutputs`, `legacySignatureHashPlan_eq_reference`, `legacySignatureHash_eq_reference` | `propext`, `Classical.choice`, `Quot.sound` |

The reader corollaries and their supporting bounds have these axiom dependencies, by `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `Transaction.WithinMaxSize.inputs_lt`, `Transaction.WithinMaxSize.outputs_lt` | `propext`, `Quot.sound` |
| `readSections_withinMaxSize` (private), `Transaction.readAllowWitness_withinMaxSize` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_readBase`, `legacySignatureHash_eq_reference_of_readBase` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_decodeBaseComplete`, `legacySignatureHash_eq_reference_of_decodeBaseComplete` | `propext`, `Classical.choice`, `Quot.sound` |
| `legacySignatureHashPlan_eq_reference_of_readAllowWitness`, `legacySignatureHash_eq_reference_of_readAllowWitness` | `propext`, `Classical.choice`, `Quot.sound` |

`DogeLib.Transaction.Proofs.ScanOps` proves that the hypothesis `hParse` survives the operations that build script code.
An instruction that `readOp` reads depends only on its own bytes (`readOp_append`, `readOp_bytes`).
So after a fully parsed head, a concatenation parses exactly as its tail does (`scanOps_append`, `scanOps_append_snd`).

`scanOps_drop`: in a fully parsed script, the suffix from a cursor at an instruction boundary parses completely.
The cursor is at a boundary when the bytes before it parse completely.
`findAndDelete_scanOps`: `FindAndDelete` keeps a fully parsed script fully parsed, when the pattern parses completely or is longer than the script.

The pattern hypothesis is needed.
The script `02 4c 01` parses as one push. The pattern `02` matches at its start, and the bytes that remain, `4c 01`, are a short `OP_PUSHDATA1`.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `scanOps_nil` | `propext`, `Quot.sound` |
| `readOp_append`, `readOp_bytes`, `scanOps_bytes`, `scanOps_opcode`, `scanOps_append`, `scanOps_append_snd`, `scanOps_drop`, `dropMatches_scanOps`, `findAndDeleteLoop_scanOps`, `findAndDelete_scanOps` | `propext`, `Classical.choice`, `Quot.sound` |

### Legacy signature hash: what ALL commits to

`DogeLib.Transaction.Proofs.LegacySighashCommitment` states what a legacy preimage commits to when the hash type is ALL without ANYONECANPAY.
Design record 0003, section 7, leaves that restriction to the hypotheses of a bridge property, and these theorems give it.

`HashType.IsAllOnly h` holds when the ANYONECANPAY bit `0x80` of `h` is clear and its low five bits are neither 2 (NONE) nor 3 (SINGLE).
That is the test of Core's serializer (D3), so the class includes the undefined low values, such as `0x00`, `0x04` and `0x21`.
Under `STRICTENC`, the encoding check rejects undefined hash types, and `0x01` is the only member that a signature can carry.
`legacyAllFields tx` is the version, the lock time, each input's outpoint and sequence in order, and the outputs.
It includes no scriptSig.

For the same script code `sc`, input index `n` and hash type `h` with `IsAllOnly h`:

- `legacyReferencePlan_allOnly_commits`: if `n` is an input index of `tx` and the transformation plans of `tx` and `tx'` are equal, then `legacyAllFields tx = legacyAllFields tx'`.
  There is no other hypothesis. The reference preimage is the base encoding of the copy, then the hash type, and `encode_injective` recovers the copy.
- `legacySignatureHashPlan_allOnly_commits`: the same for the production plans.
  It also needs the hypotheses of `legacySignatureHashPlan_eq_reference` for both transactions: a fully parsed script code, and fewer than 2^32 inputs and outputs in each.
- `legacySignatureHashPlan_eq_of_allFields` and `legacyReferencePlan_eq_of_allFields`: the converse, with no hypothesis beyond `IsAllOnly`.
  It also covers the fixed digest.
- `legacyReferencePlan_eq_iff_allFields` and `legacySignatureHashPlan_eq_iff_allFields` join the two directions.
- `legacyReferencePlan_allOnly_index_eq`: if the copy of the script code, `referenceScriptCode sc`, is not empty, equal transformation plans at indices `n` and `n'` give `n = n'`.

The index and count restrictions are needed. This proof additionally requires a fully parsed script code.
When `n` is an input index of neither transaction, both plans are the fixed digest `one`.

The production serializer writes the counts modulo 2^32, and only that many inputs or outputs.
So a transaction with 2^32 inputs or more commits to fewer inputs.
With an empty script code, every input of the copy has the empty script.
Then a transaction with two inputs has the same preimage at indices 0 and 1, as a known answer shows.

The production forward direction takes `hParse` from the transfer to the reference. A direct proof on the production body could drop it, and is not done.

`legacySignatureHash_eq_of_allFields` gives equal digests from equal committed fields.
No theorem goes from equal digests to equal fields: that needs collision resistance of double SHA-256, which DogeLib does not assume (A4).
The forward theorems are about the bytes that are hashed, so they need no assumption about the hash.

The weaker modes leave fields open. Each of these theorems gives equal production plans from agreement on fewer fields, with no other hypothesis:

- `legacySignatureHashPlan_eq_of_anyoneCanPay`, for ALL with ANYONECANPAY: the version, the lock time, the outputs, and the outpoint and sequence of input `n`. The other inputs and the input count are open.
- `legacySignatureHashPlan_eq_of_none`, for NONE without ANYONECANPAY: the version, the lock time, every outpoint and the sequence of input `n`. The outputs and the other sequences are open.
- `legacySignatureHashPlan_eq_of_single`, for SINGLE without ANYONECANPAY: the same inputs fields as NONE, and output `n`. The other outputs and the other sequences are open.

`legacySignatureHashPlan_anyoneCanPay_set_other`, `legacySignatureHashPlan_none_outputs` and `legacySignatureHashPlan_single_set_other_output` name one open field of each mode.
ANYONECANPAY combined with NONE or SINGLE has no theorem here.

`lake test` mutates the transactions of Core's 500 `sighash.json` records and recomputes the production digest.
For each mode it changes one committed and one open field, and expects a different or the same digest.
These checks test DogeLib against itself: the expected results come from these theorems, not from Core.
An expected difference assumes no collision on those inputs.

By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `legacyAllFields_eq_iff`, `legacyInputBytes_congr`, `legacyInputsBytes_anyoneCanPay_congr`, `legacyOutputsBytes_all_congr`, `referenceTransaction_inputs_allOnly`, `referenceTransaction_outputs_allOnly`, `legacyReferencePlan_eq_hashBytes_of_allOnly`, `lt_of_legacyReferencePlan_eq`, `referenceTransaction_eq_of_legacyReferencePlan_eq`, `HashType.isSingle_eq_false_of_isNone`, `HashType.isNone_eq_false_of_isSingle`, `legacySignatureHashPlan_eq_of_anyoneCanPay`, `legacySignatureHashPlan_anyoneCanPay_set_other` | `propext`, `Quot.sound` |
| `mapIdx_eq_of_getElem`, `legacyInputsBytes_congr`, `legacyOutputsBytes_single_congr`, `legacySignatureHashPlan_eq_of_allFields`, `referenceSequencedInputs_false_eq`, `referenceSequencedInputs_signedFields`, `referenceTransaction_eq_of_allFields`, `legacyReferencePlan_eq_of_allFields`, `legacyAllFields_eq_of_referenceTransaction_eq`, `legacyReferencePlan_allOnly_commits`, `legacySignatureHashPlan_allOnly_commits`, `legacyReferencePlan_eq_iff_allFields`, `legacySignatureHashPlan_eq_iff_allFields`, `legacySignatureHash_eq_of_allFields`, `legacyReferencePlan_allOnly_index_eq`, `legacySignatureHashPlan_eq_of_none`, `legacySignatureHashPlan_eq_of_single`, `legacySignatureHashPlan_none_outputs`, `legacySignatureHashPlan_single_set_other_output` | `propext`, `Classical.choice`, `Quot.sound` |

### Script instruction reader and execution state

`DogeLib.Script.Instruction` specifies one call of Core's `GetOp2` at a cursor (SOURCES.md, D24).
`readInstruction` is defined through `Transaction.readOp`, so the interpreter and the legacy signature serializer decode a script with the same definition.
`DogeLib.Script.State` specifies the state of one `EvalScript` call, its reset at the start of each call, and the main-stack hand-off of `VerifyScript` (D3).
The theorems are in `DogeLib.Script.Proofs.Instruction` and `DogeLib.Script.Proofs.State`.
For every script `s` and cursor `pc`:

- `readInstruction_eq_instruction_iff`: the reader reads instruction `i` exactly when the bytes from `pc` start with the bytes of `i`. Those bytes must be `opcode :: lengthField ++ pushed` under `InstructionEncoding`. That relation states the width of the length field and the data size without the reader. So the reader keeps the exact bytes of every push, including a nonminimal one.
- `readInstruction_eq_instruction_iff_readOp` and `readInstruction_eq_fail_iff_readOp`: the reader succeeds and fails where `readOp` does, with the same opcode and bytes.
- `readInstruction_consumes`: after an instruction, the next cursor is after `pc` and at most the length of `s`. The bytes from `pc` are the instruction bytes and then the bytes from the next cursor.
- `readInstruction_atEnd_iff` and `readInstruction_truncated_iff`: the reader reports the end exactly when `pc` is at or after the end. It reports a short push exactly when a push opcode is at `pc` and its length field or its data is short. The cursor is then after the opcode or after the length field, as `GetOp2` leaves it.
- `IsBoundary.not_inside`: no instruction boundary lies inside an instruction that starts at a boundary. So a loop of reads from cursor 0 never reads a byte of pushed data as an opcode.

For the state:

- `init_wellFormed`: the start of every call satisfies `ExecState.WellFormed`, for every script and caller stack.
- `handOff_eq_iff`: two states hand off the same start state exactly when their main stacks are equal.
- `WellFormed.advance` and `WellFormed.markSeparator`: a move of the cursor past an instruction that the reader reads, and the separator update `pbegincodehash = pc`, keep the invariants.

`truncated` reports the opcode byte and the short part, where Core returns `OP_INVALIDOPCODE` and an empty vector.
Both `atEnd` and `truncated` correspond to Core's `false`.

`evalInstruction_wellFormed` in [Script evaluation](#script-evaluation-one-evalscript-call) shows that each successful step of the evaluator keeps these invariants and the combined stack limit.
The hand-off theorems cover the two `EvalScript` calls of `VerifyScript`, not the P2SH copy and restore of the stack.

That the definitions are Core's rests on a reading of D24 and D3 (A1) and on the known answers.
`lake test` runs 50 single reads and 8 loops with hand-derived results, 15 of them from 14 records of Core's `script_tests.json`.
It also runs `init` and `handOff` on one state with nonempty locals and raw stack entries.
Core itself does not run.

The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `init_fExec`, `handOff_stack`, `handOff_altstack`, `handOff_pc`, `handOff_beginCodeHash`, `handOff_vfExec`, `handOff_opCount` | None |
| `readInstruction_atEnd_iff`, `readInstruction_instruction_unique`, `init_wellFormed`, `handOff_eq_iff`, `handOff_wellFormed`, `WellFormed.markSeparator` | `propext` |
| `readInstruction_eq_instruction_iff_readOp`, `readInstruction_eq_fail_iff_readOp`, `readInstruction_eq_truncated_iff_readOp`, `WithinStackLimit.handOff` | `propext`, `Quot.sound` |
| `readInstruction_eq_instruction_iff`, `readInstruction_consumes`, `readInstruction_nonpush`, `readInstruction_truncated_iff`, `IsBoundary.le_length`, `IsBoundary.eq_or_next_le`, `IsBoundary.not_inside`, `WellFormed.advance`, `WellFormed.pc_le_length`, `WellFormed.beginCodeHash_le_length` | `propext`, `Classical.choice`, `Quot.sound` |

### Script signature-code preparation

`Script.SignatureCode` specifies Core's vector push encoding and legacy script-code preparation (SOURCES.md, D24 and D3).
It reuses `Transaction.findAndDelete`, including its `Nat` count and the exclusion of Core counts above `INT_MAX`.
`readInstruction_pushEncoding` proves that every payload shorter than 2^32 bytes reads as one instruction with exactly that payload and any tail unread.
`pushHeader_encoding` gives the length-field width and exact payload size.
PUSHDATA4 lengths wrap modulo 2^32 outside that domain, as Core's `WriteLE32` does.
Script's 520-byte limit for pushed items lies within the round-trip domain.

`findAndDelete_traversal` proves that every input and pattern follow `DeletionTraversal`, with the exact output and count.
Each pass removes leading copies, retains one whole instruction without a search inside it, and continues at its end.
A failed read preserves every remaining byte after leading deletions, including bytes that the failed reader did not consume.
`dropMatches_decomposition` identifies the removed prefix, and `dropMatches_exhausted` excludes a match at the cursor after leading deletions for every nonempty pattern.
The cursors belong to the input after preceding deletions.
They need not be boundaries of the original script when an arbitrary pattern ends inside an instruction.

The result can contain a match that one pass creates across retained pieces.
For example, deleting `00 51` from `00 00 51 51` leaves `00 51`, as Core's test requires.
The traversal theorem does not assert that the final bytes contain no matches.

`effectiveScriptCode_nil`, `effectiveScriptCode_single` and `effectiveScriptCode_append` give suffix selection, single-signature deletion and ordered composition for every input.
The signature list follows `stacktop(-isig-k)` for increasing `k`, nearest the stack top first, and includes each signature's hash-type byte.
The caller establishes the separator cursor and supplies the signatures.
The existing signature serializer removes remaining separator instructions.

`checkSigStep` calls it with the one signature of `OP_CHECKSIG`, and `checkMultisigStep` with all signatures of `OP_CHECKMULTISIG`, from the separator cursor of the execution state.
[Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker) states their theorems.
No theorem establishes commutation of signature deletion passes.

`lake test` runs all sixteen cases of Core's `script_FindAndDelete` (D46), eight additional malformed suffix cases and eight push-size boundaries.
It also checks exact intermediate and final bytes for two signature deletions, including retained separator and payload bytes.
The expectations come from Core's assertions and a reading of D24 and D3.
Core itself does not run.
These finite tests do not prove equivalence to compiled Core.

The definitions add no axiom, cryptographic hypothesis or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `pushLengthBytes_length` | `propext` |
| `readInstruction_pushEncoding` | `propext`, `Classical.choice`, `Quot.sound` |
| `leValue_pushLengthBytes`, `pushHeader_encoding`, `findAndDelete_empty`, `dropMatches_decomposition`, `dropMatches_exhausted`, `findAndDeleteLoop_traversal`, `DeletionTraversal.zero`, `findAndDeleteLoop_empty`, `findAndDelete_eq_loop`, `findAndDelete_traversal`, `findAndDeleteLoop_malformed`, `effectiveScriptCode_nil`, `effectiveScriptCode_single`, `effectiveScriptCode_append` | `propext`, `Quot.sound` |

The effective script code keeps the parsed-script hypothesis of the transformation-reference theorem.
`readOp_pushEncoding`: `readOp` reads the push encoding of a payload shorter than 2^32 bytes as one instruction, and `scanOps_pushEncoding` follows.
`effectiveScriptCode_scanOps` takes a script of at most 2^32 bytes whose suffix from the cursor parses completely.
For every signature list, the effective script code then parses completely.

It needs no hypothesis on the signatures.
A push of a signature of 2^32 bytes or more is longer than the script code, so it never matches.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `length_lt_pushEncoding` | `propext`, `Quot.sound` |
| `readOp_pushEncoding`, `scanOps_pushEncoding`, `effectiveScriptCode_scanOps` | `propext`, `Classical.choice`, `Quot.sound` |

### Script numbers and truth values

`DogeLib.Script.Number` specifies Core's `CScriptNum` and `CastToBool` (SOURCES.md, D24 and D3).
The theorems are in `DogeLib.Script.Proofs.Number`.
For every integer `n`, byte string `b`, flag `req` and size `maxSize`:

- `value_encode`: `value (encode n) = n`.
- `isMinimal_encode` and `isMinimal_iff_encode_value`: `b` passes Core's minimality test exactly when `encode (value b) = b`. So the test accepts exactly one byte string for each integer, and rejects negative zero and every other string with a removable high byte.
- `encode_length_le_iff`: `encode n` has at most `k` bytes exactly when `2 |n| < 256 ^ k`. So every integer within ±(2^31 − 1) has at most four bytes (`encode_length_le_four`), and the sum or difference of two of them has at most five (`encode_add_length_le_five`, `encode_sub_length_le_five`).
- `decode_eq_ok_iff`, `decode_eq_overflow_iff` and `decode_eq_nonMinimal_iff` give every result of `decode`. Too many bytes give `overflow` whatever the flag. `nonMinimal` needs a length within the size, the flag and a failed test.
- `decode_encode`: if `2 |n| < 256 ^ maxSize`, then `decode (encode n) req maxSize = .ok n`. `decode_false`: without the flag, a string within the size gives its value, also when it is not minimal.
- `decode_natAbs_lt`: every decoded value satisfies `2 |n| < 256 ^ maxSize`. So a default-size decode lies within ±(2^31 − 1), a size-5 decode within ±(2^39 − 1), and a decode of up to 8 bytes within ±(2^63 − 1) (`decode_int64`).
- `getint_eq_max_min`: `getint n` is the clamp of `n` to `[-2^31, 2^31 - 1]`. `getint_decode_default`: it never changes a value that a default-size decode returns.
- `castToBool_eq_false_iff_value` and `castToBool_eq_false_iff`: `castToBool b` is false exactly when `value b = 0`, that is, when `b` is zero bytes, or zero bytes and then one `0x80`. This holds at every length. `castToBool_encode`: `castToBool (encode n)` is `n ≠ 0`.

The definitions use `Int`, and Core uses `int64_t` and `int`.
They agree only where Core's C++ is defined:

- `set_vch` shifts byte `i` left by `8*i` bits (D24, line 360). A string of more than eight bytes needs a shift of 64 bits or more, which is undefined. The constructor checks the size first (lines 220 to 237), so this shift is reachable only with a size argument above 8. `decode_int64` covers the defined sizes, and the interpreter decodes at most five bytes (D3, lines 377 and 408).
- `serialize` negates its argument (D24, line 326), which is undefined for `-2^63`. `encode` takes every integer.
- `getint` assumes a 32-bit `int`. Every supported Core target has one, but no theorem or check here establishes it. On another width Core's `getint` stays defined and clamps to that width's limits (D24, lines 307 to 310).
- `CastToBool` counts with an `unsigned int` (D3, line 40). For strings of at most `UINT_MAX` bytes it agrees with `castToBool`. On a longer string the counter wraps, and Core's loop can repeat without end, while `castToBool` returns a result. The theorems about `castToBool` hold at every length, but the Core correspondence covers only that domain.

That the definitions are Core's rests on a reading of D24 and D3 (A1) and on the known answers.
`lake test` runs 21 hand-derived encodings, 24 decodes, 9 `getint` cases and 13 `castToBool` cases.
It also runs the 247 integers of the `creation` test of `scriptnum_tests.cpp` (D44).
That test compares Core with its own 0.10.0 copy, so it gives the integers but no expected bytes.
Core itself does not run in these tests.

The Core comparison of `script.eval` and `script.verify_legacy` reaches these definitions only through the numeric opcodes and conditionals of the scripts that it sends ([docs/oracle.md](docs/oracle.md#the-comparison)).
No request compares them directly, and the comparison covers only the requests that it sends.

`OP_PICK`, `OP_ROLL` and the numeric opcodes in `Script.execOpcode` map a decode failure to `SCRIPT_ERR_UNKNOWN_ERROR`, as the `catch` of `EvalScript` does (D3, lines 1037 to 1040).
[Script evaluation](#script-evaluation-one-evalscript-call) states how the numeric opcodes stay within the defined domain of Core's `int64_t` operators.
The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `castToBool_concat` | `propext` |
| `isMinimal_encode`, `natAbs_value_lt`, `decode_eq_ok_iff`, `decode_eq_overflow_iff`, `decode_eq_nonMinimal_iff`, `decode_false`, `decode_natAbs_lt`, `decode_default_natAbs_le`, `decode_five_natAbs_le`, `getint_eq_max_min`, `getint_of_ge`, `getint_of_le`, `castToBool_eq_false_iff_value`, `castToBool_eq_false_iff` | `propext`, `Quot.sound` |
| `value_encode`, `isMinimal_iff_encode_value`, `encode_length_le_iff`, `encode_length_le_four`, `encode_add_length_le_five`, `encode_sub_length_le_five`, `decode_encode`, `decode_encode_default`, `decode_int64`, `getint_eq_self_iff`, `getint_mem`, `getint_decode_default`, `castToBool_encode` | `propext`, `Classical.choice`, `Quot.sound` |

The supporting byte and little-endian lemmas of the module use the same three axioms or fewer.

### Script evaluation, one `EvalScript` call

`DogeLib.Script.Eval` specifies one call of Core's `EvalScript` in `SIGVERSION_BASE` (SOURCES.md, D3).
It covers the opcodes of stages 2 and 3 of design record 0003: control flow, stack operations, numbers, hashes and signatures.
[Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker) states the claims about the signature opcodes.
`DogeLib.Script.Error` gives Core's `ScriptError_t` (D49), and `DogeLib.Script.Flags` gives the flag bits of D25.
The theorems are in `DogeLib.Script.Proofs.Eval`.

`evalScript checker flags script stack` returns one of three results.
`ok` is Core's `true` with `SCRIPT_ERR_OK`, and `rejected e` is Core's `false` with error `e`.
`unsupported r` means that this stage lacks a capability that the call needs, and says nothing about Core's verdict.
A flag outside the seven of design record 0003 is unsupported before any other check.
Without a checker, an executed signature opcode is unsupported, and so is `OP_CHECKLOCKTIMEVERIFY` or `OP_CHECKSEQUENCEVERIFY` with its flag set.
A check that the checker cannot decide is also unsupported.

For every flag set, script and caller stack:

- `evalScript_unsupportedFlags`: a flag bit outside `supportedFlags` gives `unsupported`, with exactly those bits.
- `evalScript_scriptSize`: with supported flags, a script of more than 10,000 bytes gives `SCRIPT_SIZE`.
- `evalScript_ok`: a successful call ends at the end of the script, with an empty `vfExec`, in a state that satisfies `ExecState.WellFormed`. If the script is not empty, the two stacks hold at most 1,000 items together.
- `evalScript_flags_congr`: two supported flag sets that agree on every supported flag except `P2SH` give the same result. So `P2SH` does not change one call.

For the loop and each instruction:

- `evalLoop_atEnd`: at the end of the script, the call succeeds exactly when `vfExec` is empty, and gives `UNBALANCED_CONDITIONAL` otherwise. `evalLoop_truncated`: a short push gives `BAD_OPCODE`.
- `evalInstruction_pushSize`, `evalInstruction_opCount` and `evalInstruction_disabled`: the push size, the opcode count and the disabled opcodes are checked in Core's order, whether or not the branch executes. `evalInstruction_verif`: `OP_VERIF` and `OP_VERNOTIF` give `BAD_OPCODE` in a skipped branch too.
- `evalInstruction_skipped`: in a skipped branch, an opcode outside `OP_IF` to `OP_ENDIF` that passes those checks only counts. The two stacks, `vfExec` and the separator cursor stay unchanged.
- `evalInstruction_wellFormed`: from a state that satisfies `ExecState.WellFormed`, a successful step and the cursor move give a state that satisfies it, within the combined stack limit. `OP_CHECKMULTISIG` raises the opcode count by its key count, and the invariant still bounds it by 201.
- `execOpcode_checker_congr`: every opcode outside `0xac` to `0xaf`, `0xb1` and `0xb2` gives the same result for any checker and any script. So those opcodes keep their stage-2 results. `OP_CHECKLOCKTIMEVERIFY` (`0xb1`) and `OP_CHECKSEQUENCEVERIFY` (`0xb2`) can depend on the checker, as [Script lock times and `VerifyScript`](#script-lock-times-and-verifyscript) states.
- The `execOpcode_*` theorems give the stack effect of each implemented opcode, its underflow error, and each unsupported case.

For the numeric and hash opcodes:

- One theorem per opcode, from `execOpcode_1add` to `execOpcode_within` and from `execOpcode_ripemd160` to `execOpcode_hash256`, gives its stack effect. The numeric effect theorems assume successful four-byte decodes without the minimal requirement. The hash effect theorems require only the stated stack shape.
- `execOpcode_numeric_underflow` and `execOpcode_hash_underflow`: too few items give `INVALID_STACK_OPERATION`. `execOpcode_numeric_decode`: an operand that fails to decode gives `UNKNOWN_ERROR`.
- `execOpcode_addSub_length`: `OP_1ADD`, `OP_1SUB`, `OP_ADD` and `OP_SUB` push at most five bytes. `execOpcode_numeric_length_le_four`: every other numeric opcode that pushes a result pushes at most four bytes.

Core computes these opcodes in `int64_t` with the operators of `CScriptNum` (D24, lines 244 to 297), and the definitions compute in `Int`.
They agree where no operator overflows and no assert fires.
Each operand is a four-byte decode and lies within ±(2^31 − 1) (`decode_default_natAbs_le`), so this holds for every operand:

- `numericOperand_ne_int64Min`: the operand of `OP_NEGATE` and `OP_ABS` is not `INT64_MIN`, which `operator-()` asserts (line 273).
- `numericOperand_add_one_le` and `numericOperand_sub_one_ge`: the asserts of `operator+=` and `operator-=` with 1 hold for `OP_1ADD` and `OP_1SUB` (lines 285 and 293).
- `numericOperand_addSub_mem`: the sum and the difference of `OP_ADD` and `OP_SUB` lie within `int64_t`. `operator+` and `operator-` (lines 258 and 259) have no assert.

The comparisons, `OP_MIN`, `OP_MAX` and `OP_WITHIN` only compare values.
The hash opcodes use the hash definitions of the `Cryptography` layer, and inherit the boundaries that their sections state.
`OP_NUMEQUALVERIFY` pushes its comparison and pops it again in Core (D3, lines 817 to 823).
The definition pops both operands directly, which differs only in an intermediate state that no check reads.

The evaluator takes no fuel.
`evalLoop` recurses on the distance from the cursor to the end of the script.
`readInstruction_progress`, in the specification, shows that each instruction moves the cursor forward.
So every call returns a result that depends only on the flags, the script and the caller's stack.

Three boundaries limit the claim:

- Core compares the operand of `OP_PICK` and `OP_ROLL` with `(int)stack.size()` (D3, line 657). Here sizes are `Nat` values. The two agree when the main stack has fewer than 2^31 items. After the first instruction the two stacks hold at most 1,000 items. So only a caller's stack of 2^31 items or more lies outside the correspondence.
- `OP_IF`, `OP_NOTIF`, `OP_VERIFY` and `OP_IFDUP` use `castToBool`, which inherits the boundary of [Script numbers and truth values](#script-numbers-and-truth-values). Core's `CastToBool` counts with an `unsigned int` (D3, line 40), so on an item of more than `UINT_MAX` bytes its loop can repeat without end. `castToBool` returns a result. A push holds at most 520 bytes, so such an item can come only from the caller's stack. Neither Core nor `evalScript` checks the size of a caller's item. For example, `OP_VERIFY` on one caller's item of 2^32 zero bytes gives `VERIFY` here, and Core's loop does not end.
- `MINIMALDATA`, `DISCOURAGE_UPGRADABLE_NOPS` and `MINIMALIF` are unsupported flags, so the evaluator has no `CheckMinimalPush`, no NOP discouragement and no minimal `OP_IF` check. `MINIMALIF` applies only to `SIGVERSION_WITNESS_V0` at the pin.
- An unsupported result can hide a Core rejection. For example, without a checker, `OP_CHECKSIG` on an empty stack is unsupported here, and Core gives `INVALID_STACK_OPERATION`.

That the definitions are Core's rests on a reading of D3 and D24 (A1) and on the known answers.
`lake test` runs 140 hand cases and 46 underflow cases, with results written by hand from D3 and D24.
The expected digests of the hash cases come from Core's `script_tests.json` (D45).
It also runs all 1,193 records of Core's `script_tests.json` (D45) through `verifyScript`.
The checker is `transactionChecker` over the record's spending transaction, with `coreVerifier`.
925 records agree with Core's expected result, 563 acceptances and 362 rejections, and none disagrees.

268 records are unsupported.
Of those, 165 have an unsupported flag and 103 have a witness.
Core itself does not run.

The definitions add no hypothesis or axiom.
The correspondence with Core covers a caller's stack of fewer than 2^31 items, each of at most `UINT_MAX` bytes.
The two boundaries above are its only execution boundaries.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `readInstruction_progress`, `evalScript_unsupportedFlags`, `evalScript_scriptSize`, `evalScript_flags_congr`, `evalLoop_atEnd`, `evalLoop_truncated`, `evalLoop_instruction`, the `evalInstruction_*` theorems except `evalInstruction_wellFormed`, `execOpcode_frame`, `execOpcode_flags_congr`, `execOpcode_checker_congr`, `checkSignatureEncoding_flags_congr`, `checkPubKeyEncoding_flags_congr`, `encode_ofBool`, the `execOpcode_*` effect, underflow and decode theorems, `numericOperand_ne_int64Min`, `numericOperand_add_one_le`, `numericOperand_sub_one_ge` | `propext`, `Quot.sound` |
| `evalInstruction_wellFormed`, `evalLoop_ok`, `evalScript_ok`, `execOpcode_addSub_length`, `execOpcode_numeric_length_le_four`, `numericOperand_addSub_mem` | `propext`, `Classical.choice`, `Quot.sound` |

### Script signature and public-key encoding

`DogeLib.Script.SignatureEncoding` specifies the encoding checks that Core's signature opcodes run before they verify a signature (SOURCES.md, D3, D50 to D53).
The theorems are in `DogeLib.Script.Proofs.SignatureEncoding`.
For every byte string and every flag set:

- `isValidSignatureEncoding_iff`: a signature passes `IsValidSignatureEncoding` exactly when it is `derBody r s` and one hash-type byte.
  Here `r` and `s` are DER integers: not empty, first byte below `0x80`, and a leading zero only before a byte of at least `0x80`.
  Together they have at most 66 bytes.
- `laxStore_eq`: the lax parser stores `laxScalars` of the values of R and S.
  That is both values when both are below the order `n`, and zero and zero otherwise.
  Core's test that a value has more than 32 bytes never changes this result.
- `parseDerLax_derBody` and `parseDerLax_dropLast_of_isValidSignatureEncoding`: the lax parser accepts every strict-DER signature without its hash type, and stores those scalars.
- `checkLowS_iff`: `checkLowS` holds exactly when the parser succeeds and stores an S of at most `⌊n/2⌋`.
  `checkLowS_derBody_iff`: on strict DER with R and S below `n`, that is the bound on S itself.
- `checkLowS_derBody_of_overflow`: on strict DER with R or S at least `n`, `checkLowS` holds whatever S is.
  `checkSignatureEncoding_overflowExample` gives one such signature with a high S, which passes `checkSignatureEncoding` with `DERSIG`, `STRICTENC` and `LOW_S`.
- `checkSignatureEncoding_eq_sigDer_iff`, `checkSignatureEncoding_eq_sigHighS_iff` and `checkSignatureEncoding_eq_sigHashtype_iff` state when each error occurs.
  `checkSignatureEncoding_error` shows that no other error occurs, and `checkSignatureEncoding_nil` that the empty signature always passes.
  `isLowDerSignature_ne_sigDer` shows that the `SIG_DER` result of `IsLowDERSignature` is unreachable from `CheckSignatureEncoding`.
- `checkPubKeyEncoding_eq_error_iff`: the only key error is `PUBKEYTYPE`, with `STRICTENC`.
  `isCompressedOrUncompressedPubKey_iff` gives the accepted shapes, and `isValidPubKey_of_isCompressedOrUncompressedPubKey` shows that each gives a valid `CPubKey`.

The LOW_S check follows `CheckLowS` and its parser, not a bound on the S bytes of the signature.
Design record 0003, section 5, requires this case.
A verifier that normalizes S loses the original value, so the definitions do not use one.
The theorems are statements about bytes.
They say nothing about elliptic-curve points, about which signatures verify, or about libsecp256k1's compiled code.

The order `n` and the half order are copied from D53 and checked against SEC 2 (S2) by reading.
`secp256k1HalfOrder_eq` proves that the half order is `n / 2`.
No theorem derives `n` from the curve.

Core's parser compares a long-form length with `sizeof(size_t)` (D50, lines 76 and 114).
`parseDerLaxWith` takes that size as a parameter, and `parseDerLax` uses 8.
`parseDerLaxWith_eq` proves the same result for every size of at least 4 on inputs of fewer than 2^24 bytes.
So 32-bit and 64-bit builds agree on every Script stack item, which has at most 520 bytes.

`checkPubKeyEncoding` omits Core's second test, which needs `SIGVERSION_WITNESS_V0` and `WITNESS_PUBKEYTYPE` (D3, lines 219 to 221).
Design record 0003 runs only `SIGVERSION_BASE`, and that flag is unsupported.

That the definitions are Core's rests on a reading of D3, D50 to D53 (A1), and on the known answers.
`lake test` checks the 60 P2PK and P2PK NOT records of `script_tests.json` (D45) inside the milestone, and 86 hand-derived cases.
The test takes each record's signature from the top of the stack after the specified `evalScript` runs `scriptSig`.
Core itself does not run in these tests.

The Core comparison of `script.eval` and `script.verify_legacy` reaches these checks only through the signature opcodes of the scripts that it sends ([docs/oracle.md](docs/oracle.md#the-comparison)).
No request compares an encoding check directly, and the comparison covers only the requests that it sends.
The definitions add no hypothesis, axiom or execution boundary.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `secp256k1HalfOrder_eq`, `secp256k1Order_lt`, `overflowExample_order_le`, `overflowExample_highS` | None |
| `laxScalars_of_lt` | `propext` |
| `checkLowS_iff`, `checkSignatureEncoding_eq`, `checkSignatureEncoding_nil`, `checkSignatureEncoding_of_flags`, `checkSignatureEncoding_eq_sigDer_iff`, `checkSignatureEncoding_eq_sigHighS_iff`, `checkSignatureEncoding_eq_sigHashtype_iff`, `checkSignatureEncoding_error`, `isLowDerSignature_ne_sigDer`, `isDefinedHashtypeSignature_iff`, `checkPubKeyEncoding_eq_error_iff`, `laxScalars_of_le`, `overflowExample_isValidSignatureEncoding` | `propext`, `Quot.sound` |
| `isValidSignatureEncoding_iff`, `laxStore_eq`, `parseDerLax_derBody`, `parseDerLax_dropLast_of_isValidSignatureEncoding`, `parseDerLaxWith_eq`, `checkLowS_derBody_iff`, `checkLowS_derBody_of_overflow`, `checkSignatureEncoding_overflowExample`, `isCompressedOrUncompressedPubKey_iff`, `isValidPubKey_of_isCompressedOrUncompressedPubKey` | `propext`, `Classical.choice`, `Quot.sound` |

The supporting byte and big-endian lemmas of the module use the same three axioms or fewer.

### Script signature opcodes and the checker

`DogeLib.Script.Signature` specifies the signature checker that `evalScript` takes as a parameter (SOURCES.md, D3 and D25).
`DogeLib.Script.Eval` specifies `OP_CHECKSIG`, `OP_CHECKSIGVERIFY`, `OP_CHECKMULTISIG` and `OP_CHECKMULTISIGVERIFY` with that checker (D3, lines 880 to 1026).
The theorems are in `DogeLib.Script.Proofs.Signature` and `DogeLib.Script.Proofs.Eval`.

The checker is a structure with three functions: `checkSig sig key scriptCode`, `checkLockTime n` and `checkSequence n`, each returning `Option Bool`.
[Script lock times and `VerifyScript`](#script-lock-times-and-verifyscript) covers the two lock-time functions.
`none` means that the check is unavailable, and the evaluator then reports `unsupported`, never a rejection.
`baseChecker` is Core's `BaseSignatureChecker`, which fails every check.
`transactionChecker tx nIn verify` is Core's `TransactionSignatureChecker::CheckSig` with `SIGVERSION_BASE`.
For every transaction, input index and verifier:

- `transactionChecker_invalidKey` and `transactionChecker_emptySig`: a key that fails `isValidPubKey` gives `some false`, and with a valid key so does an empty signature. Neither case depends on `verify`.
- `transactionChecker_verify`: for a valid key, a signature `sig ++ [h]` and a script code shorter than 2^64 bytes, the result is `verify sig key d`. Here `d` is `legacySignatureHash` of the script code with the hash type `h` zero-extended to 32 bits.
- `transactionChecker_verify_congr`: two verifiers that agree on that one request give the same result.

For the opcodes, with any checker `c`:

- `checkSigStep_underflow`, `checkSigStep_sigEncoding` and `checkSigStep_keyEncoding`: fewer than two items, then the signature encoding, then the key encoding, each before any checker request.
- `checkSigStep_checked`: after both checks, the step asks `c` once, with the signature, the key and `effectiveScriptCode script s.beginCodeHash [sig]`. It pops both items and pushes the answer, or for `OP_CHECKSIGVERIFY` pops on `true` and gives `CHECKSIGVERIFY` on `false`. `checkSigStep_checker_congr`: no other request.
- `checkMultisigStep_empty`, `checkMultisigStep_keyCountDecode`, `checkMultisigStep_pubkeyCount`, `checkMultisigStep_opCount`, `checkMultisigStep_keyDepth` and `checkMultisigStep_sigCount`: the checks before the loop, in Core's order. The last depth check already requires the dummy, so Core's later `stack.size() < 1` (line 1010) is unreachable.
- `checkMultisigStep_counted`: after those checks, the step runs `multisigLoop` on the script code with every signature push removed. It then checks the dummy and pushes the result, with the opcode count raised by the key count.
- `checkMultisigStep_loopError`, `checkMultisigStep_dummy` and `checkMultisigStep_nullDummy`: an error in the loop comes first. Without `NULLDUMMY` any dummy is consumed. With it, a nonempty dummy gives `SIG_NULLDUMMY`.
- `evalInstruction_signature_skipped`: in a skipped branch, a signature opcode only counts as one opcode. The checker is not asked, and `OP_CHECKMULTISIG` adds no key count.

The ordered-matching property is stated over a relation `R` first.
`OrderedMatch R sigs keys` says that the signatures pair in order with a subsequence of the keys.
For every relation and all lists:

- `greedyMatch_iff`: Core's greedy loop succeeds exactly when `OrderedMatch R sigs keys` holds.
- `greedyMatch_eq_noExit`: the early exit of lines 987 to 991 does not change the result.
- `multisigLoop_ok`: when the check returns `R` on every pair of the two lists, `multisigLoop` returns the greedy result. The hypothesis covers every pair, which is stronger than the pairs that Core visits.

`checkMultisigStep_matching` instantiates this for `OP_CHECKMULTISIG`.
It assumes that the counts decode to the lengths of the lists and pass Core's checks.
It assumes that every signature and key passes its encoding check, and that `c` answers `some (R sig key)` on every pair.
It also assumes that `NULLDUMMY` is clear or the dummy is empty.
Then the step pushes `[1]` exactly when `OrderedMatch R sigs keys` holds, and `[]` otherwise.
`checkMultisigStep_matching_verify` gives the same for `OP_CHECKMULTISIGVERIFY`.
`checkMultisigStep_matching_pushOrder` states the property for the lists in script push order.

The checker is the boundary of these claims.
A result of `evalScript` with `transactionChecker` holds for Core only under the verifier-agreement hypothesis.
That hypothesis says that `verify sig key d` returns `some b` only when Core's `CPubKey::Verify` returns `b` on the same signature, key and digest.
`Script.coreVerifier` is DogeLib's instance of the parameter, and for it the hypothesis becomes an A1 claim about a definition.
[Secp256k1 public-key parser and Core's verifier](#secp256k1-public-key-parser-and-cores-verifier) states what is proved about it and the finite evidence from the Core comparison.
For any other verifier, no theorem establishes the hypothesis.

The two `lake test` corpus runners use `coreVerifier`.
All 925 inside-milestone records of `script_tests.json` agree with Core's expected result, including the 44 that need a verification.
All 91 required acceptances among the 159 eligible transaction inputs accept, and no input is unsupported.
A repeated key in a multisig script does not show that different people signed.

`NULLFAIL` is unsupported, so `evalScript` reports any flag set with it before it runs.
Its branches at lines 904, 905 and 996 to 998 are absent from the definitions.
`transactionChecker` gives `none` for a script code of 2^64 bytes or more, which lies outside `Transaction.Script`.
The evaluator never passes such a script code, because its script has at most 10,000 bytes.

That the definitions are Core's rests on a reading of D3 and D25 (A1) and on the known answers.
`lake test` runs 48 signature-opcode cases with a lookup-table test checker, 5 `transactionChecker` cases and one `baseChecker` case, with results written by hand from D3.
The lookup table is a test backend and says nothing about which signatures are valid.
The corpus runners above add the 925 inside-milestone records of `script_tests.json`.
[Script evaluation](#script-evaluation-one-evalscript-call) gives the 268 unsupported records and their reasons.

The oracle's `script.eval` can select `baseChecker`, and its legacy operation can select a transaction checker.
The transaction checker uses `coreVerifier`, so finite Core comparisons also cover signature-opcode results that verify a signature.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `baseChecker_checkSig`, `tail_sublist_of_cons` | None |
| `PairsMatch.length_eq`, `orderedMatch_length`, `multisigLoop_ok`, `multisigLoop_error` | `propext` |
| `transactionChecker_invalidKey`, `transactionChecker_emptySig`, `transactionChecker_verify`, `transactionChecker_verify_congr`, `greedyMatchNoExit_iff`, `greedyMatchNoExit_short`, `greedyMatch_eq_noExit`, `greedyMatch_iff`, `execOpcode_signature_none`, `execOpcode_checkSig`, `execOpcode_checkMultisig`, the `checkSigStep_*` and `checkMultisigStep_*` theorems except `checkMultisigStep_matching_pushOrder`, `multisigCheck_ok`, `multisigLoop_multisigCheck_error`, `evalInstruction_signature_skipped` | `propext`, `Quot.sound` |
| `pairsMatch_append`, `pairsMatch_reverse`, `orderedMatch_reverse`, `checkMultisigStep_matching_pushOrder` | `propext`, `Classical.choice`, `Quot.sound` |

### Script lock times and `VerifyScript`

`DogeLib.Script.Eval` specifies `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY` with their flags (D3, lines 350 to 427).
`DogeLib.Script.Signature` gives Core's `CheckLockTime` and `CheckSequence` (D3, lines 1274 to 1353) as `lockTimeSatisfied` and `sequenceSatisfied`, the two new fields of `transactionChecker`.
`DogeLib.Script.Verify` specifies `VerifyScript` with an empty witness (D3, lines 1409 to 1526), `IsPushOnly` and `IsPayToScriptHash` (D48), and the spend predicate `verifyLegacySpend`.
The theorems are in `DogeLib.Script.Proofs.Eval`, `DogeLib.Script.Proofs.Signature` and `DogeLib.Script.Proofs.Verify`.

For the lock-time opcodes, with any checker `c` and the opcode's flag set:

- `execOpcode_cltv_underflow`, `execOpcode_cltv_decode` and `execOpcode_cltv_negative`: an empty stack, then a top item that fails the five-byte decode, then a negative operand, each before any checker request. The `csv` theorems give the same.
- `execOpcode_cltv_checked`: a nonnegative operand goes to `c.checkLockTime`, and `true` leaves the state unchanged. `execOpcode_csv_checked` gives the same for an operand with bit 31 clear.
- `execOpcode_csv_disabled`: an operand with bit 31 set leaves the state unchanged, for every checker.
- `execOpcode_cltv_transaction`: with `transactionChecker` for an `InputContext`, a nonnegative operand passes exactly when it lies on the lock time's side of 500,000,000, does not exceed the lock time, and the input's sequence is not `0xffffffff`.
- `execOpcode_csv_transaction`: with `transactionChecker`, an operand with bit 31 clear passes exactly when the version read as `uint32_t` is at least 2, bit 31 of the sequence is clear, the masked values have the same type bit, and the masked operand does not exceed the masked sequence.

Without a checker, both opcodes with their flags are unsupported (`execOpcode_cltv`, `execOpcode_csv`), as before.
With their flags clear, they are NOPs for every checker.

These checks compare the operand with fields of the spending transaction.
They do not compare the lock time with a block height or time, and they do not establish an input's age.
Design record 0003, section 3, records that the mainnet activation of CSV at the pin is unverified.
So a CSV result may hold only for relay policy (A5).

`CheckSequence` masks the operand as an `int64_t`, and `sequenceSatisfied` masks `n.toNat`.
The two agree for `n ≥ 0`, the only operands that the opcode passes.
`transactionChecker` answers `none` for an input index outside the inputs, where Core's `vin[nIn]` is undefined behavior, so the result makes no claim.
`InputContext` requires an index below the number of inputs, so `verifyLegacySpend` never reaches that case.

For `verifyScript` with any checker `c`:

- `verifyScript_unsupportedFlags`: a flag outside the seven gives `unsupported` before any evaluation. `hasFlag_sigPushOnly_eq_false`, `hasFlag_cleanStack_eq_false` and `hasFlag_witness_eq_false` show that the branches of those flags are unreachable.
- `verifyScript_noP2sh`: without `P2SH` or without the template, the result is the two evaluations with the true-top check.
- `verifyScript_p2sh`: with `P2SH`, the template, a push-only `scriptSig` whose final stack is `S ++ [redeem]`, and a `scriptPubKey` that accepts, the result is `redeem` on `S` with the true-top check.
- `verifyScript_p2sh_notPushOnly`: the same request with a `scriptSig` that is not push-only gives `SIG_PUSHONLY`.
- `verifyScript_p2sh_saved_ne_nil`: Core's assert at line 1469 holds, so the branch of `verifyScript` for an empty saved stack is unreachable. Its value is arbitrary and is not Core's behavior.
- `evalScript_p2shTemplate`: the template on `S ++ [x]` pushes `[1]` when the HASH160 digest of `x` equals its 20 bytes, and `[]` otherwise, given room for two items.
- `verifyScript_p2sh_hash` and `verifyScript_p2sh_hash_ne`: the composition from the digest of the supplied `redeem`.
- `isPushOnly_iff`: `isPushOnly` is Core's loop over the instruction boundaries of `readInstruction`. Like Core, it treats `OP_RESERVED` as push-only.

The P2SH theorems hold for the exact supplied redeem script.
They do not say that no other redeem script has the same digest. That needs a collision hypothesis (A4).
`verifyLegacySpend` takes the previous output's script from the caller, who establishes that it belongs to the referenced outpoint.
A result of `verifyLegacySpend` holds for Core only under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).

That the definitions are Core's rests on a reading of D3, D4, D24 and D48 (A1), and on the known answers.
`lake test` runs 38 lock-time cases, 20 `verifyScript` cases, 11 `isPushOnly` cases and 3 `verifyLegacySpend` cases, with results written by hand from those sources.
On `script_tests.json`, `verifyScript` with `transactionChecker` and `coreVerifier` agrees with Core's expected result on 925 records and disagrees on none.
The oracle exposes `verifyScript` through `script.verify_legacy`, with base and transaction checker selections.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `baseChecker_checkLockTime`, `baseChecker_checkSequence` | None |
| `lockTimeSatisfied_iff`, `InputContext.getElem?_index` | `propext` |
| `transactionChecker_checkLockTime`, `transactionChecker_checkSequence`, `transactionChecker_checkLockTime_none`, `transactionChecker_checkSequence_none`, `sequenceSatisfied_iff`, `checkLockTimeStep_next`, `checkSequenceStep_next`, the `execOpcode_cltv*` and `execOpcode_csv*` theorems, `execOpcode_checker_congr`, `execOpcode_script_congr`, `isPushOnlyFrom_atEnd`, `isPushOnlyFrom_truncated`, `isPushOnlyFrom_instruction`, `verifyScript_unsupportedFlags`, `hasFlag_sigPushOnly_eq_false`, `hasFlag_cleanStack_eq_false`, `hasFlag_witness_eq_false`, `verifyScript_noP2sh`, `verifyScript_p2sh`, `verifyScript_p2sh_notPushOnly`, `verifyLegacySpend_eq` | `propext`, `Quot.sound` |
| `isPushOnlyFrom_iff`, `isPushOnly_iff`, `isPayToScriptHash_iff`, `evalScript_p2shTemplate`, `evalScript_p2shTemplate_nil`, `verifyScript_p2sh_saved_ne_nil`, `verifyScript_p2sh_hash`, `verifyScript_p2sh_hash_ne` | `propext`, `Classical.choice`, `Quot.sound` |

`InputContext.ofDecoded`, in `DogeLib.Script.Proofs.Verify`, builds the input context of an input of a transaction that `decodeBaseComplete` read.
The caller supplies an index below the number of inputs.
`Transaction.decodeBaseComplete_eq_ok_iff` and `Transaction.readBase_eq_ok_iff` give `WithinMaxSize`, and so the two count bounds.
`verifyLegacySpend_ofDecoded` unfolds the spend predicate on it to `verifyScript` with `transactionChecker` for the index.
The definition lives in the proof library, because `WithinMaxSize` does.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `InputContext.ofDecoded_tx`, `InputContext.ofDecoded_index`, `verifyLegacySpend_ofDecoded` | `propext`, `Classical.choice`, `Quot.sound` |

### Script worked property: multisig with recovery

`DogeLib.Script.MultisigRecovery` builds the redeem script of design record 0003, section 7, for `k` of `n` keys with `1 ≤ k ≤ n ≤ 16`:
`OP_IF OP_k <keys> OP_n OP_CHECKMULTISIG OP_ELSE <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <R> OP_CHECKSIG OP_ENDIF`.
`DogeLib.Script.Proofs.MultisigRecovery` proves the equivalence of section 7 for this template and its 2-of-3 instance.

`MultisigRecoverySpend` collects the hypotheses, one field each:

- supported flags, with `P2SH` and `CHECKLOCKTIMEVERIFY` set
- `1 ≤ k ≤ n ≤ 16`, 33-byte keys and a 33-byte recovery key `R`
- a previous output that is the P2SH commitment to the exact redeem bytes
- a push-only `scriptSig` whose evaluation succeeds with the final stack `S ++ [redeem]`

The `InputContext` of `verifyLegacySpend` gives an input index that selects an input and fewer than 2^32 inputs and outputs.
The template discharges the other resource bounds of section 7.
The redeem script has `34 n + 47` bytes, 149 for 2-of-3 (`multisigRecoveryScript_length`).
Each of its pushes has at most 33 payload bytes.
A run counts at most `n + 7` operations, including skipped opcodes above `OP_16` and the key count.
The `scriptSig` evaluation checks the 520-byte limit on the push of the redeem script, so `n` is at most 13.

`OrdinaryBranch` and `RecoveryBranch` state the two cases without a hypothesis that execution succeeds:

- Ordinary: `S` is `below ++ dummy :: sigs ++ [sel]` with `k` signatures and `castToBool sel`.
  Every pair that Core's matching loop visits, top first (`multisigVisits`), passes `SigEncodingOk` and `KeyEncodingOk`.
  With `NULLDUMMY` the dummy is empty.
  The signatures pair in order with a subsequence of the keys under `sigAccepted` (`OrderedMatch`).
- Recovery: `S` is `below ++ [sigR, sel]` with `castToBool sel = false`.
  The lock time is at least 1,000,000 and below 500,000,000, and the input's sequence is not `0xffffffff`.
  `sigR` and `R` pass the encoding predicates, and `sigAccepted` holds for `sigR` against `R`.

`checkSignatureEncoding_ok_iff` and `checkPubKeyEncoding_ok_iff` prove that the predicates are exactly the checks of `Script.SignatureEncoding`, including the LOW_S overflow case.
By `sigAccepted_iff`, `sigAccepted` means that the key passes `isValidPubKey`.
It also means that `verify` answers `some true` on the signature without its hash-type byte and the legacy digest.
Both cases allow any stack below, nonminimal pushes and any selector bytes, with negative zero as false.

The theorems:

- `multisigRecovery_sound`: acceptance implies one of the two branches. It assumes no stack bound on `S` and no totality of `verify`.
- `multisigRecovery_ordinary_complete`: the ordinary branch implies acceptance when `S.length + n + 1 ≤ 1000` and the checker decides every visited pair.
- `multisigRecovery_recovery_complete`: the recovery branch implies acceptance when `S.length + 2 ≤ 1000`. `sigAccepted` is already a decided answer.
- `multisigRecovery_accepted_iff` and `multisigRecovery_twoOfThree_accepted_iff`: the equivalence, for a verifier that decides every request and the ordinary stack bound.
- `multisigRecovery_ordinary_unsupported` and `multisigRecovery_recovery_unsupported`: an answer `none` on a reached call gives `unsupported`, never a rejection.
- `multisigRecovery_lockTime_lt`: with `CHECKLOCKTIMEVERIFY`, a false selector and a lock time below 1,000,000 give `UNSATISFIED_LOCKTIME` before any signature check.
  `multisigRecovery_accepted_lockTime_lt`: such a spend is accepted only through the ordinary branch.
  Without the flag, `OP_CHECKLOCKTIMEVERIFY` is `OP_NOP2`, and a known answer accepts the recovery branch with lock time 0.
- `verifyLegacySpend_scriptSig_rejected` and `verifyLegacySpend_scriptSig_unsupported`: a failed `scriptSig` evaluation passes through.

Every checker call of both branches hashes the transformation-reference digest, Core's `SignatureHashOld`.
`multisigRecoveryScript_scanOps`: for `1 ≤ k ≤ n ≤ 16`, 33-byte keys and a 33-byte recovery key, every instruction of the template parses.
`ordinaryCode_scanOps` and `recoveryCode_scanOps`: so does the script code of each branch, for every signature list, by `effectiveScriptCode_scanOps`.
These discharge the parsed-script hypothesis of design record 0003, stage 3, for the template.

`transactionChecker_verify_reference` and `sigAccepted_iff_reference` compose a fully parsed script code with `legacySignatureHash_eq_reference` and the count bounds of the `InputContext`.
`MultisigRecoverySpend.sigAccepted_ordinary_iff_reference` and `MultisigRecoverySpend.sigAccepted_recovery_iff_reference` restate `sigAccepted` on each branch's script code.
It holds exactly when the key passes `isValidPubKey` and `verify` answers `some true` on the stripped signature, the key and the digest of `legacyReferencePlan`.
`MultisigRecoverySpend.checkSig_ordinary_reference` and `MultisigRecoverySpend.checkSig_recovery_reference` give the checker's answer as that `verify` call.
These results concern the digest that the checker passes to `verify`. They add nothing about `verify` itself.

The theorems hold relative to the verifier parameter, under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).
They do not establish unforgeability, private-key ownership, distinct signers or bridge custody.

Duplicate keys are allowed, and a match against duplicate keys is not distinct authorization.
The P2SH composition uses the exact supplied redeem script. A different redeem script with the same digest needs a separate hash-commitment argument (A4).
Every hash type that the flags admit is allowed, including NONE, SINGLE and ANYONECANPAY, so a signature need not commit to the whole transaction.

`MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits` and `MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits` restrict to an `IsAllOnly` hash type.
Then an accepted signature also verifies against the reference digest of every transaction `tx'` with the same `legacyAllFields` as `ctx.tx`, at the same input index.
They do not say that `tx'` passes the template: a different scriptSig of the input changes the execution.

They state invariance of an accepted verifier result under equal fields, not that changing a field invalidates the signature.
A verifier that accepts every digest satisfies them.
The commitment of the preimage to the fields is `legacyReferencePlan_allOnly_commits`. A signature-binding claim also needs cryptographic and verifier assumptions.

The lock-time conditions compare the operand with fields of the spending transaction.
A claim that recovery cannot enter a chain before a height or time needs transaction-finality and chain-context results that DogeLib does not have.
The template is a property target. A production bridge instance needs its own fixtures and custody review.

`lake test` runs 25 hand cases through `verifyLegacySpend` with a table verifier, a test backend that ignores the digest.
They cover both branches, signatures in the wrong order, a missing signature, and the lock-time and sequence boundaries.
They also cover a negative-zero selector, the dummy with and without `NULLDUMMY`, and the CLTV flag clear.
Each encoding error has a case: DER, high S, hash type and key type.

`lake test` also compares, for three script codes of the template and six hash types, `legacySignatureHash` with the digest of `legacyReferencePlan`.
Both are DogeLib definitions, so these 18 comparisons are a consistency check, not independent evidence.
The independent evidence for `legacySignatureHash` is Core's `sighash.json`.

Core's compiled code supplies the verdicts of 25 signed spends of one 2-of-3 instance of the template, with fixed keys.
`lake test` and the live Core comparison check DogeLib against them, as [B4](#b4-the-oracle-and-foreign-boundaries) states.
They cover the three signer pairs, the recovery branch and the recorded mutations.
They are finite evidence for that instance, not a theorem about other keys, lock times, transactions or flags.
By `#print axioms` with Lean `v4.35.0`:

| Theorem | Axioms |
| --- | --- |
| `multisigVisits_cons`, `greedyMatch_cons`, `smallIntOpcode_facts` | None |
| `multisigLoop_cons`, `multisigLoop_visits_error`, `pushEncoding_small`, `countOp_small`, `multisigRecoveryScript_eq`, `trueTop_boolBytes` | `propext` |
| `multisigLoop_visits_ok`, `multisigLoop_ok_visits`, `checkSignatureEncoding_ok_iff`, `checkPubKeyEncoding_ok_iff`, `multisigCheck_eq_ok_iff`, `sigAccepted_iff`, `sigAccepted_of_checkSig`, `multisigRecoveryScript_length`, `checkSigStep_recovery`, `effectiveScriptCode_length_le`, `transactionChecker_checkSig_ne_none`, `hash160_toList_length`, `verifyLegacySpend_scriptSig_rejected`, `verifyLegacySpend_scriptSig_unsupported` and the other layout lemmas | `propext`, `Quot.sound` |
| `multisigRecovery_sound`, `multisigRecovery_ordinary_complete`, `multisigRecovery_recovery_complete`, `multisigRecovery_accepted_iff`, `multisigRecovery_twoOfThree_accepted_iff`, `multisigRecovery_ordinary_unsupported`, `multisigRecovery_recovery_unsupported`, `multisigRecovery_lockTime_lt`, `multisigRecovery_accepted_lockTime_lt`, `multisigRecoveryScript_twoOfThree` and the evaluation lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| `multisigRecoveryScript_length_le`, `ordinaryCode_length_lt`, `recoveryCode_length_lt` | `propext`, `Quot.sound` |
| `scanOps_cons_opcode`, `keys_scanOps`, `redeemTail_scanOps`, `multisigRecoveryScript_scanOps`, `ordinaryCode_scanOps`, `recoveryCode_scanOps`, `transactionChecker_verify_reference`, `sigAccepted_iff_reference`, `MultisigRecoverySpend.sigAccepted_ordinary_iff_reference`, `MultisigRecoverySpend.sigAccepted_recovery_iff_reference`, `MultisigRecoverySpend.checkSig_ordinary_reference`, `MultisigRecoverySpend.checkSig_recovery_reference` | `propext`, `Classical.choice`, `Quot.sound` |
| `MultisigRecoverySpend.sigAccepted_ordinary_allOnly_commits`, `MultisigRecoverySpend.sigAccepted_recovery_allOnly_commits` | `propext`, `Classical.choice`, `Quot.sound` |

### Compact encoding and difficulty retarget

The `Work` layer specifies Core's `SetCompact`, `GetCompact` and `CalculateDogecoinNextWorkRequired` (SOURCES.md, D6, D12, D13).

For every 256-bit value `a`, `setCompact_getCompact_le` says that decoding the compact encoding of `a` gives at most `a`.
`setCompact_getCompact_flags` says that the decoder reports no sign and no overflow for it.
`getCompact_setCompact_getCompact` says that encoding the decoded value again gives the same compact.
`setCompact_getCompact_of_lt` says that the round trip is exact for `a < 2^23`.
`getCompact_assertions` says that the two `assert` statements of `GetCompact` hold for every value.

`getCompact_setCompact_iff` says that a 32-bit compact survives decoding and encoding again exactly when `GetCompact` produces it.
Core's tests contain compacts that do not survive, and three theorems record them, such as `0x04923456`, which encodes again as `0x04123456`.
`setCompact_fOverflow` says that `SetCompact` sets its overflow flag exactly when the encoded number is at least 2^256.

`modulatedTimespan_mem` says that the clamped timespan lies within the bounds of its regime, for every input.
Four theorems state those bounds for DigiShield and for each height range before it, and two state them for the mainnet parameters.
`retarget_decoded_le_powLimit` says that the new compact target decodes to at most `powLimit`, with neither flag set, for every input.
The input includes old targets above `powLimit` and 256-bit products that wrap.

The signed arithmetic is specified in `Int`, with `Int.tdiv` for the C++ division.
`signedSteps_fit` says that no `int64_t` step overflows when both block times are in `[0, 2^32)` and the target timespan is below 2^61.
`modulatedTimespan_eq_int64` says that Lean's `Int64` operations compute the same timespan on that domain.
Outside it, a C++ signed overflow is undefined behavior, and the `Int` result is a choice of this specification.

The 256-bit product at line 80 is reduced modulo 2^256, as Core reduces it.
`retarget_eq_of_no_wrap` gives the exact result when the product does not wrap.
`no_wrap_of_le_powLimit` and `mainnet_limit` say that it does not wrap for the mainnet parameters when the old target is at most `powLimit`.
`retarget_wrap_example` shows a wrap for an old target of 2^255: a longer actual timespan gives a smaller target.

`validProofOfWorkTarget_iff` supplies the old-target bound from Core's separate target check, as the supplied-hash subsection explains.
The finite-view caller checks coherent heights without establishing target validity.
A claim about a validated chain still assumes that the previous block passed the required check.

The axioms of the 45 theorems in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `mainnet_limit`, `filteredTimespan_rounding` |
| `propext` | `pow256`, `getCompact_setCompact_zero_mantissa`, `getCompact_setCompact_negative`, `setCompact_overflow_example`, `retargetTimespan_pos` |
| `propext`, `Quot.sound` | `byteLength_bounds`, `byteLength_eq`, `byteLength_le`, `and_two_pow_ne_zero`, `sign_bit`, `tdiv_eq`, `timespanLimits_le` |
| `propext`, `Classical.choice`, `Quot.sound` | Every other theorem in `Work.Proofs.ArithUint256` and `Work.Proofs.Retarget`, including `modulatedTimespan_mem`, `retarget_decoded_le_powLimit`, `setCompact_getCompact_le`, `getCompact_setCompact_iff`, `setCompact_fOverflow`, `signedSteps_fit`, `retarget_eq_of_no_wrap` and `no_wrap_of_le_powLimit` |
Some concrete examples use `decide +kernel`, which the kernel checks without compiled code.

These parts are not proved and not specified:

- The checks of `ContextualCheckBlockHeader` other than the version gates, such as `nBits` against `GetNextWorkRequired`, and `CheckBlock`.
  [Dogecoin's scrypt digest](#dogecoins-scrypt-digest), [the AuxPoW check](#the-auxpow-check) and [header proof of work](#header-proof-of-work) specify the scrypt digest, `CAuxPow::check` and `CheckAuxPowProofOfWork`.
  The supplied-hash check is specified separately below.

The word-model refinements below cover multiplication, division, both shifts, bit length and low-64-bit extraction.
They also cover division's comparison, addition, negation and subtraction dependencies.
The correspondence between Core's source and the Lean models remains subject to review (A1).

`lake test` runs the six `get_next_work_*` cases of `dogecoin_tests.cpp` and the 21 steps of `bignum_SetCompact` through the compiled code (B1).
It also runs 17 cases of the `multiply`, `divide` and `methods` tests of `arith_uint256_tests.cpp` (D16) through `mulUInt32`, `div` and `getLow64`.
All 17 cases also run through the corresponding word models.
The word division model also runs the two zero-divisor cases.

### Target validity and supplied-hash proof of work

`Work.ProofOfWork` specifies `CheckProofOfWork` at D17, `src/pow.cpp` lines 115-132.
The inputs are a supplied `Hash256`, a UInt32 compact target and a parameter record, of which only `powLimit` is read.
`hashToArith256` uses the eight little-endian `UintToArith256` word reads.
`hashToArith256_eq` proves equality to the independent radix-256 interpretation for every supplied hash.
The input bytes have Core's internal order, with byte zero least significant for the arithmetic comparison.

`validProofOfWorkTarget_iff` characterizes acceptance of the target check for every compact and parameter record.
The decoded target must be nonzero, at most `powLimit`, and have neither the negative nor overflow flag set.
The check permits noncanonical compacts, such as `0x04000001`, which decodes to 256.
`checkProofOfWork_iff` adds the condition that the supplied hash is at most the target.
`validProofOfWorkTarget_iff_exists_hash` proves that target validity is equivalent to acceptance of some supplied hash, with zero as a witness.
`checkProofOfWork_mono` proves that a smaller hash remains accepted for a fixed compact and parameter record.

`no_wrap_of_validProofOfWorkTarget` supplies the previous-target bound to `no_wrap_of_le_powLimit`.
It retains the numerical hypothesis `powLimit * 4T < 2^256`, where `T` is the target timespan.
`retarget_eq_of_validProofOfWorkTarget` also assumes `T < 2^30`, and gives the existing exact closed form for all retarget inputs.
The mainnet and testnet `*_proofOfWork_bounds` theorems discharge both numerical hypotheses at every UInt32 parameter-selection height.
They cover every selected record, including the AuxPoW eras, by kernel computation on the records after the selection proof.
Their `*_no_wrap_of_validProofOfWorkTarget` and `*_retarget_eq_of_validProofOfWorkTarget` corollaries retain only previous-target validity.

Selection height and retarget height remain explicit independent inputs.

Both regtest records fail the conservative `powLimit * 4T` bound, because their limit is `2^255 - 1`.
`regtestDigishield_modulatedTimespan` proves that the DigiShield record's multiplier is exactly one for every height and actual timespan.
`regtest_no_wrap` and `regtest_retarget_eq` therefore cover every compact at all regtest selection heights from ten, without a target-validity hypothesis.

`legacy_regtest_wrap_example` records a valid compact `0x207fffff`, actual timespan 901 and retarget height one.
The isolated retarget with the legacy regtest record returns `0x1f02467a`, after the product exceeds 2^256.
This wrap is Core's own behavior: `src/dogecoin.cpp` line 80 calls multiplication modulo 2^256 in `src/arith_uint256.cpp` lines 55-65.
DogeLib models that behavior.
The example is reachable through the isolated `CalculateDogecoinNextWorkRequired` API with that record.
The normally selected regtest `GetNextWorkRequired` caller cannot reach a legacy retarget: the legacy record applies below height ten, with interval 14400.

`lake test` runs 20 synthetic branch and boundary cases derived from D17 lines 124-129.
It also requires target validity for all 312 pinned mainnet headers.
Core's `src/test/auxpow_tests.cpp` lines 333-355 mines passing and failing digests at runtime, rather than supplies fixed digest fixtures.
The Lean tests do not compute scrypt or compare with compiled Core.
A supplied-hash check does not establish that the hash is the correct scrypt digest, or that a header or AuxPoW is valid.
[Header proof of work](#header-proof-of-work) supplies the scrypt digest and composes this check with the AuxPoW check.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems in `Work.Proofs.ProofOfWork` |
| --- | --- |
| None | `mainnet_proofOfWork_bounds` |
| `propext`, `Quot.sound` | `hashToArith256_eq`, `hashToArith256_zero`, `testnet_proofOfWork_bounds` |
| `propext`, `Classical.choice`, `Quot.sound` | All other theorems, including the target characterizations, monotonicity, retarget corollaries and legacy regtest example |

### 256-bit word arithmetic

`ArithUint256.Words` models Core's eight little-endian `UInt32` words as a function from `Fin 8`.
`ofArith_toArith` and `toArith_ofArith` prove that the word and arithmetic representations have inverse conversions.
The model follows the pinned loops in `arith_uint256.cpp` and the `GetLow64()` expression in `arith_uint256.h` (D12, D13).

`mulUInt32_toArith`, `shiftLeft_toArith`, `shiftRight_toArith`, `bits_toArith` and `getLow64_toArith` relate the word models to the arithmetic definitions.
They quantify over every eight-word input.
Multiplication also quantifies over every `UInt32` multiplier, and both shift theorems cover every natural shift.
Core takes an unsigned 32-bit shift, so that domain is included.
The corresponding `*_ofArith` theorems start from every `ArithUint256` value.
`bits_le` bounds the scan's result by 256.

`mul_intermediate_lt` proves that `carry + b32 * pn[i]` fits in 64 bits when the carry fits in 32 bits.
`mul_step` proves that the `UInt64` operations preserve that exact value.
`mulLoop_value` accounts for the full product, including the final carry, for every word count and initial carry below 2^32.
The exported multiplication theorem discards that carry modulo 2^256.

The axioms of the 24 public theorems in `Work.Proofs.ArithUint256Words`, by `#print axioms` with Lean `v4.35.0`:
All theorem names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `eval_lt`, `digits_eval`, `value_lt`, `ofArith_toArith`, `mul_intermediate_lt`, `mul_step`, `mulLoop_value`, `mulUInt32_toArith`, `getLow64_toArith`, `eval_high`, `eval_testBit`, `shiftRight_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `eval_digits`, `toArith_ofArith`, `mulUInt32_ofArith`, `getLow64_ofArith`, `bitScan_eq`, `bitsLoop_eq`, `bits_toArith`, `bits_ofArith`, `bits_le`, `shiftLeft_toArith`, `shiftLeft_ofArith`, `shiftRight_ofArith` |

`lake test` runs the four multiply and three low-64-bit cases from D16 through both representations.
It also runs 1,792 shift cases from D16 lines 159-196 and 30 zero-result cases at shifts of at least 256.
Core's independent byte helpers (D16 lines 125-154) supply expected bytes for the shift cases.
The boundary cases expect zero from Core's word-index guards (D13 lines 30-33 and 47-50).

These theorems relate Lean models, rather than Core's compiled code.
The correspondence between Core's source and each word model remains subject to review (A1).
Core's bit scan tests `pn[pos] & 1 << bits` with a signed `int` literal.
For a 32-bit `int`, N3337 section 5.8 paragraph 2 leaves `1 << 31` undefined (S1).
The model expresses the intended `0x80000000` mask with `testBit`.
No theorem assigns semantics to undefined C++ execution.

### 256-bit word division

`Work.ArithUint256Division` models Core's comparison, addition, negation, subtraction and division loops over the same eight words (D12, D13).
`compareTo_eq` compares their natural values.
`addLoop_value` accounts for the final carry, with an initial carry of at most one.
`add_step` proves that this carry and two words sum exactly in 64 bits.
`add_value`, `neg_value` and `sub_value` give addition, two's-complement negation and subtraction modulo 2^256 for every word input.
Negation follows Core's complement and prefix increment, including every wrapped word.

`divide_toArith` and `divide_ofArith` equate word division with `ArithUint256.div` for every dividend and nonzero divisor.
`divLoop_spec` preserves `num + quotient * original divisor` and leaves `num` below the original divisor.
Its hypotheses require aligned divisor words, the numerator bound at the current shift, and zero low quotient bits.
`divide_value` establishes these hypotheses from Core's bit-length alignment and zero initial quotient.
The bound also proves that the initial left shift and each accepted subtraction preserve the exact natural value.

`divide_eq_none_iff` proves that the model returns `none` exactly when the divisor's value is zero.
Core zeroes its quotient before the zero-divisor test, then throws `uint_error("Division by zero")` (D13 lines 88-92).
The model represents the exception without the operand state after the throw.
Its separate early-return branch returns the zero quotient when the divisor has more bits than the dividend.
The arithmetic `div` requires a nonzero proof and excludes the exception branch.

The quotient bit update uses Core's intended unsigned mask.
Core writes the signed expression `1 << (shift & 31)` (D13 line 100).
At bit 31, the same N3337 5.8 paragraph 2 boundary applies as for `bitScan` (S1).
No theorem assigns semantics to undefined C++ execution.
The correspondence between Core's source and these Lean models remains subject to review (A1).
No proof covers Core's compiled code or Lean's compiler and runtime (B1, B2).

`lake test` runs all ten nonzero divide cases from D16 lines 357-367 through both models.
It also checks `none` for both `BOOST_CHECK_THROW` cases at lines 362 and 368.
The expected quotients and exceptions come from Core's test file.

`readWords_ofFn` proves that the vector copy at each loop boundary preserves every word.
This copy prevents repeated evaluation of function-valued words from earlier loop states.
It adds Lean core vector and array operations to the compiled path (B2).

The axioms of all 24 public theorems in `Work.Proofs.ArithUint256Division`, by `#print axioms` with Lean `v4.35.0`:
All names in this table are in `DogeLib.Work.ArithUint256.Words`.

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `add_step`, `addLoop_value`, `add_value`, `shiftRight_value` |
| `propext`, `Classical.choice`, `Quot.sound` | `readWords_ofFn`, `compareLoop_eq`, `compareTo_eq`, `incrementLoop_digits`, `incrementLoop_value`, `complement_value`, `neg_value`, `sub_value`, `sub_value_of_le`, `shiftLeft_value`, `quotient_mask`, `quotient_or_value`, `quotient_add_value`, `divLoop_spec`, `bits_eq_zero_iff`, `bits_value_bounds`, `divide_eq_none_iff`, `divide_value`, `divide_toArith`, `divide_ofArith` |

### Remaining word paths of the retarget

`Work.ArithUint256Compact` models Core's uint64 constructor, assignment, `SetCompact` and `GetCompact` over eight words (D12, D13).
`Words.ofUInt64_value` proves that construction stores every input exactly.
`ofUInt64_toArith` and `assignUInt64_toArith` equate construction and assignment with the arithmetic embedding, for every uint64 input and previous word array.
`assignUInt64` describes the explicit base-class overload at D12 lines 88-95, which sets every word.

The implicit `arith_uint256` copy assignment hides this base overload.
Thus `*this = nWord` in `SetCompact` and `num = 0x80` in D16 construct a temporary through D12 line 257, then copy it.
The temporary uses the uint64 constructor at D12 lines 51-57, and the base copy assignment copies its words at lines 44-49.

`Words.setCompact_toArith` equates the complete decoder result with `ArithUint256.setCompact` for every compact input.
The conclusion includes the magnitude and both flags.
For small exponents, both flags read the mantissa after the right shift, as Core does.
`Words.getCompact_toArith` equates the word encoder with `ArithUint256.getCompact` for every word array and both sign arguments.
These models use the proved word shifts, bit scan and low-64-bit extraction.

`Work.ArithUint256Bytes` gives an independent radix-256 interpretation of a 32-byte target.
`Words.uintToArith256_toArith` proves that eight grouped `ReadLE32` reads give that interpretation, for every 32-byte input (D13, D37).
`Words.readLE32_toNat` proves that each group fits exactly in its word.
The portable meaning of Core's `memcpy` and `le32toh` remains a source-review boundary.
Memory layout and Core's compiled code are not proved.

`targetBytesOfHex` models Core's backwards nibble scan for `0x` followed by exactly 64 ASCII hexadecimal digits (D11).
It rejects every other format.
It does not specify Core's general whitespace, prefix and truncation behavior.

Seven `*_powLimit_literal` theorems start from Core's literal strings at D14 lines 88, 248 and 392.
They prove the resulting `Words.toArith` interpretations equal the existing network parameter limits, including inherited DigiShield and AuxPoW limits.
The kernel checks these concrete computations with `decide +kernel`.
The literals come from Core, rather than from the arithmetic values under test.
The hex parser is checked only on the three concrete network strings, with two distinct spellings.

`calculateDogecoinNextWorkRequiredWords_eq` proves that word retarget returns `some` of the arithmetic target for every existing parameter record and input.
The executable model preserves division's `Option`, and the proof uses the positive-timespan field to exclude the exception.
It includes the divisor constructor, compact operations, multiplication, division and word comparison with the limit.
`calculateDogecoinNextWorkRequiredWithWords_eq` covers every explicit word limit, with that limit's arithmetic interpretation.
`calculateDogecoinNextWorkRequiredBytes_eq` also covers every 32-byte limit, through `UintToArith256` and its independent interpretation.

`retarget_mainnet_literal`, `retarget_testnet_literal` and `retarget_regtest_literal` connect each literal directly to the byte retarget.
At every network selection height, each corollary exhibits parsed bytes and proves retarget equality for every retarget input.
These corollaries cover all ten tree records, including the records that share work fields.

The signed timespan calculation reuses Core's lines 41-74 through `Work.Retarget`.
The equality of the Lean retargets has no additional signed-arithmetic hypothesis.
Agreement with Core's signed execution retains the existing block-time and target-timespan bounds from `signedSteps_fit` and `modulatedTimespan_eq_int64`.
The inherited bit-scan and division-mask models retain their intended-unsigned-mask boundary under S1.
The models' correspondence to Core's source remains subject to review (A1), and compiler and runtime trust remains (B1, B2).

The retarget materialises intermediate words with the vector copy from the division model.
`readWords_ofFn` proves that each copy preserves the words.
The copy avoids repeated computation of earlier word operations and retains the Lean core array execution boundary (B2).

`lake test` runs all 21 D16 compact cases through both arithmetic and word models, including both flags.
The derived assignment case at line 490 exercises uint64 construction, followed by a copy whose value is unchanged.
All six D7 retarget cases run through the arithmetic function and both word entry points.
The byte entry point starts from Core's mainnet hexadecimal limit.
These expectations come from Core's tests and are not a comparison with Core's compiled code.

The axioms of all 22 public theorems in `Work.Proofs.ArithUint256Compact`, `Work.Proofs.ArithUint256Bytes` and `Work.Proofs.RetargetWords`, by `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `Words.ofUInt64_value`, `Words.ofUInt64_toArith`, `Words.assignUInt64_toArith`, `Words.readLE32_toNat`, `Words.uintToArith256_value`, `Words.uintToArith256_toArith` |
| `propext`, `Classical.choice`, `Quot.sound` | `Words.setCompact_toArith`, `Words.getCompact_toArith`, all seven `*_powLimit_literal` theorems, `Words.compareTo_gt`, `calculateDogecoinNextWorkRequiredWithWords_eq`, `calculateDogecoinNextWorkRequiredWords_eq`, `calculateDogecoinNextWorkRequiredBytes_eq`, `retarget_mainnet_literal`, `retarget_testnet_literal`, `retarget_regtest_literal` |

The `Words` and literal theorem names are in `DogeLib.Work.ArithUint256`.
The retarget and network corollary names are in `DogeLib.Work`.

### Next-work selection and work parameters

`DogeLib.Work.Consensus` projects the work fields from Core's parameter records (D14, D15).
`ConsensusTree.getConsensus` follows the left and right search links and checks the right candidate's effective height before accepting it.
The three `getConsensus_*` theorems give the projected work fields at every UInt32 target height.
Mainnet changes at 145000, testnet at 145000 and 157500, and regtest at 10.
AuxPoW records retain separate effective heights but repeat these fields.
The projection makes no claim about the other consensus fields.

`DogeLib.Work.NextWork` specifies the caller of the retarget (D17, lines 32-88).
`nextWorkRequired` selects the candidate height's parameters, as validation and mining do (D33, D34).
The local interval becomes one at previous height 145000.
`retargetInterval_no_recovery` proves that the non-retarget branch cannot execute from that previous height, for every parameter record.

The recovery loop uses the record's interval instead of that local interval.
`retargetInterval_eq_record_of_nonretarget` proves that the local and record intervals agree whenever the caller is off a retarget boundary, for every record.
Recovery requires that condition, so no input can reach recovery with different intervals.
At previous height 144999, the candidate's DigiShield record already has interval one.

The all-block minimum rule checks previous height at least 157500 and a strict delay greater than twice the spacing (D6, lines 26-39).
Selected testnet parameters permit minimum difficulty from candidate height 157500, so that candidate still retargets and candidate 157501 can use the delay rule.
This caller ignores `fPowNoRetargeting`, including on regtest.
It also ignores `fPowAllowDigishieldMinDifficultyBlocks`.

The view is a newest-first list of explicit height, UInt32 time and compact target fields.
The adapter checks consecutive heights and bounds every height below 2147483647.
The last entry may be above genesis, so the view need not contain all history.
A walk that still needs a predecessor returns `missingAncestor` at a truncated suffix.
Core's corresponding ancestor assertion aborts when the required index is absent.

The model omits skip links and uses the predecessor path for ancestor lookup (D35).
No theorem relates Core's skip-pointer traversal to that path.

`blocksToGoBack_le` excludes the negative-first-height assertion when the interval is positive and divides the next height.
The adapter checks `zeroInterval` before the retarget boundary and underflow checks.
Thus `firstHeightUnderflow` is unreachable for every validated view: a positive interval at a retarget satisfies `blocksToGoBack_le`.
Malformed-view errors are separate from both assertion cases.
These errors are adapter contracts, not Core rejection codes.
The UInt32 times widen to Int, and the fixed network spacings of 1 or 60 keep the delay arithmetic within int64_t.

`getNextWorkRequired_genesis` proves the null-tip result for every record and candidate time.
`getNextWorkRequired_minDifficulty` proves the minimum result when validation succeeds and the all-block minimum condition holds.
`recoverLastNonMinDifficulty_mem` proves that a successful recovery returns a supplied entry's compact, without a header-validity hypothesis.
These caller claims do not establish target validity.

Two theorems bound the history that the caller reads.

`nextWorkRequired_congr_prefix` takes two views that pass `validateWorkView` and start with the same entry at height `h`.
If they agree on their first `retargetInterval params h + 1` entries, where `params` is the record at the candidate height, the results are equal.
A retarget reads the entry at index `blocksToGoBack`, at most the interval.
The recovery walk stops at the latest at a height divisible by the interval (`recoverLastNonMinDifficulty_congr_prefix`).

`nextWorkRequired_ok` shows that a checked view that reaches height 0 gives a value, never an adapter error, for every network and candidate time.
It uses `difficultyAdjustmentInterval_getConsensus_pos`: every selected record has a positive interval.
The separate target-check theorem supplies the old-target bound when target validity is assumed.

`lake test` includes source-derived network and branch examples and all six D7 retarget answers through synthetic contiguous views.
The intermediate entries are synthetic, not historical headers.
These examples do not run Core or prove equality to its compiled caller.

`lake test` also reads 312 real mainnet headers at heights 144719–145030 from a public Electrum server.
The [fixture README](tests/work/mainnet-headers/README.md) records the source, date and exact request.
The test hashes all headers with compiled `Sha256d`, checks all predecessor links and requires Core's checkpoint hash at 145000 (D9).
It compares `nextWorkRequired .mainnet` with 278 difficulty copies, the interval-240 retarget at 144960 and 31 DigiShield retargets at 145000–145030.
The substantive retarget evidence is 144960 plus those 31 DigiShield blocks.

The first header supplies context.
Retarget 144720 lacks an ancestor, so the test requires `missingAncestor` there.
The test also requires target validity for all 312 headers with the selected mainnet parameters.
Those finite checks establish the old-target bound for these inputs, but neither proof of work nor AuxPoW validity.
They do not run Core or prove equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `getConsensus_mainnet`, `getConsensus_regtest` |
| `propext` | `retargetInterval_after`, `blocksToGoBack_first`, `blocksToGoBack_later`, `recoverLastNonMinDifficulty_mem`, `retargetInterval_no_recovery` |
| `propext`, `Quot.sound` | `getConsensus_testnet`, `retargetInterval_before`, `blocksToGoBack_le`, `retargetInterval_eq_record_of_nonretarget` |
| `propext`, `Quot.sound` | `validateWorkView_cons_cons`, `length_of_validateWorkView`, `recoverLastNonMinDifficulty_congr_prefix`, `difficultyAdjustmentInterval_getConsensus_pos`, `recoverLastNonMinDifficulty_ok` |
| `propext`, `Classical.choice`, `Quot.sound` | `getNextWorkRequired_genesis`, `getNextWorkRequired_minDifficulty`, `getNextWorkRequiredFromView_congr_prefix`, `nextWorkRequired_congr_prefix`, `nextWorkRequired_ok` |

### Median time past

`DogeLib.Work.MedianTimePast` specifies `CBlockIndex::GetMedianTimePast` (D18, lines 284-298).
Core collects the time of the entry and the times of up to ten predecessors, and stops early after genesis.
It sorts the collected times and returns the element at index `count / 2`, so an even count gives the upper median.
`ContextualCheckBlockHeader` calls it on the predecessor of a header (D33, lines 3103-3104).
[Contextual header validation](#contextual-header-validation) specifies that comparison with the header time.

`medianTimePast` takes the checked finite view of [next-work selection](#next-work-selection-and-work-parameters), newest first.
Let `h` be the height of the first entry, and let `k = medianTimeSpan = min(11, h + 1)`.
Core's walk has the full chain, so it always collects `k` times.
A finite view can stop above genesis, and Core's function on such a view would give a different median, not an error.
So `medianTimePast` returns the adapter error `shortView` for a view with fewer than `k` entries.

`medianTimePast` returns `invalidView` when `validateWorkView` rejects the view, and `emptyView` for the empty view.
These errors are adapter contracts, not Core rejection codes.

The times are UInt32 values widened to Int, as `GetBlockTime` widens them to int64_t (D18, lines 274-277).
The widening is exact, so the sort and the comparisons agree with Core's int64_t order on every UInt32 time.
`sortedTimes` sorts with `List.mergeSort` from Lean core.
`sortedTimes_perm` and `sortedTimes_sorted` prove that it is an ascending permutation of the first `k` times, for every view.

The theorems below hold for every view whose first entry is `last`:

- `medianTimePast_eq`: if the view passes `validateWorkView` and has at least `k` entries, the result is index `k / 2` of `sortedTimes`.
- `medianTimePast_short`: if the view passes `validateWorkView` and has fewer than `k` entries, the result is `shortView`.
- `medianTimePast_invalid` and `medianTimePast_nil` give the two other adapter errors.
- `medianTimePast_ok` gives the hypotheses and the index of `medianTimePast_eq` from a success.
- `medianTimePast_mem`: a success is the time of one of the first `k` entries.
- `medianTimePast_bounds`: a success lies between the least and the greatest of those times.
- `medianTimePast_rank`: for a success, at least `k / 2 + 1` of those times are at most the result, and at least `k - k / 2` are at least the result.
  This statement does not mention the sort, so it fixes the upper median independently of `sortedTimes`.
- `medianTimePast_congr_prefix`: two views that pass `validateWorkView` and agree on their first `k` entries give the same result, success or error.

`lake test` reads a fixture of the 13 mainnet headers at heights 0–12.
Two public Electrum servers returned the same bytes for these headers.
The [fixture README](tests/work/mainnet-genesis-headers/README.md) records the sources, the date and the exact request.
The test hashes the headers with compiled `Sha256d`, checks all predecessor links and requires Core's genesis hash (D9).

It compares the median at each height with a table derived by hand.
The table includes the even counts at heights 1, 3, 5, 7 and 9.
It also requires chain acceptance at heights 1–12: each header time is greater than the median of its predecessor.
The genesis hash anchors only height 0, so the provenance of heights 1–12 relies on the two sources.

The test also reads the 312 mainnet headers at heights 144719–145030.
It requires `shortView` for the 10 predecessors with fewer than 11 entries in the view, and chain acceptance for the 301 candidates from 144730.
Four windows have times out of order, so that the median differs from the time of the sixth entry.
The test compares those four medians with heights derived by hand.
Thirteen synthetic cases cover even counts, times out of order, equal times, the UInt32 bounds and each adapter error, with hand-derived results.
These checks do not run Core or prove equivalence on other inputs.

By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| `propext`, `Quot.sound` | `sortedTimes_perm`, `sortedTimes_sorted`, `length_sortedTimes`, `medianTimePast_nil`, `medianTimePast_invalid` |
| `propext`, `Classical.choice`, `Quot.sound` | `medianTimeSpan_bounds`, `medianTimePast_short`, `medianTimePast_eq`, `medianTimePast_ok`, `medianTimePast_mem`, `medianTimePast_bounds`, `medianTimePast_rank`, `medianTimePast_congr_prefix` |

### Proposed revisions: the framework

`DogeLib.Proposals.Framework` holds the framework of [design record 0007](docs/design/0007-proposed-revisions.md) for proposed revisions.
It belongs to the `Proposals` and `ProposalProofs` libraries, and no baseline library imports it ([ARCHITECTURE.md](ARCHITECTURE.md#proposed-revisions)).
No proposal exists yet, so these theorems state no property of any proposed revision.

`Framework.Script` copies `evalLoop`, `evalScript` and `verifyScript` as `evalLoopWith`, `evalScriptWith` and `verifyScriptWith`.
Each copy takes an instruction step `step` in place of `evalInstruction`.
It also takes an error map `embed : ScriptError → ε` for the errors that the loop and `VerifyScript` produce themselves.
`baselineStep embed checker flags` is `evalInstruction checker script flags` with its errors mapped by `embed`.

The agreement theorems hold for every error map, checker, flag set, script, state and stack:

- `evalLoopWith_baseline`: `evalLoopWith embed (baselineStep embed checker flags)` equals `evalLoop checker flags`, with the error mapped by `embed`.
- `evalScriptWith_baseline`: the same for `evalScript`.
- `verifyScriptWith_baseline`: `verifyScriptWith embed (baselineStep embed (some c) flags) flags` equals `verifyScript c flags`, with the error mapped by `embed`.

`Restricts step₁ step₀` holds when every successful step of `step₁` is a successful step of `step₀` with the same state.
For all steps with `Restricts step₁ step₀`, and all error maps of the two steps:

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

No block-level or chain-level theorem uses a projection yet, because DogeLib has no block validity.
The worked example states Script-local theorems with the identity projection.

The framework adds no axiom, hypothesis or trust assumption.
A proposal's theorems are about DogeLib's definitions, and they inherit the gaps of the baseline definitions that they reuse.
By `#print axioms` with Lean `v4.35.0`:

| Axioms | Theorems |
| --- | --- |
| None | `VerifyOutcome.verdict_ofBaseline` |
| `propext` | `Activation.none_inactive`, `Activation.isActive_lt`, `Activation.isActive_of_le`, `baselineVerdict_eq_accepted`, `VerifyOutcome.verdict_eq_accepted` |
| `propext`, `Quot.sound` | `evalLoopWith_baseline`, `evalScriptWith_baseline`, `verifyScriptWith_baseline`, `evalLoopWith_restricts`, `evalScriptWith_restricts`, `verifyScriptWith_restricts`, `verifyScript_of_restricts`, `evalLoopWith_congr`, `evalScriptWith_congr`, `verifyScriptWith_congr`, `Activation.isActive_iff`, `Activation.isActive_mono`, `inactiveEq_verifyScriptWith`, `restrictsAcceptance_verifyScriptWith` |

### Proposed revisions: the worked example

`DogeLib.Proposals.ExampleVersionVerify` is the worked example of [design record 0007](docs/design/0007-proposed-revisions.md), section 10.
It is not a proposal for Dogecoin, and no network activates it.
Decision 9 keeps it in the `Proposals` library as a permanent test of the framework.

The example redefines `OP_NOP10` (`0xb9`).
With `active` true and the opcode in an executing branch, `exampleStep` runs the baseline `evalInstruction` and then `versionCheck` on its successful state.
`versionCheck` rejects an empty stack, an operand of more than five bytes and a negative operand.
It also rejects an operand above the transaction version, read as an unsigned 32-bit value.
Without a transaction context it reports an unsupported capability.
It never pops the operand, and it returns the state that it receives or fails.

What the proofs say. Every theorem is Script-local: it is about one call of `evalScript`, `verifyScript` or `verifyLegacySpend`, not about a block or a chain.

- `exampleStep_restricts`: for every `active`, context, checker, flag set and baseline error map, the example step restricts the baseline step.
- `example_inactive_eq`, `example_evalScript_inactive_eq`, `example_spend_inactive_eq`: with `active` false, each revised definition equals the baseline result with the error under `Sum.inl`. This holds for every other argument. Every result agrees, including each rejection and each unsupported capability.
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

- **Unsupported reason.** The framework's unsupported reasons are the baseline type `Unsupported`, which the example cannot extend. A missing context reports `noContext`, which is `Unsupported.signatureOpcode 0xb9`. That constructor's documentation describes an unavailable signature check, so the label is a stand-in. The baseline reports `signatureOpcode op` only for `0xac` to `0xaf`, but no theorem states that, so a consumer that reads the reason relies on the documentation. A missing context stays unsupported, never a rejection. Issue #122 proposes a framework type of unsupported reasons that a proposal can extend.
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

### What cannot be proved yet

A `partial` definition, an `opaque` constant, or a definition that unfolds to one cannot be evaluated by the kernel.
CONTRIBUTING.md says to avoid `partial` definitions in the specification library (*Specification code*), and requires explicit treatment of `opaque` (*Proofs*).
Each such definition that remains is listed here with its reason.

## Gap A: does the definition say what Dogecoin does and what the client needs?

### A1. A wrong definition

A definition can differ from Dogecoin's behavior while every theorem about it holds, because the theorems are proved about the definition, not about Dogecoin Core.
Three things guard against that.
Each definition is named and shaped after its source in `SOURCES.md`, so that a reader can compare them line by line.
Fixtures come from pinned Core tests, primary specifications or documented historical data, never from the implementation under test.
Core comparisons run the compiled oracle against the pinned Core revision.

The source registry exists. The fixtures are listed per operation in the *Comparison* column of [COVERAGE.md](COVERAGE.md), and each records its provenance.
The Core comparison runs the compiled oracle and Core's own code at the pin on the same requests, for the operations of the oracle ([docs/oracle.md](docs/oracle.md#the-core-harness)).
It shows agreement on the requests it sends, and nothing about other inputs.

The real mainnet headers test next-work selection across DigiShield activation against historical `nBits` values.
The next-work subsection states the exact branch counts.
Hash links connect headers through 145000 to the pinned Core checkpoint, subject to the hash commitment assumption.
The checkpoint does not authenticate later headers, whose provenance still relies on the public source.
The fixture digest pins all bytes, and the compiled test checks links through 145030.
Neither check establishes proof of work, AuxPoW validity or full header validity.

The multiplication, shift, bit-length and low-64-bit models have arithmetic equivalence proofs, as the *256-bit word arithmetic* subsection states.
A reader still checks their correspondence to Core's source.
The division, comparison and subtraction models also have arithmetic equivalence proofs, as the *256-bit word division* subsection states.
The word division model represents Core's zero-divisor exception.
The arithmetic definition takes a nonzero proof.

The compact, uint64 construction and byte conversion models have arithmetic equivalence proofs, as the *Remaining word paths of the retarget* subsection states.
The composed word retarget uses these models and the proved `CompareTo` model.
Its equality with the arithmetic specification holds for every existing input.
Network powLimit proofs start from Core's hexadecimal literals, through the restricted hex parser and word conversion.
A reader still checks the models against Core's source.

A Dogecoin rule can differ from the Bitcoin rule it descends from.
A definition or proof adopted from btc-verified is evidence to investigate, not a compatibility proof for Dogecoin.

### A2. Hypotheses inside theorems

A conditional theorem is only as strong as its hypotheses.
`legacySignatureHashPlan_eq_reference` equates the field-by-field production plan with the transaction-transformation reference for every input index and hash type.
It requires fully parsed script code, fewer than 2^32 inputs and fewer than 2^32 outputs.
The transformation-reference subsection states these hypotheses and explains the short-push difference.

For the script code of the multisig-with-recovery template, `ordinaryCode_scanOps` and `recoveryCode_scanOps` discharge the parse hypothesis, and the `InputContext` gives the count bounds.
For other scripts, `effectiveScriptCode_scanOps` reduces it to the parse of the script suffix from the cursor.
Whatever those hypotheses leave unproved is part of what a reader trusts.

`transactionChecker` takes the elliptic-curve check as a parameter `verify`.
A Script result that uses it holds for Core only under the verifier-agreement hypothesis of [Script signature opcodes and the checker](#script-signature-opcodes-and-the-checker).
With `verify := coreVerifier`, the theorem keeps no verifier hypothesis.
The agreement is then an A1 claim, with the open step of [Secp256k1 public-key parser and Core's verifier](#secp256k1-public-key-parser-and-cores-verifier).
The ordered-matching theorems of that subsection also assume a checker answer and passing encoding checks on every pair of signatures and keys.

The worked property of [multisig with recovery](#script-worked-property-multisig-with-recovery) assumes a checker answer only on the pairs that Core visits, and its soundness direction assumes none.
Its converses also assume a bound on the stack below the redeem script.

`verifyLegacySpend` requires an `InputContext`, whose index selects an input and whose transaction has fewer than 2^32 inputs and outputs.
Core's transaction reader gives the two count bounds, and `InputContext.ofDecoded` takes them from a successful `decodeBaseComplete`.
A caller that builds a transaction from fields must supply them.

`no_wrap_of_validProofOfWorkTarget` discharges the old-target bound of `no_wrap_of_le_powLimit` from Core's target-validity predicate.
Its numerical bound holds for every selected mainnet and testnet record.
Regtest DigiShield uses a separate exact-multiplier argument, and legacy regtest permits wrap in the isolated retarget.
The supplied-hash subsection states the network corollaries and the caller boundary.

A chain-level application still assumes that the previous block passed Core's check with the relevant `powLimit`.
The header path supplies `GetConsensus(0)` to `CheckAuxPowProofOfWork` (D33, `src/validation.cpp` line 2933).
That function passes the record to `CheckProofOfWork` (D6, `src/dogecoin.cpp` lines 107 and 118).
Every record within a network has the same `powLimit` (D14, the record copies at lines 126-136, 282-300 and 425-432).

The round trips of the full header codec assume a payload exactly when the flag is set, and counts within `MAX_SIZE`.
The witness-allowed round trip also assumes a transaction shape.
[Full headers and the AuxPoW payload](#full-headers-and-the-auxpow-payload) states them.

The chain-level application also requires that the supplied hash is the correct scrypt digest.

`powHash_eq_spec` and `powHash_eq_fips` prove, for every 80-byte input, that the executable digest equals the RFC 7914 model with Dogecoin's parameters.
`PureBlockHeader.powHash_eq_spec` gives the same equality for the encoded bytes of every pure header.
These theorems relate DogeLib definitions, as [Dogecoin's scrypt digest](#dogecoins-scrypt-digest) states.
Source review, not a theorem, connects the executable to Core's `scrypt_1024_1_1_256_sp_generic` and the model to RFC 7914 (A1).
The comparison of digests with Core's compiled scrypt covers only the requests that it sends (B4).

`checkAuxPowProofOfWork_iff` characterizes DogeLib's definition of `CheckAuxPowProofOfWork`, and no theorem connects that definition to Core's code.
DogeLib does not specify full header validity: [Header proof of work](#header-proof-of-work) lists the checks that it omits.

The median-time-past theorems require a view that passes `validateWorkView`, and most of them require at least `medianTimeSpan` entries.
`medianTimePast` checks both conditions and returns an adapter error when one fails, so no caller discharges them silently.
No theorem says that the view is the chain below a given header.
The caller supplies that link, as Core's lookup of `pindexPrev` by hash supplies it.

The theorems of the block-index model take `WellFormed` as a hypothesis.
`lastCheckpointInIndex_eq` also assumes that each checkpoint hash in the index belongs to an entry at its table height.
[The block-index model](#the-block-index-model) states both hypotheses and what discharges them.
`checkWellFormed_iff` makes the first hypothesis checkable, and `wellFormed_preserved` shows that each step keeps it.
`accept_genesis_insert` assumes that the index lacks the genesis header's `hashPrevBlock` ([one step](#one-step-acceptblockheader)).

### A3. Side channels

DogeLib makes no constant-time claim.
The specification is a reference for behavior, not for timing.

### A4. Idealisations

A security theorem rests on a model, such as a random oracle for a hash.
DogeLib has no security theorem, so it has no idealisation.
Equality of two hash plans needs no assumption about the hash function.
A claim that different preimages give different digests needs a named collision hypothesis or a computational model.
The P2SH theorems of `DogeLib.Script.Proofs.Verify` assume no property of HASH160, and they claim nothing about other redeem scripts with the same digest.

### A5. Protocol context

Some rules apply only under a serialization mode, a network, an activation state or a historical era.
A definition that leaves out its context can be right in one era and wrong in another.
The first operations, base codecs and legacy signature hashing, have few context dependencies.

The transaction readers model two serialization modes of Core's reader: base mode and the witness-allowed format.
The witness-allowed format models serialization only.
Core rejects blocks with witness data on main and test at the pin.
The witness-format subsection records the separate script-verification and commitment mechanisms (D36), with their deployment parameters (D9).
No DogeLib theorem establishes consensus acceptance of witness data.

The legacy signature hash is the `SIGVERSION_BASE` mode of `SignatureHash`, and its script code is an input.
[Script signature-code preparation](#script-signature-code-preparation) specifies the interpreter's preparation of it.

The work-parameter search covers each network and height, and the next-work wrapper selects the candidate height.
The caller's hard-coded activation checks use the previous height, as the next-work subsection explains.
Version gating takes its record from the caller, and does not select it from a height.

`getContextualParams` selects the contextual fields of a record by network and height.
`lastCheckpoint` takes the node's checkpoint state as an explicit input.
`contextualCheckBlockHeader` selects its record at the candidate height, and takes the network, the adjusted time and the last known checkpoint as explicit inputs.
Its [subsection](#contextual-header-validation) records those inputs as execution boundaries.
Script verification takes its flags and its `InputContext` from the caller. Ledger work will need explicit context.

## Gap B: does the code that runs match the definitions?

DogeLib's theorems are about the Lean definitions, and everything between them and the running code is trusted.
A refinement proof relates the extracted functional Lean model to the specification.
Extraction and compiled Rust remain trusted boundaries (B6).

```text
 Dogecoin behavior --A-- Lean definition == proof == theorem
                              |
                              B
                              |
            compiled oracle, extracted Rust --D-- client

 C: is the proof itself sound?
```

### B1. The compilers and the runtime

The Lean compiler turns the definitions into C, a C compiler turns that into machine code, and the Lean runtime runs it.
No theorem covers that path.
Known answers and Core comparisons through the compiled code test it end to end, only on the inputs they cover.
`lake test` runs the 129 NIST CAVP SHA-256 vectors through the compiled `hash`.

### B2. Lean core's own implementations

Lean core implements some `Array`, `ByteArray` and `Nat` operations with `@[implemented_by]` or `@[extern]`.
The compiled code runs those implementations, not the definitions the kernel checks.
Lean core is a declared trusted baseline.
The packed encoders and decoders run two `@[extern]` operations of core: `ByteArray.push` and `ByteArray.get`.
`ByteSlice.toList` and the tests that call it also run `ByteArray.copySlice`, through `ByteArray.extract`.
The packed decoders of byte lists and of `Bytes n`, `instPackedCodecCountedListBytes` and `instPackedCodecBytes`, call `ByteSlice.toList` to read their bytes, so they run `ByteArray.copySlice` too.

The base-mode slice reader uses `ByteArray.size` (`lean_sarray_size`) for the bounds checks of `ByteSlice.slice` and `ByteArray.toList`.
Its fixed integer reads use `ByteArray.get` (`lean_byte_array_fget`) through `ByteSlice.get`.
Its hash and script reads use `ByteArray.copySlice` (`lean_byte_array_copy_slice`) through `ByteArray.extract` and `ByteSlice.toList`.
`ByteArray.toList` also calls `ByteArray.get!` (`lean_byte_array_get`).

`ByteSlice.size` subtracts its offsets, and `ByteSlice.take` and `ByteSlice.drop` use `ByteSlice.slice` to construct views.
Those slice operations have no separate `@[extern]` or `@[implemented_by]` body in Lean `v4.35.0`.
Only conversion of consumed hash or script bytes to a list copies bytes in this reader.

### B3. Native code during elaboration

If a library sets `precompileModules := true`, then `#eval` or an evaluating tactic in a module that imports it runs natively compiled code.
A proof is unaffected unless it uses one of the tactics of C2.

### B4. The oracle and foreign boundaries

The oracle reads fixture records and writes results through IO.
That adapter is outside the specification library, and no theorem covers it.

The oracle is `dogelib-oracle`, in the `Exports` library ([docs/oracle.md](docs/oracle.md)).
The adapter calls specification functions and converts their arguments and results:

- Lean core's `Json.parse` reads each request, and `Json.compress` writes each response. Both are trusted as Lean core is (B2).
- The adapter's own code converts hexadecimal text to bytes and back, JSON numbers and decimal strings to integers, and the specification's errors to JSON objects.
  The tests check these conversions at their boundaries, against expected values from Core's files, Core's source and Python's `hashlib`.
- The loop over standard input uses `repeat`, which Lean core defines with `partial`. `lake exe check-decls` exempts the `Exports` modules from its check of reachable opaque constants, and checks their axioms and their own declarations.

The base operations and the transaction argument of `sighash.legacy` convert hex bytes to a slice once.
`tx.read_base` uses `Transaction.readBaseSlice`.
`tx.decode_base` and `sighash.legacy` use `Transaction.decodeBaseCompleteSlice`.
`Transaction.abstractRead_readBaseSlice` preserves errors, fields and remainder bytes for every slice.
`Transaction.decodeBaseCompleteSlice_eq` preserves the complete reader's result, including errors and trailing-byte counts, for every slice.
The list readers remain the specification.

`ByteSlice.toList_ofByteArray` identifies the bytes in each whole-array slice that the adapter constructs with `ByteSlice.ofByteArray`.
These equalities do not cover the hex or JSON conversions.
The witness operations use list readers.

The witness operations convert `WitnessTransaction` stacks to arrays of item hex strings.
They expose `hasWitness`, witness-allowed serialization, the transaction ID and the witness hash.
No theorem covers these JSON conversions.
Core comparisons check these fields, consumption and errors on the recorded requests only.

The work operations convert target magnitudes in most-significant-byte-first hexadecimal and preserve compact values as UInt32 fields.
They select network parameters and pass UInt32 times to the retarget arithmetic.
`work.next` converts a newest-first JSON array to the specification's finite view.
Its `work_view` errors are adapter errors, not Core consensus rejection codes.
The harness checks caller preconditions before it invokes Core and excludes those errors from the comparison.
Its skip-height guard leaves unavailable skip destinations null, so Core uses predecessor links instead.

No theorem covers these JSON conversions, the harness guard or correspondence to Core's traversal.

The hash operations convert exact hex bytes to ByteArray and return twenty digest bytes without reversal.
The header operations preserve raw u32 fields and both hash byte orders.
The header prefix reader maps codec failure to `read/truncated` and returns the exact suffix.
The Merkle adapter requires exact 32-byte internal-order leaves and rejects arrays larger than 2^31 entries before computation.

These JSON conversions have no refinement theorem.
The Core harness calls the pinned hash classes, pure header methods and `ComputeMerkleRoot` directly.
Finite fixture and boundary comparisons cover the recorded inputs only.
They establish no all-input Core equivalence, cryptographic security, AuxPoW validity, scrypt result or full block validity.

The Script adapters call `readInstruction`, `evalScript`, `verifyScript` and `verifyLegacySpend`.
Evaluation selects no checker or `baseChecker`. Legacy verification selects `baseChecker` or `transactionChecker` with `coreVerifier`.
They encode Script errors with the names in the [shared table](harness/core/script_error_names.inc).

No theorem covers their JSON conversions.
Adapter limits allow scripts above 10,000 bytes and caller stacks above 1,000 items, so those specification boundaries remain observable.
The adapter bounds scripts and individual items to 1 MiB, stacks to 4,096 items, and total caller item bytes to 4 MiB.
`pubkey.verify` bounds each key and signature to 1 MiB and requires exactly 32 storage-order digest bytes.
It calls `coreVerify`, while the harness calls `CPubKey::Verify`.
These bounds imply fewer than 2^31 items and at most `UINT_MAX` bytes per item, the documented Core-correspondence domains.

JSON parsing and line allocation occur before these execution limits.
The limits do not bound transport memory or the Lean runtime's allocations.

The Core harness calls `GetOp` and `EvalScript` in `SIGVERSION_BASE` with `BaseSignatureChecker`.
That checker fails every signature, locktime and sequence check.
Unsupported Lean calls have no compared verdict.
The comparator reports their reasons and Core outcomes separately, and compares supported calls regardless of the opcode support set.

Two-call corpus compositions pass only the successful main stack between calls.
They ignore each record's witness and do not run `VerifyScript`, evaluate P2SH or reproduce a transaction signature checker.

Separate legacy streams call `VerifyScript` on inside-milestone corpus records and seeded mutations with each checker.
The transaction selection checks the index and InputContext count bounds before execution.
It uses the supplied previous-output script, without a UTXO lookup.
Lean decides each reached signature check with `coreVerifier`.
With the transaction checker, only unsupported flags exclude a verdict from comparison agreement.

Core uses `TransactionSignatureChecker`, `CPubKey::Verify` and libsecp256k1, with `ECCVerifyHandle` for the request loop (D3, D50).
The harness signs nothing and does not need `ECC_Start`.
These libraries, their key and signature parsing, and their compiled binary form a trusted runtime boundary, not a Lean proof.

The harness rejects flag combinations that violate Core's WITNESS and CLEANSTACK assertions without altering the flags.
The comparator counts these requests separately as `harness-refused` only after it checks both the refusal and Lean's unsupported-flags answer.
Neither outcome is comparison agreement or a Script verdict.
Finite comparisons establish neither full transaction validity nor equivalence to Core on all inputs.

A wrong conversion could make the oracle and Core disagree, or agree, for a reason outside the specification.

The Core harness, `harness/core/core_oracle.cpp`, is the other side of the comparison ([docs/oracle.md](docs/oracle.md#the-core-harness)).
A user of the comparison trusts these parts of it:

- Core's libraries at the pin, compiled by the compiler of the machine that runs the comparison: GCC 13 in CI, on `ubuntu-24.04`.
  Core v1.14.9 was released for older compilers.
  The build script uses `-O2 -ffunction-sections -fdata-sections`, and Core's configure selects C++11.
  GNU ld discards unused sections with `--gc-sections`.
- The harness's own code. It converts hexadecimal text and JSON numbers to Core's arguments, writes Core's results as JSON, and maps four exception messages to read errors.
  Any other exception from Core stops the harness, so it cannot pass as a result.
- The `plan` label of `sighash.legacy`. The harness computes it from Core's conditions instead of observing it. It stops if the label is `fixed_digest` and Core's digest is not the value one.
- The comparator, `scripts/compare_core.py`.
  Its self-test, `scripts/test_compare_core.py`, counts 102 cases: two passing controls and 100 negative checks that each fail with the code they target.
  The negative checks are 91 stream mutations, eight Rust-side mutations and one acceptance-count gap.
  Assertions about its refusal and timelock constructions run outside that count.
- For `sighash.legacy`, the oracle's preimage is checked by hashing it, not byte by byte: Core does not expose its preimage.

The separate `core-signer` tool generates [signed recovery-template fixtures](tests/script/signed-spends/README.md) with Core's `SignatureHash` and `CKey::Sign`.
Each expected verdict comes from Core's `VerifyScript`, with the digest and transaction recorded.
Fixture users trust the generator's template construction, high-S conversion, serialization and Core build.
The generator records its source blob and uses Core's randomness code with a stderr logging adapter.
Byte-for-byte regeneration checks reproducibility, but does not establish agreement with DogeLib.

`scripts/convert_script_tests.py` transcribes Core's `BuildCreditingTransaction` and `BuildSpendingTransaction` (D46) into its `context` function.
The [Script corpus](tests/script/corpus/README.md) commits the transaction bytes that this function generates for each record.
`lake test`, the oracle and the Core harness all receive those generated bytes, and the transaction checker hashes them.
So agreement between the oracle and Core on them does not check that they are the transactions of Core's test runner.
Fixture users trust that transcription, which a reader checks against D46 (A1).

`lake test` runs all 25 signed fixtures through `verifyLegacySpend` with `coreVerifier` and each record's flags.
It compares both the Boolean verdict and the ScriptError name against Core's recorded values.
The oracle and live Core also compare all 25 records through `script.verify_legacy` with the transaction checker.
These checks cover the three 2-of-3 signer pairs, the recovery branch and every recorded mutation.
They provide finite comparison evidence, without a theorem about all signed spends.

Both programs could be wrong in the same way on an input that the comparison does not send.

The five header PoW operations are IO-adapter entry points into the existing specification definitions.
Their JSON conversion and Lean diagnostic strings have no refinement theorem.
The Core harness transcribes the two version branches for `block.check_version` and all seven checks for `block.contextual_check`.
The latter transcription follows D33, lines 3066 to 3119, and calls Core helpers for each compared value.
Users trust that transcription and the harness's construction of `mapBlockIndex` and `fCheckpointsEnabled` (D67, D69).
Its `LogPrintStr` replacement writes errors to standard error and does not replace any consensus predicate.

The build disables SSE2, and its stamp records the generic scrypt variant and configure options.
The comparison still assumes Core's little-endian header memory layout and arithmetic shift of signed versions.
The contextual operation checks `ContextualCheckBlockHeader` on the stated input domain.
The caller supplies the predecessor view, adjusted time and known checkpoint state.
Neither program checks the node-state conditions in `AcceptBlockHeader` or full-block validity.

Any later foreign boundary, such as a C or Rust binding, is listed here with its size and its error handling.

### B5. Compiler substitutions in this repository

`@[implemented_by]` and `@[extern]` make the compiled code run something other than the definition, with no proof that the two agree.
`@[csimp]` replaces a function with one proved equal to it, so it adds no logical trust. The code that runs is still not the definition a reader reads.

The `DogeLib`, `Proofs` and `Refinement` libraries have no `@[extern]`, `@[implemented_by]` or `@[csimp]` declarations, by `lake exe check-decls`.
Their safe declarations depend on at most `propext`, `Classical.choice` and `Quot.sound`.
The fixtures in `scripts/CheckDeclsTest` contain them on purpose, to test the check, and no library imports them.

| Declaration | Kind | Proof-backed | Justification |
| --- | --- | --- | --- |

### B6. Extraction and the Rust toolchain

A refinement theorem about extracted Rust is about the Lean model that Charon and Aeneas produce.
It trusts the extraction, any manually modeled dependency, and the Rust compiler and runtime.
The extracted model is an implementation artifact.
It never becomes the specification.

`Refinement/Rust/src/lib.rs` implements the bounded CompactSize reader.
Charon and Aeneas at the pins in SOURCES.md produce `Refinement/Refinement/Rust/Generated/DogelibCompactsize.lean`.
`Refinement/Rust/regenerate.sh --check` compares a fresh extraction with the committed model.
The refinement theorem is about that Lean model, not a proof of the extractors or compiled Rust.
The Rust compiler, standard-library models, extraction tools and runtime remain trusted.

The native example `Refinement/Rust/examples/compactsize_oracle.rs` calls the public Rust reader through a JSON Lines adapter.
`scripts/compare_core.py --rust-compactsize PATH` compares it with the oracle and Core at the pinned revision.
The three programs agree on 404 CompactSize reads: seven existing fixtures and 397 generated boundary, truncation, non-canonical and suffix cases.
The comparison preserves errors, values, consumed counts and remainders on these inputs.

The comparison provides evidence about the compiled binary on these inputs.
No theorem covers the compiled binary or its JSON adapter.
The adapter's `serde_json` development dependency remains outside the extracted library model.

Aeneas represents each input byte with an eight-bit vector and each decoded value with a 64-bit vector.
The abstraction maps those vectors directly to Lean `UInt8` and `UInt64`.
Aeneas slices carry a proof that their length fits Rust `usize`.
This length bound limits the input representation, not the acceptance behavior of the reader.

Rust usize is modeled through Lean core's opaque platform word size.
The refinement holds on both 32- and 64-bit platforms.
The proof does not case on that word size, and it assumes neither 32 nor 64 separately.

## Gap C: is the proof itself sound?

### C1. The Lean kernel and its axioms

Every theorem trusts the Lean kernel, and whichever of the three standard axioms it uses: `propext`, `Classical.choice` and `Quot.sound`.
Those three are the allowed set. A theorem may use fewer.

`lake exe check-decls` checks the transitive axiom dependencies of safe declarations under `DogeLib` and `Refinement`, including private proof bodies.
It rejects `sorryAx` even when an unfinished proof comes from an imported module outside that scope.
Unsafe declarations are reported separately.
Detection does not require attribution to a declaration that uses the axiom directly.
It does not check the kernel, and it does not show that the axioms are consistent.

The named platform-size exception permits exactly `System.Platform.getNumBits` as a reachable opaque from `Refinement` modules.
This Lean core parameter supplies the word size of Rust `usize`.
The exception does not permit an opaque declaration in either library, another reachable opaque, or this parameter in a `DogeLib` specification definition.
The self-test rejects those cases, imported Aeneas axioms and native proofs.
The allowed axioms remain the same three standard axioms.

Aeneas and Mathlib belong only to the separate refinement package and remain outside the checked module namespaces.
The checker still follows their transitive axiom dependencies at each in-scope use.

### C2. Tactics that trust compiled code

`native_decide`, `bv_decide` and `decide +native` each add an axiom that trusts the compiled code.
A proof that uses one is no longer checked by the kernel alone.
It also trusts every `@[implemented_by]` and `@[extern]` that the compiled code reaches (B2).

CONTRIBUTING.md does not allow these tactics (*Proofs*).
btc-verified allows the axioms that `bv_decide` records, and its `CompactSize.decode_encode` and `encode_head` use `bv_decide`.
A proof adopted from btc-verified has those steps replaced by proofs the kernel checks alone (design record 0002, section 5).
In `DogeLib.Serialization.Proofs.CompactSize`, `toUInt8_lt_fd` and `toUInt8_ne_zero` replace them.

No theorem in the `DogeLib`, `Proofs` and `Refinement` libraries uses them, by `lake exe check-decls`.
The fixtures in `scripts/CheckDeclsTest` use them on purpose.

### C3. Declarations the kernel did not check

A metaprogram can add a declaration to the environment without the kernel checking it.
An independent checker that replays the environment, such as `lean4checker`, would catch it, but none runs yet.

The default declaration check loads `DogeLib`, `DogeLib.Proofs`, `DogeLib.Exports` and `Refinement` with their private proof bodies.
It requires every `.lean` source under `DogeLib/` and `Refinement/Refinement/`, plus their library roots, to appear in that imported environment.
An unreachable module fails the check, including a leaf omitted from its layer root.
This reachability check does not replay kernel checks or detect a metaprogram that bypassed them.
The default imports, checked namespaces and file inventory include the extracted model and its proof.

The default check fails if the separate refinement package is missing, unbuilt or cannot load every requested module.
`--skip-refinement` checks only DogeLib and prints `Refinement NOT checked` in the summary.
Production CI never uses this flag.

## Gap D: does the use of DogeLib hold together?

### D1. Misuse by a client

A correct definition gives a wrong answer when a client calls it outside its input domain.
A prefix decoder returns a remainder, and a client that ignores it accepts trailing bytes.
Each public operation documents its input domain, its failure behavior and whether it consumes the whole input.

`contextualCheckBlockHeader` has three inputs that only the caller can make correct: the adjusted time, the last known checkpoint and the view of the header's chain.
No theorem says that a caller supplies the values that a node would compute.
A client that passes another chain, a stale time or a checkpoint that its block index does not hold gets the result for those inputs.
[Contextual header validation](#contextual-header-validation) describes each input.

### D2. Dependency changes

A change to a pinned dependency can change a definition or a proof that DogeLib relies on.
`SOURCES.md` records the pins, and a pin changes only in a reviewed change of its own.
The root DogeLib package has no Lake dependencies.
The separate package under `Refinement/` requires DogeLib and the pinned Aeneas backend, which brings Mathlib.
[ARCHITECTURE.md](ARCHITECTURE.md#lake-libraries) explains the import boundaries, and [BUILDING.md](BUILDING.md#build-and-check) gives the build sequence.

### D3. Wrong fixtures

A fixture with a wrong expected value makes a wrong implementation pass.
Each fixture records its provenance, and a test runner compares results with the committed expectations rather than overwriting them.
A fixture can also carry generated inputs.
The Script corpus's transaction bytes come from a transcription of Core's test builders, which [B4](#b4-the-oracle-and-foreign-boundaries) states.
