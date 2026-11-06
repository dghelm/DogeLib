# Reuse of HMAC, PBKDF2 and scrypt work for design record 0004

**Date:** 2026-11-06
**Companion:** [design record 0004](../design/0004-header-proof-of-work.md), *Header proof of work*, stages 0 and 1.

This assessment answers one question for the lanes of design record 0004.
How much of the existing Lean work on HMAC, PBKDF2 and scrypt can DogeLib adapt, and what must DogeLib still write and prove?

## Summary

DogeLib can adapt the HMAC, PBKDF2 and scrypt definitions of `pyca/verified-garbage` as its models, with small changes.
Those files import only Lean core, build on DogeLib's toolchain, and use only the standard axioms.
Their proofs mostly relate the definitions to a machine model of memory, so DogeLib can reuse only a few lemmas.
EthLib supplies an executable HMAC-SHA-256 over `ByteArray`, written over the same SHA-256 that DogeLib adapted.
EthLib has no separate HMAC model, and its pinned commit in [SOURCES.md](../../SOURCES.md) has no HMAC.
A separate lane, `build/ethlib-pin-update`, moves that pin to a commit with HMAC.

DogeLib must still write these parts:

- An executable PBKDF2 and an executable `scrypt_1024_1_1_256` that follows Dogecoin Core's loops.
- Every theorem that relates an executable to its model, including `powHash_eq_spec`.
- The known answers through compiled code.

One part of the plan needs a maintainer, because it adds a pin to [SOURCES.md](../../SOURCES.md).
The [last section](#decisions-for-the-maintainer) states it.
The assessment recommends that DogeLib takes VG's material under BSD-3-Clause.

## Sources and method

The assessment reads these revisions:

| Key | Project | Revision | Licence |
| --- | --- | --- | --- |
| VG | [`pyca/verified-garbage`](https://github.com/pyca/verified-garbage/tree/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e) | `28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e` | Apache-2.0 OR BSD-3-Clause |
| EL | [EthLib](https://github.com/ethereum/EthLib/tree/bb6dfe55198243682bc2eaf94611af2dbce1be6f) | `bb6dfe55198243682bc2eaf94611af2dbce1be6f` | CC0 1.0 |
| Core | [Dogecoin Core](https://github.com/dogecoin/dogecoin/tree/e0a1c157791544e818c901bd9341896965afbf9d) | `e0a1c157791544e818c901bd9341896965afbf9d` | MIT, except `src/crypto/scrypt.cpp`, which is BSD-2-Clause |

EL `bb6dfe5` is the EthLib commit that the lane `build/ethlib-pin-update` makes the single EthLib pin.
EthLib added the two HMAC files at `4971b5a`, after the current pin `6a93711` in [SOURCES.md](../../SOURCES.md).
The last change to them is `1ce8b89`, which rewrites the proof file.
Both files and `Hash/Sha256.lean` are the same at `1ce8b89` and `bb6dfe5`.

VG paths below are relative to `lean/VerifiedGarbage/`.
Line numbers refer to the revisions in the table.

The author checked these facts with a build:

- The VG files `TCB/Mem.lean`, `Spec/Sha256.lean`, `Spec/Sha1.lean`, `Spec/Md5.lean`, `Spec/Sha512.lean`, `Spec/Hmac.lean`, `Spec/Pbkdf2.lean`, `Spec/Scrypt.lean` and `Proof/Scrypt/BlockMix.lean` build unchanged in a Lake project with no dependencies, on Lean `v4.35.0`.
- `#print axioms` reports `[propext, Quot.sound]` for `Hmac.hmac`, `Pbkdf2.pbkdf2HmacSha256`, `Scrypt.salsa`, `Scrypt.blockMix`, `Scrypt.roMix`, `Scrypt.scrypt`, `blockMix_eq` and `yAt_length`.
- A text search finds no `sorry`, `native_decide`, `bv_decide`, `implemented_by`, `extern` or `csimp` in the copied files.
  The same search over all of `Proof/Scrypt/`, `Proof/Hmac/` and `Proof/Pbkdf2/` finds no `native_decide` or `bv_decide`.
- The sequential-fill lemma of [ROMix](#romix-the-reference-fill-and-the-sequential-fill) checks against VG's `blockMix`, with the same two axioms.

The build did not cover the other VG proof files, which import VG's proof framework.
The assessment makes no axiom claim about them.
It did not build EthLib's HMAC files or run any known answer.

## Component inventory

| Component | VG definition | VG theorems at the level of the definitions | EthLib | Dogecoin Core |
| --- | --- | --- | --- | --- |
| HMAC | [`Spec/Hmac.lean`][vg-hmac], lines 27–55: `HashFunction`, `blockKey`, `hmacBlockKey`, `hmac`, `sha256` | [`Proof/Pbkdf2/Hmac.lean`][vg-proof-pbkdf2-hmac]: `hash96` and `hmac_step`, for a 64-byte key block and a 32-byte message, over VG's SHA-256. [`Proof/Pbkdf2/MdKeys.lean`][vg-proof-mdkeys]: `blockKey_short`, `xorPad_short`. The other files in `Proof/Hmac/` are about machine memory. | [`Hash/Hmac.lean`][el-hmac], lines 33–48: executable `blockKey`, `xorPad`, `hmac`. [Proofs][el-hmac-proof], lines 27–83: tag size, key block, pads. | [`hmac_sha256.cpp`][core-hmac], lines 9–34 |
| PBKDF2 | [`Spec/Pbkdf2.lean`][vg-pbkdf2], lines 23–55: `int`, `xorBytes`, `iterate`, `F`, `pbkdf2`, `pbkdf2HmacSha256` | [`Proof/Pbkdf2/Whole/Common.lean`][vg-proof-pbkdf2-whole], lines 30–75: `G`, `G_succ`, `G_zero`, `lt_nb`, `ol_le`, `nb_lt`, `nb_zero`, `done_nb`, `pbkdf2_eq`. [`Proof/Pbkdf2/Memory.lean`][vg-proof-pbkdf2-memory]: `xorBytes_length`, `iterate_congr`. | None | [`scrypt.cpp`][core-scrypt], `PBKDF2_SHA256` from line 69 |
| Salsa20/8 core | [`Spec/Scrypt.lean`][vg-scrypt], lines 35–74: `step`, `doubleRound`, `core`, `wordLE`, `serialize`, `salsa` | [`Proof/Scrypt/Spec.lean`][vg-proof-spec] relates words to memory | None | `xor_salsa8`, from line 121 |
| scryptBlockMix | Lines 79–95: `blk`, `blockMixYs`, `blockMix` | [`Proof/Scrypt/BlockMix.lean`][vg-proof-blockmix]: `yAt`, `blockMix_eq`, `salsa_length`, `yAt_length` | None | Lines 203–204 and 210–211 for r = 1 |
| scryptROMix | Lines 100–133: `leNat`, `integerify`, `mixLoop`, `roMixAux`, `roMix`, `roMixIndices` | [`Proof/Scrypt/RoMix.lean`][vg-proof-romix]: `vList_getD`, `mixLoop_succ_fst`, `blockMix_length`, `repeat_blockMix_length`, `leNat_append`. `integerify_mod` is stated over machine memory. | None | `scrypt_1024_1_1_256_sp_generic`, lines 187–218 |
| scrypt | Lines 142–159: `valid`, `scrypt` | [`Proof/Scrypt/Whole.lean`][vg-proof-whole]: `valid_pow`, `valid_r`, `scrypt_eq` | None | Lines 196 and 217 |

VG states each definition over `List Byte`, with `Byte := BitVec 8` ([`TCB/Mem.lean`][vg-mem], line 24) and `Word := BitVec 32`.
These results at the level of the definitions are of two kinds:

- `G`, `G_succ`, `nb_lt`, `pbkdf2_eq` and the other lemmas of `Whole/Common.lean`, lines 30–75, take the pseudorandom function (PRF) as a parameter.
  So they hold for any PRF, including HMAC over DogeLib's SHA-256, and the PBKDF2 lane can adapt them.
  The same file also has `rev_int` and lemmas over machine memory, which DogeLib does not need.
- `hash96` and `hmac_step` restate one HMAC-SHA-256 step as two SHA-256 compressions.
  They hold only for a 64-byte key block and a 32-byte message, and they unfold VG's SHA-256 (`compress`, `compressList`).
  With DogeLib's SHA-256 as the hash instance, they do not apply directly.
  They are a guide if a lane later writes a PBKDF2 executable that keeps the two key states, as Core does.
  `MdStep.lean` states the same step for any Merkle–Damgård hash in VG's streaming framework, which DogeLib does not adopt.

VG's own known answers run at elaboration time in `VerifiedGarbageTest/`.
They read vendored RFC files and are not theorems.
For scrypt they evaluate RFC 7914 sections 8 to 10 and the section 12 case with N = 16.

## Trust policy

VG's specification files meet the trust policy of [CONTRIBUTING.md](../../CONTRIBUTING.md#proofs), by the build and the search above.
VG's own policy is close to DogeLib's.
Its `lean/README.md` says that the emitter rejects `sorry`, `native_decide` and every non-standard axiom in its artifacts.
The emitter also rejects `implemented_by`, `extern` and `export` in the code that it runs, and `csimp` anywhere in the project.
DogeLib does not rely on VG's checks.
`lake exe check-decls` checks each adapted declaration again.

One VG proof outside the build uses `bv_omega`, in `Proof/Scrypt/RoMix.lean`, line 82.
`bv_omega` reduces bit vectors to natural numbers and calls `omega`, so it does not trust compiled code.
That lemma is about machine addresses, and DogeLib does not need it.

EthLib's HMAC proofs use only elementary tactics, such as `rw`, `simp`, `omega` and `by_cases`.
DogeLib's proof policy comes from EthLib's, and `lake exe check-decls` checks each adapted declaration.

VG trusts its `Spec/` files by review: no theorem relates them to the RFCs.
A DogeLib model adapted from them has the same status as any DogeLib model.
The RFC known answers and the Core comparison of record 0004 are its evidence.

## Representation and adaptation route

### The two representations

The models and the executables use different types:

| Part | VG | DogeLib |
| --- | --- | --- |
| Byte | `BitVec 8` | `UInt8`, in `ByteArray` |
| Byte string | `List (BitVec 8)` | `ByteArray`. The header codec returns `List UInt8`. |
| 32-bit word | `BitVec 32` | `UInt32` in executables. The SHA-256 model in `Proofs` uses `BitVec 32`. |
| SHA-256 | `VG.Spec.Sha256.hash` over lists | `Sha256.hash` over `ByteArray`, with `hash_eq_spec` for messages shorter than 2^61 bytes |

Record 0004 sets a rule for adaptation, in stage 0.
If an adaptation changes the representation of a definition, the same change proves the new definition equivalent to the source definition.

### Recommended route

1. Adapt VG's HMAC, PBKDF2 and scrypt definitions as DogeLib's models with their types unchanged.
   The changes are the namespace, the doc comments and the hash instance below.
   Each definition keeps `List (BitVec 8)` and `BitVec 32`.
   So the rule above adds no obligation to prove equivalence with the source.
2. Do not adapt VG's SHA-256.
   VG's `HashFunction` takes the hash as a parameter, so the HMAC model can use DogeLib's SHA-256.
   Define the instance as DogeLib's SHA-256 with a conversion between `List (BitVec 8)` and `ByteArray`.
   A second SHA-256 model would need its own proof of agreement with DogeLib's model.
   Record 0004 does not need that proof.
3. Write the executables over `ByteArray`, `UInt8` and `UInt32`.
   The HMAC executable is EthLib's, and the PBKDF2 and scrypt executables are new.
4. Prove each executable equal to its model in the form of `hash_eq_spec`.
   Each of these theorems crosses the representation once, and record 0004 requires them in any case.

The other routes cost more:

- A model restated over `UInt8` changes the representation.
  The rule above then requires a copy of VG's definitions and a proof of equivalence, for no gain in the final theorems.
- A Lake dependency on VG breaks the rule that the root package has no Lake dependencies, from [AGENTS.md](../../AGENTS.md#checks).
  VG also brings Mathlib and its machine models, which DogeLib does not want.
- VG's list definitions would be slow as the executable.
  For N = 1024, the VG reference ROMix applies scryptBlockMix about 525,000 times.

### Obligations per component

**HMAC.**
State the model with its hash as a parameter, as VG's `HashFunction` does.
Then prove `hmac_eq_spec` in two steps:

1. The executable equals the model instantiated with DogeLib's executable SHA-256, for every key and message.
   This step needs `ByteArray` and list conversions, and EthLib's `blockKey_of_le`, `blockKey_of_lt` and `xorPad_getElem`.
2. A corollary replaces the executable SHA-256 by the FIPS 180-4 model through `hash_eq_spec`.
   It needs the bound of `hash_eq_spec` on each SHA-256 input.
   The inner input has `64 + message.size` bytes, and the outer input has 96 bytes.
   A key longer than 64 bytes is also hashed, so the key needs the same bound.

The two models agree with Core on long keys.
Core hashes a key longer than 64 bytes and pads the digest with zeros ([`hmac_sha256.cpp`][core-hmac], lines 12–18).
VG's `blockKey` hashes a key when `64 < key.length`, and EthLib's `blockKey` does the same.

**PBKDF2.**
VG's `pbkdf2` returns `none` when `dkLen` exceeds `(2^32 - 1) * hLen`, and it is total elsewhere.

For an iteration count of zero, VG's `F` returns `U₁`.
Core does the same, because its inner loop runs for `j` from 2 to `c`.
RFC 8018 requires a positive count, so the theorem can state its domain as `0 < c` or keep the zero case.

The executable needs no streaming SHA-256, because DogeLib's SHA-256 takes the whole message.
The theorem covers every salt, iteration count and admitted `dkLen`.
It needs an induction over the blocks `T_i` and an induction over `iterate`.
VG's `G_succ` and `pbkdf2_eq` give the first, and `iterate_congr` replaces the PRF inside `iterate`.

**Salsa20/8 core.**
Core's `xor_salsa8(B, Bx)` first sets `B` to `B xor Bx`.
It then applies four double rounds to a copy, and adds the copy to `B` word by word.
VG's `salsa (xorBytes x y)` describes the same computation over bytes, with `wordLE` and `serialize` as the little-endian conversions.
The obligations are these:

- Each of the 32 steps in `UInt32` equals VG's `step` through `UInt32.toBitVec`, as `smallSigma0_toBitVec` does for SHA-256.
- The executable runs the steps in the order of VG's `doubleRound`, which is the order of RFC 7914 section 3.
  A reviewer compares this order with Core's loop, from line 142.
- The words that `le32dec` reads and `le32enc` writes equal `wordLE` and `serialize`.

**scryptBlockMix with r = 1.**
For r = 1, VG's `blockMix` returns `Y[0] ‖ Y[1]`, and the even and odd shuffle changes nothing.
Core computes `Y[0]` in `X[0..15]` and `Y[1]` in `X[16..31]` (lines 203–204).
VG's `blockMix_eq` already states `blockMix` as `Y[0]` followed by `Y[1]`.
DogeLib can adapt it with `yAt`.

**scryptROMix.**
The [next section](#romix-the-reference-fill-and-the-sequential-fill) gives the fill.

The second loop needs one more lemma: for r = 1, `integerify 1 x % 1024` equals the low ten bits of the first word of the last 64-byte block.
Core computes that value as `X[16] & 1023` (line 207).
VG's `leNat_append` gives the split of the integer.
VG's `integerify_mod` states the same fact over machine memory, so DogeLib restates it over lists.

VG's `mixLoop` reads `V[j]` with `List.getD`, and the executable reads an array.
Each index is less than 1024, so the default value never occurs.

**scrypt.**
`valid 1024 1 1 32` is a closed proposition, so `decide` proves it in the kernel.
That proof evaluates no digest, so it respects the rule of record 0004 against kernel evaluation of scrypt.
For p = 1, the model splits the 128 PBKDF2 bytes into one block, which is all of them.
`powHash_eq_spec` then composes the PBKDF2 theorem twice with the ROMix theorem.

## ROMix: the reference fill and the sequential fill

VG fills `V` in a way that costs quadratic time.
[`Spec/Scrypt.lean`][vg-scrypt-romix], line 123, defines `V[i]` as `Nat.repeat (blockMix r) i b` for each `i` on its own.
Line 124 starts the second loop from `Nat.repeat (blockMix r) N b`.
RFC 7914 section 5 gives the same values with one application of scryptBlockMix for each `i`.
Core does the same in its first loop (lines 201–205): it stores `X` in `V[i]`, then replaces `X` by its scryptBlockMix.

VG proves the sequential fill only inside each machine proof.
For example, the loop invariant of [`Proof/Scrypt/AArch64/RoMixCT.lean`][vg-romixct], lines 513–514, states it.
No VG lemma states the fill at the level of the definitions.

DogeLib keeps VG's quadratic definition as the model, and adds a sequential fill to the executable.
This split matches [CONTRIBUTING.md](../../CONTRIBUTING.md#optimizations-and-protocol-revisions).
The sketch below is the lemma that relates the two fills.
It checks against VG's `blockMix` on Lean `v4.35.0`, with the axioms `propext` and `Quot.sound` only:

```lean
/-- `f` applied `i + 1` times is `f` applied `i` times after one first application. -/
theorem repeat_succ' {α : Type} (f : α → α) :
    ∀ (i : Nat) (x : α), Nat.repeat f (i + 1) x = Nat.repeat f i (f x)
  | 0, _ => rfl
  | i + 1, x => by
    show f (Nat.repeat f (i + 1) x) = f (Nat.repeat f i (f x))
    rw [repeat_succ' f i x]

/-- Core's first loop: store `X` in `V[i]`, then replace `X` by `f X`. -/
def fillLoop {α : Type} (f : α → α) : Nat → α → Array α → Array α × α
  | 0, x, v => (v, x)
  | n + 1, x, v => fillLoop f n (f x) (v.push x)

theorem fillLoop_eq {α : Type} (f : α → α) : ∀ (n : Nat) (x : α) (v : Array α),
    fillLoop f n x v =
      ((v.toList ++ (List.range n).map fun i => Nat.repeat f i x).toArray, Nat.repeat f n x)
  | 0, x, v => by simp [fillLoop, Nat.repeat]
  | n + 1, x, v => by
    rw [fillLoop, fillLoop_eq f n (f x) (v.push x), repeat_succ']
    simp only [Array.toList_push, List.append_assoc, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.singleton_append, Nat.repeat]
    congr 3
    exact congrArg (x :: ·) (List.map_congr_left fun i _ => (repeat_succ' f i x).symm)

/-- The sequential fill gives the blocks and the final `X` of step 2 of scryptROMix. -/
theorem fill_eq_spec (r N : Nat) (b : List VG.Byte) :
    fillLoop (Scrypt.blockMix r) N b #[] =
      (((List.range N).map fun i => Nat.repeat (Scrypt.blockMix r) i b).toArray,
        Nat.repeat (Scrypt.blockMix r) N b) := by
  rw [fillLoop_eq]; simp
```

The executable stores words, not lists of bytes.
The ROMix lemma therefore composes `fill_eq_spec` with the word conversion and the BlockMix lemma of the previous section.

## Dogecoin specialization

`GetPoWHash` hashes the 80 bytes that start at `nVersion` ([`pureheader.cpp`][core-pureheader], line 28).
Core calls `scrypt_1024_1_1_256` with those bytes as password and salt, with N = 1024, r = 1, p = 1 and 32 output bytes.
The calls are in [`scrypt.cpp`][core-scrypt-generic], lines 196 and 217.
These facts connect VG's model to the Dogecoin digest:

1. **Input.**
   `Codec.encode h` gives the 80 header bytes, and `PureBlockHeader.encode_length` proves the length.
   The executable takes exactly 80 bytes, as record 0004 requires, for example as a `ByteArray` with a size proof.
   The model receives the same bytes as a list of `BitVec 8`.
   Record 0004, section 6, records the layout of Core's memory as an execution assumption.
2. **Parameters.**
   `powHash_eq_spec` states that `scrypt b b 1024 1 1 32 = some (powHash b)` after the byte conversion, for every 80-byte `b`.
   The HMAC key is 80 bytes, so both models hash it first.
3. **Output order.**
   The model returns the bytes of the second PBKDF2 in order.
   Core writes the same bytes to its output buffer at line 217, which is the internal order of `uint256`.
   A `Hash256` built from those bytes in the order of `PureBlockHeader.getHash` keeps that order.
   `checkProofOfWork` then reads it as `UintToArith256` does, as a little-endian integer.
4. **Words.**
   Core reads the 128 PBKDF2 bytes as 32 little-endian words with `le32dec`, and writes them back with `le32enc` (lines 198–199 and 214–215).
   VG's `wordLE` and `serialize` are the same conversions, 64 bytes at a time.

## Material that DogeLib does not adopt

DogeLib does not adopt these parts of VG:

- `TCB/`, which holds the instruction-set models, encoders and emitter that VG trusts.
- `Impl/`, `Artifacts/` and every proof under a target directory such as `Proof/Scrypt/X86_64/`.
- The contracts in `Spec/Scrypt/Contract.lean` and `Spec/Hmac/Generic.lean`, and the lemmas over `Mem` and `Addr`.
- The generated Rust crates and the Rust API.

These parts prove facts about assembly under VG's machine models.
DogeLib's executables are Lean code that Lean compiles.
An adoption of VG's assembly would add the machine models, the assembler and the Rust toolchain to the trusted base.
That would change the trust policy in [SOUNDNESS.md](../../SOUNDNESS.md), which only the maintainer can approve.
Record 0004 does not ask for it.

## Licence obligations

VG is available under Apache-2.0 or BSD-3-Clause, at the choice of the recipient.
Its `LICENSE` file says so, and `Cargo.toml`, line 78, states `Apache-2.0 OR BSD-3-Clause`.
Both licences are in the table of [CONTRIBUTING.md](../../CONTRIBUTING.md#material-from-other-projects), so they need no further check.
The adoption must elect one licence and say which.

This assessment recommends BSD-3-Clause, because it adds no requirement for each file:

- Apache-2.0, section 4, requires a notice of change in each modified file and the attributions of any `NOTICE` file.
- BSD-3-Clause has three conditions, in `LICENSE.BSD`, lines 7–16, and a disclaimer in lines 18–27.

The three conditions of BSD-3-Clause apply to DogeLib as follows:

1. A redistribution of source code keeps the copyright notice, the conditions and the disclaimer.
   The notice at the pin is `Copyright (c) Individual contributors`.
   DogeLib keeps a copy of `LICENSE.BSD` in `LICENSES/`, for example as `LICENSES/verified-garbage-BSD-3-Clause.txt`.
2. A redistribution in binary form reproduces the notice, the conditions and the disclaimer in its documentation or other materials.
   The condition applies when DogeLib distributes a binary that contains the adapted code, such as a built oracle executable.
   Such a distribution ships the file in `LICENSES/` with the binary.
3. The third condition covers the name of the project and the names of its contributors.
   Without written permission, DogeLib must not use those names to endorse or promote a derived product.
   DogeLib states the source of the material, but it does not present verified-garbage or its contributors as endorsing DogeLib.

VG has no `NOTICE` file at the pin, and the adapted files have no copyright header, so no other notice applies.

The election does not remove DogeLib's own rules in [CONTRIBUTING.md](../../CONTRIBUTING.md#material-from-other-projects).
Each adapted file still names VG, the commit, the licence and the upstream file in its module docstring.
It also states what the adaptation changed.
DogeLib follows these rules for all material from other projects, including CC0 material.

EthLib's files are under CC0 1.0.
An adapted EthLib file names its source commit and states the changes, as `DogeLib/Cryptography/Hash/Sha256.lean` does.

Most of Dogecoin Core is under MIT, but [`src/crypto/scrypt.cpp`][core-scrypt-notice], lines 1–28, has its own BSD-2-Clause notice.
The notice names Colin Percival, ArtForz and pooler.
BSD-2-Clause is in the table of [CONTRIBUTING.md](../../CONTRIBUTING.md#material-from-other-projects).

The scrypt executable follows the loops of that file, and `PBKDF2_SHA256` is in the same file.
If a lane copies or translates code or comments from `scrypt.cpp`, the adapted file keeps that notice, its two conditions and its disclaimer.
The lane also adds the notice to `LICENSES/`, because `LICENSES/dogecoin-core-MIT.txt` does not cover it.
The rule applies to the PBKDF2 lane and to the scrypt lanes.

## Lane plan for stages 0 and 1

The lanes follow the stages of record 0004.
Each size is an estimate of new Lean, without vendored vectors.

| Lane | Base | Content | Estimate |
| --- | --- | --- | --- |
| `feat/hmac-sha256` | `main` | The EthLib executable and its proofs, the VG model with DogeLib's SHA-256, `hmac_eq_spec` and its FIPS corollary, and the seven RFC 4231 HMAC-SHA-256 cases in `lake test` | 250–400 lines. Small. |
| `feat/pbkdf2-hmac-sha256` | `feat/hmac-sha256` | The VG model, a direct executable, `pbkdf2_eq_spec` for every admitted output length, and both RFC 7914 section 11 cases in `lake test`. The case with 80,000 iterations runs through compiled code. | 250–400 lines. Small to medium. |
| `feat/scrypt-model` | `feat/pbkdf2-hmac-sha256` | The VG Salsa20/8 core, scryptBlockMix, scryptROMix and scrypt models, with `blockMix_eq` and the length lemmas. Known answers of RFC 7914 sections 8 to 10 and the section 12 case with N = 16 through the compiled model. The other section 12 cases only if their cost fits the budget. | 300–450 lines. Medium. |
| `proof/scrypt-pow-hash` | `feat/scrypt-model` | `scrypt_1024_1_1_256` over `UInt32` arrays, the Salsa20/8, BlockMix, fill and Integerify lemmas, `powHash_eq_spec`, and the five C20 header digests in `lake test` | 600–900 lines. Large. |

The HMAC lane depends on the pull request of `build/ethlib-pin-update`.
That lane moves the EthLib pin to `bb6dfe5`, and it brings DogeLib's adapted SHA-256 and RIPEMD-160 up to that commit.
EthLib's SHA-256 files changed between `6a93711` and `bb6dfe5`, and EthLib's HMAC is written over the newer SHA-256.

The HMAC lane can take these parts from EthLib directly:

- `blockKey`, `xorPad` and `hmac` from [`Hash/Hmac.lean`][el-hmac], lines 17–48, with the namespace changed.
  The module imports `Sha256`, which DogeLib adapts from EthLib with only a namespace change after the pin update.
- `hmac_size`, `blockKey_of_le`, `blockKey_of_lt`, `blockKey_size`, `blockKey_append_zeros`, `hmac_append_zeros`, `xorPad_size` and `xorPad_getElem` from [the proofs][el-hmac-proof], lines 27–83.

EthLib gives no model separate from the executable and no theorem like `hash_eq_spec` for HMAC.
The VG model and the new theorem supply both.

Each lane reads the RFC errata before it uses a vector, as record 0004 requires.
The scrypt lanes also measure the time of the compiled model and the executable, and record it in the test budget of record 0004.
With the reference fill, the compiled model may be too slow for N = 1024.
The lane then evaluates the model only on the RFC cases.

## Decisions for the maintainer

The plan adds a pin to [SOURCES.md](../../SOURCES.md), so it needs a maintainer under [AGENTS.md](../../AGENTS.md#changes-that-need-a-maintainer):

| Decision | Proposal | Reason |
| --- | --- | --- |
| Add `pyca/verified-garbage` as a source | Pin `28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e`, under BSD-3-Clause | The HMAC, PBKDF2 and scrypt models adapt its `Spec/` files. |

The lane `build/ethlib-pin-update` handles the EthLib pin, so it is not a decision here.

<!-- Links -->

[vg-mem]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/TCB/Mem.lean#L24
[vg-hmac]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Spec/Hmac.lean#L27-L55
[vg-pbkdf2]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Spec/Pbkdf2.lean#L23-L55
[vg-scrypt]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Spec/Scrypt.lean
[vg-scrypt-romix]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Spec/Scrypt.lean#L122-L124
[vg-proof-spec]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Scrypt/Spec.lean
[vg-proof-blockmix]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Scrypt/BlockMix.lean
[vg-proof-romix]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Scrypt/RoMix.lean
[vg-proof-whole]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Scrypt/Whole.lean
[vg-romixct]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Scrypt/AArch64/RoMixCT.lean#L513-L514
[vg-proof-pbkdf2-hmac]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Pbkdf2/Hmac.lean#L43-L65
[vg-proof-mdkeys]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Pbkdf2/MdKeys.lean#L170-L180
[vg-proof-pbkdf2-whole]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Pbkdf2/Whole/Common.lean#L30-L75
[vg-proof-pbkdf2-memory]: https://github.com/pyca/verified-garbage/blob/28428ba6b81bfd8c438b7cdbcab1f8537f6bc13e/lean/VerifiedGarbage/Proof/Pbkdf2/Memory.lean
[el-hmac]: https://github.com/ethereum/EthLib/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Hash/Hmac.lean
[el-hmac-proof]: https://github.com/ethereum/EthLib/blob/bb6dfe55198243682bc2eaf94611af2dbce1be6f/EthLib/Cryptography/Proofs/Hash/Hmac.lean
[core-hmac]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/hmac_sha256.cpp#L9-L34
[core-scrypt]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.cpp
[core-scrypt-generic]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.cpp#L187-L218
[core-scrypt-notice]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.cpp#L1-L28
[core-pureheader]: https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.cpp#L28
