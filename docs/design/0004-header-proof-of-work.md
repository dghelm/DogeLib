# Header proof of work

**Status:** Proposed.
The maintainer decides on adoption.
Until then, this record sets no scope.

**Date:** 2026-11-06
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [architecture](../../ARCHITECTURE.md), [oracle contract](../oracle.md) and [design record 0003](0003-legacy-spend-validation.md).

## 1. Purpose and boundary

This record proposes the scope for an executable specification of Dogecoin's proof-of-work check of a block header.
That check is `CheckAuxPowProofOfWork` [C7].
It covers both kinds of header that Core accepts:

- A header without AuxPoW: its own scrypt digest must satisfy its compact target.
- A header with AuxPoW: a parent block header carries the work, and an AuxPoW payload connects the parent to this header.

The specification has four parts:

- The scrypt-1024-1-1-256 digest of an 80-byte pure header, with its HMAC-SHA256 and PBKDF2 dependencies.
- The AuxPoW payload: its serialization, the coinbase and chain Merkle branches, the merged-mining marker search, the chain ID test and the expected-index computation.
- The version bits: the AuxPoW flag, the chain ID and the legacy versions.
- The composition of these parts with the existing compact-target check `Work.checkProofOfWork`.

DogeLib already specifies the 80-byte pure header, its double SHA-256 hash, the AuxPoW flag test and the compact-target check for a supplied hash.
[SOUNDNESS.md](../../SOUNDNESS.md#target-validity-and-supplied-hash-proof-of-work) states that no theorem establishes the scrypt digest, AuxPoW validity or contextual header validity.
This record proposes how to close the first two of those gaps.
The theorems in section 8 are targets, not implemented results.

The record excludes these checks:

- The contextual checks of `ContextualCheckBlockHeader` against chain history: `nBits` against `GetNextWorkRequired`, the time checks, the checkpoints and the rejection of outdated versions [C8].
  Section 9 proposes one exception, the two version-gating checks, as an option for the maintainer.
- Block validity: the transaction Merkle root of the block, the coinbase rules and every other check of `CheckBlock`.
- Chain selection, chain work and block-index state.
- The framing of the P2P `headers` message, and storage on disk.
- Any security claim about merged mining, such as the uniqueness of work across chains.
- Implementation refinement and Rust extraction.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The line ranges identify the inspected source for each contract:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [pureheader.h, lines 23–155](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.h#L23-L155) | `VERSION_AUXPOW`, `VERSION_CHAIN_START`, the six fields, `GetBaseVersion`, `GetChainId`, `IsAuxpow` and `IsLegacy`. |
| C2 | [pureheader.cpp, lines 13–30](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.cpp#L13-L30) | `SetBaseVersion`, `GetHash` and `GetPoWHash`. |
| C3 | [block.h, lines 23–48](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/block.h#L23-L48) | `CBlockHeader` serialization: the AuxPoW payload follows the pure header exactly when the flag is set. |
| C4 | [auxpow.h, lines 23–183](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/auxpow.h#L23-L183) | The marker `pchMergedMiningHeader`, the serialization of `CMerkleTx` and `CAuxPow`, and `getParentBlockPoWHash`. |
| C5 | [auxpow.cpp, lines 80–161](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/auxpow.cpp#L80-L161) | `CAuxPow::check`. |
| C6 | [auxpow.cpp, lines 163–206](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/auxpow.cpp#L163-L206) | `getExpectedIndex` and `CheckMerkleBranch`. |
| C7 | [dogecoin.cpp, lines 89–125](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp#L89-L125) | `CheckAuxPowProofOfWork`. |
| C8 | [validation.cpp, lines 2927–2937](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L2927-L2937), [lines 3066–3090](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3066-L3090), [lines 3205–3239](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3205-L3239) | `CheckBlockHeader`, the start of `ContextualCheckBlockHeader`, and their order in `AcceptBlockHeader`. |
| C9 | [validation.cpp, lines 1170–1218](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1170-L1218) | Block and header reads from disk, with the proof-of-work check. |
| C10 | [chainparams.cpp, lines 120–141](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L120-L141), [lines 276–306](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L276-L306), [lines 417–437](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L417-L437) | AuxPoW parameters and their records on mainnet, testnet and regtest. |
| C11 | [chainparams.cpp, lines 180–205](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L180-L205) | Mainnet checkpoints. |
| C12 | [consensus/params.h, lines 79–88](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/params.h#L79-L88) | `nAuxpowChainId`, `fStrictChainId`, `fAllowLegacyBlocks` and `nHeightEffective`. |
| C13 | [scrypt.cpp, lines 64–218](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.cpp#L64-L218), [lines 259–264](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.cpp#L259-L264), [scrypt.h, lines 15–37](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/scrypt.h#L15-L37) | `PBKDF2_SHA256`, `xor_salsa8`, `scrypt_1024_1_1_256_sp_generic` and the variant selection. |
| C14 | [hmac_sha256.cpp, lines 9–34](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/crypto/hmac_sha256.cpp#L9-L34) | `CHMAC_SHA256`, including the key digest for keys longer than 64 bytes. |
| C15 | [configure.ac, lines 210–214](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/configure.ac#L210-L214), [lines 793–795](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/configure.ac#L793-L795), [init.cpp, lines 1254–1258](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/init.cpp#L1254-L1258) | The SSE2 scrypt variant: off by default, selected at build time and detected at start-up. |
| C16 | [transaction.h, lines 210–272](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/transaction.h#L210-L272), [serialize.h, lines 676–692](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/serialize.h#L676-L692) | The transaction reader and writer with their witness flag, and the vector reader. |
| C17 | [net.cpp, lines 696–698](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net.cpp#L696-L698), [net_processing.cpp, lines 1551–1553](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L1551-L1553), [lines 2397–2408](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L2397-L2408), [lines 2547–2550](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L2547-L2550), [line 2878](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/net_processing.cpp#L2878), [version.h, lines 14–17](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/version.h#L14-L17), [clientversion.h, lines 55–59](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/clientversion.h#L55-L59) | The stream versions of the network and disk readers. |
| C18 | [chain.cpp, lines 14–36](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp#L14-L36), [rpc/blockchain.cpp, lines 726–731](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/rpc/blockchain.cpp#L726-L731) | `CBlockIndex::GetBlockHeader` and the raw form of `getblockheader`. |
| C19 | [hash.h, lines 80–89](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/hash.h#L80-L89) | `Hash` of two byte ranges: double SHA-256 of their concatenation. |
| C20 | [scrypt_tests.cpp, lines 14–37](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/scrypt_tests.cpp#L14-L37) | Five headers and their scrypt digests. |
| C21 | [auxpow_tests.cpp, lines 113–323](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/auxpow_tests.cpp#L113-L323), [lines 334–451](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/auxpow_tests.cpp#L334-L451) | `check_auxpow`, which builds its cases deterministically, and `auxpow_pow`, which mines at run time. |

The record also cites these documents outside Core:

| Reference | Document | Subject |
| --- | --- | --- |
| X1 | [RFC 7914](https://www.rfc-editor.org/rfc/rfc7914), sections 3–6 and 8–12 | Salsa20/8 core, scryptBlockMix, scryptROMix, scrypt and their test vectors. |
| X2 | [RFC 2104](https://www.rfc-editor.org/rfc/rfc2104) and [FIPS 198-1](https://csrc.nist.gov/pubs/fips/198-1/final) | HMAC. |
| X3 | [RFC 4231](https://www.rfc-editor.org/rfc/rfc4231) | HMAC-SHA-256 test cases, including keys longer than the block. |
| X4 | [RFC 8018](https://www.rfc-editor.org/rfc/rfc8018), section 5.2 | PBKDF2. |
| X5 | S1 in [SOURCES.md](../../SOURCES.md), N3337 [expr.shift] 5.8 paragraph 3 | Right shift of a negative signed value is implementation-defined. |

The registry records none of C1 to C21 or X1 to X5 yet, except S1, which X5 extends to another paragraph.
An implementation lane adds the identifiers it uses to [SOURCES.md](../../SOURCES.md), without a change to any pin.
The findings come from source inspection, without a Core comparison run.

At the pin, no parameter named `nAuxpowStartHeight` exists.
AuxPoW activation is the `fAllowLegacyBlocks` field of the record that `GetConsensus` selects for a height [C10, C12].
That field is false from height 371,337 on mainnet, 158,100 on testnet and 20 on regtest [C10].

## 3. Contract for implementation

### The predicate

The central operation is a Boolean function of a full header and an explicit parameter record.
It follows `CheckAuxPowProofOfWork` [C7].
The full header is a pure header and an optional AuxPoW payload, as in `CBlockHeader` [C3].
The check reads three fields of the record: `nAuxpowChainId`, `fStrictChainId` and `powLimit`.
The existing `Work.checkProofOfWork` reads only `powLimit` of its parameter record.

The function returns `true` exactly when Core's function returns `true`.
A Lean diagnostic names the first check that fails, in Core's order.
That diagnostic helps tests and the oracle, but it is not part of the comparison contract (section 9, decision 6).
Core logs a message for each failure, and `CheckBlockHeader` reports every failure as `high-hash` [C8, lines 2933–2934].

The parameter record is explicit, so the function claims nothing about which record a caller should supply.
`CheckBlockHeader` supplies the height-zero record of the network [C8, line 2933].
Disk reads supply the record of the stored block's height [C9, line 1189].
In each network, every record has the same `nAuxpowChainId`, `fStrictChainId` and `powLimit` [C10].
So both callers give the same result for the same header.
A lane must prove this agreement for each network from the existing records, not assume it.

A second function specifies `CheckBlockHeader` with `fCheckPOW` true: the predicate on the height-zero record of a named network.

### The full header reader

The reader decodes the 80-byte pure header with the existing codec.
If the AuxPoW flag (bit 8) is set, it then decodes the payload in this order [C3, C4]:

| Field | Encoding |
| --- | --- |
| `tx` | A transaction, in the read mode that section 4.6 gives. |
| `hashBlock` | 32 bytes. Read, but never checked. |
| `vMerkleBranch` | Core's vector of 32-byte hashes, with a CompactSize count [C16]. |
| `nIndex` | Signed 32-bit little-endian integer. |
| `vChainMerkleBranch` | Core's vector of 32-byte hashes. |
| `nChainIndex` | Signed 32-bit little-endian integer. |
| `parentBlock` | An 80-byte pure header, which never carries a payload. |

If the flag is clear, the reader decodes no payload.
The reader reuses the existing CompactSize, counted-list and transaction readers.
It returns the exact remainder, and it reports truncation in the same way as those readers.

## 4. Core behaviour that the specification must preserve

Each item comes from the pinned source.
The specification must keep each behaviour, and a theorem or a known answer must pin it.

### 4.1 The scrypt digest

1. `GetPoWHash` calls `scrypt_1024_1_1_256` on the memory that starts at `nVersion` [C2, line 28].
   Those 80 bytes equal the serialized header only on a little-endian host with no padding between the six fields [C1, lines 29–34].
   Core does not assert that layout.
   The specification hashes the 80-byte encoding, and section 6 records the layout as an execution assumption of the comparison.
2. The password and the salt are both the 80 header bytes, with N = 1024, r = 1, p = 1 and a 32-byte output [C13, lines 196 and 217].
   PBKDF2 runs with one iteration, once for 128 bytes and once for 32 bytes.
3. The HMAC key has 80 bytes, which is more than the 64-byte block of SHA-256.
   So `CHMAC_SHA256` uses the SHA-256 digest of the header, padded with zeros, as the key [C14, lines 12–18].
4. The 128-byte block becomes 32 words through `le32dec`, and the result returns to bytes through `le32enc` [C13, lines 198–199 and 214–215].
   The index of the second loop is `32 * (X[16] & 1023)`, the low ten bits of the first word of the last 64-byte block [C13, line 207].
   That index is Integerify of RFC 7914 for r = 1 [X1].
5. Core has a generic implementation and an SSE2 implementation.
   The build uses the SSE2 implementation only with `--enable-scrypt-sse2`, which is off by default [C15].
   The specification follows the generic implementation, and the Core harness must build without SSE2 or record which variant it ran.

### 4.2 Version bits

6. `IsAuxpow` tests bit 8 (`VERSION_AUXPOW`) [C1, lines 23 and 129–132].
   DogeLib's `PureBlockHeader.isAuxpow` already implements this test.
7. `GetChainId` is `nVersion >> 16` on a signed 32-bit integer [C1, lines 110–113].
   For a negative version, the result is negative.
   C++11 makes that shift implementation-defined [X5].
   The specification uses the arithmetic shift, and section 6 records it as a compiler assumption.
8. `GetBaseVersion` is `nVersion % 256` with C++ signed remainder, so a negative version gives a remainder of zero or less [C1, lines 92–95].
   No consensus check at the pin reads it.
   The specification needs it only if an oracle operation exposes it.
9. `IsLegacy` is true for version 1, or for version 2 with chain ID zero [C1, lines 150–155].
   Version 2 always has chain ID zero, so the second condition is the same as version 2 alone.

### 4.3 `CheckAuxPowProofOfWork`

10. The checks occur in this order [C7]:
    1. Unless `IsLegacy`, with `fStrictChainId`, the chain ID must equal `nAuxpowChainId` (line 95).
    2. Without a payload, the flag must be clear, and the scrypt digest of the header must satisfy `nBits` (lines 102–110).
    3. With a payload, the flag must be set (line 115).
    4. The scrypt digest of the parent header must satisfy the `nBits` of this header (line 118).
    5. `CAuxPow::check` must accept, with this header's double SHA-256 hash and this header's own chain ID (line 121).
11. The target of the parent's proof of work comes from the `nBits` of the merge-mined header, not from the parent's own `nBits` [C7, line 118].
    The digest is the scrypt digest of all 80 parent bytes, including the parent's `nBits` [C4, lines 179–183, and C2, lines 25–30].
    So the parent's `nBits` selects no target, but a change to it changes the digest and can change the result.
12. The two mismatch rejections, a payload with a clear flag and a set flag without a payload, cannot follow from bytes.
    The reader creates a payload exactly when the flag is set [C3, lines 40–47].
    Core's tests reach the mismatches only through in-memory headers [C21, lines 388–399 and 425–439].
    The specification keeps both rejections, and a theorem shows that decoded headers never reach them.
13. A legacy header skips the chain ID test, but must still satisfy its own scrypt target.
    A header that is not legacy, has no AuxPoW flag and has the correct chain ID also uses its own scrypt digest.

### 4.4 `CAuxPow::check`

14. `nIndex` must be zero [C5, line 84].
    That condition is the only test that the transaction is a coinbase.
    Core does not check that its input spends a null outpoint.
15. With `fStrictChainId`, the parent's chain ID must differ from the chain ID argument [C5, line 87].
    The argument is the merge-mined header's own chain ID, not `nAuxpowChainId` [C7, line 121].
    Testnet has `fStrictChainId` false, so this test never applies there [C10, line 277].
16. The chain branch must have at most 30 hashes [C5, line 90].
    Core checks this before it computes any root.
17. `CheckMerkleBranch` folds a hash along a branch with `Hash`, the double SHA-256 of a 64-byte concatenation [C6, lines 196–204, and C19].
    Bit `k` of the index puts the running hash on the right at step `k`.
    An index of −1 returns the zero hash [C6, lines 194–195].
18. The coinbase branch uses index zero, so the transaction ID stays on the left at every step [C5, line 100].
    The result must equal the parent's `hashMerkleRoot`.
    No check bounds the length of this branch, other than the vector reader [C16].
19. The transaction must have at least one input [C5, lines 105–106].
    The search reads the raw bytes of `vin[0].scriptSig`, not its parsed pushes [C5, line 108].
20. The search looks for the chain root in display order, the reverse of its internal byte order [C5, lines 94–97].
    Both searches return the first occurrence (`std::search`) [C5, lines 113–117].
21. The chain root must occur in the script [C5, lines 119–120].
22. If the marker `fa be 6d 6d` occurs [C4, line 24], two conditions apply [C5, lines 122–130]:
    - No second marker starts at or after the byte that follows the start of the first marker.
    - The first root occurrence starts exactly four bytes after the start of the first marker.
23. If the marker does not occur, the first root occurrence must start at an offset of at most 20 bytes [C5, lines 131–138].
24. At least eight bytes must follow the first root occurrence [C5, lines 143–145].
    The first four bytes, read little-endian, must equal `1u << h`, where `h` is the chain branch length [C5, lines 147–152].
    The next four bytes, read little-endian, are the nonce [C5, lines 154–156].
25. `nChainIndex` must equal `getExpectedIndex(nonce, chainId, h)` [C5, line 157].
    A negative `nChainIndex` never matches, so its zero root from item 17 cannot cause acceptance.
26. `check` does not test the parent's own proof of work, as its comment says [C4, lines 163–166].
    `CheckAuxPowProofOfWork` tests it separately in item 10.

### 4.5 `getExpectedIndex`

27. The computation uses unsigned 32-bit arithmetic modulo 2^32 [C6, lines 181–186]:

    ```text
    rand = nonce
    rand = rand * 1103515245 + 12345
    rand = rand + chainId          (chainId converted modulo 2^32)
    rand = rand * 1103515245 + 12345
    result = rand % (1 << h)
    ```

28. The chain ID is a signed `int`, and the addition converts it modulo 2^32.
    A negative chain ID from item 7 therefore wraps.
29. `1 << h` is a signed `int`.
    Item 16 bounds `h` by 30 before this call, so the shift does not overflow.
    The usual arithmetic conversions make the remainder unsigned, and the result is less than 2^h.
30. The source comment claims that a 64-bit computation gives the same result [C6, lines 173–179].
    Section 8 makes that claim a theorem target, for `h` at most 30.

### 4.6 The read mode of the embedded transaction

31. The transaction reader allows witness data unless the stream version has the bit `SERIALIZE_TRANSACTION_NO_WITNESS`, 0x40000000 [C16, lines 212 and 247].
32. A network message starts with version `INIT_PROTO_VERSION`, 209 [C17, net.cpp line 698].
    Before processing, `ProcessMessages` sets the receive version [C17, net_processing.cpp line 2878].
    After `VERACK`, that version is the minimum of the peer's version and `PROTOCOL_VERSION`, 70015 [C17, net_processing.cpp lines 1551–1553].
    Neither value has the bit.
    So the `headers` and `block` handlers read the embedded transaction with witness data allowed [C17, net_processing.cpp lines 2406 and 2550].
33. The disk reader opens its file with `CLIENT_VERSION` [C9, line 1176].
    That value is the sum of 1,000,000 times the major version and smaller terms [C17, clientversion.h lines 55–59].
    For version 1.14.9, the sum is below 2^30, so it does not have the bit either.
34. `getblockheader` with `verbose` false serializes with `PROTOCOL_VERSION` [C18, rpc/blockchain.cpp lines 728–729].
    For an AuxPoW header, `GetBlockHeader` reads the full header from disk [C18, chain.cpp lines 20–26].
35. The transaction ID excludes witness data, so the read mode does not change the hash that the coinbase branch folds.
    The read mode does change which byte strings decode, and how many bytes the payload consumes.

The source inspection therefore settles the mode for the network, disk and raw RPC paths at the pin: all three allow witness data.
The specification takes the mode as an explicit parameter and uses witness-allowed for the Core paths (section 9, decision 4).

## 5. Implementation stages and exit conditions

### Layering

Scrypt, HMAC-SHA256 and PBKDF2 belong to the `Cryptography` layer.
The full header, the AuxPoW payload and `CheckAuxPowProofOfWork` belong to the `Block` layer.
[ARCHITECTURE.md](../../ARCHITECTURE.md#layers) orders the layers `Base`, `Serialization`, `Cryptography`, `Work`, `Transaction`, `Block`.
Each layer imports only earlier layers.
`Block` therefore imports `Cryptography`, `Work` and `Transaction`, and neither `Work` nor `Transaction` imports `Block`.
The AuxPoW payload needs `Transaction` for the embedded transaction, and the composition needs `Work.checkProofOfWork`.

Each stage adds its proofs under the layer's `Proofs` tree, and its oracle adapter under `Exports`.
The lane that adds the Block definitions updates the `Block` row of ARCHITECTURE.md.

### Stage 0: HMAC-SHA256 and PBKDF2-HMAC-SHA256

This stage is a separate prerequisite lane, in the pattern of the SHA-1 and RIPEMD-160 lanes of design record 0003.
It adds HMAC-SHA256 over the existing SHA-256 [X2], and PBKDF2 with HMAC-SHA256 [X4].
It keeps the key digest for keys longer than 64 bytes [C14].

The stage exits with these results:

- A model of HMAC that follows RFC 2104 and FIPS 198-1, separate from the executable definition.
- A theorem in the form of `hash_eq_spec` that relates the executable HMAC to that model.
- A PBKDF2 model that follows RFC 8018 section 5.2, and the same kind of theorem for every iteration count and output length that the model admits.
- Known answers: every RFC 4231 HMAC-SHA-256 case, including the keys of 131 bytes, and both PBKDF2 cases of RFC 7914 section 11.

### Stage 1: scrypt

The stage adds a general model of scrypt with parameters N, r, p and the output length, following RFC 7914 sections 3 to 6 [X1].
It also adds an executable `scrypt_1024_1_1_256` that follows Core's loops [C13, lines 187–218].
The executable takes exactly 80 bytes, so its type excludes other lengths.

The stage exits with these results:

- A theorem that the executable equals the general model with Core's parameters, for every 80-byte input.
  The parameters are N = 1024, r = 1, p = 1 and 32 output bytes, with the input as password and salt.
- Known answers of RFC 7914 sections 8 to 10 through the model: the Salsa20/8 core, scryptBlockMix and scryptROMix.
- The scrypt case of RFC 7914 section 12 with N = 16, r = 1 and p = 1, through the model.
- The other scrypt cases of RFC 7914 section 12 through the model, if their cost fits the test budget below.
- The five header and digest pairs of C20 through the executable.

The lane reads the RFC errata before it uses a vector, and records the result.

The executable follows Core's word order and index computation (items 2 to 4), so the theorem covers those details.

### Stage 2: the full header codec

The stage adds the AuxPoW payload and the full header, and their reader and encoder (section 3).
The read mode of the embedded transaction is a parameter.

The stage exits with these results:

- A round trip of the encoder and reader in each read mode, under the restrictions below.
- Canonicality over encoder output: the reader accepts the encoding of a full header and returns that header.
  The stage does not claim that each accepted byte string is the encoding of its result.
- A theorem that a decoded header carries a payload exactly when its flag is set (item 12).
- Exact remainder and truncation behaviour, tested at every proper prefix of each fixture.
- Agreement of the encoded pure header with the existing 80-byte codec.

The round trip of the embedded transaction inherits the restrictions of `WitnessTransaction.readAllowWitness_encode`.
Its counts must be within `MAX_SIZE`.
In the witness-allowed mode, the transaction must have witness data, or an input, or no output.
`noInputsExample_not_roundTrip` shows a transaction outside that shape: with no inputs, one output and no witness data, it is not read back.
In the base mode, the round trip applies to the base projection of the transaction, without witness data.
The header theorem also assumes that the payload is present exactly when the flag is set, and that its branch counts are within `MAX_SIZE`.

The reader must keep Core's acceptance of noncanonical witness encodings [C16, lines 214–243].
At the pin, Core's reader has no check for a witness section whose stacks are all empty.
It accepts such an extended encoding, and Core's writer then emits the base form [C16, lines 252–263].
So two byte strings decode to one transaction, with one transaction ID, and the payload lengths differ.
The specification must accept both, and must not reject the extended form to gain a canonicality theorem.

### Stage 3: `CAuxPow::check`

The stage adds `checkMerkleBranch`, `getExpectedIndex`, the marker and root search, and `CAuxPow::check`.
It keeps items 14 to 30.

The stage exits with these results:

- The theorems of section 8 for `getExpectedIndex`, `checkMerkleBranch` and the search.
- The binding theorem of section 8 for an accepted payload.
- Known answers from `check_auxpow` [C21], with inputs that the Core harness records (section 7).
- Boundary cases of the branch: lengths 30 and 31.
- Boundary cases of the search: root offsets 20 and 21 without a marker, a second marker, and a root before the marker.
- Boundary cases of the trailing words: seven and eight trailing bytes, and negative and out-of-range chain indices.

### Stage 4a: `CheckAuxPowProofOfWork` and `CheckBlockHeader`

The stage adds the predicate and `CheckBlockHeader` (section 3).
It composes stage 1, stage 3 and the existing `Work.checkProofOfWork`.

The stage exits with these results:

- The composition theorem of section 8.
- Per network, a theorem that every selected record gives the same result as the height-zero record.
- Known answers through the compiled code for the fixtures of section 7.

### Stage 4b, proposed: version gating

If the maintainer adopts decision 1, this stage adds the two version checks at the start of `ContextualCheckBlockHeader` [C8, lines 3072–3086].
The predicate reads only the version and a caller-selected record.
With `fAllowLegacyBlocks` false, a legacy version is rejected as `late-legacy-block`.
With `fAllowLegacyBlocks` true, a set AuxPoW flag is rejected as `early-auxpow-block`.

This stage closes one specific gap.
A valid AuxPoW header passes `CheckBlockHeader` before activation, because that check reads the height-zero record.
Only the contextual check rejects it [C8].
The stage does not select the record from a height and does not cover the other contextual checks.
Its exit conditions are an exact characterization theorem and known answers at the activation heights of each network.

### Stage 5: oracle and Core comparison

The proposed operations are `scrypt.hash` for 80 bytes, `block.header.read` for a full header, `auxpow.check` and `block.check_pow`.
Each takes exact bytes and an explicit parameter record or network.
Responses give the result and the Lean diagnostic separately, and the comparator never compares the diagnostic.
The comparison outputs differ by operation:

| Operation | Compared outputs |
| --- | --- |
| `scrypt.hash` | The exact 32 digest bytes, in the order that `scrypt_1024_1_1_256` writes them to its output [C13, line 217]. That order is the internal order of `uint256`, which `UintToArith256` reads as little-endian. |
| `block.header.read` | Success or failure, the decoded fields of the pure header and the payload, and the consumed length. |
| `auxpow.check` | The Boolean result of `CAuxPow::check`. |
| `block.check_pow` | The Boolean result of `CheckAuxPowProofOfWork`. |

The C20 digests are written in display order, the reverse of the output order, because the test compares `uint256::ToString` [C20, lines 19 and 31–35].
A fixture importer must reverse them, and the fixture must record that order.

These operations need a new oracle format revision.
The implementer proposes the schemas and the format name in the relevant pull request.
The format change needs the maintainer's approval ([AGENTS.md](../../AGENTS.md#changes-that-need-a-maintainer)).
This record reserves no format name.

The Core harness calls `scrypt_1024_1_1_256_sp_generic`, the `CBlockHeader` reader with the stated stream version, `CAuxPow::check` and `CheckAuxPowProofOfWork`.
It records the Core revision, the build options and the scrypt variant.

The stage exits with fixture checks, comparator self-tests and reproducible differential runs that record both revisions, the selected cases and the random seeds.
The runs include seeded mutations of payload fields, script bytes and version bits.
Any mismatch becomes a minimized regression case before an agreement claim.

### Test cost

Compiled scrypt with N = 1024 and r = 1 needs a 128 KiB scratchpad and about 4,096 Salsa20/8 core calls per digest [C13, lines 201–212].
A pure functional executable may be slower than Core's code by a constant factor.
The proposed `lake test` set has five C20 digests, 20 checkpoint headers with their parent headers and a few hundred headers before AuxPoW.
That is a few hundred digests, and the first lane measures the time and records it.
The RFC 7914 case with N = 1,048,576 needs 1 GiB in the model, so it stays outside `lake test` unless a lane shows an acceptable cost.

Kernel evaluation of scrypt is not a route to any proof in this record.
No theorem may use `decide +kernel` or `native_decide` on a scrypt digest.
The theorems are structural, and the known answers run through compiled code.

## 6. Trust and theorem boundaries

The theorems establish the behaviour of DogeLib's definitions, and their agreement with independent models.
A claim of agreement with Core needs the source review of [SOUNDNESS.md](../../SOUNDNESS.md) and the comparison of stage 5.

The comparison relies on these execution assumptions about Core:

- The host is little-endian, and the six header fields have no padding (item 1).
- The compiler implements a right shift of a negative `int32_t` as an arithmetic shift (item 7).
- The harness runs the generic scrypt, or records that it ran SSE2 and that the two variants agree on the compared inputs (item 5).

The specification makes no cryptographic claim.
A theorem target that says an accepted payload commits to the merge-mined header says what the hashes equal.
It does not say that a different header cannot reach the same hashes.
That claim needs collision resistance of double SHA-256, which needs a separate model (see [ARCHITECTURE.md](../../ARCHITECTURE.md#three-kinds-of-content)).
The record also makes no claim that work cannot be reused across chains, or that two chains cannot use one slot.
The existing kernel, compiler, runtime and source-review gaps remain as [SOUNDNESS.md](../../SOUNDNESS.md) states them.

## 7. Evidence plan

Two kinds of evidence check the code, and the reports keep them apart.

*Independent evidence* comes from a separate standard.
The RFC 4231 and RFC 7914 vectors test the HMAC, PBKDF2 and scrypt models against their standards.
They do not show that the parameters, the input bytes or the byte order match Core.

*Compatibility evidence* comes from Core or from the Dogecoin chain:

| Source | What it pins |
| --- | --- |
| C20 | Five 80-byte headers and their scrypt digests, asserted by Core's test. The input and the digest are both fixed. |
| C21, `check_auxpow` | The Boolean result of `CAuxPow::check` on cases that the test builds without mining. The harness records the built bytes, and the importer takes each expected result from the test's assertion. |
| C21, `auxpow_pow` | Cases that mine a nonce at run time. Only the Core harness can reproduce them, so they are comparison evidence, not fixed known answers. |
| C11 and mainnet headers | Full headers at checkpoint heights from 371,337. The double SHA-256 hash of each pure header must equal its checkpoint, so the chain's acceptance is evidence that Core's check returned `true`. |
| Existing mainnet headers | The 312 headers before AuxPoW in `tests/work/mainnet-headers`. Their scrypt digests must satisfy their own targets. That check is a property check, not a known answer for any digest. |

The fixture of checkpoint headers needs the AuxPoW payload.
The Electrum source of the existing fixtures returns only the 80-byte pure header.
`getblockheader <hash> false` on a synchronized node returns the full header with its payload (item 34).
The record of a dump states the node version, the network, the command and the fetch date.
The fixture records for each header whether its flag is set, because a checkpoint height does not imply an AuxPoW header.
Each parent header can also be checked against its own chain, but that check gives only supporting evidence.

Whatever the source, a test never fetches data or overwrites an expected value.
A value that DogeLib computes is never an expected value for DogeLib.

## 8. Theorem targets

The names below are proposals.
Each theorem states its domain and hypotheses in its doc comment:

| Target | Statement |
| --- | --- |
| HMAC and PBKDF2 agreement | The executable definitions equal the models of X2 and X4 for every key, message, salt, iteration count and output length in the model's domain. |
| `powHash_eq_spec` | For every 80-byte input, the executable scrypt equals the RFC 7914 model with Core's parameters. The input is password and salt, with N = 1024, r = 1, p = 1 and 32 output bytes. |
| `getExpectedIndex_lt` | For every nonce, chain ID and `h` at most 30, the result is less than 2^h. |
| `getExpectedIndex_eq` | The result equals a closed form over natural numbers: the LCG steps modulo 2^32, then the remainder modulo 2^h. |
| `getExpectedIndex_mod64` | For `h` at most 30, the same steps modulo 2^64 give the same result. This states the claim of the source comment [C6, lines 173–176]. |
| `checkMerkleBranch_eq_fold` | The branch computation equals a left fold that chooses the side from the index bits, and the zero hash for index −1. |
| Search characterization | The marker and root conditions of items 20 to 24 hold exactly when the search accepts, stated over byte offsets of the first occurrences. |
| Binding | If `check` accepts, the parent's `hashMerkleRoot` is the index-zero fold of the transaction ID. The script contains the reversed chain root at the stated offset, followed by the size and nonce words. The chain root is the fold of the merge-mined hash at `nChainIndex`, and `nChainIndex` equals the expected index. |
| Codec | A decoded header has a payload exactly when its flag is set. The round trip holds under the restrictions of stage 2. They are counts within `MAX_SIZE`, payload presence equal to the flag, and a transaction condition for each read mode. Canonicality covers encoder output only, and the reader keeps Core's acceptance of noncanonical witness encodings. |
| `checkAuxPowProofOfWork_iff` | The predicate holds exactly when the chain ID condition holds and one of two branches holds. Without a payload, the AuxPoW flag is clear, and the header's own digest satisfies `checkProofOfWork_iff` with the header's `nBits`. With a payload, the flag is set, the parent's digest satisfies `checkProofOfWork_iff` with the merge-mined header's `nBits`, and `check` accepts. |
| Record independence | For each network and every height, the predicate on the selected record equals the predicate on the height-zero record. |

No target assumes collision resistance or another cryptographic property.

## 9. Decisions proposed to the maintainer

**Date:** 2026-11-06. **Decision maker:** Maintainer. Every row is a proposal until the maintainer decides it.

| Number | Topic | Proposal | Status |
| --- | --- | --- | --- |
| 1 | Version gating | Include the legacy and early-AuxPoW checks as a pure predicate of the version and a caller-selected record, as stage 4b. The predicate is small, and it closes the gap of a valid AuxPoW header before activation. Exclude every other contextual check. | Proposed |
| 2 | HMAC-SHA256 and PBKDF2 | A separate prerequisite lane, with independent vectors, review and precise theorem claims, as for SHA-1 and RIPEMD-160. | Proposed |
| 3 | Scrypt model | A general RFC 7914 model with parameters N, r, p and the output length, and a separate executable fixed to Core's parameters, related by `powHash_eq_spec`. | Proposed |
| 4 | Read mode of the embedded transaction | An explicit parameter. The Core paths use witness-allowed, as section 4.6 shows from the source. | Proposed |
| 5 | Fixtures of full AuxPoW headers | A node RPC dump with `getblockheader <hash> false`, recorded with the node version, network, command and date, and checked against the checkpoint hashes. The maintainer chooses the source. | Proposed |
| 6 | Oracle comparison | Compare the outputs of each operation as stage 5 lists them. For `scrypt.hash`, they are the exact digest bytes in output order. Expose the first failing check as a Lean diagnostic that the comparator does not compare. | Proposed |
| 7 | Oracle format | The implementer proposes the schemas and the format name in the stage 5 pull request. The format change needs the maintainer's approval. | Proposed |
| 8 | Rust work | Implementation refinement and Rust extraction stay outside this scope. | Proposed |

## 10. Remaining risks

| Risk | Mitigation |
| --- | --- |
| The Core harness builds the SSE2 scrypt variant, so a comparison does not test the generic code that the specification follows. | The harness builds without `--enable-scrypt-sse2` and records its build options [C15]. A run that uses SSE2 says so in its report. |
| A byte-order mistake in the chain-root search: internal order instead of display order, or a reversed size or nonce word. | Known answers from `check_auxpow` with both orders, a theorem that states the reversal, and mutations that reverse the root in the Core comparison. |
| The first-occurrence semantics of `std::search` become "any occurrence" in the specification. | The search characterization theorem uses first occurrences, and the `check_auxpow` cases with two roots pin the order [C21, lines 266–292]. |
| The embedded transaction decodes in the wrong mode, so a payload with witness data is rejected or consumes a different length. | An explicit mode parameter, fixtures in both modes, and a Core comparison with the stream version of section 4.6. |
| The specification takes the parent's target from the parent's `nBits`, or omits the parent's `nBits` from the digest input. | The composition theorem names the merge-mined header's `nBits` as the target and the 80 parent bytes as the digest input. Mutations of the parent's `nBits` recompute the parent digest and check it against the unchanged target of the merge-mined header, in Lean and in Core. Mutations of the merge-mined header's `nBits` change the target. |
| A record-selection mistake: a caller uses a record of the wrong network. | The predicate takes the record explicitly, and the record-independence theorem covers the heights within each network. |
| Test time of scrypt in `lake test`. | The cost budget of section 5, with the time measured and recorded by the first lane. |

There is no pin change, trust-policy exception, public API implementation or fixture-format change in this record.
Adoption of the scope does not establish any target theorem, and it does not authorize the merge of a later implementation.
