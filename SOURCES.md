# Sources

This file is the single source registry ([CONTRIBUTING.md](CONTRIBUTING.md#sources-of-truth)). Module references and fixtures cite these pins. A pin change requires a review of the affected definitions, fixtures, and coverage claims in the same change or an explicitly linked series.

## Reference pins

| Repository | Commit | Label | Role | Adopted |
| --- | --- | --- | --- | --- |
| [Dogecoin Core](https://github.com/dogecoin/dogecoin) | `e0a1c157791544e818c901bd9341896965afbf9d` | `v1.14.9` | Compatibility target for the selected functions and modes | Proposed |
| [EthLib](https://github.com/ethereum/EthLib) | `6a93711e7cc062e787fff6747e4101a141d38b7a` | — | Model project: architecture, proof policy, writing standard, SHA-256, declaration check | Adopted |
| [btc-verified](https://github.com/ProofOfKeags/btc-verified) | `ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce` | — | Codecs, byte representations and packed refinements. Its Apache 2.0 licence is in `LICENSES/btc-verified-Apache-2.0.txt`. | Adopted |
| [Charon](https://github.com/AeneasVerif/charon) / [Aeneas](https://github.com/AeneasVerif/aeneas) | Not selected | — | Rust extraction and refinement | Not selected |
| [Lean 4](https://github.com/leanprover/lean4) | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `v4.35.0` | Toolchain, pinned in `lean-toolchain` | Adopted |

Design records 0001 and 0002 cite EthLib at `5d4b584`. The pin above is two commits later and uses the same toolchain, `v4.35.0`. The two commits add the SHA-256 precompile and the rule against every tactic that trusts compiled code. `WRITING.md` and `scripts/check_writing.py` are adapted from this pin.

*Proposed* means recorded in the design records and not yet built against. A pin becomes *Adopted* when a merged lane builds or compares against it.

The Dogecoin pin is a compatibility target for the operations DogeLib models. It is not a claim that every rule in that version is formalized, or that one version is enough evidence for historical consensus.

Keep these concepts separate:

- **Reference software revision:** the exact source used to investigate an operation.
- **Protocol context:** the network, branch, activation state, and historical era in which a rule applies.
- **Implemented coverage:** the operations and input domains actually modeled.
- **Proposed revision:** behavior intentionally different from the baseline.

## Reference identifiers

Design records and module documentation cite these identifiers.

| ID | Source |
| --- | --- |
| D1 | [Dogecoin serialization: CompactSize reader/writer, `MAX_SIZE`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/serialize.h) |
| D2 | [Dogecoin signature-hash tests: historical helper, randomized comparison, fixtures](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/sighash_tests.cpp) |
| D3 | [Dogecoin Script interpreter: signature serializer, legacy `SignatureHash`, checker wrapper](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp) |
| D4 | [Dogecoin transaction types and serialization: base and optional witness modes](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/transaction.h) |
| D5 | [Dogecoin bundled public-key parser: accepted point encodings](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/secp256k1/src/eckey_impl.h) |
| D6 | [Dogecoin difficulty: `CalculateDogecoinNextWorkRequired`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp) |
| D7 | [Dogecoin difficulty tests: DigiShield rounding regression](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/dogecoin_tests.cpp) |
| D8 | [Dogecoin hashing: `CHash256`, `CHashWriter`, `SerializeHash`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/hash.h) |
| D9 | [Dogecoin chain parameters: genesis blocks and their asserted hashes](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp) |
| D10 | [Dogecoin pure block header: fields, serialization order, `GetHash`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/primitives/pureheader.h) |
| D11 | [Dogecoin 256-bit values: `GetHex` display order](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/uint256.cpp) |
| E1 | [EthLib build definition](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/lakefile.lean) |
| E2 | [EthLib architecture](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/ARCHITECTURE.md) |
| E3 | [EthLib contribution policy](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/CONTRIBUTING.md) |
| E4 | [EthLib soundness documentation](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/SOUNDNESS.md) |
| E5 | [EthLib SHA-256 proof](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/EthLib/Cryptography/Proofs/Hash/Sha256.lean) |
| E6 | [EthLib point encoding](https://github.com/ethereum/EthLib/blob/6a93711e7cc062e787fff6747e4101a141d38b7a/EthLib/Cryptography/Secp256k1/Encoding.lean) |
| B1 | [btc-verified packed serialization](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/README.md) |
| B2 | [btc-verified codec class, pairs, transport and little-endian integers](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/Codec.lean) |
| B3 | [btc-verified packed codec class and agreement laws](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Packed/Codec.lean) |
| B4 | [btc-verified `ByteSlice` reader operations and lemmas](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteSlice.lean) |
| B5 | [btc-verified `ByteArray.toList` lemmas](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Ext/ByteArray.lean) |
| B6 | [btc-verified width casts](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/BtcVerified/Serialize/WidthCast.lean) |
| B7 | [btc-verified licence, Apache 2.0](https://github.com/ProofOfKeags/btc-verified/blob/ecf4f0d2c5ab4df84f2595ca60ba2e1fd62d1bce/LICENSE) |
| R1 | [Aeneas documentation](https://github.com/AeneasVerif/aeneas) (for discovery only: pin a revision before use) |

## Operation-to-source mapping

One row per public operation. Add rows in sorted order by operation name.

| Operation | DogeLib declaration | Source (ID, file, function) | Mode / context | Notes |
| --- | --- | --- | --- | --- |
| Byte slice reads | `ByteSlice.toList`, `ByteSlice.take`, `ByteSlice.drop`, `ByteSlice.uncons` | B4, `BtcVerified/Ext/ByteSlice.lean`, the same four functions | No Dogecoin context | Over core's `Std.Data.ByteSlice`. Lemmas in `DogeLib.Base.Proofs.ByteSlice`, and `ByteArray.toList` lemmas from B5. |
| Codec composition | `DogeLib.Serialization.instCodecProd`, `DogeLib.Serialization.Codec.ofEquiv` | B2, `BtcVerified/Serialize/Codec.lean`, `instCodecProd` and `Codec.ofEquiv` | No Dogecoin context | Laws in `DogeLib.Serialization.Proofs.Codec`. `Codec.ofEquiv` takes two functions instead of a Mathlib `Equiv`. |
| Double SHA-256 | `DogeLib.Cryptography.Hash.Sha256d.hash` | D8, `src/hash.h`, `CHash256::Finalize` | Messages of whole bytes | The digest is in SHA-256 output order. Display order (D11) is not defined here. |
| Fixed-width little-endian integers | `DogeLib.Serialization.instCodecUInt8` to `instCodecUInt64`, `bitVecCodecLE` | B2, `BtcVerified/Serialize/Codec.lean`, `instCodecUInt8` to `instCodecUInt64`, `bitVecCodecLE`. D1, `ser_writedata8` to `ser_writedata64` and `ser_readdata8` to `ser_readdata64` | All modes | Core writes these integers with `htole16`, `htole32` and `htole64`, and reads them with `le16toh`, `le32toh` and `le64toh`. The little-endian byte order follows D1 by reading. `lake test` checks it on genesis fields from D9. No Core comparison exists yet. |
| Packed codec composition | `DogeLib.Serialization.instPackedCodecProd`, `DogeLib.Serialization.PackedCodec.ofEquiv` | B3, `BtcVerified/Packed/Codec.lean`, `instPackedCodecProd` and `PackedCodec.ofEquiv` | No Dogecoin context | Agreement laws in `DogeLib.Serialization.Proofs.PackedCodec` |
| Packed fixed-width little-endian integers | `DogeLib.Serialization.instPackedCodecUInt8` to `instPackedCodecUInt64`, `packedBitVecLE` | B3, `BtcVerified/Packed/Codec.lean`, `instPackedCodecUInt8` to `instPackedCodecUInt64`, `packedBitVecLE` | All modes | Agreement laws in `DogeLib.Serialization.Proofs.PackedCodec` |
| SHA-256 | `DogeLib.Cryptography.Hash.Sha256.hash` | FIPS 180-4 §6.2. Code adapted from EthLib `EthLib/Cryptography/Hash/Sha256.lean` at `6a93711` | Messages of whole bytes | Primitive, no Dogecoin context. Primitive, no Dogecoin context. |

## Known differences

Differences between DogeLib's targets and related upstream definitions. DogeLib expects these differences and handles them by design.

| Subject | Difference | Handling |
| --- | --- | --- |
| CompactSize decoding | btc-verified accepts every canonical `UInt64`. Core `v1.14.9` also rejects values above `MAX_SIZE = 0x02000000`. Input `fe 01 00 00 02` separates them. | Separate bounded reader. See ROADMAP.md, milestone A. |
| Public-key encodings | EthLib accepts compressed and uncompressed keys. Dogecoin's bundled parser also handles hybrid encodings under applicable checks. | Review acceptance wrappers independently (D5, E6) |
| Transaction dispatch | btc-verified's top-level `Tx` models Bitcoin's witness-aware dispatch. DogeLib's first parser is base/no-witness. | Reuse from `TxBody` components, not `Tx` |

## Unresolved discrepancies

Disagreements between sources, each with a minimal reproducer. Do not normalize a discrepancy away ([CONTRIBUTING.md](CONTRIBUTING.md#sources-of-truth)).

| ID | Sources | Reproducer | Status |
| --- | --- | --- | --- |
