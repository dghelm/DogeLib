# The oracle and its record format

`dogelib-oracle` runs DogeLib's specification on requests from another program, such as a harness that runs Dogecoin Core on the same inputs.
This document defines its record format, `dogelib-oracle/1`.
The oracle supports only this format.

The oracle models Core's serialization, byte-string hashes, scrypt, pure and full headers, AuxPoW, contextual headers, header sequences and work arithmetic.
It also models legacy signature hashes, public-key verification, Script calls, transaction and block checks, block subsidy, version bits and mainnet block validation.
The [operations table](#operations) lists all 36 operations of `dogelib-oracle/1`, and [the proposal executable](#the-proposal-executable) adds revision hooks for proposed changes.
It reads transactions in base mode or with witness data allowed.
The witness operations model a serialization format only.
Segregated witness is not active on Dogecoin at the pin.
`IsWitnessEnabled` returns false, and main and test reject blocks with witness data (SOURCES.md D36).

Its [protocol context](soundness/transactions.md#transactions-the-witness-allowed-format) separates witness script verification from the commitment checks in Core.
Its output describes an operation under supplied flags, without a claim that an input is valid on any network.
In particular, `script.eval` does not check a complete spend.

## Format stability

In 0.x releases, the oracle and its Core harness are development interfaces that evolve with their fixtures and comparator.
A consumer pins a release or commit and uses that release's own oracle, harness and comparison tools.
Other releases and development commits have no compatibility promise.

Within an approved scope, an additive operation needs ordinary independent review, without a separate maintainer decision or a new format name.
A change to the behavior or record shape of an existing operation also needs only ordinary independent review.
Its pull request title has `!`, its commit body ends with a `BREAKING CHANGE:` footer, and the next release notes name it.
Neither kind of change renames the format: it stays `dogelib-oracle/1` through 0.x, because consumers pin a release.

Each release supports one format implementation.
The oracle has no aliases or migration tooling for older interfaces or format names.
Development formats `/2` to `/6` preceded the reset to `dogelib-oracle/1` and are not supported.

The Core compatibility target, theorem weakening or domain reduction, new trust assumptions and changes to agreed protocol semantics remain maintainer-only decisions.
A stability promise for 1.0 is a separate future decision.
See [the maintainer-only rules](../AGENTS.md#changes-that-need-a-maintainer).

## Running it

```bash
lake build dogelib-oracle
.lake/build/bin/dogelib-oracle             # answer requests on standard input
.lake/build/bin/dogelib-oracle --version   # print {"format":"dogelib-oracle/1"}
```

The oracle reads one request per line of standard input and writes one response per line of standard output.
It writes and flushes each response before it reads the next line. So a caller can keep the process open and send one request at a time.

A blank line has no response.
A final line without a newline is answered.
The oracle stops at the end of its input with exit status 0.
A malformed line gets an error response and does not stop the oracle.

## Requests

A request is one JSON object:

```json
{"id": "r1", "op": "compactsize.read", "bytes_hex": "fdfd00aa"}
```

- `op` names the operation. It is required.
- `id` is any JSON value. The response repeats it. It is optional.
- The other fields are the arguments of the operation. A field that the operation does not read is a request error, so that a misspelled argument cannot be ignored.
- A request should not repeat a key. The oracle does not detect a repeated key: Lean core's JSON parser keeps its last value.

Arguments use these types:

| Type | JSON form | Rule |
| --- | --- | --- |
| Bytes | string | Hexadecimal digits, two per byte, in the order Core serializes them. Upper and lower case are accepted. |
| `u32` | number | An integer from 0 to 2^32 − 1. Any notation of an integer value is accepted: `5`, `5.0`, `5e0` and `50e-1` are all 5. `1.5` and `5e-1` are rejected. |
| `u64` | string | Decimal digits, with no sign and no leading zero, for a value from 0 to 2^64 − 1. A string keeps a value above 2^53 exact in every JSON reader. |
| Target magnitude | string | Exactly 64 hexadecimal digits, most significant byte first. Upper and lower case are accepted. The magnitude is a number, separate from hash byte order. |
| Boolean | boolean | Only `true` and `false`. |
| Signed `adjusted_time` | number | An integer from `INT64_MIN` to `INT64_MAX - 7200`, checked exactly without floating-point conversion. |
| Network | string | `mainnet`, `testnet` or `regtest`. |
| Hash type | number | An integer from −2^31 to 2^32 − 1, by the rule of `u32`. The oracle reduces it modulo 2^32, as Core's `int nHashType` becomes the `uint32_t` of the preimage. |

## Responses

A response is one JSON object with an `id` and either `ok` or `error`:

```json
{"id":"r1","ok":{"consumed":3,"rest_hex":"aa","value":"253"}}
{"id":"r2","error":{"kind":"read","reason":"too_large"}}
```

`id` is the request's `id`.
It is `null` when the request has no `id`, or when the line is not a JSON object.

The oracle writes object keys in sorted order, with no spaces.
A caller should still compare responses as JSON values, not as text.

Results use these types:

| Type | JSON form |
| --- | --- |
| Bytes | `<name>_hex`: lowercase hexadecimal, in the order Core serializes them |
| 256-bit hash | Two fields: `<name>_hex` holds the bytes in the order Core serializes and hashes them. `<name>_display` holds them reversed, as Core's `uint256::GetHex` and its RPC print them. |
| `u32`, counts | number |
| `u64` | string of decimal digits |

### Errors

`error.kind` is one of these:

| Kind | Meaning | Other fields |
| --- | --- | --- |
| `adapter` | A Script request fails an adapter bound before execution. | `reason`: `resource_limit`, `input_index_out_of_range` or `context_bounds`. An adapter error is not a Script rejection. |
| `request` | The oracle could not interpret the request. Examples: invalid JSON, an unknown `op`, a missing or unknown argument, or a value out of range. | `message`, free text for a person. It is not part of the format. |
| `read` | The reader of the specification rejects the bytes, as Core's stream would. | `reason`: `truncated` (the input ends early), `non_canonical` (a CompactSize value in a longer form than needed), `too_large` (a CompactSize value above `MAX_SIZE`, `0x02000000`), or `unknown_optional_data` (a transaction flag bit other than bit 0 remains after the input and output lists and any stacks). For `sighash.legacy`, `argument` names the argument that failed. |
| `work_view` | The finite work view cannot supply a result. The view errors describe the adapter, not consensus rejection codes. | `reason`: `height_out_of_range`, `inconsistent_heights`, `missing_ancestor`, `first_height_underflow`, `zero_interval`, `empty_view` or `short_view`. `first_height_underflow` and `zero_interval` are unreachable with these network parameters and checked views. |
| `trailing_bytes` | A transaction or a block was read and bytes remain. | `count`: the number of bytes after the transaction or the block. For `sighash.legacy`, `argument`. |
| `subsidy` | The draw of `block.subsidy` rejected every word that its fuel allows. Core has no such result. | `reason`: `fuel_exhausted`. `index`: the position of the case in `cases`. |

`work_view` errors describe the finite-view adapter in the specification.
They do not describe Core consensus rejection.
The `read` and `trailing_bytes` kinds report serialization errors of the specification.

## Operations

| `op` | Arguments | `ok` fields | Specification |
| --- | --- | --- | --- |
| `auxpow.check` | `bytes_hex`, `mode`, `hash_hex`, `chain_id`, `strict_chain_id` | Boolean `valid`, and Lean-only `diagnostic`, [as below](#header-proof-of-work) | `Block.AuxPow.check`, Core's `CAuxPow::check` |
| `block.check` | `block_hex`, `mode`, `check_pow`, `check_merkle_root` (booleans) | Verdict, `corruption_possible`, `legacy_sigops`, `base_size`, `transactions`, `hash_hex`, `hash_display`, and Lean-only `diagnostic`, [as below](#transaction-and-block-checks) | `Block.decodeComplete`, then `Block.checkBlock` on mainnet, Core's `CheckBlock` |
| `block.check_pow` | `bytes_hex`, `mode`, `network`, `selection_height`, optional `payload_hex` | Boolean `valid`, and Lean-only `diagnostic`, [as below](#header-proof-of-work) | `Block.checkAuxPowProofOfWork`, Core's `CheckAuxPowProofOfWork` |
| `block.check_version` | `bytes_hex` (80 bytes), `network`, `selection_height` | Boolean `valid`, and Lean-only `diagnostic`, [as below](#header-proof-of-work) | `Block.checkVersion`, the two version gates of Core's `ContextualCheckBlockHeader` |
| `block.contextual_check` | `bytes_hex` (80 bytes), `network`, `chain`, `adjusted_time`, `checkpoints_enabled`, `known_checkpoints` | Boolean `valid`, `reject_reason` (null on acceptance), and Lean-only `diagnostic`, [as below](#contextual-header-validation) | `Block.contextualCheckBlockHeader`, Core's `ContextualCheckBlockHeader` |
| `block.contextual_check_body` | `block_hex`, `mode`, `chain` | Boolean `valid`, `reject_reason`, `dos` and `reject_code` (null on acceptance), and Lean-only `diagnostic`, [as below](#contextual-block-body) | `Block.contextualCheckBlockBody`, Core's `ContextualCheckBlock` on mainnet |
| `block.header.read` | `bytes_hex`, `mode` | `header`, `consumed`, `rest_hex`, [as below](#header-proof-of-work) | `Block.BlockHeader.read`, Core's `CBlockHeader` reader |
| `block.header_sequence` | `network`, `mode`, `adjusted_time`, `checkpoints_enabled`, `index`, `failed_blocks`, `headers` | Sequence verdict, added entries and child marks, [as below](#header-sequence-validation) | `Block.processNewBlockHeaders`, Core's `AcceptBlockHeader` sequence |
| `block.subsidy` | `cases`: an array of `height` and `prev_hash_hex` pairs | `subsidies`, and Lean-only `redraws`, [as below](#block-subsidy) | `Block.getDogecoinBlockSubsidy`, Core's `GetDogecoinBlockSubsidy` on mainnet |
| `block.validate` | `mode`, `check_pow`, `check_merkle_root`, `adjusted_time`, `chain`, `bip34_ancestor_hex`, `coins` or `coins_file`, `blocks_hex` or `blocks_file`, optional `version_bits_heights` and `coins_in_memory` | One record for each block, and the digest of the coin set, [as below](#block-validation) | `Block.validateBlock` on mainnet, Core's five validation checks through `ConnectBlock` |
| `block.version_bits_state` | `chain` | `csv` and `segwit`, the version-bits states of the next block, [as below](#version-bits-state) | `Block.versionBitsStateFull`, Core's `VersionBitsState` on mainnet |
| `compactsize.encode` | `value`: `u64` | `bytes_hex` | `CompactSize.encode`, Core's `WriteCompactSize` |
| `compactsize.read` | `bytes_hex` | `value` (`u64`), `consumed`, `rest_hex` | `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check |
| `hash.hash160` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Hash160.hash` |
| `hash.ripemd160` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Ripemd160.hash` |
| `hash.sha1` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Sha1.hash` |
| `header.encode` | `header` | `bytes_hex` | `Codec.encode` for `Block.PureBlockHeader` |
| `header.hash` | `header` | `hash_hex`, `hash_display` | `Block.PureBlockHeader.getHash` |
| `header.read` | `bytes_hex` | `header`, `consumed`, `rest_hex` | `Codec.decode` for `Block.PureBlockHeader` |
| `merkle.compute` | `leaves_hex` | `root_hex`, `root_display`, `mutated` | `Block.computeMerkleRoot` |
| `oracle.version` | none | `format`: `"dogelib-oracle/1"` | none |
| `pubkey.verify` | `pubkey_hex`, `sig_hex`, `digest_hex` | `valid` (boolean) | `Script.coreVerify` |
| `script.eval` | `bytes_hex`, `flags` (`u32`), `stack_hex`, optional `checker` | Evaluation result, [as below](#script-arguments-and-results) | `Script.evalScript`, Core's `EvalScript` in `SIGVERSION_BASE` |
| `script.read_op` | `bytes_hex`, `cursor` (`u32`) | Instruction or read failure with cursor, [as below](#script-arguments-and-results) | `Script.readInstruction`, Core's `CScript::GetOp` |
| `script.verify_legacy` | `tx_hex`, `input_index` (`u32`), `prevout_script_hex`, `flags` (`u32`), `checker` | Spend result, [as below](#legacy-script-verification) | `Script.verifyScript` or `Script.verifyLegacySpend`, Core's `VerifyScript` with no witness |
| `scrypt.hash` | `bytes_hex` (80 bytes) | `digest_hex` (32 bytes in scrypt output order), [as below](#header-proof-of-work) | `Cryptography.Hash.Scrypt.scrypt_1024_1_1_256`, Core's generic scrypt |
| `sighash.legacy` | `tx_hex`, `script_code_hex`, `input_index` (`u32`), `hash_type` | `plan`, `preimage_hex` (for `hash_bytes` only), `digest_hex`, `digest_display` | `tx_hex` is read as by `tx.decode_base`. Then `legacySignatureHashPlan` and `LegacyHashPlan.digest`: Core's `SignatureHash` with `SIGVERSION_BASE` |
| `tx.check` | `tx_hex`, `mode`, `check_duplicate_inputs` (boolean) | Verdict, `legacy_sigops`, `base_size`, and Lean-only `diagnostic`, [as below](#transaction-and-block-checks) | `Transaction.checkTransaction` and `Transaction.getLegacySigOpCount`, Core's `CheckTransaction` and `GetLegacySigOpCount` |
| `tx.decode_base` | `bytes_hex` | `tx`, `serialized_hex`, `txid_hex`, `txid_display` | `Transaction.decodeBaseComplete`: a transaction that is all of the bytes. Then its base serialization and its ID, `Transaction.txid` |
| `tx.decode_witness` | `bytes_hex` | Witness result | `Transaction.decodeAllowWitnessComplete`: the whole input with witness data allowed |
| `tx.read_base` | `bytes_hex` | `tx`, `consumed`, `rest_hex` | `Transaction.readBase`: a transaction at the start of the bytes, as Core reads the next transaction of a stream |
| `tx.read_witness` | `bytes_hex` | Witness result, `consumed`, `rest_hex` | `Transaction.readAllowWitness`: a prefix with witness data allowed |
| `work.calculate_next` | `network`, `selection_height`, `last_height`, `last_time`, `last_bits`, `first_time` | `bits` (`u32`) | `Work.calculateDogecoinNextWorkRequired` with `Work.getConsensus` |
| `work.get_compact` | `value_hex` (target magnitude), `negative` (boolean) | `compact` (`u32`) | `Work.ArithUint256.getCompact` |
| `work.next` | `network`, `chain`, `candidate_time` (`u32`) | `bits` (`u32`) | `Work.nextWorkRequired` |
| `work.set_compact` | `compact` (`u32`) | `value_hex` (target magnitude), `negative`, `overflow` (booleans) | `Work.ArithUint256.setCompact` |

### Public-key verification

`pubkey.verify` returns `{"valid": b}` for Core's `CPubKey(pubkey).Verify(digest, sig)` on a 64-bit build.
`sig_hex` contains the signature without a Script hash-type byte.
The operation accepts Core's lax DER encodings and normalizes high S before verification.
`pubkey_hex` contains a compressed, uncompressed or hybrid key, which must represent a curve point for acceptance.
Malformed key or signature bytes give `valid: false`.

The adapter bounds each key and signature to 1 MiB, with `adapter/resource_limit` above that limit.
`digest_hex` must contain exactly 32 bytes, or the adapter returns a request error.
Those bytes are in `uint256` storage order and pass unchanged to libsecp256k1.
They are not a display-order hash.
The oracle calls `Script.coreVerify`, and the harness calls Core's `CPubKey::Verify`.

### Script arguments and results

`script.read_op` reads from `cursor`, a byte offset between zero and the script length, inclusive.
The cursor can lie inside a push or its length field.
The operation preserves exact instruction bytes, including nonminimal push encodings.
It returns one of these `ok` objects:

```json
{"result":"instruction","opcode":76,"bytes_hex":"4c0107","pushed_hex":"07","cursor":3}
{"result":"at_end","cursor":3}
{"result":"truncated","opcode":77,"part":"length_field","cursor":1}
```

`cursor` is the offset after the call, including on failure.
For a truncated push, `opcode` is the original input byte, although Core leaves its opcode output as `OP_INVALIDOPCODE`.
`part` is `length_field` or `payload`.
A short length field leaves the cursor after the opcode.
A short payload leaves it after the complete length field, or after the opcode for a direct push.
An end cursor stays unchanged.

`script.eval` takes explicit flags and an initial main stack in `stack_hex`, an array of hexadecimal strings, bottom first.
Its optional `checker` is `none` (the default) or `base`.
`none` supplies no checker. `base` supplies `baseChecker`, which returns false for signature, locktime and sequence checks.
A checker value of another type or name is a request error.
It returns one of these `ok` objects:

```json
{"result":"accepted","script_error":"OK","stack_hex":["01",""]}
{"result":"rejected","script_error":"OP_RETURN"}
{"result":"unsupported","reason":"signature_opcode","opcode":172}
{"result":"unsupported","reason":"flags","bits":64}
```

Acceptance means that one `EvalScript` call returned true.
It permits an empty stack or a false top item.
It does not imply `VerifyScript` acceptance, a P2SH result or a valid transaction.
Only acceptance returns the final main stack.
The altstack and other locals reset for every call.

`script_error` follows the script-test spelling of Core's enum, as the shared [error-name table](../harness/core/script_error_names.inc) records.
The names omit `SCRIPT_ERR_`, except that `SCRIPT_ERR_SIG_NULLFAIL` becomes `NULLFAIL`.
The harness compiles the table against every enum position.
`lake test` compares every name with `ScriptError.name`, including the separate `OK` result.

Unsupported capabilities have these fields:

| `reason` | Additional field |
| --- | --- |
| `flags` | `bits`, the unsupported bits as a u32 number |
| `signature_opcode` | `opcode`, the executed opcode byte as a number |
| `check_lock_time_verify`, `check_sequence_verify` | None |

The evaluator determines whether a capability is needed.
With `checker: "none"`, every executed signature opcode is unsupported before its stack checks.
With `checker: "base"`, only unsupported flag bits can produce an unsupported result.
A skipped signature opcode, for example, does not itself cause an unsupported result.
The adapter does not replace caller flags or classify unsupported results as Script rejection.

The Script adapters limit each script to 1,048,576 bytes.
`script.eval` also limits the caller stack to 4,096 items, 1,048,576 bytes per item and 4,194,304 bytes in total.
Hexadecimal strings above twice the byte limit fail before hex decoding.
The total adds half of each item's string length in bytes, rounded down, before that item's hex validation.

These limits apply before evaluation, including when flags are unsupported.
An excessive request returns `error.kind: adapter` and `reason: resource_limit`.
A script of 10,001 bytes within those adapter limits still reaches the specification's `SCRIPT_SIZE` check under supported flags.
JSON parsing and the input line allocation precede these limits.
They bound execution inputs, not transport memory.

### Legacy Script verification

`script.verify_legacy` checks the selected input against a caller-supplied previous-output script.
It does not find that output in a UTXO set or derive flags from a network or activation state.
The request fields are:

| Field | Meaning |
| --- | --- |
| `tx_hex` | The complete base-mode spending transaction, read as by `tx.decode_base` |
| `input_index` | A u32 index below the transaction's input count |
| `prevout_script_hex` | The previous output's exact `scriptPubKey` bytes |
| `flags` | Explicit u32 Script flags |
| `checker` | Required: `base` or `transaction` |

After argument decoding, transaction decoding failures keep `read` or `trailing_bytes`, with `argument: "tx_hex"`.
An index outside the input list gives `adapter/input_index_out_of_range`.
The adapter then requires fewer than 2^32 inputs and outputs, or returns `adapter/context_bounds`.
Core's bounded reader already implies those count bounds, but the adapter checks them explicitly to construct `InputContext`.
Both checkers use these same bounds.

The previous-output script and selected input's `scriptSig` each have the 1 MiB adapter limit.
The previous-output hex limit precedes transaction decoding. The selected scriptSig limit follows the context checks.
Other transaction fields have no additional adapter resource limit.

`base` runs `verifyScript baseChecker` on the input's exact `scriptSig` and the supplied previous-output script.
`transaction` runs `verifyLegacySpend` with the transaction context and `coreVerifier`.
It checks signatures, signature encodings, hashes and transaction lock-time conditions when execution requires them.

The operation returns these `ok` shapes:

```json
{"result":"accepted","script_error":"OK"}
{"result":"rejected","script_error":"EVAL_FALSE"}
{"result":"unsupported","reason":"flags","bits":64}
```

Acceptance is the `VerifyScript` verdict under the supplied context and flags, with P2SH when requested.
It is not full transaction validity.
No response returns an intermediate stack.

For either checker, only `flags` can be unsupported.
An unsupported result is neither a Script rejection nor comparison agreement.

### Hash and block arguments

`hash.ripemd160`, `hash.hash160` and `hash.sha1` take the exact bytes in `bytes_hex`.
They return `digest_hex`, twenty bytes in digest output order, without reversal or a length prefix.
Empty input is allowed.
These operations have no network or activation parameter and make no cryptographic security claim.

`header.read` reads exactly the first 80 bytes as a `CPureBlockHeader`.
It returns `read/truncated` if fewer than 80 bytes are available.
It returns the decoded `header`, `consumed: 80` and the exact `rest_hex` on success.
The header object contains these fields:

| Field | Meaning |
| --- | --- |
| `version` | The raw u32 bits of Core's signed `nVersion` |
| `prev_block_hex`, `prev_block_display` | Previous block hash, in internal and display order |
| `merkle_root_hex`, `merkle_root_display` | Transaction Merkle root, in internal and display order |
| `time`, `bits`, `nonce` | Core's `nTime`, `nBits`, `nNonce`, each a u32 |

`header.encode` and `header.hash` take a `header` object with exactly six fields:
`version`, `prev_block_hex`, `merkle_root_hex`, `time`, `bits` and `nonce`.
`version`, `time`, `bits` and `nonce` are `u32` arguments.
`version` gives the raw bits of Core's signed `nVersion`, so a negative JSON value is a request error.
Both hash strings must contain exactly 32 bytes in internal order.
Display fields are output fields only.
Unknown fields, including fields inside `header`, are request errors.

`header.encode` returns the 80 serialized bytes as `bytes_hex`.
`header.hash` returns their double SHA-256 as `hash_hex` and `hash_display`.
The pure header boundary stays at 80 bytes even when version bit 8 indicates an AuxPoW payload.
The operations neither parse that payload nor compute scrypt or check header validity.

`merkle.compute` takes `leaves_hex`, an array of strings with exactly 32 bytes each, in internal order.
It returns `root_hex`, `root_display` and the boolean `mutated`.
The root is zero for an empty array and equals the leaf for one entry.
Odd levels duplicate the final hash for root computation.
Mutation detection compares equal aligned complete subtrees and excludes synthetic padding.

The array must have at most 2^31 entries.
A larger array is a request error before Merkle computation.
This caller bound avoids counter wrap in Core's final sweep ([D42, `MerkleComputation`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/consensus/merkle.cpp)).
The Lean specification `computeMerkleRoot` has no such bound.
The hash, header and Merkle operations do not check transaction or block validity.
[Transaction and block checks](#transaction-and-block-checks) and [block validation](#block-validation) describe the operations that do.

### Work arguments

`work.calculate_next` takes `u32` fields, except `last_height`, which must be from 0 through 2147483646.
This bound lets Core increment the height within its signed 32-bit domain.
`selection_height` selects Core's network parameter record independently of `last_height`.
The retarget arithmetic uses candidate height `last_height + 1`, `last_time - first_time`, and `last_bits`.
Both times stay within the UInt32 domain of block timestamps.
The adapter exposes no custom parameter record.

`work.next` takes `chain` as a newest-first array of objects with exactly `height`, `time` and `bits`, all `u32` fields.
Each next object represents the preceding block.
Adjacent heights must differ by one, and each height must be below 2147483647.
An empty array represents a null tip and returns compact `powLimit`.
Otherwise, the candidate height selects the network parameters.
`candidate_time` is separate from the chain.

A suffix may stop above genesis if the selected branch needs no earlier entry.
The adapter checks the whole view before it selects a branch, even when a delay would permit minimum difficulty.

```json
{"id":"target","op":"work.set_compact","compact":33587200}
{"id":"target","ok":{"negative":false,"overflow":false,"value_hex":"0000000000000000000000000000000000000000000000000000000000000080"}}
```

The compact is `0x02008000`, Core's encoding of the magnitude `0x80` (D16, line 490).
The `negative` output reports the sign flag, while `value_hex` always holds the unsigned stored magnitude.
Neither compact operation validates a proof-of-work target.
The work operations check no header validity or AuxPoW rule.

### Transaction results

The `tx` object holds every field as it was read:

```json
{"version": 1,
 "inputs": [{"prevout": {"hash_hex": "...", "hash_display": "...", "n": 0},
             "script_sig_hex": "", "sequence": 4294967295}],
 "outputs": [{"value": "5000000000", "script_pubkey_hex": "..."}],
 "lock_time": 0}
```

`version` and `value` are the bits of Core's signed `int32_t` and `int64_t` fields, as unsigned numbers.
`serialized_hex` lets a caller check that the bytes it sent are the bytes the specification writes back.

The *witness result* contains these fields:

| Field | Meaning |
| --- | --- |
| `tx` | The same transaction fields as the base operations |
| `witnesses` | One array per input, in input order. Each array holds the stack items as lowercase hexadecimal strings, in stack order. |
| `has_witness` | Core's `CTransaction::HasWitness`: some input's stack is not empty |
| `serialized_hex` | `WitnessTransaction.encode`, Core's writer with witness data allowed |
| `txid_hex`, `txid_display` | The transaction ID, from the base serialization |
| `wtxid_hex`, `wtxid_display` | `WitnessTransaction.wtxid`, Core's `GetWitnessHash`, in both byte orders |

`witnesses` is always present.
With zero inputs it is `[]`.
In base form it has one empty array per input.

For example, `witnesses: [["", "ab"], []]` means two inputs.
The first input has two stack items, an empty byte string and `ab`.
The second input has an empty stack.
`has_witness` is true in this example.

A stack with one empty item counts as witness data.
A section of empty stacks does not, so the writer uses base serialization and `wtxid` equals `txid`.
Thus `serialized_hex` can differ from the consumed input bytes.
The prefix operation reports consumption of the original input, before that normalization.

After a zero input count, the witness reader reads a flags byte.
Zero flags give no inputs and no outputs, without another output count.
Nonzero flags precede the input and output lists.
Bit 0 requests one stack per input.

The reader checks unknown flag bits after the input and output lists and any stacks, before the lock time.
Thus a list or stack error takes precedence over `unknown_optional_data`.
The complete operation checks for trailing bytes only after a successful read.

`plan` is `fixed_digest` or `hash_bytes`.
`fixed_digest` is Core's early return of the value one, when `input_index` names no input, or names no output under `SIGHASH_SINGLE`.
`hash_bytes` gives the preimage that Core hashes, so that a mismatch can be traced to its first differing byte.
`script_code_hex` is the script code as Core's `SignatureHash` receives it. `SignatureHash` itself leaves out each `OP_CODESEPARATOR`, and so does the specification. The work of Core's callers before that call, such as removing the signature from the script code, is not modeled.

### Header proof of work

Byte strings use serialization order.
`mode` is required and is either `base` or `allow_witness`, including when no payload is present.
The latter uses Core's network stream version without `SERIALIZE_TRANSACTION_NO_WITNESS`.

`scrypt.hash` fixes N = 1024, r = 1, p = 1 and a 32-byte output.
The 80 input bytes serve as both password and salt.
Its output order is the internal order of Core's `uint256`, the reverse of its displayed digest.

`block.header.read` reads a prefix and preserves its remainder.
Its `header` contains `pure`, with the same fields as `header.read`, and `auxpow`, either null or a payload object.
The payload object contains these decoded fields:

- `transaction`: the `tx`, `witnesses`, `has_witness`, `serialized_hex`, `txid_hex`, `txid_display`, `wtxid_hex` and `wtxid_display` fields of `tx.read_witness`.
- `hash_block_hex` and `hash_block_display`: the embedded `hashBlock` in both orders.
- `merkle_branch_hex` and `chain_merkle_branch_hex`: arrays of hashes in internal order.
- `index` and `chain_index`: unsigned `u32` bits of Core's signed indices.
- `parent`: the six pure-header fields, with the same representation as `header.read`.

The transaction result always serializes with witness allowed, even when the reader used base mode.
Thus `serialized_hex` describes the decoded transaction rather than the exact consumed bytes.
The consumed length and remainder still describe the input, including accepted noncanonical empty witness stacks.

`auxpow.check` requires complete serialized payload bytes, without the child header.
`hash_hex` is the 32-byte child block hash in internal order.
`chain_id` is a signed integer from -2147483648 through 2147483647, and `strict_chain_id` is a Boolean.
These parameters are explicit and need not describe a named network.
This operation checks no proof of work.

`block.check_pow` normally requires complete full-header bytes and calls `checkAuxPowProofOfWork` on the selected network record.
`network` is `mainnet`, `testnet` or `regtest`, and `selection_height` ranges from 0 through 2147483647.
Height zero gives the proof-of-work check of `CheckBlockHeader` with `fCheckPOW` true.
The operation does not check the expected difficulty against chain history.

An optional `payload_hex` selects the split-input form of `block.check_pow`.
When that field is present, `bytes_hex` must contain exactly the 80 pure-header bytes.
`payload_hex` is either null or a complete serialized payload in the requested `mode`.
The adapter preserves the pure header's flag and the independently supplied payload presence.

These requests can reach states that no serialized full header can produce.
`checkAuxPowProofOfWork_read` proves that a header returned by `BlockHeader.read` cannot reach either flag/payload mismatch.
The split form exposes the existing in-memory predicate for Core's `auxpow_pow` cases at source lines 394 and 439.

`block.check_version` checks only the two version gates of `ContextualCheckBlockHeader`.
It uses a pure header because neither gate reads the payload.
Its network and height select `fAllowLegacyBlocks`.
The Lean adapter uses `(getContextualParams network height).toVersionGateParams` (D14).

The predicate operations return `diagnostic: null` on acceptance and a Lean error string on rejection.
Parse errors use the existing `read` categories.
The complete-input operations report `trailing_bytes` with the remaining count.

### Contextual header validation

`block.contextual_check` checks the seven conditions of `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
The pure header must contain exactly 80 bytes.
The request supplies these fields:

- `network`: `mainnet`, `testnet` or `regtest`.
- `chain`: the `work.next` entries, newest first, starting at the predecessor.
- `adjusted_time`: an integer from `INT64_MIN` to `INT64_MAX - 7200`.
- `checkpoints_enabled`: a Boolean.
- `known_checkpoints`: an array of heights from the network's checkpoint table (D9, D68).
  Repeated heights have no additional effect.

A height outside that table is a request error, even with checkpoints disabled.
An adjusted time outside the stated range is a request error.
The caller supplies the link from the header to the view, the adjusted time and the known checkpoint state.
The operation cannot check that these inputs match a node's state.
It excludes genesis and does not check proof of work or an AuxPoW payload.

The view must contain `min(11, predecessor height + 1)` entries for the median, plus any ancestors that next-work selection needs.
An empty view returns `work_view` / `empty_view`.
A view too short for the median returns `work_view` / `short_view`.
Other view failures use the `work.next` error reasons, including `missing_ancestor`.
These adapter errors are separate from consensus rejections.

Acceptance returns `valid: true`, `reject_reason: null` and `diagnostic: null`.
Rejection returns `valid: false`, Core's first reject reason and a Lean diagnostic string.
The oracle format stays `dogelib-oracle/1` under the 0.x development policy.

### Header-sequence validation

`block.header_sequence` runs `Block.processNewBlockHeaders` on full headers and a supplied index (design record 0008).
The format remains `dogelib-oracle/1` under the 0.x development policy.
The request has these required fields:

| Field | Meaning |
| --- | --- |
| `network`, `mode` | Network and embedded-transaction read mode, as for `block.check_pow` |
| `adjusted_time` | One signed safe-range value for the whole call |
| `checkpoints_enabled` | Boolean checkpoint option |
| `index` | Array of initial entries, described below |
| `failed_blocks` | Display-order hashes in visit order, each identifying an index entry with `failed_valid` |
| `headers` | Array of hexadecimal full headers, including AuxPoW payloads when flagged |

Each index entry has exactly these fields:

- `header_hex`: exactly 80 pure-header bytes, from which the adapter derives the key.
- `height`: integer from 0 to 2147483646.
- `anchor`: Boolean that cuts the predecessor link.
  Height 0 also has no predecessor.
  Otherwise the predecessor comes from the header's `hashPrevBlock`.
- `failed_valid`, `failed_child`, `scripts_valid`: Boolean node-state flags.
- `chain_work`: exactly 64 hexadecimal digits, most significant digit first, supplied without a full-chain work check.

Duplicate index keys and indices that `checkWellFormed` rejects are request errors.
Each array has at most 4096 members.
Each full header has at most 1 MiB, and their combined bytes have at most 16 MiB.
These adapter limits give request errors and are separate from Core's peer-message limit.
Malformed header bytes give the existing read or trailing-byte errors.
An insufficient anchor view gives `work_view`, and a candidate height at 2147483647 gives a request error.

The result in `ok` has exactly these fields:

| Field | Meaning |
| --- | --- |
| `valid` | Boolean sequence verdict |
| `failed_at` | Zero-based failure position, or null on acceptance |
| `reject_reason`, `dos`, `reject_code` | First Core rejection's reason, score and code, or null on acceptance |
| `last_hash` | Last accepted header's display hash on complete acceptance, or null for an empty call or any rejection |
| `added` | Entries inserted before the first failure, in insertion order: `hash` in display order, `height`, and fixed-width `chain_work` |
| `marked_failed_child` | Sorted display hashes visited by the step-6 marking loop, including flags already set and entries added in the accepted prefix |
| `diagnostic` | Lean-only diagnostic string on rejection, or null on acceptance |

Known headers add no entry and bypass work and contextual checks.
The network genesis hash also bypasses failure flags.
A failed-ancestor rejection retains both prefix insertions and child marks.
The operation permits several branches in one call.

### Transaction and block checks

`tx.check` runs `Transaction.checkTransaction`, Core's `CheckTransaction`, and `block.check` runs `Block.checkBlock`, Core's `CheckBlock` (SOURCES.md D106, design record 0010, stage 0010a).
Neither operation needs a coin, a height or another block.

`tx.check` has three required fields:

- `tx_hex`: a transaction that is all of the bytes.
- `mode`: `"base"` or `"allow_witness"`, the format of `tx_hex`, as for [`block.header.read`](#header-proof-of-work).
  `CheckTransaction` reads no witness stack, so the mode changes only how the bytes are read.
  Base mode reads the ordinary encoding of a transaction with no inputs and some outputs.
  The witness-allowed reader takes the empty input count of that encoding as the marker of the extended format.
- `check_duplicate_inputs`: Core's `fCheckDuplicateInputs`. Core's block and mempool paths pass true.

`block.check` has four required fields:

- `block_hex`: a block that is all of the bytes: a full header, a CompactSize count and the transactions.
- `mode`: the read mode of every transaction, the one in an AuxPoW payload included.
  `"allow_witness"` is the mode of Core's network and disk paths.
- `check_pow`: Core's `fCheckPOW`. With true, `CheckBlockHeader` runs `CheckAuxPowProofOfWork` on the mainnet record of height zero.
- `check_merkle_root`: Core's `fCheckMerkleRoot`.

`block.check` has no network argument, and it covers mainnet only.
With `check_pow` false, no step depends on the network.

```json
{"id":"c1","op":"tx.check","tx_hex":"01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff0151ffffffff010000000000000000015100000000","mode":"base","check_duplicate_inputs":true}
{"id":"c1","ok":{"base_size":62,"diagnostic":"DogeLib.Transaction.CheckTransactionError.coinbaseLength","dos":100,"legacy_sigops":0,"reject_code":16,"reject_reason":"bad-cb-length","valid":false}}
```

The transaction is the record "Coinbase of size 1" of Core's `tx_invalid.json` (D29).

Both results have these fields in `ok`:

| Field | Meaning |
| --- | --- |
| `valid` | Core's return value |
| `reject_reason` | The reject reason of Core's `CValidationState`, or null when `valid` is true |
| `dos` | The denial-of-service score of the state, or null when `valid` is true |
| `reject_code` | The reject code of the state, 16 for `REJECT_INVALID`, or null when `valid` is true |
| `legacy_sigops` | `GetLegacySigOpCount` of the transaction, or the sum over the transactions of the block, modulo `2^32` as Core's `unsigned int` |
| `base_size` | The number of bytes of the base serialization, Core's `GetSerializeSize` with `SERIALIZE_TRANSACTION_NO_WITNESS` |
| `diagnostic` | A Lean diagnostic: the name of the error, with the position of a rejected transaction of a block, or null when `valid` is true. Core does not report it. |

`block.check` adds these fields:

| Field | Meaning |
| --- | --- |
| `corruption_possible` | `CorruptionPossible` of the state: true for `bad-txnmrklroot` and `bad-txns-duplicate`, false for another failure, and null when `valid` is true |
| `transactions` | The number of transactions |
| `hash_hex`, `hash_display` | The block hash, the double SHA-256 of the 80-byte pure header |

`legacy_sigops`, `base_size`, `transactions` and the hash are functions of the decoded bytes.
The result has them for every verdict.

A reader failure is an `error` of kind `read`, and bytes after the transaction or the block give `trailing_bytes`.
In that case no check runs.
A count of transactions above `MAX_SIZE` is `too_large` before any transaction is read.

`CheckBlock` returns true at once for a block whose member `fChecked` is set.
`block.check` is the check of a block with `fChecked` false, which is the state of every block that Core reads into a new object.
The operations do not run `ContextualCheckBlock`, so a block with witness data can be valid here.

### Contextual block body

`block.contextual_check_body` runs `Block.contextualCheckBlockBody`, Core's `ContextualCheckBlock` on mainnet (SOURCES.md D33, design record 0010, stage 0010a).
It checks the finality of every transaction, the BIP34 coinbase height from 1,034,383, the absence of witness data, and the block weight.
It has three required fields:

- `block_hex`: a block that is all of the bytes, read as for `block.check`.
- `mode`: the read mode of every transaction. The recent range reads only in `allow_witness` mode.
- `chain`: a contiguous view from the predecessor, newest first, each entry `{height, time, bits}`.
  It is empty for a block at the genesis position, where Core passes a null predecessor.
  Otherwise it reaches the aligned version-bits boundary and its predecessors, for the boundary's median time.

The candidate height is the predecessor's height plus one.
A predecessor at height 2,147,483,646 or above is a request error in the oracle.
Core can represent the candidate height 2,147,483,647, and the harness accepts a predecessor at 2,147,483,646, so this limit is narrower than Core's domain.
The comparator fails on a request error, so no compared request has such a predecessor.
The body reads the version-bits states of CSV and SegWit only to test whether either is active.
`csv_never_lockedIn` and `segwit_never_active` show that neither is active on a header chain from the mainnet genesis in which every header passed `checkBlockHeader .mainnet`.

Below the first period the aligned boundary is null and both states are `DEFINED`.
Otherwise the boundary's median time selects the case of design record 0010, section 4.
Below the CSV start the state is `DEFINED`, and at or after the CSV timeout the state is `FAILED`.
A boundary in the gap between them, which the window from 2016 to 2017 would reach, is an adapter error outside the comparison domain.
`block.validate` walks that gap ([the CSV window](#the-csv-window)).

The result has `valid`, `reject_reason`, `dos`, `reject_code` and the Lean-only `diagnostic`, as `tx.check` does.
The four reject reasons are `bad-txns-nonfinal` (score 10), `bad-cb-height`, `unexpected-witness` and `bad-blk-weight` (score 100 each), all with `reject_code` 16.
`bad-blk-weight` is reachable because this body has no base-size check.
In `block.validate` of stage 0010b, `CheckBlock` bounds the base size first.
`contextualBody_badBlkWeight_unreachable_after_checkBlock` then shows that the weight check cannot fire, under the hypothesis that the AuxPoW payload transaction has no witness data.

### Block validation

`block.validate` runs `Block.validateBlock` on a range of mainnet blocks (SOURCES.md D33, D110 and D114, design record 0010, stage 0010b).
For each block it runs Core's five checks of a new block in Core's order, and stops at the first failure:

1. `CheckBlockHeader`, when `check_pow` is true.
2. `ContextualCheckBlockHeader`, with checkpoints disabled.
3. `CheckBlock`, with the flags `check_pow` and `check_merkle_root`.
4. `ContextualCheckBlock`.
5. `ConnectBlock`, with `fJustCheck` true and Core's signature check `coreVerifier`.

For the genesis hash, steps 1 and 2 do not run, and `ConnectBlock` adds no coin.
The operation is mainnet only.

The request supplies the state before the first block, and the operation carries it through the range:

- `mode`: the read mode of every block, as for `block.check`.
- `check_pow`, `check_merkle_root`: Booleans. Real blocks set both. A request with changed blocks clears `check_pow`, because a changed block has no valid proof of work.
- `adjusted_time`: the adjusted time of step 2, as for `block.contextual_check`.
- `chain`: the view of the predecessor of the first block, newest first, each entry `{height, time, bits}`, as for `block.contextual_check_body`.
  An entry can also hold the `version` of its header, as an unsigned 32-bit number.
  It is empty exactly when the range starts at the genesis block.
  A block whose aligned version-bits boundary is in the case-3 gap of CSV needs a longer chain (see *The CSV window* below).
  A predecessor at height 2,147,483,646 or above is a request error in both programs, and in the oracle for [`block.contextual_check_body`](#contextual-block-body).
  Core can represent the candidate height 2,147,483,647, so this limit is narrower than Core's domain, and no request compares that height.
- `bip34_ancestor_hex`: the hash of the ancestor at height 1,034,383 of the predecessor, in serialization order, or null when the predecessor is below that height.
  `ConnectBlock` skips the BIP30 test when that hash is `BIP34Hash`, which never happens on mainnet (design record 0010, section 2).
  When the predecessor is at that height, the value must be the previous hash of the first block.
- `coins`: the coin set before the first block.
  Each entry is `{txid_hex, coinbase, height, outputs}`, for one transaction ID, as Core's `CCoins`.
  Each output is `{n, value, script_hex}`, where `n` is the output index, below 1,048,576, and `value` is a string of decimal digits.
  A transaction ID occurs once, and each entry has at least one output.
  A script that Core's `IsUnspendable` rejects is a request error, because such an output never enters Core's set.
- `coins_file`: in the place of `coins`, the path of a coin-set snapshot (see *Coin-set snapshots* below).
  A request has exactly one of the two, and `coins_file` needs `blocks_file`.
- `blocks_hex`: the blocks, each one all of its bytes.
- `blocks_file`: in the place of `blocks_hex`, the path of a file that holds the blocks (see *Blocks from a file* below).
  A request has exactly one of the two.
- `version_bits_heights`: optional, a list of heights in increasing order.
  For the supplied predecessor and for each accepted block at a listed height, the response reports the states of CSV and SegWit for the next block.

A block must extend the state.
The genesis block is valid only as the first block of an empty `chain`.
The previous hash of the first other block names the supplied predecessor.
Each later block must have the hash of the last accepted block as its previous hash.

An accepted block becomes the new predecessor, and its changes enter the coin set.
A rejected block changes nothing.
So a request can hold several candidates for one height: the rejected ones, and then one accepted block.

The result has five fields:

- `blocks`: one record for each block, in order.
- `out_of_domain_at`: null, or the position of the block that ended the range (see *The arithmetic domain* below).
- `set_digest_hex`: the digest of the coin set after the last record.
- `set_coins`: the number of coins in that set.
- `set_value`: the total value of that set (see *Total value* below).

A request with `coins_file` has two more fields: `start_set_digest_hex` and `start_set_coins`, the digest and the number of the coins of the snapshot.
A request with `version_bits_heights` has the field `version_bits_states`: one object `{height, csv, segwit}` for each reported height, in order, with the lowercase names of the states.

#### The CSV window

Between about heights 1.2 million and 1.72 million, a block's aligned version-bits boundary has a median time between the CSV start and timeout.
That is the case-3 gap of design record 0010, section 4, where the shortcut gives no state.
There `block.validate` computes the state of CSV as Core's `GetStateFor` does (design record 0011, stage 4).
It walks back one period at a time from the aligned boundary to the *base*: the latest boundary whose median time is below the CSV start.
Then it folds the step of the walk over the boundaries above the base.
Each has its median time and the number of blocks of its period that signal CSV.
`versionBitsStateFull_of_reset` shows that this fold equals the full walk from the genesis block over the same boundaries.

So the chain of such a request reaches the base and its ten predecessors, and every entry above the base has a version.
Otherwise the request is a request error, in the oracle and in the harness.
On mainnet the base of the whole window is the boundary at 1,189,439.
So the chain of a block near the CSV timeout has about 515,000 entries.
The oracle keeps the state of the last boundary that it walked, so a request walks each boundary once.
SegWit has a timeout of 0, and its shortcut gives its state at every boundary.
The walk can give `ACTIVE` on a made chain that signals, never on mainnet (`csv_never_lockedIn`). A block in that context gets the error `outside_model` with the detail `csv_active`, before its checks, because the context holds the aligned boundary's median time in the place of the predecessor's.
`block.contextual_check_body` still returns the adapter error `{kind: "version_bits", reason: "gap"}` in the gap.

Each record has these fields:

| Field | Value |
| --- | --- |
| `height`, `hash_hex`, `hash_display` | The height of the candidate, and its hash in both byte orders |
| `valid`, `reject_reason`, `dos`, `reject_code` | The verdict of the first failing step, as for `block.check` |
| `changes_digest_hex`, `spent`, `created` | For an accepted block: the digest of its changes, and the numbers of spent and created coins. Null for a rejected block |
| `set_digest_hex` | The digest of the coin set after an accepted block whose height is a multiple of 1,000. Null otherwise, and null in every record of a request with `coins_file` |
| `set_value` | The total value of the same set, exactly where `set_digest_hex` is not null. Null otherwise |
| `diagnostic` | Lean only: the name of the failing step and the Lean error, or null |

`ConnectBlock` adds these reject reasons to those of the four earlier steps: `bad-txns-BIP30`, `bad-txns-inputs-missingorspent`, `bad-txns-premature-spend-of-coinbase`, `bad-txns-inputvalues-outofrange`, `bad-txns-in-belowout`, `bad-blk-sigops`, `bad-cb-amount`, and the two script reasons.
A script reason is `mandatory-script-verify-flag-failed` or `non-mandatory-script-verify-flag`, then a space and the text of Core's `ScriptErrorString` in parentheses.
The non-mandatory reason has score 0 and `reject_code` 64.
`bad-txns-premature-spend-of-coinbase` has score 0.
The other reasons have score 100, and every reason but the non-mandatory one has `reject_code` 16.

#### Digests

Each program computes each digest from its own coin records, with the record format and the order below.
The comparison checks the digests and the counts, not the records.
So equal digests show equal coins only if double SHA-256 is collision resistant, which DogeLib does not model (SOUNDNESS.md, A4 and B4).
A *coin record* is these bytes:

1. One tag byte: 0 for a spent coin, 1 for a created coin, 2 for a member of the whole set.
2. The outpoint: the 32 bytes of the transaction ID, then the output index in 4 little-endian bytes.
3. The height of the coin's transaction in 4 little-endian bytes.
4. One byte: 1 for a coin of a coinbase, and 0 otherwise.
5. The output as Core serializes a `CTxOut`: the amount in 8 little-endian bytes, the CompactSize length of the script, and the script.

A digest starts as 32 zero bytes.
Each record replaces the digest `d` with the double SHA-256 of `d` followed by the record.

- `changes_digest_hex` visits the changes of the block in the order of `UpdateCoins`.
  For each transaction in block order, it takes the coin of each input in input order (tag 0), and then each output that enters the set, in output order (tag 1).
  An unspendable output enters no set and has no record.
  The genesis block has no change, so its digest is 32 zero bytes.
- `set_digest_hex` visits every coin of the set (tag 2).
  The transaction IDs are in the order of their 32 bytes as byte strings, and the outputs of one ID are in index order.

#### Total value

`set_value` is the sum of the amounts of the coins of the set, in koinu, as a string of decimal digits.
The sum can exceed `2^63`, so it is not a JSON number.
The oracle reports `CoinSet.totalValue` of `Block.Coins`, the quantity of `chain_issuance_bound` in `Block.Proofs.ConnectProperties`.

The harness writes it with its own decimal conversion, and the oracle writes an `Int`, which has no bound.
The scripts read `set_value` as a string and convert it with Python's `int`, which has no bound.
The mainnet set exceeds 2^63 - 1, the largest `CAmount`: at height 6,465,793 it holds 15,683,043,286,016,806,072 koinu.
For the harness's 128-bit sum and the comparator's issuance check, see [docs/core-harness.md](core-harness.md#what-the-harness-runs).

#### The arithmetic domain

Core adds `int64_t` amounts in `ConnectBlock` with no earlier range check, and an overflow there is undefined behaviour in C++ (design record 0010, section 3).
`Block.connectBlock` computes in the integers and returns `outOfDomain` when a sum leaves the `int64_t` range.
The oracle then ends the range: `blocks` holds the records before that block, and `out_of_domain_at` is its position.
`connect_fits` gives a condition under which no sum leaves the range.

A supplied `value` above `MAX_MONEY` is the error `{"kind": "block_validate", "reason": "coin_value_out_of_range"}`.

#### Blocks from a file

A request with `blocks_file` names a file in the format of `blocks.bin` of `scripts/fetch_blocks.py`.
For each block the file has the height and the length as 4-byte little-endian integers, and then the bytes of the block.
A relative path starts at the working directory of the program.
Both programs read one record at a time, so the file can be larger than memory.
The state, the checks, the result and the errors are those of a request with `blocks_hex`, and `index` is the position of the record.

The height of each record must be the height of its candidate.
A rejected block changes nothing, so the record after it has the same height.
A length above Core's `MAX_SIZE`, 33,554,432 bytes, is an error.
An empty file gives no block record.

The `dogelib-oracle` executable alone answers such a request, through `Exports.respondIO`.
The function `Exports.respond` reads no file, and returns a request error for the argument.
The executable writes one line to standard error after each accepted block whose height is a multiple of 1,000.

#### Coin-set snapshots

A *snapshot* is a coin set as a file, in the format `dogelib-coins/1` ([design record 0011](design/0011-mainnet-ranges.md), section 3).
A request with `coins_file` names a snapshot as the coin set before its first block.
A relative path starts at the working directory of the program.

**The file.**
A snapshot is the coin records of the whole set under the tag 2, one after the other, in the order of `set_digest_hex` ([digests](#digests)).
The transaction IDs are in the order of their 32 bytes, and the outputs of one ID are in index order.
The file has no header, no count and no other framing.
A record has 50 bytes before the length of its script: the tag, the outpoint, the height, the coinbase byte and the amount.
The CompactSize length of the script and the script follow.
One coin set has exactly one byte sequence as its snapshot.
The digest of the set is the digest chain over the records, in the order of the file.

**The checks.**
Both programs read the records in order, and return an error at the first fault.
`record` in the error is the position of the record, from 0.
For one record, the checks run in the order of this table:

| `reason` | Fault |
| --- | --- |
| `coins_file_truncated` | The file ends inside a record |
| `coins_file_tag` | The tag is not 2 |
| `coins_file_index` | The output index is 1,048,576 or more |
| `coins_file_height` | The height is above 2,147,483,646 |
| `coins_file_coinbase` | The coinbase byte is not 0 or 1 |
| `coins_file_value` | The amount is above `MAX_MONEY` as an unsigned 64-bit number. That includes every negative `int64_t` amount, and the -1 of Core's null output |
| `coins_file_script_length` | The length of the script is not in the shortest CompactSize form |
| `coins_file_script` | Core's `IsUnspendable` rejects the script: it has more than 10,000 bytes, or its first byte is `OP_RETURN`. A reader does not read a script above 10,000 bytes |
| `coins_file_order` | The record is not above the record before it in the order of the set |
| `coins_file_entry` | The record has the transaction ID of the record before it, and another height or coinbase byte |

A file that ends inside the first 50 bytes of a record, inside the length or inside the script is truncated.
So a byte after the last complete record is the error `coins_file_truncated`.
`coins_file_unreadable` is the error of a file that does not open, or of a read that fails.
The limits on the amount, the index, the script and the height are those of the `coins` argument.

**The manifest.**
A manifest is a JSON object that names one snapshot:

| Field | Value |
| --- | --- |
| `format` | `dogelib-coins/1` |
| `height` | The height of the last accepted block |
| `block_hash_hex`, `block_hash_display` | The hash of that block, in both byte orders |
| `coins` | The number of records |
| `set_digest_hex` | The digest of the set |
| `set_value` | The total value of the set, as `set_value` of the result |
| `bytes`, `sha256` | The length and the SHA-256 of the file |

The digest of a coin set does not commit to a block.
So a range from a snapshot needs the manifest: its first block must name `block_hash_hex` as its previous hash, and `scripts/snapshot_range.py` requires that.
The manifests of the snapshots of the recorded runs are in `tests/block/mainnet-blocks/snapshots`.
The snapshot files are not committed and are not release assets.

**The oracle.**
The oracle does not hold the whole set of a snapshot.
Let `T` be the transaction IDs that the blocks of the request name: the ID of each transaction, and the ID in the outpoint of each input.
`Block.Exports.blockValidateSnapshot` works in four steps:

1. It reads the blocks once and collects `T`.
2. It reads the snapshot once. It computes `start_set_digest_hex` over all records, and keeps the coins whose ID is in `T`.
3. It runs the blocks on the kept coins. Before each block, it requires that `T` holds every ID that the block names. A block that names another ID is the error `blocks_file_changed`, which can occur only if the file changes between the two reads.
4. It reads the snapshot again, and computes `set_digest_hex`, `set_coins` and `set_value` of the set after the last record. That set is the records of the file whose ID is not in `T`, merged in order with the entries of the run. A file with another number of records than in step 2 is the error `coins_file_changed`.

The theorem `validateBlock_restrict` is the reason for step 4 ([docs/soundness/blocks.md](soundness/blocks.md#validateblock_restrict-a-block-on-the-coins-that-it-names)).
On a coin set and on its restriction to `T`, `validateBlock` gives the same error, or the same coin changes.
The new set then has the entries of the restricted run at the IDs of `T`, and the entries of the old set at every other ID.
No theorem covers the reads of the two files or the merge of step 4.

The oracle alone takes the optional argument `coins_in_memory`, a Boolean.
With the value true, the oracle keeps every coin of the snapshot and runs the blocks on the whole set.
It computes the last digest from that set, as for a request with `coins`.
That form reads the snapshot once and does not use the merge.
The result has the same fields and, for one request, must have the same values.

`Exports.respondIO` answers a request with `coins_file`, as it answers one with `blocks_file`.
`Exports.respond` returns a request error for the argument.
The executable writes one line to standard error after each read of the snapshot.

#### Errors

A block that does not read gives the `read` or `trailing_bytes` error of `block.check`, with the position of the block as `index`.
The errors of a snapshot are in the table [above](#coin-set-snapshots), and they have `record` in the place of `index`.
The other errors have the kind `block_validate`, a `reason`, and `index` when a block causes them:

| `reason` | Condition |
| --- | --- |
| `coin_value_out_of_range` | A supplied coin has an amount above `MAX_MONEY` |
| `genesis_after_start` | The genesis block is not the first block of an empty chain |
| `no_predecessor` | A block that is not the genesis block has an empty chain |
| `not_linked` | A block does not extend the last accepted block |
| `file_unreadable` | The file of `blocks_file` does not open, or a read of it fails |
| `file_truncated` | The file ends inside the 8 bytes before a block, or inside a block |
| `file_record_too_long` | A record of the file gives a length above 33,554,432 bytes |
| `file_height` | A record of the file gives a height that is not the height of its candidate |
| `blocks_file_changed` | Oracle only, with `coins_file`: a block names a transaction ID that the first read of `blocks_file` did not find |
| `coins_file_changed` | Oracle only: the second read of `coins_file` finds another number of records than the first |
| `snapshot_unwritable` | Harness only: a snapshot file of `snapshot_dir` does not open, or a write of it fails |
| `outside_model` | `validateBlock` returned a result that is not Core's, and `detail` holds the Lean error. The cases are an adapter error of an earlier step, an active CSV state, an unsupported script capability, a subsidy without fuel, and a repeated transaction ID outside a coinbase |

### Block subsidy

`block.subsidy` runs `Block.getDogecoinBlockSubsidy`, Core's `GetDogecoinBlockSubsidy` with the mainnet parameter records (SOURCES.md D104, design record 0010).
It has no network argument, and it covers mainnet only.
The request has one required field, `cases`: an array of at most 65,536 objects.
Each object has exactly these fields:

- `height`: an integer from 0 to 2147483647, Core's `nHeight`.
- `prev_hash_hex`: exactly 32 bytes, the hash of the previous block in internal order.

```json
{"id":"s1","op":"block.subsidy","cases":[{"height":1,"prev_hash_hex":"9156352c1818b32e90c9e792efd6a11a82fe7956a630f03bbee236cedae3911a"},{"height":145000,"prev_hash_hex":"0000000000000000000000000000000000000000000000000000000000000000"}]}
{"id":"s1","ok":{"redraws":[0,null],"subsidies":["6841600000000","25000000000000"]}}
```

The result in `ok` has two arrays, with one entry for each case, in the order of the request:

| Field | Meaning |
| --- | --- |
| `subsidies` | The subsidy in koinu, as a string of decimal digits |
| `redraws` | A Lean diagnostic: the number of words that Boost's draw rejected before it accepted one. It is null from height 145,000, where Core draws no word. Core does not report this number. |

Below height 145,000 the subsidy depends on `prev_hash_hex`, through seven hexadecimal digits of its display form.
From 145,000 it depends on the height alone.
The operation does not check that a hash is the hash of a block, or that a block at the height exists.

More than 65,536 cases, an unknown field, a height outside the range and a hash of another length are request errors.
This adapter limit is not a limit of Core.
The draw of the specification takes fuel, 624 words in the oracle.
If a case rejects that many words, the whole request gets the error kind `subsidy`, with `reason` `fuel_exhausted` and the `index` of the case.
No known request gives that error: a [run outside CI](comparison-evidence.md#block-subsidy-comparison-evidence) covers every seed.

### Version-bits state

`block.version_bits_state` runs `Block.versionBitsStateFull`, Core's `VersionBitsState` (SOURCES.md, D102), with the mainnet parameters of the CSV and SegWit deployments (D100).
It walks every period of the chain from the genesis block, without a supplied boundary state.
`scripts/compare_version_bits_walk.py` and `scripts/core_pass.py --version-bits` compare it with Core outside CI ([the Core pass](core-harness.md#the-core-pass)).
`scripts/test_core_pass.py` compares it with Core in CI on synthetic chains.

The request has one required field, `chain`: the blocks from the genesis block to the predecessor of the next block, oldest first.
Each entry is an object with exactly these fields:

- `version`: an integer from 0 to 4294967295, the 32 bits of the block's `nVersion`. The harness reads them as Core's signed `int32_t`.
- `time`: an integer from 0 to 4294967295, the block's `nTime`.

The array has no length limit.
An entry at index `i` is the block at height `i`.

```json
{"id":"v1","op":"block.version_bits_state","chain":[]}
{"id":"v1","ok":{"csv":"defined","segwit":"defined"}}
```

The result in `ok` has two fields:

| Field | Meaning |
| --- | --- |
| `csv` | The state of the CSV deployment for the block after the last entry |
| `segwit` | The state of the SegWit deployment for the block after the last entry |

Each state is one of `defined`, `started`, `locked_in`, `active` and `failed`, Core's `THRESHOLD_DEFINED` to `THRESHOLD_FAILED`.
The harness answers an empty chain with `defined` for both deployments, without a call to `VersionBitsState`.
These are request errors: a `chain` that is not an array, an entry that is not an object, and an unknown or missing field.
A value outside its range is also a request error.

## The proposal executable

`dogelib-proposal-oracle` is a second executable, built from the `ProposalExports` library ([design record 0011](design/0011-mainnet-ranges.md), section 10.2 and decision 10).
It answers every operation of `dogelib-oracle` with the code of `dogelib-oracle`.
It adds one argument to `block.validate`, with `blocks_hex` and with `blocks_file`, and to `block.contextual_check_body`:

```text
"revision": {"name": "RelativeLockTime", "variant": null, "activation_height": 1}
```

| Field | Value |
| --- | --- |
| `name` | The name of a revision: `RelativeLockTime`. The test build also names `ExampleFaultyLocktime` and `ExampleVersionVerify`. |
| `variant` | `corrected` or `faulty` for `ExampleFaultyLocktime`, and null for the two other revisions. |
| `activation_height` | A mainnet height from 0 to 2,147,483,646, or null for no activation. |

The three fields are required, and any other field is a request error.

`ExampleFaultyLocktime` and `ExampleVersionVerify` are the examples of the framework, in the test-only `ProposalExamples` library. Neither is a proposal for Dogecoin.
Only the test build `proposal-test-oracle` names them. It runs the code of `dogelib-proposal-oracle` with the two examples added to its revisions, and `dogelib-proposal-oracle` returns a request error for an example.

`RelativeLockTime` is the proposed revision of [design record 0012](design/0012-relative-lock-time.md).
It has the rules of BIP 113, BIP 112 and BIP 68.
For `block.validate`, its transaction test reads the view `chain` of each block.
A transaction that fails the sequence locks of BIP 68 has the step `ConnectBlock`, the reason `bad-txns-nonfinal`, the score 100, the code `0x10` and its position in `tx`.
The test has three results outside the model, with the verdict `unsupported` and one of the texts `RelativeLockTime: ancestorOutsideView`, `RelativeLockTime: coinAboveBlock` and `RelativeLockTime: heightOutOfDomain` in `reason`.
A time lock on a coin needs the entries of `chain` down to ten below the block before the coin's block, or down to the genesis block.

`dogelib-oracle` has no such argument and returns a request error for it.
Without the argument, the proposal executable writes the response of `dogelib-oracle`, byte for byte.
`dogelib-proposal-oracle --version` prints the format with `"program": "dogelib-proposal-oracle"`.

With the argument, the request runs as before: the baseline `validateBlock` decides each block and carries the coin set and the chain view.
For each block, `Proposals.Framework.validateBlockWith` also runs the revision on the state before the block.
The revision is active from `activation_height`.
Each block record gains the object `revised`, and no other field of the response changes:

| Field | Value |
| --- | --- |
| `active` | Whether the revision is active at the height of the block. |
| `verdict` | `accepted`, `rejected` or `unsupported`. |
| `step` | For a rejection or an unsupported result, the check that gave it: `CheckBlockHeader`, `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock` or `ConnectBlock`. |
| `reject_reason` | For a rejection, Core's reject reason. For a script failure, the bracket holds the text of the revision's error. |
| `dos`, `reject_code` | For a rejection, the denial-of-service score and the reject code. A script failure that is not mandatory has the score 0 and the code 64, as in the baseline record. |
| `tx`, `input` | For a rejection that names them, the position of the transaction in the block and of the input in the transaction. `tx` is set for a `CheckTransaction` failure, a missing coin, a `CheckTxInputs` failure and a script failure. `input` is set for a script failure. |
| `script_error` | For a script failure, the text of the error of the first script run. A baseline error has Core's text. An error of the revision has a text that starts with the name of the revision. |
| `mandatory` | For a script failure, false when the second run accepts. The second run uses the flags without `STANDARD_NOT_MANDATORY_VERIFY_FLAGS` and the same activation. |
| `reason` | For an unsupported result, a text for the missing capability or the result outside the model. |
| `changes_digest_hex` | For an acceptance, the digest of the coin changes of the revision's result. |

A field that does not apply is null.
A *changed block* is a block whose record has `valid` true and a `revised.verdict` of `rejected`, or `valid` false and a `revised.verdict` of `accepted`.
An unsupported result is not a rejection, and its block is not a changed block.

The run answers one question for each block: what does the revision say about this block on the baseline chain below it?
It does not build the chain that revised nodes would build after a changed block.
No Core behaviour exists for an example, so no comparison supports its `revised` objects.
The theorems of `DogeLib.Proposals.Framework.Proofs.Block` relate the two verdicts ([docs/soundness/proposals.md](soundness/proposals.md#proposed-revisions-the-block-level)).

With the argument, `block.contextual_check_body` returns the response of the baseline operation with one more object, `revised`.
The object is the result of `Proposals.Framework.contextualBodyWith`: `ContextualCheckBlock` with the lock-time arguments of the revision.
The context has the view `chain`, and the version-bits states that the baseline operation computes.

| Field | Value |
| --- | --- |
| `active` | Whether the revision is active at the height of the block. |
| `verdict` | `accepted`, `rejected` or `unsupported`. |
| `reject_reason`, `dos`, `reject_code` | For a rejection, Core's reject reason, score and reject code. Null otherwise. |
| `reason` | For an unsupported result, a text for the input outside the model. Null otherwise. |
| `lock_time_cutoff` | The lock-time cutoff that the revision gives the check: the median time past, or the time of the block. |

The operation runs no header check before the body check.
`RelativeLockTime` reads the median time past of the view when it is active on an applicable block.
A `chain` without that median gives `unsupported`: an invalid view, or a view with fewer entries than Core's median walk reads.
So a request for this revision supplies the eleven predecessors, or every predecessor below height 11, as well as the entries that the baseline operation needs.
A request on which the baseline operation returns an error returns that error.

A request with `coins_file` runs the snapshot path of `dogelib-oracle` with the hook of the revision (`Block.Exports.blockValidateSnapshotWith`).
The revision runs on the same restricted coin set as the baseline: the coins whose transaction IDs the blocks name.
`validateBlock_restrict` shows that the baseline gives the same result on that set as on the whole set.
No theorem states the same for `validateBlockWith`.
So a `revised` verdict from a snapshot rests on the restricted set, as a test.

For `scripts/test_proposal_oracle.py`, see [testing the proposal executable](core-harness.md#testing-the-proposal-executable).
The test does not run a revision on the mainnet ranges of design record 0011. [Historical impact runs](comparison-evidence.md#historical-impact-runs) does.

## Not in this format

A request to build a transaction from its fields would need another format name.

## Tests

`scripts/test_oracle.sh` builds the oracle and runs `scripts/test_oracle.py`.
`tests/oracle/README.md` gives the source of each expected value.

## Related documents

- [Core harness and comparators](core-harness.md): build, boundary contract card, harness operations, response projections and Core pass mechanics.
- [Comparison evidence](comparison-evidence.md): request stream counts, replays, snapshot ranges, forced-CSV results and recorded historical impact runs.
- [Bug-finding campaign](campaign.md): campaign driver, generator, reducer, L1 and L3 replay and regression fixtures.
- [Oracle and harness trust boundaries](soundness/oracle-and-harness.md): per-operation Gap B4 boundaries and assumptions.
