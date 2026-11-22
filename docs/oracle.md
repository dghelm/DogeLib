# The oracle and its record format

`dogelib-oracle` runs DogeLib's specification on requests from another program, such as a harness that runs Dogecoin Core on the same inputs.
This document defines its record format, `dogelib-oracle/1`.
The oracle supports only this format.

The oracle models Core's serialization, legacy signature hash, work arithmetic, byte-string hashes, pure block commitments and individual Script calls.
It reads transactions in base mode or with witness data allowed.
The witness operations model a serialization format only.
Segregated witness is not active on Dogecoin at the pin.
`IsWitnessEnabled` returns false, and main and test reject blocks with witness data (SOURCES.md D36).

Its [protocol context](../SOUNDNESS.md#transactions-the-witness-allowed-format) separates witness script verification from the commitment checks in Core.
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
| `script.read_op` | `bytes_hex`, `cursor` (`u32`) | Instruction or read failure with cursor, as below | `Script.readInstruction`, Core's `CScript::GetOp` |
| `script.eval` | `bytes_hex`, `flags` (`u32`), `stack_hex`, optional `checker` | Evaluation result, as below | `Script.evalScript`, Core's `EvalScript` in `SIGVERSION_BASE` |
| `script.verify_legacy` | `tx_hex`, `input_index` (`u32`), `prevout_script_hex`, `flags` (`u32`), `checker` | Spend result, as below | `Script.verifyScript` or `Script.verifyLegacySpend`, Core's `VerifyScript` with no witness |
| `oracle.version` | none | `format`: `"dogelib-oracle/1"` | none |
| `compactsize.encode` | `value`: `u64` | `bytes_hex` | `CompactSize.encode`, Core's `WriteCompactSize` |
| `compactsize.read` | `bytes_hex` | `value` (`u64`), `consumed`, `rest_hex` | `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check |
| `tx.read_base` | `bytes_hex` | `tx`, `consumed`, `rest_hex` | `Transaction.readBase`: a transaction at the start of the bytes, as Core reads the next transaction of a stream |
| `tx.decode_base` | `bytes_hex` | `tx`, `serialized_hex`, `txid_hex`, `txid_display` | `Transaction.decodeBaseComplete`: a transaction that is all of the bytes. Then its base serialization and its ID, `Transaction.txid` |
| `tx.read_witness` | `bytes_hex` | Witness result, `consumed`, `rest_hex` | `Transaction.readAllowWitness`: a prefix with witness data allowed |
| `tx.decode_witness` | `bytes_hex` | Witness result | `Transaction.decodeAllowWitnessComplete`: the whole input with witness data allowed |
| `sighash.legacy` | `tx_hex`, `script_code_hex`, `input_index` (`u32`), `hash_type` | `plan`, `preimage_hex` (for `hash_bytes` only), `digest_hex`, `digest_display` | `tx_hex` is read as by `tx.decode_base`. Then `legacySignatureHashPlan` and `LegacyHashPlan.digest`: Core's `SignatureHash` with `SIGVERSION_BASE` |
| `pubkey.verify` | `pubkey_hex`, `sig_hex`, `digest_hex` | `valid` (boolean) | `Script.coreVerify` |
| `hash.ripemd160` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Ripemd160.hash` |
| `hash.hash160` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Hash160.hash` |
| `hash.sha1` | `bytes_hex` | `digest_hex` (twenty bytes) | `Cryptography.Hash.Sha1.hash` |
| `header.read` | `bytes_hex` | `header`, `consumed`, `rest_hex` | `Codec.decode` for `Block.PureBlockHeader` |
| `header.encode` | `header` | `bytes_hex` | `Codec.encode` for `Block.PureBlockHeader` |
| `header.hash` | `header` | `hash_hex`, `hash_display` | `Block.PureBlockHeader.getHash` |
| `merkle.compute` | `leaves_hex` | `root_hex`, `root_display`, `mutated` | `Block.computeMerkleRoot` |
| `work.set_compact` | `compact` (`u32`) | `value_hex` (target magnitude), `negative`, `overflow` (booleans) | `Work.ArithUint256.setCompact` |
| `work.get_compact` | `value_hex` (target magnitude), `negative` (boolean) | `compact` (`u32`) | `Work.ArithUint256.getCompact` |
| `work.calculate_next` | `network`, `selection_height`, `last_height`, `last_time`, `last_bits`, `first_time` | `bits` (`u32`) | `Work.calculateDogecoinNextWorkRequired` with `Work.getConsensus` |
| `work.next` | `network`, `chain`, `candidate_time` (`u32`) | `bits` (`u32`) | `Work.nextWorkRequired` |
| `block.subsidy` | `cases`: an array of `height` and `prev_hash_hex` pairs | `subsidies`, and Lean-only `redraws`, [as below](#block-subsidy) | `Block.getDogecoinBlockSubsidy`, Core's `GetDogecoinBlockSubsidy` on mainnet |
| `tx.check` | `tx_hex`, `mode`, `check_duplicate_inputs` (boolean) | Verdict, `legacy_sigops`, `base_size`, and Lean-only `diagnostic`, [as below](#transaction-and-block-checks) | `Transaction.checkTransaction` and `Transaction.getLegacySigOpCount`, Core's `CheckTransaction` and `GetLegacySigOpCount` |
| `block.check` | `block_hex`, `mode`, `check_pow`, `check_merkle_root` (booleans) | Verdict, `corruption_possible`, `legacy_sigops`, `base_size`, `transactions`, `hash_hex`, `hash_display`, and Lean-only `diagnostic`, [as below](#transaction-and-block-checks) | `Block.decodeComplete`, then `Block.checkBlock` on mainnet, Core's `CheckBlock` |

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

The harness obtains the cursor from Core's iterator and derives these diagnostic fields from the original opcode.

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

The harness calls Core's own `EvalScript` with `SIGVERSION_BASE` and `BaseSignatureChecker`.
That checker returns false for signature, locktime and sequence checks.
The harness uses this checker for either evaluation selection.
An unsupported Lean result makes no claim about Core's verdict on that request.

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

The harness calls Core's `VerifyScript` with a null witness and the selected checker.
`TransactionSignatureChecker` receives the immutable transaction, input index and amount zero, which legacy hashing does not use.
An `ECCVerifyHandle` lives for the request loop and initializes Core's verification context.
Pinned `src/pubkey.cpp`, `CPubKey::Verify` and `ECCVerifyHandle` (D50), use that context for key parsing and libsecp256k1 verification.
The harness signs nothing and does not call `ECC_Start`.
Core's binary and libsecp256k1 remain trusted runtime components, without a Lean refinement theorem.

Core asserts that WITNESS implies P2SH (D3, line 1519), and CLEANSTACK implies both P2SH and WITNESS (lines 1508 and 1509).
The harness rejects flag combinations that violate these dependencies as request errors, without changing flags.
The Lean oracle still reports those unsupported flags.

The comparator classifies these combinations as `harness-refused` only after complete base decoding, input bounds and script limits pass.
The classifier requires the operation's exact arguments, permits an optional `id`, and requires an integer `input_index`.
Earlier decode or adapter errors retain their ordinary comparison path.
The comparator requires a harness request error and an exact Lean unsupported-flags result, or fails the request.
A checked refusal counts as neither agreement nor disagreement.
A failed refusal check fails the run and stays outside the compared count.

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

## Not in this format

A request to build a transaction from its fields would need another format name.

## Tests

`scripts/test_oracle.sh` builds the oracle and runs `scripts/test_oracle.py`.
`tests/oracle/README.md` gives the source of each expected value.

## Header proof of work

These operations extend `dogelib-oracle/1` before release 0.1.0.
Byte strings use serialization order.
`mode` is required and is either `base` or `allow_witness`, including when no payload is present.
The latter uses Core's network stream version without `SERIALIZE_TRANSACTION_NO_WITNESS`.

| Operation | Required arguments | Result in `ok` |
| --- | --- | --- |
| `scrypt.hash` | `bytes_hex`, exactly 80 bytes | `digest_hex`, exactly 32 bytes in scrypt output order |
| `block.header.read` | `bytes_hex`, `mode` | `header`, `consumed`, `rest_hex` |
| `auxpow.check` | `bytes_hex`, `mode`, `hash_hex`, `chain_id`, `strict_chain_id` | Boolean `valid`, and Lean-only `diagnostic` |
| `block.check_pow` | `bytes_hex`, `mode`, `network`, `selection_height` | Boolean `valid`, and Lean-only `diagnostic` |
| `block.header_sequence` | `network`, `mode`, `adjusted_time`, `checkpoints_enabled`, `index`, `failed_blocks`, `headers` | Sequence verdict, added entries and child marks, as below |
| `block.contextual_check` | `bytes_hex`, exactly 80 bytes, `network`, `chain`, `adjusted_time`, `checkpoints_enabled`, `known_checkpoints` | Boolean `valid`, `reject_reason` (null on acceptance), and Lean-only `diagnostic` |
| `block.contextual_check_body` | `block_hex`, `mode`, `chain` | Boolean `valid`, `reject_reason`, `dos` and `reject_code` (null on acceptance), and Lean-only `diagnostic` |
| `block.check_version` | `bytes_hex`, exactly 80 bytes, `network`, `selection_height` | Boolean `valid`, and Lean-only `diagnostic` |
| `block.validate` | `mode`, `check_pow`, `check_merkle_root`, `adjusted_time`, `chain`, `bip34_ancestor_hex`, `coins`, `blocks_hex` | One record for each block, and the digest of the coin set, as [below](#block-validation) |

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
The Core harness reads the field from Core's `Params().GetConsensus(selection_height)`.

It transcribes the two branches from D33 and calls Core's own `IsLegacy` and `IsAuxpow` predicates.
It does not call the complete contextual validator, which needs chain state and checks other rules.

The predicate operations return `diagnostic: null` on acceptance and a Lean error string on rejection.
Core returns only `valid`.
The comparator excludes only Lean's `diagnostic`, and compares Boolean verdicts without coercion.
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
The harness refuses inputs outside its comparison domain before it calls Core's helpers.

Acceptance returns `valid: true`, `reject_reason: null` and `diagnostic: null`.
Rejection returns `valid: false`, Core's first reject reason and a Lean diagnostic string.
The comparator checks `valid` and `reject_reason`, including signed base-version formatting such as `bad-version(0xffffff03)`.
It excludes only the Lean diagnostic.
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

The comparator compares every response field except `diagnostic`.
It compares all other fields first, including the failure position and accepted prefix.
It excludes `marked_failed_child` only for an agreed step-6 failed-ancestor rejection at `failed_at`.
The rejecting header's predecessor must have at least two distinct failed-list members among its ancestors.
The ancestry includes entries added in the accepted prefix.

Other rejection steps and accepted calls retain the mark comparison.
Duplicate members of the failed list do not satisfy that condition alone.
A failed member below an anchor is no ancestor under the finite-index convention.
All other fields remain comparable in the excluded-mark cases.

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
The oracle reports `CoinSet.totalValue` of `Block.Proofs.ConnectProperties`, the quantity of `chain_issuance_bound`.
The harness adds the amounts of the coins of its own `CCoins` entries, in 128-bit arithmetic.

The harness's sum is an `unsigned __int128`.
Before it adds an amount, the harness requires `MoneyRange`, so each amount is at most `MAX_MONEY`, 10^18 koinu, which is below 2^60.
For a set of fewer than 2^64 coins, the sum is below 2^124, so it cannot wrap.
The harness counts the coins in a `uint64_t` without a check, so the bound has that precondition.
The recorded set at the tip has 202,470,869 coins.

The harness writes it with its own decimal conversion, and the oracle writes an `Int`, which has no bound.
The scripts read `set_value` as a string and convert it with Python's `int`, which has no bound.
The mainnet set exceeds 2^63 - 1, the largest `CAmount`: at height 6,465,793 it holds 15,683,043,286,016,806,072 koinu.
Part 7 of `scripts/test_core_pass.py` tests a set of 19,999,999,999,999,999,999 koinu in both programs. That is above 2^64, and a binary64 double does not hold it exactly.

For a request that starts at the genesis block, with the empty chain and no coins, the comparators also check the bound of `chain_issuance_bound`.
Both programs answer `block.subsidy` for each accepted height from 1, with the hash of the accepted block before it, and the subsidies must agree.
Each `set_value` must be at most the sum of the subsidies of the heights from 1 to its height.
The genesis block adds no coin, so its term is 0.
`scripts/compare_core.py --mainnet-blocks` reports a failure of this check as `ISSUANCE`, and `scripts/replay_blocks.py` checks it as its fifth step.

#### The arithmetic domain

Core adds `int64_t` amounts in `ConnectBlock` with no earlier range check, and an overflow there is undefined behaviour in C++ (design record 0010, section 3).
`Block.connectBlock` computes in the integers and returns `outOfDomain` when a sum leaves the `int64_t` range.
The oracle then ends the range: `blocks` holds the records before that block, and `out_of_domain_at` is its position.
The comparator sends the harness the request without that block and the blocks after it.
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
A file request has no `blocks_hex` list to shorten.
So the comparison fails if the oracle ends the range of a file at a block outside the arithmetic domain.

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

The theorem `validateBlock_restrict` is the reason for step 4 ([SOUNDNESS.md](../SOUNDNESS.md#validateblock_restrict-a-block-on-the-coins-that-it-names)).
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
No known request gives that error: a [run outside CI](#block-subsidy-comparison-evidence) covers every seed.

## The Core harness

`harness/core/core_oracle.cpp` answers the same requests by running Dogecoin Core's own code.
It is built against Core v1.14.9 at commit `e0a1c15`, the pin in [SOURCES.md](../SOURCES.md).
`scripts/compare_core.py` runs the harness and the oracle on one stream of requests and requires their responses to agree.
CI runs the comparison in workflow `core`, job `compare`.
The same workflow runs the comparator self-test in job `self-test` and the comparison of the proposed revision `RelativeLockTime` in job `csv-forced`, at the same time.

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle
python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The build also produces `core-signer`, a fixture generator that calls Core's `SignatureHash`, `CKey::Sign` and `VerifyScript`.
Its fixed private keys are public test data.
[Signed recovery-template fixtures](../tests/script/signed-spends/README.md) record its inputs, signatures, Core verdicts and reproduction commands.
`core-signer --fixed-digest` generates the [fixed-digest fixtures](../tests/script/signed-spends/README.md#fixed-digest-spends) of the same directory.
It runs outside the oracle comparison loop.

The build script exports the pinned commit from the clone with `git archive`.
The clone must contain that commit, but its working tree may be at any other.
It configures Core as `scripts/build_core_node.sh` does, with the daemon enabled and no wallet, GUI, tests or ZMQ.
It builds Core's server, common, utility, consensus, cryptography, UniValue, LevelDB and secp256k1 libraries, and never links `dogecoind`.
It needs autoconf, automake, libtool, pkg-config and the development files of OpenSSL and libevent (`libssl-dev` and `libevent-dev` on Ubuntu).

`scripts/core_boost.sh` supplies Boost 1.70.0 for both build scripts: it downloads the archive, checks its SHA-256 and builds five libraries into `<build-dir>/boost`.
`BOOST_ROOT` selects an installed Boost, and `BOOST_ARCHIVE` names a local copy of the archive.

The harness links the libraries of `dogecoind` in the order of `dogecoind_LDADD` (`src/Makefile.am`, lines 395 to 408), with Boost, OpenSSL and libevent.
`harness/core/core_validation.cpp` includes Core's `src/validation.cpp` and `src/timedata.cpp` as text.
The compiler sees both files unchanged, and the unit can name what they keep internal:

- The static function `AcceptBlockHeader`.
- The sets `gFailedBlocks` and `setDirtyBlockIndex` of the anonymous namespace.
- The static variable `nTimeOffset`.

The unit defines every symbol of both files, so the link takes neither `validation.o` nor `timedata.o` from the server library.
Its four functions contain no validation logic.
The server library brings in Core's network, RPC, database and memory-pool objects.
The harness runs none of that code: it opens no database, starts no thread and creates no data directory.

`core-signer` keeps its earlier link.
It uses the objects of `pow.cpp`, `chain.cpp`, `dogecoin.cpp`, `chainparams.cpp`, `chainparamsbase.cpp`, `auxpow.cpp` and `checkpoints.cpp`, compiled apart from the server library.
Function and data sections, with linker garbage collection, discard unrelated functions and their dependencies.
That link assumes GNU ld for `--gc-sections`, as Linux CI does.
These pinned sources supply the work functions and parameter constructors:

| Source | Role |
| --- | --- |
| [D17, `src/pow.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pow.cpp) | `GetNextWorkRequired` |
| [D35, `src/chain.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp) | `BuildSkip`, `GetAncestor` and the skip-height guard |
| [D6, `src/dogecoin.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp) | `CalculateDogecoinNextWorkRequired` and minimum-difficulty permission |
| [D14, `src/chainparams.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp) | Network parameter records, `SelectParams` and `GetConsensus` |
| [D67, `src/checkpoints.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/checkpoints.cpp) | `Checkpoints::GetLastCheckpoint` |
| [D39, `src/chainparamsbase.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparamsbase.cpp) | `SelectBaseParams`, called by `SelectParams` |

### What the harness runs

| `op` | Core's code |
| --- | --- |
| `block.header_sequence` | `AcceptBlockHeader` once for each header, which calls `CheckBlockHeader`, `ContextualCheckBlockHeader` and `AddToBlockIndex`, on an index that the harness builds from the request |
| `block.contextual_check` | `ContextualCheckBlockHeader` on index entries that the harness builds from the request |
| `block.contextual_check_body` | `SelectParams` for mainnet, then `ContextualCheckBlock` on a `CBlock` that Core's stream code reads, with a predecessor that the harness builds from the chain. `VersionBitsState` reads the aligned boundary's median time, and the harness seeds `THRESHOLD_FAILED` at a boundary at or after the CSV timeout. With `force_csv_active`, the harness seeds `THRESHOLD_ACTIVE` for CSV, a state that no mainnet chain reaches ([the forced CSV state](#core-with-the-csv-state-forced-to-active)) |
| `block.check` | `SelectParams` for mainnet, then `CheckBlock` on a `CBlock` that Core's stream code reads from the request, with the two flags of the request. Then `GetLegacySigOpCount` for each transaction, `GetSerializeSize` in base mode and `GetHash` |
| `block.validate` | `SelectParams` for mainnet. Then, for each block that Core's stream code reads: `CheckBlockHeader` when `check_pow` is true, `ContextualCheckBlockHeader`, `CheckBlock`, `ContextualCheckBlock`, and `ConnectBlock` with `fJustCheck` true on a new `CCoinsViewCache` over the carried set. The first two do not run for the genesis hash. `UpdateCoins` on a second cache gives the changes of an accepted block ([choices](#block-validation-in-the-harness)) |
| `block.subsidy` | `SelectParams` for mainnet, then `GetDogecoinBlockSubsidy` with `Params().GetConsensus(height)` for each case, as `ConnectBlock` calls it (D101, line 1996) |
| `compactsize.encode` | `WriteCompactSize` into a `CDataStream` |
| `compactsize.read` | `ReadCompactSize` from a `CDataStream` |
| `tx.check` | `CheckTransaction` on a `CTransaction` that Core's stream code reads from the request in the mode of the request. Then `GetLegacySigOpCount` and `GetSerializeSize` in base mode |
| `tx.read_base` | `CMutableTransaction` read from a `CDataStream` whose version has `SERIALIZE_TRANSACTION_NO_WITNESS`, so `UnserializeTransaction` reads base mode |
| `tx.decode_base` | The same read, then a check that the stream is empty. The transaction written back to a stream of the same version, and `CTransaction::GetHash` |
| `tx.read_witness`, `tx.decode_witness` | `CMutableTransaction` read from a `CDataStream` without `SERIALIZE_TRANSACTION_NO_WITNESS`. The complete operation requires an empty stream. Both write with witness data allowed and call `CTransaction::HasWitness`, `GetHash` and `GetWitnessHash`. |
| `script.read_op` | `CScript::GetOp` on the exact script bytes, with iterator `begin() + cursor` |
| `script.eval` | `EvalScript` with the caller stack and flags, `BaseSignatureChecker` and `SIGVERSION_BASE` |
| `script.verify_legacy` | `VerifyScript` with a null witness and the selected `BaseSignatureChecker` or `TransactionSignatureChecker`. `CPubKey::Verify` and `ECCVerifyHandle` use libsecp256k1 |
| `sighash.legacy` | `tx_hex` read as by `tx.decode_base`. Then `SignatureHash` with amount 0 and `SIGVERSION_BASE` |

The harness also calls these hash and block functions:

| `op` | Core's code |
| --- | --- |
| `pubkey.verify` | `CPubKey::Verify`, with storage-order `uint256` digest bytes |
| `hash.ripemd160` | `CRIPEMD160::Write` and `Finalize` |
| `hash.hash160` | `CHash160::Write` and `Finalize` |
| `hash.sha1` | `CSHA1::Write` and `Finalize` |
| `header.read` | `CPureBlockHeader` read from a `CDataStream` |
| `header.encode` | `CPureBlockHeader` written to a `CDataStream` |
| `header.hash` | `CPureBlockHeader::GetHash` |
| `merkle.compute` | `ComputeMerkleRoot`, including its `mutated` output argument |

Core's consensus archive supplies `primitives/pureheader.cpp` and `consensus/merkle.cpp`.
The same archive contains `script/interpreter.cpp`, `script/script.cpp` and `script/script_error.cpp`.
Its cryptography archive supplies RIPEMD-160, SHA-256 and SHA-1.
The harness implements no replacement hash or Merkle algorithm.

The harness also calls these work functions:

| `op` | Core's code |
| --- | --- |
| `work.set_compact`, `work.get_compact` | `arith_uint256::SetCompact` and `GetCompact` |
| `work.calculate_next` | `SelectParams`, `Params().GetConsensus(selection_height)`, then `CalculateDogecoinNextWorkRequired` on an explicit `CBlockIndex` |
| `work.next` | `SelectParams`, candidate-height `GetConsensus`, then `GetNextWorkRequired` on linked `CBlockIndex` objects |

The harness compares `work.next` only on contiguous views with enough history for the required retarget ancestor or recovery walk.
It rejects a request outside that domain before it calls Core.
Core can assert on a missing ancestor, and a truncated recovery walk can return a different result.
The comparison excludes every `work_view` fixture and checks those errors only against the oracle fixtures.
The oracle reads chain heights as `u32` and returns `work_view` with `height_out_of_range` from 2147483647.
The harness instead returns a `request` error for those heights, outside its caller domain.

The harness sets each supplied entry's `pprev`, `nHeight`, `nTime` and `nBits`.
It computes Core's `GetSkipHeight` only to decide whether to call `BuildSkip` within the supplied suffix.
When that destination precedes the suffix, the skip pointer stays null.
Core's `GetAncestor` then follows `pprev`, so this guard changes no result.
The traversal cannot diverge through a retained skip pointer because Core follows `pskip` only when its skip height is at least the target.
The `work missing skip traversal` comparison retargets from height 479 to ancestor 239 across height 256, whose skip pointer is null.

### How its responses differ

The harness answers a projection of `dogelib-oracle/1`, not the format itself:

- `--version` and `oracle.version` give the format `dogelib-oracle/1-core-projection`.
- `script.eval` and `script.verify_legacy` never return `unsupported` from the harness.
  It returns Core's verdict with the operation's checker, even when Lean reports an unsupported capability.
  An unmapped `ScriptError` stops the harness with an unmapped-Core error.
- For a truncated `script.read_op`, the harness derives `opcode` and `part` from the input and cursor.
  Core does not return these diagnostics.
- `tx.check` and `block.check` have no `diagnostic`. Core reports the reject reason, and not the Lean error or the position of a rejected transaction.
  The harness builds a new `CBlock` for each request, so `fChecked` is false at the call.
  It stops with an unmapped-Core error if that member is set.
- The block records of `block.validate` have no `diagnostic`, and `out_of_domain_at` is always null.
  Core has no test for the overflow of its sums, so the harness cannot report one.
- `block.subsidy` has no `redraws`, because Core does not report the rejected words.
  It has `boost_version` instead: the release of the Boost headers that Core's function was compiled with, such as `1.70.0`.
- `sighash.legacy` has no `preimage_hex`.
  `SignatureHash` hashes its preimage as it writes it and does not return it.
- `plan` is a label that the harness computes from the conditions of Core's two early returns, in `src/script/interpreter.cpp` lines 1225 to 1235.
  It is not observed from Core.
  If the label is `fixed_digest` and Core's digest is not the value one, the harness stops with exit status 3.
- The harness passes the hash type to Core's `int nHashType` as the same 32 bits, read as a two's complement value.
  It passes `input_index` to `unsigned int nIn` unchanged.
- Core reports a read error as a `std::ios_base::failure`.
  The harness maps four messages to `read` errors: `CDataStream::read(): end of data` to `truncated`, `non-canonical ReadCompactSize()` to `non_canonical`, `ReadCompactSize(): size too large` to `too_large`, and `Unknown transaction optional data` to `unknown_optional_data`.
  It accepts each message alone or followed by `: iostream error`, which libstdc++ appends.
  Any other exception stops the harness with exit status 3, so it fails the comparison.

The harness checks request arguments by the rules of this document.
Twenty-two adapter-limit boundary requests check both programs against the documented expectations, including `adapter/resource_limit` errors.
Other argument checks have oracle fixtures but no Core comparison.

### The proposal executable

`dogelib-proposal-oracle` is a second executable, built from the `ProposalExports` library ([design record 0011](design/0011-mainnet-ranges.md), section 10.2 and decision 10).
It answers every operation of `dogelib-oracle` with the code of `dogelib-oracle`.
It adds one argument to `block.validate`, with `blocks_hex` and with `blocks_file`, and to `block.contextual_check_body`:

```text
"revision": {"name": "ExampleVersionVerify", "variant": null, "activation_height": 0}
```

| Field | Value |
| --- | --- |
| `name` | The name of a revision: `ExampleFaultyLocktime`, `ExampleVersionVerify` or `RelativeLockTime`. |
| `variant` | `corrected` or `faulty` for `ExampleFaultyLocktime`, and null for the two other revisions. |
| `activation_height` | A mainnet height from 0 to 2,147,483,646, or null for no activation. |

The three fields are required, and any other field is a request error.
`ExampleFaultyLocktime` and `ExampleVersionVerify` are the examples of the `Proposals` library. Neither is a proposal for Dogecoin.
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
The theorems of `DogeLib.Proposals.Framework.Proofs.Block` relate the two verdicts ([SOUNDNESS.md](../SOUNDNESS.md#proposed-revisions-the-block-level)).

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

The executable has one test, which needs no Dogecoin Core:

```bash
lake build dogelib-oracle dogelib-proposal-oracle
python3 -I scripts/test_proposal_oracle.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle
```

- Without `revision`, the two programs write the same bytes on the 42 `block.validate` requests of the full comparison and on 34 requests with `blocks_file`. With `--mainnet-blocks build/mainnet-blocks`, the test adds the replay of mainnet heights 0 to 10,000.
- Without `revision`, the two programs also write the same bytes on the 22 `block.contextual_check_body` requests of the comparison. With a revision and no activation height, each `revised` object has `active` false and the baseline verdict. The examples change no lock-time argument, so the same holds for them from height 0.
- `dogelib-oracle` refuses `revision`, and the proposal executable refuses 18 malformed values of it.
- With no activation height, each `revised` object has the verdict, the reject reason and the changes digest of its baseline record. The check covers the 119 block records of those 42 requests, for each revision.
- From height 0 on the same requests, the response without the `revised` objects is the baseline response. No block goes from rejected to accepted under the two revisions with a restriction theorem.
- One request of the comparison has five blocks that fail the five checks in Core's order. Each `revised` object names the check in `step`, and the transaction at 1 in `tx` for the duplicate inputs and for the missing coin.
- Eleven made blocks give `revised` objects that the test states by hand from the text of each rule. Each block stands on a committed rule-change block and spends a supplied coin. For eight of them the script of the coin holds the rule of an example. A negative operand of each rule changes an accepted block to rejected. The counterexample of the faulty variant changes a rejected block to accepted. Three blocks are for the sequence locks of `RelativeLockTime`, with a transaction of version 2. A height lock that is met leaves the block accepted. A height lock that is one block short gives the reason `bad-txns-nonfinal`. A time lock on a coin above the block gives `unsupported` with the reason `RelativeLockTime: coinAboveBlock`.

The test does not run a revision on the mainnet ranges of design record 0011. Those runs are conditions 4 and 5 of its stage 6.

#### Core with the CSV state forced to `ACTIVE`

This evidence has its own label: Core at `e0a1c15` with the CSV state forced to `ACTIVE`.
It is about the proposed revision `RelativeLockTime` alone. It is not a Core comparison of the baseline, and it is not evidence about mainnet.

Dogecoin Core 1.14.9 holds the code of BIP 113, BIP 112 and BIP 68, and its version-bits state for CSV never becomes `ACTIVE` on mainnet (`csv_never_lockedIn`).
`block.contextual_check_body` and `block.validate` of the Core harness take one more argument, the Boolean `force_csv_active` ([design record 0012](design/0012-relative-lock-time.md), section 10.2 and decision 12).
With the value true, the harness seeds `THRESHOLD_ACTIVE` for CSV in Core's version-bits cache, at the boundary that the block reads.
Core's own `ContextualCheckBlock` then takes the median time past of the predecessor as the lock-time cutoff (D110, lines 3134 and 3135).
In `block.validate`, Core's own `ConnectBlock` also sets `SCRIPT_VERIFY_CHECKSEQUENCEVERIFY` (D114, lines 1906 to 1911), so opcode `0xb2` is `OP_CHECKSEQUENCEVERIFY`.
It also passes `LOCKTIME_VERIFY_SEQUENCE` to `SequenceLocks` (lines 1948 to 1959), so each transaction that is not a coinbase has the sequence locks of BIP 68.
No line of Core's source changes.

The harness seeds nothing for a block that is not applicable: one without a predecessor, or one whose header has the hash of the genesis block.
Below height 10,080 the aligned boundary is null, which is also the cache key of a block without a predecessor.
The harness clears the cache before and after each request.
With the argument, the `chain` must hold the eleven predecessors, or every predecessor below height 11, and the harness refuses a shorter chain.
`dogelib-oracle` and `dogelib-proposal-oracle` refuse the argument, and the harness and `dogelib-oracle` refuse `revision`.

```bash
python3 -I scripts/fetch_release_blocks.py
python3 -I scripts/relative_lock_time_candidates.py --check
python3 -I scripts/compare_csv_forced.py .lake/build/bin/dogelib-oracle .lake/build/bin/dogelib-proposal-oracle build/core-harness/core-oracle
```

`scripts/compare_csv_forced.py` sends each block to the harness with `force_csv_active`, and to the proposal executable with `RelativeLockTime` from activation height 1.
It compares the forced result of Core with the `revised` object: verdict, reject reason, score and reject code.

| Part | Requests | Contents |
| --- | ---: | --- |
| Refusals | 5 | Each program refuses the argument that it does not have, and the harness refuses a value that is not a Boolean |
| Made blocks | 37 | A lock time on each side of the median cutoff and of the block time. Final and other sequences, a height lock time and a locked coinbase. Unsorted times, and heights 1, 2, 3, 11 and 12. A period boundary before the CSV start and after the CSV timeout. Three blocks that are not applicable. Each verdict is derived by hand from `IsFinalTx` and from lines 3127 to 3140 |
| Harness state | 74 | After each made block with the argument, the same request without it and with the value false. Each gets the hand-derived baseline verdict |
| Mainnet blocks | 11,018 | Heights 0 to 10,000, heights 6,455,302 to 6,456,301 and the 17 rule-change blocks, each with the argument |
| Self-test | 32 | For 16 made blocks with two verdicts, the comparison fails with the revision inactive, and fails against a harness run without the seed |
| `block.validate` refusals | 4 | Each program refuses the argument that it does not have, and the harness refuses a value that is not a Boolean |
| `block.validate` made blocks | 36 | 18 spends of one supplied coin, at heights 1,034,382 and 3,464,751. A height operand met exactly and one short. Versions 1, 2 and -1. A sequence with bit 31, and with bits outside the mask. Time and height types. An operand with bit 31, a negative operand, one of six bytes, and an empty stack. The opcode in a skipped branch, in the `scriptSig` and in a P2SH redeem script. A script with a false result. Each verdict is derived by hand from D3, lines 392 to 427 and 1310 to 1354, and from D101, lines 1488 to 1512 |
| `block.validate` harness state | 72 | After each made block with the argument, the same request without it and with the value false. The response with the argument, without its objects `forced`, equals the response without the argument |
| `block.validate` self-test | 40 | For 20 made blocks with two verdicts, the comparison fails with the revision inactive. It also fails when the harness record without the seed stands in the place of `forced`. Each failure is a difference of verdicts |
| Sequence locks, made blocks | 61 | Each with the argument and then without it. 23 blocks at each of the heights 1,034,382 and 3,464,751: a height lock met exactly, and one block short. Versions 1, 2 and -1. Bit 31, and bits outside the mask. A coin that the block itself creates, with a height lock and a time lock of 0 and of 1. The largest time lock that is met on a coin 20 blocks below, and one unit more. A height lock on a coin above the block. Five blocks at each height are outside the model, for the three reasons. 14 blocks at height 40 on a made chain from height 0, whose entry at height `k` has the time 1,400,000,000 + 512 * `k`: time locks that are met exactly and one unit more on coins at heights 0, 1, 2 and 21, a time lock that is one second short, and height locks on the coins at heights 0 and 1. One block that Core rejects through BIP30, for the scan of the harness. Each result is derived by hand from D114, lines 309 to 384, and from BIP 68. The script computes the median times past from the times of the request |
| Sequence locks, self-test | 75 | For the 33 made blocks with two results, the comparison fails with the revision inactive. It also fails when the harness record without the seed stands in the place of `forced`. Nine malformed results of the two programs are not taken for results: an acceptance without a digest of its changes, a digest of another length, the number 1 as a verdict, a reason with a verdict, and a result outside the model with a digest, a reject field or an unknown reason |
| Scan of the harness | 1 | A block above the BIP34 height, where Core does not enforce BIP30. One transaction overwrites an unspent entry of its own ID, and the next has a time lock on a coin two blocks above the block. The harness must name `coinAboveBlock`. This check reads the harness alone |
| `block.validate` on mainnet | 1 | Heights 0 to 10,000 in one request from the empty coin set, with the argument. The harness runs each block with the seed and without it, and the run without the seed carries the state |

Every forced result agrees with its `revised` object.
The made blocks reach `bad-txns-nonfinal` from the cutoff 20 times.
One made block has a time below the median, which `ContextualCheckBlockHeader` rejects. This operation runs no header check, and both programs then accept a lock time that the baseline rejects.

The forced run accepts each of the 11,018 mainnet blocks, so no block is changed.
That count equals the committed candidate list, [`tests/proposals/relative-lock-time/cutoff-candidates.json`](../tests/proposals/relative-lock-time/README.md), which has no candidate block.
In `block.validate`, the forced run also accepts each block of heights 0 to 10,000, with the changes of the run without the seed, and the proposal executable gives the same result for each. No block of that range is changed or outside the model.
One recorded run of the whole script on a development machine takes about 16 minutes, most of it for that replay, and the proposal executable uses about 1.8 GB of memory.

With `force_csv_active` true, `block.validate` of the harness runs each block twice on the state before it.
The first run has the seed, and its result is the object `forced` of the block record.
The second run has no seed. It gives the other fields of the record, and it alone carries the coin set and the chain to the next block.
So the response without its objects `forced` is the response of the request without the argument.

| Field of `forced` | Value |
| --- | --- |
| `valid`, `reject_reason`, `dos`, `reject_code` | The verdict of the five checks with the CSV state forced to `ACTIVE`, as in the block record. |
| `changes_digest_hex`, `spent`, `created` | For an accepted block, the digest and the counts of its coin changes. Null otherwise. |
| `unsupported` | Null, or one of `ancestorOutsideView`, `coinAboveBlock` and `heightOutOfDomain`: a read of `SequenceLocks` that is outside the model of the revision. Every other field is then null. |

A block that is not applicable gets no seed, and its `forced` object is the result without it.
The comparison reads `forced` against the `revised` object of the proposal executable: verdict, reject reason, score, reject code and the digest of the changes.
The 36 made blocks reach `non-mandatory-script-verify-flag` through the opcode 20 times, and `mandatory-script-verify-flag-failed` twice, for a script that also fails without the flag.

With the forced state, Core's `ConnectBlock` also runs `SequenceLocks` of BIP 68 (D114, lines 1948 to 1959), which the revision has as `sequenceLocks`.
Each of the 36 made blocks of the opcode passes that test, in Core and in the revision: its coin is far below the block, or its lock is 0.
The 61 made blocks of the sequence locks reach `bad-txns-nonfinal` of `ConnectBlock` 23 times, with the score 100.

Three reads of `SequenceLocks` are outside the model of the revision (design record 0012, section 6.3), and the harness does not let Core make them.

| `unsupported` | Read |
| --- | --- |
| `heightOutOfDomain` | An input with a lock spends a coin at a height from 2^31 - 65535. Core computes `c + n - 1` from the left in `int`, and `c + 65535` can then overflow. |
| `coinAboveBlock` | A time lock on a coin above the block. For a coin one block above, Core reads the median time past of the block itself. For a higher coin, `GetAncestor` returns null, and Core dereferences it. |
| `ancestorOutsideView` | A time lock whose ancestor, or one of its ten predecessors, is below the supplied chain. |

Before the forced `ConnectBlock`, the harness scans the block in the order of the revision: the transactions in block order, the inputs in input order, and for one input the order of the table.
On the first such read it does not run `ConnectBlock` with the seed. The object `forced` then has that name in `unsupported`, and no verdict.
The comparison requires the verdict `unsupported` of the `revised` object, with the same reason.
So for these blocks the comparison checks that the two programs draw the limit of the model at the same place. It is no comparison of a verdict, because Core gives none.
For a coin one block above the block, Core has a defined result, which neither program gives.

The scan follows the lookup of the inputs on a second cache, and it ends at a transaction whose inputs are missing.
At a transaction that would overwrite unspent outputs of its own transaction ID, the scan clears the entry and goes on, as Core's `ConnectBlock` does when its own cache lacks the entry.
It does not follow the other exits of `ConnectBlock`: BIP30, the scripts, the count of signature operations and the amounts of an earlier transaction, and an earlier transaction that fails its own sequence lock.
So it can name a read on a block that Core would reject before that read, where the revision gives the rejection. The comparison then fails, and it sends no such block.
For example, let the transaction at 1 have a height lock that is one block short, and the transaction at 2 a time lock on a coin above the block. The scan names `coinAboveBlock`, and the revision rejects the transaction at 1.

Agreement shows that the Lean rule equals Core's dormant code on these requests.
It does not show that the rule is right for Dogecoin, and a count says nothing about other heights or about unconfirmed transactions.
The comparison covers the rule of BIP 113 through `ContextualCheckBlock`, and the rules of BIP 112 and BIP 68 through `block.validate`, on made blocks and on mainnet heights 0 to 10,000.
No forced run of `block.validate` covers a mainnet block above height 10,000.
The time lock that is one second short, and the coins at heights 0 and 1, are on the made chain alone: the made blocks on real headers have the times of their headers.
This state does not occur on mainnet (`csv_never_lockedIn`).

### Block validation in the harness

`block.validate` keeps state in the harness for the length of one request: a block index, a coin set, and Core's version-bits cache.
`harness/core/core_block_validate.inc` holds the code.
Every verdict comes from Core's five functions.
The code builds their inputs, and makes these choices (design record 0010, section 5):

- **Script checks.** `nScriptCheckThreads` is 0 and `hashAssumeValid` is null, which are Core's values before `init.cpp` reads the node's options. So `ConnectBlock` checks every script of every input, in input order, with no check queue (D114, lines 1827 to 1849 and 1924).
  `main` calls `InitSignatureCache`, because `ConnectBlock` stores accepted signatures in that cache.
- **`fJustCheck`.** `ConnectBlock` runs with `fJustCheck` true on a new `CCoinsViewCache` over the carried set. With that flag it calls `CheckBlock` with both flags false (line 1804), and it returns before it writes undo data or the transaction index (line 2009).
- **Commit.** After an accepted block, the harness calls `SetBestBlock` and `Flush` on the cache, because `fJustCheck` returns at line 2009, before `SetBestBlock` (line 2035). After a rejected block, the cache is discarded, because `UpdateCoins` runs before the coinbase check (lines 1988 and 1996).
- **The carried set.** The set is a `CCoinsView` over a `std::map`, as `CCoinsViewTest` of Core's `src/test/coins_tests.cpp`, without that class's random choices. A flush erases an entry that is pruned. With `coins_db`, the set is in Core's `CCoinsViewDB` instead (see *The Core pass* below).
- **The block index.** The harness builds one `CBlockIndex` for each entry of `chain` and for each accepted block, with Core's skip list where the skip target is inside the chain. `mapBlockIndex` holds the entry of the last accepted block alone, which `CheckInputs` reads for the spend height (lines 1407 to 1411).
- **The BIP34 ancestor.** `ConnectBlock` reads the hash of the ancestor at `BIP34Height` (line 1877). Inside the supplied chain, the entry of that height gets the supplied hash. Below the chain, the oldest entry gets a predecessor that is its own predecessor and skip entry, as for `block.header_sequence`, so that `GetAncestor` returns it for every lower height.
- **Refusals.** The harness refuses a request whose chain is too short for Core's other reads: the median time, the retarget history, and the aligned version-bits boundary with its ten predecessors. So Core never reads the added predecessor as history.
- **Version bits.** The harness seeds `THRESHOLD_FAILED` at a boundary at or after the CSV timeout, as for `block.contextual_check_body` (design record 0010, decision 3). Below the CSV start, Core's walk stops at the aligned boundary.
- **The CSV window.** Inside the window, Core's `VersionBitsState` walks back one period at a time to a boundary whose median time is below the CSV start. It counts the versions of the blocks above that boundary (`versionbits.cpp`, lines 44 to 108). So the chain must reach the boundary and its ten predecessors, and each supplied entry above it needs a `version`. Otherwise the request is a request error. Each accepted block has the version of its header.
- **Restored state.** Every exit clears `mapBlockIndex` and the version-bits cache, and restores `fCheckpointsEnabled` and the mock time.
- **Snapshots.** With `coins_file`, the harness loads every record of the snapshot into the carried set, and reports the digest and the number of the records. Its checks and their order are those of the oracle's reader.

The harness alone takes more arguments ([design record 0011](design/0011-mainnet-ranges.md), section 3.2):

- `snapshot_heights` with `snapshot_dir`: a list of heights in increasing order, and the path of a directory. After the accepted block at each listed height, the harness writes the carried set as the snapshot `coins-<height>.bin` in that directory. It writes a temporary file first and renames it.
- `digest_heights`: a list of heights in increasing order. After the accepted block at each listed height, the harness computes the digest of the whole set.
- `version_bits_heights`: as in the oracle. The predecessor at each listed height can be the supplied one or an accepted block. The harness reports Core's `VersionBitsState` of CSV and SegWit for the block after it, with the checks of the CSV window above.
- `coins_db`, `coins_db_cache_mb` and `coins_db_continue`: the coin database of the Core pass (see *The Core pass* below).

The result then has `snapshots`, `set_digests` and `version_bits_states`, one entry for each listed height that the request reached, in order.
Both programs take `version` in an entry of `chain` and `version_bits_heights` ([the CSV window](#the-csv-window)).
An entry of `set_digests` has `height`, `set_digest_hex`, `set_coins`, `set_value`, and two values of Core's `GetUTXOStats` for the same set (`rpc/blockchain.cpp`, lines 874 to 905): `hash_serialized` and `transactions`.

`hash_serialized` is the hash in the byte order of the `gettxoutsetinfo` output. It covers the best block, and each transaction ID with the index, the amount and the script of each of its coins. It does not cover the height or the coinbase flag.
`transactions` is the number of transaction IDs with a coin.
An entry of `version_bits_states` has `height`, `csv` and `segwit`, with the names of `block.version_bits_state`.
An entry of `snapshots` has those fields, the hash of the block as `hash_hex` and `hash_display`, and `file`, `bytes` and `sha256` of the written file.
`scripts/snapshot_range.py` writes the manifest from that entry, after it computes each value again from the file.
The oracle returns a request error for the other arguments of this list.

One function of the harness, `visitSet`, walks the carried set, one `CCoins` entry at a time in the order of the transaction IDs.
The digest of the whole set and the snapshot writer read the set through it alone.

#### The Core pass

[Stage 0](#measurements-for-the-core-pass) chose Core's `CCoinsViewDB` for the Core pass, because the map does not fit in memory at the tip.
With `coins_db`, the path of a directory, the harness carries the set in a `CCoinsViewDB` in `<coins_db>/chainstate`, under one `CCoinsViewCache`.
Each block's cache reads that cache, as it reads the map otherwise.
After an accepted block, the harness writes the cache to the database when its `DynamicMemoryUsage` is above `coins_db_cache_mb` megabytes, 1,024 by default.
Core writes the coins and the best block in one LevelDB batch.
So the database always holds the set after one accepted block, and names that block.

For `visitSet`, the harness first writes the cache, and then walks the database's cursor.
The cursor visits the keys in LevelDB's byte order. A key is the byte `c` and the 32 bytes of the ID, so that is the order of the transaction IDs (`src/txdb.cpp`, lines 32 and 93 to 104).

Without `coins_db_continue`, the harness empties the database first, and loads `coins` or `coins_file` into it.
With `coins_db_continue` true, the request has neither, and the set is the one in the database.
The first block must then name the database's best block as its previous hash, or the request fails with the error `coins_db_best_block`.

A request with `coins_db` has no digest of the whole set in its block records.
Its result has `coins_db_start_display` and `coins_db_best_display`: the best block of the database at the start and at the end, in display order.
The harness writes one line to standard error after each accepted block whose height is a multiple of 10,000.
`coins_db_unusable` is the error of a directory that does not exist, or of a database that does not open.

`scripts/core_pass.py` runs the pass of design record 0011, section 3.2, with these arguments.
Each segment is one request, of at most 100,000 blocks and 4 GB.
The database persists from one segment to the next, so a segment does not load a snapshot.
This persistent database is how the pass implements the segments of section 3.2, as a detail of decision 3.
Each segment starts from the database with `coins_db_continue`.
So the harness requires that the database's best block is the last block of the segment before.
Each segment reports the digest of the whole set at its end.

The pass writes a snapshot at each range start and at each multiple of 500,000, and keeps only the newest of the latter.
A stopped harness can leave the database at another height than the pass's state. The pass then starts again from its newest snapshot below that height, which it loads into an empty database with `coins_file`.

The pass keeps the header of every accepted block. It builds the `chain` of each segment from them, with the version of each entry. Inside the window the chain reaches back to the boundary below the CSV start.
It requires each checkpoint of Core, and the digests of heights 100,000, 101,000 and 145,000 of the recorded runs of stage 1.
It requests Core's version-bits state at each period boundary.
With `--version-bits`, the script checks each state of a boundary in the CSV window. Both programs compute it again with `block.version_bits_state` on the kept headers from the genesis block.

With `--seed DIR --seed-height H`, the script starts a new state from the kept snapshot at height `H` of the pass in `DIR`, which it only reads.
It copies that snapshot and checks it against its manifest, and copies the headers to `H`.
The first segment then loads the snapshot with `coins_file`, as after a restart.
The new pass must reach each digest that the seed pass recorded above `H`, at its range ends and its segment ends.
It must also reach each version-bits state that the seed pass recorded.
It stops on any difference, and its state lists the heights that it checked.

The pass runs `core-oracle-trap`, which `scripts/build_core_harness.sh --trap-overflow` builds beside `core-oracle`.
That build compiles Core's `src/validation.cpp` and `src/coins.cpp`, which hold the sums of `ConnectBlock`, with `-fsanitize=signed-integer-overflow -fno-sanitize-recover=signed-integer-overflow`.
A signed overflow in those files then ends the program with a report, in the place of undefined behaviour (design record 0011, section 3.2).
Its `--version` output has `"trap_overflow": true`.

`scripts/test_core_pass.py` tests these parts in CI on the released heights 0 to 10,000:

- Three synthetic chains reach every state from `defined` to `failed`. At each of their boundaries, `version_bits_states` of `block.validate` equals `block.version_bits_state` of both programs on the whole chain. A chain one entry too short, and an entry in the window without a version, are request errors.
- Each small request of the [full comparison](#block-validation-comparison-evidence) gives one response with `coins_db` and a cache of 1 MB, and with the map. The digests of the block records are not compared.
- The pass of heights 0 to 10,000 runs in segments of 2,500 blocks. It reaches the digest of the map at heights 9,000 and 10,000, and so does its restart from the snapshot at 9,000. A wrong best block gives `coins_db_best_block`.
- `hash_serialized` and `transactions` at height 9,000 equal the values that the test computes from the snapshot file by the definition of `GetUTXOStats`.
- `scripts/run_range.py` runs heights 9,001 to 9,200 from the pass's snapshot at 9,000 in both programs, which reach the pass's digest at 9,200. A changed hash list and a changed committed manifest each fail.
- `scripts/restrict_coins.py` writes the *restricted coins* of those 200 blocks: 8,648 of the 114,056 coins of the snapshot. The restricted coins are the coins of the start snapshot whose transaction ID the blocks name, the set `T` of the [snapshot path](#coin-set-snapshots). The oracle gives the recorded block records on them. `scripts/compare_range.py` then runs both programs on them, and they agree. The restricted set ends with a digest other than the pass's. A missing coin entry, other expected records and a changed request without a new `SHA256SUMS` each fail. `scripts/restrict_coins.py` also fails when the source request of the run no longer has the SHA-256 of its summary.
- The trap build stops on the two requests of the arithmetic-domain cases whose sums leave the `int64_t` range, once in `validation.cpp` and once in `coins.cpp`. It gives the response of the ordinary build on the other requests of those cases.
- Nineteen supplied coins of `MAX_MONEY` and one of `MAX_MONEY - 1` give a set of 19,999,999,999,999,999,999 koinu, above 2^64. Both programs give that exact `set_value` with the coins in the request and in `coins_file`. The harness also gives it with `coins_db` and in the manifest of a written snapshot. The comparator accepts both responses, and they agree with its model.

The harness reads the changes of an accepted block from a second `CCoinsViewCache` over the set before the block.
For each transaction in order, it reads the entry of each input, calls Core's `UpdateCoins`, and reads the new entry.
So the spent and created coins are Core's own entries, as they are just before and just after each transaction.
The harness then requires that the second cache and the cache of `ConnectBlock` hold equal entries for every transaction ID that the block names.
It stops with exit status 3 if they differ.

### The comparison

`scripts/compare_core.py` gives each request its own `id` and sends both programs the same text, with one exception.
For a `block.validate` request in which the oracle reports `out_of_domain_at`, the harness gets the request without that block and the blocks after it ([the arithmetic domain](#the-arithmetic-domain)).
For supported requests, the two responses must be equal as JSON values, subject to the signature-preimage and Lean-diagnostic projections below.
For `script.eval` and `script.verify_legacy`, an unsupported Lean result excludes that request from verdict agreement.
The comparator validates both result shapes and the checker-specific unsupported reasons, then reports the unsupported reason and Core outcome separately.
An adapter error is not an unsupported result.

For `sighash.legacy` with plan `hash_bytes`, the double SHA-256 of the oracle's `preimage_hex` must equal Core's `digest_hex`.
This checks the preimage against Core's digest, not byte by byte against a preimage from Core.
Outside the checked `harness-refused` category, a request error from either program fails the comparison.

A full comparison with Core `e0a1c157791544e818c901bd9341896965afbf9d` sends 389,785 stream requests.
The table `EXPECTED_OPERATION_COUNTS` of `scripts/compare_core.py` gives the number of requests for each operation.
A full run fails with `REQUEST_COUNT` when the count of any operation differs from the table.
So a change to a request set changes the table, and this section, in the same pull request:

| `op` | Stream requests |
| --- | ---: |
| `auxpow.check` | 404 |
| `block.check` | 2,232 |
| `block.check_pow` | 806 |
| `block.check_version` | 207 |
| `block.contextual_check` | 2,903 |
| `block.contextual_check_body` | 22 |
| `block.header.read` | 7,878 |
| `block.header_sequence` | 257 |
| `block.subsidy` | 148 |
| `block.validate` | 42 |
| `compactsize.encode` | 26 |
| `compactsize.read` | 404 |
| `hash.hash160` | 292 |
| `hash.ripemd160` | 299 |
| `hash.sha1` | 519 |
| `header.encode` | 349 |
| `header.hash` | 347 |
| `header.read` | 25,865 |
| `merkle.compute` | 550 |
| `pubkey.verify` | 602 |
| `script.eval` | 8,882 |
| `script.read_op` | 1,233 |
| `script.verify_legacy` | 8,137 |
| `scrypt.hash` | 272 |
| `sighash.legacy` | 4,496 |
| `tx.check` | 1,384 |
| `tx.decode_base` | 37,694 |
| `tx.decode_witness` | 45,958 |
| `tx.read_base` | 137,991 |
| `tx.read_witness` | 42,286 |
| `work.calculate_next` | 49,255 |
| `work.get_compact` | 1,552 |
| `work.next` | 1,353 |
| `work.set_compact` | 5,140 |
| Total | 389,785 |

The four transaction-reader operations receive 263,929 of the requests.
Most of them are proper prefixes and field changes of corpus transactions.
`script.eval` and `script.verify_legacy` receive 17,019, and `block.header_sequence` receives 257.
So the total is mostly evidence about the transaction readers.

The pull request records the tested DogeLib revision.
The comparison passes with zero failures, including 12 checked harness refusals, plus 22 adapter-limit cases and the 1,193 two-call compositions.
The adapter-limit cases and the compositions run outside the stream, so the table does not count them.
With `--quick` or `--rust-compactsize`, the comparator sends a subset and does not check the table.

With `--mainnet-blocks DIR`, the comparator sends only requests on real mainnet blocks, 22,020 in all.
Of these, 11,001 are `block.check` requests on the [two ranges](#transaction-and-block-check-comparison-evidence).
The other 11,018 are [`block.contextual_check_body`](#contextual-block-body-comparison-evidence) requests on the two ranges and the 17 blocks of `tests/block/mainnet-blocks/rule-changes`.
One is the [`block.validate`](#real-mainnet-blocks-from-the-genesis-block) request that replays heights 0 to 10,000.
The comparator checks each count against `tests/block/mainnet-blocks/release.json` and the number of blocks in that directory.

The transaction inputs and targeted timelocks have these counts:

| Stream | Requests | Agreement | Unsupported | Harness-refused | Disagreements |
| --- | ---: | ---: | ---: | ---: | ---: |
| Transaction inputs, accept, base | 91 | 91 | 0 | 0 | 0 |
| Transaction inputs, unknown, base | 68 | 68 | 0 | 0 | 0 |
| Transaction inputs, accept, transaction | 91 | 91 | 0 | 0 | 0 |
| Transaction inputs, unknown, transaction | 68 | 68 | 0 | 0 | 0 |
| Legacy corpus, transaction | 925 | 925 | 0 | 0 | 0 |
| Legacy mutations, transaction, seed `20261106` | 2,000 | 1,956 | 44 flags | 0 | 0 |
| Public-key Wycheproof bitcoin | 464 | 464 | 0 | 0 | 0 |
| Public-key Core signatures and reversed digest one | 6 | 6 | 0 | 0 | 0 |
| Public-key parser boundaries | 20 | 20 | 0 | 0 | 0 |
| Public-key infinity constructions | 36 | 36 | 0 | 0 | 0 |
| Public-key x above order, including changed S and R | 72 | 72 | 0 | 0 | 0 |
| Signed recovery spends | 25 | 25 | 0 | 0 | 0 |
| Fixed-digest spends and their signature hashes | 115 | 115 | 0 | 0 | 0 |
| Targeted CLTV, transaction, seed `20261107` | 932 | 932 | 0 | 0 | 0 |
| Targeted CSV, transaction, seed `20261107` | 940 | 940 | 0 | 0 | 0 |
| Refusal precedence | 7 | 7 | 0 | 0 | 0 |
| Synthetic flag refusals | 8 | 0 | 0 | 8 | 0 |

Agreement in the unknown streams means agreement with Core on the input, not agreement with a fixture expectation.
All 91 independent Core acceptance requirements passed.
The 44 Script records and 60 transaction inputs that require signature verification each give a compared verdict.

All 932 CLTV requests and 940 CSV requests reach their target opcode by construction.
The comparator counts only Core acceptance or a `NEGATIVE_LOCKTIME` or `UNSATISFIED_LOCKTIME` rejection as evidence of the target opcode.
Any other Core outcome fails the run.
The outcome counts are CLTV: 151 accepted, 84 negative-locktime and 697 unsatisfied-locktime rejections.
CSV gives 414 accepted, 60 negative-locktime and 466 unsatisfied-locktime rejections.

`lake test` runs all 159 eligible transaction inputs with `verifyLegacySpend` and `coreVerifier`.
All 159 decode as complete base bytes, and the runner excludes the other 108 input records.
All 91 required acceptances accept.
For the 68 null expectations, 11 accept and 57 reject.
The null expectations supply counts only.

The request stream is deterministic, and the random sets use a fixed seed:

- The fixtures of `tests/oracle/`, except the request errors, `oracle.version` and the request that repeats a key.
  The script prints each fixture it leaves out.
- Core's `sighash.json`, and the base-mode records of Core's transaction corpus.
- Every proper prefix of every transaction of the two corpora, and each transaction followed by 1, 3 and 40 bytes.
- Field changes in the transaction corpus and the first 100 transactions of `sighash.json`.
  Each count and length is replaced by non-canonical forms, by `MAX_SIZE` and larger values, and by a truncated CompactSize.
  Also each version, sequence, output value and lock time replaced by boundary values.
- The same transactions rebuilt with no inputs, no outputs, or empty scripts.
- CompactSize values and encodings at every boundary of the forms and of `MAX_SIZE`.
- `sighash.legacy` on the first 25 transactions of `sighash.json`, at the boundaries of the input index and the hash type.
  Also transaction arguments that fail to read, and random script codes on all of its transactions.
- Random byte changes in the transactions of both corpora.
- All 198 transaction corpus records through both witness operations, with the 39 extended records also reported as a separate set.
- Every proper prefix of those 39 records through both witness operations, and each record with 1, 3 and 40 suffix bytes.
- Count, length and fixed-field changes in all 198 records through the witness operations, plus empty stacks, empty items and replacement stack contents.
- Hand-built cases from the known answers in `tests/KnownAnswers/Transaction.lean` (`Witness.cases`).
  They cover flags `02`, `03`, `ff`, zero flags, flags `01` with zero inputs, and errors before the flag check.
- 5,000 seeded byte mutations of the 198 records, each through both witness operations.
- The `large structured base` set, through both base operations and the transaction argument of `sighash.legacy`.
  It includes transactions with 253 or 254 inputs and outputs, 1000 inputs or outputs, and scripts of 4096 or 16384 bytes.
  Variants replace both vector counts, the first input script length and the first output script length with malformed encodings.
  They also truncate fields and scripts, and append trailing bytes.

The Script comparison reports these sets separately:

- Both scripts of every one of the 1,193 corpus records, as independent calls with empty initial stacks and unchanged effective flags.
  The comparison has no witness input: a record's witness is ignored, and only its two base scripts run.
- A composition for every record: `scriptSig`, then `scriptPubKey` with the first call's successful main stack.
  Each implementation supplies its own stack to its second call.
  A rejection or unsupported result ends that side's composition.
  The composition does not run `VerifyScript` or use the corpus's expected spending verdict.
  It ignores the record's witness and runs only the two base scripts.
- Eight synthetic legacy requests violate Core's flag dependencies, with each checker and flags 256, 2048, 2304 and 257.
  The comparator checks and excludes them as `harness-refused`.
- Every inside-milestone record through `script.verify_legacy`, separately with `base` and `transaction`.
  Each request uses the recorded spending transaction, input index and previous-output script.
- All 159 inside-milestone inputs of `tx_spends.jsonl`, with each checker and separate streams for accept and unknown expectations.
  Requests retain the exact transaction bytes, input index, previous-output script and flags.
  Core and Lean must accept all 91 accept inputs with the transaction checker.
  The run also fails if the number of acceptance checks differs from the size of that stream.
  The 68 null expectations supply outcome counts without fixture agreement claims.
- Targeted transaction-checker streams for CLTV and CSV under seed `20261107`.
  Each script pushes its operand, executes its named opcode, then drops the operand and pushes true.
  This construction reaches the target opcode without a signature check or an earlier Script error.
  Cartesian boundaries and 500 seeded cases per opcode vary version, locktime, sequence and operand.
  Boundaries include 499,999,999 and 500,000,000, equality, final sequences, versions 1 and 2, and disable and type bits.
- Seven refusal-precedence requests combine unsafe flags with malformed transaction bytes, trailing bytes, empty inputs or an out-of-range index.
  These errors must compare normally, without a harness-refused exemption.
- 2,000 legacy mutations for each checker, under seed `20261106`.
  Mutations change scriptSig, scriptPubKey, version, sequence, locktime or flags.
  A scriptSig mutation serializes a fresh length in a synthetic one-input transaction.
- Base-checker copies of the individual corpus evaluations, resource boundaries and 2,000 generated evaluations.
- Every opcode and every prefix of representative direct and extended pushes, including all short length-field and payload forms.
  Extra cases read at arbitrary offsets within push encodings and at the end.
- Below, at and above the 201-operation, 520-byte push, 1,000-item stack and 10,000-byte script limits.
  Cases include skipped branches, altstack moves and caller stacks above 1,000 items.
  Bounded pushes form accepted scripts of 9,999 and 10,000 bytes, followed by a 10,001-byte `SCRIPT_SIZE` case.
- 22 adapter-limit requests sent to both programs, 18 for Script and four for `pubkey.verify`, with results checked against the documented limits.
- 2,000 generated scripts under seed `20261105`, with nested conditionals, stack operations and numeric and hash candidates.
  Comparison depends on each returned capability result, rather than a fixed list of supported opcodes.

The work comparison reports these sets separately:

- D16's `bignum_SetCompact` cases and D7's six `get_next_work_*` cases from the oracle fixtures.
- Compact exponent, mantissa, sign and overflow boundaries, plus magnitudes around every bit boundary through 256 bits.
- Retarget timespan, rounding, height and parameter boundaries on all three networks, with UInt32 time endpoints.
  Spans −69, −68, −67, 307, 308 and 309 cover DigiShield's clamp edges for timespan 60.
  Spans −8, −7 and −6 cover the lower edge for regtest's timespan 1.
  The signed compact `0x04923456` checks that retarget arithmetic ignores the sign flag.
- The `regtest legacy wrap case`: selection height 0, last height 1, times 901 and 0, and bits `0x207fffff`.
  Core's multiplication wraps modulo 2^256, and returns `0x1f02467a`.
- Synthetic network chains at the legacy, DigiShield and minimum-difficulty boundaries, with strict delay endpoints.
- Testnet recovery walks to a nonminimum target or an interval boundary below height 145000.
- The 312 recorded mainnet headers as history for 310 candidates, heights 144721 through 145030.
  Height 144720 lacks its retarget ancestor and stays an oracle error fixture in the known-answer tests.
- A retarget whose ancestor traversal crosses a block with a null skip pointer.

The hash and block comparison reports these sets separately:

- All 315 recorded pure headers: fields, exact encoding, block hash and a three-byte suffix.
- Every proper header prefix, lengths 0 through 79, for all 315 records.
- Raw header field boundaries, including signed version bits and the AuxPoW flag.
- The 34 committed Merkle cases and three mainnet transaction-ID lists.
- Generated leaf lists of sizes 0 through 64, with aligned duplicates, complete-subtree duplicates and final-subtree extension.
- All committed RIPEMD-160 and Hash160 vectors, plus the 129 short and long NIST SHA-1 vectors and Core's ten SHA-1 vectors.
  These include million-byte inputs.
- The final input of each of 100 NIST SHA-1 Monte Carlo checkpoints.
  Python hashlib derives each 60-byte input independently, and NIST supplies the expected final digest.
  The comparator does not chain the oracle's intermediate digests.
  `lake test` checks the full 100,000-call chain.
- Generated binary hash messages of lengths 0 through 200 and around padding boundaries, up to length 1025, separately for each hash.

The fixture helper reads committed expectations and fixed header offsets independently of the executables.
The comparison checks complete results, including both byte orders, fields, consumption, remainder, truncation errors and mutation flags.
The Merkle caller bound is explicit, but the comparison uses only small lists.

`scripts/test_compare_core.py` checks that the comparison can fail.
A wrapper around the oracle stands in for the harness.
Unchanged, it must pass on the full stream. Each response mutation must fail with the failure code that it targets.
One case drops a `compactsize.encode` request from the full stream, and the run must fail with `REQUEST_COUNT` alone.

Only those two cases run the full stream.
Every mutation of the oracle and Core comparison runs the comparator with `--quick`.
Such a run has a reduced stream of 22,667 requests and the two-call composition of the first 32 corpus records.
It also makes the version and AuxPoW reconstruction calls.
A mutation changes one response of that run, or the wrapper's behaviour as a process.
A response mutation that finds no response to change fails its case.

The cases are separate runs of the comparator, four at a time by default, and `--jobs N` changes that number.
Each full-stream case holds about 3.5 GB of memory.

The witness mutations change `wtxid_hex`, a stack and `has_witness`.
The work mutations change the magnitude, both flags, the encoded compact and each work operation's result bits.

Hash mutations change each digest operation.
Block mutations change every header field, encoding, both hash orders, consumption, remainder and truncation.
They also change both Merkle root orders and the mutation flag.
Script mutations change reader fields, evaluation classes, rejection errors, success errors, final stacks and unsupported fields.
An informational Core result for an unsupported request can differ without a comparison failure.

One mutation corrupts a successful second-call stack of the composition path, and the failure must name that path.
Another gives an unsupported result an opcode absent from the script instructions.
Legacy mutations corrupt verdicts, add a forbidden stack, and invent unsupported results for either checker or Core.

Two refusal mutations replace either the required Core refusal or Lean's unsupported-flags answer with a verdict.
Each must fail with its own refusal error code, and the failed refusal must stay outside the compared count.
A transaction-corpus mutation makes Core reject an input with an acceptance requirement.
That mutation must fail the independent Core acceptance requirement.

Another mutation moves one required acceptance into the refusal path and must fail the acceptance-check count.
A targeted-stream mutation gives both programs the same `BAD_OPCODE` rejection and must fail the reached-opcode check.
Classifier assertions cover argument keys, index types and the `scriptSig` size boundary at 1,048,576 and 1,048,577 bytes.

### Compiled Rust CompactSize

With `--rust-compactsize PATH`, the comparator selects only `compactsize.read` from the fixtures and CompactSize boundary set.
It sends all three programs the same 404 reader requests and compares their full responses.
The Rust crate has no encoder.
The comparator reads the oracle's version at runtime and passes it to the adapter.
The adapter identifies its projection as `FORMAT-rust-compactsize`.
[BUILDING.md](../BUILDING.md#compiled-rust-compactsize-comparison) gives the commands.

The comparator self-test also includes a three-way positive control and eight Rust-side mutations.
These mutations change consumption, the read error, the remainder, request acceptance, response count, response ID, JSON syntax and the version label.
Each mutation must fail with its expected code.

Agreement covers the requests in the stream and nothing more.

Public-key mutations flip a `valid` field and fail with `PUBKEY_VALID`.
A mutation changes the signed recovery spend's verdict and fails with `SIGNATURE_VERDICT`.
The public-key stream includes all 464 bitcoin Wycheproof cases, with Core as the verdict source, including high S.
It includes key-parser boundaries and four Core-signed inputs, plus two reversed digest-one inputs.

The [fixture notes](../tests/cryptography/secp256k1/README.md) give the provenance and arithmetic of the constructed edge cases.
The 36 infinity inputs reject, and the 24 x-above-order inputs accept.
All 24 changed-S inputs reject.
Another 24 inputs retain the verification point above `n` but claim a different R scalar, and all reject.
These comparisons give finite evidence about verdicts, not a theorem that `mulAdd` equals Core's `secp256k1_ecmult`.

### Header proof-of-work evidence

The harness builds with `--disable-scrypt-sse2` and calls `scrypt_1024_1_1_256_sp_generic` for `scrypt.hash`.
Its build stamp records the Core revision, configure options, compiler versions, host architecture and flags.
`CheckAuxPowProofOfWork` also uses generic scrypt in this build.
Core's error logging goes to a harness `LogPrintStr` sink on standard error.
The sink changes no returned verdict and keeps logs outside the JSONL stream.

The full-header reader uses Core's `CBlockHeader` reader with the requested stream mode.
The predicates call `CAuxPow::check` and `CheckAuxPowProofOfWork` directly.
For proof of work, Core selects the actual record with `Params().GetConsensus(selection_height)`.
The harness does not reproduce that parameter table.

`core-oracle --check-auxpow-fixtures` reconstructs the 26 deterministic cases of Core's `check_auxpow` with Core's classes.
The adaptation preserves their construction order and replaces assertions with serialized records and Core verdicts.
The standalone harness omits the test's chain lock because it has no concurrent chain state.
Every comparison run requires exact payload bytes, arguments and verdicts to match `tests/block/check-auxpow.json`.
The comparator also checks the 16 boundary payloads and all six historical AuxPoW payloads against committed verdict expectations.

[The Core fixture report](../tests/block/core-header-pow.json) records all 321 historical header verdicts.
Each entry identifies exact bytes by SHA-256 in the existing header fixtures and gives the selected height.
The report names the network, the three relevant parameters, the Core revision and the scrypt variant.
All 321 headers pass Core's proof-of-work check, including six complete AuxPoW headers.
The fixture loader checks the report's identities and parameters before the comparison.

The header comparison includes these streams:

| Stream | Requests | Compared result |
| --- | ---: | --- |
| Header PoW fixtures | 407 | Sixteen exact scrypt digests, 321 historical header verdicts, 48 payload verdicts and 22 mined-case replays |
| Full header readers | 7,878 | Complete decoded fields, consumption, remainder or read error in both modes |
| Version boundaries | 207 | Two version gates at activation, record-selection and signed-version boundaries |
| Mutations, seed `20261108` | 1,075 | Payload/script mutations, version bits, nonces and child/parent `nBits` |

One hundred script mutations recompute the parent Merkle root to retain the coinbase-to-parent binding.
These mutations exercise the merged-mining search after the binding check passes.
Other reader cases cover malformed branch counts, optional transaction flags and empty witness stacks.
The comparison checks fixture expectations independently of cross-implementation equality.

The self-test changes each operation's compared result and requires `SCRYPT_DIGEST`, `FULL_HEADER`, `AUXPOW_VERDICT`, `HEADER_POW` or `HEADER_VERSION`.
A reconstruction-byte mutation must fail with `AUXPOW_RECONSTRUCTION`.
Assertions also check that a Lean diagnostic difference is ignored and that an integer cannot replace a Boolean verdict.
These checks supply finite comparison evidence, not an all-input equivalence theorem with Core.

`core-oracle --auxpow-pow-fixtures` ports `mineBlock` and `auxpow_pow` from pinned Core lines 327 to 451.
It mines the nonces again on every Core comparison and records all 12 predicate assertions.
It also records the 11 mining assertions and the two version/hash assertions.

All assertions must match Core's source expectations, and all captured bytes must match [the comparison records](../tests/block/auxpow-pow.json).
Lean and Core replay the 12 cases from identical pure-header and nullable payload bytes.
Ten cases also replay through the full-header reader.
The two flag/payload mismatches require split inputs.
These records are snapshots of runtime-mined comparison cases, rather than independent fixed known answers of the source test.

[The capture script](../scripts/capture_header_pow.py) records both header reports without running Lean.
The reports name their generator and capture date.
The [fixture notes](../tests/block/README.md#core-header-proof-of-work-report) give the exact capture command.
A mined-byte self-test mutation must fail with `AUXPOW_POW_RECONSTRUCTION`.
A separate verdict mutation targets the `payload_hex` path and must fail with `HEADER_POW`.
An extra diagnostic field on a full-header reader response must fail with `FULL_HEADER`.

### Contextual header comparison evidence

The harness calls Core's `ContextualCheckBlockHeader` (D33, lines 3066 to 3119).
The verdict is its return value, and the reject reason is `GetRejectReason` of its `CValidationState`.
Earlier revisions used a transcription of that function, H2 of [design record 0006](design/0006-contextual-header-validation.md#82-the-core-side).
The harness no longer contains it.

The harness sets Core's `fCheckpointsEnabled` and fills Core's `mapBlockIndex`.
Each known height adds the corresponding table hash with that height to the block index.
The remaining harness trust is the in-memory index.
The harness builds the `CBlockIndex` entries and their links from the request, and it refuses a view that is too short.
Core's function does not reach `VersionBitsState`, so the request needs no version-bits history.

The contextual stream contains these requests:

| Stream | Requests | Compared result |
| --- | ---: | --- |
| Contextual fixtures | 2231 | Verdict and first reject reason |
| Contextual boundaries | 172 | Verdict and first reject reason, checked against hand derivations |
| Contextual mutations, seed `20261109` | 500 | Verdict and first reject reason |

The fixture stream uses real mainnet candidates from five header ranges.
Chain acceptance supplies their expected verdicts with adjusted time equal to the candidate time and no known checkpoints.
The 172 boundary expectations follow D33 and the hand derivations in `KnownAnswers.ContextualCheck`.
They cover all seven checks, first-failure order, medians near genesis and out of order, equivalent-target compact encodings, checkpoint equality and disabled checkpoints.
They also cover signed versions, the future-time bounds, AuxPoW and BIP heights on all networks, and testnet delay boundaries at candidates 100001, 157500 and 157501.

A further 500 requests mutate version, time, bits, adjusted time or known checkpoints with seed `20261109`.
They use 167 mainnet, 167 testnet and 166 regtest contexts.
Mainnet and testnet checkpoint mutations include table heights above the candidate, which can produce `bad-fork-prior-to-checkpoint`.

The comparator self-test corrupts `valid` and `reject_reason` independently.
These mutations must fail with `CONTEXTUAL_HEADER`.
A third mutation swaps one rejection string for another on a request without an independent expectation.
That mutation preserves the response shape and must fail the stream comparison of result values.
It also checks Boolean types, result fields, acceptance reasons, rejection reasons and the exclusion of Lean diagnostics.
These runs give finite evidence, not an all-input equivalence theorem with compiled Core.

### Transaction and block check comparison evidence

The harness calls Core's own `CheckTransaction`, `CheckBlock` and `GetLegacySigOpCount` (D106), on objects that Core's stream code reads.
The comparator requires equal `ok` fields, except the oracle's `diagnostic`, and equal `error` objects.
It also checks both sides against Core's text: the score and the corruption flag of each reason, and the reject code 16.
It checks the block hash against `hashlib`, and `base_size` against the byte count in base mode.
A full run fails with `REASON_NOT_REACHED` if Core never returns one of the reachable reasons of design record 0010, section 4.
`bad-txns-oversize` is exempt for `block.check`: the size test of `CheckBlock` (line 2972) comes first, and both programs return `bad-blk-length`.

The 3,616 requests of the full run are in ten sets, defined in `scripts/oracle_block_check.py`:

| Set | Requests | Contents |
| --- | ---: | --- |
| Known answers | 61 | One case or more for each reason, with the expected result read from Core's text |
| `tx.check` reasons | 242 | Each reason of `CheckTransaction` with its boundary values, both values of `check_duplicate_inputs`, and pairs of faults in each order |
| `block.check` transaction reasons | 222 | The same faults in a transaction of a block |
| `block.check` reasons | 448 | Each reason of `CheckBlock`, with the four combinations of the two flags. Mutations of the mainnet genesis block and of synthetic blocks, and Merkle duplications at the leaf level and one level above |
| Signature operations | 724 | Exactly 20,000 and 20,001 operations, both multisig opcodes after each of `OP_1` to `OP_16`, short pushes that hide later opcodes, opcode bytes in push data, and a coinbase `scriptSig` |
| Readers and witness data | 976 | Every proper prefix of a small block, bytes after a block, counts above `MAX_SIZE`, counts that are not canonical, the extended format in both modes, and unknown optional data |
| Real full headers | 402 | The mainnet full headers of [the AuxPoW activation fixture](../tests/block/mainnet-auxpow-activation-full-headers/README.md) before a synthetic transaction list, with `check_pow` true and `check_merkle_root` false |
| Size limits | 16 | Transactions and blocks of exactly 1,000,000 and 1,000,001 base bytes |
| Mainnet rule changes | 168 | The 17 real blocks at and next to the rule changes of design record 0010, with both flags in both modes, and four mutations of each block ([fixture](../tests/block/mainnet-blocks/README.md)) |
| `tx.check` corpus | 357 | The records of `tx_valid.json` and `tx_invalid.json` (D28, D29), with no expected value: agreement of the two programs |

Every request agrees.
In the full run Core returns each of the seven reasons of `CheckBlock` 30 times or more.
It returns each of the nine reasons of `CheckTransaction` 3 times or more.
`scripts/test_oracle.py` checks 3,233 requests that have an expected value, and 25 argument errors, without Core.

#### Real mainnet blocks

`scripts/fetch_blocks.py` read three sets of blocks from the maintainer's mainnet node on 2026-11-13, and checked each block before it wrote a fixture.
[The fixture README](../tests/block/mainnet-blocks/README.md) records the source, the checks, the sizes and the label of each block.

| Set | Heights | Blocks | `pinned` | `linked` | Compared in |
| --- | --- | ---: | ---: | ---: | --- |
| Rule changes | 144,998 to 145,001, 371,336 to 371,338, 599,998 to 600,001, 1,034,382 to 1,034,384, 3,464,750 to 3,464,752 | 17 | 17 | 0 | The full run, set *Mainnet rule changes* |
| Genesis to 10,000 | 0 to 10,000 | 10,001 | 10,001 | 0 | `--mainnet-blocks` |
| Recent | 6,455,302 to 6,456,301 | 1,000 | 0 | 1,000 | `--mainnet-blocks` |

A `pinned` block has a hash that a committed fixture or a Core checkpoint gives.
A `linked` block has no pinned hash.
It is consistent with its header and with its neighbours, and its place in the chain rests on the node.
The linked blocks are the whole recent range.
The blocks at heights 599,998 to 600,001 match a committed header fixture.
The node and two public TLS Electrum servers agreed on those bytes, but no checkpoint connects to that range.

The rule-change blocks are committed.
The two ranges have 44.0 MB and 19.9 MB, so they are assets of a GitHub release (design record 0010, decision 2).
`python3 -I scripts/fetch_release_blocks.py` downloads them, requires the SHA-256 values of the committed `tests/block/mainnet-blocks/release.json`, and repeats the checks of the fetch.
Then this command compares every block of both ranges:

```bash
python3 -I scripts/compare_core.py --mainnet-blocks build/mainnet-blocks .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

Each request has `check_pow` and `check_merkle_root` true, in the mode `allow_witness`.
Both programs must return a valid verdict, with the hash and the number of transactions of the manifest.
The expected base size is the size of the block without the witness data of the parent coinbase in its AuxPoW payload.
Three blocks of the recent range have such data, 36 bytes each.

All 11,001 requests agree.
The run fails with `BLOCK_ASSETS` when a file is absent or does not have its committed hash.
It fails with `REQUEST_COUNT` when the stream does not hold one request for each block of `release.json`.

The ranges are a separate run, not sets of the full run.
The comparator's self-test repeats the full run twice, with the oracle in both places.
On a development machine the oracle takes about 70 seconds for the 11,001 blocks, and Core takes about 3 seconds.
The largest sigop count of a block is 3,367, so the cost of [issue 149](https://github.com/dghelm/DogeLib/issues/149) does not show on these blocks.

This closes exit condition 1 of stage 0010a for `block.check`.
[`block.contextual_check_body`](#contextual-block-body-comparison-evidence) closes the other part.
`python3 -I scripts/test_fetch_blocks.py` and `python3 -I scripts/test_fetch_release_blocks.py` test the checks of the two fetch scripts on synthetic blocks.

Three cases have no request.
A block with more than 1,000,000 transactions has at least 10 MB, and the size clause rejects it too.
A sigop product that wraps modulo `2^32` needs `2^30` operations.
The strict chain ID rule through `block.check` needs a mined mainnet header, and `block.check_pow` covers that rule.

Until [issue 149](https://github.com/dghelm/DogeLib/issues/149) was fixed, the oracle's sigop count took time that grew with the square of the number of instructions.
A `tx.check` request whose one input has a `scriptSig` of 80,000 `OP_0` bytes (`0x00`) took about 3 seconds with the oracle of `main` at `bf5598e`.
So the requests of a megabyte hold one large push, and no request has more than about 30,000 separate opcodes in one script.
The count now reads with `nextOp`, in time linear in the length of the script.
The same request takes 0.04 seconds, and one with 1,000,000 `OP_0` bytes takes under 0.5 seconds.
Each time is the best of a few runs of the oracle on one core of a shared development machine, at nice 19.

### Contextual block body comparison evidence

The harness calls Core's own `ContextualCheckBlock` (D33) on a `CBlock` that Core's stream code reads.
The harness builds the predecessor and the version-bits boundary from the chain.
The comparator requires equal `ok` fields, except the oracle's `diagnostic`.
It also checks both sides against Core's text: the score of each reason and the reject code 16.
A full run fails with `REASON_NOT_REACHED` if Core never returns one of the four reachable reasons of design record 0010, section 4.

The 22 requests are in six sets, defined in `scripts/oracle_contextual_body.py`:

| Set | Requests | Contents |
| --- | ---: | --- |
| Valid | 3 | The genesis block, and final blocks below the first period |
| Finality | 5 | A non-final lock time by time and by height, a final sequence, lock time 0, and a non-final coinbase |
| Coinbase height | 8 | `bad-cb-height` at a period boundary, the exact boundary 1,034,382 and 1,034,383, a short height, and valid heights at the BIP65 boundary |
| Witness | 2 | Witness data in a transaction and in the coinbase |
| Weight | 2 | Blocks of exactly 1,000,000 and 1,000,001 base bytes |
| Version bits | 2 | A boundary below the CSV start (case 1) and one at or after the CSV timeout (case 2, seeded `FAILED`) |

The height boundaries use a contiguous chain back to the aligned version-bits boundary, about 6,200 entries for 1,034,383 and 7,300 for 3,464,751.
The other requests use a short chain, so the six sets add about 39,600 chain entries in all.
Every request agrees, and Core returns each of the four reasons.
`scripts/compare_core.py --mainnet-blocks` also compares the body on 11,018 real blocks: the genesis-to-10000 range, the 1,000 most recent blocks and the 17 rule-change blocks.
Below the first period the chain is the predecessor alone, and otherwise it reaches the aligned boundary from the committed blocks and the version-bits header runs of `tests/block/mainnet-blocks/version-bits-headers`.
`scripts/test_oracle.py` checks the 22 requests against their expected verdicts without Core.

### Block validation comparison evidence

The harness calls Core's own five functions, as [above](#block-validation-in-the-harness).
The comparator requires equal block records, except the oracle's `diagnostic`, and an equal digest and size of the final coin set.
It checks both sides against Core's text: the score and the code of each reason of `ConnectBlock`.
A full run fails with `REASON_NOT_REACHED` if Core returns one of the nine reachable reasons of design record 0010, section 5, for no block.

The 42 requests are in eight sets, defined in `scripts/oracle_block_validate.py`.
They need no download.
One request starts at the real genesis block.
The others start at a committed rule-change block: each keeps the real header and chain of that block, replaces the transactions and the Merkle root, and clears `check_pow`.
Their coins are synthetic.

| Set | Requests | Contents |
| --- | ---: | --- |
| Genesis chain | 2 | The genesis block with its real proof of work. A chain of 33 made blocks on the genesis block, with 17 rejected candidates: maturity 30 at depth 29 and 30, the genesis coinbase, unspendable outputs, a missing index, a double spend within a block, a spend of an output that the block creates later, a spend within the block, `bad-txns-in-belowout`, and four script failures |
| Coinbase maturity | 7 | Depth 29 and 30 for a coin below height 145,000, depth 239 and 240 from it, a coin of maturity 30 spent above height 145,000, and a coin above the spend height |
| Values and coinbase limit | 7 | `bad-txns-inputvalues-outofrange`, `bad-txns-in-belowout`, a coin of `MAX_MONEY`, and a coinbase that claims one koinu too much at heights 145,000, 599,999 and 600,000, with and without a fee |
| Arithmetic domain | 5 | Nine fees of `MAX_MONEY` in one block, which Core accepts. A tenth fee, and ten coins of `MAX_MONEY` in one transaction, which end the range. A supplied amount above `MAX_MONEY` |
| Signature operations | 3 | Exactly 20,000 operations, and 20,001 by a P2SH input, by a later transaction, by a legacy operation in an output and by one in the coinbase. The accurate count of `OP_16 OP_CHECKMULTISIG`. A `scriptSig` that is malformed, has an opcode above `OP_16`, or ends with an opcode that pushes nothing, each of which counts 0 |
| Script failures | 8 | A signature that is not strict DER below and from `BIP66Height`, with a right and a wrong signature. `OP_CHECKLOCKTIMEVERIFY` below and from `BIP65Height`. The predecessor at `BIP34Height` and above it |
| BIP30 | 4 | A coinbase and another transaction whose IDs have unspent coins. The same coinbase with the ancestor hash `BIP34Hash`, where Core skips the test and replaces the entry |
| Order and adapter errors | 6 | One block for each of the five steps, with a later fault in each. A truncated block, bytes after a block, and the three chain errors |

The expectations come from Core's text.
`scripts/oracle_block_validate.py` also computes every digest a third time, from the definition [above](#digests), in a model of the coin set that takes the verdicts from the expectations.
All 42 requests agree with Core and with the expectations.
The block records hold 60 accepted blocks and 54 rejected ones, and Core returns each of the nine reasons.

The signatures are made in the script with the private key 1, which is public test data.
A signature that is not strict DER has one more zero byte before R.
Core's verdict on each signature comes from the comparison, not from the script.

The request of the tenth fee is the example of design record 0010, section 3.
The oracle returns `out_of_domain_at`, and the harness gets the request without that block.
So no request makes Core add past the `int64_t` range.

`scripts/test_oracle.py` checks the 42 requests against their expectations without Core.

#### Real mainnet blocks from the genesis block

`scripts/compare_core.py --mainnet-blocks` sends one more request: all 10,001 blocks of heights 0 to 10,000, in one `block.validate` request with an empty chain and no coins.
Both flags are true, so each block passes its real proof of work.
Each program builds the whole coin set.

Both programs accept every block, and all 10,001 block records agree.
So do the 11 digests of the whole set, at each multiple of 1,000 and at the end.
The blocks have 155,931 transactions.
They spend 197,189 coins and create 340,566, and the final set has 143,377 coins.
Every spent output in the range is Pay to Public Key Hash or Pay to Public Key, so each input runs one ECDSA verification.

On a development machine the oracle takes about 460 seconds for this request on one core, and Core takes about 12 seconds.
The comparator runs the request in a second oracle process, at the same time as the other requests of `--mainnet-blocks`.
The default timeout of that mode is 3,600 seconds.

This closes the first part of exit condition 1 of stage 0010b: agreement on the genesis-to-10,000 range, digests included.
The recent range needs supplied coins, which design record 0011 takes from a coin-set snapshot.
The range to height 145,000 is a gate outside CI, and the next section records its runs.
Neither is in this comparison.

#### Replay of mainnet to height 145,000

`scripts/replay_blocks.py` replays mainnet from the genesis block to height 145,000, the whole random-reward era.
It is the gate *Mainnet replay to 145,000* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.
This section records a run that started on 2026-11-19 and ended on 2026-11-20.
It also records a later run, which compares the [total value](#total-value) of the coin set as well.

The script checks the two fixtures against their manifests and requires a pinned hash for every block.
It writes all 145,001 blocks to one file of 3,024,443,782 bytes, with the SHA-256 value `5295801124f275bd7b6aad9f60bc734631e8157d99a07d8a9c66ee8f2bd034e3`.
Each program gets one request that names the file through `blocks_file`, with the empty chain, the empty coin set and both flags true.
So each block passes its real proof of work, and each program builds the whole coin set.

| Input | Value |
| --- | --- |
| Oracle | Built from commit `873f0da` of pull request 170, which is `main` at `f7aeb10` with the file argument |
| Core harness | Built from the harness sources of the same commit, with Core at `e0a1c157` |
| Heights 0 to 10,000 | The release asset of the [fixtures](../tests/block/mainnet-blocks/README.md), 10,001 blocks |
| Heights 10,001 to 145,000 | `scripts/fetch_blocks.py --range 10001 145000` from a node `/Shibetoshi:1.14.9/` on 2026-11-18: 135,000 blocks, 2,979,346,409 bytes, SHA-256 `b3354074540c702ffa8f958a1276c4fb8c911a9be461d6f89e8980ef2c0c7f14`. The file is not committed and is not a release asset |

Later commits of the pull request change the answer to a failed read of the file alone, and no read failed in this run.

Both programs accept every block, and all 145,001 block records agree, each with the digest of its coin changes.
So do the 147 digests of the whole set, at each multiple of 1,000 and at the end.
The blocks spend 15,048,625 coins and create 20,143,296.
The set after height 145,000 has 5,094,671 coins, and its digest is `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d`.
The last block has the hash `cc47cae70d7c5c92828d3214a266331dde59087d4a39071fa76ddfff9b7bde72`.
No block leaves the arithmetic domain: `out_of_domain_at` is null.

The oracle took 61,365 seconds, about 17 hours, on one core at low priority, on a machine that ran other work.
Its resident memory was 7.6 GB when it passed height 112,000.
Core took 1,340 seconds.

An earlier run used an oracle from before pull request 173, which made block reads and signature hashes faster and changed no result.
That run took 149,428 seconds for the oracle.
Its response is byte for byte the response of the run above, so two builds of the oracle agree with Core on this range.

A later run used the oracle and the Core harness built from commit `18310a8` of pull request 175, which added `set_value` and merged as `3a8401b`.
It read the same blocks, from a file with the same SHA-256 value.
The command is the one of the gate in [AGENTS.md](../AGENTS.md#checks), run with `taskset -c 6 nice -n 19`.
It started at 2026-11-20T16:50:34Z and ended at 2026-11-21T11:59:26Z, and it exited with status 0.

Both programs accept every block, and the block records, the 147 digests and the 147 totals of the whole set agree.
The counts of coins, the digest of the set and the hash of the last block are those of the run of 2026-11-19.

| Quantity | Koinu |
| --- | --- |
| `set_value` after height 145,000 | 6,117,565,627,100,000,000 |
| Sum of the subsidies of heights 1 to 145,000 | 6,122,723,674,900,000,000 |
| Subsidy sum minus `set_value` | 5,158,047,800,000,000 |

Both programs gave the same subsidy for each height from 1 to 145,000.
Each of the 147 totals is at most the subsidy sum up to its height, which is the bound of `chain_issuance_bound`.
The check does not say why the set holds less than the subsidy sum.

The oracle took 67,606 seconds, about 19 hours, on one core at low priority, on a machine that ran other work.
Core took 1,283 seconds.

The runs are evidence for these blocks alone.
A node supplied the blocks above height 10,000.
Each has a pinned hash, and the [fixtures](../tests/block/mainnet-blocks/README.md) state what a pinned hash commits to.
Blocks above height 145,000 are not replayed.

#### Ranges from a snapshot

`scripts/snapshot_range.py` runs a range of mainnet blocks from a [coin-set snapshot](#coin-set-snapshots) in both programs.
It is the gate of [design record 0011](design/0011-mainnet-ranges.md), stage 1, which tests the snapshot path on blocks that the replay from the genesis block covers.
A range from the height `a + 1` to the height `b` starts from the snapshot at `a`.

The script first lets the harness replay the blocks from the genesis block, from the empty coin set.
In that *pass* the harness writes each snapshot and reports the digest of the whole set at `b`.
The script computes the SHA-256, the digest, the number of coins and the total value of each snapshot again from the file.
It requires the values of the harness and the committed [manifest](../tests/block/mainnet-blocks/README.md#coin-set-snapshots).
Both programs then get one request with `coins_file` and the blocks of the range.
A range agrees when all of these hold:

- Both programs report the digest and the number of coins of the manifest as the start.
- Both programs accept every block, with equal block records.
- Both programs report the digest of the pass at `b` as the end.
- The block records equal those of the same heights in the pass, without the digests of the whole set.
- The oracle with `coins_in_memory` returns the same `ok` object.

The script also runs 29 changed copies of the snapshot, each with the first 10 blocks of the range, in both programs:

| Change | Cases | Required result |
| --- | ---: | --- |
| Another amount, script, height or coinbase byte in one record. A removed record and an added record | 6 | Both programs report a start digest that is not the manifest's. It is the digest that the script computes from the changed file. The script also accepts the error `not_linked` from both programs, after a block that the changed coin makes both reject. In the two recorded runs, all six gave a changed start digest |
| Two records in the wrong order, and one record twice | 2 | `coins_file_order` |
| A file that ends inside a record, and a byte after the last record | 4 | `coins_file_truncated` |
| Each other fault of the [checks](#coin-set-snapshots): the tag, the entry, the amount with the values `MAX_MONEY` + 1, -1 and another negative number, the index, the script, the height, the coinbase byte and the length of the script | 15 | The error of the fault, with the position of the record |
| A removed record whose transaction ID a block of the request names | 1 | A changed start digest, or the error `not_linked` after a block that both programs reject |
| A removed record whose transaction ID no block of the request names | 1 | Both programs return the block records of the unchanged snapshot. The start digest and the end digest differ from those of the unchanged snapshot |

The last step runs the 33 small requests of the [full comparison](#block-validation-comparison-evidence) that have one record for each block, with their coins in a snapshot.
Both programs must return the result of the request with `coins`, without the digests of the whole set in the block records.
The start digest must be the one that `Model` of `scripts/oracle_block_validate.py` computes.
These requests hold rejected blocks, the BIP30 cases and the script failures.
`scripts/test_oracle.py` runs the same requests and 33 changed synthetic snapshots or requests in the oracle alone.

**The short form.**
CI runs the script on the released blocks of heights 0 to 10,000, with the snapshot at height 9,000.
The snapshot has 114,056 coins and 8,719,196 bytes.
Heights 9,001 to 10,000 agree: the blocks spend 47,185 coins and create 76,506, and the set after height 10,000 has the 143,377 coins of the replay.
On a development machine the run takes about 160 seconds on two cores, of which each oracle run of the range is about 106 seconds.

**Range S.**
This part records one run of range S of the design record, heights 100,001 to 101,000, on 2026-11-20.
It is the gate *Snapshot range S* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.

| Input | Value |
| --- | --- |
| Oracle and Core harness | Built from commit `f42b049` of the pull request, with Core at `e0a1c157` |
| Blocks | The fixtures of the [replay to height 145,000](#replay-of-mainnet-to-height-145000). The file of all 145,001 blocks has the SHA-256 value `5295801124f275bd7b6aad9f60bc734631e8157d99a07d8a9c66ee8f2bd034e3` of that replay |
| Command | The gate command, with `--write-manifests`, because the run wrote the two committed manifests |

The pass took 1,524 seconds, and the harness accepted every block.

| Snapshot | Coins | Bytes | Digest of the set | SHA-256 of the file |
| --- | ---: | ---: | --- | --- |
| Height 100,000 | 5,556,212 | 422,359,596 | `dda64f97c6bc79ee64954d5e95ba26fb207c15b5255ffd041be333d6cbe4e817` | `fc9a4ebf7a2ef72a555aa1caf06583160d1e5785d18738cca729d3cd3783bca9` |
| Height 145,000 | 5,094,671 | 387,316,918 | `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` | `0fa2f2a1e1aa43c54bf877e5aed1884cb9731412c45a06c9b8a9c84ad0b32012` |

The snapshot at height 145,000 has the number of coins and the digest of the recorded replay.
The script holds both values as constants and requires them in every run.
So the harness's snapshot at that height is the set that the oracle reached from the empty set, if double SHA-256 is collision resistant.

Range S agrees.
Both programs start from 5,556,212 coins with the digest of the manifest, and accept all 1,000 blocks with equal block records.
The blocks spend 121,665 coins and create 151,427.
Both programs end with 5,585,974 coins and the digest `e6aeca49614547750a803c3d4dd85f6986f69f819a207531f896e1aa7840aa1b`, which the pass reports at height 101,000.
The block records equal those of the pass at the same heights.
The oracle with `coins_in_memory` returns the same `ok` object.
All 29 changed snapshots give their required results.

Core took 18 seconds for the range.
The oracle took 682 seconds on the coins that the blocks name, with its two reads of the snapshot, and 728 seconds with `coins_in_memory`.
A separate run of the first form alone had a peak resident memory of 317 MB.
The whole run took about 60 minutes on four cores at low priority, on a machine that ran other work.

The run is evidence for these blocks, and it is one run.
It tests the snapshot path: every block of the range is also in the replay from the genesis block, so the range adds no agreement on a new block.
The oracle did not check the blocks between heights 101,001 and 145,000 in this run.
The hypothesis of section 3.4 of the design record applies to every later range from a snapshot: the comparison does not show that the snapshot is Core's coin set.

#### Measurements for the Core pass

Stage 0 of [design record 0011](design/0011-mainnet-ranges.md) measures the chain, the coin set at the tip, and the memory of the harness.
The stage decides whether the Core pass fits the development machine, and whether the harness carries the set in its map or in Core's `CCoinsViewDB`.
The measurements were made on 2026-11-20.

**The node.**
The node is `/Shibetoshi:1.14.9/`, and the measurements read it over read-only RPC.
At height 6,465,793, with the block hash `9ebb986b0b16a65680c5f3447baca7154e2999680c76c97f24c4441897bc7385`, the node reported these values:

| RPC value | Value |
| --- | ---: |
| `getblockchaininfo` `size_on_disk`: the block files and the undo files (`CalculateCurrentUsage`, `validation.cpp`, lines 3440 to 3449) | 204,053,139,409 bytes |
| `gettxoutsetinfo` `transactions`: the transaction IDs with an unspent output | 181,209,861 |
| `gettxoutsetinfo` `txouts`: the coins | 202,470,869 |
| `gettxoutsetinfo` `bytes_serialized`: 32 bytes and the stored value of each transaction ID (`rpc/blockchain.cpp`, lines 874 to 905) | 11,466,045,328 |
| `gettxoutsetinfo` `hash_serialized` | `a053d324494c91478b7e8525f52b062b56e976c61ef856509d59d33360048680` |
| `gettxoutsetinfo` `total_amount` | 156,830,432,860.16806 DOGE |

`gettxoutsetinfo` ran once and took 198 seconds.
The block files alone have no RPC value, so the sample below estimates them.

**The chain.**
`scripts/count_blocks.py --sample-heights --last 6465793` splits the heights from 0 to 6,465,793 into strata of 1,000 heights, and draws one height from each with the seed 20261120.
`scripts/fetch_blocks.py --heights` fetched the 6,466 sampled blocks from the node and checked them.
The fixture has 179,503,696 bytes of blocks, and its `blocks.bin` has the SHA-256 value `d3e682e3d48541cf71e71d7d869f4e72d1b964eceb2fc14f1eeb26d1f3fdcbb2`.
Of the blocks, 147 are `pinned` and 6,319 are `linked`.
The fixture is not committed.

`scripts/count_blocks.py --estimate --last 6465793` scales each stratum to the number of its heights: 1,000, or 794 for the last.
The standard error comes from collapsed strata, so it is itself an estimate.

| Quantity, heights 0 to 6,465,793 | Estimate | Standard error |
| --- | ---: | ---: |
| Bytes of the blocks | 179.5 GB | 6.4 GB |
| Transactions | 400.2 million | 18.0 million |
| Inputs | 763.8 million | 27.6 million |
| Outputs that enter the coin set | 936.4 million | 42.3 million |

The heights from 4,500,000 to 5,499,999 hold about 103 GB of the bytes and 271 million of the transactions.
There, 100,000 blocks have up to about 13 GB.

Two checks support the estimate.
The same sampled blocks give 217.3 million transactions up to height 5,050,000, and Core's `chainTxData` gives 226,128,837 (`chainparams.cpp`, lines 207 to 215).
The estimate of 179.5 GB is below the 204.1 GB of `size_on_disk`, which also counts the undo files.

Section 2 of the design record estimated 0.47 to 0.56 billion inputs.
The sample gives 0.76 billion, about 1.4 to 1.6 times as many.
Core took 89 µs for each input in the recorded run.
At that rate the pass needs about 19 hours on one core, without the cost of `CCoinsViewDB`.
At the 4.1 ms of the oracle, a replay of every block would need about 36 days on one core.
Design record 0011 does not propose that replay.

**The count script.**
`scripts/count_blocks.py` without a mode counts the transactions, inputs and outputs of a fixture.
On the recent range it gives every value of the second column of section 2 of the design record.
On the fixtures of heights 0 to 145,000, with `--coin-set`, it gives the 15,048,625 inputs and the 20,143,296 created coins of the recorded replay.
The set after height 145,000 has the 5,094,671 coins of that replay, under 2,675,914 transaction IDs.

**The memory of the harness.**
The harness carries the set as a `std::map` from the transaction ID to Core's `CCoins` (`harness/core/core_block_validate.inc`).
Two runs measured it with `/usr/bin/time -v`, each with one `block.validate` request from the empty set, as in the replay above.
The harness was built from commit `18310a8`, whose harness sources and build script equal those of `main` at `ae66db4`, with Core at `e0a1c157`.

| Run | Coins after the last block | Transaction IDs | Peak resident memory | Memory per coin | Memory per ID | Time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Heights 0 to 72,500 | 4,222,230 | 2,857,327 | 1,004.8 MB | 238 bytes | 352 bytes | 448 seconds |
| Heights 0 to 145,000 | 5,094,671 | 2,675,914 | 1,545.4 MB | 303 bytes | 578 bytes | 1,166 seconds |

The second run reports the set digest `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` of the recorded replay.
The peak includes the response, which holds one record for each block.
It is 28 MB and 57 MB of JSON in the two runs.

Suppose that the lower ratios of the first run hold at the tip.
Then the map needs about 48 GB for 202.5 million coins, or about 64 GB for 181.2 million transaction IDs.
No run measured a set of that size.
The machine has 125 GiB of memory, and `free` reported 46 GiB available, with other work running.

**The decision: `CCoinsViewDB`.**
The map does not fit reliably at the tip.
So stage 0 selects Core's `CCoinsViewDB` on a scratch directory for the Core pass, with a `CCoinsViewCache` of bounded size over it.
The harness still uses the map, and a later stage of the design record makes the change.

The harness will then use Core's own database of coins, as a node does.
Its memory will be the cache, and the records of one segment.

**The disk.**
`df` reported 909 GB available on 2026-11-20, after this stage's measurements.
Design record 0011 recorded 122 GB earlier that day.
The pass needs this space at one time:

| Item | Size |
| --- | ---: |
| One segment of blocks, which the pass deletes when the harness accepts it | At most 4 GB. Above height 4,500,000 a fetch then holds about 30,000 blocks |
| The `CCoinsViewDB` directory | At most about 35 GB: twice the keys and values of a set with 1.5 times the coins of the tip |
| The start snapshots of the eight ranges and two segment snapshots | At most about 231 GB, if no set has more than 1.5 times the coins of the tip |

The node's `bytes_serialized` of 11.5 GB is the sum of the keys and values of its database at the tip.
It does not count the other files of LevelDB or the space that a compaction needs, and no measurement here covers them.
So the table allows twice that size.

A record of a snapshot has 51 bytes and the script.
The coins at height 145,000 have 25.0 bytes of script on average, which gives 76 bytes for each record.
With the same average, a snapshot of the set at the tip has about 15.4 GB.
The coins at heights between 145,000 and the tip are not measured, and the pass reports them.

Under these assumptions the sum is at most about 270 GB, so the pass fits the 909 GB available.
The assumptions are the number of coins of each set, the average script length and the overhead of the database.
With 122 GB it fits only if the pass deletes each start snapshot after the oracle runs its range.

#### The recorded Core pass

This part records the run of [the Core pass](#the-core-pass) for stage 2 of [design record 0011](design/0011-mainnet-ranges.md).
It is the gate *Core pass* of [AGENTS.md](../AGENTS.md#checks), and it is not in CI.

| Input | Value |
| --- | --- |
| Harness | `core-oracle-trap`, built by `scripts/build_core_harness.sh --trap-overflow` from commit `46c8fa8` of pull request #185, with Core at `e0a1c157`. Its SHA-256 value is `bc49248d69c75f99b05ec8bc3c4484713edf9b126d7bd4eb4249f864aeaccd0f`. The harness of `main` at `df1b04c` differs from it only by the argument `force_csv_active` of #184, which the pass never sends |
| Script | `scripts/core_pass.py` at commit `1deb9d1` of the same pull request. The script of `df1b04c` differs in two places. It opens the headers read-only beside a running pass, and it saves the state before it deletes an old restart snapshot. Neither changes a request or a check |
| Blocks | Heights 0 to 145,000 from the fixtures of the [replay to height 145,000](#replay-of-mainnet-to-height-145000). Every later block from the maintainer's node, in segments of 100,000 blocks and at most 4 GB |
| Command | `nice -n 19 taskset -c 8,9 python3 -I scripts/core_pass.py --state build/core-pass --cache-mb 6144 --local <genesis-10000> --local <range-10001-145000> build/core-harness/core-oracle-trap`, started at 2026-11-20T23:14Z |

The pass ended at 2026-11-21T16:02Z, at height 6,465,793 with the block `9ebb986b0b16a65680c5f3447baca7154e2999680c76c97f24c4441897bc7385`.
It accepted all 6,465,794 blocks, 182,679,205,792 bytes, in 84 segments.
The segments took 60,266 seconds together, and the longest took 1,928 seconds.
Every checkpoint of Core held, and the trap build reported no signed overflow.

At height 6,465,793, three values of the pass equal those of the node's `gettxoutsetinfo` in the [measurements of stage 0](#measurements-for-the-core-pass) (decision 7):

| Value | The pass and the node |
| --- | ---: |
| `hash_serialized` | `a053d324494c91478b7e8525f52b062b56e976c61ef856509d59d33360048680` |
| `transactions` | 181,209,861 |
| `txouts`, the coins | 202,470,869 |

The script requires all three.
`hash_serialized` covers the best block, and the ID, the index, the amount and the script of each coin.
So the pass's set at the tip and the node's set have the same coins, amounts and scripts, if double SHA-256 is collision resistant.
It does not cover the height or the coinbase flag of a coin, which the digest of the set covers.
The node is not the reference software revision: it is `/Shibetoshi:1.14.9/`, and the harness is Core at `e0a1c157`.

At that height the set has the digest `6ff386f2a37464a65e11a9e48673c602e2a4f1a707040e12a7c4d06751cb90b5` and a `set_value` of 15,683,043,286,016,806,072 koinu.
The value exceeds 2^63 - 1, the largest `CAmount`, and the harness's 128-bit sum holds it exactly ([total value](#total-value)).
The node's `total_amount` was 156,830,432,860.16806 DOGE in the record of stage 0, which agrees with the pass to the digits that the record kept.
Core at `e0a1c157` sums `total_amount` in an `arith_uint256` (`rpc/blockchain.cpp`, lines 868 and 885), so that sum does not wrap either.
The script does not compare `total_amount`.

The pass has this snapshot at the start of each range.
Each committed manifest in [`tests/block/mainnet-blocks/snapshots`](../tests/block/mainnet-blocks/snapshots) is the file that the pass wrote:

| Snapshot | Coins | Bytes | Digest of the set | SHA-256 of the file |
| --- | ---: | ---: | --- | --- |
| Height 145,000, range A | 5,094,671 | 387,316,918 | `b28411dc46135fd0f85c954a664866d4f610803f7d667c9d2032ddfd6c58716d` | `0fa2f2a1e1aa43c54bf877e5aed1884cb9731412c45a06c9b8a9c84ad0b32012` |
| Height 370,336, range B | 8,576,188 | 654,238,056 | `3d63c9adf6858f73548dd3f0028ae3b6fadc71e837d6107c22aa43afc003b957` | `f16e3bf23a92d5a8112bbfdd2d07c6ab21a6cdeb6e45c9a7c22d252f0c72be0c` |
| Height 598,999, range C | 15,572,301 | 1,186,513,976 | `4355e90c77611cf22e2e1e70c4814f1d230481de5093c282a022388d66672856` | `234d2af5029ffea71986a2e18a5488515cb6bc8583ab29568c31562bd5211707` |
| Height 1,033,382, range D | 16,869,346 | 1,285,351,570 | `dd23f0095e9dd8f43f86fcab3e1f704e487974a7c8643bb365e4673c2e07d0e2` | `2ef63d136fcb1b4a61b6bc86c9f67af1832575c740f4a8644af81f5db5fb34b6` |
| Height 3,463,750, range F | 14,485,802 | 1,103,862,190 | `eaf159fc6ec3a7f8a2472271a8f162534f15c2166fd2400c7d37f1808a38a7b8` | `1043e1a13dca76e739dbb2f474594926ec57b604a5e1f928f6fec61bc1cf82c7` |
| Height 5,049,000, range H | 87,775,851 | 6,695,944,802 | `667fad0814f4f37fd1a4ecc7b6276370ed3d3bcf7b169df0498dc67865f58ccc` | `cb0176075521b01e81d998b6ac05410f24a0952b64d816118c5ad525a27394a6` |
| Height 6,455,301, range G (stage 3) | 202,740,183 | 15,407,228,563 | `5fde11f23206730ea665463a2035fd59cf55305fca973c8071dc997555869096` | `1cf629daa4fea574a32ebb80b09584df5a91a0a92a6f407a56d0916ef843375a` |

The snapshot at height 145,000 is the file of [range S](#ranges-from-a-snapshot), with the digest of the recorded replay.
So the pass reached the set that the oracle reached from the empty set.
The pass's block at height 6,456,301 is the last block of the recent range of the [released fixtures](../tests/block/mainnet-blocks/README.md).
That range starts after the snapshot of range G.
The pass also reached the recorded digests at heights 100,000 and 101,000, and it requires all three values.

The pass checked the states of the CSV window with `--version-bits`, on the headers of the pass to height 1,709,999:

```bash
python3 -I scripts/core_pass.py --state build/core-pass --version-bits .lake/build/bin/dogelib-oracle build/core-harness-rebased/core-oracle
```

All 52 boundaries from 1,189,439 to 1,703,519 agree with both full walks.
The CSV state is `defined` at 1,189,439, `started` from 1,199,519 to 1,693,439, and `failed` at 1,703,519.
The SegWit state is `defined` up to 1,461,599 and `failed` from 1,471,679, the first boundary after its start time, because its timeout is 0.

#### Ranges A to H

`scripts/run_range.py` runs each range from the pass's snapshot at its start, in the oracle and in Core.
A range agrees under section 3.4 of the design record when three things hold.
Both programs report the start digest of the manifest, accept every block with equal block records, and report the pass's digest at the end.
The block records must also equal those of the pass.
Before the range, `block.check` with both flags accepts every block in both programs.
Each range ran on one core at low priority, while the pass ran:

```bash
nice -n 19 taskset -c 10 python3 -I scripts/run_range.py --range <NAME> --pass build/core-pass --fixture build/ranges/<NAME> --output build/range-runs/<NAME> --write-hashes .lake/build/bin/dogelib-oracle build/core-harness-rebased/core-oracle
```

The oracle was built at `e927a4d`, whose Lean sources equal those of `main` at `df1b04c`.
The harness `core-oracle` was built from `df1b04c`.
Each fixture holds the blocks from `a + 1` to `b`, which `scripts/fetch_blocks.py --range` fetched from the node.
`--write-hashes` wrote the committed [hash list](../tests/block/mainnet-blocks/README.md#range-hash-lists) of each range from the headers of the pass.

| Range | Heights | Blocks | SHA-256 of `blocks.bin` | Start | End: coins and digest | Spent | Created | Core | Oracle |
| --- | --- | ---: | --- | ---: | --- | ---: | ---: | ---: | ---: |
| A | 145,001 to 155,000 | 10,000 | `c022bf754ddeb09663473add359918132d26b9fc0e742cb379cb50ac6635e82b` | 5,094,671 | 5,379,012, `fe00b205affdd2344d15cdeb073ad18a85ebfb2e8468e66c3ae96494631734c6` | 472,618 | 756,959 | 38 s | 1,426 s |
| B | 370,337 to 372,336 | 2,000 | `83140d38ea1010f69412306b5be617017a1c314a27d18ee9e5fb9aae487f4db1` | 8,576,188 | 8,622,709, `9a2633ff9d56b1de6ef4bc82016d1b22e7c43c3c8f1140a3de782f8b2afca67c` | 90,664 | 137,185 | 23 s | 568 s |
| C | 599,000 to 600,999 | 2,000 | `8594c4f65d706672e36c76db917cc0fb230fecdb7bf7a5d35cc6bd0acbdc08b9` | 15,572,301 | 15,588,181, `77b4529dad926f3bc516ee39d17b80955d4eea7e4234dcdd8b2a27271ae26179` | 173,936 | 189,816 | 67 s | 1,278 s |
| D | 1,033,383 to 1,035,382 | 2,000 | `fe0a039a16f6075981e88f8ac40614f286e58f97e5f5fa245b31b6fa3526e2a1` | 16,869,346 | 16,874,755, `c7e86aed9d7606e98d5385dec25d5176f37b77a8609390b0da70df29582f0d20` | 61,002 | 66,411 | 32 s | 856 s |
| F | 3,463,751 to 3,465,750 | 2,000 | `7b2b4b2fa443dbdbcbf4a9fa6f1188a51d30d3c8977b071a92ed282b2b154905` | 14,485,802 | 14,520,734, `a6b3bb146f7e3c41c97cdf63f699b5d50a47adc51b2e940b35980d37b8fc4849` | 154,273 | 189,205 | 36 s | 1,224 s |
| H | 5,049,001 to 5,050,000 | 1,000 | `6e2d5d9e79a327d4e0855a989ee83d4503ac9e8fb8764fbc79d20c01c53c86a9` | 87,775,851 | 87,790,115, `e3d9dec9b3a6fdfcc0cd72a3812f0961ae7c06ebe9a475cdb873d1fba7f66cfb` | 224,569 | 238,833 | 220 s | 4,466 s |

Every range agrees.
The start of each range has the coins and the digest of its snapshot in the table above.
The oracle's time includes its two reads of the snapshot.
`block.check` took the oracle 63, 14, 42, 10, 18 and 37 seconds on the six ranges.
On range H, the largest resident set of the run was 3,518,408 KiB, about 3.6 GB, which `/usr/bin/time -v` measured.
The other runs were not measured.

Each result is one run.
It holds under the hypothesis of section 3.4: the snapshot at the start is Core's coin set at its height.

Range A starts from the snapshot at 145,000, which has the digest that the oracle reached from the empty set.
So range A chains to the genesis block with no assumed start state.
The other ranges assume their start states.
The oracle did not check the blocks between the ranges.
[SOUNDNESS.md](../SOUNDNESS.md#b4-the-oracle-and-foreign-boundaries) states the hypothesis for each range.

#### The CSV window ranges E1 and E2

E1 and E2 are the two ranges of design record 0011, stage 4.
The first Core pass recorded Core's version-bits state at each period boundary.
CSV is `STARTED` from the block after the boundary 1,199,519, and `FAILED` from the block after the boundary 1,703,519.
So the rule changes at 1,199,520 and 1,703,520, and each range runs from `h - 1,000` to `h + 999`, the rule of section 4.

**The second pass.**
The first pass kept no snapshot at the two range starts.
`scripts/core_pass.py --seed` ran a second pass from the kept snapshot of range D at 1,033,382, which the first pass wrote in its replay from the genesis block:

```bash
nice -n 19 taskset -c 28 python3 -I scripts/core_pass.py --state build/core-pass-csv --seed build/core-pass --seed-height 1033382 --last 1704519 build/core-harness/core-oracle-trap
```

It ran on 2026-11-21 from 16:45 to 17:39 UTC, with the trap build of the harness at `e70318f`, and read the blocks above 1,033,382 from the node.
It accepted every block to 1,704,519 and wrote the snapshots at 1,198,519 and 1,702,519.
Its state names the heights that it checked against the first pass.
At 1,035,382 and at the seven segment ends of the first pass from 1,099,999 to 1,699,999, the digest, the number of coins and the total value equal the first pass's.
At the 67 boundaries in its heights, its version-bits states equal the first pass's.
Its 1,704,520 headers equal those of the first pass byte for byte.
`python3 -I scripts/core_pass.py --state build/core-pass-csv --version-bits .lake/build/bin/dogelib-oracle build/core-harness/core-oracle` then compared its 52 boundaries of the CSV window with both full walks, and each agreed.

| Snapshot | Coins | Digest | Total value | Bytes |
| ---: | ---: | --- | ---: | ---: |
| 1,198,519 | 16,774,101 | `c425e4c6d026e6019de51921dba183cf090da2f0f134650e2494a874c5154578` | 10,415,769,565,167,663,246 | 1,278,149,154 |
| 1,702,519 | 11,591,197 | `34d3337fd66c3e7f29a8419d816d28faa23434d3fd5a49ca112f10d81d2dec8a` | 10,919,769,565,167,663,246 | 883,951,730 |

The committed manifests are [`coins-1198519.json`](../tests/block/mainnet-blocks/snapshots/coins-1198519.json) and [`coins-1702519.json`](../tests/block/mainnet-blocks/snapshots/coins-1702519.json).

**The ranges.**
`scripts/run_range.py` ran each range from the second pass's snapshot at its start, as for the ranges A to H.
The chain of each request holds the version of each entry, and reaches at least the boundary 1,189,439, the base of the window, and its ten predecessors.
`chain_floor` of `scripts/core_pass.py` also keeps one period and 260 blocks below the range start, as for the other ranges.
So the chain of E1 reaches down to 1,188,179, with 10,341 entries, and the chain of E2 down to 1,189,428, with 513,092 entries.
Each request has `version_bits_heights` at the range start and at the boundary inside the range:

```bash
nice -n 19 taskset -c <core> python3 -I scripts/run_range.py --range <NAME> --pass build/core-pass-csv --fixture build/ranges/<NAME> --output build/range-runs/<NAME> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The oracle was built from `main` at `cc8bd97`, and the harness `core-oracle` from `e70318f`, whose harness sources equal those of `cc8bd97`.
The two ranges ran at once on 2026-11-21, on one core each.
`--write-hashes` wrote the committed [hash lists](../tests/block/mainnet-blocks/README.md#range-hash-lists): in an earlier run of E1, and in the recorded run of E2.

| Range | Heights | SHA-256 of `blocks.bin` | Start | End: coins and digest | Spent | Created | CSV states | Core | Oracle |
| --- | --- | --- | ---: | --- | ---: | ---: | --- | ---: | ---: |
| E1 | 1,198,520 to 1,200,519 | `f0647f8e1fdb6109e6297c498f8df154b24829295032824662bd34eba6a584a7` | 16,774,101 | 16,809,066, `5fa47879680925ec78db0c2ba6025722390edbe6d0bd60b01f5ea285f47d2ebe` | 57,055 | 92,020 | `DEFINED` at 1,198,519, `STARTED` at 1,199,519 | 75 s | 825 s |
| E2 | 1,702,520 to 1,704,519 | `95e0f69d1565f412da666ec68b6b4669d9a280849e12225c1964c8e4f9177225` | 11,591,197 | 11,581,142, `99dfcecda777971dff54621b7eb9b177781abe34d9194aa78a242679cc4070f0` | 68,452 | 58,397 | `STARTED` at 1,702,519, `FAILED` at 1,703,519 | 82 s | 1,100 s |

Both ranges agree under section 3.4.
Both programs report the start of the manifest, accept every block with equal block records, and report the second pass's digest at the end.
The block records also equal those of the second pass.
Both programs report the CSV states of the table, and each state at a boundary equals the one that both passes recorded.
`block.check` took the oracle 10 and 17 seconds before the ranges, and accepted every block in both programs.
An earlier run of E1, on a build of the oracle before the fix of an active CSV state, gave the same result.

Each result is one run.
It holds under the hypothesis of section 3.4: the snapshot at the start is Core's coin set at its height.
Both snapshots come from Core's replay from the genesis block: the first pass to 1,033,382, and the second pass from there.
The oracle did not check the blocks between the ranges.
On mainnet the CSV state is never active, so the walk changes no verdict of the ranges ([SOUNDNESS.md](../SOUNDNESS.md#version-bits)).
The ranges compare the states that the walk reports, in the oracle and in Core.

### Block subsidy comparison evidence

The harness calls Core's own `GetDogecoinBlockSubsidy` (D104), so the comparison tests Core's code and the Boost release of the harness build.
The comparator requires equal `subsidies`, and it checks the form of `redraws` and `boost_version` without a comparison.
It also requires each subsidy to lie in the range that Core's text allows for the height (D104, lines 138 to 148).
Its report names the Boost release, the number of cases with a redraw and the largest number of redraws.

The 148 requests hold 145,166 cases:

| Set | Requests | Cases | Expected values |
| --- | ---: | ---: | --- |
| Mainnet heights 1 to 145,000 on their real previous hashes ([fixture](../tests/block/mainnet-subsidy-prev-hashes/README.md)) | 145 | 145,000 | None: agreement of the two programs |
| Fixed schedule: 18 heights from 145,000 to 2147483647, each on three hashes | 1 | 54 | Read by hand from D104, lines 142 to 148 |
| Recorded Core values: 35 mainnet heights below 145,000 | 1 | 35 | Captured from Core's function through the harness, and computed again in each run |
| Boundaries: 11 heights from 0 to 600,001, each on seven hashes | 1 | 77 | None: agreement of the two programs |

With Boost 1.70.0 every case agrees.
The oracle reports one redraw for 30 of the 145,000 mainnet heights, and no case has more than one.
`scripts/test_oracle.py` checks the fixed schedule, the recorded Core values and the request errors without Core.

The 144,999 mainnet heights with a random subsidy hold 144,965 distinct seeds of the `2^28`, each at the height of its block.
`scripts/compare_subsidy_seeds.py` covers every seed outside CI.
It sends all `2^28` seeds at height 1, where `maxReward` is 999,999, and at height 100,000, where it is 499,999.
It fails on any disagreement and on any error, so a pass shows that 624 words of fuel suffice for every seed.
The run of 2026-11-13 passed on all 536,870,912 cases, and no seed takes more than 2 redraws.
[COVERAGE.md](../COVERAGE.md#operations) records the run.

### Header-sequence comparison evidence

The harness calls Core's static `AcceptBlockHeader` (D33, lines 3205 to 3267) once for each header of the request, in order.
That function calls Core's `CheckBlockHeader`, `ContextualCheckBlockHeader` and `AddToBlockIndex` (lines 2755 to 2788).
Earlier revisions used a transcription of these passages, H2 of [design record 0008](design/0008-header-sequence-validation.md#82-the-core-side).
The harness no longer contains it.
The harness does not call `ProcessNewBlockHeaders`, so `NotifyHeaderTip` does not run.

Each response field comes from Core's state:

- `valid`, `reject_reason`, `dos` and `reject_code` come from the return value and the `CValidationState` of the first rejected call.
- `added` lists each header whose hash `mapBlockIndex` lacked before its call, with the height and chain work of Core's new entry.
- `marked_failed_child` lists the members of Core's `setDirtyBlockIndex` after the rejected call. A rejected call adds no entry, so the set holds exactly the entries that the marking loop visited (lines 3246 to 3250).

The remaining harness trust is the in-memory index.
The harness creates one `CBlockIndex` for each index entry of the request, in Core's `mapBlockIndex`.
It sets the height, status flags, chain work and predecessor of each entry, and calls Core's `BuildSkip` with predecessors first.
It inserts the failed list into Core's `gFailedBlocks`.
That set orders its members by address, so Core visits the failed list in address order, not in request order.
The comparator already excludes `marked_failed_child` where the order can change it.

The harness sets the adjusted time through Core's mock time and time offset, and calls `UnloadBlockIndex` before and after each request.
It restores mock time 0 and offset 0 on every exit from the request, so no later request sees the adjusted time.
Mock time 0 selects the system clock, so the harness gets adjusted time 0 from mock time 1 and offset -1.

The harness accepts every adjusted time from -2^63 to 2^63 - 7201, as the oracle does.
On this path Core reads the time only through `GetAdjustedTime` and adds 7200 to it, which cannot overflow in that range.
Core also formats a log timestamp from the mock time, and that conversion fails outside the years 1400 to 9999.
The harness turns off Core's log timestamps and its debug log, so Core never makes the conversion.
`scripts/test_core_harness.py` sends sequence requests at -2^63, 0, 10^12 and 2^63 - 7201, alone and in one stream with contextual checks between them.
Each harness response must be the same alone and in the stream, and must agree with the oracle.

The harness has one internal operation, `harness.time_state`, which is not part of `dogelib-oracle/1`.
It returns Core's mock time and time offset.
The oracle has no such operation, and the comparator never sends it.
The same test sends it after a success, a consensus rejection, a request error and a decoding error, at adjusted time 0 and at 10^12.
Both values must be 0 each time.
The test fails when either reset is removed.

A request names no ancestor below an anchor.
Core's `GetAncestor` asserts a predecessor at every step, and `AddToBlockIndex` reaches it through `BuildSkip`.
So each anchor above height 0 gets one placeholder entry as its predecessor.
The placeholder is its own predecessor and its own skip entry, and it is outside `mapBlockIndex`.

`GetAncestor` returns it for every height below the anchor, and it is equal to no entry of the request.
Core follows a skip pointer only when its skip height is at least the target.
So a walk to a height at or above the anchor never passes through the placeholder.

Before each call, a preflight refuses a request with a short median, recovery or retarget history.
It applies only where `AcceptBlockHeader` reads that history.
There the header is not the genesis block, is unknown, has valid work, and has a known predecessor without a failure flag.
So Core never reads the placeholder as history, and `GetNextWorkRequired` cannot call `GetAncestor` below an anchor at `pow.cpp:84`.
The preflight returns no verdict.
`AcceptBlockHeader` does not reach `VersionBitsState`, so the request needs no version-bits history.

For the three fixture adapter errors, the comparator requires the exact Lean `work_view` error and the corresponding Core request-refusal message.
Neither response is a consensus rejection.

`scripts/oracle_header_sequence.py` defines these streams:

| Stream | Requests | Evidence |
| --- | ---: | --- |
| Regtest | 34 | D83's complete requests and hand-derived expected fields |
| Mainnet | 15 | Five full-header ranges, three pure-header initial indices, checkpoint branches, two anchor refusals and three version mutations |
| State boundaries | 8 | Prefix marks, an existing child flag, anchor separation, three failed-list search orders, the candidate height bound and size-before-decode precedence |
| Mutations, seed `20261110` | 200 | Header order, bits, time, predecessor bytes, failure/validity flags and failed-list order |

The mainnet sequences use every full candidate after the first eleven context entries of each non-genesis range.
The genesis sequence starts with an empty index.
Chain acceptance supplies expected verdicts.
Python integer arithmetic independently computes block proofs and wrapped sums from D35, lines 150 to 162.
No expectation comes from DogeLib or the harness.

The comparator prints both source revisions and each selected stream with its seed and count.
These finite comparisons do not prove agreement on all inputs.

The self-test plants disagreements in every response field and each added-entry field.
It checks both failed-list orders, keeps the other fields comparable when marks are excluded, and rejects duplicate-member over-exclusion.
The oracle tests compare fixture expectations, exact adapter errors, malformed requests and resource-limit refusals.

## Campaign runs and replay

`scripts/campaign.py --campaign generated` checks Q1 to Q7 from [design record 0009](design/0009-bug-finding-campaign.md#11-properties).
It reuses `compare` from `scripts/compare_core.py` without changing the CI comparison stream.
The default campaign checks Q6 alone.
It shuffles existing requests with the selected seed and sends fixed-size batches.
The generated campaign adds signed plans and independent property checks.

Build the oracle and harness as described above, then run these commands:

```bash
python3 -I scripts/campaign.py run --seed 20261108 --cases 10000 --seconds 600 --output build/campaign/check .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py replay build/campaign/check/<run>/failures/<digest>.json .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/test_campaign.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py run --campaign generated --signer build/core-harness/core-signer --seed 20261108 --cases 3000 --seconds 600 --batch-size 64 --output build/campaign/generated .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

`--inputs` selects `signed-spends`, `cltv`, `csv` or `signed-digests`.
The default selects the first three groups.
The digest group uses the existing recovery transactions, redeem scripts and hash types.
The timelock groups retain their original construction seed `20261107`.
The campaign seed selects the order, and `--cases` limits the prefix without repeating inputs.

`--campaign generated` selects the signed recovery-family generator and requires `--signer`.
Other names select existing requests and record the supplied name.

The generated stream starts with the 25 recovery fixtures and the targeted CLTV stream, including its boundary cases.
It then enumerates shuffled boundaries and draws plans with `random.Random(seed)`.
Plans cover both branches, signer pairs, mixed hash types, input positions, counts, selectors, supported flags and signature encodings.
The preserve mode mutates a plan before signing it.
The commitment mode signs first, then changes the spend while keeping its signatures.

The explicit `FIELDS` table in `scripts/campaign_generator.py` follows pinned `interpreter.cpp`, lines 1054 to 1143 and 1225 to 1246 (D3).
It records the committed and open fields of [section 6.3](design/0009-bug-finding-campaign.md#63-committed-and-open-fields).
SINGLE output-count changes stay above the input index, except in separate fixed-digest cases.

Before constructing a spend, the driver checks every signing digest against both programs through `sighash.legacy`.
Q1 to Q5 and Q7 derive expectations from the plan and field table, without using a program's verdict.
Q6 still checks agreement on every request, including the before and after digests.
Q4 checks Lean preimages as well as both digests and rejection.
Its security assumptions remain those of [section 11](design/0009-bug-finding-campaign.md#11-properties).
These finite checks add no theorem.

`core-signer --sign` reads JSONL requests with `id`, `tx_hex`, `input_index`, `script_code_hex`, `hash_type` and `key_ids`.
It accepts base transactions of at most 100,000 bytes, with 1 to 4 inputs, 0 to 5 outputs and an existing input index.
Script code has at most 10,000 bytes, and the hash type is a byte.
The 1 to 3 key identifiers select public test scalars 1 to 4.
A response echoes `id` and supplies `ok` with `digest_hex`, `signatures_hex`, `CORE_SIGNER_BLOB` and `request_source_blob`.
The digest uses wire byte order, and each DER signature includes its hash-type byte.

A refusal supplies `error` with `kind: "refusal"` and a `reason` string.
The request mode calls Core's `SignatureHash` and deterministic `CKey::Sign`, without returning a Script verdict.
The no-argument fixture generator and `--verification-vectors` retain their byte-for-byte regeneration checks.

`--batch-size` defaults to 2,000 cases and `--timeout` to 60 seconds per program invocation.
Each generated case sends one signing request per signature and several oracle requests.
`--seconds` limits scheduling and each invocation's remaining time.
Each version probe has a fixed 0.25-second timeout.
Probe time counts against the campaign budget.
An invocation stopped by the remaining budget marks the run incomplete without recording a program timeout.

The driver bisects a failed stream until it isolates individual requests, while time remains.
Bisection assumes that responses depend only on their requests.
If one half isolates a crash, the driver does not also save the parent batch.
A separate failure that requires requests from both halves can therefore escape attribution.

A failure that disappears in smaller batches retains its original batch for replay.
A budget that interrupts isolation also retains the failed batch and marks the run incomplete.
Exit status 1 means a disagreement, a process failure or an incomplete run.

Each run creates a fresh directory below `--output` and prints its path and counts.
Its `summary.json` records revisions, versions, seed, budgets, input selection and counts for all six outcome classes.
Generated summaries also record coverage counts for branches, hash types, errors, mutations, properties, modes and transaction boundaries.
The `q6_requests` count records assessed requests separately from cases and signing preflight requests.
The per-case `counts`, including passes, sum to `completed`.

`batch_counts` records stream failures that bisection did not attribute to individual requests.
The `failures` total includes both per-case disagreements and process failures, and these separate batch failures.

`unsupported` and harness `refusal` count apart from disagreements, and each gets a saved record.
`known` counts accepted fixed-digest cases and early recovery with CLTV disabled, after the property checks pass.
The duplicate-key behaviour is registered but unreachable in this template, whose keys are distinct.
Saved `unsupported` records name Q6 and its agreement expectation, as exclusions from comparison.
Every Q6 result retains that expectation rather than the generated plan's independent property.
A Q6 disagreement has failing side `undetermined`: agreement alone cannot establish which implementation violates an independent property.

Saved records use `dogelib-campaign-failure/1`, with the fields of [section 7.3](design/0009-bug-finding-campaign.md#73-the-saved-failure).
A file name hashes the canonical request text with SHA-256, or the request array for a batch-only failure.
Records contain exact requests, full responses, process status, standard error and the raw output of failed batches before bisection.
Per-request records retain the full raw stream in `stdout`, with its request order in `stdout_requests`.
Invalid UTF-8 bytes use JSON surrogate escapes and round-trip with Python's `surrogateescape` codec.

Existing cases have an empty `signer` array and a null `CORE_SIGNER_BLOB`.
Generated failures retain exact signing requests and responses, or process evidence, together with both signer source blobs.
The adjacent `core.stamp` records the harness build provenance, or null for a wrapper without a stamp.

Replay uses the configured `timeout` from the record and reports whether the class and failing side reproduce.
It exits with status 0 for reproduction, 1 otherwise, or 2 for an invalid invocation or saved record.
Oracle and harness failures replay stored requests without signing again.
Signer failures require `replay --signer build/core-harness/core-signer <failure> <oracle> <harness>`.
This path repeats the signing requests and checks refusals, malformed responses, process failures or digest discrepancies.

Keep saved candidates private under `build/campaign/`, as [SECURITY.md](../SECURITY.md) requires.
Console output contains counts, without candidate requests or responses.
The self-test checks six outcome classes, crash attribution within a batch, malformed output, response counts and response identifiers.

It also requires semantic mutants M1 to M6 to be detected and replayed within fixed budgets.
It writes their seed, first detected case, class and timing to `build/campaign/mutant-detection.json`.
Signer checks cover repeated-request determinism, refusal replay and malformed-response replay.
[Production replay](#production-replay) replays a saved candidate through Core's production path.

The `core` workflow runs the generated campaign at seed `20261108` with 3,000 cases, the command above.
A person reviewed the results of that seed, so a CI log shows no new candidate ([design record 0009, section 9.4](design/0009-bug-finding-campaign.md#94-a-real-finding)).
A run with a fresh seed stays on a contributor's machine.
The other campaign commands do not run in CI.

### The planted proposal search

`--campaign proposal` searches for a violation of `RestrictsAcceptance` by the planted fault of [design record 0009, section 8.1](design/0009-bug-finding-campaign.md#81-the-planted-proposal-fault).
In this campaign, the harness argument is `proposal-replay`, a test executable under `tests/`.
It is not part of `Exports`, and `dogelib-oracle` gets no proposal operation.

```bash
lake build dogelib-oracle proposal-replay
python3 -I scripts/campaign.py run --campaign proposal --variant corrected --seed 0 --cases 374480 --output build/campaign/proposal .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
```

`proposal-replay ExampleFaultyLocktime (faulty|corrected) [--active]` reads `script.verify_legacy` requests in this format.
It answers each request with the revised spend predicate of the named variant, through the oracle's own request decoding and response encoding.
Without `--active`, the revised step equals the baseline step.
It answers every other operation with an unknown-operation error, and `--version` prints the format with `"program": "proposal-replay"`.

The driver enumerates every script of one to five instructions from the alphabet of section 8.1, shortest first, with no seed.
Each of the 37,448 scripts runs with five lock times and two sequences, so the space has 374,480 cases.
The spending transaction has version 1, one input with a null outpoint and an empty `scriptSig`, no outputs and flags 0.
`--variant` selects the variant, and `--cases` limits the prefix of the enumeration.

A violation is a request that `proposal-replay` accepts and `dogelib-oracle` rejects.
Its saved failure names the property `RestrictsAcceptance`, the class `verdict` and the failing side `revised`.
The record keeps the replay's arguments in `program_arguments`, so `replay` runs the same variant.
Process failures, `unsupported` results and refusals keep the classes of section 7.2.

A failure of `proposal-replay` names the side `revised`.
A response that is not an `ok` object with the result `accepted`, `rejected` or `unsupported` checks nothing.
On either side, it is a `crash` with the code `RESULT`, so a search cannot pass without verdicts.
Flags 0 make every case of the space supported, so a proposal run also exits with status 1 when its `unsupported` count is above zero.
Other differences between two verdicts are not violations of this property.

`--script` runs one script instead of the enumeration, with `--lock-time` (default 2) and `--sequence` (default `0xfffffffe`).
It accepts hex bytes, and it splits them into instructions at push boundaries.

### Reduction

`campaign.py reduce <failure> <oracle> <harness> [<signer>]` reduces a saved failure of one generated or proposal case.
A generated failure needs the signer.
The reducer refuses a record of existing requests, and a batch of several cases, because they have no single construction plan.
It exits with status 0 when it writes an output.
It exits with status 2 for such a record, or when the stored plan no longer reproduces its failure condition.

```bash
python3 -I scripts/campaign.py run --campaign proposal --script '51 52 b3 51 87' --seed 0 --cases 1 --output build/campaign/seed .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
python3 -I scripts/campaign.py reduce build/campaign/seed/<run>/failures/<digest>.json .lake/build/bin/dogelib-oracle .lake/build/bin/proposal-replay
```

The reducer changes the plan, not the bytes.
It runs each candidate plan alone through the same run path as `run`, with the record's seed and timeout.
So a preserve plan is signed again after its mutations, and a commitment plan is signed before them and keeps its signatures.
A candidate replaces the plan when that run saves a failure with the same property, class and failing side.
A candidate that the plan's construction cannot build, such as a mutation of an input that the candidate removed, is skipped.

It tries the changes of [section 7.4](design/0009-bug-finding-campaign.md#74-replay-and-the-reducer) in this order:

1. Remove one element, then two adjacent elements, then each half of four or more elements. An element is a mutation, the signature-encoding mutation or a script instruction.
2. Remove each other input and each output, then move input `n` to position 0 or one position towards it.
3. Replace the value of each push in a script with 0. Then set the version to 1, each nonfinal sequence to 0 and each output value to 0. Replace the lock time with the least value of its class.
4. Clear each flag that is not P2SH in a generated plan. Keep each result inside the assertion domain of C7.
5. Set every hash type to ALL, then each one. Then replace a true selector with `01` and a false selector with the empty push.
6. Remove one byte of each other script.

The lock-time classes are the values below 1,000,000, the values from 1,000,000 to 499,999,999, and the values from 500,000,000.
The classes are specific to the 2-of-3 recovery template of decision 1.
Its CLTV operand is 1,000,000, and 500,000,000 separates heights from times (C4).
The template has no `OP_CHECKSEQUENCEVERIFY`, so 0 represents every nonfinal sequence.
A plan for another template needs its own classes.

A candidate must also stay in the domain of its property (section 7.4).
Every property of section 11 assumes a P2SH spend, so a generated candidate keeps the P2SH flag.
The ordinary branch (Q1) needs a true selector, and the recovery branch (Q2 and Q3) needs a false one.
The reducer skips a candidate that leaves this domain, when the stored plan is inside it.

After each accepted change, the reducer starts its current step again on the new plan.
It repeats the six steps until a complete pass accepts no change, and then it gives the label `minimal`.
The output is then 1-minimal for these changes only.
`--max-candidates` (default 2,000) limits the candidates that the reducer runs.
If the limit stops the reduction before such a pass, the label is `budget`, and the output still keeps the failure condition.

The reducer caches each result by its canonical plan, so a candidate runs once.
It writes the output to `reduced/<digest>.json` beside the run's `failures/` directory.
The output is a complete saved failure with `reduced_from` set to the original file name.
Its `reduction` field records the label, the number of candidates, the limit and each accepted change with its step.
The console shows the output path, the label and the counts, without requests.

The campaign self-test needs `proposal-replay` beside the oracle, or `--proposal-replay PATH`.

It runs the faulty search over all scripts of up to three instructions and requires violations of exactly three instructions.
It runs the corrected search over the whole space and requires no violation.
It reduces `51 52 b3 51 87` and requires three instructions with the label `minimal`.
It also reduces the first saved detection of each mutant M1 to M6.
Each reduction must keep the failure condition and the mutant's trigger, and its output must replay.
Each reduced generated plan must keep the P2SH flag and a selector of its branch's truth value.

A planted Core fault flips the verdict of each spend with a hash type `0x82` signature.
The self-test reduces its first three detections, and each reduced plan must keep a `0x82` signature.
The unmodified harness must also give the expected verdict on the reduced spend, so the template runs.
A stand-in replay that answers every request with an error must fail all 200 cases of a corrected search.
It writes the labels, candidate counts and plan sizes to `build/campaign/mutant-reduction.json`.

### Production replay

Design record 0009, [section 9.1](design/0009-bug-finding-campaign.md#91-levels), counts a candidate as a finding only after a replay through Core's production path.
`campaign.py replay --level` replays one saved failure of one generated signed-spend case at level L1 or L3.
Each replay appends its evidence to the saved failure, in the `production` field.
The field is an addition to `dogelib-campaign-failure/1`, so the format name stays the same.

Build the programs at one Core commit, each in its own directory:

```bash
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
taskset -c 16-23 nice -n 19 scripts/build_core_node.sh --revision e0a1c157791544e818c901bd9341896965afbf9d <dogecoin-git-clone> build/core-node
```

Replay a saved failure at each level:

```bash
python3 -I scripts/campaign.py replay --level L1 <failure> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
python3 -I scripts/campaign.py replay --level L3 --signer build/core-harness/core-signer --node build/core-node <failure> .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

`--target pin` is the default, and it needs builds at the pin `e0a1c15`.
`--target upstream` labels builds of another commit, as [section 9.2](design/0009-bug-finding-campaign.md#92-the-current-upstream-revision) requires.
`--revision COMMIT` also requires each build to name that full commit.
Every result records the commit, the build stamps and the SHA-256 of each program.

The replay refuses a program without a build stamp, such as a wrapper of the self-test.
It refuses a stamp of another commit, an L3 call without `--signer` and `--node`, and a saved failure outside `build/campaign/`.

| Exit status | Outcome |
| --- | --- |
| 0 | `reproduced` |
| 1 | `not-reproduced` |
| 2 | A refusal, SIGTERM or an unexpected error. The saved failure does not change. |
| 3 | `not-comparable` at L3, or `error` at L1. The replay decides nothing. |

SIGTERM stops the node and deletes its data directory before the replay exits.
The node also gets SIGKILL from Linux when the replay process dies by SIGKILL (`PR_SET_PDEATHSIG`).
After a SIGKILL, the data directory stays under `build/campaign/`.
The console shows the level, the commit, the outcome and the labels at the pin and at upstream, without requests.

#### Builds at another commit

`scripts/build_core_harness.sh --revision COMMIT <clone> <build-dir>` builds the harness and `core-signer` at that commit.
The directory must not be `build/core-harness`.
The first line of `core.stamp` is then `revision <commit>`, and `core.revision` holds the commit.
Both programs add `core_revision` to their `--version` output.
Without `--revision`, the build and its output do not change, and the pin in SOURCES.md and in CI stays `e0a1c15`.

For the upstream check, read the current commit of the pin's branch, and build from it:

```bash
git ls-remote https://github.com/dogecoin/dogecoin refs/heads/1.14-maint
scripts/build_core_harness.sh --revision <commit> <dogecoin-git-clone> build/core-harness-upstream
python3 -I scripts/campaign.py replay --level L1 --target upstream <failure> .lake/build/bin/dogelib-oracle build/core-harness-upstream/core-oracle
```

The clone must contain that commit.
On 2026-11-08 the branch was at the pin itself, `e0a1c157791544e818c901bd9341896965afbf9d`.

`scripts/build_core_node.sh --revision COMMIT <clone> <build-dir>` builds a `dogecoind` without a wallet, GUI, tests or ZMQ.
It exports the commit with `git archive` and writes `node.stamp` and `node.revision`.
It reuses the node when the stamp matches.

Pinned Core needs the Boost libraries system, filesystem, program_options, thread and chrono.
Recent distributions omit `boost_system`, so the script builds Boost 1.70.0 into the build directory.
It checks the SHA-256 of the archive first.
Boost 1.70.0 does not compile with glibc 2.34 or later, so the script applies the one-line change that Boost 1.78.0 made to `boost/thread/pthread/thread_data.hpp`.
`BOOST_ROOT` selects an installed Boost instead, and `BOOST_ARCHIVE` selects a local copy of the archive.
On this project's development machine, the node and its Boost built in 62 seconds with 8 jobs.

#### L1

L1 sends the stored requests, unchanged, to the oracle and to the harness build.
For the signed-spend family, `script.verify_legacy` calls `VerifyScript`, and `sighash.legacy` calls `SignatureHash` ([what the harness runs](#what-the-harness-runs)).
The outcome is `reproduced` when the stored class and failing side recur.
It is `error` when either program fails, crashes or times out, and `not-reproduced` otherwise.
L1 does not include the caller of [section 4, item 8](design/0009-bug-finding-campaign.md#4-behaviour-to-preserve): a node uses `CachingTransactionSignatureChecker` through `CScriptCheck`.

#### L3

L3 starts `dogecoind -regtest` in a new temporary data directory under `build/campaign/`.
The node binds RPC to 127.0.0.1 on the first free port from 24440 to 24479.
It does not listen for peers and does not connect to them.
These ports are outside the range of Core's functional test framework, 11000 to 20999, and differ from the default ports.
The replay stops the node on every exit path and deletes the data directory.

The outpoints of a saved case are random bytes, so L3 builds the same case on real outputs:

1. It mines 19 legacy blocks and 1,333 AuxPoW blocks, to height 1,352, with `generatetoaddress` (D96). Regtest starts AuxPoW at height 20, DERSIG at 1,251 and CHECKLOCKTIMEVERIFY at 1,351 (D14).
2. One funding transaction makes an output for each input. Input `n` gets the P2SH output of the redeem script, and each other input gets a bare `OP_TRUE` output. A block confirms the transaction.
3. The plan's inputs get these outpoints. In preserve mode, L3 first applies the mutations, because the signer signs the mutated transaction. In commitment mode, the mutations stay. A mutation of an outpoint or of the input count is refused, because no output can match it.
4. If the spend has no output, L3 adds one zero-value `OP_TRUE` output, because `CheckTransaction` rejects a transaction without outputs (D90). The evidence records this change.
5. `core-signer --sign` signs the same plan again: the same mode, keys, hash types, selector and signature mutation. The oracle and the harness check each signing digest, as in a run.
6. The rebuilt case must keep the saved property, verdict, error name and digest relation. Otherwise the outcome is `not-comparable`.
7. The harness that found the candidate must show the saved class and failing side on the rebuilt bytes. It is the harness of the record's replay command, or `--candidate-harness`. Otherwise the rebuilt case lost the candidate's trigger, and a node that agrees with the property gives `not-comparable`.

The node checks the spend twice:

| Path | Script flags | Source |
| --- | --- | --- |
| `sendrawtransaction` and `AcceptToMemoryPool` | The flags of the spend request, through `-promiscuousmempoolflags`. A hash-type mutation or a `hash_byte` signature clears STRICTENC from the plan's flags (`spend_flags` in `scripts/campaign_generator.py`). Regtest does not require standard transactions, so the node accepts the option. | D95, D97, D14 |
| `submitblock` with an AuxPoW block that holds the spend | The consensus flags of the block's height: P2SH, DERSIG and CHECKLOCKTIMEVERIFY, flags 517. CHECKSEQUENCEVERIFY is not active at that height, and `IsWitnessEnabled` returns false. | D96, D36 |

Both paths call `VerifyScript` through `CScriptCheck` with `CachingTransactionSignatureChecker`, the production caller.
The replay starts the node with `-par=1`, so a block's script check runs in the calling thread and its error reaches `submitblock`.
The replay maps each rejection reason to an error name through `ScriptErrorString` (D99).
Another rejection, such as `non-final` or `bad-txns-vout-empty`, makes the path `not-comparable`.

The mempool result decides the L3 outcome, because the mempool uses the flags of the spend request.
If the rebuilt request has other flags, the outcome is `not-comparable`.
After the plan's flags, the mempool checks P2SH alone again, and it reports only the first failing input (D97).
So L3 refuses a plan without P2SH or with CLEANSTACK, which the bare `OP_TRUE` inputs would fail.
The outcome is `reproduced` when the node's verdict or error name differs from the saved expectation, and `not-reproduced` when it agrees.

Core prefixes a Script rejection with `non-mandatory-script-verify-flag` when the spend passes without the flags of `STANDARD_NOT_MANDATORY_VERIFY_FLAGS` (D98).
At the pin, `MANDATORY_SCRIPT_VERIFY_FLAGS` is P2SH alone.
So that prefix does not separate policy from consensus: a block also reports a CHECKLOCKTIMEVERIFY failure with it.
The block result separates them.
The evidence sets `policy_only` when the mempool rejects the spend and the block accepts it.
For example, a high-S signature fails LOW_S in the mempool, and flags 517 accept it in a block.

After funding, the tip is at height 1,353, and `CheckFinalTx` tests the spend for the next block, height 1,354.
L3 can compare only a spend that is final in that block.
A spend is final when every sequence is `0xffffffff`.
It is also final when its lock time is a height below 1,354, or a time before the median time past.
The node rejects any other spend with `non-final`, so its outcome is `not-comparable`.

A valid recovery spend (Q2) is never final there, because the template's CLTV operand is the height 1,000,000.
The generator's acceptance cases also set lock time 1,000,000 with a nonfinal sequence on input `n`.
So most generated Q1, Q4 and Q5 cases, and every Q2 case, are `not-comparable` at L3.
Q3 cases at a lock time below 1,354 or a time lock time, and spends at lock time 0, are comparable.

#### Classification

After each replay, `production.classification` labels the candidate from the latest outcome of each level.
`label` uses the replays at the pin, and `upstream` uses the replays at upstream, or is null.
A Core-side candidate has the failing side `core`, `both` or `undetermined`.

| Candidate | Outcomes | Label |
| --- | --- | --- |
| Core-side `verdict` | L3 `reproduced` | `reproduced` |
| Core-side `verdict` | L3 `not-reproduced`, L1 `reproduced` or `not-reproduced` | `harness-fault` |
| Core-side `verdict` | L1 `reproduced`, no comparable L3 result | `reproduced-at-l1`: the candidate still needs L3 |
| Core-side `digest` | L1 `reproduced` | `reproduced` |
| Core-side `digest` | L1 `not-reproduced` with a harness whose SHA-256 differs from the harness that found the candidate | `harness-fault` |
| Any other | A `reproduced` outcome at either level | `reproduced` |
| Any | Every other combination, including an L1 `error` | `undetermined` |

For a `verdict`, L3 overrides L1, because only a node runs the production caller of [section 9.1](design/0009-bug-finding-campaign.md#91-levels).
Suppose that L1 reproduces the candidate and L3 does not.
Then the fault is in the harness's own code around `VerifyScript`, such as its transaction or flag handling.
For a `digest`, L1 decides: `sighash.legacy` calls `SignatureHash` itself, and L3 checks only verdicts.

`production.replays` keeps every replay in order, with its level, target, commit, build identities, requests, full responses and node rejection reasons.
L3 evidence also keeps the funding transaction, the new outpoints and the signer's requests and responses.
It keeps the end of the node's `debug.log` and the time of the replay.
Keep this evidence private under `build/campaign/`, as [SECURITY.md](../SECURITY.md) requires.

#### The stage 4 self-test

```bash
python3 -I scripts/test_campaign_production.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle --node build/core-node --upstream-harness build/core-harness-upstream/core-oracle
```

The self-test plants the harness fault M3 of [section 8.2](design/0009-bug-finding-campaign.md#82-planted-harness-and-model-faults), which treats lock time 500,000,000 as a height on the recovery branch.
It runs the generated campaign until it finds the fault, then reduces the first detection.
The unchanged harness must not reproduce the reduced candidate at L1, and the replay must refuse the planted wrapper.
It checks the table of labels on stated outcomes.
A stamped build that exits with status 3 must give the L1 outcome `error`.
A stamped build that contains the planted fault stands for a faulty adapter: it must reproduce at L1 and get `reproduced-at-l1`.

`--node` adds L3.
The node must reject the reduced spend with `UNSATISFIED_LOCKTIME` in its mempool and in a block, and the planted wrapper must accept the same bytes.
The candidate must then have the label `harness-fault`.
The stamped faulty build must also become `harness-fault` after L3.
With `--candidate-harness` set to the unchanged harness, the trigger is lost, and the outcome must be `not-comparable`.
`--node` also checks five other spends:

- An ordinary 2-of-3 spend, which the mempool and a block accept.
- An early recovery spend at lock time 1,000, which both reject with `UNSATISFIED_LOCKTIME`.
- A commitment-mode spend whose version changes after signing, which both reject with `mandatory-script-verify-flag-failed`.
- A spend whose first signature has bit `0x20` of its hash-type byte flipped (`hash_byte`). The node and the harness must both use flags 541, without STRICTENC.
- A high-S spend, which the mempool rejects with `SIG_HIGH_S` and a block accepts, so `policy_only` is true.

`--upstream-harness` adds L1 against another harness build, with `--target upstream`.
It sends the requests of 500 generated cases to both harness builds and reports how many responses differ.
When the node build names the same commit, it also runs L3 with `--target upstream`.

`scripts/test_campaign.py` runs the L1 part, without `--node`.
`--keep DIR` copies the first detection and its reduced output to a directory under `build/campaign/`, which the self-test otherwise deletes.
With `--node` and `--upstream-harness`, the self-test passed 17 cases in 32 seconds on the development machine.
Each L3 replay took about 1.5 seconds, and the search and reduction took about 18 seconds.

### Regression fixtures

[`tests/script/campaign/`](../tests/script/campaign/README.md) keeps each understood counterexample of the campaign as a fixture ([design record 0009, section 10](design/0009-bug-finding-campaign.md#10-regression-and-proof-follow-up)).
The fixtures reuse the format of `tests/oracle`: `script.verify_legacy` requests, and the expected response on the same line of another file.
`expected.jsonl` gives the baseline response. `expected-faulty.jsonl` and `expected-corrected.jsonl` give the responses of `proposal-replay` for each variant, with `--active`.

The README of the directory records the property, the plan, the run, both revisions, the reduction and the source of each expected value.
`lake test` checks the expected values, and `scripts/compare_core.py` sends the requests to both programs as the set `Script campaign fixtures`.
A person reviews a candidate before it becomes a fixture.
A candidate that can be a vulnerability becomes a fixture only after its report is resolved ([section 9.4](design/0009-bug-finding-campaign.md#94-a-real-finding)).
