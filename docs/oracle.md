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
| `trailing_bytes` | A transaction was read and bytes remain. | `count`: the number of bytes after the transaction. For `sighash.legacy`, `argument`. |

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
No operation checks transaction validity, witness commitments or full block validity.

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
| `block.check_version` | `bytes_hex`, exactly 80 bytes, `network`, `selection_height` | Boolean `valid`, and Lean-only `diagnostic` |

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

## The Core harness

`harness/core/core_oracle.cpp` answers the same requests by running Dogecoin Core's own code.
It is built against Core v1.14.9 at commit `e0a1c15`, the pin in [SOURCES.md](../SOURCES.md).
`scripts/compare_core.py` runs the harness and the oracle on one stream of requests and requires their responses to agree.
CI runs the comparison in workflow `core`, job `compare`.

```bash
lake build dogelib-oracle
scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
python3 -I scripts/test_compare_core.py .lake/build/bin/dogelib-oracle
python3 -I scripts/compare_core.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

The build also produces `core-signer`, a fixture generator that calls Core's `SignatureHash`, `CKey::Sign` and `VerifyScript`.
Its fixed private keys are public test data.
[Signed recovery-template fixtures](../tests/script/signed-spends/README.md) record its inputs, signatures, Core verdicts and reproduction commands.
It runs outside the oracle comparison loop.

The build script exports the pinned commit from the clone with `git archive`.
The clone must contain that commit, but its working tree may be at any other.
It builds Core's consensus, cryptography and secp256k1 libraries, and compiles Core's bundled UniValue to read the requests.
It needs autoconf, automake, libtool, pkg-config, OpenSSL's development files and Boost headers (`libboost-dev` on Ubuntu).
It links no Boost library.

The work functions and parameter constructors use these Core objects: `pow.cpp`, `chain.cpp`, `dogecoin.cpp`, `chainparams.cpp` and `chainparamsbase.cpp`, plus `auxpow.cpp` and `checkpoints.cpp` for the header checks.
Function and data sections, with linker garbage collection, discard unrelated server functions and their dependencies.
The build assumes GNU ld for `--gc-sections`, as Linux CI does.
These pinned sources supply the additional objects:

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
| `block.header_sequence` | H2 transcription of `AcceptBlockHeader`, the index part of `AddToBlockIndex` and the sequence loop, with Core helpers |
| `block.contextual_check` | H2 transcription of `ContextualCheckBlockHeader`, with Core helpers for every compared value |
| `compactsize.encode` | `WriteCompactSize` into a `CDataStream` |
| `compactsize.read` | `ReadCompactSize` from a `CDataStream` |
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

### The comparison

`scripts/compare_core.py` gives each request its own `id` and sends both programs the same text.
For supported requests, the two responses must be equal as JSON values, subject to the signature-preimage and Lean-diagnostic projections below.
For `script.eval` and `script.verify_legacy`, an unsupported Lean result excludes that request from verdict agreement.
The comparator validates both result shapes and the checker-specific unsupported reasons, then reports the unsupported reason and Core outcome separately.
An adapter error is not an unsupported result.

For `sighash.legacy` with plan `hash_bytes`, the double SHA-256 of the oracle's `preimage_hex` must equal Core's `digest_hex`.
This checks the preimage against Core's digest, not byte by byte against a preimage from Core.
Outside the checked `harness-refused` category, a request error from either program fails the comparison.

The comparison with Core `e0a1c157791544e818c901bd9341896965afbf9d` passes 382,680 stream requests.
The pull request records the tested DogeLib revision.
It reported zero failures, including 12 checked harness refusals, plus 22 adapter-limit cases and the 1,193 two-call compositions.
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
The witness mutations change `wtxid_hex`, a stack and `has_witness`.
The work mutations change the magnitude, both flags, the encoded compact and each work operation's result bits.

Hash mutations change each digest operation.
Block mutations change every header field, encoding, both hash orders, consumption, remainder and truncation.
They also change both Merkle root orders and the mutation flag.
Script mutations change reader fields, evaluation classes, rejection errors, success errors, final stacks and unsupported fields.
An informational Core result for an unsupported request can differ without a comparison failure.

One mutation runs the full composition path and corrupts a successful second-call stack.
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

The harness uses H2 of [design record 0006](design/0006-contextual-header-validation.md#82-the-core-side).
`contextualReject` transcribes D33, lines 3066 to 3119, replacing validation-state returns with reject-reason strings.
Core computes each compared value through `GetConsensus`, `IsLegacy`, `IsAuxpow`, `GetNextWorkRequired`, `GetMedianTimePast`, `GetBaseVersion` and `Checkpoints::GetLastCheckpoint`.

The harness owns `mapBlockIndex` and `fCheckpointsEnabled` and links `checkpoints.cpp`.
Each known height adds the corresponding table hash with that height to the block index.
The comparison uses a transcription, rather than the function in `validation.cpp`.
A source review must compare the transcription line by line with D33.

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

### Header-sequence comparison evidence

The harness follows H2 of [design record 0008](design/0008-header-sequence-validation.md#82-the-core-side).
It transcribes D33, lines 3205 to 3286 and 2755 to 2788, with citations beside the ordered branches.
The index transcription omits `nTimeMax` (2779), the best-header pointer (2782 to 2783) and the dirty set (2785).

It calls Core's `CheckAuxPowProofOfWork`, `GetAncestor`, `BuildSkip`, `GetBlockProof` and `Checkpoints::GetLastCheckpoint`.
The contextual step reuses `contextualReject`, with the Core helpers listed above.
The harness owns the index and visits the failed list in request order, rather than pointer-address order.
Source review must check these transcriptions against the pinned passages.

Two guards keep anchor walks inside their represented chains.
`sequenceSkip` calls `BuildSkip` only when the skip destination is at or above the branch anchor.
`sequenceAncestor` returns null for a height below that anchor and otherwise calls Core's `GetAncestor`.
Before contextual validation, the harness refuses short median, recovery and retarget histories.
So `GetNextWorkRequired` cannot call `GetAncestor` below an anchor at `pow.cpp:84`.

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

`scripts/campaign.py` checks Q1 to Q7 from [design record 0009](design/0009-bug-finding-campaign.md#11-properties).
It reuses `compare` from `scripts/compare_core.py` without changing the CI comparison stream.
The default campaign shuffles existing requests with the selected seed and sends fixed-size batches.
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
Reduction and production-path replay remain later stages of design record 0009.
The campaign commands do not run in CI at this stage.
