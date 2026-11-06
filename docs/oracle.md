# The oracle and its record format

`dogelib-oracle` runs DogeLib's specification on requests from another program, such as a harness that runs Dogecoin Core on the same inputs.
This document defines its record format, `dogelib-oracle/6`.
The oracle supports only this format.
Format `/6` exposes Script instruction reading, evaluation with a selected checker, and verification of one legacy input.
The earlier operations keep their request fields, response shapes and behavior.
Only the format name changes for them.

A change to the format needs a maintainer's approval ([AGENTS.md](../AGENTS.md#changes-that-need-a-maintainer)) and a new format name.

The oracle models Core's serialization, legacy signature hash, work arithmetic, byte-string hashes, pure block commitments and individual Script calls.
It reads transactions in base mode or with witness data allowed.
The witness operations model a serialization format only.
Segregated witness is not active on Dogecoin at the pin.
`IsWitnessEnabled` returns false, and main and test reject blocks with witness data (SOURCES.md D36).

Its [protocol context](../SOUNDNESS.md#transactions-the-witness-allowed-format) separates witness script verification from the commitment checks in Core.
Its output describes an operation under supplied flags, without a claim that an input is valid on any network.
In particular, `script.eval` does not check a complete spend.

## Running it

```bash
lake build dogelib-oracle
.lake/build/bin/dogelib-oracle             # answer requests on standard input
.lake/build/bin/dogelib-oracle --version   # print {"format":"dogelib-oracle/6"}
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
| `work_view` | The finite work view cannot supply a result. The view errors describe the adapter, not consensus rejection codes. | `reason`: `height_out_of_range`, `inconsistent_heights`, `missing_ancestor`, `first_height_underflow` or `zero_interval`. The last two are unreachable with these network parameters and checked views. |
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
| `oracle.version` | none | `format`: `"dogelib-oracle/6"` | none |
| `compactsize.encode` | `value`: `u64` | `bytes_hex` | `CompactSize.encode`, Core's `WriteCompactSize` |
| `compactsize.read` | `bytes_hex` | `value` (`u64`), `consumed`, `rest_hex` | `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check |
| `tx.read_base` | `bytes_hex` | `tx`, `consumed`, `rest_hex` | `Transaction.readBase`: a transaction at the start of the bytes, as Core reads the next transaction of a stream |
| `tx.decode_base` | `bytes_hex` | `tx`, `serialized_hex`, `txid_hex`, `txid_display` | `Transaction.decodeBaseComplete`: a transaction that is all of the bytes. Then its base serialization and its ID, `Transaction.txid` |
| `tx.read_witness` | `bytes_hex` | Witness result, `consumed`, `rest_hex` | `Transaction.readAllowWitness`: a prefix with witness data allowed |
| `tx.decode_witness` | `bytes_hex` | Witness result | `Transaction.decodeAllowWitnessComplete`: the whole input with witness data allowed |
| `sighash.legacy` | `tx_hex`, `script_code_hex`, `input_index` (`u32`), `hash_type` | `plan`, `preimage_hex` (for `hash_bytes` only), `digest_hex`, `digest_display` | `tx_hex` is read as by `tx.decode_base`. Then `legacySignatureHashPlan` and `LegacyHashPlan.digest`: Core's `SignatureHash` with `SIGVERSION_BASE` |
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
`transaction` runs `verifyLegacySpend` with the transaction context and an unavailable signature verifier.
It still checks signature encodings, hashes and transaction lock-time conditions when execution requires them.
Only a call to the unavailable verifier gives `signature_verifier`.
Malformed keys or empty signatures can give a verdict without that call.

The operation returns these `ok` shapes:

```json
{"result":"accepted","script_error":"OK"}
{"result":"rejected","script_error":"EVAL_FALSE"}
{"result":"unsupported","reason":"signature_verifier","opcode":172}
{"result":"unsupported","reason":"flags","bits":64}
```

Acceptance is the `VerifyScript` verdict under the supplied context and flags, with P2SH when requested.
It is not full transaction validity.
No response returns an intermediate stack.

The unsupported verifier opcode is one of CHECKSIG, CHECKSIGVERIFY, CHECKMULTISIG or CHECKMULTISIGVERIFY (172 through 175).
For `base`, only `flags` can be unsupported.
For `transaction`, only `flags` or `signature_verifier` can be unsupported.
Neither kind of unsupported result is a Script rejection or comparison agreement.

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

The build script exports the pinned commit from the clone with `git archive`.
The clone must contain that commit, but its working tree may be at any other.
It builds Core's consensus, cryptography and secp256k1 libraries, and compiles Core's bundled UniValue to read the requests.
It needs autoconf, automake, libtool, pkg-config, OpenSSL's development files and Boost headers (`libboost-dev` on Ubuntu).
It links no Boost library.

The work functions and parameter constructors require five additional Core objects: `pow.cpp`, `chain.cpp`, `dogecoin.cpp`, `chainparams.cpp` and `chainparamsbase.cpp`.
Function and data sections, with linker garbage collection, discard unrelated server functions and their dependencies.
The build assumes GNU ld for `--gc-sections`, as Linux CI does.
These pinned sources supply the additional objects:

| Source | Role |
| --- | --- |
| [D17, `src/pow.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pow.cpp) | `GetNextWorkRequired` |
| [D35, `src/chain.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chain.cpp) | `BuildSkip`, `GetAncestor` and the skip-height guard |
| [D6, `src/dogecoin.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/dogecoin.cpp) | `CalculateDogecoinNextWorkRequired` and minimum-difficulty permission |
| [D14, `src/chainparams.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp) | Network parameter records, `SelectParams` and `GetConsensus` |
| [D39, `src/chainparamsbase.cpp`](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparamsbase.cpp) | `SelectBaseParams`, called by `SelectParams` |

### What the harness runs

| `op` | Core's code |
| --- | --- |
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

The harness answers a projection of `dogelib-oracle/6`, not the format itself:

- `--version` and `oracle.version` give the format `dogelib-oracle/6-core-projection`.
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
Eighteen adapter-limit boundary requests check both programs against the documented expectations, including `adapter/resource_limit` errors.
Other argument checks have oracle fixtures but no Core comparison.

### The comparison

`scripts/compare_core.py` gives each request its own `id` and sends both programs the same text.
For supported requests, the two responses must be equal as JSON values, subject to the signature-preimage projection below.
For `script.eval` and `script.verify_legacy`, an unsupported Lean result excludes that request from verdict agreement.
The comparator validates both result shapes and the checker-specific unsupported reasons, then reports the unsupported reason and Core outcome separately.
An adapter error is not an unsupported result.

For `sighash.legacy` with plan `hash_bytes`, the double SHA-256 of the oracle's `preimage_hex` must equal Core's `digest_hex`.
This checks the preimage against Core's digest, not byte by byte against a preimage from Core.
Outside the checked `harness-refused` category, a request error from either program fails the comparison.

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
- Hand-built cases from the known answers in `tests/KnownAnswers.lean` (`Witness.cases`).
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
  Core must accept all 91 accept inputs with its transaction checker, even when Lean reaches its unavailable verifier.
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
- Eighteen adapter-limit requests sent to both programs, with results checked against the documented limits.
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
They also corrupt the unavailable verifier's opcode and fields.

Two refusal mutations replace either the required Core refusal or Lean's unsupported-flags answer with a verdict.
Each must fail with its own refusal error code, and the failed refusal must stay outside the compared count.
A transaction-corpus mutation makes Core reject an accept input where Lean reaches the unavailable verifier.
That mutation must fail the independent Core acceptance requirement.

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
