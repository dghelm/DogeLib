# The oracle and its record format

`dogelib-oracle` runs DogeLib's specification on requests from another program, such as a harness that runs Dogecoin Core on the same inputs.
This document defines its record format, `dogelib-oracle/1`.
A change to the format needs a maintainer's approval ([AGENTS.md](../AGENTS.md#changes-that-need-a-maintainer)) and a new format name.

The oracle models Core's serialization and its legacy signature hash.
It reads transactions in base mode only, the format without witness data.
It checks no consensus rule. Its output says what Core's code computes for an input, not that the input is valid on any network.

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
| `request` | The oracle could not interpret the request. Examples: invalid JSON, an unknown `op`, a missing or unknown argument, or a value out of range. | `message`, free text for a person. It is not part of the format. |
| `read` | The reader of the specification rejects the bytes, as Core's stream would. | `reason`: `truncated` (the input ends early), `non_canonical` (a CompactSize value in a longer form than needed) or `too_large` (a CompactSize value above `MAX_SIZE`, `0x02000000`). For `sighash.legacy`, `argument` names the argument that failed. |
| `trailing_bytes` | A transaction was read and bytes remain. | `count`: the number of bytes after the transaction. For `sighash.legacy`, `argument`. |

Only `request` errors come from the oracle itself. The other kinds are results of the specification.

## Operations

| `op` | Arguments | `ok` fields | Specification |
| --- | --- | --- | --- |
| `oracle.version` | none | `format`: `"dogelib-oracle/1"` | none |
| `compactsize.encode` | `value`: `u64` | `bytes_hex` | `CompactSize.encode`, Core's `WriteCompactSize` |
| `compactsize.read` | `bytes_hex` | `value` (`u64`), `consumed`, `rest_hex` | `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check |
| `tx.read_base` | `bytes_hex` | `tx`, `consumed`, `rest_hex` | `Transaction.readBase`: a transaction at the start of the bytes, as Core reads the next transaction of a stream |
| `tx.decode_base` | `bytes_hex` | `tx`, `serialized_hex`, `txid_hex`, `txid_display` | `Transaction.decodeBaseComplete`: a transaction that is all of the bytes. Then its base serialization and its ID, `Transaction.txid` |
| `sighash.legacy` | `tx_hex`, `script_code_hex`, `input_index` (`u32`), `hash_type` | `plan`, `preimage_hex` (for `hash_bytes` only), `digest_hex`, `digest_display` | `tx_hex` is read as by `tx.decode_base`. Then `legacySignatureHashPlan` and `LegacyHashPlan.digest`: Core's `SignatureHash` with `SIGVERSION_BASE` |

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

`plan` is `fixed_digest` or `hash_bytes`.
`fixed_digest` is Core's early return of the value one, when `input_index` names no input, or names no output under `SIGHASH_SINGLE`.
`hash_bytes` gives the preimage that Core hashes, so that a mismatch can be traced to its first differing byte.
`script_code_hex` is the script code as Core's `SignatureHash` receives it. `SignatureHash` itself leaves out each `OP_CODESEPARATOR`, and so does the specification. The work of Core's callers before that call, such as removing the signature from the script code, is not modeled.

## Not in this format

These operations are planned, and each would need a new format name:

- The witness-allowed mode of Core's transaction reader (issue #23).
  It models a serialization format that Core's code can read. It does not mean that segregated witness is active on any Dogecoin network.
- Building a transaction from its fields.

A harness that runs Dogecoin Core on the same requests does not exist yet.

## Tests

`scripts/test_oracle.sh` builds the oracle and runs `scripts/test_oracle.py`.
`tests/oracle/README.md` gives the source of each expected value.
