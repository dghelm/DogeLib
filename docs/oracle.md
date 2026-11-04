# The oracle and its record format

`dogelib-oracle` runs DogeLib's specification on requests from another program, such as a harness that runs Dogecoin Core on the same inputs.
This document defines its record format, `dogelib-oracle/2`.
The oracle supports only this format.
Compared with `dogelib-oracle/1`, prior operations keep their request fields, response shapes and behavior, and only the version string changes.
A change to the format needs a maintainer's approval ([AGENTS.md](../AGENTS.md#changes-that-need-a-maintainer)) and a new format name.

The oracle models Core's serialization and its legacy signature hash.
It reads transactions in base mode or with witness data allowed.
The witness operations model a serialization format only.
Segregated witness is not active on Dogecoin at the pin.
`IsWitnessEnabled` returns false, and main and test reject blocks with witness data (SOURCES.md D36).

Its [protocol context](../SOUNDNESS.md#transactions-the-witness-allowed-format) separates witness script verification from the commitment checks in Core.
It checks no consensus rule. Its output says what Core's code computes for an input, not that the input is valid on any network.

## Running it

```bash
lake build dogelib-oracle
.lake/build/bin/dogelib-oracle             # answer requests on standard input
.lake/build/bin/dogelib-oracle --version   # print {"format":"dogelib-oracle/2"}
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
| `read` | The reader of the specification rejects the bytes, as Core's stream would. | `reason`: `truncated` (the input ends early), `non_canonical` (a CompactSize value in a longer form than needed), `too_large` (a CompactSize value above `MAX_SIZE`, `0x02000000`), or `unknown_optional_data` (a transaction flag bit other than bit 0 remains after the input and output lists and any stacks). For `sighash.legacy`, `argument` names the argument that failed. |
| `trailing_bytes` | A transaction was read and bytes remain. | `count`: the number of bytes after the transaction. For `sighash.legacy`, `argument`. |

Only `request` errors come from the oracle itself. The other kinds are results of the specification.

## Operations

| `op` | Arguments | `ok` fields | Specification |
| --- | --- | --- | --- |
| `oracle.version` | none | `format`: `"dogelib-oracle/2"` | none |
| `compactsize.encode` | `value`: `u64` | `bytes_hex` | `CompactSize.encode`, Core's `WriteCompactSize` |
| `compactsize.read` | `bytes_hex` | `value` (`u64`), `consumed`, `rest_hex` | `CompactSize.decodeBounded`, Core's `ReadCompactSize` with its `MAX_SIZE` check |
| `tx.read_base` | `bytes_hex` | `tx`, `consumed`, `rest_hex` | `Transaction.readBase`: a transaction at the start of the bytes, as Core reads the next transaction of a stream |
| `tx.decode_base` | `bytes_hex` | `tx`, `serialized_hex`, `txid_hex`, `txid_display` | `Transaction.decodeBaseComplete`: a transaction that is all of the bytes. Then its base serialization and its ID, `Transaction.txid` |
| `tx.read_witness` | `bytes_hex` | Witness result, `consumed`, `rest_hex` | `Transaction.readAllowWitness`: a prefix with witness data allowed |
| `tx.decode_witness` | `bytes_hex` | Witness result | `Transaction.decodeAllowWitnessComplete`: the whole input with witness data allowed |
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
It needs autoconf, automake, libtool, pkg-config and OpenSSL's development files.

### What the harness runs

| `op` | Core's code |
| --- | --- |
| `compactsize.encode` | `WriteCompactSize` into a `CDataStream` |
| `compactsize.read` | `ReadCompactSize` from a `CDataStream` |
| `tx.read_base` | `CMutableTransaction` read from a `CDataStream` whose version has `SERIALIZE_TRANSACTION_NO_WITNESS`, so `UnserializeTransaction` reads base mode |
| `tx.decode_base` | The same read, then a check that the stream is empty. The transaction written back to a stream of the same version, and `CTransaction::GetHash` |
| `tx.read_witness`, `tx.decode_witness` | `CMutableTransaction` read from a `CDataStream` without `SERIALIZE_TRANSACTION_NO_WITNESS`. The complete operation requires an empty stream. Both write with witness data allowed and call `CTransaction::HasWitness`, `GetHash` and `GetWitnessHash`. |
| `sighash.legacy` | `tx_hex` read as by `tx.decode_base`. Then `SignatureHash` with amount 0 and `SIGVERSION_BASE` |

### How its responses differ

The harness answers a projection of `dogelib-oracle/2`, not the format itself:

- `--version` and `oracle.version` give the format `dogelib-oracle/2-core-projection`.
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
The comparison sends only well-formed requests, so it does not test those checks.

### The comparison

`scripts/compare_core.py` gives each request its own `id` and sends both programs the same text.
For each request the two responses must be equal as JSON values, with one exception.
For `sighash.legacy` with plan `hash_bytes`, the double SHA-256 of the oracle's `preimage_hex` must equal Core's `digest_hex`.
This checks the preimage against Core's digest, not byte by byte against a preimage from Core.
A request error from either program fails the comparison.

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

`scripts/test_compare_core.py` checks that the comparison can fail.
A wrapper around the oracle stands in for the harness.
Unchanged, it must pass on the full stream. Each of 25 mutations must fail with the failure code that it targets.
The witness mutations change `wtxid_hex`, a stack and `has_witness`.

Agreement covers the requests in the stream and nothing more.
