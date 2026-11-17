# Signed recovery-template spends

`recovery.jsonl` contains 25 signed spends and mutations from design record 0005, section 8.
The source of every digest, signature and expected verdict is Dogecoin Core at `e0a1c157791544e818c901bd9341896965afbf9d` ([SOURCES.md](../../../SOURCES.md)).
No DogeLib result supplies an expectation.
`lake test` runs all 25 records through `verifyLegacySpend` with `coreVerifier`, using each record's flags.
It compares both the Boolean verdict and the ScriptError name, and rejects every unsupported result.

For the four baselines, a compiled sanity check also checks the premises of `multisigRecovery_sound_coreVerifier`.
It checks the template commitment, supported flags, key lengths, push-only input and successful `scriptSig` evaluation with the redeem script last.
Acceptance supplies the remaining premise.
This check constructs no proof term.
The Core comparison sends the same records through `script.verify_legacy` with the transaction checker and rechecks them against live Core.

## Provenance

`harness/core/core_signer.cpp` constructs the 2-of-3 instance of `DogeLib.Script.multisigRecoveryScript` and its P2SH output.
Private scalars 1, 2 and 3 are the multisig keys, and scalar 4 is the recovery key.
These private keys are public test data for fixtures only.
Never send funds to these keys.

The generator calls Core's `SignatureHash` in `SIGVERSION_BASE`, `CKey::Sign` with `test_case=0`, and `VerifyScript` with `TransactionSignatureChecker`.
`CKey::Sign` uses RFC 6979 nonces and emits low-S DER signatures (`src/key.cpp`, lines 169–182).
It appends `SIGHASH_ALL` to each signature.
`ECC_Start` blinds the signing context with randomness, but that blinding does not change the deterministic signatures.
The generator uses Core's `random.cpp` and a stderr adapter for `LogPrintStr`.

The build script exports the pinned Core tree and uses its consensus, cryptography and secp256k1 libraries.
It also compiles Core's `key.cpp`, `random.cpp`, `support/lockedpool.cpp`, `support/cleanse.cpp` and UniValue.
The build uses C++11, `-O2`, function and data sections, linker garbage collection, OpenSSL and pthreads.
The configure options disable the daemon, utilities, GUI, wallet, tests, benchmarks, ZMQ and MiniUPnPc, and select static libraries with PIC.
`scripts/build_core_harness.sh` records the Core pin, compilers and flags in `build/core-harness/core.stamp`.
The first fixture generation used x86_64 Linux and GCC 16.2.1.

## Records

Each JSONL record contains these fields:

| Field | Meaning |
| --- | --- |
| `id`, `mutation`, `changed_field` | Case identifier, section 8 mutation and changed field. Baselines use `none`. |
| `core_revision`, `generator`, `generator_source_blob` | Core compatibility pin, generator source path and its Git blob identifier |
| `branch`, `keys`, `signers` | Intended branch, fixed private and public keys, and signer identifiers in signing order |
| `unsigned_tx_hex` | Base serialization of the transaction passed to `SignatureHash`, with an empty `scriptSig` |
| `digest_hex`, `signatures_hex` | Signing digest in Core storage order and the original signatures, including the hash-type byte |
| `spend_signatures_hex` | Signatures pushed into the spend, after high-S conversion or order reversal |
| `redeem_script_hex`, `script_pubkey_hex` | Redeem script and the P2SH output that commits to it |
| `tx_hex`, `spend_digest_hex` | Signed transaction and its digest after mutation, in Core storage order |
| `input_index`, `amount`, `hash_type`, `flags` | Arguments to Core's checker and signature hash. The amount is unused in base mode. |
| `resigned` | Whether signing uses the mutated transaction rather than the baseline transaction |
| `core_valid`, `core_error` | Core's `VerifyScript` Boolean verdict and ScriptError name |

All transactions have one input and one output.
The baseline has version 1, lock time 1,000,000, sequence `0xfffffffe`, output value 100,000,000 and output script `OP_TRUE`.
The outpoint is synthetic, so the fixtures check Script execution rather than UTXO availability or contextual transaction validity.
The flags are `P2SH`, `STRICTENC`, `DERSIG`, `LOW_S`, `NULLDUMMY` and `CHECKLOCKTIMEVERIFY` (numeric value 543).
The high-S acceptance cases clear `LOW_S`, and the hybrid-key acceptance case clears `STRICTENC`.
The companion hybrid-key case keeps `STRICTENC` and records Core's `PUBKEYTYPE` rejection.

The four baseline records cover signer pairs (1, 2), (1, 3), (2, 3), and the recovery branch.
Both branches have committed-field, selector and high-S mutations.
Each multisig high-S case changes only the first signature.
The remaining records cover reversed multisig signatures, both low-locktime signing choices, and a stale signature at lock time 1,000,001.
They also cover a final sequence and a hybrid recovery key under both settings of `STRICTENC`.

The hybrid key uses the uncompressed coordinates with the matching `06` or `07` parity prefix.
Core supplies each verdict, including `UNSATISFIED_LOCKTIME`, `SIG_HIGH_S`, `EVAL_FALSE` and `INVALID_STACK_OPERATION`.

## Reproduction

Build the harness and generate the fixtures with these commands:

```bash
JOBS=8 taskset -c 24-31 scripts/build_core_harness.sh <dogecoin-git-clone> build/core-harness
build/core-harness/core-signer > .lane/recovery.jsonl
cmp tests/script/signed-spends/recovery.jsonl .lane/recovery.jsonl
python3 -I scripts/check_signed_spends.py build/core-harness/core-signer
(cd tests/script/signed-spends && sha256sum -c SHA256SUMS)
```

Choose available CPUs when the machine has fewer than 32.
The generator takes no arguments and writes only JSONL to stdout.
The regeneration check requires byte-for-byte agreement and never rewrites committed expectations.
The Core CI job runs that check after the harness build.

## Fixed-digest spends

`fixed-digest.jsonl` contains 44 signed spends that reach, or just miss, the fixed digest of `SIGHASH_SINGLE`.
Core's `SignatureHash` returns the digest `one` when the hash type is SINGLE and the input index is at least the number of outputs (`src/script/interpreter.cpp`, lines 1225 to 1236).
The source of every digest, signature and expected verdict is Dogecoin Core at the same revision.
No DogeLib result supplies an expectation.

`lake test` runs all 44 records through `verifyLegacySpend` with `coreVerifier`, and compares the Boolean verdict and the ScriptError name.
It compares `legacySignatureHash` with each recorded digest, 142 in all.
For the 37 records with at most `input_index` outputs and only SINGLE hash types, it also runs `verifyScript` with `fixedDigestChecker`, which has no transaction.
That call is the right side of `verifyLegacySpend_eq_fixedDigest` in `DogeLib.Script.Proofs.FixedDigest`, and it must give Core's verdict.
The Core comparison sends the 44 spends through `script.verify_legacy` and their 71 signature hashes through `sighash.legacy`, and rechecks them against live Core.

### Provenance

`harness/core/core_signer_fixed_digest.cpp` builds five kinds of output script for the test keys with private scalars 1, 2 and 3:

| `coin` | Script |
| --- | --- |
| `p2pkh` | `OP_DUP OP_HASH160 <HASH160 P1> OP_EQUALVERIFY OP_CHECKSIG` |
| `multisig` | `OP_2 <P1> <P2> <P3> OP_3 OP_CHECKMULTISIG` |
| `p2sh-multisig` | `OP_HASH160 <HASH160 redeem> OP_EQUAL`, where `redeem` is the `multisig` script |
| `…-codeseparator` | The same script with `OP_CODESEPARATOR` before its signature opcode |
| `…-verify` | The same script with `OP_CHECKSIGVERIFY OP_1` or `OP_CHECKMULTISIGVERIFY OP_1` in place of its signature opcode |

The signing transaction has two inputs and one output, and the generator signs input 1.
The generator calls `SignatureHash` in `SIGVERSION_BASE`, `CKey::Sign` with `test_case=0` and `VerifyScript` with `TransactionSignatureChecker`, as for `recovery.jsonl`.
`CKey::Sign` uses RFC 6979 nonces, so each key has one signature for the digest `one`.
For a given key, the recorded signatures over `one` therefore differ only in their last byte, the hash type.
The private keys are public test data. Never send funds to these keys.

### Records

| Field | Meaning |
| --- | --- |
| `id`, `group`, `change` | Case identifier, its group, and the fields of the spend that differ from the signing transaction |
| `core_revision`, `generator` | Core compatibility pin and the generator source path |
| `keys`, `signers`, `hash_types` | The fixed keys, the signers in signature order and the hash-type byte of each signature |
| `signing_coin`, `signing_tx_hex`, `signing_input_index`, `signing_script_code_hex` | The arguments of the `SignatureHash` call that each signature signs |
| `digests_hex`, `signatures_hex` | Core's digest for each signing call, in Core storage order, and each signature with its hash-type byte |
| `coin`, `script_pubkey_hex`, `redeem_script_hex`, `script_code_hex` | The spent output script, its redeem script if it has one, and the script code that `EvalScript` passes to `CheckSig` |
| `tx_hex`, `input_index`, `output_count` | The signed spending transaction, the spent input and the number of outputs |
| `spend_digests_hex` | Core's `SignatureHash` of the spending transaction for each hash type |
| `flags` | The flags of `VerifyScript`: 543 as for `recovery.jsonl`, or 541 with `STRICTENC` clear |
| `core_valid`, `core_error` | Core's `VerifyScript` Boolean verdict and ScriptError name |

The groups:

| `group` | Records | Core's verdict |
| --- | ---: | --- |
| `baseline` | 5 | Accepted: the spend is the signing transaction |
| `transplant` | 17 | Accepted: the same signatures in another spend whose input index is at least its number of outputs |
| `hash type` | 3 | Accepted: `0x83`, SINGLE with ANYONECANPAY |
| `boundary` | 5 | Rejected: the spend has one more output, so its digest is not `one` |
| `undefined hash type` | 12 | `0x23`, `0xa3` and `0xe3`: accepted with `STRICTENC` clear, and `SIG_HASHTYPE` with it set |
| `mixed hash types` | 2 | One SINGLE and one ALL signature: accepted in the signing transaction, and rejected after a change of the outpoint |

A `transplant` record changes one group of fields: the outpoint and sequence of the input, the index, or the number of outputs.
Other records change the version, lock time and output, or the script code.
The rejections of the `boundary` group are `EVAL_FALSE`, `CHECKSIGVERIFY` and `CHECKMULTISIGVERIFY`.

### Reproduction

```bash
build/core-harness/core-signer --fixed-digest > .lane/fixed-digest.jsonl
cmp tests/script/signed-spends/fixed-digest.jsonl .lane/fixed-digest.jsonl
python3 -I scripts/check_signed_spends.py build/core-harness/core-signer
```

The regeneration check requires byte-for-byte agreement for both fixture files.
