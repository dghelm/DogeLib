# Legacy spend validation

**Status:** Adopted by the maintainer on 2026-11-04.
This record is frozen.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-04
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [architecture](../../ARCHITECTURE.md) and [oracle contract](../oracle.md).

## 1. Purpose and boundary

This record sets the scope for an executable specification of legacy Script spends, with properties conditional on an explicit signature verifier.
It connects transaction fields and legacy signature hashing to the Script rules that consume them.
The first milestone covers `VerifyScript(scriptSig, scriptPubKey, emptyWitness, flags, checker)` in `SIGVERSION_BASE` for the selected flags below.
It does not establish transaction, UTXO, block or chain validity.
Implementation refinement and Rust extraction are outside this milestone.

DogeLib already specifies raw transactions and the legacy signature hash.
Its transformation-reference theorem requires fully parsed script code and fewer than 2^32 inputs and outputs.
Successful Core-compatible transaction reads discharge the count bounds, but the caller still supplies the script-code hypothesis.
The [reader corollaries](../../DogeLib/Transaction/Proofs/LegacySighashReader.lean) state that boundary.
Script execution, signature checking and interpreter preparation of script code remain outside the [implemented coverage](../../COVERAGE.md).
The execution and spend theorems proposed here are targets, not implemented results.

The milestone excludes witness execution, witness signature hashing, activation calculation, transaction finality, relative sequence locks against chain history and block sigop limits.
Core's `IsWitnessEnabled` returns false on every network at the reference software revision [C6].
The separate witness-serialization definitions do not establish witness consensus acceptance, as [SOUNDNESS.md](../../SOUNDNESS.md#transactions-the-witness-allowed-format) explains.
Bytes that resemble witness programs retain their ordinary legacy meaning when witness flags are absent.

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
D36 identifies block validation and D9 identifies chain parameters in that registry.
The line ranges identify the inspected source for each contract:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [interpreter.h, lines 30–108](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.h#L30-L108) | Flag bits and meanings. |
| C2 | [interpreter.cpp, lines 38–50 and 110–223](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L38-L223) | Boolean conversion, signature encoding and public-key encoding. |
| C3 | [interpreter.cpp, lines 248–1046](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L248-L1046) | `EvalScript`, including limits, errors and signature operations. |
| C4 | [interpreter.cpp, lines 1248–1353](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1248-L1353) | Signature, locktime and sequence checkers. |
| C5 | [interpreter.cpp, lines 1409–1533](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1409-L1533) | `VerifyScript` and P2SH composition. |
| C6 | [validation.cpp, lines 1890–1917](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1890-L1917), [lines 3002–3008](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3002-L3008) | Block flag selection and disabled witness verification. |
| C7 | [policy.h, lines 88–105](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/policy/policy.h#L88-L105), [standard.h, lines 43–44](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/standard.h#L43-L44) | Standard policy flags and the mandatory-flags constant. |
| C8 | [script.h, lines 23–35](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script.h#L23-L35), [lines 199–374](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script.h#L199-L374) | Script limits, locktime threshold and `CScriptNum`. |
| C9 | [script.h, lines 418–464](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script.h#L418-L464), [lines 502–596](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script.h#L502-L596) | Push construction, `GetOp2` and `FindAndDelete`. |
| C10 | [script.cpp, lines 204–211 and 239–258](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script.cpp#L204-L258) | Exact P2SH template and `IsPushOnly`. |
| C11 | [script_error.h, lines 9–73](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/script_error.h#L9-L73) | `ScriptError` categories. |
| C12 | [pubkey.cpp, lines 132–187](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pubkey.cpp#L132-L187), [lines 289–295](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/pubkey.cpp#L289-L295) | Key parsing, lax DER parsing, S normalization and `CheckLowS`. |
| C13 | [script_tests.cpp, lines 123–169](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/script_tests.cpp#L123-L169), [lines 955–997](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/script_tests.cpp#L955-L997) | Script fixture construction and interpretation. |
| C14 | [transaction_tests.cpp, lines 97–262](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/transaction_tests.cpp#L97-L262) | Transaction corpus interpretation. |
| C15 | [script_tests.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/script_tests.json), lines 1–7 | Script cases and their construction context. |
| C16 | [tx_valid.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_valid.json), [tx_invalid.json](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/data/tx_invalid.json) | Transaction cases, with previous-output scripts and flags. |
| C17 | [chainparams.cpp, lines 86–87](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L86-L87), [lines 102–106](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/chainparams.cpp#L102-L106) | Mainnet BIP65/BIP66 heights and CSV deployment window (D9). |
| C18 | [rpc/blockchain.cpp, lines 1146–1174](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/rpc/blockchain.cpp#L1146-L1174), [lines 1252–1263](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/rpc/blockchain.cpp#L1252-L1263) | CSV status in `getblockchaininfo`. |

The cited findings come from source inspection, without a Core comparison run.
Implementation lanes must add operation mappings and fixture provenance to the existing registries without changing the pin.

## 3. Contract for implementation

### Inputs and results

The transaction context contains a raw `Transaction`, an input index representable as `UInt32`, and evidence that the index selects an input.
The typed context also requires fewer than 2^32 inputs and outputs.
Core-compatible transaction reads discharge those bounds, and callers of field-built transactions must supply them.
The spend operation uses that input's exact `scriptSig` and the caller's exact previous-output `scriptPubKey`.
It receives selected flags and a deterministic verifier parameter.

No previous-output amount enters legacy hashing, because `SIGVERSION_BASE` ignores that argument.
The caller establishes that the previous-output script belongs to the referenced outpoint.
The operation does not query a UTXO set.

The pure contract distinguishes these results:

- `accepted`: the two script evaluations and any P2SH evaluation satisfy Core's true-top requirement.
- `rejected(error)`: supported semantics reach a Core `ScriptError`, with Core's first-error order.
- `unsupported(feature)`: the requested flag or required operation lacks an implementation at this stage.

The adapter separately reports malformed requests, transaction decode errors and out-of-range indices.
Nonempty witness input reports `unsupported(witness)`, rather than a Script rejection.
The witness exclusion deliberately narrows Core's API: without the witness flag, Core ignores the witness argument [C5, lines 1517–1527].
Neither unsupported results nor adapter failures count as evidence that a spend fails Core's rules.
For supported requests, `accepted` corresponds to Core's `true` with `SCRIPT_ERR_OK`, and `rejected` corresponds to `false` with its error.
Intermediate execution APIs expose stacks and cursor state for proofs, but post-failure stacks need not become part of the spend contract.

The operation checks unsupported flags before execution, without discarding any bits.
Stages publish their supported flag masks and opcode capabilities.
During execution, missing required semantics report `unsupported` before the evaluator invents any stack effect or signature result.
Core-defined failures, such as a disabled opcode, remain `rejected` when the implementation supports that failure rule.
Known skipped-opcode behavior can proceed without implementation of the opcode's active stack effect.
An opcode outside a stage's capabilities must never become `BAD_OPCODE` merely because the stage lacks its semantics.

### Flags and protocol context

The first milestone supports exactly the seven flags below, individually and in combination, including the empty set.
The table omits the common `SCRIPT_VERIFY_` prefix from flag names:

| Flag | Bit | Meaning | Dogecoin context at the pin |
| --- | --- | --- | --- |
| `P2SH` | 0 | Evaluate the redeem script for the exact Pay to Script Hash (P2SH) template. | Consensus from inception [C6]. Also standard policy [C7]. |
| `STRICTENC` | 1 | Check signature DER, defined hash type and compressed or uncompressed public-key shape. | Policy only [C1, C2, C7]. |
| `DERSIG` | 2 | Require strict DER for nonempty signatures that undergo an encoding check. | Consensus from `BIP66Height`, 1,034,383 on mainnet [C6, C17]. Also standard policy [C7]. |
| `LOW_S` | 3 | Require DER and low S for nonempty signatures that undergo an encoding check. | Policy only [C2, C6, C7]. |
| `NULLDUMMY` | 4 | Require the extra multisig dummy item to have zero bytes. | Policy only at this pin [C6, C7]. |
| `CHECKLOCKTIMEVERIFY` | 9 | Enforce the CLTV operand against transaction locktime and the selected input's sequence. | Consensus from `BIP65Height`, 3,464,751 on mainnet [C6, C17]. Also standard policy [C7]. |
| `CHECKSEQUENCEVERIFY` | 10 | Enforce the CSV operand against transaction version and the selected input's sequence. | Conditional consensus if `DEPLOYMENT_CSV` is active [C6]. Mainnet activation is unverified here. Also standard policy [C7]. |

Core adds `NULLDUMMY` to block flags only inside the `IsWitnessEnabled` branch, which this pin never enters [C6].
The `MANDATORY_SCRIPT_VERIFY_FLAGS` policy constant contains only P2SH [C7].
That constant does not replace the height and deployment checks in `ConnectBlock`.
The API accepts explicit flags, so it can express historical and policy contexts without claiming to derive either.
A caller that claims consensus validity must justify its flags for the network and activation state.

Mainnet CSV uses bit 0, start time 1,462,060,800 (2016-05-01) and timeout 1,493,596,800 (2017-05-01) [C17].
That deployment window is closed.
The adjacent source comment warns that BIP heights and hashes need Dogecoin values [C17, line 103].
The source inspection does not establish whether CSV locked in before the window closed.
This record asserts neither activation nor failure.

Evidence from a synchronized mainnet node at the pin could settle this question.
The evidence should record `getblockchaininfo.bip9_softforks.csv.status`, its `since` height, and the node's tip hash and height [C18].
A historical claim also needs the relevant activation transition or a reproducible versionbits calculation from chain headers.
No such chain query or calculation forms part of this record.
Consequently, a CSV branch may enforce only relay policy in a context where CSV never activated.
CLTV has an explicit mainnet consensus height independently of CSV [C6, C17].

When their flags are absent, CLTV and CSV act as NOP2 and NOP3 [C3, lines 350–427].
All other flags report `unsupported`, including `MINIMALDATA`, `SIGPUSHONLY`, `CLEANSTACK`, `NULLFAIL` and `DISCOURAGE_UPGRADABLE_NOPS`.
Witness flags and witness-only flags also report `unsupported`.
Thus the milestone does not implement the complete standard-policy flag set [C7].
In particular, it must not enable minimal pushes, clean stacks or null-failure rules implicitly.

## 4. Implementation stages and exit conditions

The stages follow the library's separation of specification, properties and adapters.
The Script execution layer sits above Transaction and depends on it for legacy hashing.
Transaction must not import that layer and create an import cycle.
The implementation adds separate proof and export modules and updates ARCHITECTURE.md with that placement.
An implementation lane must review any relocation of the existing instruction reader separately and preserve its public contract.

### Stage 1: instruction decoding and execution state

The reader returns an opcode, exact instruction bytes, pushed bytes, next cursor and explicit truncated-push failure.
It follows `GetOp2`, including the cursor on failure [C9].
It reuses or proves agreement with `Transaction.readOp`, which already serves the signature serializer.
It must not normalize push encodings or parse a pushed byte as an opcode.

The execution state contains the main stack, altstack, program cursor, last executed separator cursor, `vfExec` conditional stack and opcode count.
The stacks contain raw byte strings, not decoded integers.
Each `EvalScript` call resets its altstack, conditionals, count and separator cursor [C3].
Only the main stack passes between calls in `VerifyScript` [C5].

The stage exits with instruction-consumption and cursor theorems, explicit state invariants and known answers for direct pushes and PUSHDATA1/2/4.
Cases include every truncated length field and payload, nonminimal pushes, and separator bytes inside pushed data.
This stage exposes decoding and state only.
It reports unsupported execution rather than a spend verdict.

### Stage 2: ordinary execution, numbers, hashes and errors

The evaluator follows Core's ordering of decode, push-size check, opcode count, disabled-opcode check and branch execution [C3, lines 275–315].
Even a skipped branch must parse, respect push-size limits, count applicable opcodes and reject disabled opcodes.
A truncated push yields `SCRIPT_ERR_BAD_OPCODE` [C3, lines 280–281].
`OP_VERIF` (0x65) and `OP_VERNOTIF` (0x66) also yield `BAD_OPCODE` inside skipped branches.
Core dispatches their opcode range even when `fExec` is false, then reaches the default error [C3, lines 311 and 1028–1029].

The evaluator implements control flow, stack operations, equality, numeric operations, ordinary NOPs and Core-defined opcode failures.
Signature operations and active timelock checks remain unsupported until their stages.

`CScriptNum` uses little-endian sign magnitude, including negative zero, with four-byte operands for ordinary numeric operations [C8].
Arithmetic may produce a five-byte result that a later numeric operation rejects.
The specification uses mathematical integers with explicit operand bounds, rather than accidental machine wrapping.
It preserves `getint` saturation where Core uses it.
`CastToBool` treats zero and negative zero as false without a numeric-size restriction [C2].
Numeric decode exceptions map to `SCRIPT_ERR_UNKNOWN_ERROR`, as Core's catch clause does [C3, lines 1037–1040].

The hash opcodes are part of execution, not signature-verifier behavior [C3, lines 847–867].
DogeLib has SHA-256 and double SHA-256, but lacks SHA-1, RIPEMD-160 and HASH160 definitions.
Separate prerequisite lanes add pure SHA-1 and RIPEMD-160 primitives, each with independent vectors, review and precise functional-proof claims.
HASH160 then composes RIPEMD-160 with SHA-256.
`OP_HASH256` uses the existing double SHA-256 definition.

Until these prerequisites land, affected opcodes report `unsupported(hashPrimitive)`.
P2SH completion depends on HASH160, so stage 4 cannot bypass this prerequisite with a trusted hash callback.
Primitive proofs and independently sourced known answers belong to their implementation lanes.

The evaluator preserves these per-script limits [C3, C8]:

| Limit | Value and scope |
| --- | --- |
| `MAX_SCRIPT_SIZE` | At most 10,000 script bytes in each `EvalScript` call. |
| `MAX_SCRIPT_ELEMENT_SIZE` | At most 520 bytes in a parsed push, including in a skipped branch. |
| `MAX_OPS_PER_SCRIPT` | At most 201 counted operations per call. Opcodes above `OP_16` count, including skipped operations. Active multisig also adds its key count. |
| Combined stack size | At most 1,000 items across the main stack and altstack after each instruction. |
| `MAX_PUBKEYS_PER_MULTISIG` | At most 20 keys in an active multisig operation. Stage 3 completes this check. |

These limits do not replace block sigop accounting or transaction and block size limits.
A redeem script passes through a stack push, so P2SH also subjects its bytes to the 520-byte element limit.
The specification must terminate without a caller-supplied fuel bound that changes a protocol result.
Operational limits in an adapter must report a separate resource failure.

The stage exits with transition and execution properties, exact supported errors, limit-boundary tests and ordinary-opcode comparisons against Core.
It includes short pushes, unbalanced conditionals, disabled versus reserved opcodes, stack underflow, negative zero and oversized numeric operands.
Until all ordinary operations land, the capability list remains explicit and missing semantics remain unsupported.

### Stage 3: signatures and effective script code

`CHECKSIG`, `CHECKSIGVERIFY`, `CHECKMULTISIG` and `CHECKMULTISIGVERIFY` use the explicit verifier parameter.
The specification checks encoding rules before signature verification, in Core's order [C2, C3].
Script-code deletion precedes those encoding checks [C3, lines 895–898].

An empty signature passes the encoding filter but fails `CheckSig` [C2, C4].
`CheckSig` first constructs `CPubKey` and rejects an invalid key, before the empty-signature check or any digest computation [C4, lines 1253–1266].
Only after the key check does it copy the signature, reject an empty signature and remove the final hash-type byte [C4, lines 1260–1264].
It zero-extends that byte to the existing `UInt32` hash-type input.
It hashes through the existing production `legacySignatureHash` and passes the remaining signature bytes, public-key bytes and digest to the verifier.
An unavailable verifier reports unsupported, never ordinary signature failure.

The effective script code starts after the last executed `OP_CODESEPARATOR` and extends to the script's end [C3, lines 873–899].
For CHECKSIG, `FindAndDelete` removes the serialized push of the entire signature, including its hash-type byte.
`CScript(vchSig)` constructs that push encoding, rather than the raw signature bytes [C9].
For multisig, removal visits every supplied signature in Core's stack order before the matching loop [C3, lines 952–981].
Deletion occurs only at instruction boundaries, and preserves a malformed tail as `FindAndDelete` does [C9].
The signature serializer then removes remaining separator instructions through its existing production behavior.

Multisig preserves Core's ordered, greedy key/signature matching, early termination, encoding-check order and extra dummy pop [C3, lines 920–1022].
The operation consumes the dummy even without `NULLDUMMY`.
With `NULLDUMMY`, a nonempty dummy yields `SCRIPT_ERR_SIG_NULLDUMMY`.
The dummy is an extra stack item, not one of the requested signatures.
Repeated keys do not prove that different people signed.

The stage exits with checker-composition theorems, ordered-matching properties, dummy tests and comparisons of exact effective script code and signature-check requests.
A separate obligation establishes the parsed-script hypothesis for any use of the transformation-reference theorem.
Reaching a signature opcode alone does not establish that the remaining script tail parses.
The production hashing contract must retain Core's malformed-tail behavior even where the transformation-reference theorem does not apply.
Signature operations can complete without that theorem if the record states the remaining proof boundary.

### Stage 4: P2SH and timelock context

`VerifyScript` evaluates `scriptSig`, saves its stack when P2SH applies, then evaluates `scriptPubKey` [C5].
The result needs a nonempty stack with a true top item.
For the exact 23-byte P2SH template, the operation requires a push-only `scriptSig`, restores the saved stack and removes its redeem-script item.
It evaluates those exact redeem-script bytes and again requires a true top item.
`IsPushOnly` follows Core's opcode test, including its treatment of `OP_RESERVED`, rather than an invented canonical-push test [C10].
It does not impose a one-item final stack without `CLEANSTACK`, which remains unsupported.

CLTV accepts a nonnegative operand of at most five bytes.
The operand and transaction locktime must select the same side of the 500,000,000 threshold.
The operand must not exceed transaction locktime, and the selected input's sequence must differ from `SEQUENCE_FINAL` [C3, C4, C8].
These checks do not compare transaction locktime with a block height or time.

CSV also accepts a nonnegative operand of at most five bytes.
An operand with its disable bit set acts as a NOP after numeric decoding [C3, lines 392–427].
Otherwise, the transaction version, interpreted as `uint32_t`, must be at least two.
The input's sequence disable bit must be clear.
The masked operand and sequence must have matching type bits, and the masked operand must not exceed the masked sequence [C4].
These checks do not establish the input's age against chain history.

The stage exits with composition properties for P2SH, CLTV and CSV, plus known answers for flag-off behavior and every stated boundary.
After stage 4, all seven selected flags and all legacy opcode behaviors must have defined results.
Any remaining capability gap stays visible as unsupported and prevents a claim of milestone completion.

### Stage 5: oracle and Core comparison

Proposed operation names are `script.read_op`, `script.eval` and `script.verify_legacy`.
The first exposes instruction and cursor results, the second exposes supported execution state, and the third checks one transaction input.
Requests carry exact script bytes and explicit flags.
Execution and spend requests also identify the verifier backend.
The comparison backend uses pinned Core's signature-verification behavior as a trusted runtime boundary.
A deterministic test backend supports evaluator tests but must not label its results as consensus validity.

Responses distinguish acceptance, Script rejection, unsupported capabilities and adapter errors.
The comparison requires exact errors where this contract promises them.
Diagnostic signature requests can expose effective script bytes, hash types and digests without changing the spend predicate.
The harness must compare Core and Lean under identical scripts, transaction context, flags and verifier behavior.
No comparison may replace excluded flags with a convenient subset.

These operations require a later oracle format revision.
The implementer proposes concrete schemas and the format increment in the relevant PR, under this scope.
The format change still requires maintainer merge authorization.
This record does not reserve a number or alter the currently supported oracle format.
The [oracle documentation](../oracle.md) remains the authority for the implemented format.

The stage exits with fixture checks, comparator self-tests and reproducible differential runs that record both revisions, selected cases and random seeds.
Any mismatch becomes a minimized regression case before an agreement claim.

## 5. Trust and theorem boundaries

The verifier parameter represents Core-compatible verification of raw public-key bytes, signature bytes without the hash-type byte, and a 32-byte digest.
Its intended behavior includes key parsing, lax DER acceptance and S normalization where strict flags do not reject the input first [C12].
A strict-DER-only ECDSA callback cannot substitute for that behavior in historical contexts.

`LOW_S` models `CheckLowS` and its parser behavior, not only a mathematical bound on the original S [C12].
If lax parsing detects an overflowing R or S, it replaces both scalars with zero and returns parsing success [C12, lines 132–166].
`CheckLowS` then accepts that zero signature, although ECDSA verification fails.
The LOW_S encoding filter can therefore accept this overflow case when the prior DER check also passes.
The predicate must preserve this case and must not depend on a verifier that normalizes S and loses the original value.

Execution theorems quantify over the verifier.
A compatibility theorem assumes that this parameter agrees with the pinned verifier on the relevant input domain.
That assumption is a named hypothesis, not a new axiom or a completed secp256k1 proof.
A runtime adapter may call libsecp256k1, but that call needs an explicit foreign-boundary disclosure in its implementation change.
Tests of the adapter do not prove the library, its parser or its binary correct.

The theorem targets establish Script behavior relative to that parameter.
They do not establish unforgeability, private-key ownership, signer independence, hash collision resistance, bridge custody or network liveness.
P2SH composition uses the exact supplied redeem script and its digest.
A claim that no different redeem script can satisfy the hash commitment needs a separate cryptographic model.
The existing kernel, compiler, runtime and source-review gaps remain as [SOUNDNESS.md](../../SOUNDNESS.md) states them.

## 6. Evidence plan

The fixture importer preserves Core's original flags, expected outcome, source index, exact bytes and construction context.
It records the source commit, file digest and importer revision.
A manifest lists supported cases and excluded cases with reasons, so skipped cases cannot inflate a comparison count.
Unsupported cases never count as successful rejection comparisons.

The proposed progression uses these corpora:

| Stage | Known answers and comparison evidence |
| --- | --- |
| 1 | Push and truncation cases from `script_tests.json` [C15], plus byte cases justified by `GetOp2` [C9]. |
| 2 | Supported control, stack, number and hash cases from C15, with each case's original flags. Add independent primitive vectors and limit boundaries. |
| 3 | Supported CHECKSIG and CHECKMULTISIG cases from C15, including encoding, hash-type, separator and dummy cases. Compare effective code and checker inputs. |
| 4 | Supported P2SH, CLTV and CSV cases from C15 and eligible transaction inputs from C16. Add explicit transaction contexts for timelock boundaries. |
| 5 | All supported corpus cases and seeded mutations through the oracle and pinned Core harness. Report unsupported and excluded totals separately. |

Core's script runner constructs a crediting transaction and a spending transaction, rather than checking two isolated strings [C13].
Those bytes affect signatures, so the importer must reproduce them exactly.
The runner also adds P2SH and WITNESS for CLEANSTACK cases [C13, lines 159–163].
Such cases remain excluded rather than silently dropping CLEANSTACK or those added flags.
Nonempty witness cases remain excluded.
The script fixture supplies an exact `ScriptError` expectation, which eligible cases can retain [C13].

The transaction runner first calls `CheckTransaction`, then checks input scripts with supplied previous outputs [C14].
Thus membership in `tx_invalid.json` does not imply that every input, or any input, fails Script verification.
The importer must identify rejection provenance before deriving a per-input known answer.
Where the corpus gives no exact per-input error, pinned Core output is comparison evidence with recorded provenance.
It must not become an independent expected value merely because the importer generated it.
Serialization-only tests of these corpora remain separate from spend-validation evidence.

## 7. Worked property target: multisig with recovery

Consider this redeem-script template, with public-key byte strings `P1`, `P2`, `P3` and recovery key `R`:

```text
OP_IF
  OP_2 <P1> <P2> <P3> OP_3 OP_CHECKMULTISIG
OP_ELSE
  <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <R> OP_CHECKSIG
OP_ENDIF
```

Angle brackets denote exact push encodings chosen when the script instance is constructed.
The positive locktime operand 1,000,000 has this script encoding:

```text
03 40 42 0f
```

The first byte pushes three bytes, which encode the positive sign-magnitude integer `0x0f4240` [C8, C9].
For this example, each public key has 33 bytes and the redeem script must satisfy the P2SH element limit.
The script family supplies a property target.
A production bridge instance needs separate fixtures and custody review.

The locktime 1,000,000 is illustrative, not a deployment height or an activation claim.
Let the previous output contain the exact P2SH commitment to these redeem-script bytes.
Assume P2SH and CLTV flags, an in-range input and supported semantics.
Quantify over every push-only `scriptSig` that supplies this exact redeem-script instance, without a canonical encoding or a fixed unlocking shape.
A different redeem script with the same digest requires a separate hash-commitment argument.
The target does not infer byte equality from digest equality.

The theorem target is an equivalence, including its converse.
If `scriptSig` evaluation fails, the spend rejects.
Otherwise, let its resulting stack be `S ++ [redeem]`, with the top item on the right.
Acceptance holds exactly when one of these cases applies under the concrete resource bounds and reached encoding predicates below:

- Ordinary branch: `S` has suffix `[dummy, sig1, sig2, selector]`, `CastToBool(selector)` is true, and ordered multisig matching succeeds.
- Recovery branch: `S` has suffix `[sigR, selector]`, `CastToBool(selector)` is false, the CLTV conditions hold, and CHECKSIG succeeds against `R`.

The resource hypotheses must state these bounds explicitly:

- Each script has at most 10,000 bytes, and the redeem script has at most 520 bytes.
- Every parsed push has at most 520 payload bytes, including pushes in skipped branches.
- Each decoded instruction prefix leaves at most 1,000 items across the main stack and altstack.
- Each call counts at most 201 operations, including skipped opcodes above `OP_16` and the active multisig key count.
- The fixed ordinary branch uses three keys and two signatures. The general target requires `1 <= k <= n <= 20`.
- Transaction input and output counts are below 2^32, and the input index selects an input.

The encoding predicates concern only the signature/key pairs that Core reaches, in Core's matching order [C2, C3].
Nonempty reached signatures require DER when DERSIG, LOW_S or STRICTENC applies.
LOW_S additionally requires the exact `CheckLowS` predicate, including its overflow behavior.
STRICTENC additionally requires defined hash types and the permitted public-key shapes.
NULLDUMMY requires an empty consumed dummy.
The formal statement must enumerate these predicates and bounds, never replace them with a bare hypothesis that execution succeeds.

Both cases allow an arbitrary stack prefix and nonminimal push encodings.
Without `NULLDUMMY`, the dummy can contain any bytes that satisfy the element limit.
With `NULLDUMMY`, the dummy must be empty.
Consensus at this pin enforces neither NULLDUMMY nor MINIMALIF, so consensus alone requires neither an empty dummy nor a canonical selector [C1, C6].
Every selector byte string has its `CastToBool` meaning, including negative zero as false [C2].
The selected flags do not impose a clean final stack.

Each signature carries its own hash-type byte, and each checker call uses the corresponding effective script code and digest.
The ordinary-branch case means Core's ordered matching accepts two supplied signatures against three key positions.
The general target uses `1 <= k <= n <= 20`, with explicit numeric pushes and the same resource hypotheses.
For P2SH instances, the 520-byte element bound further restricts the key count.
A claim about `k` distinct signers additionally needs distinct keys and a security model.
Duplicate keys alone do not establish distinct authorization.

The recovery-branch case requires transaction locktime of at least 1,000,000, below the timestamp threshold, and a nonfinal selected sequence.
It also requires a successful signature check against `R`, subject to the selected encoding flags.
The converse states that these conditions, the stated stack suffix and the execution bounds suffice for acceptance.
In particular, a transaction with locktime below 1,000,000 cannot pass this recovery branch when CLTV applies.
Without the CLTV flag, that exclusion does not hold.
A claim that recovery cannot enter a chain before a height or time also needs transaction-finality and chain-context results outside this milestone.

The execution target permits every one-byte hash type that the selected flags admit.
That includes NONE, SINGLE, SINGLE's fixed `one` digest, and ANYONECANPAY combinations.
These modes do not guarantee the transaction commitments that a custody argument might require.
A later bridge property may restrict hash types to `SIGHASH_ALL` without `ANYONECANPAY`.
Such a restriction belongs to that property's hypotheses, not an invented rule in CHECKSIG or CHECKMULTISIG.

The proof needs generic results for branch selection, stack composition, Script numbers, CLTV, CHECKSIG and ordered multisig matching.
It also needs exact script construction, P2SH composition and signature-hash preparation results.
Any use of the transformation-reference equality must discharge its parsed-script and transaction-count hypotheses for the actual effective script code.
No target assumes unforgeability merely to explain stack execution.

## 8. Decisions

**Date:** 2026-11-04. **Decision maker:** Maintainer.
The maintainer adopted this scope:

| Topic | Decision |
| --- | --- |
| Flag scope | All seven flags, including CHECKSEQUENCEVERIFY, supplied explicitly by the caller. |
| CSV activation | CSV semantics are in scope. No historical mainnet activation claim without the separate chain evidence in section 3. |
| Errors | Preserve Core's exact `ScriptError` categories and their order at the pin. Keep unsupported capabilities distinct. |
| Module placement | Script sits above Transaction, with separate proof and export modules. Preserve the dependency direction without an import cycle. |
| Signature verifier | Use a raw-byte verifier parameter and a trusted backend for comparison. Name the agreement assumption explicitly. |
| Hash primitives | SHA-1 and RIPEMD-160 each need a separate prerequisite lane, independent review, independent vectors and precise functional-proof claims. |
| Hash types | The generic interpreter supports every one-byte hash type that the selected flags admit. A later bridge property may require `SIGHASH_ALL` without `ANYONECANPAY`. |
| Worked property | Use the generic multisig and recovery template. A production bridge script is a separate application of these semantics. |
| Rust work | Implementation refinement and Rust extraction remain outside this milestone. |
| Oracle details | The implementer proposes concrete schemas and the format increment in the relevant PR, under this scope. The format change still requires maintainer merge authorization. |

## 9. Remaining risks and boundaries

The main compatibility risks are error order, skipped-branch rules, lax signature parsing and script-code mutation.
P2SH policy must not replace consensus flag selection, and a CSV checker must not stand in for chain-relative sequence locks.
Complete standard-policy coverage and witness execution need separate scope decisions.
There is no pin change, trust-policy exception, public API implementation or fixture-format change in this record.
Scope adoption does not establish any target theorem or authorize a later implementation merge.
