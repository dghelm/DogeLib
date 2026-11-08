# A property-driven bug-finding campaign

**Status:** Proposed.
Section 14 lists the proposals that wait for a maintainer decision.
Implementation status belongs in ROADMAP.md and COVERAGE.md.

**Date:** 2026-11-08
**Companions:** [Coverage](../../COVERAGE.md), [soundness](../../SOUNDNESS.md), [oracle contract](../oracle.md), [DogeLib in practice](../in-practice.md), [design record 0003](0003-legacy-spend-validation.md), [design record 0005](0005-signature-verifier.md), [design record 0007](0007-proposed-revisions.md) and [design record 0008](0008-header-sequence-validation.md).

## 1. Purpose and boundary

This record proposes a campaign that searches for counterexamples to stated properties of one signed-spend family.
Each counterexample that the campaign finds becomes a small input that a person can replay, reduce and check against Core's production code.

[DogeLib in practice](../in-practice.md#two-questions) separates two questions.
The first asks whether an implementation behaves as the specification says.
The second asks whether the specified behaviour gives a stated property.
The existing comparison answers the first question on a fixed stream of requests ([docs/oracle.md](../oracle.md#the-comparison)).
The campaign adds generated cases, properties that the campaign states independently of both implementations, and the tools that make a failure useful:

- Structured generation of signed spends in two mutation modes (section 6).
- Saved failures, a replay command and a reducer (section 7).
- A planted fault that the campaign must find by search, as its own self-test (section 8).
- A replay through Core's production path before any candidate counts as a finding (section 9).
- A fixture for each understood counterexample and, where practical, a theorem (section 10).

The guide already lists the causes of a disagreement and the limits of the H2 transcriptions ([in-practice.md](../in-practice.md#comparing-with-core-and-reading-a-disagreement)).
This record uses that list and does not repeat it.
The properties of section 11 are targets for the campaign, not implemented results.

DogeLib is a specification library for Dogecoin Core.
A property of an application or of DogeOS belongs in a downstream project, and this record proposes none.

The record excludes these subjects:

- **Transaction validation and the UTXO set.** The class of CVE-2018-17144 needs properties such as "no block spends one outpoint twice". Per-input Script verification cannot state them. They need a model of `CheckTransaction`, the UTXO set and value accounting, which is a later and larger record ([in-practice.md](../in-practice.md#further-directions)).
- **Resource bounds.** A bound on the work of validation, such as bytes hashed, is a fourth kind of claim beside compatibility, strictness and use. It belongs in a later extension of the proposal records of design record 0007.
- **Native fuzzing.** libFuzzer with a structure-aware mutator, and builds with sanitizers, find memory errors and reach more inputs per second. Section 12 keeps them as an option for the time when throughput limits the campaign.
- **Plausible and any other Lake dependency.** The root package has no Lake dependencies ([AGENTS.md](../../AGENTS.md#checks)), so a dependency needs a package proposal. Plausible's tactic also closes a goal when it finds no counterexample. Section 12 gives the reason why such a tactic can never back a theorem.
- **Header operations as campaign targets.** Section 9.3 says what a replay of `block.contextual_check` and `block.header_sequence` needs, but the campaign of this record generates only Script requests.
- **Implementation refinement and Rust extraction.**

## 2. Reference software revision

Every Core citation below refers to commit `e0a1c157791544e818c901bd9341896965afbf9d`, the compatibility pin in [SOURCES.md](../../SOURCES.md).
The line ranges identify the inspected source:

| Reference | Pinned source and inspected lines | Subject |
| --- | --- | --- |
| C1 | [script/interpreter.cpp, lines 1054–1143](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1054-L1143) | `CTransactionSignatureSerializer`: the fields that each hash type writes to the preimage. |
| C2 | [script/interpreter.cpp, lines 1225–1246](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1225-L1246) | The `SIGVERSION_BASE` part of `SignatureHash`, with the two returns of the value one. |
| C3 | [script/interpreter.cpp, lines 1253–1272](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1253-L1272) | `TransactionSignatureChecker::CheckSig`: the hash type is the last byte of the signature. |
| C4 | [script/interpreter.cpp, lines 1274–1308](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1274-L1308) | `TransactionSignatureChecker::CheckLockTime`. |
| C5 | [script/interpreter.cpp, lines 350–390](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L350-L390) | `OP_CHECKLOCKTIMEVERIFY` in `EvalScript`. |
| C6 | [script/interpreter.cpp, lines 186–212](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L186-L212) | `IsDefinedHashtypeSignature` and `CheckSignatureEncoding`. |
| C7 | [script/interpreter.cpp, lines 1409–1530](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/script/interpreter.cpp#L1409-L1530) | `VerifyScript`, with its flag assertions at lines 1508, 1509 and 1519. |
| C8 | [validation.cpp, lines 1398–1401](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1398-L1401) and [line 1462](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L1462) | `CScriptCheck::operator()`, which calls `VerifyScript` with `CachingTransactionSignatureChecker`, and `CheckInputs`. |
| C9 | [validation.cpp, lines 3066, 3205 and 3270](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.cpp#L3066-L3270), [validation.h, lines 258 and 502](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/validation.h#L258-L502) | `ContextualCheckBlockHeader` and `ProcessNewBlockHeaders`, both declared in the header, and the `static` `AcceptBlockHeader`. |
| C10 | [test/test_bitcoin.h, lines 20–39](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/test_bitcoin.h#L20-L39), [test/test_bitcoin.cpp, lines 61–76](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/test/test_bitcoin.cpp#L61-L76) | `BasicTestingSetup` and `TestingSetup`: a scratch data directory, coins view and block index. |
| C11 | [rpc/rawtransaction.cpp, line 940](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/rpc/rawtransaction.cpp#L940), [rpc/mining.cpp, line 1356](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/src/rpc/mining.cpp#L1356), [qa/rpc-tests/test_framework/mininode.py, line 1331](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/qa/rpc-tests/test_framework/mininode.py#L1331) | `sendrawtransaction`, `submitblock` and the `headers` message of the functional test framework. The pin has no `submitheader` command. |
| C12 | [SECURITY.md, lines 1–9](https://github.com/dogecoin/dogecoin/blob/e0a1c157791544e818c901bd9341896965afbf9d/SECURITY.md#L1-L9) | Core's policy for the report of a vulnerability. |

The registry already records `interpreter.cpp` (D3) and `validation.cpp` (D33).
An implementation lane adds an identifier for each other file that it cites, without a change to any pin.
The findings come from source inspection, without a campaign run.

Section 9.2 needs a check against current upstream Core.
In a local clone of Core, last fetched on 2026-09-09, `upstream/1.14-maint` is the pin itself.
`git diff e0a1c15 upstream/master -- src/script/interpreter.cpp` shows whitespace changes only, at lines 105, 145 and 871 of the pinned file.
The same diff changes 31 lines of `src/validation.cpp`, which this record did not inspect.
A campaign lane repeats the check with a fresh fetch, because a later release can change both files.

## 3. Inventory of what exists

### 3.1 The signed-spend family

The family is the multisig-with-recovery template of design record 0003, section 7.
`DogeLib.Script.multisigRecoveryScript` defines it for `k` of `n` keys ([SOUNDNESS.md](../../SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
The fixtures and the signer use its 2-of-3 instance: `OP_IF OP_2 <K1> <K2> <K3> OP_3 OP_CHECKMULTISIG OP_ELSE <1000000> OP_CHECKLOCKTIMEVERIFY OP_DROP <K4> OP_CHECKSIG OP_ENDIF`, under P2SH.
The keys are the private scalars 1, 2, 3 and 4, which are public test data ([recovery fixtures](../../tests/script/signed-spends/README.md#provenance)).

These parts exist:

| Part | Location | What it does | Limit for a campaign |
| --- | --- | --- | --- |
| Signer | `harness/core/core_signer.cpp`, `emit` and `generate` | Builds 25 fixed records with Core's `SignatureHash`, `CKey::Sign` and `VerifyScript` | No input: `main` accepts no argument except `--verification-vectors` (line 230). Hash type `SIGHASH_ALL` only (lines 110 and 127). One input and one output (`transaction`, lines 69–78). |
| Fixtures | `tests/script/signed-spends/recovery.jsonl` | 25 records with Core's verdict and error name | Core's verdict is the expected value. Every record has `hash_type` 1 and input index 0. |
| Regeneration check | `scripts/check_signed_spends.py` | Requires the signer output to equal the fixture byte for byte | Checks the signer, not a property. |
| Comparison | `scripts/oracle_pubkey.py`, `signature_spends` | Sends the 25 records through `script.verify_legacy` with `checker: "transaction"` | Fixed records. |
| Lean property | `multisigRecovery_sound` and its converses | Characterize acceptance of the template for `1 ≤ k ≤ n ≤ 16` | Relative to the verifier parameter, under the hypotheses of `MultisigRecoverySpend`. |
| Commitment theorems | `legacySignatureHashPlan_allOnly_commits`, `legacySignatureHashPlan_eq_of_none` and its companions | State which fields the Lean preimage commits to, for each hash type | ANYONECANPAY combined with NONE or SINGLE has no theorem ([SOUNDNESS.md](../../SOUNDNESS.md#legacy-signature-hash-what-all-commits-to)). |

### 3.2 The Script generators

`scripts/oracle_script.py` builds the Script streams of the comparison:

- `legacy_sets` takes 2,000 seeded mutations (seed `20261106`) of corpus records (lines 203–235). Each mutation flips a bit or appends an opcode in a script, or replaces the version, sequence, lock time or flags. `spend_tx` then builds a synthetic one-input transaction around the scripts (lines 195–200). So no mutated request carries a valid signature.
- `locktime_sets` builds targeted CLTV and CSV requests with seed `20261107` (lines 258–285). Each script pushes its operand, runs the opcode, drops the operand and pushes true. The boundaries of these requests, such as 499,999,999, 500,000,000 and a final sequence, are useful seeds for the recovery branch.
- `harness_refused` classifies the flag combinations that Core's `VerifyScript` asserts against (lines 332–347, C7).

### 3.3 The comparator

`scripts/compare_core.py` builds one deterministic stream and runs each program once on the whole stream (`main`, lines 1056–1058).
`compare` decides agreement for each request (lines 754–870).
These properties of the comparator matter for a campaign:

- The seeds are constants in the source, such as `SEED = 20261104` (line 50). No argument selects a seed or a budget.
- `run_program` raises `EXIT` for a nonzero status and `TIMEOUT` for the whole stream (lines 64–78). It discards the output of a failed run. The harness flushes each response (`std::endl`, `core_oracle.cpp` line 1234), so that output would locate the request, but the comparator does not read it.
- The report prints at most `MAX_REPORTS = 10` failures (line 51), and it cuts each request and response to 400 characters (lines 1106–1108). Nothing is saved.
- An unsupported Lean result and a checked harness refusal count as neither agreement nor disagreement (lines 1074–1081 and 1096–1098).

`scripts/test_compare_core.py` checks that the comparison can fail.
A wrapper replaces one side, and each mutation in `MUTATIONS` must fail with its own failure code (lines 30–97).
Most mutations change the first eligible response, so the wrapper tests the comparator, not the reach of the generator.

### 3.4 The planted fault

`DogeLib.Proposals.ExampleFaultyLocktime` redefines `OP_NOP4` as a lock-time check, and its faulty variant pops the operand after a successful check ([in-practice.md](../in-practice.md#vetting-a-proposed-soft-fork-a-planted-fault)).
`faulty_counterexample` proves that the faulty spend predicate accepts `51 52 b3 51 87` with lock time 2, and the baseline rejects it.
The counterexample comes from a person, not from a search.
The oracle has no operation for a proposal (design record 0007, decision 8), so the faulty rule runs only in Lean and in `lake test`.

### 3.5 Planted harness faults

The independent review of pull request #129 planted eight faults in the harness by hand, and the comparison caught seven of them ([review comment](https://github.com/dghelm/DogeLib/pull/129#issuecomment-6717383148)).
The fault that survived matched only the last member of the failed list.
That review showed that a planted fault measures what a comparison can detect, but the repository keeps no list of such faults.

## 4. Behaviour to preserve

Each item comes from the pinned source.
The generator, the properties and the reducer must keep each behaviour.

1. **Committed fields.** Under every hash type, C1 writes the version and the lock time. For input `n`, it writes the outpoint and the sequence. The script code takes the place of the `scriptSig` of input `n`. Every other input gets an empty script. Section 6.3 gives the full table.
2. **The fixed digest.** `SignatureHash` returns the value one in two cases (C2, lines 1225–1237). In the first, `n` is not an input index. In the second, the hash type is SINGLE and `n` is at least the number of outputs. That digest commits to no field.
3. **The hash type of a spend.** `CheckSig` takes the last byte of the signature as `nHashType`, a value from 0 to 255 (C3, line 1263). The preimage ends with that value as four bytes (C2, line 1244). So a change of the last byte changes the preimage. This holds even for two values of one class, such as `0x01` and `0x21`.
4. **Defined hash types.** With `STRICTENC`, the hash type without the ANYONECANPAY bit must be 1, 2 or 3. Otherwise the signature fails with `SIG_HASHTYPE` (C6, lines 186–195 and 208–209). Without `STRICTENC`, this check accepts every byte. C1 then reads each byte by its low five bits and its ANYONECANPAY bit.
5. **The lock-time check.** `CheckLockTime` (C4) succeeds only when three conditions hold. The operand and `nLockTime` lie on the same side of 500,000,000. The operand is at most `nLockTime`. The sequence of input `n` is not `0xffffffff`. Without the flag `CHECKLOCKTIMEVERIFY`, the opcode is `OP_NOP2` (C5, lines 352–358).
6. **Fields that execution reads.** Apart from the signature hash, the template reads two transaction fields: `nLockTime` and the sequence of input `n`, through C4. Every hash type commits to both (item 1). Execution also reads the `scriptSig` of input `n`, which no digest commits to (C1). Its pushes form the unlocking stack: the dummy, the signatures with their encodings, the selector and the redeem script. A change of that `scriptSig` can change the branch or the verdict with both digests unchanged. For example, the fixture `multisig-selector` keeps `digest_hex` equal to `spend_digest_hex` and gets `EVAL_FALSE`. No other open field of section 6.3 changes the execution of the template.
7. **Flag assertions.** `VerifyScript` asserts that `WITNESS` implies `P2SH` and that `CLEANSTACK` implies both (C7). The harness refuses those combinations, and the comparator classifies them (section 3.3).
8. **The production caller.** A node calls `VerifyScript` through `CScriptCheck` with `CachingTransactionSignatureChecker` (C8). The harness calls it with `TransactionSignatureChecker` ([docs/oracle.md](../oracle.md#what-the-harness-runs)). The two differ in the signature cache, and in the precomputed hashes, which only `SIGVERSION_WITNESS_V0` reads (C2, line 1180).

## 5. Options

### 5.1 The signer

A campaign in the mode that preserves execution must sign each generated transaction.
Three signers are possible:

- **S1: the Core signer with a request mode.** `core-signer --sign` reads one JSON request per line: the unsigned transaction, the input index, the script code, the hash-type byte and the key identifiers. It answers with Core's digest and the signatures, each with its hash-type byte. It uses the same `SignatureHash` and `CKey::Sign` with `test_case=0` as `emit` (lines 110 and 126). So the signatures are deterministic RFC 6979 signatures ([recovery fixtures](../../tests/script/signed-spends/README.md#provenance)).
- **S2: an independent Python signer.** A Python implementation of secp256k1, RFC 6979 and the legacy preimage, with `hashlib` for the hashes. It is a third implementation of the signature hash, so it can expose a mistake that Lean and Core share. It is also several hundred lines of cryptographic code that review must check, and it adds no evidence about Core.
- **S3: a Lean signer.** Rejected. DogeLib code never signs a digest (`core_signer.cpp`, line 3), and a signer under test would sign with the digest that it also checks.

**Recommendation: S1, with a digest check.**
Before the driver uses a signature, it sends `sighash.legacy` for the same transaction, script code, input index and hash type to both programs.
Both digests must equal the signer's digest, or the driver saves a `digest` failure and does not run the spend.
With S1, a mistake in Core's `SignatureHash` gives signatures that Core accepts, and the Lean side then disagrees.
A mistake that Lean and Core share stays hidden from the comparison, but the commitment properties Q4 and Q5 can expose it (section 11).
S2 stays available, as decision 3 says.

### 5.2 The driver

- **C1: options in `compare_core.py`.** Add `--campaign`, `--seed`, `--budget` and `--save` to the existing comparator.
- **C2: a separate driver.** `scripts/campaign.py` imports `compare`, `run_stream` and the request validators from `compare_core.py` and `oracle_script.py`. The CI stream of `compare_core.py` does not change.

**Recommendation: C2.**
The CI comparison keeps its fixed stream and its published counts.
The driver uses the same agreement function, so a campaign agreement means what a CI agreement means.

### 5.3 Where the planted fault runs

The search for the planted fault needs the baseline and the faulty rule on the same requests:

- **E1: a test executable.** `proposal-replay` lives under `tests/`, imports `DogeLib.Proposals`, and answers `script.verify_legacy` requests with the revised spend predicate. Command-line arguments name the proposal, the variant and `active`, so each request keeps the shape of `dogelib-oracle/1`. The Python driver and reducer then work on this program as on the oracle.
- **E2: a search inside Lean.** A Lean function in `tests/KnownAnswers/Proposals/` enumerates scripts and prints the first counterexample. It needs its own reducer in Lean.

**Recommendation: E1.**
One reducer serves both the signed-spend family and the proposal.
The executable is not part of `Exports`, and `dogelib-oracle` gets no proposal operation, so decision 8 of design record 0007 holds.
Decision 8 of design record 0007 concerns operations of the oracle, and `proposal-replay` adds none. The maintainer confirmed this reading on 2026-11-08 (section 14).

## 6. Generation

### 6.1 Cases

A *case* is a construction plan, not a byte string.
It has these parts:

- The shape: the number of inputs and outputs, the position `n` of the template input, and the contents of the other inputs and outputs.
- The branch: ordinary with a signer pair, or recovery with key 4.
- The hash-type byte of each signature, and the flags.
- The lock time, the sequence of each input and the selector bytes.
- A list of mutations, and the mode of section 6.2.

The driver builds the requests of a case from the plan, so the reducer can change the plan and rebuild them (section 7.4).
Each mutation names its field and its new value, so a saved failure says what changed.

### 6.2 Two mutation modes

- **Preserve execution.** The driver applies the mutations to the unsigned transaction, then signs the result. The spend reaches the signature checks with valid signatures. So the generator reaches deep paths: other hash types, other input positions, more inputs and outputs, and lock-time boundaries.
- **Test a commitment.** The driver signs the unmutated transaction, then applies the mutations, and keeps the signatures. The mode tests what the signature commits to.

Signature-encoding mutations apply to the signature bytes after the signer returns them.
They replace `S` with `n − S`, change the hash-type byte, reverse the order of the signatures or add padding to the encoding.
These changes are arithmetic and byte operations on Core's signature, so no DogeLib code signs.

### 6.3 Committed and open fields

The table gives the fields that each hash type commits to, for the input `n` that the template spends.
`C` marks a committed field and `O` an open field.
Section 4, item 2, excludes the fixed digest: SINGLE with `n` at least the number of outputs.
A person derived the table from C1 and C2 by hand:

| Field | ALL | ALL with ACP | NONE | NONE with ACP | SINGLE | SINGLE with ACP |
| --- | --- | --- | --- | --- | --- | --- |
| `nVersion`, `nLockTime` | C | C | C | C | C | C |
| Outpoint and sequence of input `n` | C | C | C | C | C | C |
| Script code (the redeem script) | C | C | C | C | C | C |
| Hash-type byte | C | C | C | C | C | C |
| `scriptSig` of any input | O | O | O | O | O | O |
| Outpoint of input `j ≠ n` | C | O | C | O | C | O |
| Sequence of input `j ≠ n` | C | O | O | O | O | O |
| Number of inputs | C | O | C | O | C | O |
| Position `n` of the template input | C | O | C | O | C | C |
| Output `n` | C | C | O | O | C | C |
| Output `i ≠ n` | C | C | O | O | O | O |
| Number of outputs | C | C | O | O | O, while it stays above `n` | O, while it stays above `n` |

"ACP" is the ANYONECANPAY bit `0x80`.
Under SINGLE, C1 writes each output `i < n` as a null output (lines 1117–1123), so the contents of those outputs are open.
Under ANYONECANPAY, C1 writes only input `n` and a count of one (lines 1097–1098 and 1131), so the number of inputs is open.
The position `n` is also open, except under SINGLE, where C1 writes `n + 1` outputs (line 1136).
The driver keeps the table as data with this derivation in its comments.
Neither implementation computes it.

For the Lean definitions, `legacySignatureHashPlan_eq_iff_allFields`, `legacySignatureHashPlan_eq_of_anyoneCanPay`, `legacySignatureHashPlan_eq_of_none` and `legacySignatureHashPlan_eq_of_single` state the same commitments for four columns.
No theorem covers the columns of NONE and SINGLE with ACP.
Review compares the table with those theorem statements, but the theorems are not the source of an expectation.

### 6.4 Seeds and the search

The campaign starts from the 25 records of `recovery.jsonl` and the boundaries of `locktime_sets`.
A seeded generator then draws plans with `random.Random(seed)`.
Some parts are enumerated in full at their boundaries, as `locktime_sets` does:

- Lock times 0, 999,999, 1,000,000, 1,000,001, 499,999,999, 500,000,000 and `0xffffffff`.
- Sequences 0, `0xfffffffe` and `0xffffffff` on input `n` and on the other inputs.
- All six defined hash types with `STRICTENC`, and the bytes `0x00`, `0x04`, `0x21`, `0x84` and `0xff` without it.
- Positions `n` from 0 to 3, with 1 to 4 inputs and 0 to 5 outputs. So SINGLE reaches both sides of the fixed digest, and mutant M5 of section 8.2 has reachable cases.
- Selectors `01`, `02` and `81` for true, and the empty push, `00`, `80` and `0000` for false.
- Each flag of the supported set `1567` set and clear, with `P2SH` set. A few cases set an unsupported flag, so the unsupported class stays visible.

The search has no coverage feedback.
The driver reports the branches, hash types, error names and mutation operators that each run reached. The targeted streams report their opcodes in the same way ([docs/oracle.md](../oracle.md#the-comparison)).

### 6.5 Expected results

Each expected result comes from a property of section 11 and the plan of the case.
The plan says which branch the case intends, which fields changed and in which mode.
The property then gives the expected verdict or the expected relation between two digests.
No expected value comes from DogeLib, from the harness or from the signer's verdict, unlike the `core_valid` field of `recovery.jsonl`.

## 7. Failures, replay and reduction

### 7.1 Seed, budget and batches

`scripts/campaign.py run` takes a campaign name, a seed, a budget of cases and a budget of seconds.
The seed, the budget and the DogeLib revision fix the sequence of plans.
The driver sends the requests in batches of a fixed size, for example 2,000.

If a batch fails with `EXIT`, `TIMEOUT`, `COUNT`, `MALFORMED` or `ID` (section 3.3), the driver bisects it to one request.
The bisection assumes that each response depends only on its request.
The harness reads and answers one line at a time (`core_oracle.cpp`, lines 1229–1242). The oracle writes and flushes each response before it reads the next line ([docs/oracle.md](../oracle.md#running-it)).

### 7.2 Outcome classes

The driver gives each failure one class:

| Class | Condition |
| --- | --- |
| `verdict` | The Script results of the two programs differ, or a result differs from the property's expected verdict. |
| `digest` | The `sighash.legacy` digests differ, or a digest relation that a property requires fails on either side. |
| `crash` | A program exits with a nonzero status or a signal, or its output fails `run_stream`'s checks. |
| `timeout` | A batch, or the bisected request alone, exceeds the time limit. |
| `unsupported` | Lean returns `unsupported` where the property needs a verdict. It is not a disagreement. |
| `refusal` | The harness refuses the request under `harness_refused`, or the signer refuses a signing request. It is not a disagreement. |

The driver counts `unsupported` and `refusal` outcomes and saves a sample of each, so that a loss of coverage stays visible.

A `verdict` or `digest` failure also records the side that fails the property:

| Lean and Core | The property | First reading |
| --- | --- | --- |
| Agree | Both satisfy it | Pass |
| Agree | Both violate it | The property is wrong, or the baseline has the behaviour. Check the list of known behaviours (section 7.5). |
| Differ | Lean violates it | A suspected mistake in the Lean model or the oracle adapter |
| Differ | Core violates it | A candidate for section 9: a mistake in Core, in the harness or in the signer |
| Differ | Both satisfy it | A compatibility disagreement, such as a different error name. Use the list of causes in the guide. |

### 7.3 The saved failure

The driver writes each failure to `build/campaign/<run>/failures/<digest>.json`, where `<digest>` is the SHA-256 of the canonical request text.
`build/` is not committed ([.gitignore](../../.gitignore)).
The proposed format is `dogelib-campaign-failure/1`, one JSON object with these fields:

| Field | Content |
| --- | --- |
| `format` | `dogelib-campaign-failure/1` |
| `campaign`, `seed`, `case_index`, `budget` | The run and the position of the case in it |
| `property` | The identifier of section 11, such as `Q4` |
| `class`, `failing_side` | The class and the side of section 7.2 |
| `plan` | The construction plan of section 6.1, with the mode and the mutations |
| `requests` | Each exact request, with its flags and context, in send order |
| `signer` | Each exact signing request and the signer's complete response, or its exit status and standard error. Empty when the case signs nothing |
| `responses` | Both complete responses to each request, without truncation |
| `expected` | The expected verdict or digest relation, and the property text it comes from |
| `revisions` | The DogeLib commit and a dirty-tree flag, the Core pin, `core.stamp`, both `--version` outputs and the signer's `CORE_SIGNER_BLOB` |
| `build` | The Lean toolchain, the Python version and the machine |
| `replay` | The exact replay command |
| `reduced_from` | The file name of the failure that the reducer started from, or null |

`core.stamp` already records the pin, the compilers, the configure options and the flags of the harness build (`scripts/build_core_harness.sh`, `stamp_text`).

### 7.4 Replay and the reducer

`scripts/campaign.py replay <failure> <oracle> <harness>` sends the stored requests unchanged and reclassifies the responses.
It never signs again, so a replay of a failure on the oracle or the harness needs no signer.
It reports whether the stored class and failing side reproduce.
A failure of the signer itself, such as a refusal or a digest that differs from both programs, has its own path.
`scripts/campaign.py replay --signer <signer> <failure> <oracle> <harness>` sends the stored signing requests to the signer again and compares its responses with the stored ones.
Every replay guarantee of this record covers signer failures only through that path.

`scripts/campaign.py reduce <failure> <oracle> <harness> <signer>` changes the plan, not the bytes.
A candidate plan replaces the current one when it keeps the *failure condition*: the same property, the same class and the same failing side.
The reducer tries these changes in order, and repeats them until no change applies:

1. Remove elements one at a time, then each pair of adjacent elements, then halves, as delta debugging does. An element is a mutation, or an instruction when the plan is a script.
2. Remove other inputs and outputs, and move input `n` towards position 0.
3. Replace numbers with simpler values of the same boundary class. For example, replace a lock time with 1,000,000, or a sequence with 0.
4. Clear flags that the failure does not need, and keep each combination inside the assertion domain of C7.
5. Replace the hash type with ALL, and the selector with `01` or the empty push.
6. Shorten other scripts byte by byte, last.

For a plan that is a script, as in section 8.1, step 3 also simplifies the value of each push, for example to 0.

The reducer respects the signing mode.
In the mode that preserves execution, it signs each candidate again.
In the mode that tests a commitment, it changes the unmutated transaction, signs that, then applies the remaining mutations and keeps the signatures.
A candidate must also stay in the domain of its property: for example, Q4 never accepts a candidate with the fixed digest.

The reducer is deterministic, and it stops after a fixed number of candidates.
Its output has one of two labels:

- `minimal`: the reducer finished a complete final pass of steps 1 to 6 in which no change kept the failure condition. The output is *1-minimal* for the reducer's changes.
- `budget`: the limit of candidates ended the reduction before such a pass. The output still keeps the failure condition, but the reducer claims no minimality.

Only an output with the label `minimal` meets an exit condition that asks for a 1-minimal output.

### 7.5 Known behaviours

Some baseline behaviours violate a natural property, and the campaign must not report them as findings.
The driver keeps a list of them, each with its source:

- The fixed digest of section 4, item 2 (C2). A signature over the value one stays valid for every change that keeps SINGLE with `n` at least the number of outputs.
- The recovery branch without `CHECKLOCKTIMEVERIFY` accepts at every lock time (C5, lines 352–358). A known answer in `lake test` already covers lock time 0 ([SOUNDNESS.md](../../SOUNDNESS.md#script-worked-property-multisig-with-recovery)).
- Duplicate keys and a match against them, which the template allows (same section).

A failure that matches a known behaviour gets the label `known`, and the driver counts it separately.
An entry enters the list only with a citation of the pinned source.

### 7.6 The oracle format

The campaign needs no change to `dogelib-oracle/1`.
It sends only `script.verify_legacy` and `sighash.legacy`, with the existing arguments.
The signer's request mode is a change to a harness tool, a development interface under the [0.x policy](../oracle.md#format-stability).
`proposal-replay` answers the shape of `script.verify_legacy`, but it is a test executable, not the oracle.
The saved-failure format is a local file format of the driver, not a fixture format, until section 10 promotes a failure to a fixture.

## 8. The campaign's own self-test

### 8.1 The planted proposal fault

The campaign must find a counterexample to the faulty rule by search, without the hand-written case.
The property is `RestrictsAcceptance` of design record 0007: if the revised spend predicate accepts, the baseline accepts.
The driver sends each request to `dogelib-oracle` and to `proposal-replay ExampleFaultyLocktime faulty --active`.
A violation is a request that the second program accepts and the first rejects.

The search space follows the counterexample's context in the guide:

- The spending transaction: version 1, one input with a null outpoint and an empty `scriptSig`, no outputs.
- Lock times 0, 1, 2, 499,999,999 and 500,000,000, and sequences `0xfffffffe` and `0xffffffff`.
- Flags 0. The flag that discourages upgradable NOPs is outside the supported flags, so it gives `unsupported`.
- Previous-output scripts of one to five instructions from the alphabet `OP_0`, `OP_1`, `OP_2`, `OP_NOP4`, `OP_DROP`, `OP_VERIFY`, `OP_EQUAL` and a push of `80`, enumerated shortest first.

A hand derivation from the rule in `ExampleFaultyLocktime.lean` gives the result that the stage must show.
The shortest violations have three instructions, for example `51 00 b3`, that is, `OP_1 OP_0 OP_NOP4`, with lock time 2 and sequence `0xfffffffe`:

| Step | Baseline: `OP_NOP4` is a NOP | Faulty rule |
| --- | --- | --- |
| `OP_1`, `OP_0` | `[1, ""]` | `[1, ""]` |
| `OP_NOP4` | `[1, ""]` | The empty operand is 0, not negative, of the same type as lock time 2 and at most 2. The sequence is not final. The check passes and pops: `[1]` |
| Result | Rejected with `EVAL_FALSE` | Accepted |

No violation has fewer instructions.
A violation needs the faulty rule to accept, so its check passes, and the check needs an item on the stack.
With an empty `scriptSig`, a shorter script that passes the check is a push followed by `OP_NOP4`.
The pop then leaves an empty stack, so the faulty rule rejects.

The five-instruction case `51 52 b3 51 87` is 1-minimal for deletion alone, because each removal of one instruction loses the violation.
Step 3 of the reducer replaces the operand 2 with 0, which keeps the violation. Step 1 then removes the adjacent pair `51 87`, which gives `51 00 b3`.
So the self-test has two exit results: the blind search finds a three-instruction violation, and the reducer takes the five-instruction seed to three instructions.
The same search on the corrected variant must find no violation, because `corrected_restrictsAcceptance` is a theorem.
A violation there would show a mistake in `proposal-replay` or in the driver.

### 8.2 Planted harness and model faults

A planted proposal fault tests one class of error.
The campaign also needs a measure of its reach: a fault that triggers only on a deep path tests whether the generator reaches that path.

`scripts/test_campaign.py` runs the driver against a wrapper, as `test_compare_core.py` does, but each mutant has a semantic trigger:

| Mutant | Side | Trigger | Change | Expected class |
| --- | --- | --- | --- | --- |
| M1 | Core | A spend whose signature has hash type `0x82` and a transaction with at least three inputs | Accept a rejected spend | `verdict` |
| M2 | Lean | `sighash.legacy` with SINGLE and input index above 0 | Change one byte of the digest | `digest` |
| M3 | Core | Lock time exactly 500,000,000 on the recovery branch | Treat it as a height | `verdict` |
| M4 | Core | A sequence `0xffffffff` on an input other than `n` | Exit with status 3 | `crash` |
| M5 | Lean | Five or more outputs | Stop answering | `timeout` |
| M6 | Core | The fixed digest of section 4, item 2 | Return a digest other than one | `digest` |

The list is a proposal, and the stage settles the triggers.
For each mutant the self-test requires detection within the budget, and it records the case index of the first detection.
It also checks that the reducer keeps the trigger, and that replay reproduces the stored class.

Source-level mutants, such as a change of one line of `core_oracle.cpp`, measure the same reach with more fidelity.
Each one needs a separate harness build, so they stay a review practice, as in the review of pull request #129.

## 9. Production-path replay

### 9.1 Levels

A candidate counts as a finding only after a replay through Core's production path.
The record proposes three levels:

| Level | What runs | Use |
| --- | --- | --- |
| L1 | The harness function is the production function. | `script.verify_legacy` calls `VerifyScript`, and `sighash.legacy` calls `SignatureHash` ([docs/oracle.md](../oracle.md#what-the-harness-runs)). |
| L2 | A program in the shape of Core's unit tests calls the production function on a scratch state. | `BasicTestingSetup` or `TestingSetup` (C10), with the production function in `validation.cpp`. |
| L3 | A regtest node. | `sendrawtransaction` or `submitblock` (C11), or a `headers` message through the functional test framework (C11). |

For the signed-spend family, L1 is the minimum.
L1 does not include the caller of section 4, item 8. So a candidate that depends on the flags or the checker of a node also needs L3.
At L3 the outpoint must be a real output on regtest, which changes a committed field, so the replay signs again.

### 9.2 The current upstream revision

A candidate that reproduces at the pin is replayed against the current upstream revision of the Core branch that the pin belongs to.
The replay builds the harness from that revision into a separate build directory.
`scripts/build_core_harness.sh` fixes `PIN` (line 18), so the replay needs a revision argument for this purpose only.
The result is a comparison with that revision, labelled with its commit, and never a change to the pin in SOURCES.md.
The maintainer accepted such an argument on 2026-11-08 (decision 14).

The pin in SOURCES.md and in the CI comparison stays `e0a1c15`. An upstream build is evidence about upstream, never a change to the compatibility target.

### 9.3 Operations with a transcription

For `block.contextual_check` and `block.header_sequence`, the harness runs an H2 transcription, not the production function ([in-practice.md](../in-practice.md#transcriptions-in-the-harness)).
A candidate there needs L2 or L3:

- `ContextualCheckBlockHeader` has external linkage and a declaration in `validation.h` (C9). An L2 program can link `validation.cpp`, select the network with `BasicTestingSetup` and call it on a hand-built `mapBlockIndex`.
- `AcceptBlockHeader` is `static` (C9), so an L2 program calls `ProcessNewBlockHeaders` on a `TestingSetup` chainstate. That program is option H1 of design record 0008, section 8.2. It keeps the stated limit of H1: it cannot put the genesis entry in the failed list.
- At L3, the functional test framework sends the headers to a regtest node. The pin has no command that accepts a header alone.

### 9.4 A real finding

DogeLib has no security policy file.
A candidate that reproduces at L1, L2 or L3, on the pin and on the current upstream revision, can be a vulnerability in Core.
The record proposes this handling:

- Do not publish the input, an exploit or a description of the effect in the repository, an issue, a pull request or a CI log.
- Keep the saved failure in the uncommitted `build/campaign/` directory, and tell the maintainer privately.
- Report through the process of Core's SECURITY.md at the current upstream revision (C12). At the pin, that file still names version 1.14.8 as the supported version (line 5).
- Add the fixture and any public description of section 10 only after the report is resolved.

CI runs only fixed seeds whose results a person has already reviewed, so a public CI log never shows a first finding.
A campaign with a fresh seed runs on a contributor's machine.
The record recommends a `SECURITY.md` for DogeLib in a separate pull request, with a contact that the maintainer chooses (decision 15).

These rules take precedence over the rule of CONTRIBUTING.md that records a minimal reproducer in SOURCES.md ([sources of truth](../../CONTRIBUTING.md#sources-of-truth)), until the report is resolved.

## 10. Regression and proof follow-up

Each understood counterexample becomes a fixture:

- Fixtures go in `tests/script/campaign/` with a README that records the property, the plan, the seed, both revisions and the reduction.
- `SHA256SUMS` pins each fixture, and the pinned-vectors gate of [AGENTS.md](../../AGENTS.md#checks) adds the directory.
- The expected value of a fixture comes from the property and a hand check against the pinned source. If the counterexample shows a Lean mistake, the fixture keeps Core's behaviour as the expected value, with the citation.
- `compare_core.py` adds the fixtures as a named set, and `lake test` runs them where the operation has a known-answer runner.

Where practical, a counterexample also becomes a theorem.
Section 11 names the theorem targets that the properties suggest.
A fixed Lean mistake gets a theorem that excludes its class, when one fits the existing proof structure.

## 11. Properties

The properties are the targets of the campaign.
Each one has a domain and a source for its expected value. Where one exists, the table also names the Lean theorem that states the property for the Lean definitions.
A theorem about the Lean definitions says nothing about Core's compiled code.
So the campaign checks every property on both implementations.

Every property assumes the 2-of-3 instance with keys 1 to 4, the P2SH output of its exact redeem script, and the flag `P2SH`.
Without `P2SH`, the output accepts any `scriptSig` that pushes the redeem script last and runs no template code.

| Property | Statement | Expected value from | Lean coverage |
| --- | --- | --- | --- |
| Q1 Ordinary acceptance | For a signer pair in key order, signatures from the mode that preserves execution, an empty dummy and a true selector, the spend is accepted. The hash types are the defined ones, or any byte without `STRICTENC`. The flags are a subset of the supported set. | Section 4, items 3 and 4, and the template | `multisigRecovery_ordinary_complete`, relative to the verifier |
| Q2 Recovery under its lock time | Take key 4, a re-signed spend and a false selector. Take a lock time from 1,000,000 to 499,999,999, and a sequence of input `n` other than `0xffffffff`. Then the spend is accepted. | Item 5 | `multisigRecovery_recovery_complete`, relative to the verifier |
| Q3 Early recovery fails | Take `CHECKLOCKTIMEVERIFY` and a false selector. Then `UNSATISFIED_LOCKTIME` follows from each of these: a lock time below 1,000,000 or of at least 500,000,000, or a final sequence of input `n`. The result holds in both modes. | Item 5, and the order of the template: the lock-time check runs before `OP_CHECKSIG` | `multisigRecovery_lockTime_lt` for the first case only |
| Q4 Committed fields | Take the mode that tests a commitment, and change a field that the hash type commits to (section 6.3). Then the Lean preimage and Core's digest change, and the spend is rejected. The fixed digest is outside the domain. | The table of section 6.3 | `legacySignatureHashPlan_allOnly_commits` for ALL without ACP |
| Q5 Open fields | Take the mode that tests a commitment. The mutation keeps the `scriptSig` of input `n`, so it keeps the unlocking stack, the branch and the signature encodings. It changes only fields that are open for the hash type of every signature that the spend uses. Then both digests and the accepted verdict stay unchanged. | The table of section 6.3, and item 6 | The theorems of section 6.3, except NONE and SINGLE with ACP |
| Q6 Agreement | Lean and Core give the same response to each request of the campaign, under `compare` of `compare_core.py`. | The comparison itself | None. A compatibility claim |
| Q7 The fixed digest | Take SINGLE with `n` at least the number of outputs. Both programs return plan `fixed_digest` and the digest one. Take a change that keeps the condition and the hash type of every signature. If it also keeps the fields of item 6, including the `scriptSig` of input `n`, the spend stays accepted. | Item 2 | `legacySignatureHashPlan_eq_fixedDigest_iff` |

Q4 assumes that double SHA-256 has no collision on the inputs of the run, as the commitment checks of `lake test` do ([SOUNDNESS.md](../../SOUNDNESS.md#legacy-signature-hash-what-all-commits-to)).
Its rejection also assumes that no one can forge a signature for the changed digest.
So a Q4 failure on acceptance is a candidate, not a proof of a forgery.
The preimage statement of Q4 is not a cryptographic security claim ([in-practice.md](../in-practice.md#what-a-theorem-does-and-does-not-establish)).

The properties go beyond the Lean theorems in three ways:

- Core's compiled code has no theorem, so Q1 to Q5 and Q7 are property checks of Core.
- The Lean theorems hold relative to a verifier parameter. The campaign runs `coreVerifier` on real signatures.
- The campaign reaches domains that no theorem covers. They include NONE and SINGLE with ACP, several inputs, every input position and hash-type bytes without `STRICTENC`.

The properties suggest these theorem targets.
The names are proposals:

| Target | Statement | Cost |
| --- | --- | --- |
| `multisigRecovery_lockTime_ge_threshold` | With `CHECKLOCKTIMEVERIFY`, a false selector and a lock time of at least 500,000,000, `verifyLegacySpend` gives `UNSATISFIED_LOCKTIME` before any signature check. | Cheap, beside `multisigRecovery_lockTime_lt` |
| `multisigRecovery_finalSequence` | The same for a sequence of input `n` equal to `0xffffffff`, at every lock time. | Cheap |
| `legacySignatureHashPlan_eq_of_none_anyoneCanPay` | Take NONE with ACP, and an input index `n` of both transactions. Then agreement on the version, the lock time and the outpoint and sequence of input `n` gives equal plans. | New lemmas |
| `legacySignatureHashPlan_eq_of_single_anyoneCanPay` | The same for SINGLE with ACP, with agreement on output `n` as well, and an output count above `n` in both transactions. | New lemmas |
| `faulty_counterexample_short` | `baselineSpend` rejects `51 00 b3` with lock time 2 and `EVAL_FALSE`, and the faulty spend predicate accepts it. | Cheap, beside `faulty_counterexample` |

No target assumes collision resistance or another cryptographic property.

## 12. Further options

**Native fuzzing.**
A libFuzzer target around `VerifyScript`, with a mutator that builds plans of section 6.1, would run many more cases per second than the JSON pipeline.
Builds with AddressSanitizer and UndefinedBehaviorSanitizer would also find memory errors and undefined behaviour in Core, which a verdict comparison cannot see.
Both need a separate build of Core with Clang, and the Lean side cannot run in the same process.
The record keeps them as a later option, for the time when the throughput of the driver limits the campaign.

**Plausible.**
Plausible gives property testing with shrinking inside Lean.
At commit `55c8532` of `leanprover-community/plausible`, the documentation of its tactic says: "If no counter-examples are found, `plausible` behaves like `admit`" (`Plausible/Tactic.lean`, line 85).
A goal that a tactic admits depends on `sorryAx`, and `lake exe check-decls` rejects that axiom ([SOUNDNESS.md](../../SOUNDNESS.md#c1-the-lean-kernel-and-its-axioms)).
So Plausible could serve only in a test package, and its result could never back a theorem.
It also needs a package proposal, because the root package has no Lake dependencies.

## 13. Stages and exit conditions

### Stage 1: driver, saved failures and replay

The stage adds `scripts/campaign.py` with `run` and `replay`, the outcome classes, batches with bisection, and the saved-failure format.
Its first input is the existing signed-spend and targeted lock-time requests, without generation.

The stage exits with these results:

- `scripts/test_campaign.py` with wrapper mutants for each class of section 7.2. Each mutant gives a saved failure whose replay reproduces the class. Signer refusals enter in stage 2, with the signer path of section 7.4.
- Zero failures on the existing requests, with the counts of each class.

### Stage 2: the signer and the generator

The stage adds `core-signer --sign` and the generator of section 6, with the table of section 6.3. It also adds the known behaviours of section 7.5 and the properties Q1 to Q7.

The stage exits with these results:

- A run at a fixed seed with zero failures other than `known`, and the coverage counts of section 6.4.
- The mutants M1 to M6 of section 8.2, each detected within the budget. A survivor fails the stage until the generator or the trigger changes.
- A check that the signer gives the same bytes for the same request twice, and a signer refusal whose replay with `--signer` reproduces it.

### Stage 3: the reducer and the planted fault

The stage adds `reduce` and the test executable `proposal-replay` (section 5.3).

The stage exits with these results:

- The blind search of section 8.1 finds a violation of three instructions, and it finds none for the corrected variant.
- The reducer takes `51 52 b3 51 87` to a three-instruction violation, with the label `minimal` of section 7.4.
- The reducer keeps the trigger of each mutant of section 8.2.

### Stage 4: production replay

The stage adds the replay procedure of section 9 for the signed-spend family at L1 and L3. It also adds the revision argument of section 9.2.

The stage exits with an end-to-end run on a planted harness fault.
The campaign finds the fault, reduces it, replays it at L1 with the unchanged harness and at L3, and classifies it as a harness fault.
So the procedure shows that it rejects a candidate that the production path does not reproduce.

### Stage 5: regression and proofs

The stage adds the fixtures of section 10 for every understood counterexample, including the three-instruction case of section 8.1.
It proves the theorem targets of section 11 that the maintainer accepts. It also adds a fixed-seed campaign with a small budget to the `core` workflow.
COVERAGE.md, SOUNDNESS.md and [docs/oracle.md](../oracle.md) change in the same pull request.

## 14. Decisions

These proposals wait for a maintainer decision:

| Number | Topic | Proposal | Alternative | Status |
| --- | --- | --- | --- | --- |
| 1 | Family | The 2-of-3 instance of the multisig-with-recovery template with keys 1 to 4, under P2SH in base mode. Cases have several inputs and outputs and every hash type (section 3.1). | Several templates, or other `k` and `n`. | Proposed |
| 2 | Properties | Q1 to Q7 of section 11, with agreement Q6 kept apart from the properties. | Agreement alone. | Proposed |
| 3 | Signer | S1: `core-signer --sign`, with a check of its digest against both programs (section 5.1). | S2: an independent Python signer. | Proposed |
| 4 | Expected values | From the property, the plan and the hand-derived table of section 6.3. Never from either implementation or the signer's verdict (section 6.5). | Core's verdict, as in `recovery.jsonl`. | Proposed |
| 5 | Driver | C2: a separate `scripts/campaign.py` that reuses `compare`. The CI stream does not change (section 5.2). | C1: options in `compare_core.py`. | Proposed |
| 6 | Saved failures | `dogelib-campaign-failure/1`, one file for each failure under `build/campaign/`, never committed (section 7.3). | One appended log for each run. | Proposed |
| 7 | Outcome classes | The six classes and the side table of section 7.2, with known behaviours counted apart (section 7.5). | Pass and fail only. | Proposed |
| 8 | Isolation | Batches with bisection on a stream-level failure (section 7.1). | One process for each request. | Proposed |
| 9 | Reducer | Changes to the plan in the order of section 7.4, aware of the signing mode and deterministic. It claims 1-minimality only after a complete final pass, and labels other output `budget`. | Byte-level delta debugging alone. | Proposed |
| 10 | Oracle format | No change to `dogelib-oracle/1`. The signer's request mode is a change to a harness tool under the 0.x policy (section 7.6). | A campaign operation in the oracle. | Proposed |
| 11 | Planted fault | E1: the test executable `proposal-replay`, outside `Exports`, and the exit results of section 8.1. | E2: a search and reducer in Lean. | Proposed |
| 12 | Reach | Semantic wrapper mutants M1 to M6 with a detection record (section 8.2). Source mutants stay a review practice. | Source mutants built for each run. | Proposed |
| 13 | Production replay | Levels L1 to L3. A candidate counts as a finding only after L1 for Script, and after L2 or L3 for an operation with a transcription (section 9.1). | Report on the harness result alone. | Proposed |
| 14 | Upstream check | Replay at the current upstream revision of the pin's branch, from a separate build with a revision argument, labelled with its commit (section 9.2). No change to the pin. | Check by source inspection only. | Proposed |
| 15 | Disclosure | The rules of section 9.4, fixed seeds only in CI, and a DogeLib `SECURITY.md` in a separate pull request. | Public issues for all candidates. | Proposed |
| 16 | Regression | Fixtures in `tests/script/campaign/` with `SHA256SUMS`, a named comparison set and theorem targets of section 11 (section 10). | Saved failures without fixtures. | Proposed |
| 17 | Exclusions | Transaction validation and the UTXO set, resource bounds, native fuzzing, Plausible and header targets stay outside this scope (sections 1 and 12). | None in this scope. | Proposed |

The maintainer answered three questions of the proposal on 2026-11-08.
The decisions stay Proposed until adoption:

- Decision 11: a test-only `proposal-replay` outside `Exports` is consistent with decision 8 of design record 0007, because that decision concerns oracle operations.
- Decision 14: the harness build may take a revision argument for labelled upstream replay builds. The pin in SOURCES.md and in the CI comparison stays `e0a1c15`.
- Section 8.1: the exit condition is a three-instruction violation, not the five-instruction case.

One question stays open:

- Decision 15: which contact does a DogeLib `SECURITY.md` give? The two options are GitHub private vulnerability reporting and an email address.

## 15. Remaining risks

| Risk | Mitigation |
| --- | --- |
| Lean and Core share a mistake in the signature hash, and S1 signs with Core's digest, so the comparison sees agreement. | Q4 and Q5 check commitments on both sides from the hand-derived table. S2 stays available. |
| The table of section 6.3 is wrong, so the campaign reports false failures or misses real ones. | Review against C1 and C2, and against the Lean commitment theorems for four of its columns. A false failure shows as "both violate" in section 7.2. |
| The generator never reaches a deep path, so zero failures say little. | The coverage counts of section 6.4 and the mutants of section 8.2. |
| The reducer changes the failure into a different one. | The failure condition keeps the property, the class and the side, and replay checks the output. |
| A campaign agreement is read as a proof for all inputs. | A finite comparison covers its requests only ([in-practice.md](../in-practice.md#what-a-theorem-does-and-does-not-establish)). Reports give counts and seeds. |
| A harness mistake is reported as a Core bug. | Section 9 and the end-to-end exit condition of stage 4. |
| A public CI log or fixture publishes a vulnerability before a report. | Section 9.4: fixed seeds in CI, uncommitted storage and fixtures after resolution. |
| The bisection meets a failure that depends on more than one request. | The driver saves the whole batch when no single request reproduces the failure. |
| Python's `random` gives a different sequence in a later release, so a seed stops reproducing a run. | A saved failure stores the exact requests, so replay does not depend on the generator. |

There is no pin change, trust-policy exception or change to an agreed theorem statement in this record.
Decision 6 introduces a local file format, and decision 16 introduces a fixture directory, which adoption would settle.
Adoption of the scope does not establish any property or theorem target, and it does not authorize the merge of a later implementation.
