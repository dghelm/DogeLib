# Campaign regression fixtures

These fixtures keep the understood counterexamples of the bug-finding campaign, as [design record 0009, section 10](../../../docs/design/0009-bug-finding-campaign.md#10-regression-and-proof-follow-up) requires.
No fixture records a finding in Core or in DogeLib: the campaign found no such finding.
Each fixture is a counterexample that the campaign's self-test planted and then found.

The expected value of each fixture comes from its property and a hand check against the pinned source.
No expected value comes from DogeLib, from the Core harness or from the campaign's saved responses.
The responses of the search only show which side failed the property.

## Files

The files reuse the record format of [`tests/oracle`](../../oracle/README.md).
Each line holds one `dogelib-oracle/1` request, and the same line of another file holds its expected response.
[docs/oracle.md](../../../docs/oracle.md) defines the format.

| File | Content |
| --- | --- |
| `requests.jsonl` | One `script.verify_legacy` request for each fixture, with the transaction checker |
| `expected.jsonl` | The baseline response: `dogelib-oracle` and the Core harness must both give it |
| `expected-faulty.jsonl` | The response of `proposal-replay ExampleFaultyLocktime faulty --active` |
| `expected-corrected.jsonl` | The response of `proposal-replay ExampleFaultyLocktime corrected --active` |
| `SHA256SUMS` | The SHA-256 of each JSONL file |

`proposal-replay` answers a request with `revisedVerifyLegacySpend` of the named variant ([the planted proposal search](../../../docs/oracle.md#the-planted-proposal-search)).
The two revised files have a line for each request, so the M3 fixture also checks that the revision leaves a spend without `OP_NOP4` unchanged.

## Checks

- `lake test` runs each request through `verifyLegacySpend` with `coreVerifier` and compares the verdict and error name with `expected.jsonl`. It runs `revisedVerifyLegacySpend` with `active` true for both variants against the two revised files (`tests/KnownAnswers/Campaign.lean`).
- `scripts/compare_core.py` sends the requests to `dogelib-oracle` and to the Core harness as the set `Script campaign fixtures`, and requires agreement. With the `lake test` check, agreement means that the harness also gives the response of `expected.jsonl`.
- The pinned-vectors gate of [AGENTS.md](../../../AGENTS.md#checks) checks `SHA256SUMS`.

## Revisions

Each fixture comes from a run with a clean tree:

- `proposal-faulty-locktime-5100b3`: the proposal search ran at DogeLib commit `8f73e380f712b7240306a76c75af867dd897fe3b`.
- `harness-fault-m3-locktime-500000000`: the detection and reduction ran at DogeLib commit `43b9ed172f8ed8299645210a4b0674cb533fa9f2`.
  That commit adds only the `--keep` option of `scripts/test_campaign_production.py` to `8f73e38`.

The Core revision is the compatibility pin `e0a1c157791544e818c901bd9341896965afbf9d` ([SOURCES.md](../../../SOURCES.md)).
The harness and the regtest node were built at the pin with `scripts/build_core_harness.sh` and `scripts/build_core_node.sh`.
The `id` of each request is new. Every other field is the exact request of the saved failure.

## `proposal-faulty-locktime-5100b3`

| Item | Value |
| --- | --- |
| Property | `RestrictsAcceptance` of design record 0007: if the revised spend predicate accepts, the baseline accepts ([design record 0009, section 8.1](../../../docs/design/0009-bug-finding-campaign.md#81-the-planted-proposal-fault)) |
| Failing side | `revised`: the faulty rule of `DogeLib.Proposals.ExampleFaultyLocktime`, a deliberate fault, not a proposal for Dogecoin |
| Plan | Script `51 00 b3` (`OP_1 OP_0 OP_NOP4`). Version 1, one input with a null outpoint, an empty `scriptSig` and sequence `0xfffffffe`, no outputs, lock time 2, flags 0 |
| Search | `campaign.py run --campaign proposal --variant faulty --seed 0 --cases 5840`. The search enumerates without a seed. The 5,840 cases are all scripts of one to three instructions. Case 1,394 is this fixture, and its saved request had the `id` `proposal-1394`. The search found 16 violations, all of three instructions |
| Reduction | None. The fixture is the search output. `campaign.py reduce` on it gives the label `minimal` after 16 candidates, with two step 3 changes: lock time 0 and sequence 0. The fixture keeps lock time 2 and sequence `0xfffffffe`, the case of section 8.1 and of the theorem target `faulty_counterexample_short` |

Expected values, by hand from pinned `src/script/interpreter.cpp` (SOURCES.md, D3) and `src/script/script.h` (D24):

- **Baseline: rejected, `EVAL_FALSE`.** `OP_1` pushes `01` (lines 317 to 341), and `OP_0` pushes the empty vector (lines 306 to 310). Without `DISCOURAGE_UPGRADABLE_NOPS`, `OP_NOP4` does nothing (lines 429 to 433). The stack is `[01, ""]`. `CastToBool` of the empty top item is false (lines 38 to 50), so `VerifyScript` returns `EVAL_FALSE` (lines 1432 to 1435).
- **Faulty rule: accepted, `OK`.** At `OP_NOP4` the rule runs the check of `OP_CHECKLOCKTIMEVERIFY` (lines 360 to 390). The empty operand is the number 0, so it is not negative. 0 and the lock time 2 are both below `LOCKTIME_THRESHOLD`, 500,000,000 (`script.h`, line 35), and 0 is at most 2 (lines 1283 to 1292). The sequence is not final (lines 1304 and 1305). The check passes, and the faulty rule pops the operand. The stack is `[01]`, and `VerifyScript` accepts.
- **Corrected rule: rejected, `EVAL_FALSE`.** The same check passes, and the corrected rule keeps the operand, as `OP_CHECKLOCKTIMEVERIFY` does. The stack is `[01, ""]`, as in the baseline.

The rule of each variant is the hand derivation of design record 0009, section 8.1, from `ExampleFaultyLocktime.lean`.

## `harness-fault-m3-locktime-500000000`

| Item | Value |
| --- | --- |
| Property | Q3 of [design record 0009, section 11](../../../docs/design/0009-bug-finding-campaign.md#11-properties): with `CHECKLOCKTIMEVERIFY` and a false selector, a lock time of at least 500,000,000 gives `UNSATISFIED_LOCKTIME` |
| Failing side | `core`, from the planted harness fault M3 of section 8.2. A wrapper around the harness treats lock time 500,000,000 as a height on the recovery branch |
| Label | `harness-fault`. At the pin, the unchanged harness does not reproduce the candidate at L1. A regtest node rejects the re-signed spend with `UNSATISFIED_LOCKTIME` in its mempool and in a block (L3) |
| Search | The stage 4 self-test: `python3 -I scripts/test_campaign_production.py .lake/build/bin/dogelib-oracle build/core-harness/core-oracle --node build/core-node --keep build/campaign/stage5-m3`. The generated campaign runs at seed `20261108`, with a budget of 3,000 cases and 120 seconds. With batches of 16 and a timeout of 3 seconds, it detects M3 at case 1,907 |
| Plan at detection | Preserve mode, recovery branch, key 4, `SIGHASH_ALL`, flags 1567. Version 2, lock time 500,000,000, three inputs with the template at position 2, five outputs |
| Reduction | `campaign.py reduce`, through the M3 wrapper: label `minimal` after 16 candidates. It removed two inputs and all five outputs, set the version to 1 and cleared the flags 2, 4, 8, 16 and 1024 |
| Reduced plan | Preserve mode, recovery branch, key 4, `SIGHASH_ALL`, flags 513 (`P2SH` and `CHECKLOCKTIMEVERIFY`). Version 1, one input with sequence 0, no outputs, lock time 500,000,000. `core-signer --sign` signed it |

The fixture is the `script.verify_legacy` request of the reduced failure.
The reduced failure also has two `sighash.legacy` requests for the signing digest, which the fixture leaves out.
The signature has no part in the expected value, because the lock-time check fails first.

Expected value, by hand from pinned `src/script/interpreter.cpp` (D3) and `src/script/script.h` (D24): **rejected, `UNSATISFIED_LOCKTIME`**, for the baseline and for both revised variants.

1. The `scriptSig` pushes a 71-byte signature, the empty vector and the 149-byte redeem script of the 2-of-3 template. The empty vector is the false selector. The previous-output script is `OP_HASH160 <20 bytes> OP_EQUAL`. Python's `hashlib` gives the HASH160 of the redeem script as those 20 bytes.
2. With `P2SH` set, `VerifyScript` evaluates the redeem script on the stack `[signature, ""]` (lines 1457 to 1477).
3. `OP_IF` pops the empty selector, which is false, so the `OP_ELSE` branch runs (lines 437 to 467).
4. The branch pushes the operand `40 42 0f`, which is 1,000,000. `OP_CHECKLOCKTIMEVERIFY` runs, because its flag is set (lines 350 to 390).
5. `CheckLockTime` compares the operand with the lock time 500,000,000 (lines 1283 to 1287). The lock time is at least `LOCKTIME_THRESHOLD` (`script.h`, line 35), and the operand is below it. The types differ, so the check fails, and the result is `UNSATISFIED_LOCKTIME` (line 387).
6. The scripts contain no executed `OP_NOP4`, so both revised variants give the same result.
