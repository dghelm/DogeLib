# Synthetic regtest header sequences

`sequences.json` supplies exact requests and hand-derived expectations for design record 0008, section 9.4.
`lake test` runs the first header of each case through `acceptBlockHeader` (`tests/KnownAnswers/HeaderSequence.lean`, `checkRegtestSteps`).
It also runs every case in full through `processNewBlockHeaders` (`checkRegtestSequences`), and compares every expected field.
The oracle and the Core comparator do not consume the fixture yet.
Its record shape is local to the fixture and does not settle the stage 5 oracle interface.

## Reproduction (D83)

The independent standard-library generator mines headers with `hashlib.scrypt`, using N = 1024, r = 1, p = 1 and 32 output bytes.
`seed.txt` supplies the ASCII seed.
SHA-256 of the seed, a colon and the header name supplies each Merkle root.
Mining tests nonces from zero in increasing order.
`bad_nonce` instead changes only the nonce of `b` to the first failing value.

The `headers` table records every full header, its double-SHA-256 display hash and its scrypt digest in internal byte order.
An AuxPoW header's recorded scrypt digest covers its pure header, not its parent.
The known-AuxPoW case tests the duplicate bypass and does not assert valid AuxPoW commitments.

Run these commands from the repository root:

```bash
python3 -I scripts/generate_header_sequences.py --check
(cd tests/block/regtest-header-sequences && sha256sum -c SHA256SUMS)
```

To reproduce the fixture in place, run `python3 -I scripts/generate_header_sequences.py`.
The `--check` mode never writes expectations or fixture bytes.
CI uses only `--check`.
The generator contains explicit expectation declarations and does not implement header acceptance.
It computes no verdict from DogeLib or the Core harness.

## Context and derivations

The reference revision is Dogecoin Core `e0a1c157791544e818c901bd9341896965afbf9d`.
Regtest uses proof-of-work limit `0x207fffff`, genesis time 1296688602 and nonce 2 (`src/chainparams.cpp:392,446-451`).
Ordinary generated headers have version `0x00620004`, correct chain ID and no AuxPoW flag.
Three-second spacing returns the limit below height 10 (`src/pow.cpp:54-62`).
From height 10, the DigiShield modulation gives `1 + trunc((3 - 1)/8) = 1`, preserving the target (`src/dogecoin.cpp:50-86`).

The activation cases also cover the regtest transition at height 20 and version thresholds 1251 and 1351.
The version cases supply eleven linked predecessors, and the lowest of them is a trusted anchor.
These supplied index entries are context, not assertions of full-chain acceptance.

Each request supplies an index, an ordered failed list, exact full headers and one adjusted time, 1296688702.
Checkpoints are disabled.
The initial validity level is tree-valid unless `scripts_valid` is true.
`anchor` cuts the predecessor walk without changing the raw header bytes.
All other initial flags are explicit.

The expected `added` list fixes insertion order, hash, height and chain work.

## Chain work

Each request index entry supplies `chain_work`, and each expected `added` entry gives it.
The value is a 256-bit number as 64 hexadecimal digits, most significant digit first.
The model does not check the chain work of a supplied entry, so a supplied value is context, as an anchor is.

Every added entry has bits `0x207fffff` or `0x207ffffe`.
`SetCompact` gives the target `t = m * 2^232` with `m = 0x7fffff` or `0x7ffffe`, without sign or overflow.
Then `2(t + 1) < 2^256 < 3(t + 1)`, so `GetBlockProof` gives `floor(2^256 / (t + 1)) = 2` (`src/chain.cpp:150-163`).
The generator asserts this value with Python integers, as `PROOF`.

`AddToBlockIndex` adds the proof to the predecessor's `nChainWork`, modulo 2^256, and gives genesis the proof alone (`src/validation.cpp:2780`).
So an entry at height `h` on a chain from genesis has chain work `2(h + 1)`.
Each supplied entry of such a chain carries that value.

The version cases supply their own anchor work: 2^128 below height 1251, and 2^256 − 23 below height 1351.
An entry `k` heights above the anchor has the anchor work plus `2k`.
In `version-upgraded-1351`, the entry at height 1350 has chain work 2^256 − 1, and the entry at height 1351 wraps to 1.
`last_hash` is null after rejection because the sequence result carries an error, rather than Core's retained pointer to a successful prefix.
Failure positions are zero-based.

Each case has a `derivation` with pinned source file and line citations.
The principal branches are `src/validation.cpp:3205-3267` and the stop-on-error loop at lines 3274–3282.
Reject constants and zero-score `Invalid` come from `src/consensus/validation.h:12-19,35-53` (D84).
The median is the upper middle sorted timestamp of at most eleven predecessors (`src/chain.h:284-301`).
`short-anchor-view` expects the specification's adapter error, not a Core rejection.
Its truncated index cannot represent Core's complete ancestor chain (design record 0008, sections 5.3 and 7.1).

The plus-one mutations distinguish two boundaries.
At the limit, plus one is `0x20800000`, which fails the target range check and gives `high-hash`.
With a predecessor at `0x207ffffe`, a one-second gap requires those harder bits, so plus one can pass work and give `bad-diffbits`.
No header after a rejected position runs, and successful prefix insertions remain.

The failed-ancestor cases record exact hashes in `marked_failed_child`.
The failed ancestor itself gets no added mark.
For two failed ancestors, the marks follow the fixture's list order.
`compare_marked_failed_child` is false for those cases because Core visits pointer-address order (design record 0008, decision 12).
Other response fields remain comparable.

## Case inventory

| Case | Expected result | DoS | Reject code | Added child marks |
| --- | --- | --- | --- | --- |
| `linear-extension` | Accepted | None | None | 0 |
| `empty` | Accepted | None | None | 0 |
| `unknown-first` | Position 0: bad-prevblk | 10 | 0 | 0 |
| `unknown-middle` | Position 1: bad-prevblk | 10 | 0 | 0 |
| `nonce-failure` | Position 0: high-hash | 50 | 16 | 0 |
| `wrong-bits-middle` | Position 1: bad-diffbits | 100 | 16 | 0 |
| `bits-plus-one-middle` | Position 1: bad-diffbits | 100 | 16 | 0 |
| `limit-plus-one` | Position 1: high-hash | 50 | 16 | 0 |
| `duplicate-in-call` | Accepted | None | None | 0 |
| `duplicate-failed_valid` | Position 0: duplicate | 0 | 0 | 0 |
| `predecessor-failed_valid` | Position 0: bad-prevblk | 100 | 16 | 0 |
| `duplicate-failed_child` | Position 0: duplicate | 0 | 0 | 0 |
| `predecessor-failed_child` | Position 0: bad-prevblk | 100 | 16 | 0 |
| `flagged-genesis` | Accepted | None | None | 0 |
| `genesis-insertion` | Accepted | None | None | 0 |
| `known-invalid-work` | Accepted | None | None | 0 |
| `known-changed-auxpow` | Accepted | None | None | 0 |
| `failed-grandparent` | Position 0: bad-prevblk | 100 | 16 | 1 |
| `scripts-valid-bypass` | Accepted | None | None | 0 |
| `failed-flag-outside-list` | Accepted | None | None | 0 |
| `context-before-failed-ancestor` | Position 0: time-too-old | 0 | 16 | 0 |
| `two-failed-genesis-a` | Position 0: bad-prevblk | 100 | 16 | 2 |
| `two-failed-a-genesis` | Position 0: bad-prevblk | 100 | 16 | 1 |
| `two-branches` | Accepted | None | None | 0 |
| `future-time` | Position 0: time-too-new | 0 | 16 | 0 |
| `short-anchor-view` | Position 0: shortView | None | None | 0 |
| `digishield-transition` | Accepted | None | None | 0 |
| `auxpow-transition-nonlegacy` | Accepted | None | None | 0 |
| `legacy_19` | Accepted | None | None | 0 |
| `legacy_20` | Position 0: late-legacy-block | 100 | 16 | 0 |
| `version-boundary-1251` | Position 1: bad-version(0x00000002) | 0 | 17 | 0 |
| `version-upgraded-1251` | Accepted | None | None | 0 |
| `version-boundary-1351` | Position 1: bad-version(0x00000003) | 0 | 17 | 0 |
| `version-upgraded-1351` | Accepted | None | None | 0 |

The mainnet fixtures supply the production retarget, checkpoint and version-activation contexts.
They include `tests/work/mainnet-headers` and the three full-header ranges beside this directory.
`tests/KnownAnswers/HeaderSequence.lean` derives the mainnet mutation verdicts by hand, and runs them through the compiled code.
Regtest needs no testnet-specific sequence rule.

Licence: original fixture data and generator under the repository licence.
Core source inspection and the genesis constants use the [Dogecoin Core MIT licence](../../../LICENSES/dogecoin-core-MIT.txt).
