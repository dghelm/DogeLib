# Brief of the block subsidy read

This text is the prompt that produced [the record](../subsidy.md).
It is exact, except that four placeholders replace the DogeLib revision and the local paths.

````markdown
# Model read: Block subsidy against Dogecoin Core and Boost 1.70.0

You are an independent reviewer. You did not write this code. Read the Lean definitions line by line against Dogecoin Core's C++ at the pinned revision and against the Boost 1.70.0 headers that Core calls, and report every place where they disagree. Don't trust doc comments, COVERAGE.md or SOURCES.md. Read the code on both sides.

- DogeLib (read-only): <DogeLib clone> at commit <DogeLib revision>
- Core at the pin e0a1c157791544e818c901bd9341896965afbf9d (read-only): <Dogecoin Core clone>
- Boost 1.70.0 headers (read-only): <Boost 1.70.0 include directory>

## Scope

**Lean**, definitions outside `Proofs/` and `Exports/`: DogeLib/Block/Subsidy.lean, with `Hash256.displayBytes` of DogeLib/Base/Bytes.lean

**Core**: src/dogecoin.cpp (generateMTRandom, GetDogecoinBlockSubsidy); src/amount.h (COIN); src/uint256.cpp (base_blob::GetHex, ToString); src/chainparams.cpp (nSubsidyHalvingInterval and fSimplifiedRewards of the mainnet records, the record tree and GetConsensus); src/consensus/params.h; the call in src/validation.cpp (ConnectBlock, line 1996)

**Boost**: boost/random/mersenne_twister.hpp (mersenne_twister_engine: seed(value), normalize_state, twist, operator(), and the mt19937 typedef); boost/random/uniform_int.hpp; boost/random/uniform_int_distribution.hpp (generate_uniform_int, every branch that `boost::uniform_int<>(1, range)` with a `boost::mt19937` can reach); boost/random/detail/signed_unsigned_tools.hpp (subtract, add)

Each Lean module's doc comments state its declared domain. A documented domain restriction is not a finding, but check that the restriction is stated, and that behaviour inside the domain matches Core and Boost. The Lean definitions cover mainnet only. The draw takes fuel, and the error `fuelExhausted` has no counterpart in Core: that is documented, so it is not a finding, but say whether the fuel can change a result that Core returns.

## Method

For each Core and Boost function, find the Lean counterpart and compare:
- the order of steps;
- the C++ types of every intermediate value (`int`, `long`, `unsigned int`, `uint32_t`, `CAmount`, Boost's `range_type`, `base_unsigned` and `mixed_range_type`), and their conversions;
- bounds and off-by-one cases, including the substring of the hash text and the bucket size;
- signedness, overflow, wrapping and truncation, including the shifts;
- byte order and hexadecimal digit order of the hash;
- the indices and the update order of the in-place twist, including Boost's split loops;
- the tempering constants and the seeding constant;
- height and parameter boundaries, and which record `GetConsensus` selects.

Where they differ, try to give a concrete input that would produce different results. For any you are unsure of, say so, and give the input that would settle it. The project's differential comparison (`scripts/compare_core.py`, operation `block.subsidy`) can test it.

## Output

Your final message is the record. Write it as Markdown in this shape:

```
# Model read: Block subsidy

- Reader: <model name and version>, an independent model reviewer, not a human
- Date: 2026-11-13
- DogeLib: <DogeLib revision>. Core: e0a1c157791544e818c901bd9341896965afbf9d. Boost: 1.70.0
- Scope: <files>

## Result
<two or three sentences: discrepancies found, yes or no; overall confidence>

## Findings
<one entry per discrepancy or suspected discrepancy: Lean file:line, Core or Boost file:line, what differs, a concrete input if known, severity (consensus-divergent / domain-boundary / documentation-only), confidence>

## Checked and agreeing
| Core or Boost construct (file:lines) | Lean definition (file:line) | Notes |
<one row per function or step you actually compared>

## Not checked
<anything in scope you did not compare, and why>
```

Be terse. Don't pad the agreeing table with prose.
````
