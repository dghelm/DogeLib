# Rust bounded CompactSize reader

`decode` reads a CompactSize prefix from a Rust byte slice.
It returns `Truncated`, `NonCanonical`, `TooLarge`, or `Success { value, consumed }`.
The remaining bytes start at `consumed`.
The implementation follows `ReadCompactSize` in pinned Dogecoin Core (SOURCES.md, D1).
It checks truncation, canonicality and `MAX_SIZE` in that order.

The Rust crate and its generated model are DogeLib material under the MIT licence.
The imported Aeneas library is a separate Apache 2.0 dependency.

`Refinement.Rust.CompactSize.decode_refines` compares the extracted model with `CompactSize.decodeBounded` on every Rust-representable byte slice.
It preserves all errors, the value and the remainder.
The abstraction maps a Rust panic or divergence to `none`, so the equality also excludes those outcomes.
`consumed_bounds` bounds the successful consumed count by the input length and restricts it to 1, 3, 5 or 9.
Rust `usize` uses Lean core's opaque platform word size, and the refinement holds on both 32- and 64-bit platforms.

Both theorems use only `propext`, `Classical.choice` and `Quot.sound`.
[SOUNDNESS.md](../../SOUNDNESS.md#b6-extraction-and-the-rust-toolchain) states the extraction and execution boundaries.

For example, `fe 01 00 00 02` returns `TooLarge`, because its canonical value exceeds `0x02000000`.
The input `ff ff ff ff ff 00 00 00 00` returns `NonCanonical` before the size check.
A successful read of `fd fd 00 ab` returns value 253 and consumed count 3, leaving `ab`.

## Regenerate the model

Run these commands from the repository root on Linux x86_64:

```bash
Refinement/Rust/setup-tools.sh
Refinement/Rust/regenerate.sh
Refinement/Rust/regenerate.sh --check
```

The setup script requires authenticated `gh` access for the release download.
Run `gh auth login` before setup.
It uses the exact-pin Aeneas release and builds Charon from its pinned source.
It installs Rust with user-local rustup and never installs system packages.
Both tools use `build/tools` by default, and both scripts accept `--tools-dir DIR`.
The intermediate LLBC file stays in `.lane/`.

The generated file is `../Refinement/Rust/Generated/DogelibCompactsize.lean`.
Do not edit it by hand.
The check extracts into a temporary lane directory and compares the full generated directory with the model files in the working tree.
Check mode also puts the intermediate LLBC file in that temporary directory.

CI builds the committed Lean model with the Mathlib cache.
The `ci` workflow also runs native Rust tests and extraction freshness on every pull request and push to `main`.
The extraction cache key includes the runner OS, architecture, pinned Rust nightly and setup script hash.
The setup script contains the Charon and Aeneas pins, so a pin change selects a different cache.
Setup checks the tool versions and Aeneas archive digest after cache restore.
Release validation installs the same tools and includes both Rust gates.

The scripts respect the caller's CPU affinity, and setup uses four Cargo jobs.
On a shared machine, prefix each command with `taskset -c 0-3 nice -n 10` for a lane assigned cores 0 through 3.

## Known answers

```bash
cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 4
```

The integration tests run the compiled Rust reader on the 20 bounded cases recorded in `tests/KnownAnswers.lean`.
Those cases come from Core's serialization assertions and a reading of D1 and D21.
They include all three errors, size boundaries and unread trailing bytes.
The second test repeats Core's 52-value power-of-two sweep through `MAX_SIZE`.
The Rust tests compare the value and consumed count, including the resulting remainder position.
These tests do not run Dogecoin Core or validate Charon and Aeneas on arbitrary Rust programs.

## Native oracle adapter

`examples/compactsize_oracle.rs` adapts the public reader to the oracle's JSON Lines interface.
The library has no encoder, so the adapter supports `compactsize.read` and `oracle.version` only.
Other operations return request errors.
The adapter flushes each response before it reads the next line.
Blank lines have no response, and a final line without a newline has a response.

The example uses `serde_json` 1.0.154 under its MIT or Apache-2.0 licence.
Cargo.lock pins this development dependency and its transitive dependencies.
The library itself has no dependencies.
The example does not form part of the extracted model.

Build the adapter and compare it with the oracle and pinned Core harness:

```bash
cargo +nightly-2026-09-17 build --locked --manifest-path Refinement/Rust/Cargo.toml --example compactsize_oracle --jobs 4
python3 -I scripts/compare_core.py --rust-compactsize Refinement/Rust/target/debug/examples/compactsize_oracle .lake/build/bin/dogelib-oracle build/core-harness/core-oracle
```

[BUILDING.md](../../BUILDING.md#comparison-with-dogecoin-core) gives the oracle and Core build commands.
The comparator reads the oracle format at runtime and passes `--oracle-format FORMAT` to the adapter.
Both version interfaces report `FORMAT-rust-compactsize`.
For example, `dogelib-oracle/2` selects `dogelib-oracle/2-rust-compactsize`.
This projection label describes CompactSize reads only.

The three programs agree on 404 reader requests: seven existing fixtures and 397 generated cases at encoding and size boundaries.
These cases include truncation, non-canonical forms, values above MAX_SIZE and trailing bytes.
The comparison checks errors, values, consumed counts and remainders.
It provides evidence about compiled Rust on these inputs, without a proof about the binary or its JSON adapter.
The Core CI job builds the example and runs the comparison.
The ordinary Cargo test command also tests the adapter's request checks and result conversion.
