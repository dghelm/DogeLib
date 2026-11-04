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
The check extracts into a temporary lane directory and compares the full generated directory with the committed files.

CI builds the committed Lean model with the Mathlib cache, without running extraction.

## Known answers

```bash
cargo +nightly-2026-09-17 test --locked --manifest-path Refinement/Rust/Cargo.toml --jobs 8
```

The integration tests run the compiled Rust reader on the 20 bounded cases recorded in `tests/KnownAnswers.lean`.
Those cases come from Core's serialization assertions and a reading of D1 and D21.
They include all three errors, size boundaries and unread trailing bytes.
The second test repeats Core's 52-value power-of-two sweep through `MAX_SIZE`.
The Rust tests compare the value and consumed count, including the resulting remainder position.
These tests do not run Dogecoin Core or validate Charon and Aeneas on arbitrary Rust programs.
