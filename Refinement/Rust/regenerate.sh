#!/usr/bin/env bash
# Regenerate the Lean model, or compare a fresh extraction with the committed file.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
tools_dir="$repo_root/.lane/tools"
output_dir="$repo_root/Refinement/Rust/Generated"
case "${1:-}" in
  '') ;;
  --check) output_dir=$(mktemp -d "$repo_root/.lane/extraction.XXXXXX"); trap 'rm -rf "$output_dir"' EXIT ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac
mkdir -p "$output_dir" "$repo_root/.lane/extraction"
cd "$repo_root/Refinement/Rust"
RUSTUP_TOOLCHAIN=nightly-2026-09-17 taskset -c 0-7 nice -n 10 "$tools_dir/charon/charon/target/release/charon" cargo --preset=aeneas --dest "$repo_root/.lane/extraction"
"$tools_dir/aeneas-dist/aeneas" -backend lean -namespace DogeLibRust -dest "$output_dir" "$repo_root/.lane/extraction/dogelib_compactsize.llbc"
if [[ ${1:-} == --check ]]; then
  diff -ru "$repo_root/Refinement/Rust/Generated" "$output_dir"
fi
