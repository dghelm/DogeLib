#!/usr/bin/env bash
# Regenerate the Lean model, or compare a fresh extraction with the working-tree model.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
tools_dir="$repo_root/build/tools"
output_dir="$repo_root/Refinement/Refinement/Rust/Generated"
extraction_dir="$repo_root/.lane/extraction"
check=false
while [[ $# -gt 0 ]]; do
  case "$1" in
    --check) check=true; shift ;;
    --tools-dir) tools_dir=$(realpath -m -- "${2:?--tools-dir requires a directory}"); shift 2 ;;
    *) echo "usage: $0 [--check] [--tools-dir DIR]" >&2; exit 2 ;;
  esac
done
if "$check"; then
  mkdir -p "$repo_root/.lane"
  check_dir=$(mktemp -d "$repo_root/.lane/extraction.XXXXXX")
  trap 'rm -rf "$check_dir"' EXIT
  output_dir="$check_dir/generated"
  extraction_dir="$check_dir/llbc"
fi
mkdir -p "$output_dir" "$extraction_dir"
cd "$repo_root/Refinement/Rust"
RUSTUP_TOOLCHAIN=nightly-2026-09-17 "$tools_dir/charon/charon/target/release/charon" cargo --preset=aeneas --dest "$extraction_dir"
"$tools_dir/aeneas-dist/aeneas" -backend lean -namespace DogeLibRust -dest "$output_dir" "$extraction_dir/dogelib_compactsize.llbc"
if "$check"; then
  diff -ru "$repo_root/Refinement/Refinement/Rust/Generated" "$output_dir"
fi
