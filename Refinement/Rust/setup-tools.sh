#!/usr/bin/env bash
# Install the pinned extraction tools without system packages.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
tools_dir="$repo_root/build/tools"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tools-dir) tools_dir=$(realpath -m -- "${2:?--tools-dir requires a directory}"); shift 2 ;;
    *) echo "usage: $0 [--tools-dir DIR]" >&2; exit 2 ;;
  esac
done
aeneas_pin=d1e177bb9fdc17fa62e730d524ac905ba19776ed
charon_pin=a58d159210b3a36fedeaba4437bda896a8b12f0d
aeneas_tag=nightly-2026.11.04-d1e177b
if [[ $(uname -sm) != "Linux x86_64" ]]; then
  echo "This setup script requires Linux x86_64." >&2
  exit 1
fi
mkdir -p "$tools_dir"
if [[ ! -d "$tools_dir/aeneas/.git" ]]; then
  git clone https://github.com/AeneasVerif/aeneas.git "$tools_dir/aeneas" --depth 1 --branch "$aeneas_tag"
fi
test "$(git -C "$tools_dir/aeneas" rev-parse HEAD)" = "$aeneas_pin"
if [[ ! -f "$tools_dir/aeneas-linux-x86_64.tar.gz" ]]; then
  gh release download "$aeneas_tag" --repo AeneasVerif/aeneas --pattern aeneas-linux-x86_64.tar.gz --dir "$tools_dir"
fi
echo "955928facac9853047edee5c68dd35bb40840955e1a5ddda66668dcb3198d72e  $tools_dir/aeneas-linux-x86_64.tar.gz" | sha256sum --check
mkdir -p "$tools_dir/aeneas-dist"
tar -xzf "$tools_dir/aeneas-linux-x86_64.tar.gz" -C "$tools_dir/aeneas-dist"
aeneas_version=$("$tools_dir/aeneas-dist/aeneas" -version)
echo "$aeneas_version"
test "$aeneas_version" = "aeneas $aeneas_tag"
if [[ ! -d "$tools_dir/charon/.git" ]]; then
  git init "$tools_dir/charon"
  git -C "$tools_dir/charon" remote add origin https://github.com/AeneasVerif/charon.git
  git -C "$tools_dir/charon" fetch --depth 1 origin "$charon_pin"
  git -C "$tools_dir/charon" checkout --detach FETCH_HEAD
fi
test "$(git -C "$tools_dir/charon" rev-parse HEAD)" = "$charon_pin"
cd "$repo_root"
rustup toolchain install nightly-2026-09-17 --profile minimal --component rustc-dev --component llvm-tools-preview --component rust-src
cd "$tools_dir/charon/charon"
RUSTUP_TOOLCHAIN=nightly-2026-09-17 cargo build --release --locked --jobs 4 --no-default-features --features rustc --bin charon --bin charon-driver
charon_version=$(./target/release/charon version)
echo "$charon_version"
test "$charon_version" = "0.1.308 ($charon_pin)"
