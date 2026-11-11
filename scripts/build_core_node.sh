#!/usr/bin/env bash
# Build a wallet-free dogecoind from a named Core revision, for the regtest
# replay of design record 0009, section 9.1 (level L3).
#
# Usage: scripts/build_core_node.sh --revision COMMIT <core-git-repo> <build-dir>
#
# The script exports the revision with `git archive`, so the build never
# touches the clone's working tree. It writes <build-dir>/core/src/dogecoind,
# <build-dir>/node.stamp, whose first line names the full commit, and
# <build-dir>/node.revision. The node is reused when node.stamp matches.
#
# scripts/core_boost.sh supplies Boost: an installed one that BOOST_ROOT names,
# or Boost 1.70.0, which it builds into <build-dir>/boost.
#
# Environment: JOBS (default 8, at most 8), CC, CXX, BOOST_ROOT, BOOST_ARCHIVE.
set -euo pipefail

if [ "$#" -ne 4 ] || [ "$1" != --revision ]; then
  echo "usage: $0 --revision COMMIT <core-git-repo> <build-dir>" >&2
  exit 2
fi
repo=$(realpath "$3")
revision=$(git -C "$repo" rev-parse --verify "$2^{commit}")
mkdir -p "$4"
build=$(realpath "$4")
here=$(cd "$(dirname "$0")/.." && pwd)
# shellcheck source=scripts/core_boost.sh
. "$here/scripts/core_boost.sh"
tree=$build/core
jobs=${JOBS:-8}
if [ "$jobs" -gt 8 ]; then jobs=8; fi
cc=${CC:-gcc}
cxx=${CXX:-g++}
configure_options=(--without-gui --disable-wallet --disable-tests --disable-bench --disable-zmq
  --without-miniupnpc --disable-scrypt-sse2 --disable-shared --with-pic)

stamp_text() {
  echo "revision $revision"
  echo "script $(sha256sum "$here/scripts/build_core_node.sh" | cut -d' ' -f1)"
  echo "boost script $(sha256sum "$here/scripts/core_boost.sh" | cut -d' ' -f1)"
  echo "cc $("$cc" --version | head -n1)"
  echo "cxx $("$cxx" --version | head -n1)"
  echo "machine $(uname -m)"
  boost_stamp_line
  echo "configure ${configure_options[*]}"
  echo "cflags -O2"
  echo "cxxflags -O2"
}

if [ -x "$tree/src/dogecoind" ] && [ -f "$build/node.stamp" ] && [ "$(cat "$build/node.stamp")" = "$(stamp_text)" ]; then
  echo "node: reusing $build/node.stamp"
else
  rm -rf "$tree" "$build/node.stamp" "$build/node.revision"
  [ -n "${BOOST_ROOT:-}" ] || build_boost "$build" "$jobs"
  boost=$(boost_root "$build")
  mkdir -p "$tree"
  git -C "$repo" archive "$revision" | tar -x -C "$tree"
  (
    cd "$tree"
    ./autogen.sh
    ./configure "${configure_options[@]}" --with-boost="$boost" --with-boost-libdir="$boost/lib" \
      CC="$cc" CXX="$cxx" CFLAGS=-O2 CXXFLAGS=-O2
    make -C src -j"$jobs" dogecoind
  )
  [ -x "$tree/src/dogecoind" ] || { echo "error: dogecoind is missing after the build" >&2; exit 1; }
  stamp_text > "$build/node.stamp"
fi
printf '%s\n' "$revision" > "$build/node.revision"
echo "built $tree/src/dogecoind at $revision"
