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
# Pinned Core needs the Boost libraries system, filesystem, program_options,
# thread and chrono. Boost 1.69 and later no longer require a boost_system
# library, and recent distributions omit it, so configure fails on them.
# BOOST_ROOT selects an installed Boost with these libraries. Without it, the
# script builds Boost 1.70.0 into <build-dir>/boost from BOOST_ARCHIVE, or from
# a download, and checks the archive's SHA-256 first. Boost 1.70.0 compares
# PTHREAD_STACK_MIN in a preprocessor condition, which glibc 2.34 and later
# reject, so the script applies the replacement that Boost 1.78.0 ships in
# boost/thread/pthread/thread_data.hpp, line 60.
#
# Environment: JOBS (default 8, at most 8), CC, CXX, BOOST_ROOT, BOOST_ARCHIVE.
set -euo pipefail

BOOST_VERSION=1.70.0
BOOST_SHA256=430ae8354789de4fd19ee52f3b1f739e1fba576f0aded0897c3c2bc00fb38778
BOOST_URL=https://archives.boost.io/release/1.70.0/source/boost_1_70_0.tar.bz2

if [ "$#" -ne 4 ] || [ "$1" != --revision ]; then
  echo "usage: $0 --revision COMMIT <core-git-repo> <build-dir>" >&2
  exit 2
fi
repo=$(realpath "$3")
revision=$(git -C "$repo" rev-parse --verify "$2^{commit}")
mkdir -p "$4"
build=$(realpath "$4")
here=$(cd "$(dirname "$0")/.." && pwd)
tree=$build/core
jobs=${JOBS:-8}
if [ "$jobs" -gt 8 ]; then jobs=8; fi
cc=${CC:-gcc}
cxx=${CXX:-g++}
configure_options=(--without-gui --disable-wallet --disable-tests --disable-bench --disable-zmq
  --without-miniupnpc --disable-scrypt-sse2 --disable-shared --with-pic)

boost_root() {
  if [ -n "${BOOST_ROOT:-}" ]; then
    echo "$BOOST_ROOT"
  else
    echo "$build/boost"
  fi
}

stamp_text() {
  echo "revision $revision"
  echo "script $(sha256sum "$here/scripts/build_core_node.sh" | cut -d' ' -f1)"
  echo "cc $("$cc" --version | head -n1)"
  echo "cxx $("$cxx" --version | head -n1)"
  echo "machine $(uname -m)"
  if [ -n "${BOOST_ROOT:-}" ]; then
    echo "boost $BOOST_ROOT"
  else
    echo "boost $BOOST_VERSION sha256 $BOOST_SHA256, PTHREAD_STACK_MIN condition from 1.78.0"
  fi
  echo "configure ${configure_options[*]}"
  echo "cflags -O2"
  echo "cxxflags -O2"
}

build_boost() {
  local prefix=$build/boost source=$build/boost-source archive=${BOOST_ARCHIVE:-$build/boost_1_70_0.tar.bz2}
  if [ -f "$prefix/boost.stamp" ] && [ "$(cat "$prefix/boost.stamp")" = "$BOOST_VERSION $BOOST_SHA256" ]; then
    echo "boost: reusing $prefix"
    return
  fi
  if [ ! -f "$archive" ]; then
    curl -fsSL -o "$archive" "$BOOST_URL"
  fi
  echo "$BOOST_SHA256  $archive" | sha256sum -c -
  rm -rf "$source" "$prefix"
  mkdir -p "$source"
  tar -xjf "$archive" -C "$source" --strip-components=1
  sed -i 's/^#if PTHREAD_STACK_MIN > 0$/#ifdef PTHREAD_STACK_MIN/' \
    "$source/boost/thread/pthread/thread_data.hpp"
  grep -q '^#ifdef PTHREAD_STACK_MIN$' "$source/boost/thread/pthread/thread_data.hpp" || {
    echo "error: the Boost thread header did not change as expected" >&2; exit 1; }
  (
    cd "$source"
    ./bootstrap.sh --with-libraries=chrono,filesystem,program_options,system,thread
    ./b2 -j"$jobs" -d0 cxxflags=-std=c++11 link=static threading=multi variant=release \
      --prefix="$prefix" install
  )
  echo "$BOOST_VERSION $BOOST_SHA256" > "$prefix/boost.stamp"
  rm -rf "$source"
}

if [ -x "$tree/src/dogecoind" ] && [ -f "$build/node.stamp" ] && [ "$(cat "$build/node.stamp")" = "$(stamp_text)" ]; then
  echo "node: reusing $build/node.stamp"
else
  rm -rf "$tree" "$build/node.stamp" "$build/node.revision"
  [ -n "${BOOST_ROOT:-}" ] || build_boost
  boost=$(boost_root)
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
