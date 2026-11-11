#!/usr/bin/env bash
# Build the Dogecoin Core harness, harness/core/core_oracle.cpp, against
# Core's own libraries at the commit that SOURCES.md pins. The harness links
# Core's server library, and harness/core/core_validation.cpp includes Core's
# src/validation.cpp and src/timedata.cpp as text.
#
# Usage: scripts/build_core_harness.sh [--revision COMMIT] <core-git-repo> <build-dir>
#
# --revision builds against another Core commit for a labelled replay
# (design record 0009, section 9.2). It needs a build directory other than
# build/core-harness. The first line of core.stamp is then
# `revision <commit>` instead of `pin <commit>`, <build-dir>/core.revision
# holds the commit, and both programs report it as `core_revision` in their
# --version output. Without --revision the build and
# its output are unchanged. The option never changes the pin.
#
# The script exports the pinned tree with `git archive`, so the build never
# touches the clone's working tree, and the clone may be checked out at any
# commit that contains the pin. It writes <build-dir>/core-oracle and <build-dir>/core-signer.
#
# The Core libraries are reused when <build-dir>/core.stamp matches the pin,
# this script, the compilers and the flags. The harness itself is always
# compiled again.
#
# The build needs the development files of OpenSSL and libevent.
# scripts/core_boost.sh supplies Boost: an installed one that BOOST_ROOT names,
# or Boost 1.70.0, which it builds into <build-dir>/boost.
#
# Environment: JOBS (default 8), CC, CXX, BOOST_ROOT, BOOST_ARCHIVE.
set -euo pipefail

PIN=e0a1c157791544e818c901bd9341896965afbf9d
revision=
if [ "${1:-}" = --revision ]; then
  [ "$#" -eq 4 ] || { echo "usage: $0 [--revision COMMIT] <core-git-repo> <build-dir>" >&2; exit 2; }
  revision=$2
  shift 2
fi

if [ "$#" -ne 2 ]; then
  echo "usage: $0 [--revision COMMIT] <core-git-repo> <build-dir>" >&2
  exit 2
fi

repo=$1
revision_flags=()
if [ -n "$revision" ]; then
  PIN=$(git -C "$repo" rev-parse --verify "$revision^{commit}")
  # An explicit replay build cannot reuse the default CI directory.
  case "$(realpath -m "$2")" in
    "$(realpath -m "$(dirname "$0")/../build/core-harness")")
      echo "error: use a separate directory for --revision" >&2; exit 2 ;;
  esac
  revision_flags=("-DCORE_BUILD_REVISION=\"$PIN\"")
fi
mkdir -p "$2"
build=$(cd "$2" && pwd)
here=$(cd "$(dirname "$0")/.." && pwd)
# shellcheck source=scripts/core_boost.sh
. "$here/scripts/core_boost.sh"
jobs=${JOBS:-8}
cc=${CC:-gcc}
cxx=${CXX:-g++}
tree=$build/core
src=$tree/src

# Core's configure adds -std=c++11 to CXX. The harness is compiled the same way.
core_cxxflags="-O2 -ffunction-sections -fdata-sections"
core_cflags="-O2"
# The options of scripts/build_core_node.sh. The daemon stays enabled, so that
# configure sets up libdogecoin_server.a, but the build never links dogecoind.
configure_options=(--without-gui --disable-wallet --disable-tests --disable-bench --disable-zmq
  --without-miniupnpc --disable-scrypt-sse2 --disable-shared --with-pic)

stamp_text() {
  if [ -n "$revision" ]; then echo "revision $PIN"; else echo "pin $PIN"; fi
  echo "script $(sha256sum "$here/scripts/build_core_harness.sh" | cut -d' ' -f1)"
  echo "boost script $(sha256sum "$here/scripts/core_boost.sh" | cut -d' ' -f1)"
  echo "cc $("$cc" --version | head -n1)"
  echo "cxx $("$cxx" --version | head -n1)"
  echo "machine $(uname -m)"
  echo "scrypt generic (--disable-scrypt-sse2)"
  boost_stamp_line
  echo "configure ${configure_options[*]}"
  echo "cflags $core_cflags"
  echo "cxxflags $core_cxxflags"
}

# The signer links these objects and libraries, as it did before the harness
# linked the server library.
signer_libs=(
  "$build/checkpoints.o"
  "$build/auxpow.o"
  "$build/pow.o"
  "$build/chain.o"
  "$build/dogecoin.o"
  "$build/chainparams.o"
  "$build/chainparamsbase.o"
  "$src/libdogecoin_consensus.a"
  "$src/crypto/libdogecoin_crypto.a"
  "$src/secp256k1/.libs/libsecp256k1.a"
)

# The harness links what dogecoind links (src/Makefile.am, dogecoind_LDADD),
# in that order.
oracle_libs=(
  "$src/libdogecoin_server.a"
  "$src/libdogecoin_common.a"
  "$src/univalue/.libs/libunivalue.a"
  "$src/libdogecoin_util.a"
  "$src/libdogecoin_consensus.a"
  "$src/crypto/libdogecoin_crypto.a"
  "$src/leveldb/libleveldb.a"
  "$src/leveldb/libmemenv.a"
  "$src/secp256k1/.libs/libsecp256k1.a"
)

libs_present() {
  local f
  for f in "${signer_libs[@]}" "${oracle_libs[@]}"; do
    [ -f "$f" ] || return 1
  done
}

if [ -f "$build/core.stamp" ] && [ "$(cat "$build/core.stamp")" = "$(stamp_text)" ] && libs_present; then
  echo "core libraries: reusing $build/core.stamp"
else
  if ! git -C "$repo" cat-file -e "$PIN^{commit}" 2>/dev/null; then
    echo "error: $repo does not contain commit $PIN" >&2
    exit 1
  fi
  rm -rf "$tree" "$build/core.stamp"
  mkdir -p "$tree"
  git -C "$repo" archive "$PIN" | tar -x -C "$tree"

  [ -n "${BOOST_ROOT:-}" ] || build_boost "$build" "$jobs"
  boost=$(boost_root "$build")
  (
    cd "$tree"
    ./autogen.sh
    ./configure "${configure_options[@]}" --with-boost="$boost" --with-boost-libdir="$boost/lib" \
      CC="$cc" CXX="$cxx" CFLAGS="$core_cflags" CXXFLAGS="$core_cxxflags"
    make -C src -j"$jobs" libdogecoin_server.a libdogecoin_common.a libdogecoin_util.a \
      libdogecoin_consensus.a crypto/libdogecoin_crypto.a univalue/libunivalue.la \
      leveldb/libleveldb.a leveldb/libmemenv.a secp256k1/libsecp256k1.la
    # The harness needs the archives, the headers and two source files. The
    # objects would only enlarge a cached build directory.
    find src -name '*.o' -delete
  )
  # The signer gets work and parameter objects without the rest of the server.
  # The linker discards unrelated functions and their server dependencies.
  for unit in checkpoints auxpow pow chain dogecoin chainparams chainparamsbase; do
    "$cxx" -std=c++11 $core_cxxflags -DHAVE_CONFIG_H \
      -I"$src" -I"$src/config" -I"$src/univalue/include" -isystem "$boost/include" \
      -c "$src/$unit.cpp" -o "$build/$unit.o"
  done
  libs_present || { echo "error: a Core library is missing after the build" >&2; exit 1; }
  stamp_text > "$build/core.stamp"
fi

boost=$(boost_root "$build")

# The harness. core_validation.cpp is the unit that includes validation.cpp.
set -x
"$cxx" -std=c++11 $core_cxxflags -DHAVE_CONFIG_H \
  -I"$src" -I"$src/config" -I"$src/univalue/include" -I"$src/secp256k1/include" \
  -I"$src/leveldb/include" -isystem "$boost/include" \
  -o "$build/core-oracle" \
  "${revision_flags[@]}" "$here/harness/core/core_oracle.cpp" "$here/harness/core/core_validation.cpp" \
  "${oracle_libs[@]}" \
  -L"$boost/lib" -lboost_system -lboost_filesystem -lboost_program_options -lboost_thread -lboost_chrono \
  -lssl -lcrypto -levent_pthreads -levent -pthread
set +x
echo "built $build/core-oracle against:"
cat "$build/core.stamp"

# UniValue parses the signer's requests. Compile every library source that the
# pinned sources.mk lists.
univalue_sources=$(sed -n 's|^UNIVALUE_LIB_SOURCES_INT += %reldir%/\(.*\.cpp\)$|\1|p' "$src/univalue/sources.mk")
if [ -z "$univalue_sources" ]; then
  echo "error: no UniValue sources in $src/univalue/sources.mk" >&2
  exit 1
fi
univalue_paths=()
for f in $univalue_sources; do
  univalue_paths+=("$src/univalue/$f")
done

# The fixture signer uses Core's key and randomness code, plus its secure pool.
"$cxx" -std=c++11 $core_cxxflags -Wl,--gc-sections -DHAVE_CONFIG_H \
  -I"$src" -I"$src/config" -I"$src/univalue/include" -I"$src/secp256k1/include" \
  "-DCORE_SIGNER_BLOB=\"$(git hash-object "$here/harness/core/core_signer.cpp")\"" \
  "-DCORE_SIGNER_REQUEST_BLOB=\"$(git hash-object "$here/harness/core/core_signer_main.cpp")\"" \
  -o "$build/core-signer" \
  "${revision_flags[@]}" "$here/harness/core/core_signer_main.cpp" "$src/key.cpp" "$src/random.cpp" \
  "$src/support/lockedpool.cpp" "$src/support/cleanse.cpp" "${univalue_paths[@]}" \
  "${signer_libs[@]}" -lcrypto -pthread
echo "built $build/core-signer"

# Explicit replay builds label their binaries without changing default output.
# A pin build removes the label of an earlier revision build in the same directory.
if [ -n "$revision" ]; then
  printf "%s\n" "$PIN" > "$build/core.revision"
else
  rm -f "$build/core.revision"
fi
