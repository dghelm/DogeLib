#!/usr/bin/env bash
# Build the Dogecoin Core harness, harness/core/core_oracle.cpp, against
# Core's own libraries at the commit that SOURCES.md pins.
#
# Usage: scripts/build_core_harness.sh <core-git-repo> <build-dir>
#
# The script exports the pinned tree with `git archive`, so the build never
# touches the clone's working tree, and the clone may be checked out at any
# commit that contains the pin. It writes <build-dir>/core-oracle and <build-dir>/core-signer.
#
# The Core libraries are reused when <build-dir>/core.stamp matches the pin,
# this script, the compilers and the flags. The harness itself is always
# compiled again.
#
# Environment: JOBS (default 8), CC, CXX.
set -euo pipefail

PIN=e0a1c157791544e818c901bd9341896965afbf9d

if [ "$#" -ne 2 ]; then
  echo "usage: $0 <core-git-repo> <build-dir>" >&2
  exit 2
fi

repo=$1
mkdir -p "$2"
build=$(cd "$2" && pwd)
here=$(cd "$(dirname "$0")/.." && pwd)
jobs=${JOBS:-8}
cc=${CC:-gcc}
cxx=${CXX:-g++}
tree=$build/core
src=$tree/src

# Core's configure adds -std=c++11 to CXX. The harness is compiled the same way.
core_cxxflags="-O2 -ffunction-sections -fdata-sections"
core_cflags="-O2"

stamp_text() {
  echo "pin $PIN"
  echo "script $(sha256sum "$here/scripts/build_core_harness.sh" | cut -d' ' -f1)"
  echo "cc $("$cc" --version | head -n1)"
  echo "cxx $("$cxx" --version | head -n1)"
  echo "machine $(uname -m)"
  echo "cflags $core_cflags"
  echo "cxxflags $core_cxxflags"
}

libs=(
  "$build/pow.o"
  "$build/chain.o"
  "$build/dogecoin.o"
  "$build/chainparams.o"
  "$build/chainparamsbase.o"
  "$src/libdogecoin_consensus.a"
  "$src/crypto/libdogecoin_crypto.a"
  "$src/secp256k1/.libs/libsecp256k1.a"
)

libs_present() {
  local f
  for f in "${libs[@]}"; do
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

  # No daemon, utilities, GUI, tests or benchmarks: configure then needs no
  # Boost (configure.ac line 683) and builds no UniValue (line 939).
  (
    cd "$tree"
    ./autogen.sh
    ./configure --with-libs --without-daemon --without-utils --without-gui \
      --disable-wallet --disable-tests --disable-bench --disable-zmq \
      --without-miniupnpc --disable-shared --with-pic \
      CC="$cc" CXX="$cxx" CFLAGS="$core_cflags" CXXFLAGS="$core_cxxflags"
    make -C src -j"$jobs" libdogecoin_consensus.a crypto/libdogecoin_crypto.a \
      secp256k1/libsecp256k1.la
  )
  # Compile work and parameter objects without the rest of the server.
  # The linker discards unrelated functions and their server dependencies.
  # chainparams.cpp and dogecoin.cpp require Boost headers, not Boost libraries.
  for unit in pow chain dogecoin chainparams chainparamsbase; do
    "$cxx" -std=c++11 $core_cxxflags -DHAVE_CONFIG_H \
      -I"$src" -I"$src/config" -I"$src/univalue/include" \
      -c "$src/$unit.cpp" -o "$build/$unit.o"
  done
  libs_present || { echo "error: a Core library is missing after the build" >&2; exit 1; }
  stamp_text > "$build/core.stamp"
fi

# UniValue parses the requests. Compile every library source that the pinned
# sources.mk lists.
univalue_sources=$(sed -n 's|^UNIVALUE_LIB_SOURCES_INT += %reldir%/\(.*\.cpp\)$|\1|p' "$src/univalue/sources.mk")
if [ -z "$univalue_sources" ]; then
  echo "error: no UniValue sources in $src/univalue/sources.mk" >&2
  exit 1
fi
univalue_paths=()
for f in $univalue_sources; do
  univalue_paths+=("$src/univalue/$f")
done

# support/cleanse.cpp defines memory_cleanse, which CDataStream's allocator
# calls. It belongs to libdogecoin_util, which this build does not make.
set -x
"$cxx" -std=c++11 $core_cxxflags -Wl,--gc-sections -DHAVE_CONFIG_H \
  -I"$src" -I"$src/config" -I"$src/univalue/include" -I"$src/secp256k1/include" \
  -o "$build/core-oracle" \
  "$here/harness/core/core_oracle.cpp" "$src/support/cleanse.cpp" "${univalue_paths[@]}" \
  "${libs[@]}" -lcrypto
set +x
echo "built $build/core-oracle against:"
cat "$build/core.stamp"

# The fixture signer uses Core's key and randomness code, plus its secure pool.
"$cxx" -std=c++11 $core_cxxflags -Wl,--gc-sections -DHAVE_CONFIG_H \
  -I"$src" -I"$src/config" -I"$src/univalue/include" -I"$src/secp256k1/include" \
  "-DCORE_SIGNER_BLOB=\"$(git hash-object "$here/harness/core/core_signer.cpp")\"" \
  -o "$build/core-signer" \
  "$here/harness/core/core_signer.cpp" "$src/key.cpp" "$src/random.cpp" \
  "$src/support/lockedpool.cpp" "$src/support/cleanse.cpp" "${univalue_paths[@]}" \
  "${libs[@]}" -lcrypto -pthread
echo "built $build/core-signer"
