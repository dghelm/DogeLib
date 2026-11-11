# Shared by scripts/build_core_harness.sh and scripts/build_core_node.sh, which
# source this file. It is not a program.
#
# Pinned Core needs the Boost libraries system, filesystem, program_options,
# thread and chrono. Boost 1.69 and later no longer require a boost_system
# library, and recent distributions omit it, so configure fails on them.
# BOOST_ROOT selects an installed Boost with these libraries. Without it,
# build_boost builds Boost 1.70.0 into <build-dir>/boost from BOOST_ARCHIVE, or
# from a download, and checks the archive's SHA-256 first. It deletes a
# downloaded archive after the build. Boost 1.70.0 compares
# PTHREAD_STACK_MIN in a preprocessor condition, which glibc 2.34 and later
# reject, so build_boost applies the replacement that Boost 1.78.0 ships in
# boost/thread/pthread/thread_data.hpp, line 60.

BOOST_VERSION=1.70.0
BOOST_SHA256=430ae8354789de4fd19ee52f3b1f739e1fba576f0aded0897c3c2bc00fb38778
BOOST_URL=https://archives.boost.io/release/1.70.0/source/boost_1_70_0.tar.bz2

# boost_root <build-dir>: the Boost prefix that the build uses.
boost_root() {
  if [ -n "${BOOST_ROOT:-}" ]; then
    echo "$BOOST_ROOT"
  else
    echo "$1/boost"
  fi
}

# boost_stamp_line: the line that a build stamp records for Boost.
boost_stamp_line() {
  if [ -n "${BOOST_ROOT:-}" ]; then
    echo "boost $BOOST_ROOT"
  else
    echo "boost $BOOST_VERSION sha256 $BOOST_SHA256, PTHREAD_STACK_MIN condition from 1.78.0"
  fi
}

# build_boost <build-dir> <jobs>: build Boost into <build-dir>/boost, unless
# its stamp shows that the same version is already there.
build_boost() {
  local build=$1 jobs=$2
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
  [ -n "${BOOST_ARCHIVE:-}" ] || rm -f "$archive"
}
