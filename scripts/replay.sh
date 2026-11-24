#!/usr/bin/env bash
# Replay every declaration of DogeLib into Lean's kernel with the replay function of leanchecker.
# Adapted from EthLib, scripts/replay.sh at commit b4070a856 (CC0 1.0).
# The changes are the library name, this note, the comments on Mathlib and on the crash of Lean v4.36.0,
# the argument LIBRARY, and the module inventory, which replays every module without a source filter.
#
# Usage: scripts/replay.sh [LIBRARY]
# LIBRARY is the directory of a library, `DogeLib` by default.
# The modules are its root file LIBRARY.lean and every `.lean` file under LIBRARY/.
# Run it after `lake build`, which writes the `.olean` files that it reads.
# `scripts/test_replay.sh` runs it on a small planted library, with `REPLAY_LEAN_PATH` for its `.olean` files.
#
# The replay reads the private part of each module, so it checks proof bodies again.
# It finds a declaration that a metaprogram added without the kernel check.
# It uses the same kernel as Lean, so it does not check the kernel itself.
#
# leanchecker replays every module whose name starts with its argument, in one process.
# So `scripts/ReplayModule.lean` calls its replay on one module alone, and each module has its own process.
# Each replay loads all imports of its module and keeps that memory until it exits.
# The script runs `REPLAY_JOBS` replays at a time.
set -euo pipefail
cd "$(dirname "$0")/.."
repo="$PWD"

library="${1:-DogeLib}"
library="${library%/}"
if [ ! -d "$library" ] || [ ! -f "$library.lean" ]; then
  echo "the library $library needs the directory $library and the root file $library.lean" >&2
  exit 2
fi
extra_path="${REPLAY_LEAN_PATH:-}"

# First, the replay must reject a theorem that the kernel never checked.
fixture_dir="$(mktemp -d)"
trap 'rm -rf "$fixture_dir"' EXIT
lake env lean -o "$fixture_dir/ReplayFixture.olean" scripts/ReplayFixture.lean
if lake env bash -c \
    'LEAN_PATH="$1:$LEAN_PATH" REPLAY_MODULE=ReplayFixture lean "$2"' \
    _ "$fixture_dir" "$repo/scripts/ReplayModule.lean" > "$fixture_dir/fixture.log" 2>&1; then
  cat "$fixture_dir/fixture.log"
  echo "the replay accepted a theorem that the kernel never checked" >&2
  exit 1
fi
# A failure for another reason, such as a missing LeanChecker module, must not pass for a rejection.
expected="while replaying declaration 'ReplayFixture.unchecked'"
if ! grep -q "$expected" "$fixture_dir/fixture.log"; then
  cat "$fixture_dir/fixture.log"
  echo "the replay failed on the fixture for another reason" >&2
  exit 1
fi
echo "the replay rejects the unchecked fixture theorem"

# Every module is replayed: the root and each file under the library directory.
# The source text does not decide which modules to skip, because a file can declare something in a form that a pattern misses.
# A module that only imports replays quickly, because it has no constants of its own.
jobs="${REPLAY_JOBS:-2}"
targets="$(mktemp)"
trap 'rm -rf "$fixture_dir" "$targets"' EXIT
base="$(dirname "$library")"
name="$(basename "$library")"
{
  echo "$name"
  (cd "$base" && find "$name" -name '*.lean' -print | sed 's/\.lean$//; s#/#.#g')
} | LC_ALL=C sort > "$targets"
echo "replaying $(wc -l < "$targets") modules of $name, $jobs at a time"
start=$SECONDS
# A proof can make the kernel evaluate a large computation that the build did not evaluate.
# Its replay can then run for hours and fill the memory of the runner.
# So each module has a time budget, and a module that exceeds it fails the replay by name.
budget="${REPLAY_BUDGET:-300}"
# `xargs` runs every module and fails if one fails.
# The kernel names the declaration that it rejects.
# A module without an `.olean` file fails too, because the replay cannot read it.
LEAN_NUM_THREADS=1 lake env bash -c '
  [ -n "$1" ] && export LEAN_PATH="$1:$LEAN_PATH"
  shift
  exec xargs -P "$@"' _ "$extra_path" "$jobs" -n 1 bash -c '
  begin=$SECONDS
  status=0
  REPLAY_MODULE="$3" timeout "$1" lean "$2" || status=$?
  if [ "$status" -eq 0 ]; then
    echo "$3 replayed in $((SECONDS - begin)) s"
  elif [ "$status" -eq 124 ]; then
    echo "$3 did not replay within the budget of $1 s" >&2
  else
    echo "$3 failed to replay after $((SECONDS - begin)) s" >&2
  fi
  exit "$((status != 0))"' _ "$budget" "$repo/scripts/ReplayModule.lean" < "$targets"
echo "replayed in $((SECONDS - start)) s"
