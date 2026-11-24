#!/usr/bin/env bash
# The kernel replay must select every module of a library and fail on each one that the kernel rejects.
# The test builds small libraries in a temporary directory and runs scripts/replay.sh on them.
# Run it from anywhere. It needs no build of DogeLib.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# An unchecked theorem, with type `False` and proof `True.intro`, as in scripts/ReplayFixture.lean.
unchecked() {
  printf '%s\n' \
    "set_option debug.skipKernelTC true in" \
    "run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl <| .thmDecl {" \
    "  name := \`$1, levelParams := [], type := Lean.mkConst \`\`False, value := Lean.mkConst \`\`True.intro }"
}

# Write a library at $1 with the name $2: a root, a parent module and its leaf.
# With $3 = bad, the root and the parent each declare an unchecked theorem.
# The parent declares it on the line of `namespace`, which a filter of source lines can miss.
library() {
  local dir=$1 name=$2 kind=$3
  mkdir -p "$dir/src/$name/Parent" "$dir/out/$name/Parent"
  { echo "import Lean"
    if [ "$kind" = bad ]; then unchecked "$name.unchecked"
    else echo "theorem $name.checked : True := trivial"; fi
  } > "$dir/src/$name.lean"
  { echo "import Lean"
    if [ "$kind" = bad ]; then printf 'namespace Plant '; unchecked "Plant.unchecked"
    else echo "namespace Plant theorem checked : True := trivial"; fi
    echo "end Plant"
  } > "$dir/src/$name/Parent.lean"
  echo "theorem $name.Parent.Leaf.checked : True := trivial" > "$dir/src/$name/Parent/Leaf.lean"
  for m in "$name" "$name/Parent" "$name/Parent/Leaf"; do
    if ! lake env lean --root="$dir/src" -o "$dir/out/$m.olean" "$dir/src/$m.lean" > "$dir/build.log" 2>&1; then
      echo "FAIL: the fixture $m does not compile"; cat "$dir/build.log"; exit 1
    fi
  done
}

replay() { REPLAY_LEAN_PATH="$1/out" bash scripts/replay.sh "$1/src/$2" > "$1/replay.log" 2>&1; }

library "$WORK/good" ReplayGood good
if replay "$WORK/good" ReplayGood \
    && grep -qx 'replaying 3 modules of ReplayGood, 2 at a time' "$WORK/good/replay.log" \
    && grep -q '^ReplayGood replayed in' "$WORK/good/replay.log" \
    && grep -q '^ReplayGood.Parent replayed in' "$WORK/good/replay.log" \
    && grep -q '^ReplayGood.Parent.Leaf replayed in' "$WORK/good/replay.log"; then
  echo "ok:   a library without an unchecked declaration replays, root and parent included"
else
  echo "FAIL: the checked library did not replay all three modules"; cat "$WORK/good/replay.log"; FAIL=1
fi

library "$WORK/bad" ReplayBad bad
if replay "$WORK/bad" ReplayBad; then
  echo "FAIL: the replay accepted the planted library"; cat "$WORK/bad/replay.log"; FAIL=1
else
  log="$WORK/bad/replay.log"
  if grep -qx 'ReplayBad failed to replay after [0-9]* s' "$log" \
      && grep -q "while replaying declaration 'ReplayBad.unchecked'" "$log"; then
    echo "ok:   an unchecked theorem in the library root fails the replay"
  else
    echo "FAIL: the root was not rejected"; cat "$log"; FAIL=1
  fi
  if grep -qx 'ReplayBad.Parent failed to replay after [0-9]* s' "$log" \
      && grep -q "while replaying declaration 'Plant.unchecked'" "$log"; then
    echo "ok:   an unchecked theorem on a namespace line of a parent module fails the replay"
  else
    echo "FAIL: the parent module was not rejected"; cat "$log"; FAIL=1
  fi
fi

# A source file without an `.olean` file must fail, not be skipped.
rm "$WORK/good/out/ReplayGood/Parent/Leaf.olean"
if replay "$WORK/good" ReplayGood; then
  echo "FAIL: a module without an .olean file passed"; cat "$WORK/good/replay.log"; FAIL=1
elif grep -qx 'ReplayGood.Parent.Leaf failed to replay after [0-9]* s' "$WORK/good/replay.log"; then
  echo "ok:   a module without an .olean file fails the replay by name"
else
  echo "FAIL: the module without an .olean file was not named"; cat "$WORK/good/replay.log"; FAIL=1
fi

exit "$FAIL"
