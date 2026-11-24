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

# The pair of Lean issue 16730: a module that stores a changed inductive type, and a module that proves `False` from it.
# A third module stores an inductive type that its own `all` field does not list (Lean issue 16688).
forged=scripts/replay-fixtures/ForgedInductive
mkdir -p "$WORK/forged/ForgedInductive"
for m in ForgedInductive ForgedInductive/Unlisted ForgedInductive/Use; do
  if ! lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$2" -o "$1/$3.olean" "$2/$3.lean"' \
      _ "$WORK/forged" scripts/replay-fixtures "$m" > "$WORK/forged/$(basename "$m").log" 2>&1; then
    echo "FAIL: the fixture $m does not compile"; cat "$WORK/forged/$(basename "$m").log"; exit 1
  fi
done
# The fixture must still be the exploit: Lean accepts the proof of `False` with no axiom.
if grep -q "'boom' does not depend on any axioms" "$WORK/forged/Use.log"; then
  echo "ok:   the planted pair proves False with no axiom when Lean compiles it"
else
  echo "FAIL: the planted pair no longer proves False"; cat "$WORK/forged/Use.log"; FAIL=1
fi
if REPLAY_LEAN_PATH="$WORK/forged" bash scripts/replay.sh "$forged" > "$WORK/forged/replay.log" 2>&1; then
  echo "FAIL: the replay accepted the changed inductive types"; cat "$WORK/forged/replay.log"; FAIL=1
else
  log="$WORK/forged/replay.log"
  if grep -qx 'ForgedInductive failed to replay after [0-9]* s' "$log" \
      && grep -q "in the module ForgedInductive: the stored inductive type 'PB2' differs from the one that the kernel generated, in \[numParams, numIndices\]" "$log"; then
    echo "ok:   a changed numParams of a mutual inductive type fails the replay"
  else
    echo "FAIL: the changed PB2 was not rejected"; cat "$log"; FAIL=1
  fi
  if grep -qx 'ForgedInductive.Unlisted failed to replay after [0-9]* s' "$log" \
      && grep -q "in the module ForgedInductive.Unlisted: 'bad' is stored, but the replayed environment does not contain it" "$log"; then
    echo "ok:   an inductive type that its own all field does not list fails the replay"
  else
    echo "FAIL: the unlisted inductive type was not rejected"; cat "$log"; FAIL=1
  fi
  # The replay trusts the imports, so the importer passes alone. The gate fails through the module it imports.
  if grep -q '^ForgedInductive.Use replayed in' "$log"; then
    echo "ok:   the importer replays alone, so the gate depends on replaying every module"
  else
    echo "FAIL: the importer did not replay"; cat "$log"; FAIL=1
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
