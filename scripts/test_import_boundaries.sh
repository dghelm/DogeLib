#!/usr/bin/env bash
# The import check must pass on the libraries as they are, and fail when a
# module under DogeLib imports DogeLib.Proposals (design record 0007,
# section 12, stage 1). Run from anywhere, after `lake build`.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
mkdir -p .lane
WORK=$(mktemp -d .lane/import-boundaries.XXXXXX)
PLANTED=DogeLib/ImportBoundaryPlanted.lean
OUT=.lake/build/lib/lean/DogeLib/ImportBoundaryPlanted
if [[ -e "$PLANTED" ]]; then
  echo "FAIL: fixture path $PLANTED already exists"; exit 1
fi
trap 'rm -rf "$WORK"; rm -f "$PLANTED" "$OUT".*' EXIT

check() { lake env lean --run scripts/CheckRefinementImports.lean "$@"; }

if check >"$WORK/default" 2>&1; then
  echo "ok:   the default libraries pass"
else
  echo "FAIL: the default libraries do not pass"; cat "$WORK/default"; FAIL=1
fi

# A baseline module with no proposal import passes when it is the only root.
if check DogeLib.Script.Verify >"$WORK/clean" 2>&1; then
  echo "ok:   a baseline module without a proposal import passes"
else
  echo "FAIL: a baseline module without a proposal import does not pass"; cat "$WORK/clean"; FAIL=1
fi

# Plant a baseline module that imports the proposal library.
cat >"$PLANTED" <<'EOF'
module
public import DogeLib.Proposals
EOF
if ! lake env lean -o "$OUT.olean" "$PLANTED" >"$WORK/build" 2>&1; then
  echo "FAIL: the planted module does not compile"; cat "$WORK/build"; exit 1
fi
if check DogeLib.ImportBoundaryPlanted >"$WORK/planted" 2>&1; then
  echo "FAIL: a baseline module that imports DogeLib.Proposals passed"; cat "$WORK/planted"; FAIL=1
elif grep -qx 'forbidden import in a baseline library: DogeLib.Proposals' "$WORK/planted" \
    && grep -qx 'forbidden import in a baseline library: DogeLib.Proposals.Framework.Script' "$WORK/planted"; then
  echo "ok:   a baseline module that imports DogeLib.Proposals fails, and the check names the proposal modules"
else
  echo "FAIL: the planted proposal import was not named"; cat "$WORK/planted"; FAIL=1
fi

exit "$FAIL"
