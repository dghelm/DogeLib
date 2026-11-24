#!/usr/bin/env bash
# The import check must pass on the libraries as they are, and fail when a
# module under DogeLib imports DogeLib.Proposals (design record 0007,
# section 12, stage 1), or the proposal exports (design record 0011,
# stage 6, condition 3), or when it imports a proof module (ARCHITECTURE.md).
# A module under DogeLib.Proposals fails when it imports the test-only
# library ProposalExamples.
# Run from anywhere, after `lake build`.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
mkdir -p .lane
WORK=$(mktemp -d .lane/import-boundaries.XXXXXX)
PLANTED=DogeLib/ImportBoundaryPlanted.lean
OUT=.lake/build/lib/lean/DogeLib/ImportBoundaryPlanted
PLANTED_PROPOSAL=DogeLib/Proposals/ImportBoundaryPlanted.lean
OUT_PROPOSAL=.lake/build/lib/lean/DogeLib/Proposals/ImportBoundaryPlanted
for path in "$PLANTED" "$PLANTED_PROPOSAL"; do
  if [[ -e "$path" ]]; then
    echo "FAIL: fixture path $path already exists"; exit 1
  fi
done
trap 'rm -rf "$WORK"; rm -f "$PLANTED" "$OUT".* "$PLANTED_PROPOSAL" "$OUT_PROPOSAL".*' EXIT

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

# The same for the proposal exports, which design record 0011, decision 10, adds.
cat >"$PLANTED" <<'EOF'
module
public import DogeLib.Proposals.Exports
EOF
if ! lake env lean -o "$OUT.olean" "$PLANTED" >"$WORK/build-exports" 2>&1; then
  echo "FAIL: the planted module with the proposal exports does not compile"; cat "$WORK/build-exports"; exit 1
fi
if check DogeLib.ImportBoundaryPlanted >"$WORK/planted-exports" 2>&1; then
  echo "FAIL: a baseline module that imports DogeLib.Proposals.Exports passed"; cat "$WORK/planted-exports"; FAIL=1
elif grep -qx 'forbidden import in a baseline library: DogeLib.Proposals.Exports' "$WORK/planted-exports" \
    && grep -qx 'forbidden import in a baseline library: DogeLib.Proposals.Framework.Block' "$WORK/planted-exports"; then
  echo "ok:   a baseline module that imports DogeLib.Proposals.Exports fails, and the check names the proposal modules"
else
  echo "FAIL: the planted import of the proposal exports was not named"; cat "$WORK/planted-exports"; FAIL=1
fi

# A specification module that imports a proof module (ARCHITECTURE.md).
cat >"$PLANTED" <<'EOF'
module
public import DogeLib.Block.Proofs.ConnectProperties
EOF
if ! lake env lean -o "$OUT.olean" "$PLANTED" >"$WORK/build-proofs" 2>&1; then
  echo "FAIL: the planted module with a proof import does not compile"; cat "$WORK/build-proofs"; exit 1
fi
if check DogeLib.ImportBoundaryPlanted >"$WORK/planted-proofs" 2>&1; then
  echo "FAIL: a specification module that imports a proof module passed"; cat "$WORK/planted-proofs"; FAIL=1
elif grep -qx 'forbidden proof import in the specification or an export library: DogeLib.Block.Proofs.ConnectProperties' "$WORK/planted-proofs" \
    && grep -qx 'forbidden proof import in the specification or an export library: DogeLib.Block.Proofs.Connect' "$WORK/planted-proofs"; then
  echo "ok:   a specification module that imports a proof module fails, and the check names the proof modules"
else
  echo "FAIL: the planted proof import was not named"; cat "$WORK/planted-proofs"; FAIL=1
fi

# A proposal module that imports the test-only examples.
cat >"$PLANTED_PROPOSAL" <<'EOF'
module
public import ProposalExamples
EOF
if ! lake env lean -o "$OUT_PROPOSAL.olean" "$PLANTED_PROPOSAL" >"$WORK/build-examples" 2>&1; then
  echo "FAIL: the planted proposal module with the examples does not compile"; cat "$WORK/build-examples"; exit 1
fi
if check DogeLib.Proposals.ImportBoundaryPlanted >"$WORK/planted-examples" 2>&1; then
  echo "FAIL: a proposal module that imports ProposalExamples passed"; cat "$WORK/planted-examples"; FAIL=1
elif grep -qx 'forbidden test import in a proposal library: ProposalExamples' "$WORK/planted-examples" \
    && grep -qx 'forbidden test import in a proposal library: ProposalExamples.ExampleFaultyLocktime' "$WORK/planted-examples" \
    && ! grep -q 'forbidden import in a baseline library' "$WORK/planted-examples"; then
  echo "ok:   a proposal module that imports ProposalExamples fails, and the check names the example modules"
else
  echo "FAIL: the planted import of the examples was not named"; cat "$WORK/planted-examples"; FAIL=1
fi

# A proposal module without a test import passes as a proposal root.
if check DogeLib.Proposals.RelativeLockTime >"$WORK/clean-proposal" 2>&1; then
  echo "ok:   a proposal module without a test import passes"
else
  echo "FAIL: a proposal module without a test import does not pass"; cat "$WORK/clean-proposal"; FAIL=1
fi

exit "$FAIL"
