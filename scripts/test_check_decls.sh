#!/usr/bin/env bash
# The declaration check must report exactly the findings planted in
# scripts/CheckDeclsTest, pass once a baseline lists them, and fail on a
# baseline entry that no longer matches. Run from anywhere.
# Adapted from EthLib, scripts/test_check_decls.sh at commit 6a93711 (CC0 1.0).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

# The fixtures contain `sorry` on purpose, so they are built without --wfail.
if ! lake build CheckDeclsTest >"$WORK/build" 2>&1; then
  echo "FAIL: the fixtures do not build"; cat "$WORK/build"; exit 1
fi

check() { lake exe check-decls --scope CheckDeclsTest "$@" CheckDeclsTest; }

# One line per planted finding: its kind, then the declaration it is reported at.
# `usesNative` and everything in Good and Exports must not appear.
# CheckDeclsForeign is outside the scope, as a dependency would be.
LC_ALL=C sort >"$WORK/expected" <<'EOF'
axiom CheckDeclsTest.Bad.Phantom._native
axiom CheckDeclsTest.Bad.assumed
axioms CheckDeclsTest.Bad.Carrier
axioms CheckDeclsTest.Bad.usesAssumed
axioms CheckDeclsTest.ImportedSorry.inherited
csimp CheckDeclsTest.Bad.double_eq_doubleFast
extern CheckDeclsTest.Bad.external
implemented_by CheckDeclsTest.Bad.slow
native CheckDeclsTest.Bad.native
native _private.CheckDeclsTest.Proofs.Native.0.CheckDeclsTest.Proofs.Native.big
opaque CheckDeclsTest.Bad.hidden
partial CheckDeclsTest.Bad.spin
reaches-opaque CheckDeclsTest.Bad.countdown
reaches-opaque CheckDeclsTest.Bad.fallback
reaches-opaque CheckDeclsTest.Bad.fallbackMessage
sorry CheckDeclsTest.Bad.unfinished
unsafe CheckDeclsTest.Bad.Ghost._unsafe_rec
unsafe CheckDeclsTest.Bad.reinterpret
EOF

check --baseline /dev/null >"$WORK/out"; got=$?
grep -vE '^(check-decls:|stale )' "$WORK/out" | cut -d: -f1 | LC_ALL=C sort -u >"$WORK/found"
if [ "$got" -ne 1 ]; then
  echo "FAIL: exit $got with an empty baseline, expected 1"; FAIL=1
fi
if diff -u "$WORK/expected" "$WORK/found"; then
  echo "ok:   every planted finding is reported, and nothing else"
else
  echo "FAIL: the findings differ from the planted ones"; FAIL=1
fi

if check --baseline "$WORK/expected" >"$WORK/out"; then
  echo "ok:   a baseline that lists every finding passes"
else
  echo "FAIL: a baseline that lists every finding does not pass"; cat "$WORK/out"; FAIL=1
fi

{ cat "$WORK/expected"; echo "partial CheckDeclsTest.Good.double"; } >"$WORK/stale"
if ! check --baseline "$WORK/stale" >"$WORK/out" \
   && grep -qx 'stale baseline entry, no longer found: partial CheckDeclsTest.Good.double' "$WORK/out"; then
  echo "ok:   a stale baseline entry is reported, and fails the check"
else
  echo "FAIL: a stale baseline entry is not handled"; cat "$WORK/out"; FAIL=1
fi

# An imported unfinished proof must fail even without a direct `sorry` in scope.
if lake exe check-decls --scope CheckDeclsTest.ImportedSorry --baseline /dev/null \
    CheckDeclsTest.ImportedSorry >"$WORK/imported"; then
  echo "FAIL: an imported unfinished proof passed"; FAIL=1
elif grep -qx 'axioms CheckDeclsTest.ImportedSorry.inherited: depends on sorryAx, from a dependency' "$WORK/imported"; then
  echo "ok:   an imported unfinished proof fails at its first in-scope use"
else
  echo "FAIL: the imported unfinished proof was not attributed"; cat "$WORK/imported"; FAIL=1
fi

# Check the actual imported environment against every production file on disk.
if lake exe check-decls >"$WORK/production" 2>&1; then
  echo "ok:   every production module is reachable and has no findings"
else
  echo "FAIL: the production declaration check failed"; cat "$WORK/production"; FAIL=1
fi

# An unimported leaf file must fail even though it has no compiled declarations.
ORPHAN=$(mktemp DogeLib/CheckDeclsUnreachableXXXXXX.lean) || exit 1
trap 'rm -rf "$WORK"; rm -f "$ORPHAN"' EXIT
printf '%s\n' 'module' >"$ORPHAN"
mod=${ORPHAN%.lean}
mod=${mod//\//.}
if lake exe check-decls >"$WORK/unreachable" 2>&1; then
  echo "FAIL: an unreachable production module passed"; FAIL=1
elif grep -qx "unreachable-module $mod: not imported by the default production roots" "$WORK/unreachable" \
    && grep -q '^check-decls: .* declarations under DogeLib,' "$WORK/unreachable"; then
  echo "ok:   an unreachable production leaf is named and fails the check"
else
  echo "FAIL: the unreachable production module was not named"; cat "$WORK/unreachable"; FAIL=1
fi
rm -f "$ORPHAN"

# The default check needs the production file inventory from the repository root.
exe="$PWD/.lake/build/bin/check-decls"
lake env bash -c 'cd "$1" && exec "$2"' _ "$WORK" "$exe" >"$WORK/cwd" 2>&1
got=$?
if [ "$got" -eq 2 ] && grep -q '^check-decls: run the default production check from the repository root' "$WORK/cwd"; then
  echo "ok:   the default check explains a missing repository root"
else
  echo "FAIL: the missing repository root was not explained"; cat "$WORK/cwd"; FAIL=1
fi

exit "$FAIL"
