#!/usr/bin/env bash
# The declaration check must report exactly the findings planted in
# scripts/CheckDeclsTest, pass once a baseline lists them, and fail on a
# baseline entry that no longer matches. Run from anywhere.
# Adapted from EthLib, scripts/test_check_decls.sh at commit bb6dfe5 (CC0 1.0).
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1
FAIL=0
mkdir -p .lane
WORK=$(mktemp -d .lane/check-decls.XXXXXX)
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
if grep -q '^check-decls: .*production inventory and full Refinement coverage NOT checked' "$WORK/out"; then
  echo "ok:   explicit module checks disclose the omitted production coverage"
else
  echo "FAIL: the explicit module check omitted its coverage notice"; cat "$WORK/out"; FAIL=1
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
    && grep -q '^check-decls: .* declarations under DogeLib and Refinement,' "$WORK/unreachable"; then
  echo "ok:   an unreachable production leaf is named and fails the check"
else
  echo "FAIL: the unreachable production module was not named"; cat "$WORK/unreachable"; FAIL=1
fi
rm -f "$ORPHAN"

# The same holds for a leaf file under the proposal libraries (design record 0007).
ORPHAN=$(mktemp DogeLib/Proposals/CheckDeclsUnreachableXXXXXX.lean) || exit 1
printf '%s\n' 'module' >"$ORPHAN"
mod=${ORPHAN%.lean}
mod=${mod//\//.}
if lake exe check-decls >"$WORK/unreachable-proposal" 2>&1; then
  echo "FAIL: an unreachable proposal module passed"; FAIL=1
elif grep -qx "unreachable-module $mod: not imported by the default production roots" "$WORK/unreachable-proposal"; then
  echo "ok:   an unreachable proposal leaf is named and fails the check"
else
  echo "FAIL: the unreachable proposal module was not named"; cat "$WORK/unreachable-proposal"; FAIL=1
fi
rm -f "$ORPHAN"

# The refinement namespace must reject local and imported trust violations.
PLANTED=Refinement/Refinement/CheckDeclsPlanted.lean
if [[ -e "$PLANTED" ]]; then
  echo "FAIL: refinement fixture path already exists"; exit 1
fi
trap 'rm -rf "$WORK"; rm -f "$ORPHAN" "$PLANTED"' EXIT
cat >"$PLANTED" <<'EOF'
module
public import Aeneas
public import CheckDeclsForeign
@[expose] public section
namespace Refinement.CheckDeclsPlanted
axiom assumed : False
def importedAeneas := Aeneas.Std.core.pin.Pin Unit
theorem native : 1 + 1 = 2 := by native_decide
def reachesHidden := CheckDeclsForeign.hiddenNat
def platform := System.Platform.numBits
end Refinement.CheckDeclsPlanted
EOF
mkdir -p Refinement/.lake/build/lib/lean/Refinement
if ! lake -d Refinement env lean -o "$PWD/Refinement/.lake/build/lib/lean/Refinement/CheckDeclsPlanted.olean" "$PWD/$PLANTED" >"$WORK/refinement-build" 2>&1; then
  echo "FAIL: refinement fixture does not compile"; cat "$WORK/refinement-build"; exit 1
fi
if lake exe check-decls --scope Refinement --baseline /dev/null Refinement.CheckDeclsPlanted >"$WORK/refinement" 2>&1; then
  echo "FAIL: refinement trust violations passed"; FAIL=1
elif grep -q '^axiom Refinement.CheckDeclsPlanted.assumed:' "$WORK/refinement" \
    && grep -q '^axioms Refinement.CheckDeclsPlanted.importedAeneas: depends on Aeneas.Std.core.pin.Pin, from a dependency' "$WORK/refinement" \
    && grep -q '^native Refinement.CheckDeclsPlanted.native:' "$WORK/refinement" \
    && grep -q '^reaches-opaque Refinement.CheckDeclsPlanted.reachesHidden:' "$WORK/refinement" \
    && ! grep -q '^reaches-opaque Refinement.CheckDeclsPlanted.platform:' "$WORK/refinement"; then
  echo "ok:   refinement rejects prohibited axioms, native proofs and other opaque dependencies"
else
  echo "FAIL: refinement trust violations were not reported"; cat "$WORK/refinement"; FAIL=1
fi
if lake exe check-decls >"$WORK/refinement-unreachable" 2>&1; then
  echo "FAIL: an unreachable refinement module passed"; FAIL=1
elif grep -q '^unreachable-module Refinement.CheckDeclsPlanted:' "$WORK/refinement-unreachable"; then
  echo "ok:   an unreachable refinement leaf is named and fails the check"
else
  echo "FAIL: the unreachable refinement module was not named"; cat "$WORK/refinement-unreachable"; FAIL=1
fi
# Import the planted module through the actual library root to test default scope.
cp Refinement/Refinement.lean "$WORK/refinement-root"
trap 'cp "$WORK/refinement-root" Refinement/Refinement.lean; rm -rf "$WORK"; rm -f "$ORPHAN" "$PLANTED"' EXIT
printf '\npublic import Refinement.CheckDeclsPlanted\n' >> Refinement/Refinement.lean
if ! lake -d Refinement build Refinement >"$WORK/planted-root-build" 2>&1; then
  echo "FAIL: the planted refinement library does not build"; cat "$WORK/planted-root-build"; exit 1
fi
if lake exe check-decls >"$WORK/planted-production" 2>&1; then
  echo "FAIL: the default check ignored a bad refinement declaration"; FAIL=1
elif grep -q '^axiom Refinement.CheckDeclsPlanted.assumed:' "$WORK/planted-production" \
    && grep -q '^axioms Refinement.CheckDeclsPlanted.importedAeneas:' "$WORK/planted-production" \
    && grep -q '^native Refinement.CheckDeclsPlanted.native:' "$WORK/planted-production" \
    && grep -q '^reaches-opaque Refinement.CheckDeclsPlanted.reachesHidden:' "$WORK/planted-production"; then
  echo "ok:   the default production check includes bad refinement declarations"
else
  echo "FAIL: the default refinement findings were not reported"; cat "$WORK/planted-production"; FAIL=1
fi
cp "$WORK/refinement-root" Refinement/Refinement.lean
if ! lake -d Refinement build Refinement >"$WORK/restored-root-build" 2>&1; then
  echo "FAIL: the restored refinement library does not build"; cat "$WORK/restored-root-build"; exit 1
fi
rm -f "$PLANTED"
trap 'rm -rf "$WORK"; rm -f "$ORPHAN" "$PLANTED"' EXIT

# The platform allowance must never apply to the specification namespace.
SPEC_PLANTED=DogeLib/CheckDeclsPlatform.lean
if [[ -e "$SPEC_PLANTED" ]]; then
  echo "FAIL: specification fixture path already exists"; exit 1
fi
trap 'rm -rf "$WORK"; rm -f "$ORPHAN" "$PLANTED" "$SPEC_PLANTED"' EXIT
cat >"$SPEC_PLANTED" <<'EOF'
module
public import Init.System.Platform
@[expose] public section
namespace DogeLib.CheckDeclsPlatform
def platform := System.Platform.numBits
end DogeLib.CheckDeclsPlatform
EOF
if ! lake env lean -o .lake/build/lib/lean/DogeLib/CheckDeclsPlatform.olean "$SPEC_PLANTED" >"$WORK/platform-build" 2>&1; then
  echo "FAIL: the specification platform fixture does not compile"; cat "$WORK/platform-build"; exit 1
fi
if lake exe check-decls --scope DogeLib --baseline /dev/null DogeLib.CheckDeclsPlatform >"$WORK/platform" 2>&1; then
  echo "FAIL: the specification reached the opaque platform word size"; FAIL=1
elif grep -q '^reaches-opaque DogeLib.CheckDeclsPlatform.platform: unfolds to \[System.Platform.getNumBits\]' "$WORK/platform"; then
  echo "ok:   the platform allowance applies only to refinement modules"
else
  echo "FAIL: the specification platform dependency was not reported"; cat "$WORK/platform"; FAIL=1
fi
rm -f "$SPEC_PLANTED"

# The default check needs the production file inventory from the repository root.
exe="$PWD/.lake/build/bin/check-decls"
lake env bash -c 'cd "$1" && exec "$2"' _ "$WORK" "$exe" >"$WORK/cwd" 2>&1
got=$?
if [ "$got" -eq 2 ] && grep -q '^check-decls: run the default production check from the repository root' "$WORK/cwd"; then
  echo "ok:   the default check explains a missing repository root"
else
  echo "FAIL: the missing repository root was not explained"; cat "$WORK/cwd"; FAIL=1
fi

# Default checks fail closed when the optional package is absent or unbuilt.
refinement_olean=Refinement/.lake/build/lib/lean/Refinement.olean
mv "$refinement_olean" "$WORK/unbuilt-root.olean"
trap 'mv "$WORK/unbuilt-root.olean" "$refinement_olean" 2>/dev/null || true; mv "$WORK/refinement-lakefile" Refinement/lakefile.lean 2>/dev/null || true; rm -rf "$WORK"' EXIT
if lake exe check-decls >"$WORK/unbuilt" 2>&1; then
  echo "FAIL: the default check passed without the built refinement package"; FAIL=1
elif grep -q '^check-decls: refinement package unbuilt:' "$WORK/unbuilt"; then
  echo "ok:   the default check fails closed on an unbuilt refinement package"
else
  echo "FAIL: the unbuilt refinement package was not explained"; cat "$WORK/unbuilt"; FAIL=1
fi
if lake exe check-decls --skip-refinement >"$WORK/skipped" 2>&1 \
    && grep -q '^check-decls: .*Refinement NOT checked' "$WORK/skipped"; then
  echo "ok:   explicit omission passes with the Refinement NOT checked summary"
else
  echo "FAIL: explicit omission did not pass with its summary notice"; cat "$WORK/skipped"; FAIL=1
fi
mv "$WORK/unbuilt-root.olean" "$refinement_olean"
mv Refinement/lakefile.lean "$WORK/refinement-lakefile"
if lake exe check-decls >"$WORK/absent" 2>&1; then
  echo "FAIL: the default check passed without the refinement package"; FAIL=1
elif grep -q '^check-decls: refinement package unavailable:' "$WORK/absent"; then
  echo "ok:   the default check fails closed on an absent refinement package"
else
  echo "FAIL: the absent refinement package was not explained"; cat "$WORK/absent"; FAIL=1
fi
mv "$WORK/refinement-lakefile" Refinement/lakefile.lean

exit "$FAIL"
