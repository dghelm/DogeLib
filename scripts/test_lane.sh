#!/usr/bin/env bash
# Regression tests for scripts/lane. Runs in a temporary repository; touches nothing else.
#   bash scripts/test_lane.sh
set -euo pipefail

LANE_SRC=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/lane
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

export GIT_AUTHOR_NAME=test GIT_AUTHOR_EMAIL=test@example.invalid
export GIT_COMMITTER_NAME=test GIT_COMMITTER_EMAIL=test@example.invalid
unset DOGELIB_LANES_DIR

pass=0
fail() { echo "FAIL: $*" >&2; exit 1; }
ok() { pass=$((pass + 1)); echo "ok - $*"; }
# expect_fail <description> <command...>: the command must exit nonzero.
expect_fail() { local d=$1; shift; if "$@" >/dev/null 2>&1; then fail "$d: succeeded"; fi; ok "$d"; }

REPO=$TMP/DogeLib
LANES=$TMP/DogeLib-worktrees
mkdir -p "$REPO/scripts"
cp "$LANE_SRC" "$REPO/scripts/lane"
printf '/STATUS.md\n/.lane/\n' >"$REPO/.gitignore"
cd "$REPO"
git init -q -b main
git add -A
git commit -qm init
lane() { "$REPO/scripts/lane" "$@"; }

# Creation and validation.
expect_fail "rejects a bad type" lane new Feat/x
expect_fail "rejects a bad slug" lane new feat/Bad_Slug
expect_fail "rejects an unknown base" lane new feat/x --base no-such-ref
lane new feat/a >/dev/null
[ -f "$LANES/feat-a/STATUS.md" ] || fail "new did not write STATUS.md"
[ -d "$LANES/feat-a/.lane" ] || fail "new did not create .lane/"
ok "new creates worktree, STATUS.md, and .lane/"
[ -z "$(git -C "$LANES/feat-a" status --porcelain)" ] || fail "lane files are not ignored"
ok "STATUS.md and .lane/ do not make the lane dirty"
expect_fail "rejects an existing branch" lane new feat/a
git -C "$LANES/feat-a" commit -q --allow-empty -m a1
lane new proof/b --base feat/a >/dev/null
[ "$(git rev-parse proof/b)" = "$(git rev-parse feat/a)" ] || fail "stacked lane has the wrong base"
ok "stacked lane starts at its base"

# Listing tolerates missing STATUS.md and a detached HEAD.
lane new chore/c >/dev/null
rm "$LANES/chore-c/STATUS.md"
git -C "$LANES/proof-b" checkout -q --detach
out=$(lane list) || fail "list exited nonzero"
grep -q '^chore-c  *? ' <<<"$out" || fail "missing STATUS.md not shown as '?': $out"
grep -q '^proof-b .*(detached)' <<<"$out" || fail "detached lane not listed: $out"
grep -q '^feat-a  *active  *0  *+1/-0 ' <<<"$out" || fail "feat-a row wrong: $out"
ok "list reports missing STATUS.md, detached HEAD, and divergence"
git -C "$LANES/proof-b" checkout -q proof/b

# Lanes directory override.
expect_fail "rejects a relative DOGELIB_LANES_DIR" env DOGELIB_LANES_DIR=rel "$REPO/scripts/lane" list
ALT=$TMP/alt-lanes
DOGELIB_LANES_DIR=$ALT lane new docs/d >/dev/null
[ -d "$ALT/docs-d" ] || fail "override not used by new"
(cd "$ALT/docs-d" && DOGELIB_LANES_DIR=$ALT/ "$REPO/scripts/lane" rm docs-d >/dev/null)
[ ! -e "$ALT/docs-d" ] || fail "override not used by rm from inside the lane"
[ -d "$ALT/.archive" ] || fail "rm did not archive under the override"
ok "absolute override resolves the same from main and from a lane"

# Removal.
touch "$LANES/feat-a/untracked"
expect_fail "rm refuses a dirty lane" lane rm feat-a
[ -d "$LANES/feat-a" ] || fail "dirty lane was removed"
rm "$LANES/feat-a/untracked"
expect_fail "rm rejects a path instead of a lane name" lane rm ../feat-a
echo note >"$LANES/feat-a/.lane/log.txt"
(cd "$LANES/feat-a" && "$REPO/scripts/lane" rm feat-a >/dev/null)
[ ! -e "$LANES/feat-a" ] || fail "worktree still present"
ls "$LANES"/.archive/feat-a-*/lane/log.txt >/dev/null 2>&1 || fail ".lane/ not archived"
git show-ref --verify --quiet refs/heads/feat/a || fail "unmerged branch was deleted"
ok "rm from inside the lane archives files and keeps an unmerged branch"
git merge -q --ff-only proof/b
lane rm proof-b >/dev/null
git show-ref --verify --quiet refs/heads/proof/b && fail "merged branch was kept"
ok "rm deletes a merged branch"

echo "all $pass checks passed"
