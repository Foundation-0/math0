#!/usr/bin/env bash
# Rebuild every math0 result and re-run every audit.
# Requires elan (https://github.com/leanprover/elan).
# Usage: scripts/verify.sh [--clean] [--expect N]
#   --clean     delete lean/.lake/build first, so every math0 module is elaborated and checked by the
#               kernel in this run instead of being replayed from an earlier build
#   --expect N  fail unless exactly N distinct statement checks ran (one per catalog result)
# MATH0_BATCH (default 2) is how many math0 modules are built at once: the heaviest proof files need
# up to 8 GB of memory each.
set -euo pipefail
clean=0
expect=""
while [ $# -gt 0 ]; do
  case "$1" in
    --clean) clean=1; shift ;;
    --expect) expect="$2"; shift 2 ;;
    *) echo "usage: $0 [--clean] [--expect N]" >&2; exit 2 ;;
  esac
done
batch="${MATH0_BATCH:-2}"
cd "$(dirname "$0")/../lean"
lake exe cache get
if [ "$clean" = 1 ]; then rm -rf .lake/build; fi
log="$(mktemp)"
# The audit, then every frozen statement, then every result, a few modules at a time.
mapfile -t mods < <(echo Math0.Audit; sed -n 's/^import //p' Math0/Statements.lean;
                    sed -n 's/^import //p' Math0.lean | grep -v -x -e Math0.Audit -e Math0.Statements)
for ((i = 0; i < ${#mods[@]}; i += batch)); do
  lake build "${mods[@]:i:batch}" 2>&1 | tee -a "$log"
done
lake build 2>&1 | tee -a "$log"   # the root modules, which only import what is already built
# The upstream statement source must be the pristine pinned checkout.
for pkg in formal_conjectures mathlib; do
  if [ -n "$(git -C ".lake/packages/$pkg" status --porcelain)" ]; then
    echo "error: .lake/packages/$pkg has local modifications" >&2
    exit 1
  fi
done
# A module built in an earlier batch is replayed by later ones, so count distinct checks.
checks=$(grep -o "math0 statement check: .*" "$log" | sort -u | wc -l)
if [ -n "$expect" ] && [ "$checks" != "$expect" ]; then
  echo "error: expected $expect statement checks, found $checks" >&2
  exit 1
fi
echo "OK: build succeeded; ${checks} statement checks passed (only propext, Classical.choice, Quot.sound allowed)."
