#!/usr/bin/env bash
# Rebuild every math0 result and re-run every audit.
# Requires elan (https://github.com/leanprover/elan).
# Usage: scripts/verify.sh [--clean] [--expect N]
#   --clean     delete lean/.lake/build first, so every math0 module is re-elaborated and
#               re-checked by the kernel instead of being replayed from an earlier build
#   --expect N  fail unless exactly N statement checks ran (one per catalog result)
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
cd "$(dirname "$0")/../lean"
lake exe cache get
if [ "$clean" = 1 ]; then rm -rf .lake/build; fi
log="$(mktemp)"
lake build 2>&1 | tee "$log"
# The upstream statement source must be the pristine pinned checkout.
for pkg in formal_conjectures mathlib; do
  if [ -n "$(git -C ".lake/packages/$pkg" status --porcelain)" ]; then
    echo "error: .lake/packages/$pkg has local modifications" >&2
    exit 1
  fi
done
checks=$(grep -c "math0 statement check" "$log" || true)
if [ "$clean" = 1 ] && grep -q "Replayed Math0" "$log"; then
  echo "error: some math0 modules were replayed rather than rebuilt" >&2
  exit 1
fi
if [ -n "$expect" ] && [ "$checks" != "$expect" ]; then
  echo "error: expected $expect statement checks, found $checks" >&2
  exit 1
fi
echo "OK: build succeeded; ${checks} statement checks passed (only propext, Classical.choice, Quot.sound allowed)."
