#!/usr/bin/env bash
# Rebuild every math0 result from scratch and re-run every audit.
# Requires elan (https://github.com/leanprover/elan). Usage: scripts/verify.sh
set -euo pipefail
cd "$(dirname "$0")/../lean"
lake exe cache get
lake build 2>&1 | tee /tmp/math0-build.log
# The upstream statement source must be the pristine pinned checkout.
for pkg in formal_conjectures mathlib; do
  if [ -n "$(git -C ".lake/packages/$pkg" status --porcelain)" ]; then
    echo "error: .lake/packages/$pkg has local modifications" >&2
    exit 1
  fi
done
checks=$(grep -c "math0 statement check" /tmp/math0-build.log || true)
echo "OK: build succeeded; ${checks} statement checks passed (only propext, Classical.choice, Quot.sound allowed)."
