#!/usr/bin/env bash
# Tests for the audit commands in lean/Math0/Audit.lean.
# Every file in tests/audit/fail must be rejected with the message named on its first line
# ("-- expect: <text>"); every file in tests/audit/pass must compile.
# Requires a built Math0.Audit (lake build Math0.Audit). Usage: scripts/test_audit.sh
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT/lean"
status=0
for f in "$ROOT"/tests/audit/fail/*.lean; do
  expect="$(head -1 "$f" | sed -n 's/^-- expect: //p')"
  if [ -z "$expect" ]; then echo "FAIL $f: no '-- expect:' line"; status=1; continue; fi
  if out="$(lake env lean "$f" 2>&1)"; then
    echo "FAIL $(basename "$f"): accepted, but it should be rejected"; status=1
  elif ! grep -qF "$expect" <<<"$out"; then
    echo "FAIL $(basename "$f"): rejected without '$expect':"; echo "$out" | head -5; status=1
  else
    echo "ok   $(basename "$f") is rejected ($expect)"
  fi
done
for f in "$ROOT"/tests/audit/pass/*.lean; do
  if out="$(lake env lean "$f" 2>&1)"; then
    echo "ok   $(basename "$f") is accepted"
  else
    echo "FAIL $(basename "$f"): rejected:"; echo "$out" | head -10; status=1
  fi
done
exit $status
