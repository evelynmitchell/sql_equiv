#!/usr/bin/env bash
# rewrite-audit: run the trust-base guard ad hoc.
#
#   check_trust_base.sh <Module> <Namespace> [--vacuity]
#
# Run from the Lean project root (where `lake env` works). Builds a temporary
# file that imports <Module>, defines #assert_trust_base, and checks every
# theorem under <Namespace>. With --vacuity it first plants a `sorry` theorem
# in <Namespace> and expects the guard to FAIL (exit 0 if it does).
set -euo pipefail
mod="${1:?module to import, e.g. MyProject}"
ns="${2:?namespace to check, e.g. MyProject}"
mode="${3:-}"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
f="$tmp/TrustBaseCheck.lean"
{
  echo "import Lean"
  echo "import $mod"
  grep -v '^import ' "$here/TrustBase.lean"
  echo
  if [ "$mode" = "--vacuity" ]; then
    echo "theorem $ns.rewriteAuditVacuityProbe : 1 = 1 := by sorry"
  fi
  echo "#assert_trust_base $ns"
} > "$f"
if [ "$mode" = "--vacuity" ]; then
  if lake env lean "$f" >"$tmp/out" 2>&1; then
    cat "$tmp/out"; echo "VACUITY CHECK FAILED: planted sorry was not detected"; exit 1
  fi
  grep -q "sorryAx" "$tmp/out" && { echo "vacuity check OK: planted sorry detected"; exit 0; }
  cat "$tmp/out"; echo "VACUITY CHECK INCONCLUSIVE: guard failed for another reason"; exit 1
fi
lake env lean "$f"
