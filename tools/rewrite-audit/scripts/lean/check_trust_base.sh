#!/usr/bin/env bash
# rewrite-audit: run the trust-base guard ad hoc.
#
#   check_trust_base.sh <Module> <Namespace> [--vacuity]
#
# Run from the Lean project root (where `lake env` works). Builds a temporary
# file that imports <Module>, defines #assert_trust_base, and checks every
# theorem, definition and opaque constant under <Namespace>. With --vacuity it
# first plants three probes in <Namespace> (a public `sorry` theorem, a private
# `native_decide` theorem, and a proof-carrying definition with `sorry`) and
# expects the guard to FAIL and name all three (exit 0 if it does).
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
    echo "private theorem $ns.rewriteAuditVacuityPrivate : (2 : Nat) * 21 = 42 := by native_decide"
    echo "def $ns.rewriteAuditVacuityDef (n : Nat) : { m : Nat // m = n + 1 } := ⟨n, sorry⟩"
  fi
  echo "#assert_trust_base $ns"
} > "$f"
if [ "$mode" = "--vacuity" ]; then
  if lake env lean "$f" >"$tmp/out" 2>&1; then
    cat "$tmp/out"; echo "VACUITY CHECK FAILED: planted sorry was not detected"; exit 1
  fi
  missing=""
  for probe in rewriteAuditVacuityProbe rewriteAuditVacuityPrivate rewriteAuditVacuityDef; do
    grep -q "$probe" "$tmp/out" || missing="$missing $probe"
  done
  if [ -z "$missing" ]; then
    echo "vacuity check OK: public sorry, private native_decide and proof-carrying def all detected"; exit 0
  fi
  cat "$tmp/out"; echo "VACUITY CHECK FAILED: not reported:$missing"; exit 1
fi
lake env lean "$f"
