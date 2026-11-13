#!/usr/bin/env bash
# rewrite-audit: print the axioms of named theorems.
#
#   print_axioms.sh <Module> <name> [<name> ...]
#
# Run from the Lean project root.
set -euo pipefail
mod="${1:?module to import}"; shift
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
f="$tmp/PrintAxioms.lean"
echo "import $mod" > "$f"
for n in "$@"; do echo "#print axioms $n" >> "$f"; done
lake env lean "$f"
