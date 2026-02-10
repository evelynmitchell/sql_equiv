#!/usr/bin/env python3
"""
Auto-update axiom/theorem counts in documentation files.

Counts `^axiom ` and `^theorem ` declarations in SqlEquiv/**/*.lean,
then updates sentinel lines in:
  - docs/PROVING_AXIOMS_PLAN.md
  - docs/theorem_coverage_audit_plan.md
  - tools/axiom_count_minimum.txt  (ratchet — only decreases)

Run standalone or from the pre-commit hook.
Exit code is always 0 (advisory, not blocking).
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SQLEQUIV = ROOT / "SqlEquiv"
EQUIV_DIR = SQLEQUIV / "Equiv"


def count_declarations():
    """Count axiom/theorem declarations in SqlEquiv/**/*.lean."""
    equiv_axioms = 0
    infra_axioms = 0
    total_theorems = 0
    axiom_files = set()

    for lean_file in sorted(SQLEQUIV.rglob("*.lean")):
        file_axioms = 0
        file_theorems = 0
        with open(lean_file) as f:
            for line in f:
                if re.match(r"^axiom ", line):
                    file_axioms += 1
                elif re.match(r"^theorem ", line):
                    file_theorems += 1

        if file_axioms > 0:
            axiom_files.add(lean_file)
            if EQUIV_DIR in lean_file.parents:
                equiv_axioms += file_axioms
            else:
                infra_axioms += file_axioms

        total_theorems += file_theorems

    total_axioms = equiv_axioms + infra_axioms
    return {
        "total_axioms": total_axioms,
        "equiv_axioms": equiv_axioms,
        "infra_axioms": infra_axioms,
        "total_theorems": total_theorems,
        "axiom_file_count": len(axiom_files),
    }


def update_file(path, replacements):
    """Apply regex replacements to a file. Returns True if changed."""
    text = path.read_text()
    original = text
    for pattern, repl in replacements:
        text = re.sub(pattern, repl, text)
    if text != original:
        path.write_text(text)
        return True
    return False


def main():
    counts = count_declarations()
    total = counts["total_axioms"]
    equiv = counts["equiv_axioms"]
    infra = counts["infra_axioms"]
    theorems = counts["total_theorems"]
    n_files = counts["axiom_file_count"]

    changed = []

    # --- docs/PROVING_AXIOMS_PLAN.md ---
    plan_path = ROOT / "docs" / "PROVING_AXIOMS_PLAN.md"
    if plan_path.exists():
        if update_file(plan_path, [
            # **Current totals**: N axioms remaining (X in Equiv/, Y in infrastructure files), Z theorems proved.
            (
                r"\*\*Current totals\*\*: \d+ axioms remaining \(\d+ in Equiv/, \d+ in infrastructure files\), \d+ theorems proved\.",
                f"**Current totals**: {total} axioms remaining ({equiv} in Equiv/, {infra} in infrastructure files), {theorems} theorems proved.",
            ),
            # Axiom ratchet: N
            (
                r"Axiom ratchet: \d+",
                f"Axiom ratchet: {total}",
            ),
        ]):
            changed.append(str(plan_path.relative_to(ROOT)))

    # --- docs/theorem_coverage_audit_plan.md ---
    audit_path = ROOT / "docs" / "theorem_coverage_audit_plan.md"
    if audit_path.exists():
        if update_file(audit_path, [
            # **N axioms** across M `.lean` files (X in `Equiv/`, Y in infrastructure)
            (
                r"\*\*\d+ axioms\*\* across \d+ `.lean` files \(\d+ in `Equiv/`, \d+ in infrastructure\)",
                f"**{total} axioms** across {n_files} `.lean` files ({equiv} in `Equiv/`, {infra} in infrastructure)",
            ),
            # **Z theorems** proved (...)
            (
                r"\*\*\d+ theorems\*\* proved(?: \(all in `Equiv/`\))?",
                f"**{theorems} theorems** proved",
            ),
            # Axiom ratchet: N
            (
                r"Axiom ratchet: \d+",
                f"Axiom ratchet: {total}",
            ),
            # Grand Total: N axioms, Z theorems
            (
                r"Grand Total: \d+ axioms, \d+ theorems",
                f"Grand Total: {total} axioms, {theorems} theorems",
            ),
        ]):
            changed.append(str(audit_path.relative_to(ROOT)))

    # --- tools/axiom_count_minimum.txt (ratchet: only decrease) ---
    ratchet_path = ROOT / "tools" / "axiom_count_minimum.txt"
    if ratchet_path.exists():
        old_ratchet = int(ratchet_path.read_text().strip())
        if total < old_ratchet:
            ratchet_path.write_text(f"{total}\n")
            changed.append(str(ratchet_path.relative_to(ROOT)))
            print(f"  Ratchet decreased: {old_ratchet} -> {total}")
        elif total > old_ratchet:
            print(f"  WARNING: axiom count ({total}) exceeds ratchet ({old_ratchet}) — new axioms added?")

    # --- Summary ---
    print(f"  Counts: {total} axioms ({equiv} Equiv/ + {infra} infra), {theorems} theorems")
    if changed:
        print(f"  Updated: {', '.join(changed)}")
    else:
        print("  No changes needed.")

    return changed


if __name__ == "__main__":
    changed = main()
    sys.exit(0)
