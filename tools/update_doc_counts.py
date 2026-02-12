#!/usr/bin/env python3
"""
Auto-update axiom/theorem counts in documentation files.

Counts `^axiom ` and `^theorem ` declarations in SqlEquiv/**/*.lean,
then updates sentinel lines and per-file tables in:
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

# Descriptions for per-file tables (keyed by filename without .lean)
FILE_DESCRIPTIONS = {
    # Equiv/
    "Comparison": "Comparison, boolean, arithmetic equivalences",
    "StatementAxioms": "Statement-level axioms (joins, subqueries, set ops)",
    "ExprAxioms": "Expression-level axioms and theorems",
    "Decidable": "Decidable equivalence helpers",
    "Defs": "Core definitions (ExprEquiv, StmtEquiv)",
    "ValueLemmas": "Value-level helper lemmas",
    "SetBagLemmas": "Set/bag equivalence lemmas",
    # Infrastructure
    "Semantics": "Evaluator unfolding (evalExprWithDb_lit, _binOp, etc.)",
    "Optimizer": "Optimizer correctness (pushdown, join reorder)",
    "ExprNormalization": "Normalization preserves semantics",
    "JoinReordering": "Join reorder forward/backward",
    "PredicatePushdown": "Predicate pushdown preserves semantics",
    "OptimizerUtils": "Optimizer utility lemmas",
}


def count_declarations():
    """Count axiom/theorem declarations in SqlEquiv/**/*.lean.

    Returns (summary_dict, per_file_list) where per_file_list contains
    (relative_path, stem, axioms, theorems, is_equiv) tuples.
    """
    per_file = []

    for lean_file in sorted(SQLEQUIV.rglob("*.lean")):
        file_axioms = 0
        file_theorems = 0
        with open(lean_file, encoding="utf-8") as f:
            for line in f:
                if re.match(r"^\s*(?:private\s+)?axiom\s", line):
                    file_axioms += 1
                elif re.match(r"^\s*(?:private\s+)?theorem\s", line):
                    file_theorems += 1

        if file_axioms > 0 or file_theorems > 0:
            is_equiv = EQUIV_DIR in lean_file.parents
            rel = str(lean_file.relative_to(SQLEQUIV))
            per_file.append((rel, lean_file.stem, file_axioms, file_theorems, is_equiv))

    equiv_axioms = sum(a for _, _, a, _, e in per_file if e)
    infra_axioms = sum(a for _, _, a, _, e in per_file if not e)
    total_theorems = sum(t for _, _, _, t, _ in per_file)
    total_axioms = equiv_axioms + infra_axioms
    axiom_files = sum(1 for _, _, a, _, _ in per_file if a > 0)

    summary = {
        "total_axioms": total_axioms,
        "equiv_axioms": equiv_axioms,
        "infra_axioms": infra_axioms,
        "total_theorems": total_theorems,
        "axiom_file_count": axiom_files,
    }
    return summary, per_file


def generate_table(rows):
    """Generate a markdown table from (filename, axioms, theorems, description) rows."""
    lines = ["| File | Axioms | Theorems | Description |",
             "|------|--------|----------|-------------|"]
    total_a, total_t = 0, 0
    for fname, axioms, theorems, desc in rows:
        lines.append(f"| `{fname}` | {axioms} | {theorems} | {desc} |")
        total_a += axioms
        total_t += theorems
    lines.append(f"| **Subtotal** | **{total_a}** | **{total_t}** | |")
    return "\n".join(lines), total_a, total_t


def update_audit_tables(audit_path, per_file, total_axioms, total_theorems):
    """Regenerate the per-file tables in theorem_coverage_audit_plan.md."""
    text = audit_path.read_text(encoding="utf-8")
    original = text

    # Build equiv rows
    equiv_rows = []
    for rel, stem, axioms, theorems, is_equiv in per_file:
        if is_equiv:
            desc = FILE_DESCRIPTIONS.get(stem, "")
            equiv_rows.append((stem + ".lean", axioms, theorems, desc))

    # Build infra rows
    infra_rows = []
    for rel, stem, axioms, theorems, is_equiv in per_file:
        if not is_equiv:
            desc = FILE_DESCRIPTIONS.get(stem, "")
            infra_rows.append((stem + ".lean", axioms, theorems, desc))

    equiv_table, equiv_a, equiv_t = generate_table(equiv_rows)
    infra_table, infra_a, infra_t = generate_table(infra_rows)

    total = total_axioms + total_theorems
    pct = total_theorems / total * 100 if total > 0 else 0

    # Replace equiv table
    text = re.sub(
        r"(### Equivalence Axioms \(`SqlEquiv/Equiv/`\)\n\n)"
        r"\|[^\n]*\n\|[^\n]*\n(?:\|[^\n]*\n)*",
        rf"\1{equiv_table}\n",
        text,
    )

    # Replace infra table
    text = re.sub(
        r"(### Infrastructure Axioms\n\n)"
        r"\|[^\n]*\n\|[^\n]*\n(?:\|[^\n]*\n)*",
        rf"\1{infra_table}\n",
        text,
    )

    # Replace Grand Total line
    text = re.sub(
        r"### Grand Total:.*",
        f"### Grand Total: {total_axioms} axioms, {total_theorems} theorems ({pct:.1f}% proved)",
        text,
    )

    # Replace status header counts
    text = re.sub(
        r"\*\*\d+ axioms\*\* across \d+ `.lean` files \(\d+ in `Equiv/`, \d+ in infrastructure\)",
        f"**{total_axioms} axioms** across {sum(1 for _, _, a, _, _ in per_file if a > 0)} `.lean` files ({equiv_a} in `Equiv/`, {infra_a} in infrastructure)",
        text,
    )
    text = re.sub(
        r"\*\*\d+ theorems\*\* proved[^\n]*",
        f"**{total_theorems} theorems** proved ({pct:.1f}%)",
        text,
    )

    if text != original:
        audit_path.write_text(text, encoding="utf-8")
        return True
    return False


def update_file(path, replacements):
    """Apply regex replacements to a file. Returns True if changed."""
    text = path.read_text(encoding="utf-8")
    original = text
    for pattern, repl in replacements:
        text = re.sub(pattern, repl, text)
    if text != original:
        path.write_text(text, encoding="utf-8")
        return True
    return False


def main():
    summary, per_file = count_declarations()
    total = summary["total_axioms"]
    equiv = summary["equiv_axioms"]
    infra = summary["infra_axioms"]
    theorems = summary["total_theorems"]

    changed = []

    # --- docs/PROVING_AXIOMS_PLAN.md ---
    plan_path = ROOT / "docs" / "PROVING_AXIOMS_PLAN.md"
    if plan_path.exists():
        total_all = total + theorems
        pct = theorems / total_all * 100 if total_all > 0 else 0
        if update_file(plan_path, [
            (
                r"\*\*Current totals\*\*: \d+ axioms remaining[^\n]*",
                f"**Current totals**: {total} axioms remaining ({equiv} in Equiv/, {infra} in infrastructure files), {theorems} theorems proved ({pct:.1f}%).",
            ),
            (
                r"Axiom ratchet: \d+",
                f"Axiom ratchet: {total}",
            ),
        ]):
            changed.append(str(plan_path.relative_to(ROOT)))

    # --- docs/theorem_coverage_audit_plan.md (tables + summary) ---
    audit_path = ROOT / "docs" / "theorem_coverage_audit_plan.md"
    if audit_path.exists():
        if update_audit_tables(audit_path, per_file, total, theorems):
            changed.append(str(audit_path.relative_to(ROOT)))
        # Also update ratchet line
        if update_file(audit_path, [
            (r"Axiom ratchet: \d+", f"Axiom ratchet: {total}"),
        ]):
            if str(audit_path.relative_to(ROOT)) not in changed:
                changed.append(str(audit_path.relative_to(ROOT)))

    # --- tools/axiom_count_minimum.txt (ratchet: only decrease) ---
    ratchet_path = ROOT / "tools" / "axiom_count_minimum.txt"
    if ratchet_path.exists():
        old_ratchet = int(ratchet_path.read_text(encoding="utf-8").strip())
        if total < old_ratchet:
            ratchet_path.write_text(f"{total}\n", encoding="utf-8")
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
