#!/usr/bin/env python3
"""Count axioms and theorems across the SqlEquiv codebase.

Usage:
    python tools/count_axioms_theorems.py          # summary
    python tools/count_axioms_theorems.py -v        # per-file breakdown
    python tools/count_axioms_theorems.py --names   # list every axiom/theorem name
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SQLEQUIV_DIR = PROJECT_ROOT / "SqlEquiv"

AXIOM_RE = re.compile(r"^\s*(?:private\s+)?axiom\s+([^\s:({]+)")
THEOREM_RE = re.compile(r"^\s*(?:private\s+)?theorem\s+([^\s:({]+)")


def scan_file(path: Path) -> tuple[list[str], list[str]]:
    """Return (axiom_names, theorem_names) found in a .lean file."""
    axioms: list[str] = []
    theorems: list[str] = []
    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.lstrip()
        if not line or line.startswith("--"):
            continue
        m = AXIOM_RE.match(raw_line)
        if m:
            axioms.append(m.group(1))
            continue
        m = THEOREM_RE.match(raw_line)
        if m:
            theorems.append(m.group(1))
    return axioms, theorems


def main() -> None:
    parser = argparse.ArgumentParser(description="Count axioms and theorems")
    parser.add_argument("-v", "--verbose", action="store_true", help="Per-file breakdown")
    parser.add_argument("--names", action="store_true", help="List every axiom/theorem name")
    args = parser.parse_args()

    files = sorted(SQLEQUIV_DIR.rglob("*.lean"))

    total_axioms = 0
    total_theorems = 0
    rows: list[tuple[str, list[str], list[str]]] = []

    for f in files:
        axioms, theorems = scan_file(f)
        if axioms or theorems:
            rel = str(f.relative_to(PROJECT_ROOT))
            rows.append((rel, axioms, theorems))
            total_axioms += len(axioms)
            total_theorems += len(theorems)

    total = total_axioms + total_theorems

    # Summary
    print("=" * 52)
    print(" Axiom / Theorem Count")
    print("=" * 52)
    print(f"  Axioms:    {total_axioms:>4}")
    print(f"  Theorems:  {total_theorems:>4}")
    print(f"  Total:     {total:>4}")
    if total > 0:
        pct = total_theorems / total * 100
        print(f"  Proved:    {pct:>5.1f}%")
    print()

    # Per-file breakdown
    if args.verbose or args.names:
        hdr = f"  {'File':<45s} {'Axioms':>6s} {'Thms':>6s} {'Total':>6s}"
        print(hdr)
        print("  " + "-" * (len(hdr) - 2))
        for rel, axioms, theorems in rows:
            short = rel.replace("SqlEquiv/", "")
            print(f"  {short:<45s} {len(axioms):>6d} {len(theorems):>6d} {len(axioms)+len(theorems):>6d}")
        print("  " + "-" * (len(hdr) - 2))
        print(f"  {'TOTAL':<45s} {total_axioms:>6d} {total_theorems:>6d} {total:>6d}")
        print()

    # Names listing
    if args.names:
        for rel, axioms, theorems in rows:
            short = rel.replace("SqlEquiv/", "")
            if axioms:
                print(f"  {short} — axioms:")
                for name in axioms:
                    print(f"    - {name}")
            if theorems:
                print(f"  {short} — theorems:")
                for name in theorems:
                    print(f"    + {name}")
            print()


if __name__ == "__main__":
    main()
