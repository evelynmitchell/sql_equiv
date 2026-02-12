#!/usr/bin/env python3
"""Find unused private declarations in Lean files.

Scans for `private theorem`, `private def`, `private lemma`, etc. and checks
whether the declared name appears anywhere else in the same file.  If it only
appears at its definition site, it's reported as unused.

Usage:
    uv run python tools/unused_private_checker.py              # check all
    uv run python tools/unused_private_checker.py SqlEquiv/Equiv/StatementAxioms.lean
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SQLEQUIV_DIR = PROJECT_ROOT / "SqlEquiv"

# Matches: private theorem foo, private def bar, private lemma baz, etc.
PRIVATE_DECL_RE = re.compile(
    r"^\s*private\s+(?:theorem|def|lemma|abbrev|instance)\s+([^\s:({]+)"
)


def check_file(path: Path) -> list[tuple[int, str]]:
    """Return [(line_number, name)] for unused private declarations."""
    lines = path.read_text(encoding="utf-8").splitlines()
    full_text = "\n".join(lines)

    unused = []
    for i, line in enumerate(lines, 1):
        m = PRIVATE_DECL_RE.match(line)
        if not m:
            continue
        name = m.group(1)
        # Count occurrences as whole-word matches
        occurrences = len(re.findall(rf"\b{re.escape(name)}\b", full_text))
        if occurrences <= 1:
            unused.append((i, name))

    return unused


def main() -> int:
    if len(sys.argv) > 1:
        files = [Path(a) for a in sys.argv[1:]]
    else:
        files = sorted(SQLEQUIV_DIR.rglob("*.lean"))

    total_unused = 0

    for f in files:
        if not f.exists():
            print(f"  {f}: not found", file=sys.stderr)
            continue
        unused = check_file(f)
        if unused:
            try:
                rel = str(f.relative_to(PROJECT_ROOT))
            except ValueError:
                rel = str(f)
            for lineno, name in unused:
                print(f"  {rel}:{lineno}: unused private `{name}`")
            total_unused += len(unused)

    if total_unused:
        print(f"\n  {total_unused} unused private declaration(s) found.")
        return 1
    else:
        print("  No unused private declarations found.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
