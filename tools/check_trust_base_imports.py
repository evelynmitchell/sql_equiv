#!/usr/bin/env python3
"""
The trust-base tests assert "no sorry, no extra axioms" over the modules they import. A proof
file they do not import is not checked at all, and the assertion stays green (this happened to
four `SqlBridge/Correct*.lean` files until 21 Nov 2026).

This check fails when a library module that holds proofs is not imported by its trust-base
test:
  - every `SqlBridge/*.lean` except the executables' `*Main.lean` must be imported by
    `SqlCoreTest/TrustBaseTest.lean`.

Usage: python3 tools/check_trust_base_imports.py
Stdlib only.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECKS = [
    (ROOT / "SqlBridge", "SqlBridge", ROOT / "SqlCoreTest" / "TrustBaseTest.lean"),
]


def main() -> None:
    errors: list[str] = []
    for src_dir, prefix, test in CHECKS:
        imported = set(re.findall(r"^import\s+(\S+)", test.read_text(encoding="utf-8"), re.M))
        modules = sorted(
            f"{prefix}.{p.stem}" for p in src_dir.glob("*.lean") if not p.stem.endswith("Main")
        )
        if len(modules) < 5:
            errors.append(f"only {len(modules)} modules found under {src_dir} (wrong directory?)")
        for m in modules:
            if m not in imported:
                errors.append(f"{m} is not imported by {test.relative_to(ROOT)}")
    if errors:
        sys.exit("Trust-base import check FAILED:\n  " + "\n  ".join(errors))
    print("Trust-base import check passed")


if __name__ == "__main__":
    main()
