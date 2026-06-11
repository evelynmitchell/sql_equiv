#!/usr/bin/env python3
"""
Convert LSpec runner stdout into per-test JSONL (#209).

The LSpec executable prints suite headers followed by indented result lines
("✓ name" / "×/✗ name"). This converts a captured log into the same JSONL
shape the unit runner emits via TEST_RESULTS_JSON:
    {"suite": ..., "name": ..., "pass": ...}

Usage: python3 tools/lspec_results_to_json.py <lspec-stdout.log> <out.jsonl>

Stdlib only (CI runs plain python3).
"""

from __future__ import annotations

import json
import re
import sys


def convert(log_path: str, out_path: str) -> int:
    suite = "unknown"
    count = 0
    result_re = re.compile(r"^\s*([✓×✗x])\*?\s+(.*\S)\s*$")
    with open(log_path, encoding="utf-8") as log, open(out_path, "w", encoding="utf-8") as out:
        for line in log:
            line = line.rstrip("\n")
            m = result_re.match(line)
            if m:
                mark, name = m.groups()
                out.write(json.dumps(
                    {"suite": suite, "name": name, "pass": mark == "✓"},
                    ensure_ascii=False) + "\n")
                count += 1
            elif line and not line.startswith((" ", "\t", "─", "═", "Running")):
                suite = line.strip().rstrip(":")
    return count


def main() -> None:
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    n = convert(sys.argv[1], sys.argv[2])
    print(f"Wrote {n} test results to {sys.argv[2]}")
    if n == 0:
        sys.exit("error: no test results found in log — format drift?")


if __name__ == "__main__":
    main()
