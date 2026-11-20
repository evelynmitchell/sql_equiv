#!/usr/bin/env python3
"""
Spider elaboration-rate baseline for the typed core (#295, phase 6).

Runs every Spider dev query (benchmarks/spider/dev_queries.jsonl) through the
parser and the typed-core elaborator (`lake exe spider_elab`) against its
database's schema (benchmarks/spider/dev_tables.json), and reports what
fraction elaborates into `SqlCore.Query`. The failure classes are the work
list of phase 8 (#297): each unsupported construct is a candidate extension.

The elaborating count is ratcheted in tools/spider_elab_minimum.txt: CI fails
if it regresses. When the fragment grows, run with --update-ratchet.

Usage:
    python3 tools/spider_elab_baseline.py            # report + ratchet check
    python3 tools/spider_elab_baseline.py --check    # ratchet check only (CI)
    python3 tools/spider_elab_baseline.py --update-ratchet

Stdlib only (CI runs plain python3).
"""

from __future__ import annotations

import json
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
QUERIES = ROOT / "benchmarks" / "spider" / "dev_queries.jsonl"
TABLES = ROOT / "benchmarks" / "spider" / "dev_tables.json"
REPORT = ROOT / "benchmarks" / "spider" / "elab_report.md"
RATCHET = ROOT / "tools" / "spider_elab_minimum.txt"
EXE = ROOT / ".lake" / "build" / "bin" / "spider_elab"


# Elaborator-correctness roadmap (#352, docs/TYPED_CORE_PLAN.md): each step lifts the features
# it names (`SqlBridge.Coverage`) into the theorem's fragment. Step 0 (#351, done) let the
# theorem apply to Spider's case-folding schemas at all; steps 1 (ORDER BY / LIMIT), 2 (inner
# and cross joins), 3a (aggregates without GROUP BY, AVG aside) and 3b-1 (GROUP BY columns,
# items keys or aggregates) are done and counted in "Today".
ROADMAP = [
    # On Spider, every non-column ORDER BY key and every unaliased item next to an ORDER BY is an
    # aggregate (`ORDER BY count(*)`, `SELECT x, count(*) … ORDER BY …`): step 3 extends step 1's
    # key resolution to them.
    ("3b-2..4. HAVING, ordered by aggregates, bare columns",
     {"aggregate/GROUP BY", "ORDER BY expression", "unnamed item with ORDER BY"}),
    ("4. IS NULL, negation, arithmetic, IN list, BETWEEN",
     {"IS NULL/negation", "arithmetic", "IN list/BETWEEN"}),
    ("5. DISTINCT", {"DISTINCT"}),
]


def run() -> tuple[int, int, dict[str, list[str]], list[set[str]]]:
    if not EXE.exists():
        sys.exit(f"error: {EXE} not built — run `lake build spider_elab` first")
    queries = [json.loads(l) for l in QUERIES.read_text().splitlines() if l.strip()]
    out = subprocess.run(
        [str(EXE), str(TABLES), str(QUERIES)], capture_output=True, text=True, check=True
    ).stdout.splitlines()
    if len(out) != len(queries):
        sys.exit(f"error: {len(out)} results for {len(queries)} queries")
    ok, failures, features = 0, defaultdict(list), []
    for line, q in zip(out, queries):
        if line == "ok" or line.startswith("ok\t"):
            ok += 1
            rest = line.split("\t", 1)[1] if "\t" in line else ""
            features.append({f for f in rest.split(",") if f})
        else:
            cls = line.split("\t", 1)[1] if "\t" in line else line
            failures[cls].append(f"[{q['db']}] {q['query']}")
    return ok, len(queries), failures, features


def coverage_lines(features: list[set[str]]) -> list[str]:
    """The coverage section: elaborated queries in the correctness theorem's fragment today and
    after each roadmap step (cumulative), and what keeps the rest out."""
    now = sum(1 for f in features if not f)
    lines = [
        "## Elaborator-correctness coverage (#352)",
        "",
        "`elabStmt_correct_join` (`SqlBridge/CorrectJoin.lean`) proves that an elaborated",
        "query's typed result rows match the untyped evaluator's, in order, for",
        "`SELECT e₁, …, eₖ FROM f [WHERE p] [ORDER BY c₁, …] [LIMIT n] [OFFSET m]`, `f` tables",
        "under inner joins and cross joins, with literals, columns, comparisons, `AND`, `OR`, `NOT`,",
        "column `ORDER BY` keys, and (with an `ORDER BY`) items that are columns or have an",
        "alias; `elabStmt_correct_agg` (`SqlBridge/CorrectAgg.lean`) does for",
        "`SELECT agg₁, …, aggₖ FROM f [WHERE p]` with `COUNT`, `COUNT(DISTINCT)`, `SUM`, `MIN`,",
        "`MAX` (not `AVG`, pending its rounding decision), and `elabStmt_correct_group`",
        "(`SqlBridge/CorrectGroup.lean`) for the same `GROUP BY` columns, each item a key column or",
        "such an aggregate. Counts are of the elaborated",
        "queries with that shape (`SqlBridge.Coverage.outsideFragment`); roadmap and reasoning in",
        "`docs/TYPED_CORE_PLAN.md`. The theorem covers Spider's schemas, which fold names to",
        "lowercase (#351), given that the untyped database answers every spelling of a table name",
        "alike (as the evaluate harness's lowercasing does) and nothing orders booleans.",
        "",
        "| Step | Queries in the fragment |",
        "|------|------------------------:|",
        f"| Today | {now} |",
    ]
    lifted: set[str] = set()
    for name, feats in ROADMAP:
        lifted |= feats
        lines.append(f"| after {name} | {sum(1 for f in features if f <= lifted)} |")
    rest = defaultdict(int)
    for f in features:
        for x in f - lifted:
            rest[x] += 1
    lines += ["", "Still outside after step 5 (queries using each feature):", ""]
    lines += [f"- {x}: {c}" for x, c in sorted(rest.items(), key=lambda kv: -kv[1])]
    return lines + [""]


def write_report(ok: int, total: int, failures: dict, features: list[set[str]]) -> None:
    rate = 100.0 * ok / total if total else 0.0
    lines = [
        "# Spider Dev-Set Elaboration Report (typed core)",
        "",
        "Generated by `tools/spider_elab_baseline.py` — do not edit by hand.",
        "",
        f"**Elaboration rate: {ok}/{total} queries ({rate:.1f}%)** elaborate into `SqlCore.Query`",
        "(parsed, names resolved, well-typed).",
        "",
        "Queries are parsed in the `sqlite` dialect (Spider's gold results come from sqlite), as in",
        "`tools/spider_eval_baseline.py`.",
        "",
        "Schemas come from `dev_tables.json`: names are lowercased and references folded to",
        "lowercase (sqlite names are case-insensitive), `number` columns are `int`, `text`/`time`/",
        "`others` are `text`. A `typeError` is a query that is ill-typed under the declared column",
        "types (sqlite accepts it through type affinity, e.g. a `text` column compared with `32`).",
        "",
        *coverage_lines(features),
        "## Failure classes (largest first)",
        "",
        "| Count | Class | Example (first occurrence) |",
        "|------:|-------|----------------------------|",
    ]
    for cls, items in sorted(failures.items(), key=lambda kv: -len(kv[1])):
        example = items[0]
        example = (example[:100] + "…") if len(example) > 100 else example
        example = example.replace("|", "\\|")
        lines.append(f"| {len(items)} | {cls} | `{example}` |")
    REPORT.write_text("\n".join(lines) + "\n")


def main() -> None:
    check_only = "--check" in sys.argv
    update = "--update-ratchet" in sys.argv
    ok, total, failures, features = run()
    if not check_only:
        write_report(ok, total, failures, features)
        print(f"Elaboration rate: {ok}/{total} ({100.0 * ok / total:.1f}%) — report: {REPORT}")
    minimum = int(RATCHET.read_text().strip()) if RATCHET.exists() else 0
    if update or not RATCHET.exists():
        RATCHET.write_text(f"{ok}\n")
        print(f"Ratchet set to {ok}")
        return
    if ok < minimum:
        sys.exit(f"FAIL: Spider elaboration count regressed: {ok} < ratchet {minimum}")
    print(f"Ratchet check passed: {ok} >= {minimum}")


if __name__ == "__main__":
    main()
