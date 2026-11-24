#!/usr/bin/env python3
"""
Typed-core coverage of the test corpus (#458, phase 9.0).

Phase 9 ports to the typed core every feature the untyped evaluator has; Spider cannot
measure that (its queries use none of the missing features). This tool collects the SQL
strings of the unit tests (`Test/*.lean`) and of the differential suites
(`LSpecTests/Diff*.lean`), runs each through the parser and the typed-core elaborator
(`lake exe spider_elab`) against the test schema below, and reports how many elaborate into
`SqlCore.Query`, with the failure classes: each `unsupported: …` class is work for a phase 9
step.

A string is parsed in its file's dialect (DiffSqlite: sqlite, DiffDuckdb: duckdb,
DiffPostgres: postgres); in `Test/`, in the dialect named on its line or the line before
(`.sqlite`, `.duckdb`, `.postgres`), else `standard`. Not every string is a query to
elaborate, so the report keeps these apart and leaves them out of the rate:
- parse errors: tests of rejections, and strings in another dialect than guessed;
- unknown tables or columns: parser tests over tables that are not in the test schema, and
  tests of missing columns.

The elaborating count is ratcheted in tools/typed_corpus_minimum.txt.

Usage:
    python3 tools/typed_corpus_baseline.py            # report + ratchet check
    python3 tools/typed_corpus_baseline.py --check    # ratchet check only (CI)
    python3 tools/typed_corpus_baseline.py --update-ratchet

Stdlib only.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "spider_elab"
REPORT = ROOT / "benchmarks" / "typed_corpus" / "report.md"
RATCHET = ROOT / "tools" / "typed_corpus_minimum.txt"

# The tables of the test databases (Test/SemanticsTest.lean `testDb`, LSpecTests/QueryHelpers,
# the Diff* suites, the rewriter sweep), with the column types of the typed transcription
# (SqlCoreTest/SchemaExamples.lean) where it has the table.
SCHEMA: dict[str, list[tuple[str, str]]] = {
    "users": [("id", "number"), ("name", "text"), ("age", "number"), ("department", "text")],
    "orders": [("id", "number"), ("user_id", "number"), ("amount", "number"), ("product", "text")],
    "products": [("id", "number"), ("name", "text"), ("price", "number")],
    "items": [("id", "number"), ("name", "text"), ("price", "decimal")],
    "singer": [("Singer_ID", "number"), ("Name", "text"), ("Country", "text"), ("Age", "number")],
    "museum": [("name", "text"), ("staff", "number")],
    "dups": [("x", "number")],
    "other": [("x", "number")],
    "Été": [("Élan", "number"), ("日本", "number")],
    "t": [("a", "number")],
}

SOURCES = sorted((ROOT / "Test").glob("*.lean")) + sorted((ROOT / "LSpecTests").glob("Diff*.lean"))
FILE_DIALECT = {"DiffSqlite.lean": "sqlite", "DiffDuckdb.lean": "duckdb", "DiffPostgres.lean": "postgres"}

# A Lean string literal that starts like a SQL statement.
SQL_RE = re.compile(r'"((?:SELECT|WITH|INSERT|UPDATE|DELETE)\s(?:[^"\\]|\\.)*)"', re.I)
DIALECT_RE = re.compile(r"\.(sqlite|duckdb|postgres)\b")


def unescape(s: str) -> str:
    return s.replace('\\"', '"').replace("\\n", " ").replace("\\\\", "\\")


def corpus() -> list[tuple[str, str]]:
    """Distinct (dialect, sql) pairs, in order of first appearance."""
    seen: dict[tuple[str, str], None] = {}
    for path in SOURCES:
        lines = path.read_text(encoding="utf-8").split("\n")
        for i, line in enumerate(lines):
            if line.lstrip().startswith("--"):
                continue
            for m in SQL_RE.finditer(line):
                sql = unescape(m.group(1)).strip().rstrip(";")
                if "{" in sql:      # an interpolated s!"…" template, not a query
                    continue
                d = FILE_DIALECT.get(path.name)
                if d is None:
                    here = DIALECT_RE.search(line) or (DIALECT_RE.search(lines[i - 1]) if i else None)
                    d = here.group(1) if here else "standard"
                seen.setdefault((d, sql))
    return list(seen)


def _self_test() -> None:
    m = SQL_RE.search('  testX "n" .sqlite "SELECT a, \\"b\\" FROM t" 3,')
    assert m and unescape(m.group(1)) == 'SELECT a, "b" FROM t', m
    assert SQL_RE.search('"selected rows"') is None
    assert SQL_RE.search('"Select-level relations"') is None


def tables_json() -> dict:
    names = list(SCHEMA)
    cols = [[-1, "*"]] + [[ti, c] for ti, t in enumerate(names) for c, _ in SCHEMA[t]]
    types = ["text"] + [ty for t in names for _, ty in SCHEMA[t]]
    return {"db_id": "test", "table_names_original": names,
            "column_names_original": cols, "column_types": types}


def run() -> tuple[list[tuple[str, str, str]], int]:
    """(dialect, sql, outcome) per corpus entry; outcome is `ok` or the failure class."""
    if not EXE.exists():
        sys.exit(f"error: {EXE} not built — run `lake build spider_elab` first")
    qs = corpus()
    with tempfile.TemporaryDirectory() as d:
        tp, qp = Path(d) / "tables.json", Path(d) / "queries.jsonl"
        tp.write_text(json.dumps([tables_json()]))
        qp.write_text("".join(json.dumps({"db": "test", "query": q, "dialect": dl}) + "\n"
                              for dl, q in qs))
        out = subprocess.run([str(EXE), str(tp), str(qp)], capture_output=True, text=True,
                             check=True).stdout.splitlines()
    if len(out) != len(qs):
        sys.exit(f"error: {len(qs)} queries but {len(out)} result lines")
    res = []
    for (dl, q), line in zip(qs, out):
        status, _, rest = line.partition("\t")
        res.append((dl, q, "ok" if status == "ok" else rest))
    return res, len(qs)


APART = ("parse error", "unknownTable", "unknownColumn", "ambiguousColumn")


def main() -> None:
    _self_test()
    check_only = "--check" in sys.argv
    update = "--update-ratchet" in sys.argv
    res, total = run()
    ok = sum(1 for _, _, o in res if o == "ok")
    classes: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for dl, q, o in res:
        if o != "ok":
            classes[o].append((dl, q))
    apart = sum(len(v) for c, v in classes.items() if c in APART)
    counted = total - apart
    rate = 100.0 * ok / counted if counted else 0.0
    if not check_only:
        lines = [
            "# Typed-Core Coverage of the Test Corpus",
            "",
            "Generated by `tools/typed_corpus_baseline.py` (#458) — do not edit by hand.",
            "",
            f"**{ok}/{counted} statements ({rate:.1f}%) elaborate into the typed core**, of the "
            f"{total} distinct SQL strings in `Test/*.lean` and `LSpecTests/Diff*.lean`.",
            "",
            f"Left out of the rate ({apart}): strings the parser rejects in the guessed dialect "
            "(tests of rejections), and strings over tables or columns that are not in the test "
            "schema (parser tests, tests of missing columns).",
            "",
            "## Classes (largest first)",
            "",
            "| Count | Class | Counted | Example |",
            "|------:|-------|:-------:|---------|",
        ]
        for c, items in sorted(classes.items(), key=lambda kv: -len(kv[1])):
            dl, q = items[0]
            q = (q[:90] + "…") if len(q) > 90 else q
            lines.append(f"| {len(items)} | {c} | {'no' if c in APART else 'yes'} | `{q}` ({dl}) |")
        REPORT.parent.mkdir(parents=True, exist_ok=True)
        REPORT.write_text("\n".join(lines) + "\n")
        print(f"Typed corpus: {ok}/{counted} elaborate ({rate:.1f}%); {apart} left out — report: {REPORT}")
    minimum = int(RATCHET.read_text().strip()) if RATCHET.exists() else 0
    if update or not RATCHET.exists():
        RATCHET.write_text(f"{ok}\n")
        print(f"Ratchet set to {ok}")
        return
    if ok < minimum:
        sys.exit(f"FAIL: typed-corpus elaboration regressed: {ok} < ratchet {minimum}")
    print(f"Ratchet check passed: {ok} >= {minimum}")


if __name__ == "__main__":
    main()
