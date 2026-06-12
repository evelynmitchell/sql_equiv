#!/usr/bin/env python3
"""
Spider evaluate-rate baseline (north-star metric, stage 2 — #225).

For every (db, query) pair in the dev corpus, builds the schema from
benchmarks/spider/dev_tables.json, populates small DETERMINISTIC synthetic
data (FK-aware so joins discriminate), evaluates the query with our engine
(sql_equiv --spider-eval) and with sqlite3 (in-process — the Spider-fidelity
oracle per the role split on #225), and compares result multisets.

Failure classes become issues; the agree-count is ratcheted in
tools/spider_eval_minimum.txt.

Usage:
    python3 tools/spider_eval_baseline.py            # report + ratchet check
    python3 tools/spider_eval_baseline.py --check    # ratchet check only (CI)
    python3 tools/spider_eval_baseline.py --update-ratchet

Stdlib only (CI runs plain python3; sqlite3 is stdlib).
"""

from __future__ import annotations

import json
import re
import sqlite3
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TABLES = ROOT / "benchmarks" / "spider" / "dev_tables.json"
QUERIES = ROOT / "benchmarks" / "spider" / "dev_queries.jsonl"
REPORT = ROOT / "benchmarks" / "spider" / "eval_report.md"
RATCHET = ROOT / "tools" / "spider_eval_minimum.txt"
EXE = ROOT / ".lake" / "build" / "bin" / "sql_equiv"

N_ROWS = 5


def gen_value(ti: int, ci: int, r: int, ctype: str, is_pk: bool, is_fk: bool):
    """Deterministic synthetic cell. PKs are 1..N (so FKs can reference them);
    FKs cycle 1..N; NULLs appear on row 3 for some non-key columns."""
    if is_pk:
        return r + 1
    if is_fk:
        return (r % N_ROWS) + 1
    if r == 3 and (ci + ti) % 3 == 0:
        return None
    if ctype == "number":
        return (r * 7 + ci * 3 + ti) % 40 + r
    if ctype == "boolean":
        return r % 2
    if ctype == "time":
        return f"202{r % 3}-0{(ci % 9) + 1}-1{r % 5}"
    return f"t{ti}c{ci}r{r % 3}"  # text/others; repeats every 3 rows for GROUP BY


def build_db(schema: dict):
    """Returns (tables, rows): tables = [(name, [colnames])], rows[name] = [[cells]]"""
    names = schema["table_names_original"]
    cols = schema["column_names_original"]  # [table_idx, name], idx 0 is (-1, '*')
    types = schema["column_types"]
    pks = set(schema.get("primary_keys", []))
    fks = {a for a, _ in schema.get("foreign_keys", [])}
    per_table: dict[int, list[tuple[int, str, str]]] = defaultdict(list)
    for idx, (ti, cname) in enumerate(cols):
        if ti >= 0:
            per_table[ti].append((idx, cname, types[idx]))
    tables, rows = [], {}
    for ti, tname in enumerate(names):
        if tname.lower().startswith("sqlite_"):
            continue  # AUTOINCREMENT artifact leaked into tables.json; reserved in sqlite
        tcols = per_table[ti]
        tables.append((tname, [c for _, c, _ in tcols]))
        rows[tname] = [
            [gen_value(ti, idx, r, ctype, idx in pks, idx in fks)
             for idx, _, ctype in tcols]
            for r in range(N_ROWS)
        ]
    return tables, rows


def sqlite_for(schema: dict, tables, rows) -> sqlite3.Connection:
    conn = sqlite3.connect(":memory:")
    types = schema["column_types"]
    cols = schema["column_names_original"]
    per_table_types: dict[str, list[str]] = {}
    ti_of = {t: i for i, t in enumerate(schema["table_names_original"])}
    for tname, colnames in tables:
        ti = ti_of[tname]
        ctypes = [types[i] for i, (t, _) in enumerate(cols) if t == ti]
        decls = ", ".join(
            f'"{c}" {"INTEGER" if ty in ("number", "boolean") else "TEXT"}'
            for c, ty in zip(colnames, ctypes))
        conn.execute(f'CREATE TABLE "{tname}" ({decls})')
        ph = ", ".join("?" * len(colnames))
        conn.executemany(f'INSERT INTO "{tname}" VALUES ({ph})', rows[tname])
    return conn


def cell_str(v) -> str:
    if v is None:
        return "NULL"
    if isinstance(v, float):
        return f"{v:.10g}"
    return str(v)


def normalize(rows_) -> Counter:
    return Counter(tuple(cell_str(c) for c in row) for row in rows_)


def classify_query(sql: str) -> str:
    """Feature signature for failure grouping."""
    u = sql.upper()
    feats = [k for k in ("JOIN", "GROUP BY", "HAVING", "ORDER BY", "AVG", "SUM(",
                         "COUNT", "INTERSECT", "UNION", "EXCEPT", "LIKE",
                         "DISTINCT", "BETWEEN") if k in u]
    return "+".join(feats[:3]) if feats else "plain SELECT"


def main() -> None:
    check_only = "--check" in sys.argv
    update = "--update-ratchet" in sys.argv
    if not EXE.exists():
        sys.exit(f"error: {EXE} not built — run `lake build sql_equiv` first")

    schemas = {s["db_id"]: s for s in json.load(open(TABLES))}
    pairs = [json.loads(l) for l in open(QUERIES)]

    # Build manifest for our engine + sqlite connections
    manifest_lines = []
    conns: dict[str, sqlite3.Connection] = {}
    for db_id, schema in schemas.items():
        tables, rows = build_db(schema)
        conns[db_id] = sqlite_for(schema, tables, rows)
        manifest_lines.append(f"#DB {db_id}")
        for tname, colnames in tables:
            manifest_lines.append(f"#TABLE {tname}")
            manifest_lines.append("|".join(colnames))
            for row in rows[tname]:
                manifest_lines.append("|".join(cell_str(c) for c in row))
    for p in pairs:
        manifest_lines.append(f"#QUERY {p['db']}")
        manifest_lines.append(p["query"])

    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("\n".join(manifest_lines) + "\n")
        manifest_path = f.name

    out = subprocess.run([str(EXE), "--spider-eval", manifest_path],
                         capture_output=True, text=True, check=True).stdout

    # Parse our results
    ours: dict[int, tuple[str, list]] = {}
    cur, cur_rows = None, []
    for line in out.splitlines():
        m = re.match(r"#RESULT (\d+) (ok|err ?(.*))", line)
        if m:
            if cur is not None and cur not in ours:
                ours[cur] = ("ok", cur_rows)
            idx = int(m.group(1))
            if m.group(2) == "ok":
                cur, cur_rows = idx, []
            else:
                ours[idx] = ("err", m.group(3) or "error")
                cur = None
        elif line == "#END":
            if cur is not None:
                ours[cur] = ("ok", cur_rows)
                cur = None
        elif cur is not None:
            cur_rows.append(line.split("|"))

    agree = 0
    failures: dict[str, list[tuple[str, str]]] = defaultdict(list)
    oracle_err = 0
    for i, p in enumerate(pairs, start=1):
        try:
            sq_rows = conns[p["db"]].execute(p["query"]).fetchall()
        except sqlite3.Error as e:
            oracle_err += 1
            failures[f"oracle-error: {type(e).__name__}"].append((p["query"], str(e)))
            continue
        status, payload = ours.get(i, ("err", "missing output"))
        if status == "err":
            failures[f"ours-error: {classify_query(p['query'])}"].append(
                (p["query"], str(payload)))
            continue
        if normalize(payload) == normalize(sq_rows):
            agree += 1
        else:
            failures[f"mismatch: {classify_query(p['query'])}"].append(
                (p["query"], f"ours {len(payload)} rows vs sqlite {len(sq_rows)} rows"))

    total = len(pairs) - oracle_err
    rate = 100.0 * agree / total if total else 0.0
    if not check_only:
        lines = [
            "# Spider Dev-Set Evaluate Report",
            "",
            "Generated by `tools/spider_eval_baseline.py` — do not edit by hand.",
            "",
            f"**Evaluate-agreement rate vs sqlite (Spider-fidelity oracle): "
            f"{agree}/{total} ({rate:.1f}%)** "
            f"({oracle_err} queries errored on the oracle and are excluded)",
            "",
            "Deterministic synthetic data (5 rows/table, FK-aware) over the dev",
            "schemas; multiset comparison of result rows.",
            "",
            "## Failure classes (largest first)",
            "",
            "| Count | Class | Example query | Detail |",
            "|------:|-------|---------------|--------|",
        ]
        for cls, items in sorted(failures.items(), key=lambda kv: -len(kv[1])):
            q, d = items[0]
            q = (q[:70] + "…") if len(q) > 70 else q
            lines.append(f"| {len(items)} | {cls} | `{q}` | {d[:60]} |")
        REPORT.write_text("\n".join(lines) + "\n")
        print(f"Evaluate-agreement: {agree}/{total} ({rate:.1f}%) — report: {REPORT}")

    minimum = int(RATCHET.read_text().strip()) if RATCHET.exists() else 0
    if update or not RATCHET.exists():
        RATCHET.write_text(f"{agree}\n")
        print(f"Ratchet set to {agree}")
        return
    if agree < minimum:
        sys.exit(f"FAIL: Spider evaluate-agreement regressed: {agree} < ratchet {minimum}")
    print(f"Ratchet check passed: {agree} >= {minimum}")


if __name__ == "__main__":
    main()
