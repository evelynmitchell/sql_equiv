#!/usr/bin/env python3
"""
Spider evaluate-rate baseline (north-star metric, stage 2 — #225).

For every (db, query) pair in the dev corpus, builds the schema from
benchmarks/spider/dev_tables.json, populates small DETERMINISTIC synthetic
data (FK-aware so joins discriminate), evaluates the query with our engine
(sql_equiv --spider-eval) and with sqlite3 (in-process — the Spider-fidelity
oracle per the role split on #225), and compares result multisets. Each
disagreement is cross-checked on DuckDB (the `duckdb` CLI, same data): when
DuckDB rejects the query or disagrees with sqlite, Postgres (`psql`, same
data) breaks the tie: if it gives sqlite's answer the query is a failure of
ours ("tiebroken against ours"); otherwise it is labelled "engine-divergent"
and is not a failure of ours (still not counted as agreement).

Failure classes become issues. Two counts are ratcheted (#266), and CI fails if either drops:
- exact multiset matches, in tools/spider_eval_exact_minimum.txt (the headline);
- the combined agree-count, in tools/spider_eval_minimum.txt: exact matches plus
  "tie-valid" answers (`ORDER BY … LIMIT n` where the cutoff falls inside a tie and our rows
  are a valid tie-break, see `tie_valid`, guarded by a self-test that runs on every
  invocation) plus "TEXT-affinity emulated" matches (#235).

Usage:
    python3 tools/spider_eval_baseline.py            # report + ratchet check
    python3 tools/spider_eval_baseline.py --check    # ratchet check only (CI)
    python3 tools/spider_eval_baseline.py --update-ratchet
    python3 tools/spider_eval_baseline.py --stress=8   # also: seeded data variants, report only

Stdlib only (CI runs plain python3; sqlite3 is stdlib).
"""

from __future__ import annotations

import json
import os
import random
import shutil
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
EXACT_RATCHET = ROOT / "tools" / "spider_eval_exact_minimum.txt"
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


def gen_value_varied(rng, ctype: str, is_pk_row: int | None, is_fk: bool):
    """A stress-variant cell (`--stress`): duplicates, negatives, zeros and NULLs anywhere
    outside primary keys; foreign keys may dangle or be NULL."""
    if is_pk_row is not None:
        return is_pk_row + 1
    if is_fk:
        return None if rng.random() < 0.1 else rng.randint(1, 7)
    if rng.random() < 0.2:
        return None
    if ctype == "number":
        return rng.choice([0, 1, 1, 2, -3, 5, 5, 8, 13, 40, -1, 100])
    if ctype == "boolean":
        return rng.randint(0, 1)
    if ctype == "time":
        return f"202{rng.randint(0, 3)}-0{rng.randint(1, 9)}-1{rng.randint(0, 9)}"
    return f"v{rng.randint(0, 3)}"  # small pool: many duplicates for GROUP BY / DISTINCT


def build_db(schema: dict, variant: int = 0):
    """Returns (tables, rows): tables = [(name, [colnames])], rows[name] = [[cells]].
    Variant 0 is the fixed, ratcheted data. Variants 1.. (`--stress`) are seeded by
    (db_id, variant): each table gets 0–8 rows and `gen_value_varied` cells."""
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
        if variant == 0:
            rows[tname] = [
                [gen_value(ti, idx, r, ctype, idx in pks, idx in fks)
                 for idx, _, ctype in tcols]
                for r in range(N_ROWS)
            ]
        else:
            rng = random.Random(f"{schema['db_id']}:{tname}:{variant}")
            n = rng.choice([0, 1, 2, 3, 5, 8])
            rows[tname] = [
                [gen_value_varied(rng, ctype, r if idx in pks else None, idx in fks)
                 for idx, _, ctype in tcols]
                for r in range(n)
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


_DEC = re.compile(r"-?\d+\.\d+")


def cell_str(v) -> str:
    """A cell as compared: sqlite floats and our decimals (`AVG` is exact or rounded to 16
    places, registry row 7) both to 10 significant digits."""
    if v is None:
        return "NULL"
    if isinstance(v, float):
        return f"{v:.10g}"
    if isinstance(v, str) and _DEC.fullmatch(v):
        return f"{float(v):.10g}"
    return str(v)


def normalize(rows_) -> Counter:
    return Counter(tuple(cell_str(c) for c in row) for row in rows_)


_TAIL = re.compile(
    r"(?is)^\s*select\s+(?P<cols>.*?)\s+from\s+(?P<rest>.*)\s+order\s+by\s+"
    r"(?P<ob>.*?)\s+limit\s+(?P<n>\d+)\s*;?\s*$")


def _split_top_level(s: str) -> list[str]:
    """Split on commas that are not inside parentheses."""
    parts, depth, cur = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return [p.strip() for p in parts]


def tie_valid(conn: sqlite3.Connection, query: str, ours_rows: list, sq_rows: list) -> bool:
    """True when a mismatch is only a tie-break difference (#234 follow-up).

    For a query ending in a top-level `ORDER BY k1[, k2…] LIMIT n` (no
    DISTINCT, no set operation), sqlite's rows are re-fetched with the sort
    keys prepended and without the LIMIT. Our result is a valid answer iff it
    has the same row count and consists of every row sorting strictly before
    the cutoff key plus some choice of rows tied at the cutoff. A NULL key at
    the cutoff is NOT accepted (that is the NULL-ordering divergence, a real
    difference), and any probe error counts as a real mismatch.
    """
    if not ours_rows or len(ours_rows) != len(sq_rows):
        return False
    m = _TAIL.match(query)
    if not m:
        return False
    cols, rest, ob, n = m.group("cols"), m.group("rest"), m.group("ob"), int(m.group("n"))
    if re.match(r"(?i)distinct\b", cols.strip()) or re.search(
            r"(?i)\b(union|intersect|except)\b", rest):
        return False
    keys = [re.sub(r"(?i)\s+(asc|desc)$", "", k) for k in _split_top_level(ob)]
    # A positional key (`ORDER BY 1`) would be re-selected as a constant,
    # making every row look tied; never accept those.
    if any(re.fullmatch(r"\d+", k) for k in keys):
        return False
    try:
        full = conn.execute(
            f"SELECT {', '.join(keys)}, {cols} FROM {rest} ORDER BY {ob}").fetchall()
    except sqlite3.Error:
        return False
    if len(full) < n:
        return False
    nk = len(keys)
    cut = tuple(full[n - 1][:nk])
    if any(v is None for v in cut):
        return False
    payload = lambda r: tuple(cell_str(c) for c in r[nk:])
    strict = Counter(payload(r) for r in full[:n] if tuple(r[:nk]) != cut)
    tied = Counter(payload(r) for r in full if tuple(r[:nk]) == cut)
    ours = Counter(tuple(r) for r in ours_rows)
    if strict - ours:          # every strictly-better row must be present
        return False
    return not ((ours - strict) - tied)   # the rest must come from the tied rows


def _self_test_tie_valid() -> None:
    """Guards the tie classifier against accepting wrong answers. Runs on
    every invocation (including CI's --check); cheap, in-memory sqlite."""
    c = sqlite3.connect(":memory:")
    c.execute("CREATE TABLE t (name TEXT, k INTEGER)")
    c.executemany("INSERT INTO t VALUES (?, ?)",
                  [("a", 1), ("b", 2), ("c", 2), ("d", 3), ("e", None)])
    q1 = "SELECT name FROM t WHERE k IS NOT NULL ORDER BY k DESC LIMIT 1"
    q2 = "SELECT name FROM t WHERE k IS NOT NULL ORDER BY k LIMIT 2"
    sq2 = c.execute(q2).fetchall()                      # a, then b or c
    cases = [
        # (description, query, ours, expected)
        ("tied row is a valid tie-break", q2, [["a"], ["c"]], True),
        ("missing the strictly-better row", q2, [["b"], ["c"]], False),
        ("non-tie: wrong row", q1, [["b"]], False),
        ("row from outside the tie", q2, [["a"], ["d"]], False),
        ("NULL key at the cutoff", "SELECT name FROM t ORDER BY k LIMIT 1", [["a"]], False),
        ("DISTINCT is not analysed",
         "SELECT DISTINCT name FROM t WHERE k IS NOT NULL ORDER BY k LIMIT 2",
         [["a"], ["c"]], False),
        ("empty result is never a tie", q2, [], False),
        ("positional ORDER BY is not analysed",
         "SELECT name FROM t WHERE k IS NOT NULL ORDER BY 1 LIMIT 2", [["d"], ["c"]], False),
    ]
    for desc, q, ours, expected in cases:
        sq = sq2 if q == q2 else c.execute(q).fetchall()
        got = tie_valid(c, q, ours, sq)
        if got != expected:
            sys.exit(f"FAIL: tie_valid self-test '{desc}': expected {expected}, got {got}")


# --------------------------------------------------------------------------
# TEXT-affinity emulation (#235, option A)
# --------------------------------------------------------------------------
# sqlite compares a TEXT-affinity column with a numeric literal by converting
# the literal to text (`year >= 2014` compares `year` with '2014' as strings).
# Our engine keeps strict typing (string vs number is a type error, see
# docs/IMPLEMENTATION_DEFINED.md rows 10 and 12), so for OUR engine only the
# harness rewrites such comparisons to `year >= '2014'`, which is exactly the
# comparison sqlite performs. sqlite still runs the original query. Matches
# that depend on the rewrite are reported as their own category.

_CMP = r"(=|!=|<>|>=|<=|>|<)"
_NUM = r"-?\d+(?:\.\d+)?"
_COL_NUM = re.compile(r"(?<![\w'\".])((?:\w+\.)?(\w+))\s*" + _CMP + r"\s*(" + _NUM + r")(?![\w.])")
_NUM_COL = re.compile(r"(?<![\w'\".])(" + _NUM + r")\s*" + _CMP + r"\s*((?:\w+\.)?(\w+))(?![\w.(])")


def text_affinity_columns(schema: dict, tables, rows) -> set[str]:
    """Lower-cased column names whose comparisons with a number can be
    emulated: in EVERY table of the database that has a column of that name,
    it has TEXT affinity (declared TEXT by sqlite_for) and all its non-NULL
    synthetic values are non-numeric strings (our manifest shape-parses
    numeric-looking cells as numbers, so those columns are left alone)."""
    ok: dict[str, bool] = {}
    for tname, colnames in tables:
        for ci, cname in enumerate(colnames):
            vals = [r[ci] for r in rows[tname] if r[ci] is not None]
            good = bool(vals) and all(
                isinstance(v, str) and not re.fullmatch(_NUM, v) for v in vals)
            key = cname.lower()
            ok[key] = ok.get(key, True) and good
    return {k for k, v in ok.items() if v}


def _string_spans(sql: str) -> list[tuple[int, int]]:
    return [m.span() for m in re.finditer(r"'(?:[^']|'')*'|\"[^\"]*\"", sql)]


def emulate_text_affinity(sql: str, text_cols: set[str]) -> str:
    """Quote numeric literals compared with a TEXT-affinity column."""
    spans = _string_spans(sql)
    inside = lambda i: any(a <= i < b for a, b in spans)

    def col_num(m: re.Match) -> str:
        if inside(m.start()) or m.group(2).lower() not in text_cols:
            return m.group(0)
        return f"{m.group(1)} {m.group(3)} '{m.group(4)}'"

    def num_col(m: re.Match) -> str:
        if inside(m.start()) or m.group(4).lower() not in text_cols:
            return m.group(0)
        return f"'{m.group(1)}' {m.group(2)} {m.group(3)}"

    return _NUM_COL.sub(num_col, _COL_NUM.sub(col_num, sql))


def _self_test_text_affinity() -> None:
    """Guards the rewrite: it must touch only TEXT-affinity column vs number
    comparisons, and never numbers inside string literals or other columns."""
    cols = {"year", "name"}
    cases = [
        ("SELECT * FROM c WHERE year >= 2014", "SELECT * FROM c WHERE year >= '2014'"),
        ("SELECT * FROM c WHERE T1.year = 2014", "SELECT * FROM c WHERE T1.year = '2014'"),
        ("SELECT * FROM c WHERE 2014 < year", "SELECT * FROM c WHERE '2014' < year"),
        ("SELECT * FROM c WHERE age > 30", "SELECT * FROM c WHERE age > 30"),
        ("SELECT * FROM c WHERE name = 'year = 5'", "SELECT * FROM c WHERE name = 'year = 5'"),
        ("SELECT * FROM c WHERE year = 2014.5", "SELECT * FROM c WHERE year = '2014.5'"),
        ("SELECT count(*) > 3 FROM c", "SELECT count(*) > 3 FROM c"),
    ]
    for src, want in cases:
        got = emulate_text_affinity(src, cols)
        if got != want:
            sys.exit(f"FAIL: text-affinity self-test: {src!r} -> {got!r}, expected {want!r}")


def text_declared_columns(schema: dict) -> set[str]:
    """Lower-cased column names that `sqlite_for` declares TEXT (any Spider type but `number`
    and `boolean`, so `time` too: we have no date type, #211) in every table of the database
    that has a column of that name (registry row 17)."""
    ok: dict[str, bool] = {}
    for (_ti, cname), ctype in zip(schema["column_names_original"], schema["column_types"]):
        if cname == "*":
            continue
        key = cname.lower()
        ok[key] = ok.get(key, True) and ctype not in ("number", "boolean")
    return {k for k, v in ok.items() if v}


_AGG_COL = re.compile(r"\b(avg|sum)\s*\(\s*(?:distinct\s+)?(?:\w+\.)?(\w+)\s*\)", re.I)


def aggregates_text(sql: str, text_cols: set[str]) -> bool:
    """Whether the query takes AVG or SUM of a TEXT-declared column. sqlite converts the text
    to numbers there (a numeric prefix, else 0); we, DuckDB and Postgres treat it as a type
    error (registry row 17)."""
    spans = _string_spans(sql)
    return any(m.group(2).lower() in text_cols and not any(a <= m.start() < b for a, b in spans)
               for m in _AGG_COL.finditer(sql))


def _self_test_aggregates_text() -> None:
    """Guards the row-17 label: AVG/SUM of a TEXT column only, never of a numeric column,
    another aggregate, or text inside a string literal."""
    cols = {"horsepower", "age"}
    cases = [
        ("SELECT avg(horsepower) FROM cars_data", True),
        ("SELECT AVG(T1.Horsepower) FROM cars_data AS T1", True),
        ("SELECT sum(DISTINCT age) FROM dogs", True),
        ("SELECT avg(weight) FROM cars_data", False),
        ("SELECT max(horsepower) FROM cars_data", False),
        ("SELECT count(*) FROM t WHERE name = 'avg(age)'", False),
    ]
    for src, want in cases:
        if aggregates_text(src, cols) != want:
            sys.exit(f"FAIL: aggregates-text self-test: {src!r} -> {not want}, expected {want}")


def classify_query(sql: str) -> str:
    """Feature signature for failure grouping."""
    u = sql.upper()
    feats = [k for k in ("JOIN", "GROUP BY", "HAVING", "ORDER BY", "AVG", "SUM(",
                         "COUNT", "INTERSECT", "UNION", "EXCEPT", "LIKE",
                         "DISTINCT", "BETWEEN") if k in u]
    return "+".join(feats[:3]) if feats else "plain SELECT"


DUCKDB = shutil.which("duckdb")


def _duck_literal(v) -> str:
    if v is None:
        return "NULL"
    if isinstance(v, (int, float)):
        return str(v)
    return "'" + str(v).replace("'", "''") + "'"


def duckdb_file(schema: dict, tables, rows, workdir: Path) -> Path:
    """A DuckDB database holding the same synthetic data as `sqlite_for` (same column types:
    `number`/`boolean` as integers, everything else as text)."""
    path = workdir / f"{schema['db_id']}.duckdb"
    if path.exists():
        return path
    types = schema["column_types"]
    cols = schema["column_names_original"]
    ti_of = {t: i for i, t in enumerate(schema["table_names_original"])}
    stmts = []
    for tname, colnames in tables:
        ctypes = [types[i] for i, (t, _) in enumerate(cols) if t == ti_of[tname]]
        decls = ", ".join(f'"{c}" {"BIGINT" if ty in ("number", "boolean") else "VARCHAR"}'
                          for c, ty in zip(colnames, ctypes))
        stmts.append(f'CREATE TABLE "{tname}" ({decls});')
        for row in rows[tname]:
            stmts.append(f'INSERT INTO "{tname}" VALUES ({", ".join(_duck_literal(c) for c in row)});')
    subprocess.run([DUCKDB, str(path)], input="\n".join(stmts), text=True,
                   capture_output=True, check=True)
    return path


def duckdb_rows(path: Path, query: str):
    """("ok", rows) or ("err", message): the query on DuckDB, cells as text, booleans as 1/0."""
    r = subprocess.run([DUCKDB, "-readonly", "-noheader", "-list", "-separator", "\x1f",
                        "-nullvalue", "NULL", str(path), "-c", query],
                       capture_output=True, text=True, timeout=30)
    if r.returncode != 0 or r.stderr.strip():
        msg = (r.stderr.strip().splitlines() or ["error"])[0]
        return ("err", msg.split(". ")[0][:100])
    out = []
    for line in r.stdout.splitlines():
        out.append([{"true": "1", "false": "0"}.get(c, None if c == "NULL" else c)
                    for c in line.split("\x1f")])
    return ("ok", out)


def duckdb_verdict(path: Path | None, query: str, ours: list, sq_rows: list) -> str | None:
    """Stage 2 (#225): None when DuckDB agrees with sqlite (a failure of ours), else the
    engine-divergent label: DuckDB rejects the query, or returns another answer (and whether
    ours is DuckDB's)."""
    if path is None:
        return None
    status, duck = duckdb_rows(path, query)
    if status == "err":
        return f"engine-divergent: DuckDB rejects the query ({duck})"
    if normalize(duck) == normalize(sq_rows):
        return None
    if normalize(ours) == normalize(duck):
        return "engine-divergent: DuckDB differs from sqlite, ours matches DuckDB"
    return "engine-divergent: DuckDB differs from sqlite and from ours"


def _postgres_available() -> bool:
    if shutil.which("psql") is None:
        return False
    r = subprocess.run(["psql", "-X", "-At", "-c", "select 1"], capture_output=True, text=True)
    return r.returncode == 0 and r.stdout.strip() == "1"


POSTGRES = _postgres_available()


def postgres_schema(schema: dict, tables, rows, tag: str) -> str:
    """Load the same synthetic data as `sqlite_for` into a fresh Postgres schema (BIGINT for
    `number`/`boolean`, TEXT otherwise) and return its name. Table and column names are
    lowercased, so the unquoted (case-insensitive) identifiers of Spider queries resolve."""
    name = f"spider_{tag}_{schema['db_id']}".lower()
    types = schema["column_types"]
    cols = schema["column_names_original"]
    ti_of = {t: i for i, t in enumerate(schema["table_names_original"])}
    stmts = [f'DROP SCHEMA IF EXISTS "{name}" CASCADE;', f'CREATE SCHEMA "{name}";']
    for tname, colnames in tables:
        ctypes = [types[i] for i, (t, _) in enumerate(cols) if t == ti_of[tname]]
        decls = ", ".join(f'"{c.lower()}" {"BIGINT" if ty in ("number", "boolean") else "TEXT"}'
                          for c, ty in zip(colnames, ctypes))
        stmts.append(f'CREATE TABLE "{name}"."{tname.lower()}" ({decls});')
        for row in rows[tname]:
            stmts.append(f'INSERT INTO "{name}"."{tname.lower()}" VALUES '
                         f'({", ".join(_duck_literal(c) for c in row)});')
    subprocess.run(["psql", "-X", "-q", "-v", "ON_ERROR_STOP=1"], input="\n".join(stmts),
                   text=True, capture_output=True, check=True)
    return name


def postgres_drop(names) -> None:
    if names:
        subprocess.run(["psql", "-X", "-q", "-c",
                        "; ".join(f'DROP SCHEMA IF EXISTS "{n}" CASCADE' for n in names)],
                       capture_output=True, text=True)


def postgres_rows(schema_name: str, query: str):
    """("ok", rows) or ("err", message): the query on Postgres, cells as text, booleans 1/0."""
    r = subprocess.run(["psql", "-X", "-q", "-At", "-F", "\x1f", "-P", "null=NULL",
                        "-v", "ON_ERROR_STOP=1",
                        "-c", f'SET search_path TO "{schema_name}"', "-c", query],
                       capture_output=True, text=True, timeout=30)
    if r.returncode != 0:
        msg = next((l for l in r.stderr.splitlines() if l.startswith("ERROR")), "error")
        return ("err", msg[:100])
    out = []
    for line in r.stdout.splitlines():
        out.append([{"t": "1", "f": "0"}.get(c, None if c == "NULL" else c)
                    for c in line.split("\x1f")])
    return ("ok", out)


def postgres_tiebreak(schema_name: str, query: str, ours: list, sq_rows: list,
                      duck) -> tuple[bool, str]:
    """#225 tiebreaker for an engine-divergent query: (Postgres sides with sqlite, note).
    `duck` is DuckDB's ("ok", rows) / ("err", msg). When Postgres gives sqlite's answer, two
    of three oracles agree against ours, so the query is a failure of ours after all."""
    status, pg = postgres_rows(schema_name, query)
    if status == "err":
        return (False, f"Postgres rejects the query ({pg})")
    if normalize(pg) == normalize(sq_rows):
        return (True, "Postgres matches sqlite")
    if normalize(pg) == normalize(ours):
        return (False, "Postgres matches ours")
    if duck[0] == "ok" and normalize(pg) == normalize(duck[1]):
        return (False, "Postgres matches DuckDB")
    return (False, "Postgres differs from sqlite, DuckDB and ours")


def _self_test_postgres_tiebreak() -> None:
    """Guards `postgres_tiebreak` (needs a reachable Postgres; skipped without one)."""
    if not POSTGRES:
        return
    schema = {"db_id": "selftest", "table_names_original": ["T"],
              "column_names_original": [[-1, "*"], [0, "N"], [0, "s"]],
              "column_types": ["text", "number", "text"]}
    name = postgres_schema(schema, [("T", ["N", "s"])],
                           {"T": [[1, "a"], [2, None], [None, "it's"]]}, "selftest")
    try:
        sq = [[1, "a"], [2, None], [None, "it's"]]
        assert postgres_tiebreak(name, "SELECT N, s FROM T", [], sq, ("err", "")) == \
            (True, "Postgres matches sqlite")
        sides, note = postgres_tiebreak(name, "SELECT avg(s) FROM T", [], [[0.0]], ("err", ""))
        assert not sides and note.startswith("Postgres rejects"), note
        assert postgres_tiebreak(name, "SELECT 1 = 1", [["1"]], [[0]], ("err", "")) == \
            (False, "Postgres matches ours")
        assert postgres_tiebreak(name, "SELECT 2", [[3]], [[1]], ("ok", [["2"]])) == \
            (False, "Postgres matches DuckDB")
        assert postgres_tiebreak(name, "SELECT 2", [[3]], [[1]], ("ok", [["4"]])) == \
            (False, "Postgres differs from sqlite, DuckDB and ours")
        # 1/2 = 0 on sqlite and Postgres; 0.5 on DuckDB: the tie goes to sqlite.
        assert postgres_tiebreak(name, "SELECT 1/2", [["0.5"]], [[0]], ("ok", [["0.5"]])) == \
            (True, "Postgres matches sqlite")
    finally:
        postgres_drop([name])


def _self_test_duckdb_verdict() -> None:
    """Guards `duckdb_verdict` (needs the duckdb CLI; skipped without it)."""
    if DUCKDB is None:
        return
    schema = {"db_id": "t", "table_names_original": ["T"],
              "column_names_original": [[-1, "*"], [0, "n"], [0, "s"]],
              "column_types": ["text", "number", "text"]}
    with tempfile.TemporaryDirectory() as d:
        path = duckdb_file(schema, [("T", ["n", "s"])],
                           {"T": [[1, "a"], [2, None], [None, "it's"]]}, Path(d))
        q = 'SELECT n, s FROM T'
        sq = [[1, "a"], [2, None], [None, "it's"]]
        assert duckdb_verdict(path, q, [], sq) is None, "DuckDB agrees with sqlite"
        v = duckdb_verdict(path, "SELECT avg(s) FROM T", [], [[0.0]])
        assert v and v.startswith("engine-divergent: DuckDB rejects"), v
        v = duckdb_verdict(path, "SELECT 1 = 1", [["1"]], [[0]])
        assert v == "engine-divergent: DuckDB differs from sqlite, ours matches DuckDB", v
        v = duckdb_verdict(path, "SELECT 2", [[3]], [[1]])
        assert v == "engine-divergent: DuckDB differs from sqlite and from ours", v
        assert duckdb_verdict(None, q, [], sq) is None


def run_corpus(schemas: dict, pairs: list, variant: int):
    """Evaluate every corpus query on one data variant, with us and with sqlite. Returns
    (agree, tie_ok, affinity_ok, failures, oracle_err, accepted): `accepted[i]` is "agree" for an
    accepted answer; failures are grouped by class as (query, detail)."""
    accepted: dict[int, str] = {}

    # Build manifest for our engine + sqlite connections
    manifest_lines = []
    conns: dict[str, sqlite3.Connection] = {}
    text_cols: dict[str, set[str]] = {}
    built: dict[str, tuple] = {}
    for db_id, schema in schemas.items():
        tables, rows = build_db(schema, variant)
        built[db_id] = (tables, rows)
        conns[db_id] = sqlite_for(schema, tables, rows)
        text_cols[db_id] = text_affinity_columns(schema, tables, rows)
        manifest_lines.append(f"#DB {db_id}")
        for tname, colnames in tables:
            manifest_lines.append(f"#TABLE {tname}")
            manifest_lines.append("|".join(colnames))
            for row in rows[tname]:
                manifest_lines.append("|".join(cell_str(c) for c in row))
    # Every query runs as written; queries the affinity rewrite changes also
    # run rewritten, as extra manifest entries after the corpus. The original
    # is always preferred, so the rewrite can only turn a failure into an
    # (labelled) agreement, never the reverse.
    rewritten: dict[int, int] = {}   # corpus index -> manifest index of rewrite
    extra: list[tuple[str, str]] = []
    for i, p in enumerate(pairs, start=1):
        manifest_lines.append(f"#QUERY {p['db']}")
        manifest_lines.append(p["query"])
        ours_sql = emulate_text_affinity(p["query"], text_cols.get(p["db"], set()))
        if ours_sql != p["query"]:
            extra.append((p["db"], ours_sql))
            rewritten[i] = len(pairs) + len(extra)
    for db_id, sql in extra:
        manifest_lines.append(f"#QUERY {db_id}")
        manifest_lines.append(sql)

    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write("\n".join(manifest_lines) + "\n")
        manifest_path = f.name

    out = subprocess.run([str(EXE), "--dialect", "sqlite", "--spider-eval", manifest_path],
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

    duck_dir = Path(tempfile.mkdtemp(prefix="spider_duck_")) if DUCKDB else None

    pg_schemas: dict[str, str] = {}

    def duck_label(i: int, p: dict, ours_rows: list, sq_rows: list, label: str) -> str:
        if duck_dir is None:
            return label
        tables, rows = built[p["db"]]
        path = duckdb_file(schemas[p["db"]], tables, rows, duck_dir)
        verdict = duckdb_verdict(path, p["query"], ours_rows, sq_rows)
        if verdict is None:
            return label
        if not POSTGRES:
            return f"{verdict} — {label}"
        if p["db"] not in pg_schemas:
            pg_schemas[p["db"]] = postgres_schema(schemas[p["db"]], tables, rows,
                                                  f"{os.getpid()}_v{variant}")
        sides, note = postgres_tiebreak(pg_schemas[p["db"]], p["query"], ours_rows, sq_rows,
                                        duckdb_rows(path, p["query"]))
        if sides:
            what = verdict.removeprefix("engine-divergent: ")
            return f"tiebroken against ours: {what}, but {note} — {label}"
        return f"{verdict}; {note} — {label}"

    agree = 0
    tie_ok: list[str] = []
    affinity_ok: list[str] = []
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
            failures[duck_label(i, p, [], sq_rows, f"ours-error: {classify_query(p['query'])}")
                     ].append((p["query"], str(payload)))
            continue
        if normalize(payload) == normalize(sq_rows):
            agree += 1
            accepted[i] = "agree"
            continue
        elif (i in rewritten
              and ours.get(rewritten[i], ("err", ""))[0] == "ok"
              and (normalize(ours[rewritten[i]][1]) == normalize(sq_rows)
                   or tie_valid(conns[p["db"]], p["query"], ours[rewritten[i]][1], sq_rows))):
            affinity_ok.append(p["query"])
            accepted[i] = "agree"
        elif tie_valid(conns[p["db"]], p["query"], payload, sq_rows):
            tie_ok.append(p["query"])
            accepted[i] = "agree"
        elif aggregates_text(p["query"], text_declared_columns(schemas[p["db"]])):
            # A known divergence, reported under its own label and still counted as a
            # failure: sqlite coerces TEXT inside AVG/SUM (registry row 17, decided).
            failures[duck_label(i, p, payload, sq_rows,
                "known divergence: AVG/SUM over a TEXT column (registry row 17)")].append(
                (p["query"], f"ours {payload} vs sqlite {sq_rows}"))
        else:
            failures[duck_label(i, p, payload, sq_rows,
                f"mismatch: {classify_query(p['query'])}")].append(
                (p["query"], f"ours {len(payload)} rows vs sqlite {len(sq_rows)} rows"))

    if duck_dir is not None:
        shutil.rmtree(duck_dir, ignore_errors=True)
    postgres_drop(pg_schemas.values())
    return agree, tie_ok, affinity_ok, failures, oracle_err, accepted


STRESS_REPORT = ROOT / "benchmarks" / "spider" / "stress_report.md"


def run_stress(schemas: dict, pairs: list, status0: dict, k: int) -> None:
    """`--stress=K`: re-run the corpus on K seeded data variants (`build_db`, variants 1..K)
    and report the queries that the fixed data accepts but some variant does not, grouped by
    failure class. Not ratcheted: a backlog of issue candidates the fixed 5-row data hides."""
    hidden: dict[str, dict[str, tuple[int, str]]] = defaultdict(dict)  # class -> query -> example
    for v in range(1, k + 1):
        _, _, _, failures, _, status = run_corpus(schemas, pairs, v)
        cls_of = {q: (cls, d) for cls, items in failures.items() for q, d in items}
        for i, p in enumerate(pairs, start=1):
            if status0.get(i) == "agree" and status.get(i) != "agree":
                cls, detail = cls_of.get(p["query"], ("unknown", ""))
                hidden[cls].setdefault(p["query"], (v, detail))
    n = len({q for qs in hidden.values() for q in qs})
    lines = [
        "# Spider Dev-Set Stress Report",
        "",
        "Generated by `tools/spider_eval_baseline.py --stress=K` — do not edit by hand.",
        "",
        f"**{n} queries agree with sqlite on the fixed data but not on at least one of {k} "
        "seeded data variants** (0–8 rows per table; NULLs anywhere outside primary keys; "
        "duplicate, zero and negative numbers; dangling or NULL foreign keys). Not ratcheted: "
        "issue candidates the fixed 5-row data hides (#225).",
        "",
        "| Count | Class | Example query | Variant | Detail |",
        "|------:|-------|---------------|--------:|--------|",
    ]
    for cls, qs in sorted(hidden.items(), key=lambda kv: -len(kv[1])):
        q, (v, d) = next(iter(qs.items()))
        q = (q[:70] + "…") if len(q) > 70 else q
        d = d.replace("|", "\\|")[:80]
        lines.append(f"| {len(qs)} | {cls} | `{q}` | {v} | {d} |")
    STRESS_REPORT.write_text("\n".join(lines) + "\n")
    print(f"Stress: {n} queries hidden by the fixed data across {k} variants — report: {STRESS_REPORT}")


def main() -> None:
    check_only = "--check" in sys.argv
    update = "--update-ratchet" in sys.argv
    _self_test_tie_valid()
    _self_test_text_affinity()
    _self_test_aggregates_text()
    _self_test_duckdb_verdict()
    _self_test_postgres_tiebreak()
    if not EXE.exists():
        sys.exit(f"error: {EXE} not built — run `lake build sql_equiv` first")

    schemas = {s["db_id"]: s for s in json.load(open(TABLES))}
    pairs = [json.loads(l) for l in open(QUERIES)]
    stress = next((int(a.split("=", 1)[1]) for a in sys.argv if a.startswith("--stress=")), 0)
    agree, tie_ok, affinity_ok, failures, oracle_err, status0 = run_corpus(schemas, pairs, 0)
    if stress:
        run_stress(schemas, pairs, status0, stress)
    total = len(pairs) - oracle_err
    accepted = agree + len(tie_ok) + len(affinity_ok)
    rate = 100.0 * accepted / total if total else 0.0
    strict_rate = 100.0 * agree / total if total else 0.0
    divergent = sum(len(v) for c, v in failures.items() if c.startswith("engine-divergent"))
    ours_fail = sum(len(v) for c, v in failures.items()
                    if not c.startswith(("engine-divergent", "oracle-error")))
    if not check_only:
        lines = [
            "# Spider Dev-Set Evaluate Report",
            "",
            "Generated by `tools/spider_eval_baseline.py` — do not edit by hand.",
            "",
            f"**Exact multiset match vs sqlite (Spider-fidelity oracle): "
            f"{agree}/{total} ({strict_rate:.1f}%)** "
            f"({oracle_err} queries errored on the oracle and are excluded)",
            "",
            f"With the accepted categories below: {agree} exact + {len(tie_ok)} tie-valid + "
            f"{len(affinity_ok)} affinity-emulated = **{accepted}/{total} ({rate:.1f}%) "
            f"evaluate-agreement**. Both counts are ratcheted (#266).",
            "",
            f"- Tie-valid: {len(tie_ok)}: `ORDER BY … LIMIT n` where the cutoff falls inside",
            "  a tie and our rows are a valid tie-break (every row sorting strictly before",
            "  the cutoff, plus tied rows). Not counted as failures. A NULL key at the",
            "  cutoff is not accepted as a tie.",
            f"- TEXT-affinity emulated: {len(affinity_ok)}: queries comparing a TEXT column",
            "  with a number, which sqlite compares as text. For our engine only, the",
            "  harness quotes the number (`year >= 2014` → `year >= '2014'`), the",
            "  comparison sqlite performs; our core semantics keep it a type error (#235,",
            "  docs/IMPLEMENTATION_DEFINED.md row 12). Includes rewritten answers that are",
            "  tie-valid. The original query is always tried first.",
            (f"- Engine-divergent: {divergent}: DuckDB (cross-check) rejects the query or"
             if DUCKDB else
             "- Engine-divergent: not checked (duckdb CLI not installed): every"),
            ("  disagrees with sqlite, so sqlite's answer is not the only defensible one."
             if DUCKDB else "  disagreement below counts as ours."),
            "  Still counted as disagreements with sqlite (the rate above), but not as",
            "  failures of ours. The class says whether ours matches DuckDB, and what",
            ("  Postgres (the standards tiebreaker) answers." if POSTGRES else
             "  Postgres tiebreaker: not run (no reachable Postgres)."),
            f"- Failures of ours: {ours_fail}: sqlite and DuckDB agree and we do not, or they",
            "  disagree and Postgres gives sqlite's answer (class `tiebroken against ours`).",
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
        print(f"Exact match: {agree}/{total} ({strict_rate:.1f}%); +{len(tie_ok)} tie-valid, "
              f"+{len(affinity_ok)} affinity-emulated = evaluate-agreement {accepted}/{total} "
              f"({rate:.1f}%) ["
              f"engine-divergent {divergent if DUCKDB else 'n/a'}, ours {ours_fail}] "
              f"— report: {REPORT}")

    # Two ratchets (#266): exact matches, and exact + tie-valid + affinity-emulated.
    ratchets = [(EXACT_RATCHET, agree, "exact match"), (RATCHET, accepted, "evaluate-agreement")]
    if update or not all(path.exists() for path, _, _ in ratchets):
        for path, value, what in ratchets:
            path.write_text(f"{value}\n")
            print(f"Ratchet set: {what} {value}")
        return
    failed = False
    for path, value, what in ratchets:
        minimum = int(path.read_text().strip())
        if value < minimum:
            print(f"FAIL: Spider {what} regressed: {value} < ratchet {minimum}")
            failed = True
        else:
            print(f"Ratchet check passed: {what} {value} >= {minimum}")
    if failed:
        sys.exit(1)

if __name__ == "__main__":
    main()
