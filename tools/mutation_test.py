#!/usr/bin/env python3
"""
Mutation testing of the evaluator's dispatch arms (#210).

Every arm of the value-level dispatch in `SqlEquiv/SemanticsBase.lean` (`Value.eq`,
`Value.compare`, `Value.toBool`, `evalBinOp`, `evalUnaryOp`, `evalFunc`) gets one or two
mutants:
- a value mutation, the first rule of `VALUE_RULES` that applies to the arm's result: flip a
  boolean or a comparison, swap an ordering, add one to an integer or decimal, drop
  `natAbs`/`toUpper`/`toLower`, swap `tdiv`/`tmod`;
- an error/NULL mutation: a result becomes `none` (an evaluation error); an arm that returns
  `none` returns NULL instead, and one that returns NULL returns `none`.

Each mutant is built and tested, and classified:
- killed by proofs: the build fails in a later declaration or module (a theorem, a `decide`
  check): the kernel noticed;
- killed by tests: the build passes and a unit test (`sql_equiv_test`) or an LSpec property
  (`sql_equiv_lspec`, at reduced samples, differential oracles included) fails;
- survived: nothing noticed. These are the actionable report: a semantics arm no proof or test
  is sensitive to;
- invalid: the mutant itself does not compile (in the mutated function). Not counted.

The SqlCore / SqlBridge proofs are not built (they need Mathlib); a mutant they would reject
can show as killed by tests or as survived.

Usage:
    python3 tools/mutation_test.py --list                  # the mutants, no build
    python3 tools/mutation_test.py --shard 0/8 --out s0.json [--limit N] [--sites evalFunc,...]
    python3 tools/mutation_test.py --merge s*.json         # report + results JSON

Run it in a scratch checkout or worktree: it edits SemanticsBase.lean (restoring it after each
mutant, and on exit) and leaves the build cache holding the last mutant's build.

Stdlib only.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass, asdict, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET = Path("SqlEquiv/SemanticsBase.lean")
SITES = ["Value.eq", "Value.compare", "Value.toBool", "evalBinOp", "evalUnaryOp", "evalFunc"]
REPORT = Path("benchmarks/mutation/report.md")
RESULTS = Path("benchmarks/mutation/results.json")
LSPEC_SAMPLES = "1000"

# ----------------------------------------------------------------------------------------------
# Mutant generation
# ----------------------------------------------------------------------------------------------

# (name, regex, replacement): the first rule whose regex matches the arm's result is applied,
# once. Replacements keep the parentheses balanced.
VALUE_RULES: list[tuple[str, str, str]] = [
    ("bool-true-false", r"\.bool true\b", ".bool false"),
    ("bool-false-true", r"\.bool false\b", ".bool true"),
    ("eq-to-ne", r" == ", " != "),
    ("ne-to-eq", r" != ", " == "),
    ("negate-bool", r"\.bool \(", ".bool !("),
    ("negate-bool", r"Value\.bool \(", "Value.bool !("),
    ("swap-ordering", r"some \(Ord\.compare", "some (Ordering.swap <| Ord.compare"),
    ("drop-negation", r"!(?=[a-zA-Z(])", ""),
    ("int-plus-one", r"\.int \(", ".int (1 + "),
    ("int-plus-one", r"\.int ([\w.]+)", r".int (1 + \1)"),
    ("round-places", r"(roundDecimal \w+ \w+) 0\)", r"\1 1)"),
    ("round-places", r"(roundDecimal \w+ \w+) d\)", r"\1 (d + 1))"),
    ("decimal-plus-one", r"Value\.mkDecimal \(", "Value.mkDecimal (1 + "),
    ("decimal-plus-one", r"\.decimal \(", ".decimal (1 + "),
    ("string-prefix", r"\.string \(", '.string ("x" ++ '),
    ("drop-call", r"(?<!Char)\.(toUpper|toLower|natAbs)\b", ""),
    ("tdiv-to-tmod", r"\.tdiv\b", ".tmod"),
    ("tmod-to-tdiv", r"\.tmod\b", ".tdiv"),
]

ARM_RE = re.compile(r"^  \| (?P<pat>.*?)=>(?P<rhs>.*)$")


@dataclass
class Mutant:
    id: str
    site: str
    line: int          # 1-based line of the arm in the original file
    op: str
    pattern: str
    original: str
    mutated: str
    end_line: int      # last line of the arm's result (inclusive)
    status: str = "pending"
    killers: list[str] = field(default_factory=list)
    detail: str = ""
    seconds: float = 0.0


def strip_comment(s: str) -> str:
    i = s.find("--")
    return s if i < 0 else s[:i]


def site_ranges(lines: list[str]) -> dict[str, tuple[int, int]]:
    """0-based [start, end) line range of each site's definition."""
    out = {}
    for site in SITES:
        start = next((i for i, l in enumerate(lines) if l.startswith(f"def {site} ")), None)
        if start is None:
            raise SystemExit(f"error: `def {site}` not found in {TARGET}")
        end = start + 1
        while end < len(lines) and (lines[end].strip() == "" or lines[end].startswith(" ")):
            end += 1
        out[site] = (start, end)
    return out


def arms(lines: list[str], start: int, end: int):
    """(line index, pattern, result text, last line index) of each top-level arm."""
    i = start
    while i < end:
        m = ARM_RE.match(lines[i])
        if not m:
            i += 1
            continue
        rhs = strip_comment(m.group("rhs")).strip()
        j = i + 1
        cont = []
        while j < end and lines[j].startswith("    ") and not lines[j].lstrip().startswith("--"):
            cont.append(strip_comment(lines[j]).strip())
            j += 1
        full = " ".join([rhs] + cont).strip()
        yield i, m.group("pat").strip(), full, j - 1
        i = j


def value_mutation(rhs: str) -> tuple[str, str] | None:
    for name, rx, repl in VALUE_RULES:
        new, n = re.subn(rx, repl, rhs, count=1)
        if n and new != rhs:
            return name, new
    return None


def mutants_for(site: str, idx: int, pat: str, rhs: str, last: int) -> list[Mutant]:
    out: list[tuple[str, str]] = []
    if rhs == "none":
        # the Value-level sites return `Option Value`; Value.eq/toBool `Option Bool` and
        # Value.compare `Option Ordering`, which have no NULL: an error becomes a result
        if site in ("Value.eq", "Value.toBool"):
            out.append(("error-to-value", "some false"))
        elif site == "Value.compare":
            out.append(("error-to-value", "some .eq"))
        else:
            out.append(("error-to-null", "some (.null none)"))
    elif re.fullmatch(r"some \(\.null [^()]*\)", rhs):
        out.append(("null-to-error", "none"))
    else:
        vm = value_mutation(rhs)
        if vm:
            out.append(vm)
        out.append(("value-to-error", "none"))
    return [Mutant(id=f"{site}:{idx + 1}:{op}", site=site, line=idx + 1, op=op, pattern=pat,
                   original=rhs, mutated=new, end_line=last + 1) for op, new in out]


def all_mutants(text: str) -> list[Mutant]:
    lines = text.split("\n")
    out: list[Mutant] = []
    for site, (s, e) in site_ranges(lines).items():
        for idx, pat, rhs, last in arms(lines, s + 1, e):
            out.extend(mutants_for(site, idx, pat, rhs, last))
    return out


def apply(text: str, m: Mutant) -> str:
    lines = text.split("\n")
    i = m.line - 1
    head = lines[i][: lines[i].index("=>") + 2]
    lines[i : m.end_line] = [f"{head} {m.mutated}"]
    return "\n".join(lines)


def _self_test() -> None:
    """Guards the arm parser and the rules on a synthetic snippet (runs on every invocation)."""
    src = "\n".join([
        "def evalUnaryOp (op : UnaryOp) (e : Option Value) : Option Value :=",
        "  match op, e with",
        "  | .not, some (.bool b) => some (.bool (!b))",
        "  | .not, some (.null _) => some (.null none)  -- NOT NULL = NULL",
        "  | .neg, some (.int n) =>",
        "    some (.int (-n))",
        "  | _, _ => none",
        "",
        "-- next",
    ])
    lines = src.split("\n")
    got = list(arms(lines, 1, 7))
    assert [g[0] for g in got] == [2, 3, 4, 6], got
    assert got[2][2] == "some (.int (-n))", got[2]
    ms = [m for g in got for m in mutants_for("evalUnaryOp", *g)]
    ops = [m.op for m in ms]
    assert ops == ["negate-bool", "value-to-error", "null-to-error", "int-plus-one",
                   "value-to-error", "error-to-null"], ops
    neg = next(m for m in ms if m.op == "int-plus-one")
    applied = apply(src, neg).split("\n")
    assert applied[4] == "  | .neg, some (.int n) => some (.int (1 + -n))", applied[4]
    assert applied[5] == "  | _, _ => none", applied[5]
    assert value_mutation("some (.string s.toUpper)") == ("drop-call", "some (.string s)")
    assert value_mutation("some (.bool (likeMatch (s.map Char.toLower) p))")[0] == "negate-bool"


# ----------------------------------------------------------------------------------------------
# Running
# ----------------------------------------------------------------------------------------------

def run(cmd: list[str], env: dict | None = None, timeout: int = 3600) -> tuple[int, str]:
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout,
                       env={**os.environ, **(env or {})})
    return r.returncode, r.stdout + r.stderr


def failing_tests() -> tuple[list[str], str]:
    """Names of the failing unit tests and LSpec properties on the current tree."""
    fails: list[str] = []
    with tempfile.TemporaryDirectory() as d:
        unit = Path(d) / "unit.jsonl"
        _, out = run(["lake", "exe", "sql_equiv_test"], {"TEST_RESULTS_JSON": str(unit)}, 1800)
        if unit.exists():
            for line in unit.read_text().splitlines():
                rec = json.loads(line)
                if not rec.get("pass", True):
                    fails.append(f"unit: {rec.get('name')}")
        log = Path(d) / "lspec.log"
        _, lout = run(["lake", "exe", "sql_equiv_lspec"], {"LSPEC_SAMPLES": LSPEC_SAMPLES}, 3600)
        log.write_text(lout)
        js = Path(d) / "lspec.jsonl"
        run([sys.executable, "tools/lspec_results_to_json.py", str(log), str(js)])
        if js.exists():
            for line in js.read_text().splitlines():
                rec = json.loads(line)
                if not rec.get("pass", True):
                    fails.append(f"lspec: {rec.get('suite')} / {rec.get('name')}")
    return fails, out[-2000:]


def classify_build_failure(out: str, m: Mutant) -> tuple[str, str]:
    """`invalid` when the first error is inside the mutated function (the mutant does not
    compile), else `killed-proof` (a later declaration or module rejected it)."""
    errs = re.findall(r"^error: ([^:\s]+\.lean):(\d+):\d+: (.*)$", out, re.M)
    if not errs:
        return "invalid", "build failed without a located error"
    f, ln, msg = errs[0]
    ln = int(ln)
    if f.endswith(str(TARGET)):
        start, end = site_ranges((ROOT / TARGET).read_text().split("\n"))[m.site]
        if start + 1 <= ln <= end:
            return "invalid", f"{f}:{ln}: {msg[:120]}"
    return "killed-proof", f"{f}:{ln}: {msg[:120]}"


def run_mutants(mutants: list[Mutant], out_path: Path, baseline_fails: set[str]) -> None:
    path = ROOT / TARGET
    original = path.read_text()
    results: list[dict] = []
    try:
        for k, m in enumerate(mutants, 1):
            t0 = time.time()
            path.write_text(apply(original, m))
            rc, out = run(["lake", "build", "sql_equiv_test", "sql_equiv_lspec"], timeout=3600)
            if rc != 0:
                m.status, m.detail = classify_build_failure(out, m)
            else:
                fails, _ = failing_tests()
                new = [f for f in fails if f not in baseline_fails]
                m.status = "killed-test" if new else "survived"
                m.killers = new
            m.seconds = round(time.time() - t0, 1)
            print(f"[{k}/{len(mutants)}] {m.id}: {m.status} ({m.seconds}s)"
                  f"{' — ' + m.detail if m.detail else ''}{' — ' + str(len(m.killers)) + ' killers' if m.killers else ''}",
                  flush=True)
            results.append(asdict(m))
            out_path.write_text(json.dumps(results, indent=1))
    finally:
        path.write_text(original)


# ----------------------------------------------------------------------------------------------
# Report
# ----------------------------------------------------------------------------------------------

def merge(files: list[Path]) -> None:
    rows: list[dict] = []
    for f in files:
        rows.extend(json.loads(f.read_text()))
    rows.sort(key=lambda r: (SITES.index(r["site"]), r["line"], r["op"]))
    counts = {s: 0 for s in ["killed-proof", "killed-test", "survived", "invalid"]}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    valid = len(rows) - counts["invalid"]
    killed = counts["killed-proof"] + counts["killed-test"]
    lines = [
        "# Mutation Testing Report",
        "",
        "Generated by `tools/mutation_test.py --merge` (#210) — do not edit by hand.",
        "",
        f"**Mutation score: {killed}/{valid} valid mutants killed"
        f" ({100.0 * killed / valid if valid else 0:.1f}%)** of {len(rows)} generated over the "
        f"dispatch arms of `{TARGET}`.",
        "",
        f"- Killed by proofs (the build fails in a theorem or `decide` check): {counts['killed-proof']}",
        f"- Killed by tests (unit tests, or LSpec at {LSPEC_SAMPLES} samples with the "
        f"differential oracles): {counts['killed-test']}",
        f"- **Survived** (no proof or test noticed): {counts['survived']}",
        f"- Invalid (the mutant does not compile): {counts['invalid']}",
        "",
        "## Per site",
        "",
        "| Site | Mutants | Proofs | Tests | Survived | Invalid |",
        "|---|--:|--:|--:|--:|--:|",
    ]
    for s in SITES:
        rs = [r for r in rows if r["site"] == s]
        if not rs:
            continue
        c = lambda st: sum(1 for r in rs if r["status"] == st)
        lines.append(f"| `{s}` | {len(rs)} | {c('killed-proof')} | {c('killed-test')} | "
                     f"{c('survived')} | {c('invalid')} |")
    lines += ["", "## Survivors", ""]
    surv = [r for r in rows if r["status"] == "survived"]
    if not surv:
        lines.append("None.")
    else:
        lines += ["| Site | Line | Arm | Mutation | Original → mutated |", "|---|--:|---|---|---|"]
        for r in surv:
            lines.append(f"| `{r['site']}` | {r['line']} | `{r['pattern']}` | {r['op']} | "
                         f"`{r['original']}` → `{r['mutated']}` |")
    killers: dict[str, int] = {}
    for r in rows:
        for k in r["killers"]:
            killers[k] = killers.get(k, 0) + 1
    lines += ["", "## Most sensitive tests", "",
              "| Test | Mutants killed |", "|---|--:|"]
    for k, n in sorted(killers.items(), key=lambda kv: -kv[1])[:25]:
        lines.append(f"| {k} | {n} |")
    (ROOT / REPORT).parent.mkdir(parents=True, exist_ok=True)
    (ROOT / REPORT).write_text("\n".join(lines) + "\n")
    (ROOT / RESULTS).write_text(json.dumps(rows, indent=1) + "\n")
    print(f"Mutation score {killed}/{valid}: {counts} — report: {REPORT}")


def main() -> None:
    _self_test()
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--shard", default="0/1")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--sites", default="")
    ap.add_argument("--out", default="mutation-results.json")
    ap.add_argument("--merge", nargs="*")
    a = ap.parse_args()
    if a.merge is not None:
        merge([Path(f) for f in a.merge])
        return
    ms = all_mutants((ROOT / TARGET).read_text())
    if a.sites:
        wanted = set(a.sites.split(","))
        ms = [m for m in ms if m.site in wanted]
    i, n = (int(x) for x in a.shard.split("/"))
    ms = [m for k, m in enumerate(ms) if k % n == i]
    if a.limit:
        ms = ms[: a.limit]
    if a.list:
        for m in ms:
            print(f"{m.id}\t{m.original}  →  {m.mutated}")
        print(f"{len(ms)} mutants")
        return
    print(f"Baseline: building and testing the unmutated tree", flush=True)
    rc, out = run(["lake", "build", "sql_equiv_test", "sql_equiv_lspec"])
    if rc != 0:
        sys.exit(f"error: the unmutated tree does not build:\n{out[-2000:]}")
    baseline, _ = failing_tests()
    if baseline:
        print(f"Baseline failures (ignored as killers): {baseline}", flush=True)
    run_mutants(ms, Path(a.out), set(baseline))


if __name__ == "__main__":
    main()
