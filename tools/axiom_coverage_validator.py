#!/usr/bin/env python3
"""
Axiom & Theorem Coverage Validator for sql_equiv Lean 4 project.

Validates that each axiom/theorem is exercised by the test suite by:
1. Commenting out each axiom one at a time
2. Attempting to build and run tests
3. Checking whether the build fails (compile-time coverage) or tests fail (runtime coverage)
4. Reporting which axioms have no test coverage

Additional modes:
- --runtime: Static runtime coverage (test-name matching, no build, no file edits)
- --theorems: Include public theorems from Equiv/ and LSpec `-- covers:` annotations

WARNING: without --runtime, the script edits source files in place (it comments out one
declaration at a time, rebuilds, and restores the file), and with --theorems that takes hours.
Do not edit the tree while it runs. Use `--runtime --theorems` for the static report.

Usage:
    python tools/axiom_coverage_validator.py                    # Run all axioms
    python tools/axiom_coverage_validator.py --verify-parse     # Just list axioms found
    python tools/axiom_coverage_validator.py --axiom and_self   # Single axiom
    python tools/axiom_coverage_validator.py --file Equiv.lean  # Single file
    python tools/axiom_coverage_validator.py --resume           # Resume from checkpoint
    python tools/axiom_coverage_validator.py --dry-run          # Parse only, no modification
    python tools/axiom_coverage_validator.py --runtime          # Static runtime coverage (no build)
    python tools/axiom_coverage_validator.py --runtime --theorems  # Include theorem coverage
"""

from __future__ import annotations

import argparse
import json
import re
import signal
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from datetime import datetime
from pathlib import Path


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SQLEQUIV_DIR = PROJECT_ROOT / "SqlEquiv"
EQUIV_DIR = SQLEQUIV_DIR / "Equiv"

# lake lives under ~/.elan/bin which may not be in subprocess PATH
_ELAN_BIN = Path.home() / ".elan" / "bin"
_LAKE = str(_ELAN_BIN / "lake") if _ELAN_BIN.exists() else "lake"

BUILD_CMD = [_LAKE, "build", "sql_equiv_test"]
TEST_CMD = [_LAKE, "exe", "sql_equiv_test"]

DEFAULT_BUILD_TIMEOUT = 300   # 5 minutes
DEFAULT_TEST_TIMEOUT = 120    # 2 minutes

CHECKPOINT_FILE = PROJECT_ROOT / "tools" / "axiom_coverage_checkpoint.json"
REPORT_FILE = PROJECT_ROOT / "tools" / "axiom_coverage_report.json"
RATCHET_FILE = PROJECT_ROOT / "tools" / "axiom_count_minimum.txt"

AXIOM_FILES = sorted(SQLEQUIV_DIR.rglob("*.lean"))

TEST_DIR = PROJECT_ROOT / "Test"
TEST_FILES = sorted(TEST_DIR.rglob("*.lean")) if TEST_DIR.exists() else []

LSPEC_DIR = PROJECT_ROOT / "LSpecTests"
LSPEC_FILES = sorted(LSPEC_DIR.rglob("*.lean")) if LSPEC_DIR.exists() else []


# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------

@dataclass
class AxiomLocation:
    name: str
    file_path: str        # absolute path
    start_line: int       # 0-indexed
    end_line: int         # 0-indexed, inclusive
    source_lines: list[str]
    kind: str = "axiom"   # "axiom" or "theorem"

    @property
    def short_file(self) -> str:
        return Path(self.file_path).name

    @property
    def line_count(self) -> int:
        return self.end_line - self.start_line + 1


@dataclass
class AxiomTestResult:
    axiom_name: str
    file_path: str
    start_line: int
    end_line: int
    status: str           # compile_fail | test_fail | no_coverage | error
    build_exit_code: int
    build_stderr: str
    test_exit_code: int | None
    test_stdout: str
    elapsed_seconds: float
    timestamp: str


# ---------------------------------------------------------------------------
# Declaration parsing (axioms and theorems)
# ---------------------------------------------------------------------------

def parse_axioms(file_path: Path) -> list[AxiomLocation]:
    """Parse all axiom declarations from a Lean file.

    An axiom starts with ``axiom`` at column 0. Continuation lines are
    indented. The axiom ends at a blank line or a line starting at column 0.
    """
    text = file_path.read_text()
    lines = text.splitlines()
    axioms: list[AxiomLocation] = []
    i = 0
    while i < len(lines):
        m = re.match(r"^axiom\s+([\w.']+)", lines[i])
        if m:
            name = m.group(1)
            start = i
            end = i
            j = i + 1
            while j < len(lines):
                line = lines[j]
                if line.strip() == "":
                    break
                if len(line) > 0 and line[0] not in (" ", "\t"):
                    break
                end = j
                j += 1
            axioms.append(AxiomLocation(
                name=name,
                file_path=str(file_path),
                start_line=start,
                end_line=end,
                source_lines=lines[start:end + 1],
                kind="axiom",
            ))
            i = end + 1
        else:
            i += 1
    return axioms


def parse_theorems(file_path: Path) -> list[AxiomLocation]:
    """Parse public theorem declarations from a Lean file.

    A theorem starts with ``theorem`` at column 0 (not ``private theorem``).
    Continuation lines are indented. The theorem ends at a blank line or a
    line starting at column 0.
    """
    text = file_path.read_text()
    lines = text.splitlines()
    theorems: list[AxiomLocation] = []
    i = 0
    while i < len(lines):
        # Match "theorem name" but NOT "private theorem name"
        m = re.match(r"^theorem\s+([\w.']+)", lines[i])
        if m:
            name = m.group(1)
            start = i
            end = i
            j = i + 1
            while j < len(lines):
                line = lines[j]
                if line.strip() == "":
                    break
                if len(line) > 0 and line[0] not in (" ", "\t"):
                    break
                end = j
                j += 1
            theorems.append(AxiomLocation(
                name=name,
                file_path=str(file_path),
                start_line=start,
                end_line=end,
                source_lines=lines[start:end + 1],
                kind="theorem",
            ))
            i = end + 1
        else:
            i += 1
    return theorems


def parse_test_names(file_path: Path) -> list[str]:
    """Extract test name strings from a Lean test file.

    Looks for quoted string literals passed to test helpers (``testExprEquiv``,
    ``testQueryEquiv``, etc.) and inline ``.pass`` / ``.fail`` result
    constructors.
    """
    text = file_path.read_text()
    names: list[str] = []
    # Pattern 1: testHelper "name" ...
    for m in re.finditer(r'test\w+\s+"([^"]+)"', text):
        names.append(m.group(1))
    # Pattern 2: .pass "name" / .fail "name"
    for m in re.finditer(r'\.(?:pass|fail)\s+"([^"]+)"', text):
        names.append(m.group(1))
    return names


def parse_lspec_covers(file_path: Path) -> list[str]:
    """Extract theorem names from ``-- covers: name1, name2`` comments.

    Returns a flat list of all theorem names referenced by covers annotations
    in the given file.
    """
    text = file_path.read_text()
    names: list[str] = []
    for m in re.finditer(r"--\s*covers:\s*(.+)", text):
        for name in m.group(1).split(","):
            stripped = name.strip()
            if stripped:
                names.append(stripped)
    return names


# ---------------------------------------------------------------------------
# Runtime coverage analysis (static, no build needed)
# ---------------------------------------------------------------------------

def runtime_analysis(
    axioms: list[AxiomLocation],
    test_files: list[Path] | None = None,
    lspec_files: list[Path] | None = None,
) -> dict:
    """Match declaration names against test name strings and LSpec annotations.

    A declaration is *test-covered* if any Test/ test name starts with its name.
    A declaration is *lspec-covered* if any LSpec ``-- covers:`` annotation
    matches its name exactly.
    A declaration is *covered* if matched by either source.
    """
    if test_files is None:
        test_files = TEST_FILES

    # Collect all test names across Test/ files
    all_test_names: list[str] = []
    test_files_scanned = 0
    for tf in test_files:
        if tf.exists():
            try:
                all_test_names.extend(parse_test_names(tf))
                test_files_scanned += 1
            except Exception as e:
                print(f"Warning: Could not parse {tf}: {e}", file=sys.stderr)

    # Collect all LSpec covers annotations
    all_lspec_covers: list[str] = []
    lspec_files_scanned = 0
    if lspec_files is not None:
        for lf in lspec_files:
            if lf.exists():
                try:
                    all_lspec_covers.extend(parse_lspec_covers(lf))
                    lspec_files_scanned += 1
                except Exception as e:
                    print(f"Warning: Could not parse LSpec {lf}: {e}", file=sys.stderr)

    lspec_covers_set = set(all_lspec_covers)

    if test_files_scanned == 0 and lspec_files_scanned == 0:
        print("WARNING: No test files found. Check that file paths are correct.",
              file=sys.stderr)

    # Match: declaration is covered if any test name starts with it OR any
    # LSpec annotation matches it exactly
    test_covered: list[AxiomLocation] = []
    lspec_covered: list[AxiomLocation] = []
    both_covered: list[AxiomLocation] = []
    uncovered: list[AxiomLocation] = []
    coverage_map: dict[str, list[str]] = {}  # decl_name -> matching tests
    lspec_coverage_map: dict[str, bool] = {}  # decl_name -> has lspec coverage

    def _test_matches_axiom(test_name: str, axiom_name: str) -> bool:
        """True if test_name is axiom_name exactly or followed by a non-identifier char."""
        if not test_name.startswith(axiom_name):
            return False
        if len(test_name) == len(axiom_name):
            return True
        # Next char must not be a word character (avoids "join_comm" matching "join_comm_full")
        return test_name[len(axiom_name)] not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_"

    for ax in axioms:
        test_matches = [t for t in all_test_names if _test_matches_axiom(t, ax.name)]
        has_test = bool(test_matches)
        has_lspec = ax.name in lspec_covers_set

        if test_matches:
            coverage_map[ax.name] = test_matches
        if has_lspec:
            lspec_coverage_map[ax.name] = True

        if has_test and has_lspec:
            both_covered.append(ax)
        elif has_test:
            test_covered.append(ax)
        elif has_lspec:
            lspec_covered.append(ax)
        else:
            uncovered.append(ax)

    covered_count = len(test_covered) + len(lspec_covered) + len(both_covered)

    return {
        "total_axioms": len(axioms),
        "total_test_names": len(all_test_names),
        "total_lspec_covers": len(all_lspec_covers),
        "files_scanned": test_files_scanned,
        "lspec_files_scanned": lspec_files_scanned,
        "covered_count": covered_count,
        "uncovered_count": len(uncovered),
        "test_covered_count": len(test_covered) + len(both_covered),
        "lspec_covered_count": len(lspec_covered) + len(both_covered),
        "both_covered_count": len(both_covered),
        "test_only_count": len(test_covered),
        "lspec_only_count": len(lspec_covered),
        "test_covered": test_covered,
        "lspec_covered": lspec_covered,
        "both_covered": both_covered,
        "covered": test_covered + lspec_covered + both_covered,
        "uncovered": uncovered,
        "coverage_map": coverage_map,
        "lspec_coverage_map": lspec_coverage_map,
    }


def print_runtime_report(analysis: dict) -> None:
    total = analysis["total_axioms"]
    covered = analysis["covered_count"]
    uncovered_count = analysis["uncovered_count"]

    if total == 0:
        print("No declarations found.")
        return

    cov_pct = covered / total * 100
    uncov_pct = uncovered_count / total * 100

    has_lspec = analysis["lspec_files_scanned"] > 0

    label = "declarations" if has_lspec else "axioms"

    print()
    print("=" * 60)
    print(" Runtime Coverage Analysis (static)")
    print("=" * 60)
    print(f"Test files scanned:   {analysis['files_scanned']}")
    print(f"Test names found:     {analysis['total_test_names']}")
    if has_lspec:
        print(f"LSpec files scanned:  {analysis['lspec_files_scanned']}")
        print(f"LSpec covers found:   {analysis['total_lspec_covers']}")
    print(f"Total {label}:     {total}")
    print(f"Covered:              {covered:>3} ({cov_pct:4.1f}%)")
    if has_lspec:
        print(f"  Test/ only:         {analysis['test_only_count']:>3}")
        print(f"  LSpec only:         {analysis['lspec_only_count']:>3}")
        print(f"  Both:               {analysis['both_covered_count']:>3}")
    print(f"Not covered:          {uncovered_count:>3} ({uncov_pct:4.1f}%)")

    uncovered_decls: list[AxiomLocation] = analysis["uncovered"]
    if uncovered_decls:
        print(f"\n--- Uncovered {label.title()} ({uncovered_count}) ---")
        for ax in uncovered_decls:
            kind_tag = f"[{ax.kind}]" if has_lspec else ""
            print(f"  {ax.short_file}:{ax.start_line + 1}  {ax.name}  {kind_tag}")

    # Per-file breakdown
    by_file: dict[str, dict[str, int]] = {}
    for ax in analysis["covered"]:
        fname = ax.short_file
        bucket = by_file.setdefault(fname, {"total": 0, "covered": 0, "uncovered": 0})
        bucket["total"] += 1
        bucket["covered"] += 1
    for ax in uncovered_decls:
        fname = ax.short_file
        bucket = by_file.setdefault(fname, {"total": 0, "covered": 0, "uncovered": 0})
        bucket["total"] += 1
        bucket["uncovered"] += 1

    print("\n--- Per-File Breakdown ---")
    for fname, b in sorted(by_file.items()):
        file_pct = b["covered"] / b["total"] * 100 if b["total"] else 0
        print(f"  {fname:30s}  {b['total']:>3} {label} | "
              f"{b['covered']:>3} covered | "
              f"{b['uncovered']:>3} uncovered | {file_pct:5.1f}%")

    print()


def save_runtime_report(analysis: dict, path: Path) -> None:
    """Save runtime coverage results as JSON."""
    data = {
        "mode": "runtime",
        "timestamp": datetime.now().isoformat(),
        "summary": {
            "total_declarations": analysis["total_axioms"],
            "total_test_names": analysis["total_test_names"],
            "total_lspec_covers": analysis["total_lspec_covers"],
            "files_scanned": analysis["files_scanned"],
            "lspec_files_scanned": analysis["lspec_files_scanned"],
            "covered": analysis["covered_count"],
            "test_only": analysis["test_only_count"],
            "lspec_only": analysis["lspec_only_count"],
            "both": analysis["both_covered_count"],
            "not_covered": analysis["uncovered_count"],
            "coverage_pct": round(
                analysis["covered_count"] / analysis["total_axioms"] * 100, 1
            ) if analysis["total_axioms"] else 0,
        },
        "uncovered": [
            {"name": ax.name, "file": ax.short_file, "line": ax.start_line + 1,
             "kind": ax.kind}
            for ax in analysis["uncovered"]
        ],
        "coverage_map": analysis["coverage_map"],
        "lspec_coverage_map": analysis["lspec_coverage_map"],
    }
    path.write_text(json.dumps(data, indent=2) + "\n")


# ---------------------------------------------------------------------------
# File manipulation (comment-out / restore)
# ---------------------------------------------------------------------------

class ConcurrentEditError(RuntimeError):
    """The file under test was edited by someone else while a declaration was commented out."""


def comment_out_axiom(file_path: Path, axiom: AxiomLocation) -> tuple[str, str]:
    """Comment out a declaration. Returns (original, mutated) file contents for restoration."""
    original = file_path.read_text()
    lines = original.splitlines(keepends=True)
    for idx in range(axiom.start_line, axiom.end_line + 1):
        lines[idx] = "-- " + lines[idx]
    mutated = "".join(lines)
    file_path.write_text(mutated)
    return original, mutated


def restore_file(file_path: Path, original: str, mutated: str | None = None) -> None:
    """Restore a file and verify the restoration succeeded.

    If `mutated` is given and the file no longer holds it, someone edited the file while the
    declaration was commented out (this happened on 19 Nov 2026: the restore overwrote an edit).
    Then the edit is kept: only the commented-out block is put back, if it is still there
    unchanged, and `ConcurrentEditError` is raised so the run stops (its line numbers are stale).
    """
    current = file_path.read_text()
    if mutated is not None and current != mutated:
        o_lines = original.splitlines(keepends=True)
        m_lines = mutated.splitlines(keepends=True)
        changed = [i for i, (a, b) in enumerate(zip(o_lines, m_lines)) if a != b]
        o_block = "".join(o_lines[changed[0]:changed[-1] + 1]) if changed else ""
        m_block = "".join(m_lines[changed[0]:changed[-1] + 1]) if changed else ""
        if m_block and current.count(m_block) == 1:
            file_path.write_text(current.replace(m_block, o_block))
            raise ConcurrentEditError(
                f"{file_path} was edited during the run. The edit was kept and the "
                f"commented-out declaration restored. Stopping: line numbers are stale.")
        raise ConcurrentEditError(
            f"CRITICAL: {file_path} was edited during the run and the commented-out "
            f"declaration could not be located. The file was left as it is; check it for a "
            f"block of lines starting with '-- ' and compare with `git diff`.")
    file_path.write_text(original)
    if file_path.read_text() != original:
        raise RuntimeError(f"CRITICAL: failed to restore {file_path}")


# ---------------------------------------------------------------------------
# Build / test execution
# ---------------------------------------------------------------------------

def run_build(timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        BUILD_CMD,
        cwd=str(PROJECT_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def run_tests(timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        TEST_CMD,
        cwd=str(PROJECT_ROOT),
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def test_single_axiom(
    axiom: AxiomLocation,
    build_timeout: int,
    test_timeout: int,
) -> AxiomTestResult:
    """Comment out one axiom, build, optionally run tests, restore."""
    fpath = Path(axiom.file_path)
    original: str | None = None
    mutated: str | None = None
    t0 = time.time()

    try:
        original, mutated = comment_out_axiom(fpath, axiom)

        # -- build --
        try:
            build = run_build(build_timeout)
        except subprocess.TimeoutExpired:
            return _result(axiom, "error", 1, "BUILD TIMEOUT", None, "", t0)

        if build.returncode != 0:
            return _result(
                axiom, "compile_fail",
                build.returncode, build.stderr[:500],
                None, "", t0,
            )

        # -- tests --
        try:
            test = run_tests(test_timeout)
        except subprocess.TimeoutExpired:
            return _result(axiom, "error", 0, "", None, "TEST TIMEOUT", t0)

        has_failure = "TESTS FAILED" in test.stdout or test.returncode != 0
        status = "test_fail" if has_failure else "no_coverage"
        return _result(
            axiom, status,
            build.returncode, build.stderr[:500],
            test.returncode, test.stdout[-1000:], t0,
        )

    except Exception as exc:
        return _result(axiom, "error", -1, str(exc)[:500], None, "", t0)

    finally:
        if original is not None:
            restore_file(fpath, original, mutated)


def _result(
    axiom: AxiomLocation,
    status: str,
    build_rc: int,
    build_stderr: str,
    test_rc: int | None,
    test_stdout: str,
    t0: float,
) -> AxiomTestResult:
    return AxiomTestResult(
        axiom_name=axiom.name,
        file_path=axiom.file_path,
        start_line=axiom.start_line,
        end_line=axiom.end_line,
        status=status,
        build_exit_code=build_rc,
        build_stderr=build_stderr,
        test_exit_code=test_rc,
        test_stdout=test_stdout,
        elapsed_seconds=round(time.time() - t0, 1),
        timestamp=datetime.now().isoformat(),
    )


# ---------------------------------------------------------------------------
# Checkpoint persistence
# ---------------------------------------------------------------------------

def save_checkpoint(results: list[AxiomTestResult], path: Path) -> None:
    data = {
        "last_updated": datetime.now().isoformat(),
        "completed": len(results),
        "results": [asdict(r) for r in results],
    }
    path.write_text(json.dumps(data, indent=2) + "\n")


def load_checkpoint(path: Path) -> list[AxiomTestResult]:
    if not path.exists():
        return []
    try:
        data = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"Warning: failed to load checkpoint {path}: {exc}. Starting fresh.",
              file=sys.stderr)
        return []
    if not isinstance(data, dict) or not isinstance(data.get("results"), list):
        print(f"Warning: malformed checkpoint {path}. Starting fresh.",
              file=sys.stderr)
        return []
    results: list[AxiomTestResult] = []
    for i, r in enumerate(data["results"]):
        try:
            results.append(AxiomTestResult(**r))
        except Exception as exc:
            print(f"Warning: skipping checkpoint entry #{i}: {exc}",
                  file=sys.stderr)
    return results


# ---------------------------------------------------------------------------
# Pre-flight checks
# ---------------------------------------------------------------------------

def preflight_checks(build_timeout: int, test_timeout: int, ci: bool = False) -> None:
    if not (PROJECT_ROOT / "lakefile.toml").exists():
        sys.exit("Error: lakefile.toml not found. Run from project root.")

    # Warn about uncommitted changes
    git = subprocess.run(
        ["git", "status", "--porcelain", "SqlEquiv/"],
        cwd=str(PROJECT_ROOT), capture_output=True, text=True,
    )
    if git.stdout.strip():
        if ci:
            print("WARNING: uncommitted changes in SqlEquiv/ (continuing in CI mode)")
        else:
            print("WARNING: uncommitted changes in SqlEquiv/.")
            print("  The script will temporarily modify and restore files.")
            ans = input("  Proceed? [y/N] ").strip().lower()
            if ans != "y":
                sys.exit("Aborted.")

    # Baseline build
    print("Pre-flight: building baseline...", flush=True)
    try:
        build = subprocess.run(
            BUILD_CMD, cwd=str(PROJECT_ROOT),
            capture_output=True, text=True, timeout=build_timeout,
        )
    except subprocess.TimeoutExpired:
        sys.exit(f"Error: baseline build timed out after {build_timeout}s.")
    if build.returncode != 0:
        sys.exit(
            f"Error: baseline build failed. Fix before running validator.\n"
            f"{build.stderr[:500]}"
        )
    print("Pre-flight: baseline build OK", flush=True)

    # Baseline tests
    print("Pre-flight: running baseline tests...", flush=True)
    try:
        test = subprocess.run(
            TEST_CMD, cwd=str(PROJECT_ROOT),
            capture_output=True, text=True, timeout=test_timeout,
        )
    except subprocess.TimeoutExpired:
        sys.exit(f"Error: baseline tests timed out after {test_timeout}s.")
    baseline_failures = test.stdout.count("TESTS FAILED")
    print(
        f"Pre-flight: baseline tests done "
        f"(exit={test.returncode}, suites with failures={baseline_failures})",
        flush=True,
    )


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------

def run_axiom_tests(
    axioms: list[AxiomLocation],
    args: argparse.Namespace,
) -> list[AxiomTestResult]:
    checkpoint_path = Path(args.checkpoint)
    results = load_checkpoint(checkpoint_path) if args.resume else []
    completed_names = {r.axiom_name for r in results}

    shutdown = False
    orig_handler = signal.getsignal(signal.SIGINT)

    def on_sigint(signum, frame):
        nonlocal shutdown
        if shutdown:
            signal.signal(signal.SIGINT, signal.SIG_DFL)
            raise KeyboardInterrupt
        shutdown = True
        print("\nShutdown requested — finishing current axiom...")

    signal.signal(signal.SIGINT, on_sigint)

    # A terminated run (SIGTERM, e.g. a stopped background task) must still restore the file:
    # raising here unwinds through `test_single_axiom`'s `finally`.
    def on_sigterm(signum, frame):
        raise SystemExit("Terminated: restoring the file under test and stopping.")

    orig_term = signal.getsignal(signal.SIGTERM)
    signal.signal(signal.SIGTERM, on_sigterm)

    total = len(axioms)
    for i, axiom in enumerate(axioms):
        if axiom.name in completed_names:
            continue
        if shutdown:
            break

        label = f"[{i + 1}/{total}] {axiom.name} ({axiom.short_file}:{axiom.start_line + 1})"
        print(f"{label} ...", end=" ", flush=True)

        try:
            result = test_single_axiom(axiom, args.build_timeout, args.test_timeout)
        except ConcurrentEditError as exc:
            save_checkpoint(results, checkpoint_path)
            sys.exit(f"\n{exc}")
        results.append(result)

        tag = {
            "compile_fail": "C",
            "test_fail": "T",
            "no_coverage": "!",
            "error": "E",
        }[result.status]
        print(f"[{tag}] {result.elapsed_seconds}s")

        save_checkpoint(results, checkpoint_path)

    signal.signal(signal.SIGINT, orig_handler)
    signal.signal(signal.SIGTERM, orig_term)
    return results


# ---------------------------------------------------------------------------
# Report generation
# ---------------------------------------------------------------------------

def generate_report(
    results: list[AxiomTestResult],
    all_axioms: list[AxiomLocation],
) -> dict:
    counts = {"compile_fail": 0, "test_fail": 0, "no_coverage": 0, "error": 0}
    for r in results:
        counts[r.status] = counts.get(r.status, 0) + 1

    total = len(all_axioms)
    covered = counts["compile_fail"] + counts["test_fail"]

    by_file: dict[str, dict[str, int]] = {}
    for r in results:
        fname = Path(r.file_path).name
        bucket = by_file.setdefault(fname, {
            "total": 0, "compile_fail": 0, "test_fail": 0,
            "no_coverage": 0, "error": 0,
        })
        bucket["total"] += 1
        bucket[r.status] += 1

    uncovered = [
        {"name": r.axiom_name, "file": Path(r.file_path).name,
         "line": r.start_line + 1}
        for r in results if r.status == "no_coverage"
    ]

    return {
        "summary": {
            "total_axioms": total,
            "tested": len(results),
            "compile_time_covered": counts["compile_fail"],
            "runtime_test_covered": counts["test_fail"],
            "no_coverage": counts["no_coverage"],
            "errors": counts["error"],
            "coverage_pct": round(covered / total * 100, 1) if total else 0,
        },
        "by_file": by_file,
        "uncovered_axioms": uncovered,
        "all_results": [asdict(r) for r in results],
    }


def print_summary(report: dict) -> None:
    s = report["summary"]
    total = s["total_axioms"]
    print()
    print("=" * 42)
    print(" Axiom Coverage Validation Report")
    print("=" * 42)
    def pct(n: int) -> str:
        return f"{n/total*100:4.1f}%" if total else "N/A"

    print(f"Total axioms:           {total}")
    print(f"Tested:                 {s['tested']}")
    print(f"Compile-time covered:   {s['compile_time_covered']:>3} ({pct(s['compile_time_covered'])})")
    print(f"Runtime test covered:   {s['runtime_test_covered']:>3} ({pct(s['runtime_test_covered'])})")
    print(f"No coverage:            {s['no_coverage']:>3} ({pct(s['no_coverage'])})")
    print(f"Errors/timeouts:        {s['errors']:>3} ({pct(s['errors'])})")
    print(f"\nCoverage rate: {s['coverage_pct']}%")

    uncovered = report["uncovered_axioms"]
    if uncovered:
        print(f"\n--- Uncovered Axioms ({len(uncovered)}) ---")
        for u in uncovered:
            print(f"  {u['file']}:{u['line']}  {u['name']}")

    print("\n--- Per-File Breakdown ---")
    for fname, b in sorted(report["by_file"].items()):
        print(f"  {fname:30s}  {b['total']:>3} axioms | "
              f"{b['compile_fail']:>3} compile | {b['test_fail']:>3} test | "
              f"{b['no_coverage']:>3} uncovered | {b['error']:>3} error")
    print()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Validate axiom test coverage by commenting out axioms one at a time",
    )
    p.add_argument("--file", default=None,
                   help="Only test axioms in this file (e.g. 'Equiv.lean')")
    p.add_argument("--axiom", default=None,
                   help="Only test a specific axiom by name")
    p.add_argument("--resume", action="store_true",
                   help="Resume from checkpoint file")
    p.add_argument("--checkpoint", default=str(CHECKPOINT_FILE),
                   help="Checkpoint file path")
    p.add_argument("--report", default=str(REPORT_FILE),
                   help="Report file path")
    p.add_argument("--build-timeout", type=int, default=DEFAULT_BUILD_TIMEOUT,
                   help=f"Build timeout in seconds (default: {DEFAULT_BUILD_TIMEOUT})")
    p.add_argument("--test-timeout", type=int, default=DEFAULT_TEST_TIMEOUT,
                   help=f"Test timeout in seconds (default: {DEFAULT_TEST_TIMEOUT})")
    p.add_argument("--dry-run", action="store_true",
                   help="Parse and list axioms without testing")
    p.add_argument("--verify-parse", action="store_true",
                   help="Only parse and list all declarations")
    p.add_argument("--ci", action="store_true",
                   help="CI mode: skip interactive prompts")
    p.add_argument("--self-test", action="store_true",
                   help="Check the comment-out/restore logic on a temporary file and exit")
    p.add_argument("--runtime", action="store_true",
                   help="Static runtime coverage: match test names to axiom names (no build)")
    p.add_argument("--theorems", action="store_true",
                   help="Include public theorems from Equiv/ and LSpec covers annotations")
    p.add_argument("--update-ratchet", action="store_true",
                   help="Update the axiom count ratchet file to the current count")
    return p.parse_args()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def self_test() -> None:
    """The restore logic on a temporary file: a plain round trip, an edit made elsewhere in the
    file during the run (kept; the block is restored; the run stops), and an edit of the
    commented-out block itself (the file is left alone, with a loud error)."""
    import tempfile
    src = ("theorem a : True := trivial\n\ntheorem b : True :=\n  trivial\n\n"
           "theorem c : True := trivial\n")
    with tempfile.TemporaryDirectory() as d:
        f = Path(d) / "a.lean"
        loc = AxiomLocation(name="b", file_path=str(f), start_line=2, end_line=3,
                            kind="theorem", source_lines=[])
        f.write_text(src)
        original, mutated = comment_out_axiom(f, loc)
        assert "-- theorem b" in f.read_text()
        restore_file(f, original, mutated)
        assert f.read_text() == src, "round trip"

        f.write_text(src)
        original, mutated = comment_out_axiom(f, loc)
        f.write_text(f.read_text().replace("theorem c ", "theorem c2 "))
        try:
            restore_file(f, original, mutated)
            raise AssertionError("an edit during the run was not detected")
        except ConcurrentEditError:
            pass
        assert f.read_text() == src.replace("theorem c ", "theorem c2 "), "edit kept, block restored"

        f.write_text(src)
        original, mutated = comment_out_axiom(f, loc)
        edited = f.read_text().replace("--   trivial", "--   by trivial")
        f.write_text(edited)
        try:
            restore_file(f, original, mutated)
            raise AssertionError("an edit of the block was not detected")
        except ConcurrentEditError as exc:
            assert "CRITICAL" in str(exc)
        assert f.read_text() == edited, "file left alone"
    print("Self-test passed: restore keeps concurrent edits (3 cases)")


def main() -> None:
    args = parse_args()

    if args.self_test:
        self_test()
        return

    include_theorems = getattr(args, "theorems", False)

    # Discover axioms
    all_decls: list[AxiomLocation] = []
    files_processed = 0
    for fpath in AXIOM_FILES:
        if fpath.exists():
            all_decls.extend(parse_axioms(fpath))
            files_processed += 1

    axiom_count = len(all_decls)

    # Discover theorems from Equiv/ if --theorems
    theorem_count = 0
    if include_theorems:
        equiv_files = sorted(EQUIV_DIR.rglob("*.lean")) if EQUIV_DIR.exists() else []
        for fpath in equiv_files:
            if fpath.exists():
                all_decls.extend(parse_theorems(fpath))
        theorem_count = len(all_decls) - axiom_count

    if include_theorems:
        print(f"Found {axiom_count} axioms + {theorem_count} theorems = "
              f"{len(all_decls)} declarations across {files_processed} files")
    else:
        print(f"Found {axiom_count} axioms across {files_processed} files")

    # Filters
    if args.file:
        all_decls = [a for a in all_decls if args.file in a.file_path]
        if not all_decls:
            sys.exit(f"Error: no declarations found matching file filter '{args.file}'")
        print(f"Filtered to {len(all_decls)} declarations matching '{args.file}'")

    if args.axiom:
        all_decls = [a for a in all_decls if a.name == args.axiom]
        if not all_decls:
            sys.exit(f"Error: declaration '{args.axiom}' not found")
        print(f"Testing single declaration: {args.axiom}")

    # List-only modes
    if args.verify_parse or args.dry_run:
        for ax in all_decls:
            kind = f"[{ax.kind}]" if include_theorems else ""
            print(f"  {ax.short_file}:{ax.start_line + 1}-{ax.end_line + 1}  "
                  f"{ax.name}  ({ax.line_count} lines) {kind}")
        return

    # Static runtime coverage analysis (no build needed)
    if args.runtime:
        lspec_files = LSPEC_FILES if include_theorems else None
        analysis = runtime_analysis(all_decls, lspec_files=lspec_files)
        print_runtime_report(analysis)
        report_path = Path(args.report)
        save_runtime_report(analysis, report_path)
        print(f"Full report: {report_path}")

        # Ratchet: update or check (axiom count only, not theorem count)
        if args.update_ratchet:
            RATCHET_FILE.write_text(f"{axiom_count}\n")
            print(f"Updated ratchet to {axiom_count} in {RATCHET_FILE}")
        elif RATCHET_FILE.exists():
            minimum = int(RATCHET_FILE.read_text().strip())
            if axiom_count < minimum:
                print(f"\nERROR: Axiom count regression! "
                      f"Found {axiom_count} axioms, expected >= {minimum}.",
                      file=sys.stderr)
                print("  If axioms were intentionally removed, run with "
                      "--runtime --update-ratchet", file=sys.stderr)
                sys.exit(1)
            else:
                print(f"Ratchet check passed: {axiom_count} >= {minimum}")
        return

    # Pre-flight
    preflight_checks(args.build_timeout, args.test_timeout, ci=args.ci)

    # Run
    results = run_axiom_tests(all_decls, args)

    # Report
    report = generate_report(results, all_decls)
    Path(args.report).write_text(json.dumps(report, indent=2) + "\n")
    print_summary(report)
    print(f"Full report: {args.report}")
    print(f"Checkpoint:  {args.checkpoint}")


if __name__ == "__main__":
    main()
