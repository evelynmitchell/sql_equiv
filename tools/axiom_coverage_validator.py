#!/usr/bin/env python3
"""
Axiom Coverage Validator for sql_equiv Lean 4 project.

Validates that each axiom is exercised by the test suite by:
1. Commenting out each axiom one at a time
2. Attempting to build and run tests
3. Checking whether the build fails (compile-time coverage) or tests fail (runtime coverage)
4. Reporting which axioms have no test coverage

Usage:
    python tools/axiom_coverage_validator.py                    # Run all axioms
    python tools/axiom_coverage_validator.py --verify-parse     # Just list axioms found
    python tools/axiom_coverage_validator.py --axiom and_self   # Single axiom
    python tools/axiom_coverage_validator.py --file Equiv.lean  # Single file
    python tools/axiom_coverage_validator.py --resume           # Resume from checkpoint
    python tools/axiom_coverage_validator.py --dry-run          # Parse only, no modification
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

# lake lives under ~/.elan/bin which may not be in subprocess PATH
_ELAN_BIN = Path.home() / ".elan" / "bin"
_LAKE = str(_ELAN_BIN / "lake") if _ELAN_BIN.exists() else "lake"

BUILD_CMD = [_LAKE, "build", "sql_equiv_test"]
TEST_CMD = [_LAKE, "exe", "sql_equiv_test"]

DEFAULT_BUILD_TIMEOUT = 300   # 5 minutes
DEFAULT_TEST_TIMEOUT = 120    # 2 minutes

CHECKPOINT_FILE = PROJECT_ROOT / "tools" / "axiom_coverage_checkpoint.json"
REPORT_FILE = PROJECT_ROOT / "tools" / "axiom_coverage_report.json"

AXIOM_FILES = [
    SQLEQUIV_DIR / "Equiv.lean",
    SQLEQUIV_DIR / "Semantics.lean",
    SQLEQUIV_DIR / "OptimizerUtils.lean",
    SQLEQUIV_DIR / "ExprNormalization.lean",
    SQLEQUIV_DIR / "Optimizer.lean",
    SQLEQUIV_DIR / "JoinReordering.lean",
    SQLEQUIV_DIR / "PredicatePushdown.lean",
]


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
# Axiom parsing
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
        m = re.match(r"^axiom\s+(\w+)", lines[i])
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
            ))
            i = end + 1
        else:
            i += 1
    return axioms


# ---------------------------------------------------------------------------
# File manipulation (comment-out / restore)
# ---------------------------------------------------------------------------

def comment_out_axiom(file_path: Path, axiom: AxiomLocation) -> str:
    """Comment out an axiom. Returns original file content for restoration."""
    original = file_path.read_text()
    lines = original.splitlines(keepends=True)
    for idx in range(axiom.start_line, axiom.end_line + 1):
        lines[idx] = "-- " + lines[idx]
    file_path.write_text("".join(lines))
    return original


def restore_file(file_path: Path, original: str) -> None:
    """Restore a file and verify the restoration succeeded."""
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
    t0 = time.time()

    try:
        original = comment_out_axiom(fpath, axiom)

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
            restore_file(fpath, original)


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

    total = len(axioms)
    for i, axiom in enumerate(axioms):
        if axiom.name in completed_names:
            continue
        if shutdown:
            break

        label = f"[{i + 1}/{total}] {axiom.name} ({axiom.short_file}:{axiom.start_line + 1})"
        print(f"{label} ...", end=" ", flush=True)

        result = test_single_axiom(axiom, args.build_timeout, args.test_timeout)
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
                   help="Only parse and list all axioms")
    p.add_argument("--ci", action="store_true",
                   help="CI mode: skip interactive prompts")
    return p.parse_args()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    args = parse_args()

    # Discover axioms
    all_axioms: list[AxiomLocation] = []
    files_processed = 0
    for fpath in AXIOM_FILES:
        if fpath.exists():
            all_axioms.extend(parse_axioms(fpath))
            files_processed += 1
    print(f"Found {len(all_axioms)} axioms across {files_processed} files")

    # Filters
    if args.file:
        all_axioms = [a for a in all_axioms if args.file in a.file_path]
        if not all_axioms:
            sys.exit(f"Error: no axioms found matching file filter '{args.file}'")
        print(f"Filtered to {len(all_axioms)} axioms matching '{args.file}'")

    if args.axiom:
        all_axioms = [a for a in all_axioms if a.name == args.axiom]
        if not all_axioms:
            sys.exit(f"Error: axiom '{args.axiom}' not found")
        print(f"Testing single axiom: {args.axiom}")

    # List-only modes
    if args.verify_parse or args.dry_run:
        for ax in all_axioms:
            print(f"  {ax.short_file}:{ax.start_line + 1}-{ax.end_line + 1}  "
                  f"{ax.name}  ({ax.line_count} lines)")
        return

    # Pre-flight
    preflight_checks(args.build_timeout, args.test_timeout, ci=args.ci)

    # Run
    results = run_axiom_tests(all_axioms, args)

    # Report
    report = generate_report(results, all_axioms)
    Path(args.report).write_text(json.dumps(report, indent=2) + "\n")
    print_summary(report)
    print(f"Full report: {args.report}")
    print(f"Checkpoint:  {args.checkpoint}")


if __name__ == "__main__":
    main()
