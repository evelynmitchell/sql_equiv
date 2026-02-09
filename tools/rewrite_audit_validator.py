#!/usr/bin/env python3
"""
Rewrite Audit Validator

Static analysis tool that verifies rewrite arms in standalone Expr→Expr
rewrite functions (listed in REWRITE_FUNCTIONS) have corresponding @rewrite
annotations documenting their type assumptions and guard mechanisms.

Note: inline rewrites in optimizeExpr (double negation, CASE constant folding,
empty IN-list) are not scanned — they are context-dependent optimizations
guarded by literal pattern matching, not standalone rewrite functions.

Annotation format (Lean comment above a rewrite arm):
  -- @rewrite <category> <var>:<type> [<var>:<type>...] [guard:<name>]

Categories: identity, annihilation, structural, constant-fold, idempotent
Types: int, bool, any, null
Guards: isDefinitelyBool, isDefinitelyNonInt, short_circuit, structural_eq,
        literal_match, literal_int_match, exprCompare, or any Lean function name
Pattern guards (short_circuit, literal_match, literal_int_match, structural_eq)
are enforced by pattern matching in the arm body, not by calling a named function.

Usage:
  python3 tools/rewrite_audit_validator.py [--function NAME] [--report PATH] [--verify-parse]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent

# Map of function name -> (file path relative to project root, arm patterns)
REWRITE_FUNCTIONS: dict[str, dict] = {
    # -- Optimizer.lean --
    "applyDeMorgan": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.unaryOp",
    },
    "eliminateDoubleNegation": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.unaryOp",
    },
    "applyIdentityLaws": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.binOp",
    },
    "applyIdempotentLaws": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.binOp",
    },
    "applyComplementLaws": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.binOp",
    },
    "simplifyArithmetic": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.binOp",
    },
    "constantFoldBinOp": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| some \w+, some \w+",
    },
    "constantFoldUnaryOp": {
        "file": "SqlEquiv/Optimizer.lean",
        "arm_pattern": r"^\s*\| \.\w+, some",
    },
    # -- ExprNormalization.lean --
    "normalizeExprCanonical": {
        "file": "SqlEquiv/ExprNormalization.lean",
        "arm_pattern": r"^\s*\| \.binOp \.(and|or|add|mul|eq|ne)\b",
    },
}

VALID_CATEGORIES = {"identity", "annihilation", "structural", "constant-fold", "idempotent"}
VALID_TYPES = {"int", "bool", "any", "null"}

ANNOTATION_MARKER_RE = re.compile(r"--\s*@rewrite\s+(.+)")


def parse_annotation(line: str, line_number: int) -> Annotation | None:
    """Parse a @rewrite annotation line into a structured Annotation.

    Tokenizes the annotation and classifies each token into exactly one slot:
      - First token → category
      - Tokens matching 'guard:<name>' → guard
      - Tokens matching '<name>:<type>' → variable

    Returns None if the line is not an annotation. Raises ValueError if
    the annotation is malformed (so callers can report the error).
    """
    m = ANNOTATION_MARKER_RE.search(line)
    if not m:
        return None

    tokens = m.group(1).split()
    if not tokens:
        return None

    category = tokens[0]
    variables: list[tuple[str, str]] = []
    guard: str | None = None

    for token in tokens[1:]:
        if ":" not in token:
            raise ValueError(
                f"Line {line_number}: malformed token '{token}' "
                f"(expected 'name:type' or 'guard:name')"
            )
        key, value = token.split(":", 1)
        if key == "guard":
            if guard is not None:
                raise ValueError(
                    f"Line {line_number}: duplicate guard declaration"
                )
            guard = value
        else:
            if value not in VALID_TYPES:
                raise ValueError(
                    f"Line {line_number}: invalid type '{value}' for variable '{key}' "
                    f"(valid: {', '.join(sorted(VALID_TYPES))})"
                )
            variables.append((key, value))

    if not variables:
        raise ValueError(
            f"Line {line_number}: annotation has no variable declarations"
        )

    return Annotation(
        line=line_number,
        category=category,
        variables=variables,
        guard=guard,
    )

# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------

@dataclass
class Annotation:
    line: int
    category: str
    variables: list[tuple[str, str]]  # [(name, type), ...]
    guard: str | None

@dataclass
class RewriteArm:
    line: int
    text: str
    annotation: Annotation | None = None

@dataclass
class FunctionAudit:
    name: str
    file: str
    arms: list[RewriteArm] = field(default_factory=list)
    annotations: list[Annotation] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def find_function_range(lines: list[str], func_name: str) -> tuple[int, int] | None:
    """Find the start and end line indices of a function definition."""
    start = None
    for i, line in enumerate(lines):
        if re.search(rf'\bdef\s+{re.escape(func_name)}\b', line):
            start = i
            break
    if start is None:
        return None

    # Find the end: next def at same or lower indent, or end of file
    base_indent = len(lines[start]) - len(lines[start].lstrip())
    end = len(lines)
    for i in range(start + 1, len(lines)):
        stripped = lines[i].lstrip()
        if not stripped or stripped.startswith('--'):
            continue
        indent = len(lines[i]) - len(lines[i].lstrip())
        # A new top-level def or section marker at same/lower indent
        if indent <= base_indent and (
            re.match(r'(partial\s+|private\s+)?def\s+', stripped)
            or stripped.startswith('mutual')
            or stripped.startswith('end')
            or stripped.startswith('-- ==')
        ):
            end = i
            break
    return (start, end)


def is_catchall(line: str, func_name: str) -> bool:
    """Check if a match arm is a catch-all (not a rewrite)."""
    stripped = line.strip()
    # Explicit catch-alls
    if re.match(r'\| e =>', stripped):
        return True
    if re.match(r'\| _, _ =>', stripped):
        return True
    if re.match(r'\| \(_, _\)', stripped):
        return True
    # For constantFoldBinOp: `| _, _ =>` catch-all
    if func_name == "constantFoldBinOp" and re.match(r'\| _, _ =>', stripped):
        return True
    # For constantFoldUnaryOp: `| _, _ =>` catch-all
    if func_name == "constantFoldUnaryOp" and re.match(r'\| _, _ =>', stripped):
        return True
    return False


def parse_function(lines: list[str], func_name: str, config: dict) -> FunctionAudit:
    """Parse a function to find its rewrite arms and annotations."""
    file_path = config["file"]
    arm_pattern = re.compile(config["arm_pattern"])
    audit = FunctionAudit(name=func_name, file=file_path)

    fn_range = find_function_range(lines, func_name)
    if fn_range is None:
        audit.errors.append(f"Function {func_name} not found in {file_path}")
        return audit

    start, end = fn_range

    # Collect all annotations and arms within the function range
    pending_annotations: list[Annotation] = []

    for i in range(start, end):
        line = lines[i]

        # Check for annotation
        try:
            ann = parse_annotation(line, i + 1)
        except ValueError as e:
            audit.errors.append(f"Malformed annotation in {audit.file}: {e}")
            continue
        if ann is not None:
            pending_annotations.append(ann)
            audit.annotations.append(ann)
            continue

        # Check for rewrite arm
        if arm_pattern.search(line) and not is_catchall(line, func_name):
            arm = RewriteArm(line=i + 1, text=line.strip())

            # Match with closest preceding annotation (within 3 lines)
            best_ann = None
            best_dist = 4  # >3 means no match
            for ann in pending_annotations:
                dist = arm.line - ann.line
                if 0 < dist <= 3 and dist < best_dist:
                    best_ann = ann
                    best_dist = dist

            if best_ann is not None:
                arm.annotation = best_ann
                pending_annotations.remove(best_ann)

            audit.arms.append(arm)

    return audit


# ---------------------------------------------------------------------------
# Validation
# ---------------------------------------------------------------------------

def validate_audit(audit: FunctionAudit) -> None:
    """Run validation checks on a parsed function audit."""
    # Check 1: Unannotated arms (ERROR)
    for arm in audit.arms:
        if arm.annotation is None:
            audit.errors.append(
                f"Unannotated arm at {audit.file}:{arm.line}: {arm.text}"
            )

    # Check 2: Invalid category
    for ann in audit.annotations:
        if ann.category not in VALID_CATEGORIES:
            audit.errors.append(
                f"Invalid category '{ann.category}' at {audit.file}:{ann.line} "
                f"(valid: {', '.join(sorted(VALID_CATEGORIES))})"
            )

    # Check 3: Guard declared but not used in arm body (ERROR)
    # Whitelisted guards are enforced by pattern matching, not by name in code
    PATTERN_GUARDS = {"short_circuit", "literal_match", "literal_int_match", "structural_eq"}
    file_path = PROJECT_ROOT / audit.file
    if file_path.exists():
        source_lines = file_path.read_text().splitlines()
        for arm in audit.arms:
            if arm.annotation is None or not arm.annotation.guard:
                continue
            if arm.annotation.guard in PATTERN_GUARDS:
                continue
            # Find the arm body: from the arm line to the next '|' arm or end
            start_idx = arm.line - 1  # 0-based
            end_idx = len(source_lines)
            for i in range(start_idx + 1, len(source_lines)):
                if re.match(r"^\s*\| ", source_lines[i]):
                    end_idx = i
                    break
            arm_text = "\n".join(source_lines[start_idx:end_idx])
            if not re.search(rf'\b{re.escape(arm.annotation.guard)}\b', arm_text):
                audit.errors.append(
                    f"Guard '{arm.annotation.guard}' declared at {audit.file}:{arm.annotation.line} "
                    f"but not used in arm body at line {arm.line}"
                )

    # Check 4: var:int or var:bool with no guard (WARNING for identity/annihilation)
    for arm in audit.arms:
        if arm.annotation is None:
            continue
        ann = arm.annotation
        if ann.category in ("identity", "annihilation"):
            has_typed_var = any(t in ("int", "bool") for _, t in ann.variables)
            if has_typed_var and ann.guard is None:
                audit.warnings.append(
                    f"Unguarded {ann.category} rewrite at {audit.file}:{arm.line}: "
                    f"{arm.text} — type assumption without runtime guard"
                )

    # Check 5: Stale annotations (annotation with no matching arm) (WARNING)
    matched_annotation_ids = {id(arm.annotation) for arm in audit.arms if arm.annotation}
    for ann in audit.annotations:
        if id(ann) not in matched_annotation_ids:
            audit.warnings.append(
                f"Stale annotation at {audit.file}:{ann.line} — no matching arm found"
            )


# ---------------------------------------------------------------------------
# Output
# ---------------------------------------------------------------------------

def print_summary(audits: list[FunctionAudit], verify_parse: bool = False) -> None:
    """Print human-readable summary."""
    total_arms = 0
    total_annotated = 0
    total_errors = 0
    total_warnings = 0

    for audit in audits:
        total_arms += len(audit.arms)
        total_annotated += sum(1 for a in audit.arms if a.annotation)
        total_errors += len(audit.errors)
        total_warnings += len(audit.warnings)

        if verify_parse or audit.errors or audit.warnings:
            print(f"\n{'='*60}")
            print(f"  {audit.name} ({audit.file})")
            print(f"{'='*60}")

        if verify_parse:
            print(f"  Arms found: {len(audit.arms)}")
            for arm in audit.arms:
                ann_str = ""
                if arm.annotation:
                    ann_str = (
                        f" ← @rewrite {arm.annotation.category}"
                        f" {' '.join(f'{n}:{t}' for n, t in arm.annotation.variables)}"
                    )
                    if arm.annotation.guard:
                        ann_str += f" guard:{arm.annotation.guard}"
                print(f"    L{arm.line}: {arm.text[:60]}{ann_str}")
            print(f"  Annotations found: {len(audit.annotations)}")

        for err in audit.errors:
            print(f"  ERROR: {err}")
        for warn in audit.warnings:
            print(f"  WARNING: {warn}")

    print(f"\n{'='*60}")
    print(f"  SUMMARY")
    print(f"{'='*60}")
    print(f"  Functions scanned:  {len(audits)}")
    print(f"  Total rewrite arms: {total_arms}")
    print(f"  Annotated arms:     {total_annotated}")
    print(f"  Unannotated arms:   {total_arms - total_annotated}")
    print(f"  Errors:             {total_errors}")
    print(f"  Warnings:           {total_warnings}")

    if total_errors > 0:
        print(f"\n  RESULT: FAIL ({total_errors} error(s))")
    elif total_warnings > 0:
        print(f"\n  RESULT: PASS with {total_warnings} warning(s)")
    else:
        print(f"\n  RESULT: PASS (all arms annotated and guarded)")


def write_report(audits: list[FunctionAudit], path: Path) -> None:
    """Write JSON report."""
    report = {
        "functions": [],
        "summary": {
            "total_arms": 0,
            "annotated_arms": 0,
            "unannotated_arms": 0,
            "errors": 0,
            "warnings": 0,
        },
    }

    for audit in audits:
        func_entry = {
            "name": audit.name,
            "file": audit.file,
            "arms": [],
            "errors": audit.errors,
            "warnings": audit.warnings,
        }
        for arm in audit.arms:
            arm_entry = {
                "line": arm.line,
                "text": arm.text,
                "annotated": arm.annotation is not None,
            }
            if arm.annotation:
                arm_entry["annotation"] = {
                    "line": arm.annotation.line,
                    "category": arm.annotation.category,
                    "variables": [
                        {"name": n, "type": t} for n, t in arm.annotation.variables
                    ],
                    "guard": arm.annotation.guard,
                }
            func_entry["arms"].append(arm_entry)
        report["functions"].append(func_entry)

        report["summary"]["total_arms"] += len(audit.arms)
        annotated = sum(1 for a in audit.arms if a.annotation)
        report["summary"]["annotated_arms"] += annotated
        report["summary"]["unannotated_arms"] += len(audit.arms) - annotated
        report["summary"]["errors"] += len(audit.errors)
        report["summary"]["warnings"] += len(audit.warnings)

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"\n  Report written to {path}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate @rewrite annotations on optimizer rewrite arms"
    )
    parser.add_argument(
        "--function", "-f",
        help="Only check a specific function (by name)",
    )
    parser.add_argument(
        "--report", "-r",
        default="tools/rewrite_audit_report.json",
        help="Path for JSON report output (default: tools/rewrite_audit_report.json)",
    )
    parser.add_argument(
        "--verify-parse",
        action="store_true",
        help="Show detailed parse results for each function",
    )
    parser.add_argument(
        "--no-report",
        action="store_true",
        help="Skip writing the JSON report file",
    )
    args = parser.parse_args()

    # Filter functions if --function specified
    functions = REWRITE_FUNCTIONS
    if args.function:
        if args.function not in functions:
            print(f"Unknown function: {args.function}")
            print(f"Known functions: {', '.join(sorted(functions))}")
            return 1
        functions = {args.function: functions[args.function]}

    # Parse and validate each function
    # Cache file contents by path
    file_cache: dict[str, list[str]] = {}
    audits: list[FunctionAudit] = []

    for func_name, config in functions.items():
        file_path = config["file"]
        if file_path not in file_cache:
            full_path = PROJECT_ROOT / file_path
            if not full_path.exists():
                audit = FunctionAudit(name=func_name, file=file_path)
                audit.errors.append(f"File not found: {full_path}")
                audits.append(audit)
                continue
            file_cache[file_path] = full_path.read_text().splitlines()

        lines = file_cache[file_path]
        audit = parse_function(lines, func_name, config)
        validate_audit(audit)
        audits.append(audit)

    # Output
    print_summary(audits, verify_parse=args.verify_parse)
    if not args.no_report:
        report_path = Path(args.report) if Path(args.report).is_absolute() else PROJECT_ROOT / args.report
        write_report(audits, report_path)

    # Exit code
    total_errors = sum(len(a.errors) for a in audits)
    return 1 if total_errors > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
