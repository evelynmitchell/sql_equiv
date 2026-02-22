#!/usr/bin/env python3
"""
Definition Coverage Matrix Tool for sql_equiv Lean 4 project.

Analyzes evalBinOp, evalUnaryOp, evalFunc, Value.eq, Value.compare, and
Value.toBool to produce matrices showing which type combinations have
explicit match arms, which fall through to wildcards, and which may be
missing SQL semantics.

Outputs:
  Console  — summary table + gap list
  Markdown — docs/definition_coverage_matrix.md
  JSON     — tools/definition_coverage_report.json

Usage:
    uv run python tools/definition_coverage_matrix.py               # full report
    uv run python tools/definition_coverage_matrix.py --gaps-only   # gaps only
    uv run python tools/definition_coverage_matrix.py --function evalBinOp --op and
    uv run python tools/definition_coverage_matrix.py --json        # JSON only
    uv run python tools/definition_coverage_matrix.py --no-tests    # skip test scan
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

PROJECT_ROOT = Path(__file__).resolve().parent.parent
SEMANTICS_BASE = PROJECT_ROOT / "SqlEquiv" / "SemanticsBase.lean"

VALUE_TYPES = ["int", "string", "bool", "null"]
OPTION_VALUE_TYPES = ["int", "string", "bool", "null", "none"]

BINOP_OPS = [
    "add", "sub", "mul", "div", "mod",
    "eq", "ne", "lt", "le", "gt", "ge",
    "and", "or",
    "concat", "like",
]

UNARYOP_OPS = ["not", "neg", "isNull", "isNotNull"]

FUNC_DEFS = {
    "COALESCE": {"arity": "variadic", "arg_desc": "List (Option Value)"},
    "NULLIF":   {"arity": 2, "arg_desc": "[Option Value, Option Value]"},
    "ABS":      {"arity": 1, "arg_desc": "[Option Value]"},
    "LENGTH":   {"arity": 1, "arg_desc": "[Option Value]"},
    "UPPER":    {"arity": 1, "arg_desc": "[Option Value]"},
    "LOWER":    {"arity": 1, "arg_desc": "[Option Value]"},
    "CONCAT":   {"arity": 2, "arg_desc": "[Option Value, Option Value]"},
}

# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------

@dataclass
class CoverageCell:
    """One cell in a coverage matrix."""
    op: str
    left_type: str                        # for unary/toBool: "N/A"
    right_type: str                       # for unary/toBool: the single input type
    status: str                           # explicit | wildcard | delegated | value-dependent
    result_type: str                      # int | string | bool | null | none | conditional | ...
    detail: str = ""                      # extra info (delegation target, value-dep breakdown)
    line_number: int = 0
    tested: bool = False
    test_names: list[str] = field(default_factory=list)


@dataclass
class CoverageMatrix:
    """Matrix for one function (optionally one operator)."""
    function_name: str
    operator: str                         # "" for non-operator functions
    cells: list[CoverageCell] = field(default_factory=list)
    explicit_count: int = 0
    wildcard_count: int = 0
    delegated_count: int = 0
    value_dep_count: int = 0
    total_count: int = 0


@dataclass
class GapEntry:
    """A potential SQL semantics gap."""
    function: str
    op: str
    left_type: str
    right_type: str
    severity: str                         # HIGH | MEDIUM | LOW
    description: str


# ---------------------------------------------------------------------------
# Match arm parser
# ---------------------------------------------------------------------------

@dataclass
class ParsedArm:
    """A single parsed match arm."""
    patterns: list[str]                   # raw pattern strings per position
    result: str                           # raw RHS
    line_number: int
    is_multiline: bool = False


def parse_function_arms(source: str, func_name: str, start_line: int, end_line: int) -> list[ParsedArm]:
    """Extract match arms from a function body."""
    lines = source.splitlines()
    arms: list[ParsedArm] = []
    i = start_line - 1  # 0-indexed
    while i < min(end_line, len(lines)):
        line = lines[i]
        m = re.match(r'^\s*\|\s+(.+?)\s+=>\s*(.*)', line)
        if m:
            pattern_part = m.group(1).strip()
            result_part = m.group(2).strip()
            ln = i + 1
            # Handle multi-line arms (result on next line)
            if not result_part and i + 1 < len(lines):
                result_part = lines[i + 1].strip()
                is_ml = True
            else:
                is_ml = False
            # Parse patterns by splitting on commas at the top level
            patterns = _split_top_level(pattern_part)
            arms.append(ParsedArm(patterns=patterns, result=result_part, line_number=ln, is_multiline=is_ml))
        i += 1
    return arms


def _split_top_level(s: str) -> list[str]:
    """Split pattern string on top-level commas (not inside parens or brackets)."""
    parts = []
    depth = 0
    current: list[str] = []
    for ch in s:
        if ch in ('(', '['):
            depth += 1
            current.append(ch)
        elif ch in (')', ']'):
            if depth > 0:
                depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            parts.append(''.join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        parts.append(''.join(current).strip())
    return parts


def classify_pattern(pat: str) -> str:
    """Classify a pattern into a type label.

    Returns one of: a concrete type ("int", "string", "bool", "null"),
    a qualified match ("some_any", "any", "none_literal"),
    or a specific-value label ("bool_true", "bool_false").
    """
    pat = pat.strip()
    # Option Value patterns: some (.constructor ...)
    if re.match(r'^some\s+\(\.int\b', pat):
        return "int"
    if re.match(r'^some\s+\(\.string\b', pat):
        return "string"
    if re.match(r'^some\s+\(\.bool\s+true\)', pat):
        return "bool_true"
    if re.match(r'^some\s+\(\.bool\s+false\)', pat):
        return "bool_false"
    if re.match(r'^some\s+\(\.bool\b', pat):
        return "bool"
    if re.match(r'^some\s+\(\.null\b', pat):
        return "null"
    # some _ or some x — matches any Some
    if re.match(r'^some\s+[_a-z]', pat):
        return "some_any"
    # Bare Value constructor patterns (for Value.eq, Value.compare, Value.toBool)
    if re.match(r'^\.int\b', pat):
        return "int"
    if re.match(r'^\.string\b', pat):
        return "string"
    if re.match(r'^\.bool\s+true\b', pat):
        return "bool_true"
    if re.match(r'^\.bool\s+false\b', pat):
        return "bool_false"
    if re.match(r'^\.bool\b', pat):
        return "bool"
    if re.match(r'^\.null\b', pat):
        return "null"
    # Bare variable or _ — matches everything including none
    if pat == '_' or re.match(r'^[a-z_]\w*$', pat):
        return "any"
    # Operator patterns like .add, .eq (standalone, no args)
    if re.match(r'^\.\w+$', pat):
        return pat[1:]  # strip the dot
    # String literals (evalFunc function names)
    if pat.startswith('"') and pat.endswith('"'):
        return pat.strip('"')
    return pat


def classify_result(result: str) -> str:
    """Classify a match arm's RHS into a result type."""
    # Strip inline comments (-- ...)
    result = re.sub(r'\s*--.*$', '', result).strip()
    if result.startswith("some (.int"):
        return "int"
    if result.startswith("some (.string"):
        return "string"
    if result.startswith("some (.bool"):
        return "bool"
    if result.startswith("some (.null"):
        return "null"
    if re.match(r'^\(.*\.eq\b.*\)\.map\s+Value\.bool', result):
        return "delegated_eq"
    if re.match(r'^\(.*\.eq\b.*\)\.map\s+\(fun', result):
        return "delegated_eq"
    if re.match(r'^\(.*\.compare\b.*\)\.map', result):
        return "delegated_compare"
    if result == "none":
        return "none"
    if result.startswith("if"):
        return "conditional"
    if "isNullValue" in result:
        return "bool"  # isNull/isNotNull always return bool
    # Value-level results: some (a == b), some (n != 0)
    if result.startswith("some") and ("==" in result or "!=" in result):
        return "bool"
    if "Ord.compare" in result:
        return "ordering"
    # `some variable` — could be passthrough (evalFunc) or bool (Value.toBool)
    # Context determines meaning; classify as "passthrough" for now
    if re.match(r'^some\s+[a-z_]\w*$', result):
        return "passthrough"
    if result.startswith("some (.") and not any(
        result.startswith(f"some (.{t}") for t in ("int", "string", "bool", "null")
    ):
        return "passthrough"
    return "other"


# ---------------------------------------------------------------------------
# Function locator
# ---------------------------------------------------------------------------

def find_function_range(source: str, name: str) -> tuple[int, int]:
    """Find the line range of a def."""
    lines = source.splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(rf'^def\s+{re.escape(name)}\b', line):
            start = i + 1  # 1-indexed
            break
    if start is None:
        return 0, 0
    # End: next top-level def or theorem or end of section
    end = len(lines)
    for i in range(start, len(lines)):
        if re.match(r'^(def|theorem|/--|end\s)', lines[i]) and i + 1 > start:
            end = i + 1  # 1-indexed
            break
    return start, end


# ---------------------------------------------------------------------------
# Matrix builder
# ---------------------------------------------------------------------------

def _pattern_matches_type(pat_class: str, type_name: str) -> bool:
    """Does a classified pattern match a given type?"""
    if pat_class == "any":
        return True
    if pat_class == "some_any" and type_name != "none":
        return True
    if pat_class == type_name:
        return True
    # bool_true / bool_false match "bool"
    if pat_class in ("bool_true", "bool_false") and type_name == "bool":
        return True
    return False


def _resolve_delegation(result_class: str, left_type: str, right_type: str,
                        value_eq_arms: list[ParsedArm],
                        value_compare_arms: list[ParsedArm]) -> str:
    """Trace through Value.eq or Value.compare to get final result."""
    if result_class == "delegated_eq":
        inner = _resolve_value_func(value_eq_arms, left_type, right_type)
        if inner == "none":
            return "none"
        return "bool"  # .map Value.bool or .map (fun b => Value.bool (!b))
    if result_class == "delegated_compare":
        inner = _resolve_value_func(value_compare_arms, left_type, right_type)
        if inner == "none":
            return "none"
        return "bool"  # .map (fun o => Value.bool ...)
    return result_class


def _resolve_value_func(arms: list[ParsedArm], left_type: str, right_type: str) -> str:
    """Check Value.eq or Value.compare arms for a (Value, Value) pair."""
    for arm in arms:
        if len(arm.patterns) < 2:
            continue
        lp = classify_pattern(arm.patterns[0])
        rp = classify_pattern(arm.patterns[1])
        if _pattern_matches_type(lp, left_type) and _pattern_matches_type(rp, right_type):
            r = classify_result(arm.result)
            if r == "other":
                # some (a == b) / some (Ord.compare a b) etc.
                return "some"
            return r
    return "none"


def build_binop_matrix(source: str, op: str,
                       binop_arms: list[ParsedArm],
                       value_eq_arms: list[ParsedArm],
                       value_compare_arms: list[ParsedArm]) -> CoverageMatrix:
    """Build coverage matrix for one BinOp operator."""
    matrix = CoverageMatrix(function_name="evalBinOp", operator=op)

    # Filter arms for this op + catch-all
    relevant_arms = []
    for arm in binop_arms:
        if len(arm.patterns) < 3:
            continue
        op_pat = classify_pattern(arm.patterns[0])
        if op_pat == op or op_pat == "any" or op_pat.startswith("_"):
            relevant_arms.append(arm)

    for lt in OPTION_VALUE_TYPES:
        for rt in OPTION_VALUE_TYPES:
            cell = _resolve_binop_cell(op, lt, rt, relevant_arms,
                                       value_eq_arms, value_compare_arms)
            matrix.cells.append(cell)
            if cell.status == "explicit":
                matrix.explicit_count += 1
            elif cell.status == "wildcard":
                matrix.wildcard_count += 1
            elif cell.status == "delegated":
                matrix.delegated_count += 1
            elif cell.status == "value-dependent":
                matrix.value_dep_count += 1
            matrix.total_count += 1

    return matrix


def _resolve_binop_cell(op: str, lt: str, rt: str,
                        arms: list[ParsedArm],
                        value_eq_arms: list[ParsedArm],
                        value_compare_arms: list[ParsedArm]) -> CoverageCell:
    """Resolve a single (op, left_type, right_type) cell."""
    # For AND/OR with bool inputs, check value-dependent behavior
    if op in ("and", "or") and (lt == "bool" or rt == "bool"):
        return _resolve_value_dependent_cell(op, lt, rt, arms,
                                              value_eq_arms, value_compare_arms)

    # Normal resolution: first matching arm wins
    for arm in arms:
        lp = classify_pattern(arm.patterns[1])
        rp = classify_pattern(arm.patterns[2])
        if _pattern_matches_type(lp, lt) and _pattern_matches_type(rp, rt):
            rc = classify_result(arm.result)
            is_explicit = (lp not in ("any", "some_any") or rp not in ("any", "some_any"))

            if rc.startswith("delegated_"):
                resolved = _resolve_delegation(rc, lt, rt,
                                                value_eq_arms, value_compare_arms)
                return CoverageCell(
                    op=op, left_type=lt, right_type=rt,
                    status="delegated", result_type=resolved,
                    detail=f"via {rc.split('_')[1]}",
                    line_number=arm.line_number,
                )

            if rc == "conditional":
                return CoverageCell(
                    op=op, left_type=lt, right_type=rt,
                    status="explicit", result_type="conditional",
                    detail=arm.result,
                    line_number=arm.line_number,
                )

            status = "explicit" if is_explicit else "wildcard"
            # Catch-all arm at the end
            if lp == "any" and rp == "any":
                status = "wildcard"

            return CoverageCell(
                op=op, left_type=lt, right_type=rt,
                status=status, result_type=rc,
                line_number=arm.line_number,
            )

    # No arm matched — shouldn't happen with catch-all
    return CoverageCell(
        op=op, left_type=lt, right_type=rt,
        status="wildcard", result_type="none",
    )


def _resolve_value_dependent_cell(op: str, lt: str, rt: str,
                                   arms: list[ParsedArm],
                                   value_eq_arms: list[ParsedArm],
                                   value_compare_arms: list[ParsedArm]) -> CoverageCell:
    """Resolve AND/OR cells where bool value matters."""
    results: dict[str, tuple[str, str, int]] = {}  # value -> (status, result, line)

    bool_values = ["bool_true", "bool_false"]
    for bv in bool_values:
        effective_lt = bv if lt == "bool" else lt
        effective_rt = bv if rt == "bool" else rt
        for arm in arms:
            lp = classify_pattern(arm.patterns[1])
            rp = classify_pattern(arm.patterns[2])
            if _pattern_matches_value(lp, effective_lt) and _pattern_matches_value(rp, effective_rt):
                rc = classify_result(arm.result)
                is_explicit = lp not in ("any",) and rp not in ("any",)
                status = "explicit" if is_explicit else "wildcard"
                if lp == "any" and rp == "any":
                    status = "wildcard"
                results[bv] = (status, rc, arm.line_number)
                break
        else:
            results[bv] = ("wildcard", "none", 0)

    # Both bool values AND both sides being bool
    if lt == "bool" and rt == "bool":
        # Check all 4 combinations
        combos: dict[str, tuple[str, str, int]] = {}
        for lv in bool_values:
            for rv in bool_values:
                for arm in arms:
                    lp = classify_pattern(arm.patterns[1])
                    rp = classify_pattern(arm.patterns[2])
                    if _pattern_matches_value(lp, lv) and _pattern_matches_value(rp, rv):
                        rc = classify_result(arm.result)
                        combos[f"{lv},{rv}"] = ("explicit", rc, arm.line_number)
                        break
                else:
                    combos[f"{lv},{rv}"] = ("wildcard", "none", 0)
        # If all combos yield the same result, simplify
        unique_results = set(v[1] for v in combos.values())
        if len(unique_results) == 1:
            r = list(combos.values())[0]
            return CoverageCell(
                op=op, left_type=lt, right_type=rt,
                status="explicit", result_type=r[1],
                line_number=r[2],
            )
        detail_parts = []
        for k, v in combos.items():
            detail_parts.append(f"{k}={v[1]}")
        return CoverageCell(
            op=op, left_type=lt, right_type=rt,
            status="explicit", result_type="bool",
            detail="; ".join(detail_parts),
            line_number=list(combos.values())[0][2],
        )

    # Check if results differ
    true_res = results.get("bool_true", ("wildcard", "none", 0))
    false_res = results.get("bool_false", ("wildcard", "none", 0))

    if true_res[1] == false_res[1] and true_res[0] == false_res[0]:
        return CoverageCell(
            op=op, left_type=lt, right_type=rt,
            status=true_res[0], result_type=true_res[1],
            line_number=true_res[2],
        )

    detail = f"true={true_res[1]}, false={false_res[1]}"
    return CoverageCell(
        op=op, left_type=lt, right_type=rt,
        status="value-dependent",
        result_type="varies",
        detail=detail,
        line_number=true_res[2] or false_res[2],
    )


def _pattern_matches_value(pat_class: str, value: str) -> bool:
    """Match a pattern against a specific value (including bool_true/bool_false)."""
    if pat_class == "any":
        return True
    if pat_class == "some_any" and value != "none":
        return True
    if pat_class == value:
        return True
    # "bool" pattern matches bool_true and bool_false
    if pat_class == "bool" and value in ("bool_true", "bool_false", "bool"):
        return True
    if pat_class == "null" and value == "null":
        return True
    if pat_class == "int" and value == "int":
        return True
    if pat_class == "string" and value == "string":
        return True
    return False


def build_unaryop_matrix(source: str, op: str,
                         unary_arms: list[ParsedArm]) -> CoverageMatrix:
    """Build coverage matrix for one UnaryOp operator."""
    matrix = CoverageMatrix(function_name="evalUnaryOp", operator=op)

    relevant_arms = []
    for arm in unary_arms:
        if len(arm.patterns) < 2:
            continue
        op_pat = classify_pattern(arm.patterns[0])
        if op_pat == op or op_pat == "any" or op_pat.startswith("_"):
            relevant_arms.append(arm)

    for vt in OPTION_VALUE_TYPES:
        for arm in relevant_arms:
            vp = classify_pattern(arm.patterns[1])
            if _pattern_matches_type(vp, vt):
                rc = classify_result(arm.result)
                is_explicit = vp not in ("any",)
                status = "explicit" if is_explicit else "wildcard"
                if vp == "any" and classify_pattern(arm.patterns[0]) == "any":
                    status = "wildcard"
                # isNull/isNotNull with bare variable are total — mark explicit
                if op in ("isNull", "isNotNull") and vp == "any" and classify_pattern(arm.patterns[0]) == op:
                    status = "explicit"
                cell = CoverageCell(
                    op=op, left_type="N/A", right_type=vt,
                    status=status, result_type=rc,
                    line_number=arm.line_number,
                )
                matrix.cells.append(cell)
                if status == "explicit":
                    matrix.explicit_count += 1
                else:
                    matrix.wildcard_count += 1
                matrix.total_count += 1
                break
        else:
            cell = CoverageCell(
                op=op, left_type="N/A", right_type=vt,
                status="wildcard", result_type="none",
            )
            matrix.cells.append(cell)
            matrix.wildcard_count += 1
            matrix.total_count += 1

    return matrix


def build_value_func_matrix(source: str, func_name: str,
                            arms: list[ParsedArm]) -> CoverageMatrix:
    """Build matrix for Value.eq, Value.compare, Value.toBool."""
    matrix = CoverageMatrix(function_name=func_name, operator="")

    if func_name == "Value.toBool":
        for vt in VALUE_TYPES:
            for arm in arms:
                if len(arm.patterns) < 1:
                    continue
                vp = classify_pattern(arm.patterns[0])
                if _pattern_matches_type(vp, vt):
                    rc = classify_result(arm.result)
                    # Value.toBool returns Option Bool, not Option Value
                    # "passthrough" (some b) and "other" are both bool results
                    if rc in ("passthrough", "other"):
                        rc = "bool"
                    status = "explicit" if vp not in ("any",) else "wildcard"
                    cell = CoverageCell(
                        op="toBool", left_type="N/A", right_type=vt,
                        status=status, result_type=rc,
                        line_number=arm.line_number,
                    )
                    matrix.cells.append(cell)
                    if status == "explicit":
                        matrix.explicit_count += 1
                    else:
                        matrix.wildcard_count += 1
                    matrix.total_count += 1
                    break
    else:
        # Value.eq and Value.compare: 4x4 matrix
        for lt in VALUE_TYPES:
            for rt in VALUE_TYPES:
                for arm in arms:
                    if len(arm.patterns) < 2:
                        continue
                    lp = classify_pattern(arm.patterns[0])
                    rp = classify_pattern(arm.patterns[1])
                    if _pattern_matches_type(lp, lt) and _pattern_matches_type(rp, rt):
                        rc = classify_result(arm.result)
                        if rc == "other":
                            # some (a == b) etc.
                            if "==" in arm.result:
                                rc = "bool"
                            elif "Ord.compare" in arm.result:
                                rc = "ordering"
                            else:
                                rc = "some"
                        status = "explicit" if (lp not in ("any",) or rp not in ("any",)) else "wildcard"
                        if lp == "any" and rp == "any":
                            status = "wildcard"
                        cell = CoverageCell(
                            op=func_name.split(".")[-1], left_type=lt, right_type=rt,
                            status=status, result_type=rc,
                            line_number=arm.line_number,
                        )
                        matrix.cells.append(cell)
                        if status == "explicit":
                            matrix.explicit_count += 1
                        else:
                            matrix.wildcard_count += 1
                        matrix.total_count += 1
                        break

    return matrix


def build_evalfunc_matrix(source: str, func_arms: list[ParsedArm]) -> list[CoverageMatrix]:
    """Build per-function matrices for evalFunc."""
    matrices: list[CoverageMatrix] = []

    for func_name, fdef in FUNC_DEFS.items():
        matrix = CoverageMatrix(function_name="evalFunc", operator=func_name)

        if func_name == "COALESCE":
            # Variadic — special: covers any list input
            cell = CoverageCell(
                op="COALESCE", left_type="N/A", right_type="List(Option Value)",
                status="explicit", result_type="passthrough",
                detail="first non-null via isNullValue filter",
            )
            _find_line_for_func(func_arms, "COALESCE", cell)
            matrix.cells.append(cell)
            matrix.explicit_count += 1
            matrix.total_count += 1
            # Note: COALESCE conflates none (error) with null
            matrices.append(matrix)
            continue

        if fdef["arity"] == 1:
            for vt in OPTION_VALUE_TYPES:
                cell = _resolve_func_cell(func_name, [vt], func_arms)
                matrix.cells.append(cell)
                if cell.status == "explicit":
                    matrix.explicit_count += 1
                else:
                    matrix.wildcard_count += 1
                matrix.total_count += 1

        elif fdef["arity"] == 2:
            for lt in OPTION_VALUE_TYPES:
                for rt in OPTION_VALUE_TYPES:
                    cell = _resolve_func_cell(func_name, [lt, rt], func_arms)
                    matrix.cells.append(cell)
                    if cell.status == "explicit":
                        matrix.explicit_count += 1
                    elif cell.status == "delegated":
                        matrix.delegated_count += 1
                    else:
                        matrix.wildcard_count += 1
                    matrix.total_count += 1

        matrices.append(matrix)

    return matrices


def _find_line_for_func(arms: list[ParsedArm], func_name: str, cell: CoverageCell) -> None:
    """Find the source line for a function arm."""
    for arm in arms:
        if len(arm.patterns) >= 1 and func_name.upper() in arm.patterns[0].upper():
            cell.line_number = arm.line_number
            break


def _resolve_func_cell(func_name: str, arg_types: list[str],
                       arms: list[ParsedArm]) -> CoverageCell:
    """Resolve one evalFunc cell."""
    for arm in arms:
        if len(arm.patterns) < 2:
            continue
        # Pattern 0 is the function name, pattern 1 is the args pattern
        fn_pat = arm.patterns[0].strip().strip('"')
        if fn_pat.upper() != func_name.upper() and fn_pat != "_":
            continue

        args_str = arm.patterns[1].strip()
        arg_pats = _parse_func_args(args_str)

        if arg_pats is None:
            # Catch-all
            if args_str == "_":
                return CoverageCell(
                    op=func_name, left_type=arg_types[0] if len(arg_types) >= 1 else "N/A",
                    right_type=arg_types[-1] if len(arg_types) >= 2 else arg_types[0] if arg_types else "N/A",
                    status="wildcard", result_type="none",
                    line_number=arm.line_number,
                )
            continue

        if len(arg_pats) != len(arg_types):
            continue

        match = True
        for ap, at_ in zip(arg_pats, arg_types):
            if not _pattern_matches_type(classify_pattern(ap), at_):
                match = False
                break

        if match:
            rc = classify_result(arm.result)
            # Check delegation in NULLIF
            if "eq" in arm.result and func_name == "NULLIF":
                rc = "conditional"

            lt = arg_types[0] if len(arg_types) >= 1 else "N/A"
            rt = arg_types[-1] if len(arg_types) >= 2 else (arg_types[0] if arg_types else "N/A")

            return CoverageCell(
                op=func_name,
                left_type=lt,
                right_type=rt,
                status="explicit",
                result_type=rc,
                detail=arm.result if rc == "conditional" else "",
                line_number=arm.line_number,
            )

    # Fall through to catch-all
    lt = arg_types[0] if len(arg_types) >= 1 else "N/A"
    rt = arg_types[-1] if len(arg_types) >= 2 else (arg_types[0] if arg_types else "N/A")
    return CoverageCell(
        op=func_name, left_type=lt, right_type=rt,
        status="wildcard", result_type="none",
    )


def _parse_func_args(args_str: str) -> Optional[list[str]]:
    """Parse [arg1, arg2, ...] into individual arg patterns. Returns None for catch-all."""
    args_str = args_str.strip()
    if args_str == "_":
        return None
    if not args_str.startswith("[") or not args_str.endswith("]"):
        # Could be 'vals' or other variable
        return None
    inner = args_str[1:-1].strip()
    if not inner:
        return []
    return _split_top_level(inner)


# ---------------------------------------------------------------------------
# SQL semantics gap classifier
# ---------------------------------------------------------------------------

# Static knowledge base: (function, op, left, right) -> (severity, description)
KNOWN_GAPS: list[dict] = [
    {"function": "evalFunc", "op": "ABS", "types": [("string",), ("bool",)],
     "severity": "LOW", "desc": "ABS(string/bool) — not valid SQL, wildcard correct"},
    {"function": "evalFunc", "op": "CONCAT", "types": [],
     "severity": "MEDIUM", "desc": "CONCAT null type preserved (evalFunc) vs lost (evalBinOp .concat)"},
    {"function": "evalFunc", "op": "COALESCE", "types": [],
     "severity": "LOW", "desc": "COALESCE conflates none (error) with null via isNullValue"},
    {"function": "Value.compare", "op": "compare", "types": [("bool", "bool")],
     "severity": "LOW", "desc": "Value.compare has no bool×bool arm — some SQL dialects support this"},
]

INTENTIONAL_WILDCARDS = {
    # (function, op, left, right) -> reason
    ("evalBinOp", "add", "string", "string"): "Not valid SQL (string + string)",
    ("evalBinOp", "add", "bool", "bool"): "Not valid SQL (bool + bool)",
    ("evalBinOp", "sub", "string", "string"): "Not valid SQL",
    ("evalBinOp", "sub", "bool", "bool"): "Not valid SQL",
    ("evalBinOp", "mul", "string", "string"): "Not valid SQL",
    ("evalBinOp", "mul", "bool", "bool"): "Not valid SQL",
    ("evalBinOp", "div", "string", "string"): "Not valid SQL",
    ("evalBinOp", "div", "bool", "bool"): "Not valid SQL",
    ("evalBinOp", "mod", "string", "string"): "Not valid SQL",
    ("evalBinOp", "mod", "bool", "bool"): "Not valid SQL",
    ("evalBinOp", "concat", "int", "int"): "Not valid SQL (int || int)",
    ("evalBinOp", "concat", "bool", "bool"): "Not valid SQL",
    ("evalBinOp", "like", "int", "int"): "Not valid SQL",
    ("evalBinOp", "like", "bool", "bool"): "Not valid SQL",
}


def classify_gaps(matrices: list[CoverageMatrix]) -> list[GapEntry]:
    """Find potential SQL semantics gaps across all matrices."""
    gaps: list[GapEntry] = []

    # Check known gaps from static knowledge base
    for gap_def in KNOWN_GAPS:
        if gap_def["types"]:
            for type_combo in gap_def["types"]:
                gaps.append(GapEntry(
                    function=gap_def["function"],
                    op=gap_def["op"],
                    left_type=type_combo[0] if len(type_combo) > 1 else "N/A",
                    right_type=type_combo[-1],
                    severity=gap_def["severity"],
                    description=gap_def["desc"],
                ))
        else:
            gaps.append(GapEntry(
                function=gap_def["function"],
                op=gap_def["op"],
                left_type="N/A",
                right_type="N/A",
                severity=gap_def["severity"],
                description=gap_def["desc"],
            ))

    # Scan for delegated→none cells (delegation resolves to error)
    # Skip cross-type pairs — SQL standard doesn't allow cross-type comparisons
    for m in matrices:
        for cell in m.cells:
            if cell.status == "delegated" and cell.result_type == "none":
                # Cross-type comparisons are intentional wildcards
                if cell.left_type != cell.right_type and \
                   cell.left_type not in ("none", "null") and \
                   cell.right_type not in ("none", "null"):
                    continue
                key = (m.function_name, cell.op, cell.left_type, cell.right_type)
                if key not in INTENTIONAL_WILDCARDS:
                    gaps.append(GapEntry(
                        function=m.function_name,
                        op=cell.op,
                        left_type=cell.left_type,
                        right_type=cell.right_type,
                        severity="LOW",
                        description=f"Delegation to {cell.detail} returns none for {cell.left_type}×{cell.right_type}",
                    ))

    return gaps


# ---------------------------------------------------------------------------
# Test cross-referencer
# ---------------------------------------------------------------------------

TEST_FILES = [
    PROJECT_ROOT / "Test" / "AxiomCoverageTest.lean",
    PROJECT_ROOT / "LSpecTests" / "NullSemantics.lean",
    PROJECT_ROOT / "LSpecTests" / "ExprAlgebra.lean",
]


def scan_tests() -> dict[str, list[str]]:
    """Scan test files for function/op/type references.

    Returns a dict mapping (function, op, left_type, right_type) keys
    to lists of test names.
    """
    coverage: dict[str, list[str]] = {}

    for test_file in TEST_FILES:
        if not test_file.exists():
            continue
        text = test_file.read_text()
        _scan_evalBinOp_tests(text, coverage, test_file.name)
        _scan_evalUnaryOp_tests(text, coverage, test_file.name)
        _scan_evalFunc_tests(text, coverage, test_file.name)

    return coverage


def _current_test_name(text: str, pos: int) -> str:
    """Find the nearest test name before pos."""
    # Look for .pass "name" or check ... "name" patterns
    chunk = text[:pos]
    # LSpec check pattern
    m = list(re.finditer(r'check\s+(?:\([^)]*\)\s+)?"([^"]+)"', chunk))
    if m:
        return m[-1].group(1)
    # .pass/.fail pattern
    m = list(re.finditer(r'\.(pass|fail)\s+"([^"]+)"', chunk))
    if m:
        return m[-1].group(2)
    return "unknown"


def _scan_evalBinOp_tests(text: str, coverage: dict[str, list[str]], filename: str) -> None:
    """Find evalBinOp references and map to (op, left_type, right_type)."""
    for m in re.finditer(
        r'evalBinOp\s+\.(\w+)\s+'
        r'\(?(some\s+\(\.(\w+)[^)]*\)|some\s+\w+|none)\)?\s+'
        r'\(?(some\s+\(\.(\w+)[^)]*\)|some\s+\w+|none)\)?',
        text
    ):
        op = m.group(1)
        lt = _extract_type_from_match(m.group(2), m.group(3))
        rt = _extract_type_from_match(m.group(4), m.group(5))
        tname = _current_test_name(text, m.start())
        key = f"evalBinOp|{op}|{lt}|{rt}"
        coverage.setdefault(key, []).append(f"{filename}: {tname}")

    # Universal quantifier patterns: ∀ v : Value
    for m in re.finditer(
        r'∀\s+\w+\s*:\s*Value.*?evalBinOp\s+\.(\w+)\s+'
        r'\(?(some\s+\(\.(\w+)[^)]*\)|some\s+\w+|none)\)?',
        text, re.DOTALL
    ):
        op = m.group(1)
        lt = _extract_type_from_match(m.group(2), m.group(3))
        tname = _current_test_name(text, m.start())
        # Quantified over all Value types
        for vt in VALUE_TYPES:
            key = f"evalBinOp|{op}|{lt}|{vt}"
            coverage.setdefault(key, []).append(f"{filename}: {tname} (∀ Value)")


def _scan_evalUnaryOp_tests(text: str, coverage: dict[str, list[str]], filename: str) -> None:
    """Find evalUnaryOp references."""
    for m in re.finditer(
        r'evalUnaryOp\s+\.(\w+)\s+'
        r'\(?(some\s+\(\.(\w+)[^)]*\)|some\s+\w+|none)\)?',
        text
    ):
        op = m.group(1)
        vt = _extract_type_from_match(m.group(2), m.group(3))
        tname = _current_test_name(text, m.start())
        key = f"evalUnaryOp|{op}|N/A|{vt}"
        coverage.setdefault(key, []).append(f"{filename}: {tname}")

    # Universal quantifier: ∀ v : Value
    for m in re.finditer(
        r'∀\s+\w+\s*:\s*Value.*?evalUnaryOp\s+\.(\w+)',
        text, re.DOTALL
    ):
        op = m.group(1)
        tname = _current_test_name(text, m.start())
        for vt in VALUE_TYPES:
            key = f"evalUnaryOp|{op}|N/A|{vt}"
            coverage.setdefault(key, []).append(f"{filename}: {tname} (∀ Value)")


def _scan_evalFunc_tests(text: str, coverage: dict[str, list[str]], filename: str) -> None:
    """Find evalFunc references."""
    for m in re.finditer(r'evalFunc\s+"(\w+)"\s+\[([^\]]*)\]', text):
        func = m.group(1).upper()
        args_str = m.group(2)
        tname = _current_test_name(text, m.start())
        types = []
        for arg_m in re.finditer(r'some\s+\(\.(\w+)', args_str):
            types.append(arg_m.group(1))
        if not types:
            if "none" in args_str:
                types = ["none"]
        lt = types[0] if len(types) >= 1 else "N/A"
        rt = types[-1] if len(types) >= 2 else (types[0] if types else "N/A")
        key = f"evalFunc|{func}|{lt}|{rt}"
        coverage.setdefault(key, []).append(f"{filename}: {tname}")


def _extract_type_from_match(full: Optional[str], constructor: Optional[str]) -> str:
    """Extract type from regex match groups."""
    if constructor:
        return constructor
    if full and full.strip() == "none":
        return "none"
    if full and full.startswith("some"):
        return "some_any"
    return "any"


def apply_test_coverage(matrices: list[CoverageMatrix], test_map: dict[str, list[str]]) -> None:
    """Mark cells as tested based on test cross-reference."""
    for m in matrices:
        for cell in m.cells:
            key = f"{m.function_name}|{cell.op}|{cell.left_type}|{cell.right_type}"
            if key in test_map:
                cell.tested = True
                cell.test_names = test_map[key]


# ---------------------------------------------------------------------------
# Report generators
# ---------------------------------------------------------------------------

def _cell_symbol(cell: CoverageCell) -> str:
    """Short display symbol for a cell."""
    if cell.status == "wildcard":
        sym = "\u2717"  # ✗
    elif cell.status == "value-dependent":
        sym = "v-dep"
    elif cell.status == "delegated":
        sym = cell.result_type
    elif cell.result_type == "conditional":
        sym = "cond"
    else:
        sym = cell.result_type

    suffix = ""
    if cell.tested:
        suffix = " [T]"
    return sym + suffix


def generate_markdown(matrices: list[CoverageMatrix], gaps: list[GapEntry]) -> str:
    """Generate full markdown report."""
    lines: list[str] = []
    lines.append("# Definition Coverage Matrix Report")
    lines.append("")
    lines.append("Auto-generated by `tools/definition_coverage_matrix.py`.")
    lines.append("")

    # Summary
    total_cells = sum(m.total_count for m in matrices)
    total_explicit = sum(m.explicit_count for m in matrices)
    total_wildcard = sum(m.wildcard_count for m in matrices)
    total_delegated = sum(m.delegated_count for m in matrices)
    total_valdep = sum(m.value_dep_count for m in matrices)

    lines.append("## Summary")
    lines.append("")
    lines.append(f"| Metric | Count |")
    lines.append(f"|--------|-------|")
    lines.append(f"| Total cells | {total_cells} |")
    lines.append(f"| Explicit arms | {total_explicit} |")
    lines.append(f"| Wildcard (none/error) | {total_wildcard} |")
    lines.append(f"| Delegated | {total_delegated} |")
    lines.append(f"| Value-dependent | {total_valdep} |")
    lines.append(f"| Potential gaps | {len(gaps)} |")
    lines.append("")

    # Per-function matrices
    for m in matrices:
        lines.append(f"## {m.function_name}" + (f" .{m.operator}" if m.operator else ""))
        lines.append("")
        lines.append(f"Explicit: {m.explicit_count} | Wildcard: {m.wildcard_count}"
                      + (f" | Delegated: {m.delegated_count}" if m.delegated_count else "")
                      + (f" | Value-dep: {m.value_dep_count}" if m.value_dep_count else ""))
        lines.append("")

        if m.function_name == "evalBinOp":
            _render_2d_matrix(lines, m, OPTION_VALUE_TYPES, OPTION_VALUE_TYPES)
        elif m.function_name == "evalUnaryOp":
            _render_1d_matrix(lines, m, OPTION_VALUE_TYPES)
        elif m.function_name == "Value.toBool":
            _render_1d_matrix(lines, m, VALUE_TYPES)
        elif m.function_name in ("Value.eq", "Value.compare"):
            _render_2d_matrix(lines, m, VALUE_TYPES, VALUE_TYPES)
        elif m.function_name == "evalFunc":
            if m.operator == "COALESCE":
                lines.append("Variadic function — handles any list input.")
                if m.cells:
                    lines.append(f"  Status: {m.cells[0].status}, Detail: {m.cells[0].detail}")
            elif any(c.left_type == c.right_type == c.op for c in m.cells):
                # 1-arity
                _render_1d_matrix(lines, m, OPTION_VALUE_TYPES)
            else:
                arity = FUNC_DEFS.get(m.operator, {}).get("arity", 1)
                if arity == 1:
                    _render_1d_matrix(lines, m, OPTION_VALUE_TYPES)
                else:
                    _render_2d_matrix(lines, m, OPTION_VALUE_TYPES, OPTION_VALUE_TYPES)
        lines.append("")

    # Gaps section
    if gaps:
        lines.append("## Potential Gaps")
        lines.append("")
        lines.append("| Severity | Function | Op | Types | Description |")
        lines.append("|----------|----------|----|-------|-------------|")
        for g in sorted(gaps, key=lambda x: {"HIGH": 0, "MEDIUM": 1, "LOW": 2}[x.severity]):
            types = f"{g.left_type}×{g.right_type}" if g.left_type != "N/A" else g.right_type
            lines.append(f"| **{g.severity}** | {g.function} | {g.op} | {types} | {g.description} |")
        lines.append("")

    # Legend
    lines.append("## Legend")
    lines.append("")
    lines.append("- **int/string/bool/null** — explicit arm returning that type")
    lines.append("- **\u2717** — wildcard (falls through to `none`/error)")
    lines.append("- **cond** — conditional result (e.g., div-by-zero check)")
    lines.append("- **v-dep** — value-dependent (different bool values give different results)")
    lines.append("- **[T]** — tested by at least one test case")
    lines.append("- **delegated** — result resolved through Value.eq or Value.compare")
    lines.append("")

    return "\n".join(lines)


def _render_2d_matrix(lines: list[str], m: CoverageMatrix,
                      row_types: list[str], col_types: list[str]) -> None:
    """Render a 2D matrix as a markdown table."""
    # Build lookup
    cell_map: dict[tuple[str, str], CoverageCell] = {}
    for c in m.cells:
        cell_map[(c.left_type, c.right_type)] = c

    # Header
    hdr = "| |" + "|".join(f" {ct} " for ct in col_types) + "|"
    sep = "|---|" + "|".join("---" for _ in col_types) + "|"
    lines.append(hdr)
    lines.append(sep)

    for rt in row_types:
        row_parts = [f"| **{rt}** "]
        for ct in col_types:
            cell = cell_map.get((rt, ct))
            if cell:
                row_parts.append(f"| {_cell_symbol(cell)} ")
            else:
                row_parts.append("| ? ")
        row_parts.append("|")
        lines.append("".join(row_parts))


def _render_1d_matrix(lines: list[str], m: CoverageMatrix,
                      types: list[str]) -> None:
    """Render a 1D matrix as a markdown table."""
    hdr = "| Type | Result | Status | Tested |"
    sep = "|------|--------|--------|--------|"
    lines.append(hdr)
    lines.append(sep)
    cell_map = {c.right_type: c for c in m.cells}
    for t in types:
        cell = cell_map.get(t)
        if cell:
            tested = "Yes" if cell.tested else "No"
            lines.append(f"| {t} | {cell.result_type} | {cell.status} | {tested} |")
        else:
            lines.append(f"| {t} | ? | ? | No |")


def generate_json(matrices: list[CoverageMatrix], gaps: list[GapEntry]) -> dict:
    """Generate JSON report."""
    total_cells = sum(m.total_count for m in matrices)
    total_explicit = sum(m.explicit_count for m in matrices)
    total_wildcard = sum(m.wildcard_count for m in matrices)
    total_delegated = sum(m.delegated_count for m in matrices)
    total_valdep = sum(m.value_dep_count for m in matrices)

    return {
        "summary": {
            "total_cells": total_cells,
            "explicit": total_explicit,
            "wildcard": total_wildcard,
            "delegated": total_delegated,
            "value_dependent": total_valdep,
            "gaps": len(gaps),
        },
        "matrices": [
            {
                "function": m.function_name,
                "operator": m.operator,
                "explicit": m.explicit_count,
                "wildcard": m.wildcard_count,
                "delegated": m.delegated_count,
                "value_dependent": m.value_dep_count,
                "total": m.total_count,
                "cells": [asdict(c) for c in m.cells],
            }
            for m in matrices
        ],
        "gaps": [asdict(g) for g in gaps],
    }


def print_console_summary(matrices: list[CoverageMatrix], gaps: list[GapEntry]) -> None:
    """Print concise console summary."""
    total_cells = sum(m.total_count for m in matrices)
    total_explicit = sum(m.explicit_count for m in matrices)
    total_wildcard = sum(m.wildcard_count for m in matrices)
    total_delegated = sum(m.delegated_count for m in matrices)
    total_valdep = sum(m.value_dep_count for m in matrices)
    total_tested = sum(1 for m in matrices for c in m.cells if c.tested)

    print("=" * 60)
    print("  Definition Coverage Matrix — Summary")
    print("=" * 60)
    print(f"  Total cells analyzed:  {total_cells}")
    print(f"  Explicit match arms:   {total_explicit}")
    print(f"  Wildcard (none/error): {total_wildcard}")
    print(f"  Delegated:             {total_delegated}")
    print(f"  Value-dependent:       {total_valdep}")
    print(f"  Tested cells:          {total_tested}")
    print(f"  Potential gaps:        {len(gaps)}")
    print()

    # Per-function summary
    print(f"  {'Function':<30} {'Expl':>5} {'Wild':>5} {'Deleg':>5} {'VDep':>5} {'Total':>5}")
    print(f"  {'-'*30} {'-'*5} {'-'*5} {'-'*5} {'-'*5} {'-'*5}")
    for m in matrices:
        name = f"{m.function_name}" + (f" .{m.operator}" if m.operator else "")
        print(f"  {name:<30} {m.explicit_count:>5} {m.wildcard_count:>5} "
              f"{m.delegated_count:>5} {m.value_dep_count:>5} {m.total_count:>5}")
    print()

    # Gaps
    if gaps:
        print("  Potential Gaps:")
        for g in sorted(gaps, key=lambda x: {"HIGH": 0, "MEDIUM": 1, "LOW": 2}[x.severity]):
            types = f"{g.left_type}x{g.right_type}" if g.left_type != "N/A" else g.right_type
            print(f"    [{g.severity:>6}] {g.function} {g.op} ({types}): {g.description}")
        print()


# ---------------------------------------------------------------------------
# Main orchestrator
# ---------------------------------------------------------------------------

def run(args: argparse.Namespace) -> None:
    """Main entry point."""
    if not SEMANTICS_BASE.exists():
        print(f"Error: {SEMANTICS_BASE} not found", file=sys.stderr)
        sys.exit(1)

    source = SEMANTICS_BASE.read_text()

    # Parse all function arms
    s, e = find_function_range(source, "evalBinOp")
    binop_arms = parse_function_arms(source, "evalBinOp", s, e)

    s, e = find_function_range(source, "evalUnaryOp")
    unary_arms = parse_function_arms(source, "evalUnaryOp", s, e)

    s, e = find_function_range(source, "evalFunc")
    func_arms = parse_function_arms(source, "evalFunc", s, e)

    s, e = find_function_range(source, "Value.eq")
    value_eq_arms = parse_function_arms(source, "Value.eq", s, e)

    s, e = find_function_range(source, "Value.compare")
    value_compare_arms = parse_function_arms(source, "Value.compare", s, e)

    s, e = find_function_range(source, "Value.toBool")
    value_tobool_arms = parse_function_arms(source, "Value.toBool", s, e)

    # Build matrices
    matrices: list[CoverageMatrix] = []

    # Filter by --function and --op if provided
    filter_func = getattr(args, 'function', None)
    filter_op = getattr(args, 'op', None)

    if not filter_func or filter_func == "evalBinOp":
        for op in BINOP_OPS:
            if filter_op and filter_op != op:
                continue
            matrices.append(build_binop_matrix(source, op, binop_arms,
                                                value_eq_arms, value_compare_arms))

    if not filter_func or filter_func == "evalUnaryOp":
        for op in UNARYOP_OPS:
            if filter_op and filter_op != op:
                continue
            matrices.append(build_unaryop_matrix(source, op, unary_arms))

    if not filter_func or filter_func == "Value.eq":
        if not filter_op:
            matrices.append(build_value_func_matrix(source, "Value.eq", value_eq_arms))

    if not filter_func or filter_func == "Value.compare":
        if not filter_op:
            matrices.append(build_value_func_matrix(source, "Value.compare", value_compare_arms))

    if not filter_func or filter_func == "Value.toBool":
        if not filter_op:
            matrices.append(build_value_func_matrix(source, "Value.toBool", value_tobool_arms))

    if not filter_func or filter_func == "evalFunc":
        func_matrices = build_evalfunc_matrix(source, func_arms)
        if filter_op:
            func_matrices = [m for m in func_matrices if m.operator.upper() == filter_op.upper()]
        matrices.extend(func_matrices)

    # Test cross-reference
    if not getattr(args, 'no_tests', False):
        test_map = scan_tests()
        apply_test_coverage(matrices, test_map)

    # Classify gaps (filter to relevant functions/ops)
    gaps = classify_gaps(matrices)
    if filter_func:
        gaps = [g for g in gaps if g.function == filter_func or
                (filter_func == "evalFunc" and g.function == "evalFunc")]
    if filter_op:
        gaps = [g for g in gaps if g.op == filter_op or g.op == filter_op.upper()]

    # Output
    gaps_only = getattr(args, 'gaps_only', False)
    json_only = getattr(args, 'json', False)

    if json_only:
        report = generate_json(matrices, gaps)
        json_path = PROJECT_ROOT / "tools" / "definition_coverage_report.json"
        json_path.write_text(json.dumps(report, indent=2) + "\n")
        print(f"JSON report written to {json_path}")
        return

    if not gaps_only:
        print_console_summary(matrices, gaps)

        # Write markdown
        md = generate_markdown(matrices, gaps)
        md_path = PROJECT_ROOT / "docs" / "definition_coverage_matrix.md"
        md_path.parent.mkdir(parents=True, exist_ok=True)
        md_path.write_text(md + "\n")
        print(f"Markdown report written to {md_path}")

        # Write JSON
        report = generate_json(matrices, gaps)
        json_path = PROJECT_ROOT / "tools" / "definition_coverage_report.json"
        json_path.write_text(json.dumps(report, indent=2) + "\n")
        print(f"JSON report written to {json_path}")
    else:
        if not gaps:
            print("No potential gaps found.")
        else:
            print(f"Found {len(gaps)} potential gaps:")
            for g in sorted(gaps, key=lambda x: {"HIGH": 0, "MEDIUM": 1, "LOW": 2}[x.severity]):
                types = f"{g.left_type}x{g.right_type}" if g.left_type != "N/A" else g.right_type
                print(f"  [{g.severity:>6}] {g.function} {g.op} ({types}): {g.description}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Definition coverage matrix for sql_equiv evaluator functions"
    )
    parser.add_argument("--gaps-only", action="store_true",
                        help="Only show potential gaps")
    parser.add_argument("--function", type=str, default=None,
                        help="Filter to specific function (evalBinOp, evalUnaryOp, etc.)")
    parser.add_argument("--op", type=str, default=None,
                        help="Filter to specific operator (add, and, etc.)")
    parser.add_argument("--json", action="store_true",
                        help="Only output JSON report")
    parser.add_argument("--no-tests", action="store_true",
                        help="Skip test cross-reference scan")
    args = parser.parse_args()
    run(args)


if __name__ == "__main__":
    main()
