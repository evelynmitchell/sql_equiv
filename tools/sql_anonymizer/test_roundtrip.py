#!/usr/bin/env python3
"""
Round-trip test for SQL anonymizer/deanonymizer.

Validates that: deanonymize(anonymize(sql)) == sql

Usage:
    python test_roundtrip.py
    python test_roundtrip.py --verbose
"""

import argparse
import tempfile
from pathlib import Path

from sql_anonymize import SQLAnonymizer, AnonymizationMapping
from sql_deanonymize import SQLDeanonymizer


# Test cases: (name, sql)
TEST_CASES = [
    (
        "simple_select",
        "SELECT id, name, salary FROM employees WHERE department = 'HR'"
    ),
    (
        "join_query",
        """SELECT e.name, d.dept_name, e.salary
           FROM employees e
           JOIN departments d ON e.dept_id = d.id
           WHERE e.salary > 50000"""
    ),
    (
        "aggregate_query",
        """SELECT department, COUNT(*) as emp_count, AVG(salary) as avg_salary
           FROM employees
           WHERE hire_date > '2020-01-01'
           GROUP BY department
           HAVING COUNT(*) > 5"""
    ),
    (
        "subquery",
        """SELECT * FROM employees
           WHERE salary > (SELECT AVG(salary) FROM employees WHERE department = 'Engineering')"""
    ),
    (
        "complex_query",
        """SELECT
             e.employee_id,
             e.first_name,
             e.last_name,
             d.department_name,
             l.city,
             j.job_title,
             e.salary
           FROM employees e
           INNER JOIN departments d ON e.department_id = d.department_id
           INNER JOIN locations l ON d.location_id = l.location_id
           INNER JOIN jobs j ON e.job_id = j.job_id
           WHERE e.salary BETWEEN 5000 AND 15000
             AND d.department_name IN ('Sales', 'Marketing', 'IT')
           ORDER BY e.salary DESC
           LIMIT 100"""
    ),
    (
        "union_query",
        """SELECT name, 'employee' as type FROM employees
           UNION ALL
           SELECT name, 'contractor' as type FROM contractors"""
    ),
    (
        "case_when",
        """SELECT name,
                  CASE
                    WHEN salary > 100000 THEN 'high'
                    WHEN salary > 50000 THEN 'medium'
                    ELSE 'low'
                  END as salary_band
           FROM employees"""
    ),
    (
        "window_function",
        """SELECT name, department, salary,
                  RANK() OVER (PARTITION BY department ORDER BY salary DESC) as dept_rank
           FROM employees"""
    ),
]


def normalize_whitespace(sql: str) -> str:
    """Normalize SQL whitespace for comparison."""
    import re
    # Replace multiple whitespace with single space
    sql = re.sub(r'\s+', ' ', sql)
    # Trim
    sql = sql.strip()
    return sql


def run_roundtrip_test(name: str, sql: str, verbose: bool = False) -> bool:
    """Run a single round-trip test."""
    # Create fresh mapping for each test
    mapping = AnonymizationMapping()

    # Anonymize
    anonymizer = SQLAnonymizer(mapping)
    anonymized = anonymizer.anonymize(sql)

    # Deanonymize
    deanonymizer = SQLDeanonymizer(mapping)
    restored = deanonymizer.deanonymize(anonymized)

    # Compare (normalized)
    original_norm = normalize_whitespace(sql)
    restored_norm = normalize_whitespace(restored)

    passed = original_norm.lower() == restored_norm.lower()

    if verbose or not passed:
        print(f"\n{'='*60}")
        print(f"Test: {name}")
        print(f"{'='*60}")
        print(f"\nOriginal:\n{sql}")
        print(f"\nAnonymized:\n{anonymized}")
        print(f"\nRestored:\n{restored}")
        print(f"\nMapping:")
        print(f"  Tables: {mapping.tables}")
        print(f"  Columns: {dict(list(mapping.columns.items())[:10])}...")
        print(f"  Literals: {dict(list(mapping.literals.items())[:5])}...")

    status = "PASS" if passed else "FAIL"
    print(f"[{status}] {name}")

    if not passed:
        print(f"  Original (normalized):  {original_norm[:100]}...")
        print(f"  Restored (normalized):  {restored_norm[:100]}...")

    return passed


def test_determinism(verbose: bool = False) -> bool:
    """Test that anonymization is deterministic."""
    sql = "SELECT id, name FROM employees WHERE dept = 'HR'"

    mapping1 = AnonymizationMapping()
    mapping2 = AnonymizationMapping()

    anonymizer1 = SQLAnonymizer(mapping1)
    anonymizer2 = SQLAnonymizer(mapping2)

    result1 = anonymizer1.anonymize(sql)
    result2 = anonymizer2.anonymize(sql)

    passed = result1 == result2

    if verbose:
        print(f"\nDeterminism test:")
        print(f"  Run 1: {result1}")
        print(f"  Run 2: {result2}")

    status = "PASS" if passed else "FAIL"
    print(f"[{status}] determinism")

    return passed


def test_incremental_mapping(verbose: bool = False) -> bool:
    """Test that mapping can be used incrementally across multiple queries."""
    queries = [
        "SELECT id, name FROM employees",
        "SELECT id, dept FROM departments",
        "SELECT e.name, d.dept FROM employees e JOIN departments d ON e.dept_id = d.id",
    ]

    # Use same mapping for all queries
    mapping = AnonymizationMapping()
    anonymizer = SQLAnonymizer(mapping)

    results = []
    for q in queries:
        results.append(anonymizer.anonymize(q))

    # Verify mapping grew
    expected_tables = 2  # employees, departments
    actual_tables = len(mapping.tables)

    passed = actual_tables == expected_tables

    if verbose:
        print(f"\nIncremental mapping test:")
        for i, (q, r) in enumerate(zip(queries, results)):
            print(f"  Query {i+1}: {q}")
            print(f"  Anon  {i+1}: {r}")
        print(f"  Final mapping tables: {mapping.tables}")

    status = "PASS" if passed else "FAIL"
    print(f"[{status}] incremental_mapping (expected {expected_tables} tables, got {actual_tables})")

    return passed


def test_mapping_persistence(verbose: bool = False) -> bool:
    """Test that mapping can be saved and loaded."""
    sql = "SELECT salary FROM employees WHERE name = 'John'"

    # Create and use mapping
    mapping1 = AnonymizationMapping()
    anonymizer = SQLAnonymizer(mapping1)
    anonymized = anonymizer.anonymize(sql)

    # Save mapping
    with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
        import json
        json.dump(mapping1.to_dict(), f)
        temp_path = Path(f.name)

    try:
        # Load mapping
        mapping2 = AnonymizationMapping.load(temp_path)

        # Verify mappings are equivalent
        passed = (mapping1.tables == mapping2.tables and
                  mapping1.columns == mapping2.columns and
                  mapping1.literals == mapping2.literals)

        if verbose:
            print(f"\nPersistence test:")
            print(f"  Original mapping: {mapping1.to_dict()}")
            print(f"  Loaded mapping: {mapping2.to_dict()}")

    finally:
        temp_path.unlink()

    status = "PASS" if passed else "FAIL"
    print(f"[{status}] mapping_persistence")

    return passed


def main():
    parser = argparse.ArgumentParser(description='Run round-trip tests')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Show detailed output')
    args = parser.parse_args()

    print("SQL Anonymizer Round-Trip Tests")
    print("="*60)

    passed = 0
    failed = 0

    # Run all round-trip tests
    for name, sql in TEST_CASES:
        if run_roundtrip_test(name, sql, args.verbose):
            passed += 1
        else:
            failed += 1

    # Run other tests
    if test_determinism(args.verbose):
        passed += 1
    else:
        failed += 1

    if test_incremental_mapping(args.verbose):
        passed += 1
    else:
        failed += 1

    if test_mapping_persistence(args.verbose):
        passed += 1
    else:
        failed += 1

    print()
    print("="*60)
    print(f"Results: {passed} passed, {failed} failed")
    print("="*60)

    return 0 if failed == 0 else 1


if __name__ == '__main__':
    exit(main())
