#!/usr/bin/env python3
"""
SQL Deanonymizer - Restore original table names, column names, and literals.

This tool reverses the anonymization performed by sql_anonymize.py.

Usage:
    python sql_deanonymize.py anonymized.sql -o restored.sql -m mapping.json
    python sql_deanonymize.py anonymized.sql -o restored.sql -m mapping.json.enc --password
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Optional

from sql_anonymize import AnonymizationMapping


class SQLDeanonymizer:
    """Restores anonymized SQL queries to their original form."""

    def __init__(self, mapping: AnonymizationMapping):
        self.mapping = mapping
        # Build reverse lookup patterns
        self._build_patterns()

    def _build_patterns(self):
        """Build regex patterns for efficient replacement."""
        # Sort by length (longest first) to avoid partial matches
        # e.g., replace "t_10" before "t_1"

        def sorted_items(d):
            return sorted(d.items(), key=lambda x: -len(x[1]))

        self._table_patterns = sorted_items(self.mapping.tables)
        self._column_patterns = sorted_items(self.mapping.columns)
        self._literal_patterns = sorted_items(self.mapping.literals)
        self._schema_patterns = sorted_items(self.mapping.schemas)

    def deanonymize(self, sql: str) -> str:
        """Restore anonymized SQL to original form."""
        result = sql

        # Replace in order: schemas, tables, columns, literals
        # Use word boundaries to avoid partial replacements

        # Schemas (schema_N)
        for original, anon in self._schema_patterns:
            pattern = rf'\b{re.escape(anon)}\b'
            result = re.sub(pattern, original, result, flags=re.IGNORECASE)

        # Tables (t_N)
        for original, anon in self._table_patterns:
            pattern = rf'\b{re.escape(anon)}\b'
            result = re.sub(pattern, original, result, flags=re.IGNORECASE)

        # Columns (c_N) - need to handle qualified names
        for original, anon in self._column_patterns:
            pattern = rf'\b{re.escape(anon)}\b'
            # If original was qualified (table.column), extract just column name
            if '.' in original:
                _, col_name = original.rsplit('.', 1)
            else:
                col_name = original
            result = re.sub(pattern, col_name, result, flags=re.IGNORECASE)

        # Literals (strings and numbers)
        for original, anon in self._literal_patterns:
            # Escape special regex characters in the anonymized value
            if anon.startswith("'") or anon.startswith('"'):
                # String literal - exact match
                pattern = re.escape(anon)
            else:
                # Numeric literal - word boundary match
                pattern = rf'\b{re.escape(anon)}\b'
            result = re.sub(pattern, original, result)

        return result


def main():
    parser = argparse.ArgumentParser(
        description='Restore anonymized SQL queries to their original form'
    )
    parser.add_argument('input', type=Path, help='Input anonymized SQL file')
    parser.add_argument('-o', '--output', type=Path, required=True,
                        help='Output file for restored SQL')
    parser.add_argument('-m', '--mapping', type=Path, required=True,
                        help='Mapping file (created by sql_anonymize.py)')
    parser.add_argument('--password', action='store_true',
                        help='Decrypt password-protected mapping file')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Print statistics')

    args = parser.parse_args()

    # Get password if needed
    password = None
    if args.password:
        import getpass
        password = getpass.getpass('Mapping file password: ')

    # Load mapping
    if not args.mapping.exists():
        print(f"Error: Mapping file not found: {args.mapping}", file=sys.stderr)
        sys.exit(1)

    mapping = AnonymizationMapping.load(args.mapping, password)

    if args.verbose:
        print(f"Loaded mapping with {len(mapping.tables)} tables, "
              f"{len(mapping.columns)} columns, {len(mapping.literals)} literals")

    # Read anonymized SQL
    anon_sql = args.input.read_text()

    # Deanonymize
    deanonymizer = SQLDeanonymizer(mapping)
    restored_sql = deanonymizer.deanonymize(anon_sql)

    # Write output
    args.output.write_text(restored_sql)

    if args.verbose:
        print(f"Restored SQL written to {args.output}")


if __name__ == '__main__':
    main()
