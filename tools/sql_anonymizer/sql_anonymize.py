#!/usr/bin/env python3
"""
SQL Anonymizer - Replace table names, column names, and literals with anonymous identifiers.

This tool is completely independent of sql_equiv and can be validated separately.

Usage:
    python sql_anonymize.py input.sql -o output.sql -m mapping.json
    python sql_anonymize.py input.sql -o output.sql -m mapping.json.enc --password
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Dict, Optional, Set, Tuple
import hashlib

try:
    import sqlparse
    from sqlparse.sql import (
        Token, TokenList, Identifier, IdentifierList,
        Where, Comparison, Function, Parenthesis
    )
    from sqlparse.tokens import (
        Keyword, Name, String, Number, Punctuation,
        Wildcard, Operator, DML, DDL
    )
except ImportError:
    print("Error: sqlparse is required. Install with: pip install sqlparse")
    sys.exit(1)


@dataclass
class AnonymizationMapping:
    """Bidirectional mapping for anonymization/deanonymization."""

    tables: Dict[str, str] = field(default_factory=dict)
    columns: Dict[str, str] = field(default_factory=dict)
    literals: Dict[str, str] = field(default_factory=dict)
    schemas: Dict[str, str] = field(default_factory=dict)

    # Reverse mappings (auto-generated)
    _reverse_tables: Dict[str, str] = field(default_factory=dict)
    _reverse_columns: Dict[str, str] = field(default_factory=dict)
    _reverse_literals: Dict[str, str] = field(default_factory=dict)
    _reverse_schemas: Dict[str, str] = field(default_factory=dict)

    # Counters for generating anonymous names
    _table_counter: int = 0
    _column_counter: int = 0
    _literal_counter: int = 0
    _schema_counter: int = 0

    def _rebuild_reverse_mappings(self):
        """Rebuild reverse mappings from forward mappings."""
        self._reverse_tables = {v: k for k, v in self.tables.items()}
        self._reverse_columns = {v: k for k, v in self.columns.items()}
        self._reverse_literals = {v: k for k, v in self.literals.items()}
        self._reverse_schemas = {v: k for k, v in self.schemas.items()}

    def get_or_create_table(self, original: str) -> str:
        """Get anonymized table name, creating if needed."""
        key = original.lower()
        if key not in self.tables:
            self._table_counter += 1
            anon = f"t_{self._table_counter}"
            self.tables[key] = anon
            self._reverse_tables[anon] = key
        return self.tables[key]

    def get_or_create_column(self, original: str, table: Optional[str] = None) -> str:
        """Get anonymized column name, creating if needed."""
        # Use qualified name if table is provided
        if table:
            key = f"{table.lower()}.{original.lower()}"
        else:
            key = original.lower()

        if key not in self.columns:
            self._column_counter += 1
            anon = f"c_{self._column_counter}"
            self.columns[key] = anon
            self._reverse_columns[anon] = key
        return self.columns[key]

    def get_or_create_literal(self, original: str) -> str:
        """Get anonymized literal, creating if needed."""
        if original not in self.literals:
            self._literal_counter += 1
            # Preserve type: strings stay strings, numbers stay numbers
            if original.startswith("'") or original.startswith('"'):
                # String literal
                anon = f"'s_{self._literal_counter}'"
            elif '.' in original:
                # Float
                anon = str(float(hashlib.md5(original.encode()).hexdigest()[:8], 16) / 1000000)
            else:
                # Integer
                anon = str(int(hashlib.md5(original.encode()).hexdigest()[:8], 16) % 100000)
            self.literals[original] = anon
            self._reverse_literals[anon] = original
        return self.literals[original]

    def get_or_create_schema(self, original: str) -> str:
        """Get anonymized schema name, creating if needed."""
        key = original.lower()
        if key not in self.schemas:
            self._schema_counter += 1
            anon = f"schema_{self._schema_counter}"
            self.schemas[key] = anon
            self._reverse_schemas[anon] = key
        return self.schemas[key]

    def get_original_table(self, anon: str) -> Optional[str]:
        """Get original table name from anonymized."""
        return self._reverse_tables.get(anon.lower())

    def get_original_column(self, anon: str) -> Optional[str]:
        """Get original column name from anonymized."""
        return self._reverse_columns.get(anon.lower())

    def get_original_literal(self, anon: str) -> Optional[str]:
        """Get original literal from anonymized."""
        return self._reverse_literals.get(anon)

    def to_dict(self) -> dict:
        """Convert to dictionary for JSON serialization."""
        return {
            "version": "1.0",
            "created": datetime.now().isoformat(),
            "mappings": {
                "tables": self.tables,
                "columns": self.columns,
                "literals": self.literals,
                "schemas": self.schemas,
            },
            "counters": {
                "tables": self._table_counter,
                "columns": self._column_counter,
                "literals": self._literal_counter,
                "schemas": self._schema_counter,
            }
        }

    @classmethod
    def from_dict(cls, data: dict) -> 'AnonymizationMapping':
        """Create from dictionary (JSON deserialization)."""
        mapping = cls()
        mappings = data.get("mappings", {})
        mapping.tables = mappings.get("tables", {})
        mapping.columns = mappings.get("columns", {})
        mapping.literals = mappings.get("literals", {})
        mapping.schemas = mappings.get("schemas", {})

        counters = data.get("counters", {})
        mapping._table_counter = counters.get("tables", len(mapping.tables))
        mapping._column_counter = counters.get("columns", len(mapping.columns))
        mapping._literal_counter = counters.get("literals", len(mapping.literals))
        mapping._schema_counter = counters.get("schemas", len(mapping.schemas))

        mapping._rebuild_reverse_mappings()
        return mapping

    def save(self, path: Path, password: Optional[str] = None):
        """Save mapping to file, optionally encrypted."""
        data = json.dumps(self.to_dict(), indent=2)

        if password:
            from mapping_manager import encrypt_data
            data = encrypt_data(data.encode(), password)
            path.write_bytes(data)
        else:
            path.write_text(data)

    @classmethod
    def load(cls, path: Path, password: Optional[str] = None) -> 'AnonymizationMapping':
        """Load mapping from file, optionally decrypting."""
        if password:
            from mapping_manager import decrypt_data
            data = decrypt_data(path.read_bytes(), password)
            return cls.from_dict(json.loads(data))
        else:
            return cls.from_dict(json.loads(path.read_text()))


# SQL keywords that should NOT be anonymized
SQL_KEYWORDS = {
    'select', 'from', 'where', 'and', 'or', 'not', 'in', 'is', 'null',
    'join', 'inner', 'outer', 'left', 'right', 'full', 'cross', 'on',
    'group', 'by', 'having', 'order', 'asc', 'desc', 'limit', 'offset',
    'union', 'intersect', 'except', 'all', 'distinct', 'as',
    'insert', 'into', 'values', 'update', 'set', 'delete',
    'create', 'table', 'index', 'view', 'drop', 'alter', 'add',
    'primary', 'key', 'foreign', 'references', 'unique', 'check',
    'default', 'constraint', 'cascade', 'restrict',
    'case', 'when', 'then', 'else', 'end',
    'between', 'like', 'escape', 'exists',
    'true', 'false', 'unknown',
    'int', 'integer', 'varchar', 'char', 'text', 'boolean', 'bool',
    'float', 'double', 'decimal', 'numeric', 'date', 'time', 'timestamp',
    'with', 'recursive', 'over', 'partition', 'window', 'rows', 'range',
    'preceding', 'following', 'unbounded', 'current', 'row',
}

# SQL functions that should NOT be anonymized
SQL_FUNCTIONS = {
    'count', 'sum', 'avg', 'min', 'max',
    'coalesce', 'nullif', 'cast', 'convert',
    'concat', 'substring', 'substr', 'length', 'len', 'trim', 'ltrim', 'rtrim',
    'upper', 'lower', 'replace', 'reverse',
    'abs', 'ceil', 'ceiling', 'floor', 'round', 'mod', 'power', 'sqrt',
    'now', 'current_date', 'current_time', 'current_timestamp',
    'date', 'year', 'month', 'day', 'hour', 'minute', 'second',
    'row_number', 'rank', 'dense_rank', 'ntile', 'lag', 'lead',
    'first_value', 'last_value', 'nth_value',
    'string_agg', 'array_agg', 'json_agg',
    'greatest', 'least', 'if', 'ifnull', 'isnull', 'nvl',
}


class SQLAnonymizer:
    """Anonymizes SQL queries using token-based replacement."""

    def __init__(self, mapping: Optional[AnonymizationMapping] = None,
                 preserve: Optional[Set[str]] = None):
        self.mapping = mapping or AnonymizationMapping()
        self.preserve = preserve or set()
        self.preserve.update(SQL_KEYWORDS)
        self.preserve.update(SQL_FUNCTIONS)
        # Track context for qualified column names
        self._current_table: Optional[str] = None
        self._table_aliases: Dict[str, str] = {}  # alias -> original table

    def should_preserve(self, name: str) -> bool:
        """Check if a name should be preserved (not anonymized)."""
        return name.lower() in self.preserve

    def anonymize(self, sql: str) -> str:
        """Anonymize a SQL string."""
        # Parse the SQL
        parsed = sqlparse.parse(sql)

        results = []
        for statement in parsed:
            # First pass: collect table aliases
            self._collect_aliases(statement)
            # Second pass: anonymize
            anon_statement = self._anonymize_token_list(statement)
            results.append(str(anon_statement))

        return '\n'.join(results)

    def _collect_aliases(self, token_list):
        """Collect table aliases from FROM and JOIN clauses."""
        self._table_aliases = {}

        for token in token_list.flatten():
            # This is a simplified approach; real implementation would
            # need to properly parse FROM clauses
            pass

        # Use regex to find "table AS alias" or "table alias" patterns
        sql = str(token_list)
        # Pattern: FROM table_name [AS] alias or JOIN table_name [AS] alias
        pattern = r'(?:FROM|JOIN)\s+(\w+)(?:\s+(?:AS\s+)?(\w+))?'
        for match in re.finditer(pattern, sql, re.IGNORECASE):
            table = match.group(1)
            alias = match.group(2)
            if alias and alias.lower() not in SQL_KEYWORDS:
                self._table_aliases[alias.lower()] = table.lower()

    def _anonymize_token_list(self, token_list) -> TokenList:
        """Recursively anonymize a token list."""
        new_tokens = []

        i = 0
        tokens = list(token_list.tokens)

        while i < len(tokens):
            token = tokens[i]

            if isinstance(token, Identifier):
                new_tokens.append(self._anonymize_identifier(token))
            elif isinstance(token, IdentifierList):
                new_tokens.append(self._anonymize_identifier_list(token))
            elif isinstance(token, Function):
                new_tokens.append(self._anonymize_function(token))
            elif isinstance(token, Where):
                new_tokens.append(self._anonymize_where(token))
            elif isinstance(token, Comparison):
                new_tokens.append(self._anonymize_comparison(token))
            elif isinstance(token, Parenthesis):
                new_tokens.append(self._anonymize_parenthesis(token))
            elif isinstance(token, TokenList):
                new_tokens.append(self._anonymize_token_list(token))
            elif token.ttype in (String.Single, String.Double, String.Symbol):
                # String literal
                anon_value = self.mapping.get_or_create_literal(token.value)
                new_tokens.append(Token(token.ttype, anon_value))
            elif token.ttype in (Number.Integer, Number.Float):
                # Numeric literal
                anon_value = self.mapping.get_or_create_literal(token.value)
                new_tokens.append(Token(token.ttype, anon_value))
            elif token.ttype is Name or token.ttype is None:
                # Potential table or column name
                if token.value and not self.should_preserve(token.value):
                    # Check context to determine if table or column
                    if self._is_table_context(tokens, i):
                        anon_value = self.mapping.get_or_create_table(token.value)
                    else:
                        anon_value = self.mapping.get_or_create_column(token.value)
                    new_tokens.append(Token(token.ttype, anon_value))
                else:
                    new_tokens.append(token)
            else:
                new_tokens.append(token)

            i += 1

        # Create new token list with anonymized tokens
        result = TokenList(new_tokens)
        return result

    def _is_table_context(self, tokens, index: int) -> bool:
        """Determine if current position is in a table name context."""
        # Look backwards for FROM or JOIN
        for i in range(index - 1, -1, -1):
            token = tokens[i]
            if token.ttype is Keyword:
                upper = token.value.upper()
                if upper in ('FROM', 'JOIN', 'INTO', 'UPDATE', 'TABLE'):
                    return True
                if upper in ('SELECT', 'WHERE', 'AND', 'OR', 'ON', 'SET'):
                    return False
            elif token.ttype is Punctuation and token.value == ',':
                # Continue looking back
                continue
            elif token.ttype not in (None,) and token.value.strip():
                break
        return False

    def _anonymize_identifier(self, identifier: Identifier) -> Identifier:
        """Anonymize an identifier (table.column or column AS alias)."""
        parts = list(identifier.tokens)
        new_parts = []

        for i, part in enumerate(parts):
            if part.ttype is Name or (part.ttype is None and part.value not in ('.', ' ')):
                name = part.value
                if not self.should_preserve(name):
                    # Check if this is a qualified name (table.column)
                    if i > 0 and parts[i-1].value == '.':
                        # This is a column after table.
                        anon_value = self.mapping.get_or_create_column(name)
                    elif i < len(parts) - 1 and parts[i+1].value == '.':
                        # This is a table before .column
                        anon_value = self.mapping.get_or_create_table(name)
                    else:
                        # Context-dependent
                        anon_value = self.mapping.get_or_create_column(name)
                    new_parts.append(Token(part.ttype, anon_value))
                else:
                    new_parts.append(part)
            elif isinstance(part, TokenList):
                new_parts.append(self._anonymize_token_list(part))
            else:
                new_parts.append(part)

        return Identifier(new_parts)

    def _anonymize_identifier_list(self, id_list: IdentifierList) -> IdentifierList:
        """Anonymize a list of identifiers."""
        new_tokens = []
        for token in id_list.tokens:
            if isinstance(token, Identifier):
                new_tokens.append(self._anonymize_identifier(token))
            elif isinstance(token, TokenList):
                new_tokens.append(self._anonymize_token_list(token))
            else:
                new_tokens.append(token)
        return IdentifierList(new_tokens)

    def _anonymize_function(self, func: Function) -> Function:
        """Anonymize a function call (preserve function name, anonymize args)."""
        new_tokens = []
        for token in func.tokens:
            if isinstance(token, Parenthesis):
                new_tokens.append(self._anonymize_parenthesis(token))
            elif isinstance(token, TokenList):
                new_tokens.append(self._anonymize_token_list(token))
            else:
                # Keep function name as-is
                new_tokens.append(token)
        return Function(new_tokens)

    def _anonymize_where(self, where: Where) -> Where:
        """Anonymize a WHERE clause."""
        return Where(self._anonymize_token_list(where).tokens)

    def _anonymize_comparison(self, comparison: Comparison) -> Comparison:
        """Anonymize a comparison expression."""
        return Comparison(self._anonymize_token_list(comparison).tokens)

    def _anonymize_parenthesis(self, paren: Parenthesis) -> Parenthesis:
        """Anonymize content within parentheses."""
        return Parenthesis(self._anonymize_token_list(paren).tokens)


def main():
    parser = argparse.ArgumentParser(
        description='Anonymize SQL queries by replacing table/column names and literals'
    )
    parser.add_argument('input', type=Path, help='Input SQL file')
    parser.add_argument('-o', '--output', type=Path, required=True,
                        help='Output file for anonymized SQL')
    parser.add_argument('-m', '--mapping', type=Path, required=True,
                        help='Mapping file (will be created/updated)')
    parser.add_argument('--password', action='store_true',
                        help='Encrypt mapping file with password')
    parser.add_argument('--preserve', type=str, default='',
                        help='Comma-separated list of names to preserve')
    parser.add_argument('--verbose', '-v', action='store_true',
                        help='Print mapping statistics')

    args = parser.parse_args()

    # Get password if needed
    password = None
    if args.password:
        import getpass
        password = getpass.getpass('Mapping file password: ')

    # Load or create mapping
    if args.mapping.exists():
        mapping = AnonymizationMapping.load(args.mapping, password)
        if args.verbose:
            print(f"Loaded existing mapping with {len(mapping.tables)} tables, "
                  f"{len(mapping.columns)} columns, {len(mapping.literals)} literals")
    else:
        mapping = AnonymizationMapping()

    # Parse preserve list
    preserve = set()
    if args.preserve:
        preserve = {name.strip().lower() for name in args.preserve.split(',')}

    # Read input SQL
    sql = args.input.read_text()

    # Anonymize
    anonymizer = SQLAnonymizer(mapping, preserve)
    anonymized_sql = anonymizer.anonymize(sql)

    # Write output
    args.output.write_text(anonymized_sql)

    # Save mapping
    mapping.save(args.mapping, password)

    if args.verbose:
        print(f"Anonymized SQL written to {args.output}")
        print(f"Mapping saved to {args.mapping}")
        print(f"Tables: {len(mapping.tables)}, Columns: {len(mapping.columns)}, "
              f"Literals: {len(mapping.literals)}")


if __name__ == '__main__':
    main()
