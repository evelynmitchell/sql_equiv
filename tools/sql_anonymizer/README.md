# SQL Anonymizer/Deanonymizer Utilities

## Overview

Standalone utilities for anonymizing and deanonymizing SQL queries, enabling users to test sql_equiv without exposing confidential schema or data.

**Key Principle:** These tools are completely independent of sql_equiv and can be validated separately.

---

## Use Case

```
┌─────────────────┐     ┌──────────────┐     ┌─────────────────┐
│ Confidential    │     │ Anonymized   │     │ sql_equiv       │
│ SQL Query       │────▶│ SQL Query    │────▶│ Analysis        │
│                 │     │              │     │                 │
│ SELECT salary   │     │ SELECT c_7   │     │ Equivalence     │
│ FROM employees  │     │ FROM t_3     │     │ Check           │
│ WHERE dept='HR' │     │ WHERE c_2='x'│     │                 │
└─────────────────┘     └──────────────┘     └─────────────────┘
        │                      │                     │
        │                      │                     ▼
        │                      │              ┌─────────────────┐
        │                      │              │ Anonymized      │
        │                      │              │ Result          │
        │                      │              └────────┬────────┘
        │                      │                       │
        │               ┌──────┴───────┐               │
        │               │ Mapping File │◀──────────────┘
        │               │ (encrypted)  │
        │               └──────┬───────┘
        │                      │
        ▼                      ▼
┌─────────────────────────────────────────────────────────────┐
│                    Deanonymize                              │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
                  ┌─────────────────┐
                  │ Original Names  │
                  │ Restored        │
                  └─────────────────┘
```

---

## Components

### 1. `sql_anonymize.py`
Anonymizes SQL queries by replacing:
- Table names → `t_N`
- Column names → `c_N`
- String literals → `'s_N'`
- Numeric literals → randomized values (preserving type)
- Schema names → `schema_N`

### 2. `sql_deanonymize.py`
Reverses anonymization using the mapping file.

### 3. `mapping_manager.py`
Manages encrypted mapping files:
- Create, load, save mappings
- Password-protected encryption
- Mapping validation

---

## Mapping File Format

```json
{
  "version": "1.0",
  "created": "2024-01-31T12:00:00Z",
  "checksum": "sha256:...",
  "mappings": {
    "tables": {
      "employees": "t_1",
      "departments": "t_2",
      "salaries": "t_3"
    },
    "columns": {
      "employees.id": "c_1",
      "employees.name": "c_2",
      "employees.salary": "c_3",
      "departments.dept_name": "c_4"
    },
    "literals": {
      "'HR'": "'s_1'",
      "'Engineering'": "'s_2'",
      "50000": "12345"
    },
    "schemas": {
      "hr_schema": "schema_1",
      "finance_schema": "schema_2"
    }
  }
}
```

---

## Security Considerations

1. **Mapping file encryption**: AES-256 with password-derived key (PBKDF2)
2. **Deterministic mapping**: Same input always produces same output (for consistency)
3. **No information leakage**: Anonymized names reveal nothing about originals
4. **Secure deletion**: Option to securely delete mapping after use

---

## Command Line Interface

### Anonymize

```bash
# Basic usage
python sql_anonymize.py input.sql -o anonymized.sql -m mapping.json

# With encryption
python sql_anonymize.py input.sql -o anonymized.sql -m mapping.json.enc --password

# Batch mode
python sql_anonymize.py --batch input_dir/ -o output_dir/ -m mapping.json

# Preserve specific names (e.g., SQL keywords, functions)
python sql_anonymize.py input.sql -o output.sql -m mapping.json --preserve "COUNT,SUM,AVG"
```

### Deanonymize

```bash
# Basic usage
python sql_deanonymize.py anonymized.sql -o restored.sql -m mapping.json

# With encrypted mapping
python sql_deanonymize.py anonymized.sql -o restored.sql -m mapping.json.enc --password
```

### Mapping Management

```bash
# Create new mapping
python mapping_manager.py create -o mapping.json

# Encrypt existing mapping
python mapping_manager.py encrypt mapping.json -o mapping.json.enc --password

# Decrypt mapping
python mapping_manager.py decrypt mapping.json.enc -o mapping.json --password

# Validate mapping (check for collisions, completeness)
python mapping_manager.py validate mapping.json

# Merge mappings (for incremental anonymization)
python mapping_manager.py merge mapping1.json mapping2.json -o combined.json
```

---

## Validation Strategy

Users can validate the tools independently:

### Round-Trip Test
```bash
# 1. Anonymize
python sql_anonymize.py original.sql -o anon.sql -m map.json

# 2. Deanonymize
python sql_deanonymize.py anon.sql -o restored.sql -m map.json

# 3. Compare (should be identical)
diff original.sql restored.sql
```

### Determinism Test
```bash
# Run twice, should produce identical output
python sql_anonymize.py input.sql -o out1.sql -m map.json
python sql_anonymize.py input.sql -o out2.sql -m map.json
diff out1.sql out2.sql  # Should be empty
```

### Parsing Test
```bash
# Anonymized SQL should still be valid SQL
python -c "import sqlparse; sqlparse.parse(open('anon.sql').read())"
```

---

## Limitations

1. **Comments**: SQL comments are preserved but not anonymized (may leak info)
2. **Dynamic SQL**: String concatenation building SQL cannot be anonymized
3. **Stored procedures**: Only SQL statements, not procedural code
4. **Dialect-specific**: Some dialect-specific syntax may not parse correctly

---

## Dependencies

- Python 3.8+
- `sqlparse` - SQL parsing
- `cryptography` - Encryption (optional, for encrypted mappings)

---

## Installation

```bash
cd tools/sql_anonymizer
pip install -r requirements.txt

# Or standalone (no sql_equiv needed)
pip install sqlparse cryptography
```
