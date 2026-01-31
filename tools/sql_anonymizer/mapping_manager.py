#!/usr/bin/env python3
"""
Mapping Manager - Create, encrypt, decrypt, and validate anonymization mappings.

Usage:
    python mapping_manager.py create -o mapping.json
    python mapping_manager.py encrypt mapping.json -o mapping.json.enc --password
    python mapping_manager.py decrypt mapping.json.enc -o mapping.json --password
    python mapping_manager.py validate mapping.json
    python mapping_manager.py merge mapping1.json mapping2.json -o combined.json
"""

import argparse
import base64
import hashlib
import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Optional

# Optional: cryptography for encryption
try:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
    from cryptography.hazmat.primitives import hashes
    HAS_CRYPTO = True
except ImportError:
    HAS_CRYPTO = False


# ============================================================================
# Encryption/Decryption Functions
# ============================================================================

def derive_key(password: str, salt: bytes) -> bytes:
    """Derive a 256-bit key from password using PBKDF2."""
    if not HAS_CRYPTO:
        raise RuntimeError("cryptography package required for encryption. "
                          "Install with: pip install cryptography")

    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,  # 256 bits
        salt=salt,
        iterations=480000,  # OWASP recommended minimum
    )
    return kdf.derive(password.encode())


def encrypt_data(data: bytes, password: str) -> bytes:
    """Encrypt data with AES-256-GCM using password-derived key.

    Format: salt (16 bytes) || nonce (12 bytes) || ciphertext || tag (16 bytes)
    """
    if not HAS_CRYPTO:
        raise RuntimeError("cryptography package required for encryption")

    salt = os.urandom(16)
    nonce = os.urandom(12)
    key = derive_key(password, salt)

    aesgcm = AESGCM(key)
    ciphertext = aesgcm.encrypt(nonce, data, None)

    return salt + nonce + ciphertext


def decrypt_data(encrypted: bytes, password: str) -> bytes:
    """Decrypt AES-256-GCM encrypted data."""
    if not HAS_CRYPTO:
        raise RuntimeError("cryptography package required for decryption")

    if len(encrypted) < 28:  # 16 salt + 12 nonce
        raise ValueError("Invalid encrypted data")

    salt = encrypted[:16]
    nonce = encrypted[16:28]
    ciphertext = encrypted[28:]

    key = derive_key(password, salt)
    aesgcm = AESGCM(key)

    try:
        return aesgcm.decrypt(nonce, ciphertext, None)
    except Exception as e:
        raise ValueError("Decryption failed - wrong password or corrupted data") from e


# ============================================================================
# Mapping Operations
# ============================================================================

def create_mapping(output_path: Path, password: Optional[str] = None):
    """Create a new empty mapping file."""
    mapping = {
        "version": "1.0",
        "created": datetime.now().isoformat(),
        "mappings": {
            "tables": {},
            "columns": {},
            "literals": {},
            "schemas": {},
        },
        "counters": {
            "tables": 0,
            "columns": 0,
            "literals": 0,
            "schemas": 0,
        }
    }

    data = json.dumps(mapping, indent=2)

    if password:
        encrypted = encrypt_data(data.encode(), password)
        output_path.write_bytes(encrypted)
    else:
        output_path.write_text(data)

    print(f"Created new mapping file: {output_path}")


def encrypt_mapping(input_path: Path, output_path: Path, password: str):
    """Encrypt an existing plaintext mapping file."""
    data = input_path.read_bytes()
    encrypted = encrypt_data(data, password)
    output_path.write_bytes(encrypted)
    print(f"Encrypted mapping written to: {output_path}")


def decrypt_mapping(input_path: Path, output_path: Path, password: str):
    """Decrypt an encrypted mapping file."""
    encrypted = input_path.read_bytes()
    data = decrypt_data(encrypted, password)
    output_path.write_bytes(data)
    print(f"Decrypted mapping written to: {output_path}")


def validate_mapping(mapping_path: Path, password: Optional[str] = None) -> bool:
    """Validate a mapping file for consistency and correctness.

    Checks:
    1. Valid JSON structure
    2. Required fields present
    3. No duplicate anonymized values (collision detection)
    4. Counters are consistent
    5. Bidirectional mapping is possible
    """
    print(f"Validating mapping: {mapping_path}")
    errors = []
    warnings = []

    # Load mapping
    try:
        if password:
            data = decrypt_data(mapping_path.read_bytes(), password)
            mapping = json.loads(data)
        else:
            mapping = json.loads(mapping_path.read_text())
    except json.JSONDecodeError as e:
        print(f"ERROR: Invalid JSON: {e}")
        return False
    except ValueError as e:
        print(f"ERROR: {e}")
        return False

    # Check version
    if "version" not in mapping:
        warnings.append("Missing 'version' field")

    # Check required fields
    if "mappings" not in mapping:
        errors.append("Missing 'mappings' field")
    else:
        mappings = mapping["mappings"]
        for field in ["tables", "columns", "literals", "schemas"]:
            if field not in mappings:
                errors.append(f"Missing 'mappings.{field}' field")

    if errors:
        for e in errors:
            print(f"  ERROR: {e}")
        return False

    # Check for collisions (duplicate anonymized values)
    def check_collisions(mapping_dict: dict, name: str):
        values = list(mapping_dict.values())
        duplicates = set(v for v in values if values.count(v) > 1)
        if duplicates:
            errors.append(f"Collision in {name}: {duplicates}")

    mappings = mapping["mappings"]
    check_collisions(mappings.get("tables", {}), "tables")
    check_collisions(mappings.get("columns", {}), "columns")
    check_collisions(mappings.get("literals", {}), "literals")
    check_collisions(mappings.get("schemas", {}), "schemas")

    # Check counters
    if "counters" in mapping:
        counters = mapping["counters"]
        for field in ["tables", "columns", "literals", "schemas"]:
            if field in counters and field in mappings:
                expected_min = len(mappings[field])
                if counters[field] < expected_min:
                    warnings.append(f"Counter for {field} ({counters[field]}) < "
                                   f"mapping count ({expected_min})")

    # Check for valid anonymized name formats
    for original, anon in mappings.get("tables", {}).items():
        if not anon.startswith("t_"):
            warnings.append(f"Non-standard table anonymization: {original} -> {anon}")

    for original, anon in mappings.get("columns", {}).items():
        if not anon.startswith("c_"):
            warnings.append(f"Non-standard column anonymization: {original} -> {anon}")

    # Print results
    if errors:
        for e in errors:
            print(f"  ERROR: {e}")
        print(f"Validation FAILED with {len(errors)} error(s)")
        return False

    if warnings:
        for w in warnings:
            print(f"  WARNING: {w}")

    # Print statistics
    print(f"  Tables: {len(mappings.get('tables', {}))}")
    print(f"  Columns: {len(mappings.get('columns', {}))}")
    print(f"  Literals: {len(mappings.get('literals', {}))}")
    print(f"  Schemas: {len(mappings.get('schemas', {}))}")

    print(f"Validation PASSED{' with warnings' if warnings else ''}")
    return True


def merge_mappings(inputs: list[Path], output_path: Path, password: Optional[str] = None):
    """Merge multiple mapping files into one.

    Later mappings take precedence for conflicts.
    """
    merged = {
        "version": "1.0",
        "created": datetime.now().isoformat(),
        "mappings": {
            "tables": {},
            "columns": {},
            "literals": {},
            "schemas": {},
        },
        "counters": {
            "tables": 0,
            "columns": 0,
            "literals": 0,
            "schemas": 0,
        }
    }

    for input_path in inputs:
        print(f"Merging: {input_path}")

        if password:
            data = decrypt_data(input_path.read_bytes(), password)
            mapping = json.loads(data)
        else:
            mapping = json.loads(input_path.read_text())

        mappings = mapping.get("mappings", {})
        for field in ["tables", "columns", "literals", "schemas"]:
            if field in mappings:
                merged["mappings"][field].update(mappings[field])

        # Update counters to max
        counters = mapping.get("counters", {})
        for field in ["tables", "columns", "literals", "schemas"]:
            if field in counters:
                merged["counters"][field] = max(
                    merged["counters"][field],
                    counters[field]
                )

    # Ensure counters are at least as large as mapping counts
    for field in ["tables", "columns", "literals", "schemas"]:
        merged["counters"][field] = max(
            merged["counters"][field],
            len(merged["mappings"][field])
        )

    data = json.dumps(merged, indent=2)
    if password:
        output_path.write_bytes(encrypt_data(data.encode(), password))
    else:
        output_path.write_text(data)

    print(f"Merged mapping written to: {output_path}")
    print(f"  Tables: {len(merged['mappings']['tables'])}")
    print(f"  Columns: {len(merged['mappings']['columns'])}")
    print(f"  Literals: {len(merged['mappings']['literals'])}")
    print(f"  Schemas: {len(merged['mappings']['schemas'])}")


def show_mapping(mapping_path: Path, password: Optional[str] = None):
    """Display mapping contents."""
    if password:
        data = decrypt_data(mapping_path.read_bytes(), password)
        mapping = json.loads(data)
    else:
        mapping = json.loads(mapping_path.read_text())

    print(f"Mapping file: {mapping_path}")
    print(f"Version: {mapping.get('version', 'unknown')}")
    print(f"Created: {mapping.get('created', 'unknown')}")
    print()

    mappings = mapping.get("mappings", {})

    if mappings.get("tables"):
        print("Tables:")
        for original, anon in sorted(mappings["tables"].items()):
            print(f"  {original} -> {anon}")
        print()

    if mappings.get("columns"):
        print("Columns:")
        for original, anon in sorted(mappings["columns"].items()):
            print(f"  {original} -> {anon}")
        print()

    if mappings.get("schemas"):
        print("Schemas:")
        for original, anon in sorted(mappings["schemas"].items()):
            print(f"  {original} -> {anon}")
        print()

    if mappings.get("literals"):
        print(f"Literals: {len(mappings['literals'])} entries")
        # Don't print all literals by default (could be many)
        for original, anon in list(mappings["literals"].items())[:10]:
            print(f"  {original} -> {anon}")
        if len(mappings["literals"]) > 10:
            print(f"  ... and {len(mappings['literals']) - 10} more")


def main():
    parser = argparse.ArgumentParser(
        description='Manage SQL anonymization mapping files'
    )
    subparsers = parser.add_subparsers(dest='command', required=True)

    # Create command
    create_parser = subparsers.add_parser('create', help='Create new mapping file')
    create_parser.add_argument('-o', '--output', type=Path, required=True,
                               help='Output mapping file')
    create_parser.add_argument('--password', action='store_true',
                               help='Encrypt with password')

    # Encrypt command
    encrypt_parser = subparsers.add_parser('encrypt', help='Encrypt mapping file')
    encrypt_parser.add_argument('input', type=Path, help='Input plaintext mapping')
    encrypt_parser.add_argument('-o', '--output', type=Path, required=True,
                                help='Output encrypted mapping')

    # Decrypt command
    decrypt_parser = subparsers.add_parser('decrypt', help='Decrypt mapping file')
    decrypt_parser.add_argument('input', type=Path, help='Input encrypted mapping')
    decrypt_parser.add_argument('-o', '--output', type=Path, required=True,
                                help='Output plaintext mapping')

    # Validate command
    validate_parser = subparsers.add_parser('validate', help='Validate mapping file')
    validate_parser.add_argument('input', type=Path, help='Mapping file to validate')
    validate_parser.add_argument('--password', action='store_true',
                                 help='Mapping is encrypted')

    # Merge command
    merge_parser = subparsers.add_parser('merge', help='Merge multiple mappings')
    merge_parser.add_argument('inputs', type=Path, nargs='+',
                              help='Input mapping files')
    merge_parser.add_argument('-o', '--output', type=Path, required=True,
                              help='Output merged mapping')
    merge_parser.add_argument('--password', action='store_true',
                              help='Mappings are encrypted')

    # Show command
    show_parser = subparsers.add_parser('show', help='Display mapping contents')
    show_parser.add_argument('input', type=Path, help='Mapping file')
    show_parser.add_argument('--password', action='store_true',
                             help='Mapping is encrypted')

    args = parser.parse_args()

    # Get password if needed
    password = None
    if getattr(args, 'password', False) or args.command in ('encrypt', 'decrypt'):
        import getpass
        password = getpass.getpass('Password: ')

    # Execute command
    if args.command == 'create':
        create_mapping(args.output, password)
    elif args.command == 'encrypt':
        encrypt_mapping(args.input, args.output, password)
    elif args.command == 'decrypt':
        decrypt_mapping(args.input, args.output, password)
    elif args.command == 'validate':
        success = validate_mapping(args.input, password)
        sys.exit(0 if success else 1)
    elif args.command == 'merge':
        merge_mappings(args.inputs, args.output, password)
    elif args.command == 'show':
        show_mapping(args.input, password)


if __name__ == '__main__':
    main()
