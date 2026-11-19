#!/usr/bin/env python3
"""Flag Lean theorems whose two sides are textually identical (#307).

A theorem `lhs = rhs` (or `↔`, `≃ₑ`, `≃ₛ`, `≃ᵩ`, `≃`) whose sides are the same text up to
whitespace proves nothing whatever its name promises: it is closed by `rfl` and its hypotheses
go unused. Reflexivity lemmas are the exception and are allowed by name (`*_refl`).

Usage: find_identical_sides.py DIR [DIR ...]
Exit status 1 if any theorem is flagged, 0 otherwise. A heuristic over source text: it splits
the file into declarations and compares the two sides of the statement's top-level relation, so
it can miss a vacuous theorem written differently, but it does not parse proofs.
"""
import re
import sys
from pathlib import Path

DECL = re.compile(
    r"\n(?=(?:private |protected )?(?:theorem|lemma|def|instance|abbrev|structure|inductive|"
    r"/--|/-!|--|section|end|namespace|open|variable|@\[))"
)
THM = re.compile(r"(?:private |protected )?(?:theorem|lemma)\s+(\S+)(.*?):=(.*)$", re.S)
REL = re.compile(r"\s(?:=|↔|≃ₑ|≃ₛ|≃ᵩ|≃)\s")
OPEN, CLOSE = "([{⟨", ")]}⟩"


def statement(sig: str) -> str | None:
    """The text after the last top-level `:` of a theorem signature."""
    depth, cut = 0, None
    for i, ch in enumerate(sig):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ":" and depth == 0:
            cut = i
    return None if cut is None else sig[cut + 1:]


def flagged(path: Path):
    for block in DECL.split(path.read_text(encoding="utf-8")):
        m = THM.match(block)
        if not m or m.group(1).endswith("_refl"):
            continue
        stmt = statement(m.group(2))
        if stmt is None:
            continue
        sides = REL.split(stmt)
        if len(sides) == 2 and " ".join(sides[0].split()) == " ".join(sides[1].split()):
            yield m.group(1)


def main() -> int:
    dirs = sys.argv[1:] or ["."]
    hits = [(f, name) for d in dirs for f in sorted(Path(d).rglob("*.lean"))
            if ".lake" not in f.parts for name in flagged(f)]
    for f, name in hits:
        print(f"{f}: theorem {name} has identical sides")
    if hits:
        print(f"{len(hits)} theorem(s) with identical sides: each proves nothing (see #307)")
        return 1
    print("OK: no theorem has identical sides")
    return 0


if __name__ == "__main__":
    sys.exit(main())
