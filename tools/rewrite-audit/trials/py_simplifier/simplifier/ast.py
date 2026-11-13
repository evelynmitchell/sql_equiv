"""Expression AST."""
from dataclasses import dataclass
from typing import Union


@dataclass(frozen=True)
class Lit:
    value: object  # int, str, bool, or NULL


@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class BinOp:
    op: str  # '+', '*', 'AND', 'OR', '='
    left: "Expr"
    right: "Expr"


@dataclass(frozen=True)
class Not:
    operand: "Expr"


Expr = Union[Lit, Var, BinOp, Not]
