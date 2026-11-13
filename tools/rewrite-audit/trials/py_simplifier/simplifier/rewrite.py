"""Simplifier: rewrite rules applied bottom-up to a fixed point."""
from .ast import Lit, Var, BinOp, Not
from .evaluator import apply_binary, apply_unary
from .values import ERROR, is_bool, is_int


def is_definitely_int(e):
    """Conservative: true only if `e` always evaluates to an int."""
    if isinstance(e, Lit):
        return is_int(e.value)
    if isinstance(e, BinOp) and e.op in ("+", "*"):
        return is_definitely_int(e.left) and is_definitely_int(e.right)
    return False


def is_definitely_bool(e):
    """Conservative: true only if `e` always evaluates to a bool."""
    if isinstance(e, Lit):
        return is_bool(e.value)
    if isinstance(e, Not):
        return is_definitely_bool(e.operand)
    if isinstance(e, BinOp) and e.op in ("AND", "OR"):
        return is_definitely_bool(e.left) and is_definitely_bool(e.right)
    return False


def rewrite_once(e):
    """Apply the first matching rule at the root, or return `e` unchanged."""
    if isinstance(e, BinOp):
        l, r = e.left, e.right
        # constant folding, using the evaluator itself; never fold to an error
        if isinstance(l, Lit) and isinstance(r, Lit):
            v = apply_binary(e.op, l.value, r.value)
            if v is not ERROR:
                return Lit(v)
        # x * 1 -> x
        if e.op == "*" and r == Lit(1):
            return l
        # x + 0 -> x, for definitely-int x
        if e.op == "+" and r == Lit(0) and is_definitely_int(l):
            return l
        # x AND TRUE -> x, for definitely-bool x
        if e.op == "AND" and r == Lit(True) and is_definitely_bool(l):
            return l
        # x AND FALSE -> FALSE
        if e.op == "AND" and r == Lit(False):
            return Lit(False)
    if isinstance(e, Not):
        # constant folding
        if isinstance(e.operand, Lit):
            v = apply_unary("NOT", e.operand.value)
            if v is not ERROR:
                return Lit(v)
        # NOT NOT x -> x, for definitely-bool x
        if isinstance(e.operand, Not) and is_definitely_bool(e.operand.operand):
            return e.operand.operand
    return e


def simplify(e):
    """Rewrite children first, then the root, until nothing changes."""
    if isinstance(e, BinOp):
        e = BinOp(e.op, simplify(e.left), simplify(e.right))
    elif isinstance(e, Not):
        e = Not(simplify(e.operand))
    while True:
        e2 = rewrite_once(e)
        if e2 == e:
            return e
        e = simplify(e2) if e2 != e else e2
