"""Evaluator: the semantics every rewrite must preserve."""
from .ast import Lit, Var, BinOp, Not
from .values import NULL, ERROR, is_bool, is_int, is_str


def apply_binary(op, a, b):
    if op == "AND":
        # FALSE wins over everything (including errors), then errors, then NULL
        if a is False or b is False:
            return False
        if a is ERROR or b is ERROR:
            return ERROR
        if not ((is_bool(a) or a is NULL) and (is_bool(b) or b is NULL)):
            return ERROR
        if a is NULL or b is NULL:
            return NULL
        return True
    if op == "OR":
        if a is True or b is True:
            return True
        if a is ERROR or b is ERROR:
            return ERROR
        if not ((is_bool(a) or a is NULL) and (is_bool(b) or b is NULL)):
            return ERROR
        if a is NULL or b is NULL:
            return NULL
        return False
    if a is ERROR or b is ERROR:
        return ERROR
    if a is NULL or b is NULL:
        return NULL
    if op == "+":
        if is_int(a) and is_int(b):
            return a + b
        if is_str(a) and is_str(b):
            return a + b
        return ERROR
    if op == "*":
        if is_int(a) and is_int(b):
            return a * b
        return ERROR
    if op == "=":
        if type(a) is type(b):
            return a == b
        return ERROR
    return ERROR


def apply_unary(op, a):
    if a is ERROR:
        return ERROR
    if a is NULL:
        return NULL
    if op == "NOT":
        return (not a) if is_bool(a) else ERROR
    return ERROR


def evaluate(expr, env):
    """Evaluate `expr` with variable bindings `env` (a dict)."""
    if isinstance(expr, Lit):
        return expr.value
    if isinstance(expr, Var):
        return env.get(expr.name, ERROR)
    if isinstance(expr, BinOp):
        return apply_binary(expr.op, evaluate(expr.left, env), evaluate(expr.right, env))
    if isinstance(expr, Not):
        return apply_unary("NOT", evaluate(expr.operand, env))
    return ERROR
