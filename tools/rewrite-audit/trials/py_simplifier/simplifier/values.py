"""Runtime values.

A value is one of: a Python int (never bool), a str, a bool, NULL, or ERROR.
NULL is SQL-style "unknown"; ERROR is an evaluation error (type mismatch,
unbound variable). Note that bool is checked before int everywhere, because
in Python `isinstance(True, int)` is true.
"""


class _Sentinel:
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name


NULL = _Sentinel("NULL")
ERROR = _Sentinel("ERROR")


def is_bool(v):
    return isinstance(v, bool)


def is_int(v):
    return isinstance(v, int) and not isinstance(v, bool)


def is_str(v):
    return isinstance(v, str)
