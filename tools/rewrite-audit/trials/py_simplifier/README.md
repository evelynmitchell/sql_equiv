# py_simplifier

A tiny expression language with an evaluator (`simplifier/evaluator.py`) and a
rule-based simplifier (`simplifier/rewrite.py`). The simplifier must preserve
`evaluate(expr, env)` for every expression and every variable binding.

```python
from simplifier.ast import Lit, Var, BinOp
from simplifier.rewrite import simplify
simplify(BinOp("+", Var("x"), Lit(0)))
```
