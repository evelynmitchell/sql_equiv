# Discovery: finding the rewriter, evaluator and value domain

Run this when `.claude/rewrite-audit.json` does not exist. Report what you
found, ask the user to confirm or correct it in one question, and propose the
config file. Write the file only if the user agrees.

## What to find

| Item | What it is | How to find it |
|---|---|---|
| **Rewriters** | Functions from an expression AST to an expression AST, or rule tables (pattern → replacement) | Search signatures and names (below); follow callers of the optimizer/simplifier entry point |
| **Evaluator** | The interpreter whose results the rewrites must preserve, and its dispatch functions for binary/unary operators and function calls | From a rewriter's AST type, find functions taking that type and returning a value or result type |
| **Value domain** | The runtime value type: its constructors, its NULL representation(s) and its error representation | The evaluator's return type, e.g. an enum or inductive `Value`, wrapped in `Option`/`Result`/exceptions for errors |
| **Relation** | What "the rewrite is correct" means, and what it quantifies over (rows, environments, databases, configuration) | Proof-assistant projects: the type or theorem the rewriter returns. Others: the docs and the tests' assertion |
| **Probe** | Existing property, fuzz or differential tests over the rewriter | Search tests for calls to the rewriter that compare evaluation before and after |

## Heuristics by language

### Lean 4
- Rewriters:
  - `def f : Expr → Expr`;
  - functions returning a subtype `{ e' : Expr // R e e' }`;
  - `simp`-style rule sets.

  `grep -rn "Expr → Expr\|{ e' : Expr //" --include=*.lean`.

  Drop false positives whose result is not an expression, e.g. a structural
  equality `Expr → Expr → Bool`.
- Decision procedures: functions that return a **proof-carrying result**
  rather than an expression, e.g. an inductive whose "equivalent" constructor
  holds a proof of the relation. They aren't found by the signature grep.
  Search for the relation's name in `def` result types and `inductive`
  constructors, and audit them like rewriters: which relation does the
  proof-carrying case conclude, and under which check?
- Evaluator: `def eval… : … → Expr → Option Value` (or `Except`). Its dispatch
  is usually `match op, l, r with` with a final catch-all `| _, _, _ => none`.
- Relation: the `R` in the subtype, or the conclusion of the correctness
  theorem (e.g. `theorem rewrite_equiv : e ≈ rewrite e`). Unfold its
  definition to see what it quantifies over.

### Python
- Rewriters:
  - `ast.NodeTransformer` subclasses;
  - functions taking and returning a node class;
  - `match` statements on node types;
  - dicts of pattern → replacement.
- Evaluator: `eval`/`interpret`/`execute` methods. Errors are exceptions or
  sentinel values; NULL is often `None`.

### TypeScript / JavaScript
- Rewriters: `(node: Expr) => Expr`, visitor objects, `switch (node.kind)`.
- Evaluator: `evaluate(node, ctx)`. Watch for `undefined` vs `null` vs thrown
  errors as three distinct "values".

### Rust
- Rewriters: `fn …(e: &Expr) -> Expr` or `Box<Expr>`, `match` arms.
- Evaluator: `fn eval(&self, …) -> Result<Value, Error>`. `Option<Value>`
  inside `Value` can mean NULL.

### Other languages
Ask the user to name the rewriter and evaluator entry points.

## Config file: `.claude/rewrite-audit.json`

```json
{
  "rewriters": [
    { "name": "simplify", "file": "src/simplify.lean", "proof": "simplify_equiv" }
  ],
  "evaluator": {
    "entry": "evalExpr",
    "dispatch": ["applyBinary", "applyUnary", "callFunction"],
    "file": "src/Semantics.lean"
  },
  "valueDomain": {
    "type": "Value",
    "file": "src/Ast.lean",
    "null": "Value.null",
    "error": "Option.none"
  },
  "relation": {
    "name": "Equiv",
    "quantifiesOver": ["row", "database"],
    "weakerVariantsToReject": []
  },
  "guards": [
    { "name": "isBoolGuard", "bridge": "isBoolGuard_sound" }
  ],
  "probe": {
    "command": "lake exe tests",
    "group": "Rewriter context sweep",
    "mutantSelfCheck": true
  },
  "trustGuard": "Test/TrustBase.lean",
  "projectSpecificChecks": []
}
```

Fields:
- **`proof`, `guards`, `trustGuard`:** optional. Use them for proof-assistant
  projects.
- **`relation.weakerVariantsToReject`:** names relations that look like the
  real one but quantify over less. Any proof concluding one of them is a
  finding.
- **`projectSpecificChecks`:** free-text checks the project wants added to
  every run. They're listed in the report.
