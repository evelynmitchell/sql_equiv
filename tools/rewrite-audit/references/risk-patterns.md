# Rewrite shapes that most often fail

Check every arm against these. Each lists why it fails and what makes it sound.

| Shape | Example | Why it breaks | What makes it sound |
|---|---|---|---|
| **Identity elimination** | `a AND TRUE → a`, `a + 0 → a`, `a * 1 → a`, `a \|\| '' → a` | Removing the operator lets `a`'s raw value through. For a wrong-kind `a`, the original hits a catch-all and errors, but the rewrite returns `a` | A guard that `a` has the operator's kind, plus bridge evidence |
| **Absorption** | `a AND FALSE → FALSE`, `a * 0 → 0` | The constant is right only if the evaluator really short-circuits. If `a` is an error or a wrong kind, the original may error while the rewrite does not | Check the evaluator's arms for error/NULL `a`. `a * 0` is often unsound for NULL (`NULL * 0 = NULL`) |
| **Double negation** | `NOT NOT a → a`, `-(-a) → a` | `NOT` on a non-boolean is an error, so `NOT NOT 42` errors while the rewrite returns `42` | A guard that `a` has the kind |
| **Self-comparison** | `a = a → TRUE`, `a - a → 0`, `x LIKE x → TRUE` | Wrong for NULL (`NULL = NULL` is NULL), for errors, and for NaN | Guard against NULL, error and NaN; or rewrite to `a IS NOT NULL` |
| **Reordering** | `a AND b → b AND a`, `a + b → b + a` | Sound for values; unsound if the language short-circuits errors (`FALSE AND error` vs `error AND FALSE`) or has side effects | Check the evaluator's three-valued or short-circuit arms in both orders |
| **Constant folding** | `1 + 2 → 3`, `'a' \|\| 'b' → 'ab'` | Folding with the host language's semantics instead of the evaluator's: overflow, rounding, integer division sign, string collation | Fold by calling the evaluator itself |
| **Pattern specialisation** | `x LIKE '%' → x IS NOT NULL` | The equivalence depends on the operand's kind (non-strings) or a mode (case-insensitive LIKE, collation) | A kind guard; match only the exact mode the proof covers |
| **Context-dependent rules** | Removing a subquery, `EXISTS(…) → TRUE`, hoisting expressions | The result depends on data (empty vs non-empty table), the row, or configuration. A proof over a restricted context (empty database, single row) does not transfer | The proof/test must quantify over every context the evaluator reads |
| **Division-related** | `a / a → 1`, `0 / a → 0` | Division by zero errors; integer vs float division; rounding direction for negatives | A guard that excludes zero, or no rule |

When an arm matches a shape, trace the "why it breaks" combination explicitly
in the report, even if it ends up `ok` or `GUARD`.
