# Value domains: building the enumeration table

The protocol enumerates every runtime result an operand can produce. Build
the table from the project's value type, not from memory.

## Steps

1. **Read the value type.** List its constructors: integer, decimal, float,
   string, boolean, date, … One row each.
2. **Find the NULL representation(s).** SQL-like evaluators often have more
   than one:
   - typed NULL vs untyped NULL;
   - `None` inside a value vs an absent value.

   Add one row per kind that can behave differently. For example, an arm may
   propagate a typed NULL but not an untyped one.
3. **Find the error representation.** Examples:
   - `Option.none` or `Except.error`;
   - an exception;
   - `undefined`;
   - a sentinel.

   Add one row for it. Errors are the most common source of mismatches, because
   catch-all arms map wrong-kind inputs to errors.
4. **Note special values within a kind** when an arm depends on them:
   - zero, for division;
   - empty string, for LIKE or concatenation;
   - `true`/`false` separately, for boolean identities;
   - NaN/±0 for floats.

## Template

| Result | Description |
|--------|-------------|
| `<int n>` | integer |
| `<string s>` | string |
| `<bool b>` | boolean (consider true and false separately for boolean identities) |
| `<decimal …>` | exact decimal, if present |
| `<null (typed)>` | typed NULL, if the domain distinguishes it |
| `<null (untyped)>` | untyped NULL |
| `<error>` | evaluation error (type mismatch, missing column, division by zero) |

For a binary rule, enumerate the cross product of both operands' rows. Prune
only combinations the evaluator provably treats identically, and say so in
the report.

If the value type gains a constructor, re-run the audit. Arms proven against
the old type keep their proofs only if the proof still checks.
