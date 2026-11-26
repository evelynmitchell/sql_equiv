# Upstream inventory: what of `SqlCore` could move to cslib-frontier

This is step 1 and 2 of #467 (phase 9.9): an inventory of the typed core's modules, what each
depends on, and a proposed order for offering them upstream. Opening the conversation is a human
gate (the user's); nothing here has been proposed upstream yet.

Compiled on 26 Nov 2026 against cslib-frontier `296c23d` (its `main` that day), read only.

## Where upstream stands

- **What it is.** cslib-frontier is a staging ground for CSLib (`leanprover/cslib`). Its SQL
  development is `CslibFrontier/Languages/SQL`, 14 modules, 4455 lines, 334 theorems. Every one
  is marked `-- upstream: candidate`: proposed for CSLib, not yet submitted.
- **Since our last re-diff** (`d619c680e`, 22 Nov 2026; `docs/TYPED_CORE_PLAN.md`): two
  proof-shortening waves touched the SQL files (#8628, #8629, 25 Nov), and it has
  `JoinSize.lean` (equijoin row counts as the streaming library's join size), which `SqlCore`
  does not have.
- **Pins.** Both are on Lean `v4.36.0-rc2`. Upstream's Mathlib is `bbff2954`; ours is still
  `69552756`, the commit we pinned to match the frontier earlier. A contribution is built
  against their pin, so our pin moves first.
- **How it takes contributions** (its `CONTRIBUTING.md` and `AGENTS.md`):
  - agree on a substantial development before implementing it, through an issue (its
    development template) or a pull request;
  - keep each pull request one reviewable change, with a checked client for a new API;
  - files mirror CSLib's paths and namespace (`Cslib.SQL`, not our `SqlCore`), and follow its
    template: Apache header, `module`, an `-- upstream:` marker, `public import` for the API;
  - reuse what CSLib and Mathlib already have before defining anything;
  - `Authors:` names the originator and the human whose agents implemented it, and ports keep
    their original authors. Our files already credit Evelyn Mitchell and Samuel Schlesinger, as
    upstream's do.

## What can move, and what cannot

- **`SqlCore` can.** It imports only Mathlib, Batteries and itself: no parser, no `SqlEquiv`.
- **`SqlBridge` cannot, as it is.** The elaborator and its correctness proofs are written over
  our parser's AST (`SqlEquiv`); the Spider harness and CLI are tools. A parser front end would be
  a separate proposal, if upstream wants one.
- **`SqlEquiv` stays here** (decision D7: the reference oracle).

## The main difficulty: our extensions change upstream's types

Most of our work is not new modules beside upstream's but wider versions of its central types,
so each step upstream extends a type and repairs every proof over it:

| Type | Upstream | `SqlCore` |
|---|---|---|
| `Query` | 6 constructors: table, select, project, join, unionAll, distinct | 18: also aggregate, orderBy, limit, intersect, difference, attach, one, outer, lateral, window, recurse, outerJoin |
| `Value` | int, text, bool | also decimal (exact) |
| `BinOp` | arith, cmp, and, or, concat | also like |
| `UnOp` | not, neg, isNull, isNotNull | also round, lower, upper, length, toDecimal |
| `EvalError` | typeMismatch, divisionByZero | also unsupported, cardinality, recursionLimit |
| evaluation | `Query.eval D` | `Query.evalIn D env`, an outer row threaded through for correlated subqueries (decision D6); `eval` is the closed case |

The evaluation change is the most invasive: it touches every evaluator clause and every law.

## Modules

Lines and theorem counts, ours against upstream's file of the same name.

| `SqlCore` module | Lines (ours / upstream) | Theorems (ours / upstream) | Relation to upstream |
|---|--:|--:|---|
| `Row`, `Schema`, `Column` | 78/78, 80/80, 175/175 | 3/3, 1/1, 9/9 | the same up to the namespace, the `-- upstream:` marker and the provenance docstring (upstream's says it adapts `sql_equiv`'s rows) |
| `Value` | 139 / 118 | 13 / 9 | extended: `decimal` |
| `Truth` | 198 / 271 | 42 / 43 | diverged: 145 differing lines and one more theorem upstream (last touched upstream 25 Nov); not yet traced |
| `Scalar` | 1080 / 792 | 84 / 70 | extended: decimal arithmetic, LIKE, scalar functions, new errors |
| `Expr`, `Typing` | 321/310, 523/323 | 27/25, 25/18 | extended with the new operators; typing and soundness |
| `Equiv` | 485 / 332 | 59 / 40 | extended: laws for the new operators |
| `Query` | 1660 / 515 | 82 / 32 | extended: 12 more constructors, `evalIn`, typing, soundness |
| `QueryEquiv`, `QueryLaws` | 525/369, 723/446 | 51/41, 45/28 | extended: congruence and laws for the new constructors |
| `Simplify` | 616 / 495 | 11 / 11 | extended: arms for every constructor |
| `Aggregate` | 367 / — | 9 / — | new: aggregate calls over a group, typing, soundness |
| `Stmt` | 135 / — | 3 / — | new: INSERT, UPDATE, DELETE (`exec_spec`) |
| `Canon` | 419 / — | 28 / — | new: canonical forms modulo AC, with certificates |
| `Check` | 653 / — | 7 / — | new: proof-carrying checkers `Expr/Query.checkEquiv` |
| `Except`, `Preconditions`, `Basic` | 259, 86, 28 | 32, 6, 1 | new: `Except` lemmas, decidable side conditions, notation |
| `Foundations/` (4 files) | 221 | 11 | new: `Option.Rel`, `List.dedup`, list product, `Fin` lemmas |
| — | — / 151 | — / 5 | upstream only: `JoinSize` |

## Proposed order

Each step is one upstream pull request (or a short series), useful on its own, smallest change
to upstream's types first. Each brings its typing, soundness, laws and simplifier arms, and
kernel-checked examples as the checked client.

0. **Sync first** (here, not upstream): move our Mathlib pin to upstream's; port its 25 Nov proof
   waves and decide whether to take `JoinSize`; re-diff. Then a contribution is a diff on their
   current files.
1. **Foundations**: `Option.Rel`, the `List.dedup` and list-product lemmas, `FinAddFlip`, the
   `Except` lemmas. Check Mathlib and CSLib for each first; what exists is dropped, the rest
   is small and self-contained. Possibly better aimed at Mathlib.
2. **Exact decimals**: `Value.decimal` and its arithmetic and comparison. One new constructor,
   scalar layer only.
3. **Scalar functions and LIKE**: the `UnOp` and `BinOp` additions.
4. **Aggregates and `GROUP BY`**: `Aggregate.lean` and `Query.aggregate`. The largest gain for
   SQL coverage.
5. **`ORDER BY` and `LIMIT`/`OFFSET`**: `Query.orderBy`, `Query.limit`.
6. **`INTERSECT` and `EXCEPT`**: two constructors with set laws.
7. **The decision procedures**: `Canon` and `Check` over whatever constructors are upstream by
   then (they can go earlier, over upstream's six).
8. **Subqueries**: `attach`, `one`, `outer`, `lateral` and the environment-threaded `evalIn`.
   The most invasive change, so it needs a design conversation first (decision D6 and the 9.4a
   spike on #462 have the alternatives and their costs).
9. **Outer joins, window functions, `WITH RECURSIVE`**: `outerJoin`, `window`, `recurse`.
10. **Statements**: `Stmt` (INSERT, UPDATE, DELETE).

## Questions for the conversation

- Does upstream want SQL beyond its current fragment in the frontier, or a smaller core plus
  extensions as separate modules?
- The error type: are `unsupported`, `cardinality` and `recursionLimit` acceptable in the core
  `EvalError`, or should extensions carry their own?
- Correlated subqueries: is threading an environment through `eval` acceptable (D6), or would
  they prefer another encoding?
- Namespace and paths: all moved code becomes `Cslib.SQL.*`; is a module per feature (as
  `Aggregate`) preferred over growing `Query.lean`?
- Is a parser front end (`SqlBridge`) wanted, or out of scope?
