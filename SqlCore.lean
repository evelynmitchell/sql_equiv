/-
  SqlCore: the typed semantic core of sql_equiv (#287).

  A new library beside `SqlEquiv`, built in phases (#289–#298). Phases 1–3
  (values and three-valued logic, rows and schemas, typed expressions) are
  re-derived here from cslib-frontier's SQL development; queries and laws
  (phases 4–5) will come from depending on cslib-frontier. Decisions:
  `docs/TYPED_CORE_DECISIONS.md`; plan: `docs/TYPED_CORE_PLAN.md`.

  Unlike `SqlEquiv`, this library may import Mathlib, and it uses Lean's
  module system as Mathlib and cslib-frontier do.
-/
module

public import SqlCore.Basic
public import SqlCore.Except
public import SqlCore.Value
public import SqlCore.Truth
public import SqlCore.Scalar
public import SqlCore.Row
public import SqlCore.Column
public import SqlCore.Schema
public import SqlCore.Expr
public import SqlCore.Typing
public import SqlCore.Aggregate
public import SqlCore.Preconditions
public import SqlCore.Query
public import SqlCore.Equiv
public import SqlCore.QueryEquiv
public import SqlCore.QueryLaws
public import SqlCore.Simplify
public import SqlCore.Canon
public import SqlCore.Check
