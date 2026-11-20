/-
  Dialect-faithful printing (#267).

  `Stmt.toSqlIn d s` prints `s` as SQL for dialect `d` and checks that the text means the
  same thing there: re-parsed in `d`, it must give back every dialect choice recorded in
  `s`. Where SQL cannot spell a choice that `d` would read differently, it refuses with an
  error naming the choice, instead of printing SQL that silently changes meaning.

  Choices and how they print (docs/IMPLEMENTATION_DEFINED.md):
  - NULL position (row 1): `NULLS FIRST/LAST` wherever it differs from `d`'s rule. Always
    expressible.
  - LIKE letter case (row 8): a case-insensitive `likeCI` prints as `LIKE` for sqlite and
    as `LOWER(x) LIKE LOWER(p)` elsewhere. A case-sensitive `like` has no spelling for
    sqlite, whose `LIKE` folds ASCII case: refused.
  - MIN/MAX mode (rows 13, 14, T9) and SUM/AVG over booleans (row 18): no SQL spelling.
    Refused when `d` would record a different mode on re-parsing.

  The check compares the original and the re-parsed statement printed with annotations
  (`PrintCfg.annotate`), which spell these choices out as comments.
-/
import SqlEquiv.Parser
import SqlEquiv.Pretty

namespace SqlEquiv

/-- The dialect's name as the CLI and `Dialect.ofString?` spell it. -/
def Dialect.name : Dialect → String
  | .standard => "standard"
  | .sqlite => "sqlite"
  | .duckdb => "duckdb"
  | .postgres => "postgres"

/-- The `/*…*/` annotations of an annotated rendering, in order. -/
private def annotations (s : String) : List String :=
  ((s.splitOn "/*").drop 1).map fun part => (part.splitOn "*/").headD ""

/-- Explain the first choice that differs between the original and the re-parsed statement. -/
private def explainLoss (d : Dialect) (orig reparsed : String) : String :=
  let pairs := (annotations orig).zip (annotations reparsed)
  match pairs.find? (fun (a, b) => a != b) with
  | some ("cs", "ci") =>
    s!"a case-sensitive LIKE has no spelling in {d.name}, whose LIKE ignores ASCII letter case"
  | some (a, b) =>
    s!"{d.name} cannot express a dialect choice recorded in this statement " ++
    s!"(MIN/MAX mode or SUM/AVG over booleans): [{a}] would re-parse as [{b}]"
  | none =>
    s!"the SQL printed for {d.name} does not parse back to the same statement"

/-- SQL for dialect `d` that `d` reads with every dialect choice recorded in the statement,
    or an error naming a choice `d` cannot express. -/
def Stmt.toSqlIn (d : Dialect) (s : Stmt) : Except String String := do
  let cfg := PrintCfg.of d
  let sql := s.toSqlWith cfg
  let s' ← (parse sql (dialect := d)).mapError fun e =>
    s!"the SQL printed for {d.name} does not parse in it: {e}"
  let annotated := s.toSqlWith { cfg with annotate := true }
  let annotated' := s'.toSqlWith { cfg with annotate := true }
  if annotated == annotated' then pure sql
  else throw (explainLoss d annotated annotated')

end SqlEquiv
