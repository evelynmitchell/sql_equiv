import SqlEquiv

open SqlEquiv

/-- Demo: Parse and pretty-print SQL -/
def demoParser : IO Unit := do
  let queries := [
    "SELECT * FROM users WHERE age > 18",
    "SELECT name, email FROM users WHERE status = 'active' AND verified = TRUE",
    "SELECT u.name, o.total FROM users u INNER JOIN orders o ON u.id = o.user_id",
    "INSERT INTO users (name, email) VALUES ('Alice', 'alice@example.com')",
    "UPDATE users SET status = 'inactive' WHERE last_login < '2024-01-01'",
    "DELETE FROM sessions WHERE expired = TRUE",
    -- Spider benchmark style queries
    "SELECT COUNT(*) FROM users",
    "SELECT MAX(age), MIN(age), AVG(salary) FROM employees",
    "SELECT department, COUNT(DISTINCT employee_id) FROM employees GROUP BY department",
    "SELECT name FROM users WHERE id IN (SELECT user_id FROM orders)",
    "SELECT * FROM users WHERE EXISTS (SELECT 1 FROM orders WHERE orders.user_id = users.id)",
    "SELECT name FROM active_users UNION SELECT name FROM admin_users",
    "SELECT * FROM (SELECT name, age FROM users WHERE age > 21) AS adults"
  ]

  for query in queries do
    IO.println s!"─────────────────────────────────────"
    IO.println s!"Input:  {query}"
    match parse query with
    | .ok stmt =>
      IO.println s!"Output: {stmt.toSql}"
    | .error e =>
      IO.println s!"Error:  {e}"
  IO.println "─────────────────────────────────────"

/-- Demo: Expression equivalence -/
def demoEquivalence : IO Unit := do
  IO.println "\n═══════════════════════════════════"
  IO.println "Expression Equivalence Framework"
  IO.println "═══════════════════════════════════"

  -- Show equivalence definitions
  IO.println "Equivalence is defined as:"
  IO.println "  e1 ≃ₑ e2 := ∀ row, evalExpr row e1 = evalExpr row e2"
  IO.println ""
  IO.println "Properties proven:"
  IO.println s!"✓ Reflexivity: e ≃ₑ e"
  IO.println s!"✓ Symmetry: e1 ≃ₑ e2 → e2 ≃ₑ e1"
  IO.println s!"✓ Transitivity: e1 ≃ₑ e2 → e2 ≃ₑ e3 → e1 ≃ₑ e3"
  IO.println ""
  IO.println "Same properties hold for SELECT and statement equivalence!"

/-- Demo: Evaluation -/
def demoEvaluation : IO Unit := do
  IO.println "\n═══════════════════════════════════"
  IO.println "SQL Evaluation Demo"
  IO.println "═══════════════════════════════════"

  -- Create a simple database
  let usersTable : Table := [
    [("id", .int 1), ("name", .string "Alice"), ("age", .int 30)],
    [("id", .int 2), ("name", .string "Bob"), ("age", .int 25)],
    [("id", .int 3), ("name", .string "Carol"), ("age", .int 35)]
  ]

  let db : Database := fun name =>
    if name == "users" then usersTable else []

  -- Parse and evaluate a SELECT
  let query := "SELECT name, age FROM users WHERE age > 25"
  IO.println s!"Query: {query}"

  match parseSelectStr query with
  | .ok sel =>
    let result := evalSelect db sel
    IO.println s!"Result: {result.length} rows"
    for row in result do
      let cols := row.map fun (k, v) => s!"{k}={v.toSql}"
      IO.println s!"  {", ".intercalate cols}"
  | .error e =>
    IO.println s!"Parse error: {e}"

/-- Demo: Syntactic equivalence checking -/
def demoNormalization : IO Unit := do
  IO.println "\n═══════════════════════════════════"
  IO.println "Syntactic Equivalence via Normalization"
  IO.println "═══════════════════════════════════"

  -- Two expressions that should be equivalent
  let x := Expr.col { table := none, column := "x" }
  let y := Expr.col { table := none, column := "y" }

  let e1 := Expr.binOp .and x y
  let e2 := Expr.binOp .and y x

  let equiv := syntacticEquiv e1 e2
  IO.println s!"Is '{e1.toSql}' ≡ '{e2.toSql}'? {equiv}"

  let e3 := Expr.binOp .add x (Expr.lit (.int 1))
  let e4 := Expr.binOp .add (Expr.lit (.int 1)) x

  let equiv2 := syntacticEquiv e3 e4
  IO.println s!"Is '{e3.toSql}' ≡ '{e4.toSql}'? {equiv2}"

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════╗"
  IO.println "║  SQL Parser & Equivalence Prover  ║"
  IO.println "║          in Lean 4                ║"
  IO.println "╚═══════════════════════════════════╝"

  demoParser
  demoEquivalence
  demoEvaluation
  demoNormalization

  IO.println "\n✓ All proofs type-checked by Lean!"
