/-
  SQL Equivalence REPL

  Interactive command-line interface for the sql_equiv project.
  Supports parsing, evaluation, equivalence checking, and normalization.

  Since phase 9.8 (#466) `eval`, `equiv` and the batch mode run on the typed core
  (`SqlBridge.Cli`); `SqlEquiv`'s evaluator is the reference oracle (decision D7), shown only
  where the typed core does not elaborate a statement or disagrees with it.
-/
import SqlEquiv
import SqlBridge.Cli

open SqlEquiv

/-- Target dialect for parsing (`--dialect`, or the REPL's `dialect` command):
    which engine's implementation-defined behaviour queries are checked against.
    See docs/IMPLEMENTATION_DEFINED.md. -/
initialize dialectRef : IO.Ref Dialect ← IO.mkRef defaultDialect

/-- Parse with the current target dialect. -/
def parseD (sql : String) : IO (Except String Stmt) := do
  return parse sql (dialect := ← dialectRef.get)

def dialectName : Dialect → String
  | .standard => "standard"
  | .sqlite => "sqlite"
  | .duckdb => "duckdb"
  | .postgres => "postgres"

-- ============================================================================
-- ANSI Color Support
-- ============================================================================

namespace Color

def reset : String := "\x1b[0m"
def bold : String := "\x1b[1m"
def dim : String := "\x1b[2m"

def red : String := "\x1b[31m"
def green : String := "\x1b[32m"
def yellow : String := "\x1b[33m"
def blue : String := "\x1b[34m"
def magenta : String := "\x1b[35m"
def cyan : String := "\x1b[36m"
def white : String := "\x1b[37m"

def bgBlue : String := "\x1b[44m"
def bgGreen : String := "\x1b[42m"
def bgRed : String := "\x1b[41m"

def colorize (color : String) (s : String) : String :=
  color ++ s ++ reset

def error (s : String) : String := colorize red s
def success (s : String) : String := colorize green s
def info (s : String) : String := colorize cyan s
def warning (s : String) : String := colorize yellow s
def keyword (s : String) : String := colorize (bold ++ blue) s
def highlight (s : String) : String := colorize (bold ++ magenta) s

-- Additional helper functions for styled text
def dimText (s : String) : String := colorize dim s
def boldText (s : String) : String := colorize bold s
def cyanText (s : String) : String := colorize cyan s
def boldCyan (s : String) : String := colorize (bold ++ cyan) s

end Color

-- ============================================================================
-- Sample Database
-- ============================================================================

/-- Sample users table -/
def sampleUsers : Table := [
  [("id", .int 1), ("name", .string "Alice"), ("age", .int 30), ("department", .string "Engineering")],
  [("id", .int 2), ("name", .string "Bob"), ("age", .int 25), ("department", .string "Marketing")],
  [("id", .int 3), ("name", .string "Carol"), ("age", .int 35), ("department", .string "Engineering")],
  [("id", .int 4), ("name", .string "David"), ("age", .int 28), ("department", .string "Sales")],
  [("id", .int 5), ("name", .string "Eve"), ("age", .int 22), ("department", .string "Marketing")]
]

/-- Sample orders table -/
def sampleOrders : Table := [
  [("id", .int 101), ("user_id", .int 1), ("amount", .int 150), ("product", .string "Laptop")],
  [("id", .int 102), ("user_id", .int 1), ("amount", .int 50), ("product", .string "Mouse")],
  [("id", .int 103), ("user_id", .int 2), ("amount", .int 200), ("product", .string "Monitor")],
  [("id", .int 104), ("user_id", .int 3), ("amount", .int 75), ("product", .string "Keyboard")],
  [("id", .int 105), ("user_id", .int 4), ("amount", .int 300), ("product", .string "Laptop")],
  [("id", .int 106), ("user_id", .int 1), ("amount", .int 25), ("product", .string "Cable")]
]

/-- Sample products table -/
def sampleProducts : Table := [
  [("id", .int 1), ("name", .string "Laptop"), ("price", .int 999)],
  [("id", .int 2), ("name", .string "Monitor"), ("price", .int 299)],
  [("id", .int 3), ("name", .string "Keyboard"), ("price", .int 79)],
  [("id", .int 4), ("name", .string "Mouse"), ("price", .int 49)],
  [("id", .int 5), ("name", .string "Cable"), ("price", .int 15)]
]

/-- Sample database combining all tables -/
def sampleDatabase : Database := fun name =>
  match name.toLower with
  | "users" => sampleUsers
  | "orders" => sampleOrders
  | "products" => sampleProducts
  | _ => []

-- ============================================================================
-- Table Formatting
-- ============================================================================

/-- Get maximum width for each column in a table result -/
def getColumnWidths (headers : List String) (rows : List (List String)) : List Nat :=
  let headerWidths := headers.map String.length
  let rowWidths := rows.map (fun row => row.map String.length)
  let allWidths := headerWidths :: rowWidths
  let numCols := headers.length
  List.range numCols |>.map fun i =>
    (allWidths.filterMap fun row => row[i]?).foldl max 0

/-- Pad string to given width -/
def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- Format a row with separators -/
def formatRow (cells : List String) (widths : List Nat) : String :=
  let paddedCells := cells.zipWith padRight widths
  "| " ++ " | ".intercalate paddedCells ++ " |"

/-- Create a separator line -/
def separatorLine (widths : List Nat) : String :=
  let dashes := widths.map fun w => String.ofList (List.replicate (w + 2) '-')
  "+" ++ "+".intercalate dashes ++ "+"

/-- Convert Value to display string -/
def valueToDisplay : Value -> String
  | .int n => toString n
  | .decimal u s => Value.toSql (.decimal u s)
  | .string s => s
  | .bool b => if b then "true" else "false"
  | .null _ => "NULL"

/-- Pretty print a table result -/
def prettyTable (result : Table) : String :=
  if result.isEmpty then
    Color.dimText "  (empty result set)"
  else
    -- Extract column names from first row
    match result.head? with
    | none => Color.dimText "  (empty result set)"
    | some firstRow =>
      let headers := firstRow.map Prod.fst
      let rows := result.map fun row => row.map (valueToDisplay ·.snd)
      let widths := getColumnWidths headers rows

      let headerLine := formatRow (headers.map Color.boldText) widths
      let sep := separatorLine widths
      let dataLines := rows.map fun row => formatRow row widths

      "\n" ++ sep ++ "\n" ++ headerLine ++ "\n" ++ sep ++ "\n" ++
      "\n".intercalate dataLines ++ "\n" ++ sep

/-- The sample tables' typed declarations (the typed core's schema of `sampleDatabase`). -/
def sampleDecls : List SqlBridge.Cli.TableDecl := [
  ("users", [("id", .int), ("name", .text), ("age", .int), ("department", .text)]),
  ("orders", [("id", .int), ("user_id", .int), ("amount", .int), ("product", .text)]),
  ("products", [("id", .int), ("name", .text), ("price", .int)])]

/-- A typed-core result as a table. -/
def prettyResult (r : SqlBridge.Cli.Result) : String :=
  if r.rows.isEmpty then Color.dimText "  (empty result set)"
  else
    let widths := getColumnWidths r.columns r.rows
    let sep := separatorLine widths
    "\n" ++ sep ++ "\n" ++ formatRow (r.columns.map Color.boldText) widths ++ "\n" ++ sep ++ "\n" ++
      "\n".intercalate (r.rows.map fun row => formatRow row widths) ++ "\n" ++ sep

/-- The reference oracle's rows, rendered as the typed core renders them (for comparison). -/
def oracleRows (t : Table) : List (List String) :=
  t.map fun row => row.map fun (_, v) => SqlBridge.SpiderEval.renderDatum (SqlBridge.Cli.datumOf v)

/-- Rows as a bag (sorted), for comparing the typed core with the oracle. -/
def bagOfRows (rows : List (List String)) : List String :=
  (rows.map fun r => "|".intercalate r).mergeSort (· ≤ ·)

/-- Run a statement on the typed core, and on the reference oracle where the typed core does not
elaborate it or disagrees with it. `brief` limits the printed rows (batch mode). -/
def runStatement (stmt : Stmt) (brief : Bool) : IO Unit := do
  let oracle := evalStmt sampleDatabase stmt
  let oracleTable : Option Table := match stmt with
    | .query _ => oracle.2
    | .insert i => some (oracle.1 i.table)
    | .update u => some (oracle.1 u.table)
    | .delete d => some (oracle.1 d.table)
  match SqlBridge.Cli.typedRun sampleDecls sampleDatabase (← dialectRef.get) stmt with
  | .ok r =>
    IO.println s!"\n{Color.success "Result"} ({r.rows.length} rows, typed core):"
    if !brief || r.rows.length ≤ 5 then IO.println (prettyResult r)
    if let some t := oracleTable then
      if bagOfRows (oracleRows t) != bagOfRows r.rows then
        IO.println s!"\n{Color.warning "The reference oracle (SqlEquiv) disagrees"} ({t.length} rows):"
        IO.println (prettyTable t)
  | .error e =>
    IO.println s!"\n{Color.warning "Typed core"}: {e}"
    match oracleTable with
    | some t =>
      IO.println s!"{Color.dimText "Reference oracle (SqlEquiv)"} ({t.length} rows):"
      if !brief || t.length ≤ 5 then IO.println (prettyTable t)
    | none => pure ()

-- ============================================================================
-- AST Pretty Printing (for debugging)
-- ============================================================================

/-- Pretty print AST in a more readable format -/
partial def prettyAst (stmt : Stmt) : String :=
  match stmt with
  | .query q => prettyQuery q
  | .insert i => s!"INSERT INTO {i.table} ..."
  | .update u => s!"UPDATE {u.table} ..."
  | .delete d => s!"DELETE FROM {d.table} ..."
where
  prettyQuery : Query -> String
  | .simple sel => prettySelect sel
  | .compound l op r => s!"{prettyQuery l} {op.toSql} {prettyQuery r}"
  | .withCTE ctes q => s!"WITH {ctes.length} CTEs: {prettyQuery q}"
  | .ordered q ob _ _ => s!"{prettyQuery q} ORDER BY/LIMIT ({ob.length} keys)"

  prettySelect (sel : SelectStmt) : String :=
    let parts := [
      Color.keyword "SELECT" ++
        (if sel.distinct then " " ++ Color.keyword "DISTINCT" else ""),
      s!"  items: [{sel.items.length} items]",
      match sel.fromClause with
      | some f => s!"  {Color.keyword "FROM"}: {prettyFrom f}"
      | none => "",
      match sel.whereClause with
      | some w => s!"  {Color.keyword "WHERE"}: {w.toSql}"
      | none => "",
      if sel.groupBy.isEmpty then ""
      else s!"  {Color.keyword "GROUP BY"}: {sel.groupBy.length} expressions",
      match sel.having with
      | some h => s!"  {Color.keyword "HAVING"}: {h.toSql}"
      | none => "",
      if sel.orderBy.isEmpty then ""
      else s!"  {Color.keyword "ORDER BY"}: {sel.orderBy.length} items",
      match sel.limitVal with
      | some n => s!"  {Color.keyword "LIMIT"}: {n}"
      | none => "",
      match sel.offsetVal with
      | some n => s!"  {Color.keyword "OFFSET"}: {n}"
      | none => ""
    ]
    "\n".intercalate (parts.filter (· != ""))

  prettyFrom : FromClause -> String
  | .table t => t.name ++ (match t.alias with | some a => s!" AS {a}" | none => "")
  | .subquery _ al => s!"(subquery) AS {al}"
  | .join l jt r _ => s!"{prettyFrom l} {jt.toSql} {prettyFrom r}"

-- ============================================================================
-- Expression Normalization (for equivalence)
-- ============================================================================

/-- Normalize a SELECT statement for comparison -/
partial def normalizeSelect (sel : SelectStmt) : SelectStmt :=
  .mk sel.distinct
      sel.items
      sel.fromClause
      (sel.whereClause.map normalizeExpr)
      (sel.groupBy.map normalizeExpr)
      (sel.having.map normalizeExpr)
      sel.orderBy
      sel.limitVal
      sel.offsetVal

/-- Check if two SELECT statements are syntactically equivalent after normalization -/
def selectSyntacticEquiv (s1 s2 : SelectStmt) : Bool :=
  let n1 := normalizeSelect s1
  let n2 := normalizeSelect s2
  n1 == n2

/-- Detailed equivalence check result -/
inductive EquivResult
  | equivalent : String -> EquivResult
  | notEquivalent : String -> EquivResult
  | maybeEquivalent : String -> EquivResult
  | parseError : String -> EquivResult

def EquivResult.toString : EquivResult -> String
  | .equivalent reason => Color.success "Equivalent" ++ ": " ++ reason
  | .notEquivalent reason => Color.error "Not equivalent" ++ ": " ++ reason
  | .maybeEquivalent reason => Color.warning "May be equivalent" ++ ": " ++ reason
  | .parseError err => Color.error "Parse error" ++ ": " ++ err

-- ============================================================================
-- Commands Implementation
-- ============================================================================

/-- Parse SQL and show AST -/
def cmdParse (sql : String) : IO Unit := do
  IO.println s!"\n{Color.info "Parsing"}: {sql}"
  match ← parseD sql with
  | .ok stmt =>
    IO.println s!"\n{Color.success "AST"}:"
    IO.println (prettyAst stmt)
    IO.println s!"\n{Color.info "Reconstructed SQL"}:"
    IO.println s!"  {stmt.toSql}"
  | .error e =>
    IO.println s!"\n{Color.error "Error"}: {e}"

/-- Evaluate SQL against sample database -/
def cmdEval (sql : String) : IO Unit := do
  IO.println s!"\n{Color.info "Evaluating"}: {sql}"
  match ← parseD sql with
  | .ok stmt => runStatement stmt false
  | .error e =>
    IO.println s!"\n{Color.error "Parse error"}: {e}"

/-- Check equivalence of two queries -/
def cmdEquiv (input : String) : IO Unit := do
  -- Split by | to get two queries
  let parts := input.splitOn "|"
  if parts.length != 2 then
    IO.println s!"\n{Color.error "Error"}: Expected two queries separated by '|'"
    IO.println "  Usage: equiv SELECT ... | SELECT ..."
    return

  let sql1 := parts[0]!.trimAscii.toString
  let sql2 := parts[1]!.trimAscii.toString

  IO.println s!"\n{Color.info "Query 1"}: {sql1}"
  IO.println s!"{Color.info "Query 2"}: {sql2}"
  IO.println ""

  match ← parseD sql1, ← parseD sql2 with
  | .ok stmt1, .ok stmt2 =>
    -- the typed core first (#466): a proof from `Query.checkEquiv`, or the sample database
    let typed := SqlBridge.Cli.typedEquiv sampleDecls sampleDatabase (← dialectRef.get) stmt1 stmt2
    let result : EquivResult := match typed with
      | .proved => .equivalent "proved by the typed core's checker (Query.checkEquiv) on every conforming database"
      | .sameOnSample => .maybeEquivalent "not proved; same rows on the sample database (typed core)"
      | .bothFail why => .maybeEquivalent s!"not proved; {why} on the sample database (typed core)"
      | .differOnSample why => .notEquivalent s!"{why} (typed core)"
      | .notElaborated why =>
      -- outside the typed core: the reference oracle's syntactic checks (SqlEquiv)
      let _ := why
      if stmt1 == stmt2 then
        .equivalent "Queries are syntactically identical"
      else
        match stmt1, stmt2 with
        | .query (.simple sel1), .query (.simple sel2) =>
          -- Check normalized equivalence
          if selectSyntacticEquiv sel1 sel2 then
            .equivalent "Queries are equivalent after normalization"
          else
            -- Check if they differ only in column order
            let items1 := sel1.items
            let items2 := sel2.items
            if items1.length == items2.length &&
               items1.all (fun i => items2.contains i) then
              .maybeEquivalent "Column order differs (semantically may be equivalent)"
            else if sel1.fromClause == sel2.fromClause &&
                    sel1.whereClause == sel2.whereClause then
              .maybeEquivalent "Same FROM and WHERE, but different SELECT items"
            else
              -- Evaluate both on sample database to check
              let r1 := evalSelect sampleDatabase sel1
              let r2 := evalSelect sampleDatabase sel2
              if r1 == r2 then
                .maybeEquivalent "Results match on sample database (reference oracle; may not be universally equivalent)"
              else
                .notEquivalent "Different results on sample database (reference oracle)"
        | _, _ =>
          .notEquivalent "Different statement types or complex queries"
    if let .notElaborated why := typed then
      IO.println s!"  {Color.dimText s!"Typed core: does not elaborate ({why}); the reference oracle (SqlEquiv) decides"}"

    IO.println s!"  {result.toString}"

    -- Show normalized forms
    match stmt1, stmt2 with
    | .query (.simple sel1), .query (.simple sel2) =>
      let norm1 := normalizeSelect sel1
      let norm2 := normalizeSelect sel2
      IO.println s!"\n{Color.dimText "Normalized forms:"}"
      IO.println s!"  Q1: {norm1.toSql}"
      IO.println s!"  Q2: {norm2.toSql}"
    | _, _ => pure ()

  | .error e1, .error e2 =>
    IO.println s!"{Color.error "Parse errors"}:"
    IO.println s!"  Query 1: {e1}"
    IO.println s!"  Query 2: {e2}"
  | .error e, .ok _ =>
    IO.println s!"{Color.error "Parse error in Query 1"}: {e}"
  | .ok _, .error e =>
    IO.println s!"{Color.error "Parse error in Query 2"}: {e}"

/-- Show normalized form -/
def cmdNormalize (sql : String) : IO Unit := do
  IO.println s!"\n{Color.info "Normalizing"}: {sql}"
  match ← parseD sql with
  | .ok stmt =>
    match stmt with
    | .query (.simple sel) =>
      let normalized := normalizeSelect sel
      IO.println s!"\n{Color.success "Original"}:"
      IO.println s!"  {sel.toSql}"
      IO.println s!"\n{Color.success "Normalized"} {Color.dimText "(reference oracle: SqlEquiv's normalizeExpr, decision D3)"}:"
      IO.println s!"  {normalized.toSql}"

      -- Show WHERE clause normalization details
      match sel.whereClause with
      | some expr =>
        let normExpr := normalizeExpr expr
        IO.println s!"\n{Color.dimText "WHERE clause details:"}"
        IO.println s!"  Original:   {expr.toSql}"
        IO.println s!"  Normalized: {normExpr.toSql}"
      | none => pure ()
    | _ =>
      IO.println s!"\n{Color.warning "Note"}: Normalization is only detailed for simple SELECT queries"
      IO.println s!"  {stmt.toSql}"
  | .error e =>
    IO.println s!"\n{Color.error "Parse error"}: {e}"

/-- Show help -/
def cmdHelp : IO Unit := do
  IO.println s!"\n{Color.boldCyan "SQL Equivalence REPL - Available Commands"}{Color.reset}\n"
  IO.println s!"  {Color.keyword "parse"} <sql>        Parse SQL and show AST"
  IO.println s!"  {Color.keyword "eval"} <sql>         Evaluate on the sample database (typed core)"
  IO.println s!"  {Color.keyword "equiv"} <q1> | <q2>  Check if two queries are equivalent"
  IO.println s!"  {Color.keyword "normalize"} <sql>    Show normalized form of query"
  IO.println s!"  {Color.keyword "schema"}             Show sample database schema"
  IO.println s!"  {Color.keyword "dialect"} [name]     Show or set the target dialect (standard, sqlite, duckdb, postgres)"
  IO.println s!"  {Color.keyword "help"}               Show this help message"
  IO.println s!"  {Color.keyword "quit"} / {Color.keyword "exit"}       Exit the REPL"
  IO.println ""
  IO.println s!"{Color.dimText "Examples:"}"
  IO.println s!"  sql> parse SELECT * FROM users WHERE age > 25"
  IO.println s!"  sql> eval SELECT name, age FROM users ORDER BY age DESC"
  IO.println s!"  sql> equiv SELECT a, b FROM t | SELECT b, a FROM t"
  IO.println s!"  sql> normalize SELECT * FROM users WHERE x AND y"
  IO.println ""

/-- Show database schema -/
def cmdSchema : IO Unit := do
  IO.println s!"\n{Color.boldCyan "Sample Database Schema"}{Color.reset}\n"

  IO.println s!"{Color.keyword "users"} ({sampleUsers.length} rows)"
  IO.println "  id         : INT"
  IO.println "  name       : VARCHAR"
  IO.println "  age        : INT"
  IO.println "  department : VARCHAR"
  IO.println ""

  IO.println s!"{Color.keyword "orders"} ({sampleOrders.length} rows)"
  IO.println "  id         : INT"
  IO.println "  user_id    : INT"
  IO.println "  amount     : INT"
  IO.println "  product    : VARCHAR"
  IO.println ""

  IO.println s!"{Color.keyword "products"} ({sampleProducts.length} rows)"
  IO.println "  id         : INT"
  IO.println "  name       : VARCHAR"
  IO.println "  price      : INT"
  IO.println ""

-- ============================================================================
-- Batch Mode
-- ============================================================================

/-- Process a file in batch mode -/
def processBatchFile (filename : String) : IO Unit := do
  IO.println s!"\n{Color.info "Processing file"}: {filename}\n"

  let content <- IO.FS.readFile filename
  let lines := content.splitOn "\n"

  let mut lineNum := 0
  let mut currentQuery := ""

  for line in lines do
    lineNum := lineNum + 1
    let trimmed := line.trimAscii.toString

    -- Skip empty lines and comments
    if trimmed.isEmpty || trimmed.startsWith "--" then
      continue

    -- Accumulate multi-line queries
    currentQuery := currentQuery ++ " " ++ trimmed

    -- Check if query is complete (ends with semicolon)
    if trimmed.endsWith ";" then
      let query := currentQuery.trimAscii.toString.dropEnd 1 |>.toString  -- Remove semicolon
      IO.println s!"{Color.dimText "---"} Line {lineNum}: {query.take 50}..."

      match ← parseD query with
      | .ok stmt => runStatement stmt true
      | .error e =>
        IO.println s!"{Color.error "ERROR"}: {e}"

      currentQuery := ""
      IO.println ""

-- ============================================================================
-- REPL Main Loop
-- ============================================================================

/-- Parse a command from input -/
def parseCommand (input : String) : Option (String × String) :=
  let trimmed := input.trimAscii.toString
  if trimmed.isEmpty then none
  else
    let parts := trimmed.splitOn " "
    match parts.head? with
    | none => none
    | some cmd =>
      let args := " ".intercalate (parts.drop 1)
      some (cmd.toLower, args)

/-- Main REPL loop -/
partial def replLoop : IO Unit := do
  IO.print s!"{Color.cyanText "sql>"} "
  (← IO.getStdout).flush

  let stdin <- IO.getStdin
  let raw <- stdin.getLine
  -- end of input: `getLine` returns "" (an empty line is "\n"); stop instead of looping forever
  if raw.isEmpty then
    IO.println ""
    return
  let input := raw.trimAscii.toString

  match parseCommand input with
  | none => replLoop
  | some (cmd, args) =>
    match cmd with
    | "quit" | "exit" | "q" =>
      IO.println s!"\n{Color.info "Goodbye!"}"
    | "help" | "h" | "?" =>
      cmdHelp
      replLoop
    | "parse" | "p" =>
      if args.isEmpty then
        IO.println s!"{Color.error "Error"}: Missing SQL argument"
        IO.println "  Usage: parse <sql>"
      else
        cmdParse args
      replLoop
    | "eval" | "e" | "run" =>
      if args.isEmpty then
        IO.println s!"{Color.error "Error"}: Missing SQL argument"
        IO.println "  Usage: eval <sql>"
      else
        cmdEval args
      replLoop
    | "equiv" | "eq" =>
      if args.isEmpty then
        IO.println s!"{Color.error "Error"}: Missing SQL arguments"
        IO.println "  Usage: equiv <query1> | <query2>"
      else
        cmdEquiv args
      replLoop
    | "normalize" | "norm" | "n" =>
      if args.isEmpty then
        IO.println s!"{Color.error "Error"}: Missing SQL argument"
        IO.println "  Usage: normalize <sql>"
      else
        cmdNormalize args
      replLoop
    | "schema" | "s" =>
      cmdSchema
      replLoop
    | "dialect" =>
      if args.isEmpty then
        IO.println s!"Dialect: {dialectName (← dialectRef.get)}"
      else
        match Dialect.ofString? args with
        | some d =>
          dialectRef.set d
          IO.println s!"{Color.success "Dialect"}: {dialectName d}"
        | none =>
          IO.println s!"{Color.error "Unknown dialect"}: {args} (standard, sqlite, duckdb, postgres)"
      replLoop
    | _ =>
      -- Try to parse as SQL directly (default: eval)
      if input.toUpper.startsWith "SELECT" ||
         input.toUpper.startsWith "INSERT" ||
         input.toUpper.startsWith "UPDATE" ||
         input.toUpper.startsWith "DELETE" then
        cmdEval input
      else
        IO.println s!"{Color.error "Unknown command"}: {cmd}"
        IO.println "  Type 'help' for available commands"
      replLoop

/-- Print welcome banner -/
def printBanner : IO Unit := do
  IO.println ""
  IO.println s!"{Color.boldCyan "+===================================+"}"
  IO.println s!"|  SQL Parser & Equivalence Prover  |"
  IO.println s!"|           in Lean 4               |"
  IO.println s!"+==================================={Color.reset}"
  IO.println ""
  IO.println s!"{Color.dimText "Type 'help' for available commands"}"
  IO.println s!"{Color.dimText "Type 'schema' to see sample database"}"
  IO.println ""

-- ============================================================================
-- Main Entry Point
-- ============================================================================

/-- Remove `--dialect <name>` from the arguments. -/
def extractDialect : List String → Option String × List String
  | "--dialect" :: name :: rest => (some name, rest)
  | ["--dialect"] => (some "", [])
  | a :: rest => let (d, r) := extractDialect rest; (d, a :: r)
  | [] => (none, [])

def main (args0 : List String) : IO Unit := do
  let (dialectArg, args) := extractDialect args0
  match dialectArg with
  | some name =>
    match Dialect.ofString? name with
    | some d => dialectRef.set d
    | none =>
      IO.eprintln s!"Unknown dialect: {name} (standard, sqlite, duckdb, postgres)"
      IO.Process.exit 2
  | none =>
    -- The Spider gold results were computed on sqlite, so --spider-eval
    -- defaults to the sqlite dialect; everything else defaults to standard.
    if args.head? == some "--spider-eval" then dialectRef.set .sqlite
  -- Check for batch mode
  if args.length >= 2 && args[0]! == "--file" then
    let filename := args[1]!
    -- Try to process file (will fail if doesn't exist)
    try
      processBatchFile filename
    catch _ =>
      IO.println s!"{Color.error "Error"}: File not found or could not be read: {filename}"
      IO.Process.exit 1
  else if args.length >= 2 && args[0]! == "--parse-lines" then
    -- Machine-readable parse check (Spider baseline, tools/spider_parse_baseline.py):
    -- one SQL statement per line; prints "ok<TAB>line" or "err<TAB>line<TAB>message".
    let filename := args[1]!
    let content ← IO.FS.readFile filename
    let mut n := 0
    for line in content.splitOn "\n" do
      n := n + 1
      if line.trimAscii.isEmpty then
        continue
      match ← parseD line with
      | .ok _ => IO.println s!"ok\t{n}"
      | .error e =>
        let msg := (e.splitOn "\n").headD e
        IO.println s!"err\t{n}\t{msg}"
  else if args.length >= 2 && args[0]! == "--spider-eval" then
    -- Batch evaluation for the Spider evaluate-rate baseline (#225,
    -- tools/spider_eval_baseline.py). Manifest format, one item per line:
    --   #DB <db_id>          start a database
    --   #TABLE <name>        start a table (within current db)
    --   col1|col2            header row for current table
    --   v1|v2                data row (shape-parsed: NULL / int / d.d / text)
    --   #QUERY <db_id>       next line is the SQL (one line)
    -- Output per query: "#RESULT <i> ok" + header-less pipe rows + "#END",
    -- or "#RESULT <i> err <msg>".
    let content ← IO.FS.readFile args[1]!
    let parseCell : String → SqlEquiv.Value := fun c =>
      if c == "NULL" then .null none
      else match c.toInt? with
      | some n => .int n
      | none =>
        match c.splitOn "." with
        | [ip, fp] =>
          if fp.length > 0 && fp.all Char.isDigit then
            match (ip ++ fp).toInt? with
            | some u => SqlEquiv.Value.mkDecimal u fp.length
            | none => .string c
          else .string c
        | _ => .string c
    let renderCell : SqlEquiv.Value → String := fun v =>
      match v with
      | .int n => toString n
      | .string st => st
      | .bool b => if b then "1" else "0"
      | .null _ => "NULL"
      | .decimal _ _ => v.toSql
    let mut dbs : List (String × List (String × SqlEquiv.Table)) := []
    let mut curDb : String := ""
    let mut curTable : String := ""
    let mut curCols : List String := []
    let mut curRows : SqlEquiv.Table := []
    let mut queries : List (String × String) := []
    let mut pendingQueryDb : Option String := none
    let flushTable : List (String × List (String × SqlEquiv.Table)) → String → String →
        List String → SqlEquiv.Table → List (String × List (String × SqlEquiv.Table)) :=
      fun dbs' db tbl _cols rows =>
        if db == "" || tbl == "" then dbs'
        else match dbs'.lookup db with
        | some tbls => (db, (tbl, rows.reverse) :: tbls) :: dbs'.filter (·.1 != db)
        | none => (db, [(tbl, rows.reverse)]) :: dbs'
    for line in content.splitOn "\n" do
      match pendingQueryDb with
      | some qdb =>
        queries := queries ++ [(qdb, line)]
        pendingQueryDb := none
      | none =>
        if line.startsWith "#DB " then
          dbs := flushTable dbs curDb curTable curCols curRows
          curDb := (line.drop 4).trimAscii.toString
          curTable := ""; curCols := []; curRows := []
        else if line.startsWith "#TABLE " then
          dbs := flushTable dbs curDb curTable curCols curRows
          curTable := (line.drop 7).trimAscii.toString
          curCols := []; curRows := []
        else if line.startsWith "#QUERY " then
          dbs := flushTable dbs curDb curTable curCols curRows
          curTable := ""; curCols := []; curRows := []
          pendingQueryDb := some ((line.drop 7).trimAscii.toString)
        else if line.trimAscii.isEmpty then
          pure ()
        else if curTable != "" && curCols.isEmpty then
          curCols := line.splitOn "|"
        else if curTable != "" then
          let cells := (line.splitOn "|").map parseCell
          curRows := (curCols.zip cells) :: curRows
    dbs := flushTable dbs curDb curTable curCols curRows
    let mut i := 0
    for (qdb, sql) in queries do
      i := i + 1
      let tbls := (dbs.lookup qdb).getD []
      let database : SqlEquiv.Database := fun n =>
        ((tbls.find? (fun (tn, _) => tn.toLower == n.toLower)).map (·.2)).getD []
      match ← parseD sql with
      | .error e =>
        IO.println s!"#RESULT {i} err parse: {(s!"{e}".splitOn "\n").headD ""}"
      | .ok stmt =>
        -- the dialect's error mode decides whether an evaluation error fails the query (#270)
        match SqlEquiv.evalStmtIn (← dialectRef.get).config.errors database stmt with
        | .error e => IO.println s!"#RESULT {i} err {e}"
        | .ok (_, none) => IO.println s!"#RESULT {i} err no-result"
        | .ok (_, some tableResult) =>
          IO.println s!"#RESULT {i} ok"
          for row in tableResult do
            IO.println (String.intercalate "|" (row.map (fun (_, v) => renderCell v)))
          IO.println "#END"
  else if args.length >= 1 && (args[0]! == "--help" || args[0]! == "-h") then
    IO.println "Usage: sql_equiv [options]"
    IO.println ""
    IO.println "Options:"
    IO.println "  --file <path>   Process SQL file in batch mode"
    IO.println "  --parse-lines <path>  Parse one statement per line, machine-readable output"
    IO.println "  --dialect <name>  Target engine for implementation-defined behaviour:"
    IO.println "                    standard (default), sqlite, duckdb, postgres"
    IO.println "                    (--spider-eval defaults to sqlite)"
    IO.println "  --help, -h      Show this help message"
    IO.println ""
    IO.println "Without options, starts interactive REPL mode."
  else
    -- Interactive mode
    printBanner
    replLoop
