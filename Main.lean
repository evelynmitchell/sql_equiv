/-
  SQL Equivalence REPL

  Interactive command-line interface for the sql_equiv project.
  Supports parsing, evaluation, equivalence checking, and normalization.
-/
import SqlEquiv

open SqlEquiv

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
  | .string s => s
  | .bool b => if b then "true" else "false"
  | .null => "NULL"

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
  | .subquery _ alias => s!"(subquery) AS {alias}"
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
  match parse sql with
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
  match parse sql with
  | .ok stmt =>
    let (_, result) := evalStmt sampleDatabase stmt
    match result with
    | some table =>
      IO.println s!"\n{Color.success "Result"} ({table.length} rows):"
      IO.println (prettyTable table)
    | none =>
      IO.println s!"\n{Color.success "Statement executed"} (no result set)"
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

  match parse sql1, parse sql2 with
  | .ok stmt1, .ok stmt2 =>
    -- Check syntactic equivalence
    let result : EquivResult :=
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
                .maybeEquivalent "Results match on sample database (may not be universally equivalent)"
              else
                .notEquivalent "Different results on sample database"
        | _, _ =>
          .notEquivalent "Different statement types or complex queries"

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
  match parse sql with
  | .ok stmt =>
    match stmt with
    | .query (.simple sel) =>
      let normalized := normalizeSelect sel
      IO.println s!"\n{Color.success "Original"}:"
      IO.println s!"  {sel.toSql}"
      IO.println s!"\n{Color.success "Normalized"}:"
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

/-- Show optimized query (placeholder for future optimizer) -/
def cmdOptimize (sql : String) : IO Unit := do
  IO.println s!"\n{Color.info "Optimizing"}: {sql}"
  match parse sql with
  | .ok stmt =>
    IO.println s!"\n{Color.success "Original"}:"
    IO.println s!"  {stmt.toSql}"

    -- Apply basic optimizations
    match stmt with
    | .query (.simple sel) =>
      -- Optimization 1: Remove WHERE TRUE
      let (optimized, msg) : SelectStmt × Option String := match sel.whereClause with
        | some (.lit (.bool true)) =>
          let newSel := SelectStmt.mk sel.distinct sel.items sel.fromClause none sel.groupBy sel.having sel.orderBy sel.limitVal sel.offsetVal
          (newSel, some s!"\n{Color.info "Optimization"}: Removed redundant WHERE TRUE")
        -- Optimization 2: Detect WHERE FALSE (empty result)
        | some (.lit (.bool false)) =>
          (sel, some s!"\n{Color.warning "Warning"}: WHERE FALSE will always return empty result")
        | _ => (sel, none)

      if let some m := msg then IO.println m
      IO.println s!"\n{Color.success "Optimized"}:"
      IO.println s!"  {optimized.toSql}"
    | _ =>
      IO.println s!"\n{Color.dimText "(No optimizations available for this statement type)"}"
      IO.println s!"  {stmt.toSql}"
  | .error e =>
    IO.println s!"\n{Color.error "Parse error"}: {e}"

/-- Show help -/
def cmdHelp : IO Unit := do
  IO.println s!"\n{Color.boldCyan "SQL Equivalence REPL - Available Commands"}{Color.reset}\n"
  IO.println s!"  {Color.keyword "parse"} <sql>        Parse SQL and show AST"
  IO.println s!"  {Color.keyword "eval"} <sql>         Evaluate query against sample database"
  IO.println s!"  {Color.keyword "equiv"} <q1> | <q2>  Check if two queries are equivalent"
  IO.println s!"  {Color.keyword "normalize"} <sql>    Show normalized form of query"
  IO.println s!"  {Color.keyword "optimize"} <sql>     Show optimized query"
  IO.println s!"  {Color.keyword "schema"}             Show sample database schema"
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

      match parse query with
      | .ok stmt =>
        let (_, result) := evalStmt sampleDatabase stmt
        match result with
        | some table =>
          IO.println s!"{Color.success "OK"}: {table.length} rows"
          if table.length <= 5 then
            IO.println (prettyTable table)
        | none =>
          IO.println s!"{Color.success "OK"}: Statement executed"
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
  let input <- stdin.getLine
  let input := input.trimAscii.toString

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
    | "optimize" | "opt" | "o" =>
      if args.isEmpty then
        IO.println s!"{Color.error "Error"}: Missing SQL argument"
        IO.println "  Usage: optimize <sql>"
      else
        cmdOptimize args
      replLoop
    | "schema" | "s" =>
      cmdSchema
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

def main (args : List String) : IO Unit := do
  -- Check for batch mode
  if args.length >= 2 && args[0]! == "--file" then
    let filename := args[1]!
    -- Try to process file (will fail if doesn't exist)
    try
      processBatchFile filename
    catch _ =>
      IO.println s!"{Color.error "Error"}: File not found or could not be read: {filename}"
      IO.Process.exit 1
  else if args.length >= 1 && (args[0]! == "--help" || args[0]! == "-h") then
    IO.println "Usage: sql_equiv [options]"
    IO.println ""
    IO.println "Options:"
    IO.println "  --file <path>   Process SQL file in batch mode"
    IO.println "  --help, -h      Show this help message"
    IO.println ""
    IO.println "Without options, starts interactive REPL mode."
  else
    -- Interactive mode
    printBanner
    replLoop
