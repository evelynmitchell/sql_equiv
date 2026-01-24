/-
  SQL Parser: String → AST

  Hand-rolled recursive descent parser with tokenizer.
  Uses a simple Parser monad for error handling and state.
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Tokens
-- ============================================================================

/-- Token types produced by the lexer -/
inductive Token where
  | keyword  : String → Token          -- SELECT, FROM, WHERE, etc.
  | ident    : String → Token          -- identifiers
  | intLit   : Int → Token             -- integer literals
  | strLit   : String → Token          -- string literals
  | op       : String → Token          -- operators: +, -, *, /, =, <>, etc.
  | lparen   : Token                   -- (
  | rparen   : Token                   -- )
  | comma    : Token                   -- ,
  | dot      : Token                   -- .
  | semicolon: Token                   -- ;
  | star     : Token                   -- * (when used as select all)
  | eof      : Token
  deriving Repr, BEq, Inhabited

-- ============================================================================
-- Parser Monad
-- ============================================================================

/-- Parser state: remaining tokens and position -/
structure ParseState where
  tokens : List Token
  pos    : Nat
  deriving Repr

/-- Parser error -/
structure ParseError where
  message : String
  pos     : Nat
  deriving Repr

/-- Parser monad: Either error or (result, remaining state) -/
abbrev Parser (α : Type) := ParseState → Except ParseError (α × ParseState)

namespace Parser

def pure (a : α) : Parser α := fun s => .ok (a, s)

def bind (p : Parser α) (f : α → Parser β) : Parser β := fun s =>
  match p s with
  | .error e => .error e
  | .ok (a, s') => f a s'

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

def fail (msg : String) : Parser α := fun s =>
  .error { message := msg, pos := s.pos }

def getState : Parser ParseState := fun s => .ok (s, s)

def setState (s : ParseState) : Parser Unit := fun _ => .ok ((), s)

/-- Peek at current token without consuming -/
def peek : Parser Token := fun s =>
  match s.tokens with
  | [] => .ok (.eof, s)
  | t :: _ => .ok (t, s)

/-- Consume and return current token -/
def advance : Parser Token := fun s =>
  match s.tokens with
  | [] => .ok (.eof, s)
  | t :: ts => .ok (t, { tokens := ts, pos := s.pos + 1 })

/-- Check if current token matches -/
def check (pred : Token → Bool) : Parser Bool := do
  let t ← peek
  return pred t

/-- Try parser, backtrack on failure -/
def tryP (p : Parser α) : Parser (Option α) := fun s =>
  match p s with
  | .error _ => .ok (none, s)
  | .ok (a, s') => .ok (some a, s')

/-- Parse with alternative on failure -/
def orElse (p1 : Parser α) (p2 : Unit → Parser α) : Parser α := fun s =>
  match p1 s with
  | .ok r => .ok r
  | .error _ => p2 () s

instance : OrElse (Parser α) where
  orElse := orElse

/-- Expect a specific token -/
def expect (expected : Token) (msg : String) : Parser Unit := do
  let t ← advance
  if t == expected then return ()
  else fail msg

/-- Parse zero or more -/
partial def many (p : Parser α) : Parser (List α) := do
  match ← tryP p with
  | none => return []
  | some a =>
    let rest ← many p
    return a :: rest

/-- Parse one or more -/
def many1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← many p
  return first :: rest

/-- Parse separated list -/
partial def sepBy (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  match ← tryP p with
  | none => return []
  | some first =>
    let rest ← many (do sep; p)
    return first :: rest

/-- Parse non-empty separated list -/
def sepBy1 (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  let first ← p
  let rest ← many (do sep; p)
  return first :: rest

end Parser

-- ============================================================================
-- Tokenizer
-- ============================================================================

/-- SQL keywords (uppercase for matching) -/
def sqlKeywords : List String := [
  "SELECT", "FROM", "WHERE", "AND", "OR", "NOT", "NULL", "TRUE", "FALSE",
  "INSERT", "INTO", "VALUES", "UPDATE", "SET", "DELETE",
  "JOIN", "INNER", "LEFT", "RIGHT", "FULL", "CROSS", "ON",
  "ORDER", "BY", "ASC", "DESC", "GROUP", "HAVING", "DISTINCT",
  "LIMIT", "OFFSET", "AS", "IN", "BETWEEN", "LIKE", "CASE", "WHEN", "THEN",
  "ELSE", "END", "IS", "UNION", "INTERSECT", "EXCEPT", "ALL",
  "COUNT", "SUM", "AVG", "MIN", "MAX", "EXISTS"
]

/-- Check if string is an aggregate function name -/
def isAggFunc (s : String) : Option AggFunc :=
  match s.toUpper with
  | "COUNT" => some .count
  | "SUM"   => some .sum
  | "AVG"   => some .avg
  | "MIN"   => some .min
  | "MAX"   => some .max
  | _       => none

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def isDigit (c : Char) : Bool :=
  c >= '0' && c <= '9'

def isAlpha (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'

def isAlphaNum (c : Char) : Bool :=
  isAlpha c || isDigit c

/-- Tokenize input string -/
partial def tokenize (input : String) : Except String (List Token) := do
  let rec go (chars : List Char) (acc : List Token) : Except String (List Token) :=
    match chars with
    | [] => .ok acc.reverse
    | c :: rest =>
      if isWhitespace c then
        go rest acc
      else if c == '(' then
        go rest (.lparen :: acc)
      else if c == ')' then
        go rest (.rparen :: acc)
      else if c == ',' then
        go rest (.comma :: acc)
      else if c == '.' then
        go rest (.dot :: acc)
      else if c == ';' then
        go rest (.semicolon :: acc)
      else if c == '*' then
        go rest (.star :: acc)
      else if c == '+' then
        go rest (.op "+" :: acc)
      else if c == '-' then
        go rest (.op "-" :: acc)
      else if c == '/' then
        go rest (.op "/" :: acc)
      else if c == '%' then
        go rest (.op "%" :: acc)
      else if c == '=' then
        go rest (.op "=" :: acc)
      else if c == '<' then
        match rest with
        | '>' :: rest' => go rest' (.op "<>" :: acc)
        | '=' :: rest' => go rest' (.op "<=" :: acc)
        | _ => go rest (.op "<" :: acc)
      else if c == '>' then
        match rest with
        | '=' :: rest' => go rest' (.op ">=" :: acc)
        | _ => go rest (.op ">" :: acc)
      else if c == '|' then
        match rest with
        | '|' :: rest' => go rest' (.op "||" :: acc)
        | _ => .error "Unexpected character: |"
      else if c == '!' then
        match rest with
        | '=' :: rest' => go rest' (.op "<>" :: acc)
        | _ => .error "Unexpected character: !"
      else if c == '\'' then
        -- String literal
        let rec readStr (cs : List Char) (accStr : List Char) : Except String (String × List Char) :=
          match cs with
          | [] => .error "Unterminated string literal"
          | '\'' :: '\'' :: cs' => readStr cs' ('\'' :: accStr)  -- escaped quote
          | '\'' :: cs' => .ok (String.ofList accStr.reverse, cs')
          | ch :: cs' => readStr cs' (ch :: accStr)
        match readStr rest [] with
        | .error e => .error e
        | .ok (s, rest') => go rest' (.strLit s :: acc)
      else if isDigit c then
        -- Integer literal
        let (digits, rest') := rest.span isDigit
        let numStr := String.ofList (c :: digits)
        match numStr.toInt? with
        | some n => go rest' (.intLit n :: acc)
        | none => .error s!"Invalid integer: {numStr}"
      else if isAlpha c then
        -- Identifier or keyword
        let (chars', rest') := rest.span isAlphaNum
        let word := String.ofList (c :: chars')
        let upper := word.toUpper
        if sqlKeywords.contains upper then
          go rest' (.keyword upper :: acc)
        else
          go rest' (.ident word :: acc)
      else
        .error s!"Unexpected character: {c}"
  go input.toList []

-- ============================================================================
-- Expression Parser
-- ============================================================================

/-- Check if token is a keyword -/
def isKeyword (kw : String) : Token → Bool
  | .keyword k => k == kw
  | _ => false

/-- Parse identifier -/
def parseIdent : Parser String := do
  let t ← Parser.advance
  match t with
  | .ident s => return s
  | .keyword s => return s  -- Allow keywords as identifiers in some contexts
  | _ => Parser.fail "Expected identifier"

/-- Parse column reference (possibly qualified) -/
def parseColumnRef : Parser ColumnRef := do
  let first ← parseIdent
  let hasDot ← Parser.check (· == .dot)
  if hasDot then
    let _ ← Parser.advance  -- consume dot
    let col ← parseIdent
    return { table := some first, column := col }
  else
    return { table := none, column := first }

/-- Keywords that cannot be used as column names in SELECT items -/
def reservedSelectKeywords : List String := [
  "FROM", "WHERE", "GROUP", "HAVING", "ORDER", "LIMIT", "OFFSET",
  "UNION", "INTERSECT", "EXCEPT", "INTO", "VALUES"
]

-- Expression parsing uses mutual recursion with SELECT parser (for subqueries)
mutual

/-- Parse primary expression (literals, columns, parenthesized, aggregates, EXISTS) -/
partial def parsePrimary : Parser Expr := do
  let t ← Parser.peek
  match t with
  | .intLit n =>
    let _ ← Parser.advance
    return .lit (.int n)
  | .strLit s =>
    let _ ← Parser.advance
    return .lit (.string s)
  | .keyword "TRUE" =>
    let _ ← Parser.advance
    return .lit (.bool true)
  | .keyword "FALSE" =>
    let _ ← Parser.advance
    return .lit (.bool false)
  | .keyword "NULL" =>
    let _ ← Parser.advance
    return .lit .null
  | .keyword "NOT" =>
    let _ ← Parser.advance
    -- Check for NOT EXISTS
    let t2 ← Parser.peek
    if isKeyword "EXISTS" t2 then
      let _ ← Parser.advance
      Parser.expect .lparen "Expected ("
      let sel ← parseSelectStmt
      Parser.expect .rparen "Expected )"
      return .exists true sel  -- negated EXISTS
    else
      let e ← parsePrimary
      return .unaryOp .not e
  | .op "-" =>
    let _ ← Parser.advance
    let e ← parsePrimary
    return .unaryOp .neg e
  | .keyword "CASE" =>
    let _ ← Parser.advance
    let branches ← parseWhenBranches
    let else_ ← parseElse
    Parser.expect (.keyword "END") "Expected END"
    return .case branches else_
  | .keyword "EXISTS" =>
    let _ ← Parser.advance
    Parser.expect .lparen "Expected ("
    let sel ← parseSelectStmt
    Parser.expect .rparen "Expected )"
    return .exists false sel
  | .lparen =>
    let _ ← Parser.advance
    -- Could be subquery or parenthesized expression
    let t' ← Parser.peek
    if isKeyword "SELECT" t' then
      -- Scalar subquery
      let sel ← parseSelectStmt
      Parser.expect .rparen "Expected )"
      return .subquery sel
    else
      let e ← parseExpr
      Parser.expect .rparen "Expected )"
      return e
  | .ident _ | .keyword _ =>
    -- Could be column ref, function call, or aggregate
    let first ← parseIdent
    let t' ← Parser.peek
    if t' == .lparen then
      -- Check if it's an aggregate function
      match isAggFunc first with
      | some aggFn =>
        let _ ← Parser.advance
        -- Check for COUNT(*)
        let t'' ← Parser.peek
        if aggFn == .count && t'' == .star then
          let _ ← Parser.advance
          Parser.expect .rparen "Expected )"
          return .countStar
        else
          -- Check for DISTINCT
          let hasDistinct ←
            if isKeyword "DISTINCT" t'' then
              let _ ← Parser.advance
              Parser.pure true
            else
              Parser.pure false
          -- Parse the argument (could be * for COUNT, or an expression)
          let t''' ← Parser.peek
          if t''' == .star then
            let _ ← Parser.advance
            Parser.expect .rparen "Expected )"
            return .countStar
          else
            let arg ← parseExpr
            Parser.expect .rparen "Expected )"
            return .agg aggFn (some arg) hasDistinct
      | none =>
        -- Regular function call
        let _ ← Parser.advance
        let args ← Parser.sepBy parseExpr (Parser.expect .comma "")
        Parser.expect .rparen "Expected )"
        return .func first args
    else if t' == .dot then
      -- Qualified column
      let _ ← Parser.advance
      let col ← parseIdent
      return .col { table := some first, column := col }
    else
      return .col { table := none, column := first }
  | _ => Parser.fail "Expected expression"

where
  parseWhenBranches : Parser (List (Expr × Expr)) := do
    let t ← Parser.peek
    if isKeyword "WHEN" t then
      let _ ← Parser.advance
      let cond ← parseExpr
      Parser.expect (.keyword "THEN") "Expected THEN"
      let result ← parseExpr
      let rest ← parseWhenBranches
      return (cond, result) :: rest
    else
      return []

  parseElse : Parser (Option Expr) := do
    let t ← Parser.peek
    if isKeyword "ELSE" t then
      let _ ← Parser.advance
      let e ← parseExpr
      return some e
    else
      return none

/-- Parse postfix operators (IS NULL, IN, NOT IN, BETWEEN, LIKE) -/
partial def parsePostfix (e : Expr) : Parser Expr := do
  let t ← Parser.peek
  if isKeyword "IS" t then
    let _ ← Parser.advance
    let t2 ← Parser.peek
    if isKeyword "NULL" t2 then
      let _ ← Parser.advance
      parsePostfix (.unaryOp .isNull e)
    else if isKeyword "NOT" t2 then
      let _ ← Parser.advance
      Parser.expect (.keyword "NULL") "Expected NULL"
      parsePostfix (.unaryOp .isNotNull e)
    else
      Parser.fail "Expected NULL or NOT NULL after IS"
  else if isKeyword "NOT" t then
    -- NOT IN
    let _ ← Parser.advance
    let t2 ← Parser.peek
    if isKeyword "IN" t2 then
      let _ ← Parser.advance
      Parser.expect .lparen "Expected ("
      -- Check if it's a subquery or value list
      let t3 ← Parser.peek
      if isKeyword "SELECT" t3 then
        let sel ← parseSelectStmt
        Parser.expect .rparen "Expected )"
        parsePostfix (.inSubquery e true sel)  -- negated
      else
        let vals ← Parser.sepBy1 parseExpr (Parser.expect .comma "")
        Parser.expect .rparen "Expected )"
        parsePostfix (.inList e true vals)  -- negated
    else
      Parser.fail "Expected IN after NOT"
  else if isKeyword "IN" t then
    let _ ← Parser.advance
    Parser.expect .lparen "Expected ("
    -- Check if it's a subquery or value list
    let t2 ← Parser.peek
    if isKeyword "SELECT" t2 then
      let sel ← parseSelectStmt
      Parser.expect .rparen "Expected )"
      parsePostfix (.inSubquery e false sel)
    else
      let vals ← Parser.sepBy1 parseExpr (Parser.expect .comma "")
      Parser.expect .rparen "Expected )"
      parsePostfix (.inList e false vals)
  else if isKeyword "BETWEEN" t then
    let _ ← Parser.advance
    let lo ← parseAddSub  -- Use parseAddSub to avoid consuming the AND
    Parser.expect (.keyword "AND") "Expected AND in BETWEEN"
    let hi ← parseAddSub
    parsePostfix (.between e lo hi)
  else if isKeyword "LIKE" t then
    let _ ← Parser.advance
    let pattern ← parsePrimary
    parsePostfix (.binOp .like e pattern)
  else
    return e

/-- Parse multiplication/division (highest precedence binops) -/
partial def parseMulDiv : Parser Expr := do
  let left ← parsePrimary
  let left' ← parsePostfix left
  parseMulDivRest left'
where
  parseMulDivRest (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    match t with
    | .star =>
      let _ ← Parser.advance
      let right ← parsePrimary
      let right' ← parsePostfix right
      parseMulDivRest (.binOp .mul left right')
    | .op "/" =>
      let _ ← Parser.advance
      let right ← parsePrimary
      let right' ← parsePostfix right
      parseMulDivRest (.binOp .div left right')
    | .op "%" =>
      let _ ← Parser.advance
      let right ← parsePrimary
      let right' ← parsePostfix right
      parseMulDivRest (.binOp .mod left right')
    | _ => return left

/-- Parse addition/subtraction -/
partial def parseAddSub : Parser Expr := do
  let left ← parseMulDiv
  parseAddSubRest left
where
  parseAddSubRest (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    match t with
    | .op "+" =>
      let _ ← Parser.advance
      let right ← parseMulDiv
      parseAddSubRest (.binOp .add left right)
    | .op "-" =>
      let _ ← Parser.advance
      let right ← parseMulDiv
      parseAddSubRest (.binOp .sub left right)
    | .op "||" =>
      let _ ← Parser.advance
      let right ← parseMulDiv
      parseAddSubRest (.binOp .concat left right)
    | _ => return left

/-- Parse comparison operators -/
partial def parseComparison : Parser Expr := do
  let left ← parseAddSub
  parseCompRest left
where
  parseCompRest (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    match t with
    | .op "=" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .eq left right
    | .op "<>" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .ne left right
    | .op "<" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .lt left right
    | .op "<=" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .le left right
    | .op ">" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .gt left right
    | .op ">=" =>
      let _ ← Parser.advance
      let right ← parseAddSub
      return .binOp .ge left right
    | _ => return left

/-- Parse AND expressions -/
partial def parseAnd : Parser Expr := do
  let left ← parseComparison
  parseAndRest left
where
  parseAndRest (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    if isKeyword "AND" t then
      let _ ← Parser.advance
      let right ← parseComparison
      parseAndRest (.binOp .and left right)
    else
      return left

/-- Parse OR expressions (lowest precedence) -/
partial def parseOr : Parser Expr := do
  let left ← parseAnd
  parseOrRest left
where
  parseOrRest (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    if isKeyword "OR" t then
      let _ ← Parser.advance
      let right ← parseAnd
      parseOrRest (.binOp .or left right)
    else
      return left

/-- Main expression parser -/
partial def parseExpr : Parser Expr := parseOr

-- ============================================================================
-- SELECT Parser (within mutual block for subquery support)
-- ============================================================================

/-- Parse SELECT item: *, table.*, or expr AS alias -/
partial def parseSelectItem : Parser SelectItem := do
  let t ← Parser.peek
  match t with
  | .star =>
    let _ ← Parser.advance
    return .star none
  | .keyword kw =>
    -- Check if this keyword is reserved (cannot be a column name)
    if reservedSelectKeywords.contains kw then
      Parser.fail s!"Unexpected keyword {kw} in SELECT list"
    else
      -- Some keywords like aggregate functions can appear in SELECT items
      let e ← parseExpr
      let alias ← parseAlias
      return .exprItem e alias
  | .ident name =>
    -- Check for table.*
    let _ ← Parser.advance
    let t' ← Parser.peek
    if t' == .dot then
      let _ ← Parser.advance
      let t'' ← Parser.peek
      if t'' == .star then
        let _ ← Parser.advance
        return .star (some name)
      else
        -- It's table.column, put back the dot and re-parse as expression
        -- Actually, we need to handle this differently - parse as column ref
        let col ← parseIdent
        let e := Expr.col { table := some name, column := col }
        let alias ← parseAlias
        return .exprItem e alias
    else
      -- It's an identifier, could be column or start of expression
      let e := Expr.col { table := none, column := name }
      -- Check for more expression parts
      let e' ← parsePostfix e
      let e'' ← continueExprFrom e'
      let alias ← parseAlias
      return .exprItem e'' alias
  | _ =>
    -- General expression
    let e ← parseExpr
    let alias ← parseAlias
    return .exprItem e alias
where
  parseAlias : Parser (Option String) := do
    let t ← Parser.peek
    if isKeyword "AS" t then
      let _ ← Parser.advance
      let name ← parseIdent
      return some name
    else if t matches .ident _ then
      -- Alias without AS (if not a keyword that could start next clause)
      let name ← parseIdent
      return some name
    else
      return none

  -- Continue parsing expression from a starting expression (for operator precedence)
  continueExprFrom (left : Expr) : Parser Expr := do
    let t ← Parser.peek
    match t with
    | .star => do
      let _ ← Parser.advance
      let right ← parsePrimary
      let right' ← parsePostfix right
      continueExprFrom (.binOp .mul left right')
    | .op "+" | .op "-" | .op "/" | .op "||" | .op "%" =>
      -- There's more to the expression, but we've already consumed part
      -- For simplicity, just return what we have
      return left
    | _ => return left

/-- Parse table reference with optional alias -/
partial def parseTableRef : Parser TableRef := do
  let name ← parseIdent
  let alias ← do
    let t ← Parser.peek
    if isKeyword "AS" t then
      let _ ← Parser.advance
      some <$> parseIdent
    else if t matches .ident _ then
      some <$> parseIdent
    else
      Parser.pure none
  return { name := name, alias := alias }

/-- Parse JOIN type -/
partial def parseJoinType : Parser JoinType := do
  let t ← Parser.peek
  if isKeyword "INNER" t then
    let _ ← Parser.advance
    Parser.expect (.keyword "JOIN") "Expected JOIN"
    return .inner
  else if isKeyword "LEFT" t then
    let _ ← Parser.advance
    let _ ← Parser.tryP (Parser.expect (.keyword "OUTER") "")
    Parser.expect (.keyword "JOIN") "Expected JOIN"
    return .left
  else if isKeyword "RIGHT" t then
    let _ ← Parser.advance
    let _ ← Parser.tryP (Parser.expect (.keyword "OUTER") "")
    Parser.expect (.keyword "JOIN") "Expected JOIN"
    return .right
  else if isKeyword "FULL" t then
    let _ ← Parser.advance
    let _ ← Parser.tryP (Parser.expect (.keyword "OUTER") "")
    Parser.expect (.keyword "JOIN") "Expected JOIN"
    return .full
  else if isKeyword "CROSS" t then
    let _ ← Parser.advance
    Parser.expect (.keyword "JOIN") "Expected JOIN"
    return .cross
  else if isKeyword "JOIN" t then
    let _ ← Parser.advance
    return .inner
  else
    Parser.fail "Expected JOIN type"

/-- Parse a single FROM source (table or subquery) -/
partial def parseFromSource : Parser FromClause := do
  let t ← Parser.peek
  if t == .lparen then
    -- Subquery in FROM clause
    let _ ← Parser.advance
    let sel ← parseSelectStmt
    Parser.expect .rparen "Expected )"
    -- Must have alias
    let _ ← Parser.tryP (Parser.expect (.keyword "AS") "")
    let alias ← parseIdent
    return .subquery sel alias
  else
    -- Regular table reference
    let tref ← parseTableRef
    return .table tref

/-- Parse FROM clause with joins -/
partial def parseFromClause : Parser FromClause := do
  let first ← parseFromSource
  parseJoins first
where
  parseJoins (left : FromClause) : Parser FromClause := do
    let t ← Parser.peek
    let isJoin := isKeyword "JOIN" t || isKeyword "INNER" t || isKeyword "LEFT" t ||
                  isKeyword "RIGHT" t || isKeyword "FULL" t || isKeyword "CROSS" t
    if isJoin then
      let jtype ← parseJoinType
      let right ← parseFromSource
      let on_ ← if jtype == .cross then Parser.pure none else do
        Parser.expect (.keyword "ON") "Expected ON"
        some <$> parseExpr
      parseJoins (.join left jtype right on_)
    else
      return left

/-- Parse ORDER BY item -/
partial def parseOrderByItem : Parser OrderByItem := do
  let expr ← parseExpr
  let t ← Parser.peek
  let dir ←
    if isKeyword "ASC" t then
      let _ ← Parser.advance
      Parser.pure OrderDir.asc
    else if isKeyword "DESC" t then
      let _ ← Parser.advance
      Parser.pure OrderDir.desc
    else
      Parser.pure OrderDir.asc  -- default
  return .mk expr dir

/-- Parse SELECT statement (implementation for mutual recursion) -/
partial def parseSelectStmt : Parser SelectStmt := do
  Parser.expect (.keyword "SELECT") "Expected SELECT"

  -- DISTINCT?
  let t0 ← Parser.peek
  let distinct ←
    if isKeyword "DISTINCT" t0 then
      let _ ← Parser.advance
      Parser.pure true
    else
      Parser.pure false

  -- Select items
  let items ← Parser.sepBy1 parseSelectItem (Parser.expect .comma "")

  -- FROM clause (optional)
  let t1 ← Parser.peek
  let fromClause ←
    if isKeyword "FROM" t1 then
      let _ ← Parser.advance
      some <$> parseFromClause
    else
      Parser.pure none

  -- WHERE clause (optional)
  let t2 ← Parser.peek
  let whereClause ←
    if isKeyword "WHERE" t2 then
      let _ ← Parser.advance
      some <$> parseExpr
    else
      Parser.pure none

  -- GROUP BY clause (optional)
  let t3 ← Parser.peek
  let groupBy ←
    if isKeyword "GROUP" t3 then
      let _ ← Parser.advance
      Parser.expect (.keyword "BY") "Expected BY after GROUP"
      Parser.sepBy1 parseExpr (Parser.expect .comma "")
    else
      Parser.pure []

  -- HAVING clause (optional)
  let t4 ← Parser.peek
  let having ←
    if isKeyword "HAVING" t4 then
      let _ ← Parser.advance
      some <$> parseExpr
    else
      Parser.pure none

  -- ORDER BY clause (optional)
  let t5 ← Parser.peek
  let orderBy ←
    if isKeyword "ORDER" t5 then
      let _ ← Parser.advance
      Parser.expect (.keyword "BY") "Expected BY after ORDER"
      Parser.sepBy1 parseOrderByItem (Parser.expect .comma "")
    else
      Parser.pure []

  -- LIMIT (optional)
  let t6 ← Parser.peek
  let limitVal ←
    if isKeyword "LIMIT" t6 then
      let _ ← Parser.advance
      let t' ← Parser.advance
      match t' with
      | .intLit n => Parser.pure (some n.toNat)
      | _ => Parser.fail "Expected integer after LIMIT"
    else
      Parser.pure none

  -- OFFSET (optional)
  let t7 ← Parser.peek
  let offsetVal ←
    if isKeyword "OFFSET" t7 then
      let _ ← Parser.advance
      let t' ← Parser.advance
      match t' with
      | .intLit n => Parser.pure (some n.toNat)
      | _ => Parser.fail "Expected integer after OFFSET"
    else
      Parser.pure none

  return .mk distinct items fromClause whereClause groupBy having orderBy limitVal offsetVal

/-- Alias for parseSelectStmt (backwards compatibility) -/
partial def parseSelect : Parser SelectStmt := parseSelectStmt

/-- Parse set operation (UNION, INTERSECT, EXCEPT) -/
partial def parseSetOp : Parser (Option SetOp) := do
  let t ← Parser.peek
  if isKeyword "UNION" t then
    let _ ← Parser.advance
    let t2 ← Parser.peek
    if isKeyword "ALL" t2 then
      let _ ← Parser.advance
      return some .unionAll
    else
      return some .union
  else if isKeyword "INTERSECT" t then
    let _ ← Parser.advance
    return some .intersect
  else if isKeyword "EXCEPT" t then
    let _ ← Parser.advance
    return some .exceptOp
  else
    return none

/-- Parse a query (SELECT with optional set operations) -/
partial def parseQuery : Parser Query := do
  let first ← parseSelectStmt
  parseQueryRest (.simple first)
where
  parseQueryRest (left : Query) : Parser Query := do
    match ← parseSetOp with
    | some op =>
      let right ← parseSelectStmt
      parseQueryRest (.compound left op (.simple right))
    | none =>
      return left

-- ============================================================================
-- INSERT Parser
-- ============================================================================

partial def parseInsert : Parser InsertStmt := do
  Parser.expect (.keyword "INSERT") "Expected INSERT"
  Parser.expect (.keyword "INTO") "Expected INTO"

  let table ← parseIdent

  -- Optional column list
  let t0 ← Parser.peek
  let columns ←
    if t0 == .lparen then
      let _ ← Parser.advance
      let cols ← Parser.sepBy1 parseIdent (Parser.expect .comma "")
      Parser.expect .rparen "Expected )"
      Parser.pure (some cols)
    else
      Parser.pure none

  -- VALUES or SELECT
  let t1 ← Parser.peek
  let source ←
    if isKeyword "VALUES" t1 then
      let _ ← Parser.advance
      let rows ← Parser.sepBy1 (do
        Parser.expect .lparen "Expected ("
        let vals ← Parser.sepBy1 parseExpr (Parser.expect .comma "")
        Parser.expect .rparen "Expected )"
        Parser.pure vals
      ) (Parser.expect .comma "")
      Parser.pure (InsertSource.values rows)
    else if isKeyword "SELECT" t1 then
      let sel ← parseSelect
      Parser.pure (InsertSource.selectStmt sel)
    else
      Parser.fail "Expected VALUES or SELECT"

  return { table := table, columns := columns, source := source }

-- ============================================================================
-- UPDATE Parser
-- ============================================================================

partial def parseUpdate : Parser UpdateStmt := do
  Parser.expect (.keyword "UPDATE") "Expected UPDATE"

  let table ← parseIdent

  Parser.expect (.keyword "SET") "Expected SET"

  let assignments ← Parser.sepBy1 (do
    let col ← parseIdent
    Parser.expect (.op "=") "Expected ="
    let val ← parseExpr
    Parser.pure { column := col, value := val : Assignment }
  ) (Parser.expect .comma "")

  let t ← Parser.peek
  let whereClause ←
    if isKeyword "WHERE" t then
      let _ ← Parser.advance
      some <$> parseExpr
    else
      Parser.pure none

  return { table := table, assignments := assignments, whereClause := whereClause }

-- ============================================================================
-- DELETE Parser
-- ============================================================================

partial def parseDelete : Parser DeleteStmt := do
  Parser.expect (.keyword "DELETE") "Expected DELETE"
  Parser.expect (.keyword "FROM") "Expected FROM"

  let table ← parseIdent

  let t ← Parser.peek
  let whereClause ←
    if isKeyword "WHERE" t then
      let _ ← Parser.advance
      some <$> parseExpr
    else
      Parser.pure none

  return { table := table, whereClause := whereClause }

-- ============================================================================
-- Top-level Parser
-- ============================================================================

/-- Parse any SQL statement -/
partial def parseStmt : Parser Stmt := do
  let t ← Parser.peek
  if isKeyword "SELECT" t then
    .query <$> parseQuery
  else if isKeyword "INSERT" t then
    .insert <$> parseInsert
  else if isKeyword "UPDATE" t then
    .update <$> parseUpdate
  else if isKeyword "DELETE" t then
    .delete <$> parseDelete
  else
    Parser.fail "Expected SELECT, INSERT, UPDATE, or DELETE"

end -- mutual

/-- Parse SQL string to AST -/
def parse (input : String) : Except String Stmt := do
  let tokens ← tokenize input
  let state : ParseState := { tokens := tokens, pos := 0 }
  match parseStmt state with
  | .error e => Except.error s!"Parse error at position {e.pos}: {e.message}"
  | .ok (stmt, _) => Except.ok stmt

/-- Parse SELECT statement specifically -/
def parseSelectStr (input : String) : Except String SelectStmt := do
  let tokens ← tokenize input
  let state : ParseState := { tokens := tokens, pos := 0 }
  match parseSelect state with
  | .error e => Except.error s!"Parse error at position {e.pos}: {e.message}"
  | .ok (stmt, _) => Except.ok stmt

end SqlEquiv
