/-
  SQL Parser: String → AST

  Hand-rolled recursive descent parser with tokenizer.
  Uses a simple Parser monad for error handling and state.
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Position Tracking
-- ============================================================================

/-- Source position for error messages -/
structure SourcePos where
  line   : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, Inhabited

instance : ToString SourcePos where
  toString p := s!"line {p.line}, column {p.column}"

-- ============================================================================
-- Tokens
-- ============================================================================

/-- Token types produced by the lexer -/
inductive Token where
  | keyword  : String → Token          -- SELECT, FROM, WHERE, etc.
  | ident    : String → Token          -- identifiers
  | intLit   : Int → Token             -- integer literals
  | decLit   : Int → Nat → Token       -- decimal literals: unscaled value, scale (123.45 → 12345, 2)
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

/-- Token with source position -/
structure PositionedToken where
  token : Token
  pos   : SourcePos
  text  : String  -- original text representation
  deriving Repr, BEq, Inhabited

/-- Get human-readable description of a token -/
def Token.describe : Token → String
  | .keyword s => s!"keyword '{s}'"
  | .ident s => s!"identifier '{s}'"
  | .intLit n => s!"integer {n}"
  | .decLit u s => s!"decimal {u}e-{s}"
  | .strLit s => s!"string '{s}'"
  | .op s => s!"operator '{s}'"
  | .lparen => "'('"
  | .rparen => "')'"
  | .comma => "','"
  | .dot => "'.'"
  | .semicolon => "';'"
  | .star => "'*'"
  | .eof => "end of input"

-- ============================================================================
-- Parser Monad
-- ============================================================================

/-- Parser state: remaining tokens with positions -/
structure ParseState where
  tokens      : List PositionedToken
  pos         : Nat
  input       : String              -- original input for context
  parenStack  : List SourcePos      -- track open parentheses positions
  /-- The dialect's implementation-defined choices, written into the AST as
      it is built (NULL position of ORDER BY items, MIN/MAX mixed-type mode) -/
  config : DialectConfig := defaultDialect.config
  deriving Repr

/-- Parser error with detailed context -/
structure ParseError where
  message    : String
  line       : Nat
  column     : Nat
  context    : Option String        -- surrounding text
  suggestion : Option String        -- suggested fix
  deriving Repr

instance : ToString ParseError where
  toString e :=
    let loc := s!"at line {e.line}, column {e.column}"
    let ctx := match e.context with
      | some c => s!"\n  Near: {c}"
      | none => ""
    let sug := match e.suggestion with
      | some s => s!"\n  Suggestion: {s}"
      | none => ""
    s!"{e.message} {loc}{ctx}{sug}"

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

/-- Get context around current position -/
private def getContext (state : ParseState) : Option String :=
  -- Get up to 30 chars around current token
  match state.tokens with
  | [] => none
  | pt :: _ =>
    let startIdx := if pt.pos.column > 15 then pt.pos.column - 15 else 0
    let snippet := (state.input.drop startIdx |>.take 30).toString
    if snippet.isEmpty then none else some snippet

/-- Get current position -/
private def currentPos (state : ParseState) : SourcePos :=
  match state.tokens with
  | [] => ⟨1, state.input.length + 1⟩  -- end of input
  | pt :: _ => pt.pos

/-- Create an error with full context -/
def fail (msg : String) : Parser α := fun s =>
  let pos := currentPos s
  .error {
    message := msg
    line := pos.line
    column := pos.column
    context := getContext s
    suggestion := none
  }

/-- Create an error with a suggestion -/
def failWithSuggestion (msg : String) (suggestion : String) : Parser α := fun s =>
  let pos := currentPos s
  .error {
    message := msg
    line := pos.line
    column := pos.column
    context := getContext s
    suggestion := some suggestion
  }

def getState : Parser ParseState := fun s => .ok (s, s)

def setState (s : ParseState) : Parser Unit := fun _ => .ok ((), s)

/-- Peek at current token without consuming -/
def peek : Parser Token := fun s =>
  match s.tokens with
  | [] => .ok (.eof, s)
  | pt :: _ => .ok (pt.token, s)

/-- Peek at current positioned token -/
def peekPositioned : Parser PositionedToken := fun s =>
  match s.tokens with
  | [] => .ok (⟨.eof, ⟨1, s.input.length + 1⟩, ""⟩, s)
  | pt :: _ => .ok (pt, s)

/-- Consume and return current token -/
def advance : Parser Token := fun s =>
  match s.tokens with
  | [] => .ok (.eof, s)
  | pt :: pts => .ok (pt.token, { s with tokens := pts, pos := s.pos + 1 })

/-- Consume and return current positioned token -/
def advancePositioned : Parser PositionedToken := fun s =>
  match s.tokens with
  | [] => .ok (⟨.eof, ⟨1, s.input.length + 1⟩, ""⟩, s)
  | pt :: pts => .ok (pt, { s with tokens := pts, pos := s.pos + 1 })

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

/-- Expect a specific token with better error messages -/
def expect (expected : Token) (msg : String) : Parser Unit := fun s =>
  match s.tokens with
  | [] =>
    let pos := currentPos s
    .error {
      message := if msg.isEmpty then s!"Expected {expected.describe}, got end of input" else msg
      line := pos.line
      column := pos.column
      context := getContext s
      suggestion := none
    }
  | pt :: pts =>
    if pt.token == expected then
      .ok ((), { s with tokens := pts, pos := s.pos + 1 })
    else
      let actualDesc := pt.token.describe
      let expectedDesc := expected.describe
      .error {
        message := if msg.isEmpty then s!"Expected {expectedDesc}, got {actualDesc}" else s!"{msg} (got {actualDesc})"
        line := pt.pos.line
        column := pt.pos.column
        context := getContext s
        suggestion := none
      }

/-- Push open paren position onto stack -/
def pushParen : Parser Unit := fun s =>
  let pos := currentPos s
  .ok ((), { s with parenStack := pos :: s.parenStack })

/-- Pop paren position from stack -/
def popParen : Parser Unit := fun s =>
  match s.parenStack with
  | [] => .ok ((), s)
  | _ :: rest => .ok ((), { s with parenStack := rest })

/-- Expect close paren and pop from stack -/
def expectCloseParen (_openPos : SourcePos) : Parser Unit := do
  Parser.expect .rparen "Expected )"
  Parser.popParen

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
  "COUNT", "SUM", "AVG", "MIN", "MAX", "EXISTS",
  "WITH", "RECURSIVE", "OVER", "PARTITION", "ROW_NUMBER", "RANK", "DENSE_RANK"
]

/-- Check if string is an aggregate function name. MIN/MAX record the
    dialect's MIN/MAX mode (`mixed`). -/
def isAggFunc (s : String) (mixed : MinMaxMode := defaultDialect.config.minMaxMode) :
    Option AggFunc :=
  match s.toUpper with
  | "COUNT" => some .count
  | "SUM"   => some .sum
  | "AVG"   => some .avg
  | "MIN"   => some (.min mixed)
  | "MAX"   => some (.max mixed)
  | _       => none

/-- Map an aggregate function to its window-function counterpart
    (used when an aggregate call is followed by OVER, #214). -/
def aggToWindowFunc : AggFunc → WindowFunc
  | .count => .count
  | .sum   => .sum
  | .avg   => .avg
  | .min m => .min m
  | .max m => .max m

/-- Check if string is a ranking window function (ROW_NUMBER/RANK/DENSE_RANK).
    These are only valid with an OVER clause. -/
def isRankingFunc (s : String) : Option WindowFunc :=
  match s.toUpper with
  | "ROW_NUMBER" => some .rowNumber
  | "RANK"       => some .rank
  | "DENSE_RANK" => some .denseRank
  | _            => none

def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

def isDigit (c : Char) : Bool :=
  c >= '0' && c <= '9'

def isAlpha (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'

def isAlphaNum (c : Char) : Bool :=
  isAlpha c || isDigit c

/-- Tokenizer state tracking position -/
structure TokenizerState where
  line   : Nat := 1
  column : Nat := 1
  offset : Nat := 0  -- character offset from start
  deriving Repr

/-- Tokenizer error with position -/
structure TokenizerError where
  message : String
  line    : Nat
  column  : Nat
  context : Option String
  deriving Repr

instance : ToString TokenizerError where
  toString e :=
    let ctx := match e.context with
      | some c => s!" near '{c}'"
      | none => ""
    s!"{e.message} at line {e.line}, column {e.column}{ctx}"

/-- Advance position for a character -/
private def advancePos (state : TokenizerState) (c : Char) : TokenizerState :=
  if c == '\n' then
    { line := state.line + 1, column := 1, offset := state.offset + 1 }
  else
    { line := state.line, column := state.column + 1, offset := state.offset + 1 }

/-- Advance position for multiple characters -/
private def advancePosMany (state : TokenizerState) (chars : List Char) : TokenizerState :=
  chars.foldl advancePos state

/-- Get context string around position -/
private def getContextAt (input : String) (offset : Nat) : Option String :=
  let startIdx := if offset > 10 then offset - 10 else 0
  let snippet := (input.drop startIdx |>.take 20).toString
  if snippet.isEmpty then none else some snippet

/-- Tokenize input string with position tracking -/
partial def tokenize (input : String) : Except TokenizerError (List PositionedToken) := do
  let rec go (chars : List Char) (state : TokenizerState) (acc : List PositionedToken)
      : Except TokenizerError (List PositionedToken) :=
    match chars with
    | [] => .ok acc.reverse
    | c :: rest =>
      if isWhitespace c then
        go rest (advancePos state c) acc
      else if c == '(' then
        let pt := ⟨.lparen, ⟨state.line, state.column⟩, "("⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == ')' then
        let pt := ⟨.rparen, ⟨state.line, state.column⟩, ")"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == ',' then
        let pt := ⟨.comma, ⟨state.line, state.column⟩, ","⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '.' then
        -- Leading-dot decimal literal (`.5`); a bare dot stays the
        -- qualification token (column names can't start with a digit).
        match rest with
        | c2 :: rest' =>
          if isDigit c2 then
            let startPos := ⟨state.line, state.column⟩
            let (fracDigits, rest'') := rest'.span isDigit
            let allFrac := c2 :: fracDigits
            let consumed := '.' :: allFrac
            match (String.ofList allFrac).toInt? with
            | some u =>
              let pt := ⟨.decLit u allFrac.length, startPos, String.ofList consumed⟩
              go rest'' (advancePosMany state consumed) (pt :: acc)
            | none => .error {
                message := s!"Invalid decimal: {String.ofList consumed}"
                line := startPos.line
                column := startPos.column
                context := getContextAt input state.offset
              }
          else
            let pt := ⟨.dot, ⟨state.line, state.column⟩, "."⟩
            go rest (advancePos state c) (pt :: acc)
        | [] =>
          let pt := ⟨.dot, ⟨state.line, state.column⟩, "."⟩
          go rest (advancePos state c) (pt :: acc)
      else if c == ';' then
        let pt := ⟨.semicolon, ⟨state.line, state.column⟩, ";"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '*' then
        let pt := ⟨.star, ⟨state.line, state.column⟩, "*"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '+' then
        let pt := ⟨.op "+", ⟨state.line, state.column⟩, "+"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '-' then
        let pt := ⟨.op "-", ⟨state.line, state.column⟩, "-"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '/' then
        let pt := ⟨.op "/", ⟨state.line, state.column⟩, "/"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '%' then
        let pt := ⟨.op "%", ⟨state.line, state.column⟩, "%"⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '=' then
        let pt := ⟨.op "=", ⟨state.line, state.column⟩, "="⟩
        go rest (advancePos state c) (pt :: acc)
      else if c == '<' then
        match rest with
        | '>' :: rest' =>
          let pt := ⟨.op "<>", ⟨state.line, state.column⟩, "<>"⟩
          go rest' (advancePosMany state ['<', '>']) (pt :: acc)
        | '=' :: rest' =>
          let pt := ⟨.op "<=", ⟨state.line, state.column⟩, "<="⟩
          go rest' (advancePosMany state ['<', '=']) (pt :: acc)
        | _ =>
          let pt := ⟨.op "<", ⟨state.line, state.column⟩, "<"⟩
          go rest (advancePos state c) (pt :: acc)
      else if c == '>' then
        match rest with
        | '=' :: rest' =>
          let pt := ⟨.op ">=", ⟨state.line, state.column⟩, ">="⟩
          go rest' (advancePosMany state ['>', '=']) (pt :: acc)
        | _ =>
          let pt := ⟨.op ">", ⟨state.line, state.column⟩, ">"⟩
          go rest (advancePos state c) (pt :: acc)
      else if c == '|' then
        match rest with
        | '|' :: rest' =>
          let pt := ⟨.op "||", ⟨state.line, state.column⟩, "||"⟩
          go rest' (advancePosMany state ['|', '|']) (pt :: acc)
        | _ => .error {
            message := "Unexpected character '|' (did you mean '||'?)"
            line := state.line
            column := state.column
            context := getContextAt input state.offset
          }
      else if c == '!' then
        match rest with
        | '=' :: rest' =>
          let pt := ⟨.op "<>", ⟨state.line, state.column⟩, "!="⟩
          go rest' (advancePosMany state ['!', '=']) (pt :: acc)
        | _ => .error {
            message := "Unexpected character '!' (did you mean '!='?)"
            line := state.line
            column := state.column
            context := getContextAt input state.offset
          }
      else if c == '\'' then
        -- String literal
        let startPos := ⟨state.line, state.column⟩
        let rec readStr (cs : List Char) (st : TokenizerState) (accStr : List Char)
            : Except TokenizerError (String × List Char × TokenizerState) :=
          match cs with
          | [] => .error {
              message := "Unterminated string literal"
              line := startPos.line
              column := startPos.column
              context := some s!"String started at line {startPos.line}, column {startPos.column}"
            }
          | '\'' :: '\'' :: cs' =>
            readStr cs' (advancePosMany st ['\'', '\'']) ('\'' :: accStr)
          | '\'' :: cs' =>
            .ok (String.ofList accStr.reverse, cs', advancePos st '\'')
          | ch :: cs' =>
            readStr cs' (advancePos st ch) (ch :: accStr)
        match readStr rest (advancePos state c) [] with
        | .error e => .error e
        | .ok (s, rest', state') =>
          let pt := ⟨.strLit s, startPos, s!"'{s}'"⟩
          go rest' state' (pt :: acc)
      else if c == '"' then
        -- Double-quoted string literal (#215). Dialect decision: the SQL
        -- standard reserves double quotes for identifiers, but the project
        -- targets Spider compatibility and Spider/SQLite write string
        -- literals as "...". We have no quoted-identifier support, so there
        -- is no ambiguity today; revisit if quoted identifiers are added.
        let startPos := ⟨state.line, state.column⟩
        let rec readDStr (cs : List Char) (st : TokenizerState) (accStr : List Char)
            : Except TokenizerError (String × List Char × TokenizerState) :=
          match cs with
          | [] => .error {
              message := "Unterminated string literal"
              line := startPos.line
              column := startPos.column
              context := some s!"String started at line {startPos.line}, column {startPos.column}"
            }
          | '"' :: '"' :: cs' =>
            readDStr cs' (advancePosMany st ['"', '"']) ('"' :: accStr)
          | '"' :: cs' =>
            .ok (String.ofList accStr.reverse, cs', advancePos st '"')
          | ch :: cs' =>
            readDStr cs' (advancePos st ch) (ch :: accStr)
        match readDStr rest (advancePos state c) [] with
        | .error e => .error e
        | .ok (s, rest', state') =>
          let pt := ⟨.strLit s, startPos, s!"\"{s}\""⟩
          go rest' state' (pt :: acc)
      else if isDigit c then
        -- Integer or decimal literal. A '.' continues the number only when a
        -- digit follows, so `t1.col` and `1.x` still tokenize the dot alone.
        let startPos := ⟨state.line, state.column⟩
        let (digits, rest') := rest.span isDigit
        let allDigits := c :: digits
        let numStr := String.ofList allDigits
        let intToken := fun () =>
          match numStr.toInt? with
          | some n =>
            let pt := ⟨.intLit n, startPos, numStr⟩
            go rest' (advancePosMany state allDigits) (pt :: acc)
          | none => .error {
              message := s!"Invalid integer: {numStr}"
              line := startPos.line
              column := startPos.column
              context := getContextAt input state.offset
            }
        -- Exponent syntax (1e5, 1.5E-2) is float territory — reject loudly
        -- rather than silently lexing `1e5` as integer 1 aliased `e5` (#202).
        let isExponent := fun (cs : List Char) =>
          match cs with
          | 'e' :: d :: _ => isDigit d || d == '+' || d == '-'
          | 'E' :: d :: _ => isDigit d || d == '+' || d == '-'
          | _ => false
        let exponentError : List Char → Except TokenizerError (List PositionedToken) :=
          fun lit => .error {
            message := s!"Exponent literals are not supported (float types are not \
implemented): {String.ofList lit}…"
            line := startPos.line
            column := startPos.column
            context := getContextAt input state.offset
          }
        let decimalToken := fun (allFrac : List Char) (consumed : List Char) rest''' =>
          let unscaledStr := String.ofList (allDigits ++ allFrac)
          match unscaledStr.toInt? with
          | some u =>
            let pt := ⟨.decLit u allFrac.length, startPos, String.ofList consumed⟩
            go rest''' (advancePosMany state consumed) (pt :: acc)
          | none => .error {
              message := s!"Invalid decimal: {String.ofList consumed}"
              line := startPos.line
              column := startPos.column
              context := getContextAt input state.offset
            }
        match rest' with
        | '.' :: c2 :: rest'' =>
          if isDigit c2 then
            let (fracDigits, rest''') := rest''.span isDigit
            let allFrac := c2 :: fracDigits
            if isExponent rest''' then exponentError (allDigits ++ '.' :: allFrac)
            else decimalToken allFrac (allDigits ++ '.' :: allFrac) rest'''
          else if isAlpha c2 then intToken ()  -- e.g. `1.x`: leave the dot alone
          else
            -- Trailing-dot literal `1.` — engines read this as 1.0
            decimalToken [] (allDigits ++ ['.']) (c2 :: rest'')
        | ['.'] => decimalToken [] (allDigits ++ ['.']) []
        | _ =>
          if isExponent rest' then exponentError allDigits
          else intToken ()
      else if isAlpha c then
        -- Identifier or keyword
        let startPos := ⟨state.line, state.column⟩
        let (chars', rest') := rest.span isAlphaNum
        let allChars := c :: chars'
        let word := String.ofList allChars
        let upper := word.toUpper
        let token := if sqlKeywords.contains upper then .keyword upper else .ident word
        let pt := ⟨token, startPos, word⟩
        go rest' (advancePosMany state allChars) (pt :: acc)
      else
        .error {
          message := s!"Unexpected character: '{c}'"
          line := state.line
          column := state.column
          context := getContextAt input state.offset
        }
  go input.toList ⟨1, 1, 0⟩ []

-- ============================================================================
-- Error Helpers
-- ============================================================================

/-- Compute edit distance between two strings (for suggestions) -/
private partial def editDistance (s1 s2 : String) : Nat :=
  let a := s1.toList
  let b := s2.toList
  let m := a.length
  let n := b.length
  if m == 0 then n
  else if n == 0 then m
  else
    -- Simple recursive implementation (not optimal but fine for short keywords)
    let rec go (i j : Nat) : Nat :=
      if i == 0 then j
      else if j == 0 then i
      else
        let cost := if a[i-1]? == b[j-1]? then 0 else 1
        let del := go (i-1) j + 1
        let ins := go i (j-1) + 1
        let sub := go (i-1) (j-1) + cost
        Nat.min del (Nat.min ins sub)
    go m n

/-- Find similar keywords to a misspelled word -/
def suggestKeyword (word : String) : Option String :=
  let upper := word.toUpper
  let candidates := sqlKeywords.filter fun kw =>
    let dist := editDistance upper kw
    dist <= 2 && dist > 0  -- Allow up to 2 edits, but not exact match
  match candidates with
  | [] => none
  | kw :: _ => some kw

/-- Suggest fixes for common SQL mistakes -/
def suggestFix (context : String) (token : Token) : Option String :=
  match token with
  | .ident s =>
    match suggestKeyword s with
    | some kw => some s!"Did you mean '{kw}'?"
    | none => none
  | .keyword "WHERE" =>
    let containsSubstr (haystack needle : String) : Bool :=
      (haystack.splitOn needle).length > 1
    if containsSubstr context.toUpper "SELECT" && !containsSubstr context.toUpper "FROM" then
      some "Add a FROM clause before WHERE"
    else none
  | _ => none

-- ============================================================================
-- Expression Parser
-- ============================================================================

/-- Check if token is a keyword -/
def isKeyword (kw : String) : Token → Bool
  | .keyword k => k == kw
  | _ => false

/-- Contextual word (e.g. NULLS, FIRST, LAST after an ORDER BY key): matches a
    keyword or an identifier case-insensitively, without reserving the word, so
    columns named `first`/`last` keep working elsewhere. -/
def isWord (w : String) : Token → Bool
  | .keyword k => k.toUpper == w
  | .ident s => s.toUpper == w
  | _ => false

/-- Parse identifier with better error -/
def parseIdent : Parser String := do
  let pt ← Parser.peekPositioned
  match pt.token with
  | .ident s =>
    let _ ← Parser.advance
    return s
  | .keyword s =>
    let _ ← Parser.advance
    return s  -- Allow keywords as identifiers in some contexts
  | .eof =>
    Parser.fail "Expected identifier, but reached end of input"
  | t =>
    Parser.fail s!"Expected identifier, got {t.describe}"

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
/-- `ORDER BY k`, with `k` an integer literal, sorts by the `k`-th SELECT item (1-based), as in
    sqlite, DuckDB and Postgres (#316). The position is resolved here, at parse time, to that
    item's expression, so evaluation and the equivalence theorems never see it. A position out of
    range is an error, as in all three engines. With a `*` item the parser cannot count the
    columns, so positions are left as written. -/
def resolveOrderPositions (items : List SelectItem) (ob : List OrderByItem) :
    Except String (List OrderByItem) :=
  if items.any (fun | .star _ => true | _ => false) then .ok ob
  else ob.mapM fun
    | .mk (.lit (.int k)) dir nulls =>
      match (if 1 ≤ k then items[(k - 1).toNat]? else none) with
      | some (.exprItem e _) => .ok (.mk e dir nulls)
      | _ => .error s!"ORDER BY position {k} is not in the select list (1 to {items.length})"
    | o => .ok o

/-- Whether an ORDER BY key of a `SELECT DISTINCT` appears in its select list
    (row 5): a position, an output name (alias or column name), or an
    expression equal to a selected one. The check is syntactic and lenient:
    with a `*` item every key is accepted, and column names match without
    their qualifier and case-insensitively, so it never rejects a query that
    Postgres accepts. -/
def distinctOrderKeySelected (items : List SelectItem) (e : Expr) : Bool :=
  items.any fun
    | .star _ => true
    | .exprItem e' al =>
      e' == e ||
      (match e with
       | .lit (.int _) => true
       | .col ⟨_, c⟩ =>
         al.any (·.toLower == c.toLower) ||
         (match e' with | .col ⟨_, c'⟩ => c'.toLower == c.toLower | _ => false)
       | _ => false)

mutual

/-- Parse the rest of a subquery body (#218): fold UNION [ALL] / INTERSECT /
    EXCEPT chains left-associatively into SubQuery.compound (mirrors
    parseQueryRest for top-level queries). -/
partial def parseSubQueryRest (left : SubQuery) : Parser SubQuery := do
  match ← parseSetOp with
  | some op =>
    let right ← parseSelectStmt
    parseSubQueryRest (.compound left op (.simple right))
  | none =>
    return left

/-- Parse a subquery body (#218): a SELECT optionally followed by a set-op
    chain. A bare SELECT becomes `.simple`. WITH (CTEs) is rejected inside
    subqueries. -/
partial def parseSubQueryBody : Parser SubQuery := do
  let t ← Parser.peek
  if isKeyword "WITH" t then
    Parser.fail "WITH (CTE) is not supported inside subqueries"
  else
    let first ← parseSelectStmt
    parseSubQueryRest (.simple first)

/-- Parse an OVER clause (#214):
    `OVER ( [PARTITION BY exprs] [ORDER BY items] )`, both parts optional,
    in that order. The OVER keyword itself is consumed here. -/
partial def parseOverClause : Parser WindowSpec := do
  Parser.expect (.keyword "OVER") "Expected OVER"
  Parser.expect .lparen "Expected ( after OVER"
  let t ← Parser.peek
  let partitionBy ←
    if isKeyword "PARTITION" t then
      let _ ← Parser.advance
      Parser.expect (.keyword "BY") "Expected BY after PARTITION"
      Parser.sepBy1 parseExpr (Parser.expect .comma "")
    else
      Parser.pure []
  let t2 ← Parser.peek
  let orderBy ←
    if isKeyword "ORDER" t2 then
      let _ ← Parser.advance
      Parser.expect (.keyword "BY") "Expected BY after ORDER"
      Parser.sepBy1 parseOrderByItem (Parser.expect .comma "")
    else
      Parser.pure []
  Parser.expect .rparen "Expected ) to close OVER clause"
  return .mk partitionBy orderBy

/-- After a fully parsed aggregate call: if OVER follows, build the
    window-function form (`wfn`/`warg`); otherwise return the plain
    aggregate `aggExpr`. DISTINCT inside a window aggregate is rejected
    loudly — the evaluator does not support it (#214). -/
partial def finishAggOrWindow (aggExpr : Expr) (wfn : WindowFunc)
    (warg : Option Expr) (hasDistinct : Bool) : Parser Expr := do
  let t ← Parser.peek
  if isKeyword "OVER" t then
    if hasDistinct then
      Parser.fail "DISTINCT is not supported in window functions"
    else
      let spec ← parseOverClause
      return .windowFn wfn warg spec
  else
    return aggExpr

/-- Parse primary expression (literals, columns, parenthesized, aggregates, EXISTS) -/
partial def parsePrimary : Parser Expr := do
  let t ← Parser.peek
  match t with
  | .intLit n =>
    let _ ← Parser.advance
    return .lit (.int n)
  | .decLit u s =>
    let _ ← Parser.advance
    -- mkDecimal keeps stored decimals canonical (2.50 → decimal 25 1)
    return .lit (Value.mkDecimal u s)
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
    return .lit (.null none)  -- Untyped NULL from parser
  | .keyword "NOT" =>
    let _ ← Parser.advance
    -- Check for NOT EXISTS
    let t2 ← Parser.peek
    if isKeyword "EXISTS" t2 then
      let _ ← Parser.advance
      Parser.expect .lparen "Expected ("
      let sq ← parseSubQueryBody
      Parser.expect .rparen "Expected )"
      return .exists true sq  -- negated EXISTS
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
    let sq ← parseSubQueryBody
    Parser.expect .rparen "Expected )"
    return .exists false sq
  | .lparen =>
    -- Track paren position for better error messages
    let openPt ← Parser.peekPositioned
    let _ ← Parser.advance
    Parser.pushParen
    -- Could be subquery or parenthesized expression
    let t' ← Parser.peek
    if isKeyword "SELECT" t' then
      -- Scalar subquery (possibly a set-op chain, #218)
      let sq ← parseSubQueryBody
      Parser.expectCloseParen openPt.pos
      return .subquery sq
    else
      let e ← parseExpr
      Parser.expectCloseParen openPt.pos
      return e
  | .ident _ | .keyword _ =>
    -- Could be column ref, function call, or aggregate
    let first ← parseIdent
    let t' ← Parser.peek
    if t' == .lparen then
      -- Check if it's an aggregate function
      let mixed ← fun st => .ok (st.config.minMaxMode, st)
      match isAggFunc first mixed with
      | some aggFn =>
        let _ ← Parser.advance
        -- Check for COUNT(*)
        let t'' ← Parser.peek
        if aggFn == .count && t'' == .star then
          let _ ← Parser.advance
          Parser.expect .rparen "Expected )"
          finishAggOrWindow .countStar .count none false
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
            finishAggOrWindow .countStar .count none hasDistinct
          else
            let arg ← parseExpr
            Parser.expect .rparen "Expected )"
            finishAggOrWindow (.agg aggFn (some arg) hasDistinct)
              (aggToWindowFunc aggFn) (some arg) hasDistinct
      | none =>
        match isRankingFunc first with
        | some wfn =>
          -- Ranking window function: zero args, OVER is mandatory (#214) —
          -- without this, ROW_NUMBER() silently misparsed as Expr.func.
          let _ ← Parser.advance
          Parser.expect .rparen s!"Expected ) ({first} takes no arguments)"
          let t'' ← Parser.peek
          if isKeyword "OVER" t'' then
            let spec ← parseOverClause
            return .windowFn wfn none spec
          else
            Parser.fail s!"window function {first} requires OVER clause"
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
        let sq ← parseSubQueryBody
        Parser.expect .rparen "Expected )"
        parsePostfix (.inSubquery e true sq)  -- negated
      else
        let vals ← Parser.sepBy1 parseExpr (Parser.expect .comma "")
        Parser.expect .rparen "Expected )"
        parsePostfix (.inList e true vals)  -- negated
    else if isKeyword "LIKE" t2 then
      -- x NOT LIKE p  ≡  NOT (x LIKE p), with the dialect's LIKE operator
      let _ ← Parser.advance
      let pattern ← parsePrimary
      let likeCase ← fun st => .ok (st.config.likeCase, st)
      let op : BinOp := match likeCase with
        | .sensitive => .like
        | .asciiInsensitive => .likeCI
      parsePostfix (.unaryOp .not (.binOp op e pattern))
    else
      Parser.fail "Expected IN or LIKE after NOT"
  else if isKeyword "IN" t then
    let _ ← Parser.advance
    Parser.expect .lparen "Expected ("
    -- Check if it's a subquery or value list
    let t2 ← Parser.peek
    if isKeyword "SELECT" t2 then
      let sq ← parseSubQueryBody
      Parser.expect .rparen "Expected )"
      parsePostfix (.inSubquery e false sq)
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
    let likeCase ← fun st => .ok (st.config.likeCase, st)
    let op : BinOp := match likeCase with
      | .sensitive => .like
      | .asciiInsensitive => .likeCI
    parsePostfix (.binOp op e pattern)
  else if isKeyword "OVER" t then
    -- A window-eligible call consumes its OVER before postfix parsing, so an
    -- OVER reaching here is attached to a non-window expression. Error loudly
    -- instead of leaving it to be silently swallowed (#214).
    Parser.fail "OVER is only valid immediately after a window or aggregate function call"
  else
    return e

/-- Parse multiplication/division (highest precedence binops) -/
partial def parseMulDiv : Parser Expr := do
  let left ← parsePrimary
  let left' ← parsePostfix left
  parseMulDivRest left'

partial def parseMulDivRest (left : Expr) : Parser Expr := do
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

partial def parseAddSubRest (left : Expr) : Parser Expr := do
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

partial def parseCompRest (left : Expr) : Parser Expr := do
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
    -- Check for table.* (need to peek ahead without consuming the ident)
    let _ ← Parser.advance
    let t' ← Parser.peek
    if t' == .dot then
      let _ ← Parser.advance
      let t'' ← Parser.peek
      if t'' == .star then
        let _ ← Parser.advance
        return .star (some name)
      else
        -- It's table.column, parse as column ref
        let col ← parseIdent
        let e := Expr.col { table := some name, column := col }
        let e' ← parsePostfix e
        let e'' ← continueExprFrom e'
        let alias ← parseAlias
        return .exprItem e'' alias
    else if t' == .lparen then
      -- Function call or aggregate — check for aggregate first
      let mixed ← fun st => .ok (st.config.minMaxMode, st)
      match isAggFunc name mixed with
      | some aggFn =>
        let _ ← Parser.advance
        let t'' ← Parser.peek
        if aggFn == .count && t'' == .star then
          let _ ← Parser.advance
          Parser.expect .rparen "Expected )"
          let e ← finishAggOrWindow .countStar .count none false
          let e' ← parsePostfix e
          let e'' ← continueExprFrom e'
          let alias ← parseAlias
          return .exprItem e'' alias
        else
          let hasDistinct ←
            if isKeyword "DISTINCT" t'' then
              let _ ← Parser.advance
              Parser.pure true
            else
              Parser.pure false
          let t''' ← Parser.peek
          if t''' == .star then
            let _ ← Parser.advance
            Parser.expect .rparen "Expected )"
            let e ← finishAggOrWindow .countStar .count none hasDistinct
            let e' ← parsePostfix e
            let e'' ← continueExprFrom e'
            let alias ← parseAlias
            return .exprItem e'' alias
          else
            let arg ← parseExpr
            Parser.expect .rparen "Expected )"
            let e ← finishAggOrWindow (.agg aggFn (some arg) hasDistinct)
              (aggToWindowFunc aggFn) (some arg) hasDistinct
            let e' ← parsePostfix e
            let e'' ← continueExprFrom e'
            let alias ← parseAlias
            return .exprItem e'' alias
      | none =>
        -- Regular function call
        let _ ← Parser.advance
        let args ← Parser.sepBy parseExpr (Parser.expect .comma "")
        Parser.expect .rparen "Expected )"
        let e := Expr.func name args
        let e' ← parsePostfix e
        let e'' ← continueExprFrom e'
        let alias ← parseAlias
        return .exprItem e'' alias
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

  -- Continue parsing an expression from an already-parsed postfix expression
  -- (#228): resume the precedence chain (mul/div/mod → add/sub/concat →
  -- comparison) instead of punting and leaving trailing operators — the old
  -- "just return what we have" comment relied on the top-level parser
  -- silently discarding the rest of the statement.
  continueExprFrom (left : Expr) : Parser Expr := do
    let l1 ← parseMulDivRest left
    let l2 ← parseAddSubRest l1
    parseCompRest l2

/-- Parse the remaining `, item` parts of a SELECT list without backtracking
    (#214): if an item after a comma fails to parse, the error propagates
    instead of the list being silently truncated (sepBy would backtrack,
    leaving the tail to be dropped by the top-level parser). -/
partial def parseSelectItemsRest (acc : List SelectItem) : Parser (List SelectItem) := do
  let t ← Parser.peek
  if t == .comma then
    let _ ← Parser.advance
    let item ← parseSelectItem
    parseSelectItemsRest (acc ++ [item])
  else
    return acc

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
    -- Subquery in FROM clause (possibly a set-op chain, #218)
    let _ ← Parser.advance
    let sq ← parseSubQueryBody
    Parser.expect .rparen "Expected )"
    -- Optional alias (#218): `AS ident`, a bare identifier, or nothing.
    -- Spider writes anonymous FROM subqueries like
    -- `SELECT COUNT(*) FROM (SELECT ... INTERSECT SELECT ...)`; the alias
    -- is not used by evaluation, so anonymous subqueries get "sub".
    let t' ← Parser.peek
    if isKeyword "AS" t' then
      let _ ← Parser.advance
      let alias ← parseIdent
      return .subquery sq alias
    else
      match t' with
      | .ident _ =>
        let alias ← parseIdent
        return .subquery sq alias
      | _ => return .subquery sq "sub"
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
      -- ON is optional for non-cross joins too (Spider/SQLite write bare
      -- `A JOIN B WHERE ...` meaning a cross product); the AST and evaluator
      -- already model the missing condition as `none`.
      let on_ ← if jtype == .cross then Parser.pure none else do
        let t ← Parser.peek
        if isKeyword "ON" t then
          let _ ← Parser.advance
          some <$> parseExpr
        else
          Parser.pure none
      parseJoins (.join left jtype right on_)
    else if t == .comma then
      -- Comma-separated FROM list = implicit cross join (#228; previously
      -- the tail after the comma was silently discarded)
      let _ ← Parser.advance
      let right ← parseFromSource
      parseJoins (.join left .cross right none)
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
  -- Optional NULLS FIRST / NULLS LAST; otherwise the configured engine rule.
  let t ← Parser.peek
  let nulls ←
    if isWord "NULLS" t then
      let _ ← Parser.advance
      let t2 ← Parser.peek
      if isWord "FIRST" t2 then
        let _ ← Parser.advance
        Parser.pure NullsOrder.first
      else if isWord "LAST" t2 then
        let _ ← Parser.advance
        Parser.pure NullsOrder.last
      else
        Parser.fail "Expected FIRST or LAST after NULLS"
    else
      fun st => .ok (st.config.nullOrdering.resolve dir, st)
  return .mk expr dir nulls

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

  -- Select items. Parsed without backtracking: a failure in any item after a
  -- comma is a loud error, not a silent truncation of the statement (#214).
  let firstItem ← parseSelectItem
  let items ← parseSelectItemsRest [firstItem]

  -- A leftover OVER here is attached to something that isn't a window or
  -- aggregate call (e.g. after a bare column); previously the whole tail
  -- `OVER (...) FROM ...` was silently swallowed (#214).
  let tOver ← Parser.peek
  if isKeyword "OVER" tOver then
    Parser.fail "OVER is only valid immediately after a window or aggregate function call"

  -- FROM clause (optional) - with better error detection
  let t1 ← Parser.peek
  let fromClause ←
    if isKeyword "FROM" t1 then
      let _ ← Parser.advance
      some <$> parseFromClause
    else if isKeyword "WHERE" t1 || isKeyword "GROUP" t1 ||
            isKeyword "HAVING" t1 || isKeyword "ORDER" t1 then
      -- Common mistake: forgot FROM before WHERE/GROUP BY/etc.
      Parser.failWithSuggestion
        s!"Missing FROM clause before {(match t1 with | .keyword k => k | _ => "clause")}"
        "Add 'FROM table_name' before this clause"
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

  -- Catch-all (#214): an unconsumed OVER after any clause (e.g. `FROM t
  -- OVER (...)`) must be a loud error — the top-level parser ignores
  -- leftover tokens, so without this the tail would vanish silently.
  let tEnd ← Parser.peek
  if isKeyword "OVER" tEnd then
    Parser.fail "OVER is only valid immediately after a window or aggregate function call"

  -- #316: `ORDER BY k` names the k-th SELECT item.
  let orderBy ← match resolveOrderPositions items orderBy with
    | .ok ob => Parser.pure ob
    | .error msg => Parser.fail msg

  -- Row 5: DISTINCT with an ORDER BY key outside the select list, per dialect.
  let dob ← fun st => .ok (st.config.distinctOrderBy, st)
  if distinct && dob == .reject &&
      orderBy.any (fun | .mk e _ _ => !distinctOrderKeySelected items e) then
    Parser.fail "for SELECT DISTINCT, ORDER BY expressions must appear in select list"

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

/-- Parse query rest (handles UNION, INTERSECT, EXCEPT) -/
partial def parseQueryRest (left : Query) : Parser Query := do
  match ← parseSetOp with
  | some op =>
    let right ← parseSelectStmt
    parseQueryRest (.compound left op (.simple right))
  | none =>
    return left

/-- Parse a query body (SELECT with optional set operations, but not WITH) -/
partial def parseQueryBody : Parser Query := do
  let first ← parseSelectStmt
  parseQueryRest (.simple first)

/-- Parse a single CTE: name AS (query) -/
partial def parseCTEDef (isRecursive : Bool) : Parser CTEDef := do
  let name ← parseIdent
  Parser.expect (.keyword "AS") "Expected AS"
  Parser.expect .lparen "Expected ("
  let query ← parseQueryBody  -- Now parses compound queries (UNION, etc.)
  Parser.expect .rparen "Expected )"
  return .mk name query isRecursive

/-- Parse comma-separated list of CTEs -/
partial def parseCTEList (isRecursive : Bool) : Parser (List CTEDef) :=
  Parser.sepBy1 (parseCTEDef isRecursive) (Parser.expect .comma "")

/-- Parse a query (SELECT with optional set operations, or WITH clause) -/
partial def parseQuery : Parser Query := do
  let t ← Parser.peek
  if isKeyword "WITH" t then
    let _ ← Parser.advance
    -- Check for RECURSIVE keyword
    let t2 ← Parser.peek
    let isRecursive := isKeyword "RECURSIVE" t2
    if isRecursive then
      let _ ← Parser.advance
    let ctes ← parseCTEList isRecursive
    let mainQuery ← parseQueryBody
    return .withCTE ctes mainQuery
  else
    parseQueryBody

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
  if isKeyword "SELECT" t || isKeyword "WITH" t then
    .query <$> parseQuery
  else if isKeyword "INSERT" t then
    .insert <$> parseInsert
  else if isKeyword "UPDATE" t then
    .update <$> parseUpdate
  else if isKeyword "DELETE" t then
    .delete <$> parseDelete
  else
    Parser.fail "Expected SELECT, WITH, INSERT, UPDATE, or DELETE"

end -- mutual

/-- Require that parsing consumed the whole input (#228): leftover tokens
    beyond a trailing semicolon are a loud error, never silently discarded —
    the enabler of the OVER-clause and similar swallow bugs. -/
private def requireConsumed (state : ParseState) : Except String Unit :=
  let rest := match state.tokens with
    | ⟨.semicolon, _, _⟩ :: rest' => rest'
    | rest' => rest'
  match rest with
  | [] => Except.ok ()
  | pt :: _ =>
    Except.error s!"Parse error at line {pt.pos.line}, column {pt.pos.column}: Unexpected trailing input starting with {pt.token.describe}"

/-- Parse a statement for a target `dialect` (default: `standard`). `config`
    overrides individual choices, e.g.
    `parse sql (config := { Dialect.sqlite.config with nullOrdering := .nullsLargest })`. -/
def parse (input : String) (dialect : Dialect := defaultDialect)
    (config : DialectConfig := dialect.config) : Except String Stmt := do
  let tokens ← (tokenize input).mapError toString
  let state : ParseState :=
    { tokens := tokens, pos := 0, input := input, parenStack := [], config := config }
  match parseStmt state with
  | .error e => Except.error s!"Parse error at line {e.line}, column {e.column}: {e.message}"
  | .ok (stmt, state') => do
    requireConsumed state'
    Except.ok stmt

/-- Parse SELECT statement specifically -/
def parseSelectStr (input : String) (dialect : Dialect := defaultDialect)
    (config : DialectConfig := dialect.config) : Except String SelectStmt := do
  let tokens ← (tokenize input).mapError toString
  let state : ParseState :=
    { tokens := tokens, pos := 0, input := input, parenStack := [], config := config }
  match parseSelect state with
  | .error e => Except.error s!"Parse error at line {e.line}, column {e.column}: {e.message}"
  | .ok (stmt, state') => do
    requireConsumed state'
    Except.ok stmt

end SqlEquiv
