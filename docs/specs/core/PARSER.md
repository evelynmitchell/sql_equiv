# SQL Parser

## Cleanroom Specification

**Module:** `SqlEquiv/Parser.lean`
**Status:** Implemented ✅
**Lines:** 1-1354

---

## 1. Intended Function

The SQL parser transforms SQL text into Abstract Syntax Trees (ASTs). It uses a hand-rolled recursive descent parser with a separate tokenization phase.

### 1.1 Black-Box Specification

```
parse : String → Except String Stmt
  Parse any SQL statement (SELECT, INSERT, UPDATE, DELETE)

parseSelectStr : String → Except String SelectStmt
  Parse a SELECT statement specifically
```

### 1.2 Architecture

```
SQL Text  →  Tokenizer  →  List Token  →  Parser  →  AST

           tokenize()          parseStmt()
            ↓                      ↓
         Token list          Recursive descent
         with positions      with error recovery
```

---

## 2. Tokenizer

### 2.1 Token Types

```lean
inductive Token where
  | keyword  : String → Token    -- SELECT, FROM, WHERE, etc.
  | ident    : String → Token    -- identifiers
  | intLit   : Int → Token       -- integer literals
  | strLit   : String → Token    -- string literals (single-quoted)
  | op       : String → Token    -- operators: +, -, *, /, =, <>, etc.
  | lparen   : Token             -- (
  | rparen   : Token             -- )
  | comma    : Token             -- ,
  | dot      : Token             -- .
  | semicolon: Token             -- ;
  | star     : Token             -- * (SELECT ALL)
  | eof      : Token             -- end of input
```

### 2.2 Positioned Token

```lean
structure PositionedToken where
  token : Token
  pos   : SourcePos        -- line, column
  text  : String           -- original text
```

### 2.3 Tokenization Rules

| Input Pattern | Token Type |
|---------------|------------|
| Whitespace | Skipped |
| `(`, `)` | lparen, rparen |
| `,`, `.`, `;` | comma, dot, semicolon |
| `*` | star |
| `+`, `-`, `/`, `%` | op |
| `=` | op "=" |
| `<>`, `!=` | op "<>" |
| `<`, `<=`, `>`, `>=` | op |
| `\|\|` | op "\|\|" (concat) |
| `'string'` | strLit |
| `123` | intLit |
| `word` | keyword (if in list) or ident |

### 2.4 SQL Keywords

```lean
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
```

Keywords are case-insensitive (converted to uppercase for matching).

### 2.5 String Literals

- Delimited by single quotes: `'hello'`
- Escape single quote by doubling: `'it''s'` → `it's`
- Unterminated strings produce error with position

---

## 3. Parser Monad

### 3.1 State

```lean
structure ParseState where
  tokens     : List PositionedToken  -- remaining tokens
  pos        : Nat                   -- current position index
  input      : String                -- original input for context
  parenStack : List SourcePos        -- track open parentheses
```

### 3.2 Error Type

```lean
structure ParseError where
  message    : String
  line       : Nat
  column     : Nat
  context    : Option String    -- surrounding text
  suggestion : Option String    -- suggested fix
```

### 3.3 Parser Type

```lean
abbrev Parser (α : Type) := ParseState → Except ParseError (α × ParseState)
```

### 3.4 Combinators

| Combinator | Purpose |
|------------|---------|
| `pure a` | Return value without consuming |
| `bind p f` | Sequence parsers |
| `peek` | Look at current token |
| `advance` | Consume and return token |
| `expect tok msg` | Require specific token |
| `tryP p` | Try parser, backtrack on failure |
| `many p` | Zero or more |
| `many1 p` | One or more |
| `sepBy p sep` | List separated by sep |
| `sepBy1 p sep` | Non-empty separated list |

---

## 4. Expression Parser

### 4.1 Precedence Levels

```
Lowest    OR
  ↑       AND
  ↑       NOT (unary)
  ↑       =, <>, <, <=, >, >=, IS, IN, BETWEEN, LIKE
  ↑       +, -, ||
  ↑       *, /, %
Highest   Unary -, function calls, parentheses
```

### 4.2 Grammar

```
expr      := or_expr
or_expr   := and_expr (OR and_expr)*
and_expr  := comp_expr (AND comp_expr)*
comp_expr := add_expr (comp_op add_expr)?
add_expr  := mul_expr (('+' | '-' | '||') mul_expr)*
mul_expr  := unary (('*' | '/' | '%') unary)*
unary     := ('-' | NOT)? postfix
postfix   := primary (IS NULL | IS NOT NULL | IN (...) | BETWEEN ... | LIKE ...)*
primary   := literal | column_ref | func_call | aggregate | CASE | EXISTS | '(' expr ')'
```

### 4.3 Primary Expressions

| Syntax | Parser Action |
|--------|---------------|
| `123` | `Expr.lit (Value.int 123)` |
| `'str'` | `Expr.lit (Value.string "str")` |
| `TRUE/FALSE` | `Expr.lit (Value.bool _)` |
| `NULL` | `Expr.lit (Value.null none)` |
| `col` | `Expr.col {table: none, column: col}` |
| `t.col` | `Expr.col {table: some t, column: col}` |
| `func(args)` | `Expr.func "func" args` |
| `COUNT(*)` | `Expr.countStar` |
| `SUM(x)` | `Expr.agg .sum (some x) false` |
| `(SELECT...)` | `Expr.subquery sel` |
| `EXISTS(...)` | `Expr.exists false sel` |
| `CASE...END` | `Expr.case branches else_` |

### 4.4 Postfix Operators

| Syntax | Parser Action |
|--------|---------------|
| `e IS NULL` | `Expr.unaryOp .isNull e` |
| `e IS NOT NULL` | `Expr.unaryOp .isNotNull e` |
| `e IN (a,b,c)` | `Expr.inList e false [a,b,c]` |
| `e NOT IN (...)` | `Expr.inList e true [...]` |
| `e IN (SELECT...)` | `Expr.inSubquery e false sel` |
| `e BETWEEN lo AND hi` | `Expr.between e lo hi` |
| `e LIKE pat` | `Expr.binOp .like e pat` |

---

## 5. SELECT Statement Parser

### 5.1 Grammar

```
select_stmt := SELECT [DISTINCT] select_items
               [FROM from_clause]
               [WHERE expr]
               [GROUP BY expr_list]
               [HAVING expr]
               [ORDER BY order_items]
               [LIMIT int]
               [OFFSET int]
```

### 5.2 SELECT Items

```
select_item := '*'
             | table '.' '*'
             | expr [AS alias]
             | expr alias      -- alias without AS
```

### 5.3 FROM Clause

```
from_clause := from_source (join_clause)*

from_source := table_ref
             | '(' select_stmt ')' [AS] alias

table_ref := name [[AS] alias]

join_clause := join_type from_source [ON expr]

join_type := [INNER] JOIN
           | LEFT [OUTER] JOIN
           | RIGHT [OUTER] JOIN
           | FULL [OUTER] JOIN
           | CROSS JOIN
```

### 5.4 ORDER BY

```
order_item := expr [ASC | DESC]
```

Default direction is ASC.

---

## 6. Query Parser (Set Operations)

### 6.1 Grammar

```
query := WITH [RECURSIVE] cte_list query_body
       | query_body

query_body := select_stmt (set_op select_stmt)*

set_op := UNION [ALL]
        | INTERSECT
        | EXCEPT

cte_list := cte_def (',' cte_def)*

cte_def := name AS '(' query_body ')'
```

### 6.2 CTE Parsing

```lean
partial def parseCTEDef (isRecursive : Bool) : Parser CTEDef := do
  let name ← parseIdent
  Parser.expect (.keyword "AS") "Expected AS"
  Parser.expect .lparen "Expected ("
  let query ← parseQueryBody
  Parser.expect .rparen "Expected )"
  return .mk name query isRecursive
```

---

## 7. DML Statement Parsers

### 7.1 INSERT

```
insert := INSERT INTO table ['(' columns ')']
          (VALUES rows | select_stmt)

rows := '(' expr_list ')' (',' '(' expr_list ')')*
```

### 7.2 UPDATE

```
update := UPDATE table SET assignments [WHERE expr]

assignments := assignment (',' assignment)*

assignment := column '=' expr
```

### 7.3 DELETE

```
delete := DELETE FROM table [WHERE expr]
```

---

## 8. Error Handling

### 8.1 Error Context

Each error includes:
- Message describing the problem
- Line and column number
- Surrounding text context
- Optional suggestion for fix

### 8.2 Common Error Detection

| Error | Detection | Suggestion |
|-------|-----------|------------|
| Missing FROM | WHERE before FROM | "Add FROM clause" |
| Misspelled keyword | Edit distance check | "Did you mean X?" |
| Unclosed paren | Paren stack tracking | Position of opening paren |
| Unterminated string | Quote tracking | Position where string started |

### 8.3 Edit Distance

```lean
def suggestKeyword (word : String) : Option String :=
  let candidates := sqlKeywords.filter fun kw =>
    editDistance word.toUpper kw <= 2
  candidates.head?
```

Suggests keywords within 2 edits of the misspelled word.

---

## 9. Correctness Conditions

### 9.1 Completeness

```lean
-- Every valid SQL string should parse
∀ sql, isValidSQL sql → parse sql ≠ error
```

### 9.2 Soundness

```lean
-- Parse result should match SQL semantics
∀ sql ast, parse sql = ok ast →
  eval ast = interpret sql (using reference semantics)
```

### 9.3 Roundtrip

```lean
-- Parse → Pretty → Parse should be stable
∀ ast, parse (pretty ast) = ok ast'
  → ast ≈ ast'  -- structurally equivalent
```

### 9.4 Error Position Accuracy

```lean
-- Error position should point to actual problem
∀ sql pos, parseError sql pos →
  sql[pos] is related to the error
```

---

## 10. Testing Strategy

### 10.1 Tokenizer Tests

```lean
-- Basic tokens
#guard tokenize "SELECT * FROM t" = ok [
  keyword "SELECT", star, keyword "FROM", ident "t"
]

-- String literals
#guard tokenize "'hello'" = ok [strLit "hello"]
#guard tokenize "'it''s'" = ok [strLit "it's"]

-- Multi-char operators
#guard tokenize "a <> b" = ok [ident "a", op "<>", ident "b"]
#guard tokenize "a || b" = ok [ident "a", op "||", ident "b"]
```

### 10.2 Expression Tests

```lean
-- Precedence
#guard parse "1 + 2 * 3" = ok (add 1 (mul 2 3))  -- not (mul (add 1 2) 3)

-- Associativity
#guard parse "1 - 2 - 3" = ok (sub (sub 1 2) 3)  -- left-associative
```

### 10.3 SELECT Tests

```lean
-- Simple SELECT
#guard parse "SELECT * FROM t" = ok (expectedAST)

-- With JOIN
#guard parse "SELECT * FROM a JOIN b ON a.x = b.x" = ok (expectedAST)

-- With subquery
#guard parse "SELECT * FROM (SELECT 1) AS s" = ok (expectedAST)
```

### 10.4 Error Tests

```lean
-- Missing FROM
#guard parse "SELECT * WHERE x = 1" = error (contains "FROM")

-- Unclosed paren
#guard parse "SELECT (1 + 2" = error (contains ")")

-- Unknown token
#guard parse "SELECT @x" = error (contains "Unexpected")
```

---

## 11. Integration Points

### 11.1 With AST

Parser produces all AST types defined in `Ast.lean`.

### 11.2 With Pretty Printer

Roundtrip: `parse(pretty(ast))` should reproduce equivalent AST.

### 11.3 With Evaluator

Parsed AST can be directly evaluated by `Semantics.lean`.

---

## 12. Design Decisions

### 12.1 Recursive Descent

**Choice:** Hand-written recursive descent parser

**Rationale:**
- Full control over error messages
- Easy to extend for new SQL features
- No parser generator dependency
- Better integration with Lean's type system

### 12.2 Mutual Recursion

Expressions and SELECT statements are mutually recursive:
- Expressions can contain subqueries
- SELECT items contain expressions

Handled with Lean's `mutual` block and `partial` keyword.

### 12.3 Keywords as Identifiers

Some keywords are allowed as identifiers in certain contexts:
- Column names can shadow keywords
- Handled by falling back to keyword text as identifier

### 12.4 Optional AS

Both `SELECT x AS y` and `SELECT x y` are supported for aliases.

---

## 13. Limitations

### 13.1 Not Supported

- `--` comments (line comments)
- `/* */` comments (block comments)
- Hexadecimal literals
- Unicode identifiers
- Quoted identifiers (`"column name"`)
- Floating point literals
- Scientific notation
- Date/time literals

### 13.2 Parser Combinator Trade-offs

- `tryP` backtracks fully (may hide errors)
- No packrat memoization (acceptable for SQL sizes)
- Left-recursion avoided by iterative loops

---

## 14. References

- ISO/IEC 9075 SQL Standard, Section 5 (Lexical elements)
- ISO/IEC 9075 SQL Standard, Section 6-7 (Expressions and queries)
- Aho, Lam, Sethi, Ullman, "Compilers: Principles, Techniques, and Tools"
