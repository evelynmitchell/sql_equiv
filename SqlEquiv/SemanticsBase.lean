/-
  SQL Semantics: Base Types and Operator Evaluators

  Core types (Row, Table, Database), value operations, and operator evaluators
  that are used by both the main evaluator (Semantics.lean) and the non-partial
  core evaluators (SemanticsCore.lean).
-/
import SqlEquiv.Ast

namespace SqlEquiv

-- ============================================================================
-- Core Types
-- ============================================================================

/-- A row is a mapping from column names to values -/
abbrev Row := List (String × Value)

/-- A table is a list of rows (bag semantics for now) -/
abbrev Table := List Row

/-- A database maps table names to tables -/
abbrev Database := String → Table

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Enumerate a list with indices -/
def listEnumerate {α : Type} (xs : List α) : List (Nat × α) :=
  go 0 xs
where
  go (i : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (i, x) :: go (i + 1) xs

-- ============================================================================
-- Row Operations
-- ============================================================================

/-- Case-insensitive key lookup. SQL identifiers are case-insensitive
    (`country` resolves a column stored as `Country`), so all row lookups
    compare case-folded keys. First match wins: two columns whose names
    differ only by case collide deliberately, the same shadowing
    `List.lookup` already gave exact-duplicate keys.
    Structured like `List.lookup` so lookup lemmas port directly. -/
def Row.lookupCI : Row → String → Option Value
  | [], _ => none
  | (k, v) :: rest, key =>
    if k.toLower == key.toLower then some v else Row.lookupCI rest key

/-- Get value from row by column name -/
def Row.get (row : Row) (col : String) : Option Value :=
  row.lookupCI col

/-- Does key `k` already carry qualifier `q` (`k` starts with `q.`)? -/
def hasQualifier (q k : String) : Bool := (q ++ ".").toList.isPrefixOf k.toList

theorem hasQualifier_mk (q c : String) : hasQualifier q s!"{q}.{c}" = true := by
  unfold hasQualifier
  rw [List.isPrefixOf_iff_prefix]
  simp only [String.toList_append, toString]
  exact ⟨c.toList, by simp⟩

/-- Key of a derived-table column under alias `alias` (#257): a key that
    already carries the qualifier is kept; otherwise its column part (after
    the last `.`, or the whole key) is qualified by `alias`. So
    `(SELECT name … ) AS x` exposes `x.name`, `(SELECT * FROM users) AS x`
    turns `users.name` into `x.name`, and a derived table named after the
    table it wraps renames nothing. -/
def requalifyKey (alias k : String) : String :=
  if hasQualifier alias k then k else s!"{alias}.{(k.splitOn ".").getLastD k}"

/-- Re-qualify every key of a derived-table row by the table's alias. -/
def requalifyRow (alias : String) (row : Row) : Row :=
  row.map fun (k, v) => (requalifyKey alias k, v)

theorem requalifyKey_mk (q c : String) : requalifyKey q s!"{q}.{c}" = s!"{q}.{c}" := by
  simp [requalifyKey, hasQualifier_mk]

/-- Get value from row by qualified column name -/
def Row.getQualified (row : Row) (table : Option String) (col : String) : Option Value :=
  match table with
  | some t => row.lookupCI s!"{t}.{col}"
  | none =>
    -- First entry, in row order, whose key is `col` or ends in `.col`. A
    -- single pass, so that row order decides: correlated subquery rows are
    -- `inner ++ outer`, and an unqualified outer key (from a derived table)
    -- must not beat a qualified inner key (innermost scope wins, #253).
    match row.find? (fun (k, _) =>
        k.toLower == col.toLower || k.toLower.endsWith s!".{col.toLower}") with
    | some (_, v) => some v
    | none => none

-- ============================================================================
-- Value Operations
-- ============================================================================

/-- Compare two values for equality -/
def Value.eq : Value → Value → Option Bool
  | .null _, _ => none  -- NULL = anything is NULL
  | _, .null _ => none
  | .int a, .int b => some (a == b)
  | .string a, .string b => some (a == b)
  | .bool a, .bool b => some (a == b)
  -- Decimal: compare scale-aligned unscaled values (1.0 = 1.00)
  | .decimal u1 s1, .decimal u2 s2 =>
    some (u1 * 10 ^ (max s1 s2 - s1) == u2 * 10 ^ (max s1 s2 - s2))
  -- int↔decimal promotion (#201): 1 = 1.0 is TRUE, not a type error
  | .int a, .decimal u s => some (a * 10 ^ s == u)
  | .decimal u s, .int b => some (u == b * 10 ^ s)
  | _, _ => none  -- type mismatch

/-- Compare two values for ordering -/
def Value.compare : Value → Value → Option Ordering
  | .null _, _ => none
  | _, .null _ => none
  | .int a, .int b => some (Ord.compare a b)
  | .string a, .string b => some (Ord.compare a b)
  -- Decimal: compare scale-aligned unscaled values
  | .decimal u1 s1, .decimal u2 s2 =>
    some (Ord.compare (u1 * 10 ^ (max s1 s2 - s1)) (u2 * 10 ^ (max s1 s2 - s2)))
  -- int↔decimal promotion (#201)
  | .int a, .decimal u s => some (Ord.compare (a * 10 ^ s) u)
  | .decimal u s, .int b => some (Ord.compare u (b * 10 ^ s))
  | _, _ => none

/-- Convert value to boolean for WHERE clauses -/
def Value.toBool : Value → Option Bool
  | .bool b => some b
  | .null _ => none
  | .int n => some (n != 0)
  | .decimal u _ => some (u != 0)
  | _ => none

-- ============================================================================
-- Numeric Aggregation Helpers (#201)
-- ============================================================================

/-- Numeric view for aggregation: ints promote to scale-0 scaled integers. -/
def Value.toScaled? : Value → Option (Int × Nat)
  | .int n => some (n, 0)
  | .decimal u s => some (u, s)
  | _ => none

/-- True if any value is a decimal — drives the aggregate result type
    (SUM over a decimal column is decimal; over ints stays int). -/
def anyDecimal (vs : List Value) : Bool :=
  vs.any fun | .decimal _ _ => true | _ => false

/-- Scale-aligned sum of the numeric values in the list (non-numerics are
    ignored, matching the previous int-only behavior). Empty sums to (0, 0). -/
def sumScaled (vs : List Value) : Int × Nat :=
  (vs.filterMap Value.toScaled?).foldl
    (fun a b => (a.1 * 10 ^ (max a.2 b.2 - a.2) + b.1 * 10 ^ (max a.2 b.2 - b.2),
                 max a.2 b.2))
    (0, 0)

/-- Number of numeric values (the AVG denominator). -/
def countNumeric (vs : List Value) : Nat :=
  (vs.filterMap Value.toScaled?).length

/-- SUM over numerics: decimal iff any input was decimal. Empty gives int 0;
    callers that want SQL's NULL-on-empty guard with `countNumeric`. -/
def sumNumeric (vs : List Value) : Value :=
  if anyDecimal vs then Value.mkDecimal (sumScaled vs).1 (sumScaled vs).2
  else .int (sumScaled vs).1

/-- AVG over numerics (truncating division, consistent with the existing
    integer AVG); none when there are no numeric inputs. -/
def avgNumeric (vs : List Value) : Option Value :=
  let n := countNumeric vs
  if n == 0 then none
  else if anyDecimal vs then
    some (Value.mkDecimal ((sumScaled vs).1.tdiv (Int.ofNat n)) (sumScaled vs).2)
  else some (.int ((sumScaled vs).1.tdiv (Int.ofNat n)))

/-- Least (`wantMax = false`) or greatest value of a list under `Value.compare`;
    returns the original value (canonical form preserved). -/
def extremeValue (wantMax : Bool) (vs : List Value) : Option Value :=
  vs.foldl (fun acc v =>
    match acc with
    | none => some v
    | some m =>
      if Value.compare m v == some (if wantMax then .lt else .gt) then some v else acc) none

/-- MIN/MAX aggregate result (#256, #261). NULLs and values of other types
    are skipped. Numerics compare scale-aware, strings by code point.
    Booleans follow `mode.bools` (registry row 14): `.error` makes any boolean
    an error; `.asInt` reads them as 1/0; `.ordered` gives a boolean result
    (false < true) when the input is only booleans, else reads them as 1/0.
    Input mixing numbers and strings follows `mode.mixed` (row 13): `.error`
    is an error, `.typeClass` orders numbers before strings (sqlite), so MAX is
    the greatest string and MIN the least number. An error is `none`; no
    eligible input gives NULL. -/
def minMaxAgg (mode : MinMaxMode) (wantMax : Bool) (vs : List Value) : Option Value :=
  let bools := vs.filter fun v => match v with | .bool _ => true | _ => false
  let isNum := fun v => (Value.toScaled? v).isSome
  let isStr := fun v => match v with | .string _ => true | _ => false
  let others := vs.filter fun v => isNum v || isStr v
  let asInts := bools.map fun v => match v with
    | .bool b => Value.int (if b then 1 else 0)
    | v => v
  let resolved : Option (List Value) :=
    if bools.isEmpty then some others
    else match mode.bools with
      | .error => none
      | .asInt => some (others ++ asInts)
      | .ordered => if others.isEmpty then some bools else some (others ++ asInts)
  resolved.bind fun vs' =>
    if vs'.all (fun v => match v with | .bool _ => true | _ => false) && !vs'.isEmpty then
      -- booleans only (`.ordered`): false < true
      let anyTrue := vs'.any (· == .bool true)
      let allTrue := vs'.all (· == .bool true)
      some (.bool (if wantMax then anyTrue else allTrue))
    else
      let nums := vs'.filter isNum
      let strs := vs'.filter isStr
      let pool : Option (List Value) :=
        if nums.isEmpty then some strs
        else if strs.isEmpty then some nums
        else match mode.mixed with
          | .error => none
          | .typeClass => some (if wantMax then strs else nums)
      pool.map fun p => (extremeValue wantMax p).getD (.null none)


/-- The MIN/MAX calls of an expression outside subqueries and window functions, as
    `(wantMax, mode, argument, distinct)`: the positions `hasAggregate` looks at. -/
def minMaxCalls : Expr → List (Bool × MinMaxMode × Option Expr × Bool)
  | .agg (.min m) a d => [(false, m, a, d)]
  | .agg (.max m) a d => [(true, m, a, d)]
  | .binOp _ l r => minMaxCalls l ++ minMaxCalls r
  | .unaryOp _ e => minMaxCalls e
  | .func _ args => minMaxCallsList args
  | .case branches else_ => minMaxCallsPairs branches ++ minMaxCallsOpt else_
  | .inList e _ vals => minMaxCalls e ++ minMaxCallsList vals
  | .between e lo hi => minMaxCalls e ++ minMaxCalls lo ++ minMaxCalls hi
  | _ => []
where
  minMaxCallsList : List Expr → List (Bool × MinMaxMode × Option Expr × Bool)
    | [] => []
    | e :: es => minMaxCalls e ++ minMaxCallsList es
  minMaxCallsPairs : List (Expr × Expr) → List (Bool × MinMaxMode × Option Expr × Bool)
    | [] => []
    | (c, r) :: ps => minMaxCalls c ++ minMaxCalls r ++ minMaxCallsPairs ps
  minMaxCallsOpt : Option Expr → List (Bool × MinMaxMode × Option Expr × Bool)
    | none => []
    | some e => minMaxCalls e

/-- The MIN/MAX calls of a SELECT list and its HAVING clause. -/
def selectMinMaxCalls (items : List SelectItem) (having : Option Expr) :
    List (Bool × MinMaxMode × Option Expr × Bool) :=
  items.flatMap (fun | .exprItem e _ => minMaxCalls e | .star _ => []) ++
    minMaxCalls.minMaxCallsOpt having

/-- The row a group's bare columns read (registry T9). With exactly one MIN/MAX call, not
    DISTINCT, over a column, whose mode has `bareRow` (the sqlite dialect): the first row where
    the column equals the extreme, or the last row when there is no extreme (every value NULL),
    as sqlite does. Otherwise the group's first row (also for MIN/MAX of a non-column
    expression, where the typed core follows sqlite and `SqlEquiv` does not). `none` exactly for
    an empty group. -/
def bareSampleRow (argEval : Row → Expr → Option Value)
    (calls : List (Bool × MinMaxMode × Option Expr × Bool)) (rows : Table) : Option Row :=
  match calls with
  | [(wantMax, m, some (.col c), false)] =>
    if m.bareRow then
      match minMaxAgg m wantMax (rows.filterMap fun r => argEval r (.col c)) with
      | some (.null _) | none => rows.getLast?
      | some v => (rows.find? fun r => argEval r (.col c) == some v).or rows.head?
    else rows.head?
  | _ => rows.head?

theorem bareSampleRow_eq_none_iff (argEval : Row → Expr → Option Value)
    (calls : List (Bool × MinMaxMode × Option Expr × Bool)) (rows : Table) :
    bareSampleRow argEval calls rows = none ↔ rows = [] := by
  unfold bareSampleRow
  split
  · split
    · split
      · simp
      · simp
      · cases rows <;> simp
    · simp
  · simp

/-- `bareSampleRow` reads its argument evaluator only on column references. -/
theorem bareSampleRow_congr {argA argB : Row → Expr → Option Value}
    (h : ∀ r c, argA r (.col c) = argB r (.col c))
    (calls : List (Bool × MinMaxMode × Option Expr × Bool)) (rows : Table) :
    bareSampleRow argA calls rows = bareSampleRow argB calls rows := by
  unfold bareSampleRow
  split <;> simp only [h]

-- ============================================================================
-- Expression Evaluation Helper Functions (standalone)
-- ============================================================================

/-! ### LIKE (#323)

`s LIKE p`: `%` matches any sequence of characters, `_` exactly one, and any other character
itself. The matcher is an automaton whose states are the pattern suffixes still to match; it is
structural, so it reduces under `decide`. It is the typed core's (`SqlCore.likeText`), ported. -/

/-- The pattern suffixes reachable without reading a character: a leading `%` may match the empty
    string. -/
def likePatClosure : List Char → List (List Char)
  | '%' :: p => ('%' :: p) :: likePatClosure p
  | p => [p]

/-- The pattern suffixes after reading `c` from the state `p`. -/
def likePatStep (c : Char) : List Char → List (List Char)
  | '%' :: p => likePatClosure ('%' :: p)
  | '_' :: p => likePatClosure p
  | d :: p => if d == c then likePatClosure p else []
  | [] => []

/-- Run the automaton over the text from a set of states; the text matches if the empty suffix
    (the whole pattern used) is reachable at its end. -/
def likePatRun : List (List Char) → List Char → Bool
  | sts, [] => sts.contains []
  | sts, c :: s => likePatRun ((sts.flatMap (likePatStep c)).eraseDups) s

/-- `s LIKE pat`, characters compared exactly (#323). The sqlite dialect's `likeCI` lowercases
    both sides first. -/
def likeMatch (s pat : String) : Bool :=
  likePatRun (likePatClosure pat.toList) s.toList

/-- Evaluate binary operator.
    NULL SEMANTICS (Option 3): When either operand is a SQL NULL (`some (.null _)`),
    arithmetic/comparison/string ops return `some (.null none)` instead of `none`.
    This separates "SQL NULL propagation" from "evaluation error" (which remains `none`).
    AND/OR keep SQL three-valued logic short-circuit rules.
    Note: We use `some _` (not bare `_`) so that `none` (errors) still propagate as `none`. -/
def evalBinOp (op : BinOp) (l r : Option Value) : Option Value :=
  match op, l, r with
  -- Arithmetic: null propagation
  | .add, some (.null _), some _ => some (.null none)
  | .add, some _, some (.null _) => some (.null none)
  | .add, some (.int a), some (.int b) => some (.int (a + b))
  -- Decimal arithmetic: scale-align, compute, renormalize (#201).
  -- int↔decimal promotes the int to scale-0 decimal per the SQL standard.
  | .add, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal
      (u1 * 10 ^ (max s1 s2 - s1) + u2 * 10 ^ (max s1 s2 - s2)) (max s1 s2))
  | .add, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * 10 ^ s + u) s)
  | .add, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u + b * 10 ^ s) s)
  | .sub, some (.null _), some _ => some (.null none)
  | .sub, some _, some (.null _) => some (.null none)
  | .sub, some (.int a), some (.int b) => some (.int (a - b))
  | .sub, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal
      (u1 * 10 ^ (max s1 s2 - s1) - u2 * 10 ^ (max s1 s2 - s2)) (max s1 s2))
  | .sub, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * 10 ^ s - u) s)
  | .sub, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u - b * 10 ^ s) s)
  | .mul, some (.null _), some _ => some (.null none)
  | .mul, some _, some (.null _) => some (.null none)
  | .mul, some (.int a), some (.int b) => some (.int (a * b))
  | .mul, some (.decimal u1 s1), some (.decimal u2 s2) =>
    some (Value.mkDecimal (u1 * u2) (s1 + s2))
  | .mul, some (.int a), some (.decimal u s) => some (Value.mkDecimal (a * u) s)
  | .mul, some (.decimal u s), some (.int b) => some (Value.mkDecimal (u * b) s)
  -- NOTE: decimal div/mod intentionally fall to the error catch-all for now —
  -- result-scale policy is engine-specific and deferred (tracked in #201).
  | .div, some (.null _), some _ => some (.null none)
  | .div, some _, some (.null _) => some (.null none)
  -- Integer division and modulo truncate toward zero (sqlite, DuckDB `//`,
  -- Postgres: -7 / 2 = -3, -7 % 2 = -1), not Lean's Euclidean `/` and `%`.
  | .div, some (.int a), some (.int b) =>
    if b == 0 then none else some (.int (a.tdiv b))
  | .mod, some (.null _), some _ => some (.null none)
  | .mod, some _, some (.null _) => some (.null none)
  | .mod, some (.int a), some (.int b) =>
    if b == 0 then none else some (.int (a.tmod b))
  -- Comparison: null propagation (NULL = anything → NULL)
  | .eq, some (.null _), some _ => some (.null none)
  | .eq, some _, some (.null _) => some (.null none)
  | .eq, some a, some b => (a.eq b).map Value.bool
  | .ne, some (.null _), some _ => some (.null none)
  | .ne, some _, some (.null _) => some (.null none)
  | .ne, some a, some b => (a.eq b).map (fun b => Value.bool (!b))
  | .lt, some (.null _), some _ => some (.null none)
  | .lt, some _, some (.null _) => some (.null none)
  | .lt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .lt))
  | .le, some (.null _), some _ => some (.null none)
  | .le, some _, some (.null _) => some (.null none)
  | .le, some a, some b => (a.compare b).map (fun o => Value.bool (o != .gt))
  | .gt, some (.null _), some _ => some (.null none)
  | .gt, some _, some (.null _) => some (.null none)
  | .gt, some a, some b => (a.compare b).map (fun o => Value.bool (o == .gt))
  | .ge, some (.null _), some _ => some (.null none)
  | .ge, some _, some (.null _) => some (.null none)
  | .ge, some a, some b => (a.compare b).map (fun o => Value.bool (o != .lt))
  -- Boolean: SQL three-valued logic
  -- Short-circuit rules (FALSE dominates AND, TRUE dominates OR)
  | .and, some (.bool a), some (.bool b) => some (.bool (a && b))
  | .and, some (.bool false), _ => some (.bool false)  -- FALSE AND anything = FALSE
  | .and, _, some (.bool false) => some (.bool false)
  -- AND: null propagation (after short-circuit, null + value = null; none still propagates)
  | .and, some (.null _), some _ => some (.null none)
  | .and, some _, some (.null _) => some (.null none)
  | .or, some (.bool a), some (.bool b) => some (.bool (a || b))
  | .or, some (.bool true), _ => some (.bool true)      -- TRUE OR anything = TRUE
  | .or, _, some (.bool true) => some (.bool true)
  -- OR: null propagation (after short-circuit, null + value = null; none still propagates)
  | .or, some (.null _), some _ => some (.null none)
  | .or, some _, some (.null _) => some (.null none)
  -- String: null propagation
  | .concat, some (.null _), some _ => some (.null none)
  | .concat, some _, some (.null _) => some (.null none)
  | .concat, some (.string a), some (.string b) => some (.string (a ++ b))
  | .like, some (.null _), some _ => some (.null none)
  | .like, some _, some (.null _) => some (.null none)
  | .like, some (.string s), some (.string pat) =>
    some (.bool (likeMatch s pat))
  -- ASCII case-insensitive LIKE (sqlite dialect): Char.toLower only maps A-Z
  | .likeCI, some (.null _), some _ => some (.null none)
  | .likeCI, some _, some (.null _) => some (.null none)
  | .likeCI, some (.string s), some (.string pat) =>
    some (.bool (likeMatch (s.map Char.toLower) (pat.map Char.toLower)))
  -- Everything else is a genuine error (type mismatch, missing value)
  | _, _, _ => none

/-- A value with the static type of a NULL erased: all NULLs are one grouping key (#315). SQL
    treats NULLs as "not distinct" when grouping, whatever expression produced them; the type tag
    on `Value.null` is an artefact of the untyped representation. -/
def Value.eraseNullType : Value → Value
  | .null _ => .null none
  | v => v

/-- A value as a set operation compares it (#324): NULLs are one value whatever their type tag,
    and numbers compare by value, as `=` does (`1 = 1.0`): an integer becomes the equal decimal
    and a decimal its canonical form, so `1`, `1.0` and `1.00` share a key. -/
def Value.setKey : Value → Value
  | .null _ => .null none
  | .int n => .decimal n 0
  | .decimal u s => Value.mkDecimal u s
  | v => v

/-- A row's values in column order, as set operations compare them (`Value.setKey`, #324).
    Set operations match rows by position and value, as the standard does: column names, the
    static type of a NULL and the representation of a number take no part. -/
def Row.valueKey (row : Row) : List Value := (row.map Prod.snd).map Value.setKey

/-- Keep the first element of each class of elements with equal `f`, in order (#324). -/
def dedupByKey {α β : Type} [BEq β] (f : α → β) : List α → List α
  | [] => []
  | x :: xs => x :: dedupByKey f (xs.filter fun y => !(f y == f x))
termination_by l => l.length
decreasing_by
  simp only [List.length_cons, List.length_unattach]
  exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_attach ..)))

@[simp] theorem dedupByKey_nil {α β : Type} [BEq β] (f : α → β) :
    dedupByKey f ([] : List α) = [] := by
  rw [dedupByKey]

theorem dedupByKey_cons {α β : Type} [BEq β] (f : α → β) (x : α) (xs : List α) :
    dedupByKey f (x :: xs) = x :: dedupByKey f (xs.filter fun y => !(f y == f x)) := by
  rw [dedupByKey]

/-- Deduplicating pairs by a key on their first component, then keeping the first components, is
    deduplicating the first components (#320): the pairs' second components stay aligned with
    the deduplicated firsts. -/
theorem map_fst_dedupByKey {α γ β : Type} [BEq β] (f : α → β) (L : List (α × γ)) :
    (dedupByKey (fun p => f p.1) L).map Prod.fst = dedupByKey f (L.map Prod.fst) := by
  suffices ∀ (n : Nat) (L : List (α × γ)), L.length ≤ n →
      (dedupByKey (fun p => f p.1) L).map Prod.fst = dedupByKey f (L.map Prod.fst) from
    this L.length L (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro L hL
    cases L with
    | nil => simp
    | cons _ _ => simp at hL
  | succ k ih =>
    intro L hL
    match L with
    | [] => simp
    | p :: ps =>
      have hlen : (ps.filter fun q => !(f q.1 == f p.1)).length ≤ k :=
        Nat.le_trans (List.length_filter_le _ _) (by simp at hL; omega)
      rw [dedupByKey_cons, List.map_cons, ih _ hlen, List.map_cons, dedupByKey_cons, List.filter_map]
      rfl

/-- Deduplicating aligned pairs by their first components keeps as many pairs as deduplicating
    the first components alone (#320). -/
theorem length_dedupByKey_zip {α γ β : Type} [BEq β] (f : α → β) (P : List α) (S : List γ)
    (h : P.length = S.length) :
    (dedupByKey (fun p => f p.1) (P.zip S)).length = (dedupByKey f P).length := by
  have := congrArg List.length (map_fst_dedupByKey f (P.zip S))
  rwa [List.length_map, List.map_fst_zip (by omega)] at this

/-- Deduplication never lengthens a list. -/
theorem length_dedupByKey_le {α β : Type} [BEq β] (f : α → β) (l : List α) :
    (dedupByKey f l).length ≤ l.length := by
  suffices ∀ (n : Nat) (l : List α), l.length ≤ n → (dedupByKey f l).length ≤ l.length from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl
    match l with
    | [] => simp
    | x :: xs =>
      have hf := List.length_filter_le (fun y => !(f y == f x)) xs
      have := ih (xs.filter fun y => !(f y == f x)) (by simp at hl; omega)
      rw [dedupByKey_cons, List.length_cons, List.length_cons]
      omega

/-- The column names of a table, read from its first row (#324). -/
def Table.columnNames (t : Table) : Option (List String) := t.head?.map (·.map Prod.fst)

/-- Rename a row's columns positionally to `names` when the arities agree (#324): the columns
    of a set operation are named by its first branch. -/
def Row.renameTo : Option (List String) → Row → Row
  | some ns, row => if ns.length = row.length then ns.zip (row.map Prod.snd) else row
  | none, row => row

/-- Apply a set operation to two result tables. Shared by top-level Query
    evaluation and SubQuery evaluation (#218). Rows are compared by `Row.valueKey`
    (position and value; NULLs equal whatever their type tag, #324), and the right
    branch's rows take the left branch's column names: `names`, the names the caller reads
    from the leftmost branch's SELECT list (`Query.outputNames?`, #340), or, when that has a
    `*`, the names of the left table's first row.
    UNION dedups, UNION ALL concatenates, INTERSECT/EXCEPT filter by membership and
    dedup (#223); dedup keeps the first row of each key. -/
def applySetOp (op : SetOp) (names : Option (List String)) (l r : Table) : Table :=
  let ns := match names with
    | some ns => some ns
    | none => Table.columnNames l
  match op with
  | .union => dedupByKey Row.valueKey (l ++ r.map (Row.renameTo ns))
  | .unionAll => l ++ r.map (Row.renameTo ns)
  | .intersect =>
    dedupByKey Row.valueKey (l.filter fun row => (r.map Row.valueKey).contains (Row.valueKey row))
  | .exceptOp =>
    dedupByKey Row.valueKey (l.filter fun row => !(r.map Row.valueKey).contains (Row.valueKey row))

/-- Check if Option Value is NULL (none or some null) -/
def isNullValue : Option Value → Bool
  | none => true
  | some (.null _) => true
  | _ => false

/-- Whether some row's first value equals `v` (`x IN (subquery)` found a match). -/
def inSubqueryMatch (v : Value) (rows : Table) : Bool :=
  rows.any fun subRow =>
    match subRow.head? with
    | some (_, subVal) => v.eq subVal == some true
    | none => false

/-- Whether a NULL takes part in `v IN (subquery)` (#330): `v` is NULL and the subquery has a
    row, or some row's first value is NULL. -/
def inSubqueryHasNull (v : Value) (rows : Table) : Bool :=
  (v.isNull && !rows.isEmpty) ||
    rows.any fun subRow =>
      match subRow.head? with
      | some (_, subVal) => subVal.isNull
      | none => false

/-- `v IN (subquery)` (or `NOT IN` when `neg`), three-valued as the standard defines it (#330),
    and as `IN (list)` already is: TRUE if some row's first value equals `v`, otherwise unknown
    (NULL) if a NULL takes part, otherwise FALSE. `NOT IN` negates, and unknown stays unknown, so
    `5 NOT IN (SELECT NULL)` drops the row in a WHERE clause. An empty subquery gives FALSE
    (`NOT IN`: TRUE), even for a NULL `v`. -/
def inSubqueryResult (neg : Bool) (v : Value) (rows : Table) : Value :=
  if inSubqueryMatch v rows then .bool (!neg)
  else if inSubqueryHasNull v rows then .null none
  else .bool neg

/-- A match makes `IN (subquery)` TRUE (`NOT IN`: FALSE), NULLs or not. -/
theorem inSubqueryResult_of_match {neg : Bool} {v : Value} {rows : Table}
    (h : inSubqueryMatch v rows = true) : inSubqueryResult neg v rows = .bool (!neg) := by
  simp [inSubqueryResult, h]

/-- `IN (subquery)` is TRUE only on a match. -/
theorem inSubqueryMatch_of_result_true {v : Value} {rows : Table}
    (h : inSubqueryResult false v rows = .bool true) : inSubqueryMatch v rows = true := by
  unfold inSubqueryResult at h
  cases hm : inSubqueryMatch v rows
  · cases hn : inSubqueryHasNull v rows <;> simp [hm, hn] at h
  · rfl

/-- Without NULLs, `IN (subquery)` is two-valued: the membership test. -/
theorem inSubqueryResult_of_not_hasNull {neg : Bool} {v : Value} {rows : Table}
    (h : inSubqueryHasNull v rows = false) :
    inSubqueryResult neg v rows =
      .bool (if neg then !inSubqueryMatch v rows else inSubqueryMatch v rows) := by
  unfold inSubqueryResult
  cases hm : inSubqueryMatch v rows <;> cases neg <;> simp [h]

/-- Evaluate unary operator.
    NULL SEMANTICS (Option 3): NOT/NEG on null returns `some (.null none)` instead of `none`. -/
def evalUnaryOp (op : UnaryOp) (e : Option Value) : Option Value :=
  match op, e with
  | .not, some (.bool b) => some (.bool (!b))
  | .not, some (.null _) => some (.null none)  -- NOT NULL = NULL
  | .neg, some (.int n) => some (.int (-n))
  | .neg, some (.decimal u s) => some (.decimal (-u) s)  -- canonical form preserved
  | .neg, some (.null _) => some (.null none)  -- -NULL = NULL
  | .isNull, v => some (.bool (isNullValue v))
  | .isNotNull, v => some (.bool (!isNullValue v))
  | _, _ => none

/-- `u / 10^k` rounded to an integer, half away from zero (`ROUND`, #355). -/
def roundHalfAway (u : Int) (k : Nat) : Int :=
  let p := 10 ^ k
  let q := u.natAbs / p
  let q' := if 2 * (u.natAbs % p) ≥ p then q + 1 else q
  if u < 0 then -(q' : Int) else (q' : Int)

/-- `ROUND(n, d)` of an integer: unchanged for `d ≥ 0`; for `d < 0`, rounded to a multiple of
    `10^-d`, half away from zero (DuckDB, Postgres; registry row 16). -/
def roundInt (n d : Int) : Int :=
  if d ≥ 0 then n else roundHalfAway n d.natAbs * 10 ^ d.natAbs

/-- `ROUND(u / 10^s, d)` of a decimal, exactly, half away from zero; the result is a decimal
    with at most `max d 0` places (registry row 16). -/
def roundDecimal (u : Int) (s : Nat) (d : Int) : Value :=
  if (s : Int) ≤ d then .decimal u s
  else if 0 ≤ d then Value.mkDecimal (roundHalfAway u (s - d.toNat)) d.toNat
  else Value.mkDecimal (roundHalfAway u (s + d.natAbs) * 10 ^ d.natAbs) 0

/-- Evaluate scalar function -/
def evalFunc (name : String) (args : List (Option Value)) : Option Value :=
  match name.toUpper, args with
  | "COALESCE", vals =>
    vals.find? (fun v => !isNullValue v) |>.join
  | "NULLIF", [some a, some b] =>
    if a.eq b == some true then some (.null none) else some a
  | "ABS", [some (.null _)] => some (.null none)
  | "ABS", [some (.int n)] => some (.int n.natAbs)
  | "ABS", [some (.decimal u sc)] => some (.decimal u.natAbs sc)  -- canonical form preserved
  -- ROUND keeps the input type: an integer stays an integer, a decimal is rounded exactly
  -- (registry row 16, #355). NULL in either argument gives NULL.
  | "ROUND", [some (.null _)] => some (.null none)
  | "ROUND", [some (.null _), some _] => some (.null none)
  | "ROUND", [some _, some (.null _)] => some (.null none)
  | "ROUND", [some (.int n)] => some (.int n)
  | "ROUND", [some (.int n), some (.int d)] => some (.int (roundInt n d))
  | "ROUND", [some (.decimal u sc)] => some (roundDecimal u sc 0)
  | "ROUND", [some (.decimal u sc), some (.int d)] => some (roundDecimal u sc d)
  | "LENGTH", [some (.null _)] => some (.null none)
  | "LENGTH", [some (.string s)] => some (.int s.length)
  | "UPPER", [some (.null _)] => some (.null none)
  | "UPPER", [some (.string s)] => some (.string s.toUpper)
  | "LOWER", [some (.null _)] => some (.null none)
  | "LOWER", [some (.string s)] => some (.string s.toLower)
  | "CONCAT", [some (.null _), some _] => some (.null none)
  | "CONCAT", [some _, some (.null _)] => some (.null none)
  | "CONCAT", [some (.string a), some (.string b)] => some (.string (a ++ b))
  | _, _ => none

/-- Get column name from expression for output -/
def exprToName : Expr → String
  | .col c => c.column
  | .func name _ => name
  | .agg .count _ _ => "count"
  | .agg .sum _ _ => "sum"
  | .agg .avg _ _ => "avg"
  | .agg (.min _) _ _ => "min"
  | .agg (.max _) _ _ => "max"
  | .countStar => "count"
  | _ => "expr"

/-- The output column names of a SELECT list when they do not depend on the data (#340): each
    item is an expression, named by its alias or `exprToName` exactly as the evaluator names it
    (`evalSelectItemParam`). A `*` item's columns come from the rows, so then `none`. -/
def SelectItem.outputNames? (items : List SelectItem) : Option (List String) :=
  items.mapM fun
    | .exprItem e al => some (al.getD (exprToName e))
    | .star _ => none

/-- A query's output column names, read from its leftmost branch (#340): a set operation's
    columns are named by its first branch even when that branch has no rows. -/
def Query.outputNames? (q : Query) : Option (List String) :=
  SelectItem.outputNames? q.leftmostItems

/-- A subquery body's output column names, read from its leftmost branch (#340). -/
def SubQuery.outputNames? (sq : SubQuery) : Option (List String) :=
  SelectItem.outputNames? sq.leftmostItems

-- ============================================================================
-- evalBinOp Lemmas
-- ============================================================================

/-- AND returns `some (.bool true)` iff both operands are `some (.bool true)`. -/
theorem evalBinOp_and_true_iff (l r : Option Value) :
    (evalBinOp .and l r == some (.bool true)) =
    ((l == some (.bool true)) && (r == some (.bool true))) := by
  cases l with
  | none =>
    cases r with
    | none => rfl
    | some w => cases w with
      | bool b => cases b <;> rfl
      | null _ => rfl
      | int _ => rfl
      | string _ => rfl
      | decimal _ _ => rfl
  | some v =>
    cases v with
    | bool b =>
      cases b with
      | true =>
        cases r with
        | none => rfl
        | some w => cases w with
          | bool b' => cases b' <;> rfl
          | null _ => rfl
          | int _ => rfl
          | string _ => rfl
          | decimal _ _ => rfl
      | false =>
        cases r with
        | none => rfl
        | some w => cases w with
          | bool b' => cases b' <;> rfl
          | null _ => rfl
          | int _ => rfl
          | string _ => rfl
          | decimal _ _ => rfl
    | null _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | int _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | string _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl
    | decimal _ _ =>
      cases r with
      | none => rfl
      | some w => cases w with
        | bool b => cases b <;> rfl
        | null _ => rfl
        | int _ => rfl
        | string _ => rfl
        | decimal _ _ => rfl

end SqlEquiv
