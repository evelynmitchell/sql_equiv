"""Generate the total, structurally recursive DecidableEq block for the AST.

`deriving DecidableEq` does not handle the nested mutual AST in Lean 4.27,
so SqlEquiv/Ast.lean carries a hand-shaped block between
`-- BEGIN GENERATED (tools/gen_ast_deceq.py)` and `-- END GENERATED`.

  python3 tools/gen_ast_deceq.py           # print the block
  python3 tools/gen_ast_deceq.py --write   # replace the block in Ast.lean
  python3 tools/gen_ast_deceq.py --check   # exit 1 if Ast.lean is stale

When a constructor or field changes, update the tables at the bottom
(P = field with an existing DecidableEq instance; otherwise the name of
the mutual decider for that field).
"""
import pathlib
import sys
P = None  # plain field (uses existing DecidableEq instance)

def rhs(fields):
    if not fields:
        return "isTrue rfl"
    (a, b, rec) = fields[0]
    inner = rhs(fields[1:])
    core = (f"if h : {a} = {b} then by subst h; exact ({inner}) "
            f"else isFalse (fun n => h (by injection n <;> assumption))")
    if rec:
        core = f"let _ : Decidable ({a} = {b}) := {rec} {a} {b}\n      " + core
    return core

def gen_type(tname, ctors):
    """ctors: list of (ctorName, [fieldRec or None])"""
    multi = len(ctors) > 1
    out = [f"def {tname}.decEq (a b : {tname}) : Decidable (a = b) :="]
    if multi:
        out.append("  match a with")
        for k, (c, fs) in enumerate(ctors):
            xs = [f"a{i}" for i in range(len(fs))]
            ys = [f"b{i}" for i in range(len(fs))]
            pa = f"@{tname}.{c} {' '.join(xs)}".rstrip()
            pb = f"@{tname}.{c} {' '.join(ys)}".rstrip()
            body = rhs(list(zip(xs, ys, fs)))
            out.append(f"  | {pa} =>")
            out.append(f"    if hb : b.ctorIdx = {k} then")
            out.append(f"      match b, hb with")
            out.append(f"      | {pb}, _ =>\n        {body}")
            out.append(f"    else isFalse (fun e => hb (by subst e; rfl))")
    else:
        out.append("  match a, b with")
        (c, fs) = ctors[0]
        xs = [f"a{i}" for i in range(len(fs))]
        ys = [f"b{i}" for i in range(len(fs))]
        pa = f"@{tname}.{c} {' '.join(xs)}".rstrip()
        pb = f"@{tname}.{c} {' '.join(ys)}".rstrip()
        out.append(f"  | {pa}, {pb} =>\n    {rhs(list(zip(xs, ys, fs)))}")
    out.append("termination_by structural a")
    return "\n".join(out)

def gen_list(fname, elem, elemdec):
    return f"""def {fname} (a b : List {elem}) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match {elemdec} x y, {fname} xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1 h2; rfl)
    | isFalse h1, _ => isFalse (fun e => by injection e; contradiction)
    | _, isFalse h2 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a"""

def gen_opt(fname, elem, elemdec):
    return f"""def {fname} (a b : Option {elem}) : Decidable (a = b) :=
  match a, b with
  | none, none => isTrue rfl
  | some x, some y =>
    match {elemdec} x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by injection e; contradiction)
  | none, some _ => isFalse (fun e => by cases e)
  | some _, none => isFalse (fun e => by cases e)
termination_by structural a"""

def gen_pairs(fname, elem, elemdec):
    return f"""def {fname} (a b : List ({elem} × {elem})) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | (x1, x2) :: xs, (y1, y2) :: ys =>
    match {elemdec} x1 y1, {elemdec} x2 y2, {fname} xs ys with
    | isTrue h1, isTrue h2, isTrue h3 => isTrue (by subst h1 h2 h3; rfl)
    | isFalse h1, _, _ => isFalse (fun e => by injection e with e1; injection e1; contradiction)
    | _, isFalse h2, _ => isFalse (fun e => by injection e with e1; injection e1; contradiction)
    | _, _, isFalse h3 => isFalse (fun e => by injection e; contradiction)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
termination_by structural a"""

E, EL, EO, EP = "Expr.decEq", "Expr.decEqList", "Expr.decEqOpt", "Expr.decEqPairs"
SQ, WS, OB, OBL = "SubQuery.decEq", "WindowSpec.decEq", "OrderByItem.decEq", "OrderByItem.decEqList"
SIL, FC, FCO, SS = "SelectItem.decEqList", "FromClause.decEq", "FromClause.decEqOpt", "SelectStmt.decEq"

block1 = [
    gen_type("WindowSpec", [("mk", [EL, OBL])]),
    gen_type("Expr", [
        ("lit", [P]), ("col", [P]), ("binOp", [P, E, E]), ("unaryOp", [P, E]),
        ("func", [P, EL]), ("agg", [P, EO, P]), ("countStar", []),
        ("«case»", [EP, EO]), ("inList", [E, P, EL]), ("inSubquery", [E, P, SQ]),
        ("exists", [P, SQ]), ("subquery", [SQ]), ("between", [E, E, E]),
        ("windowFn", [P, EO, WS])]),
    gen_list(EL, "Expr", E), gen_opt(EO, "Expr", E), gen_pairs(EP, "Expr", E),
    gen_type("OrderByItem", [("mk", [E, P, P])]),
    gen_list(OBL, "OrderByItem", OB),
    gen_type("SelectItem", [("star", [P]), ("exprItem", [E, P])]),
    gen_list(SIL, "SelectItem", "SelectItem.decEq"),
    gen_type("FromClause", [("table", [P]), ("subquery", [SQ, P]), ("join", [FC, P, FC, EO])]),
    gen_opt(FCO, "FromClause", FC),
    gen_type("SubQuery", [("simple", [SS]), ("compound", [SQ, P, SQ])]),
    gen_type("SelectStmt", [("mk", [P, SIL, FCO, EO, EL, EO, OBL, P, P])]),
]
block2 = [
    gen_type("CTEDef", [("mk", [P, "Query.decEq", P])]),
    gen_list("CTEDef.decEqList", "CTEDef", "CTEDef.decEq"),
    gen_type("Query", [("simple", [P]), ("compound", ["Query.decEq", P, "Query.decEq"]),
                       ("withCTE", ["CTEDef.decEqList", "Query.decEq"])]),
]
parts = ["mutual\n" + "\n\n".join(block1) + "\nend\n"]
parts.append("""instance : DecidableEq WindowSpec := WindowSpec.decEq
instance : DecidableEq Expr := Expr.decEq
instance : DecidableEq OrderByItem := OrderByItem.decEq
instance : DecidableEq SelectItem := SelectItem.decEq
instance : DecidableEq FromClause := FromClause.decEq
instance : DecidableEq SubQuery := SubQuery.decEq
instance : DecidableEq SelectStmt := SelectStmt.decEq
""")
parts.append("mutual\n" + "\n\n".join(block2) + "\nend\n")
parts.append("""instance : DecidableEq CTEDef := CTEDef.decEq
instance : DecidableEq Query := Query.decEq""")

BLOCK = "\n".join(parts).strip("\n")
BEGIN = "-- BEGIN GENERATED (tools/gen_ast_deceq.py)"
END = "-- END GENERATED"
AST = pathlib.Path(__file__).resolve().parent.parent / "SqlEquiv" / "Ast.lean"


def current():
    text = AST.read_text()
    i, j = text.index(BEGIN) + len(BEGIN), text.index(END)
    return text, i, j


if __name__ == "__main__":
    if "--write" in sys.argv:
        text, i, j = current()
        AST.write_text(text[:i] + "\n" + BLOCK + "\n" + text[j:])
    elif "--check" in sys.argv:
        text, i, j = current()
        if text[i:j].strip("\n") != BLOCK:
            print("SqlEquiv/Ast.lean DecidableEq block is stale; run "
                  "python3 tools/gen_ast_deceq.py --write", file=sys.stderr)
            sys.exit(1)
        print("Ast.lean DecidableEq block is up to date")
    else:
        print(BLOCK)
