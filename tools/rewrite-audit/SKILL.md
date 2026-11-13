---
name: rewrite-audit
description: Soundness audit for expression rewriters (optimizers, simplifiers, query rewriters, lint autofixes). Checks each rewrite rule against the evaluator for every runtime kind of value, including NULLs and errors, checks type guards, runs a differential probe with a mutant vacuity check, and for Lean projects audits the trust base, runtime/proof divergence and the scope of the proven relation. Use when asked to audit a rewriter or optimizer, after changing rewrite rules or the evaluator, or for "/rewrite-audit".
---

# rewrite-audit

An expression rewrite `lhs → rhs` is sound only if `eval(lhs) = eval(rhs)` for
**every runtime kind of value** each free variable can take (including NULL
and evaluation errors), and in **every context** the evaluator depends on
(rows, environments, databases, configuration). Untyped or dynamically typed
ASTs hide the bugs: an evaluator with catch-all "type error" arms behaves
differently once a rewrite removes an operator. The classic case is
`a AND TRUE → a`. When `a` is the integer `42`, the original is a type error,
but the rewrite returns `42`.

## Usage

- `/rewrite-audit`: full scan of every rewriter found in the project.
- `/rewrite-audit <function>`: audit one rewrite function.

## Procedure

### 0. Load or build the project map

Read `.claude/rewrite-audit.json` if it exists (schema in
`references/discovery.md`). It names:
- the rewriters;
- the evaluator entry points;
- the value type, including its NULL and error representations;
- the equivalence relation the rewriter must preserve, and what it should
  quantify over;
- the probe command;
- for proof-assistant projects, the trust guard.

If the file does not exist, follow `references/discovery.md` to find these.
Show the findings and ask the user to confirm or correct them in **one**
question. Then propose the config file contents, and write the file only if
the user agrees.

### 1. Trust and runtime checks (proof-assistant projects only)

If the project is a Lean project (`lakefile.lean`/`lakefile.toml`, `*.lean`),
load `references/lean.md` and run its checks first:
- trust base;
- runtime/proof divergence;
- relation scope;
- guard bridges.

### 2. Audit each rewrite arm

For each rewriter, take each pattern arm that returns a structurally
different expression and apply the protocol below.

Audit both levels:
- the **root rules**, the per-node step;
- the **driver**: the traversal or fixed-point loop that applies them. Its own
  equality checks ("did anything change?") can share a pattern-matching bug.

Through the driver, some arms may be unreachable on the inputs their guards
accept, for instance when constant folding fires first. Report that
reachability; an arm whose only reachable effect is a bug matters more.

- **Arms with a machine-checked proof:** confirm the proof concludes the
  *full* relation (§1 relation scope) and that every guard has bridge
  evidence. A full hand-trace is not needed.
- **Unproven arms:** do the full trace.

### 3. Empirical probe

Follow `references/probe-design.md`:
- run the project's property or differential tests over the rewriter;
- or propose one if none exists;
- always do the mutant vacuity check.

### 4. Report

Use `references/output-format.md`.

## The audit protocol (per arm)

1. **Identify the rule.** Write it as `pattern → result`, with its guard if
   any.
2. **List free variables.** These are the sub-expressions the pattern binds.
3. **Enumerate value kinds.** Build the table from the project's value type
   (`references/value-domains.md`): one row per constructor, plus each NULL
   kind and the error result. For binary operators take the cross product;
   for single-variable rules take every row.

   Also enumerate the kinds of every **constant the pattern matches**. A
   pattern compared with host-language equality may match constants of
   other kinds (Python `Lit(1) == Lit(True)`).
4. **Trace BEFORE.** For each combination, follow the evaluator's dispatch for
   the original expression. Note which arm fires, especially catch-alls that
   return an error.
5. **Trace AFTER.** Do the same for the rewritten expression. The result is
   one of:
   - a different operator (trace it);
   - a bare variable (its raw value);
   - a literal.
6. **Compare.** Equal results are `ok`. Different results are `MISMATCH`, a
   soundness bug; record the concrete counterexample. If the evaluator
   depends on context, vary it too: rows, environment, database contents
   (e.g. an empty vs a non-empty table for EXISTS-like constructs).
7. **Check guards.** A guard (e.g. "operand is definitely boolean") must:
   - reject every wrong-kind input, including errors and NULLs where they
     matter;
   - be conservative: false negatives are fine, false positives are bugs;
   - have **bridge evidence** tying it to the semantic precondition the rule
     needs. That means a proof in a proof assistant, or a test otherwise.

     The evidence must quantify over the same contexts as the relation.
     Mark combinations a guard excludes as `GUARD`.

`references/risk-patterns.md` lists the rule shapes that most often fail. Check
every arm against it.

## After the audit

For each issue:
- suggest a fix: add or tighten a guard and its bridge, narrow the pattern,
  or strengthen the proof to the full relation;
- offer a regression test that encodes the counterexample;
- offer to extend the probe so the class of bug is caught automatically.
