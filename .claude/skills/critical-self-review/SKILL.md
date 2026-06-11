---
name: critical-self-review
description: >-
  Adversarial self-review of the current changes when no external reviewer is
  available (e.g. to conserve Copilot/human review credits). Use when the user
  asks for a critical review, a self-review, a "second opinion", a pre-push
  sanity check, "review my changes/PR critically", "poke holes in this", or an
  explicit alternative to Copilot. Reviews BOTH code (correctness, edge cases,
  security, tests, reuse/simplification) AND prose/strategy/PRD/research docs
  (load-bearing assumptions, unstated risks, weak evidence, internal
  consistency, missing alternatives). Produces ranked, honest findings — never a
  rubber stamp.
---

# Critical self-review

You are the skeptic the author can't be about their own work. Your job is to
find what's wrong, weak, unproven, or missing — not to reassure. A review that
only praises is a failed review. Be rigorous, specific, and honest; separate
high-confidence findings from speculation, and never invent problems to seem
thorough.

## When to run (project rule)

This repo's trigger heuristic lives in `CLAUDE.md` ("review when a bug would
be quiet, skip when it would be loud") — consult it for the always-review and
skip categories. Two rules from it bind every review run here:

- **Verify findings empirically (probe, don't speculate) before acting on
  them.** A confident-sounding finding that wasn't probed has been wrong
  before in this repo (a "live soundness hole" that was commented-out code).
- **Check docs shipped with the behavior** (README/plan checkboxes/
  TESTING_STRATEGY) as part of the review.

## Step 1 — Establish scope

Figure out exactly what you're reviewing, in this order of preference:

1. If the user named a PR/branch/file, review that.
2. Otherwise review the working-tree diff: `git diff` (unstaged) + `git diff --staged`.
3. If the working tree is clean, review the branch against its base:
   `git merge-base HEAD <base>` then `git diff <base>...HEAD` (base is usually
   `main`/`master`, or the PR base).
4. For a remote PR, fetch the diff via the GitHub tools.

State the scope you settled on in one line before diving in.

## Step 2 — Read the actual changes (and enough context)

- Read every changed hunk, plus enough surrounding code/doc to judge it in
  context — a diff read in isolation hides most real bugs.
- For code: trace the changed paths, their callers, and the data that flows
  through them. Check the tests that cover (or fail to cover) the change.
- For docs/strategy: read the whole argument, not just edited lines, so you can
  judge internal consistency and what's been left unsaid.

## Step 3 — Review along the right dimensions

Pick the dimensions that fit the content. Most changes are one or the other;
some are both.

### For code
- **Correctness & edge cases** — off-by-one, null/empty/boundary inputs, error
  and failure paths, concurrency/ordering, floating-point/tolerance, resource
  leaks, time zones, encodings.
- **Security** — injection, authz, secrets/PII in code or logs, unsafe
  deserialization, untrusted input reaching a sink.
- **Contract & compatibility** — API/behavior changes, backward compatibility,
  migrations.
- **Tests** — do they actually exercise the new behavior and its failure modes,
  or just the happy path? What's untested?
- **Reuse & simplification** — duplicated logic, a simpler construct, an existing
  helper that already does this, dead code.

### For prose / strategy / PRD / research
- **Load-bearing assumptions** — what must be true for this to work? Is it stated
  and is it justified, or asserted? Name the riskiest one.
- **Evidence quality** — are numbers/claims sourced and plausible? Inconsistent
  figures? Cherry-picked or vanity metrics? An irrelevant denominator (e.g. a
  TAM that isn't the addressable share)?
- **Unstated risks & failure modes** — what could make this fail that the
  document doesn't mention?
- **Alternatives not considered** — is the chosen path compared against the
  obvious other options?
- **Internal consistency** — do the sections agree? Do conclusions follow from
  the stated premises?
- **Feasibility & cost** — can this actually be built/run within the stated
  constraints (budget, time, team)?

## Step 4 — Output format

Deliver findings in this shape:

1. **Scope** — one line on what was reviewed.
2. **What's genuinely strong** — 2–4 bullets, brief. (Establishes you read it; do
   not pad.)
3. **Findings, ranked by leverage/severity** — most important first
   (existential/blocking → major → minor/nit). For each:
   - a clear statement of the problem,
   - *why* it matters (the bug it causes / the risk it creates),
   - a concrete fix or the experiment that would resolve it,
   - a confidence tag when uncertain (e.g. "speculative — verify").
   - Cite `file:line` for code.
4. **The single highest-leverage thing** — if the author does one thing, what is
   it?

Prefer a scannable structure (short headers, tables for many small items). Keep
nits clearly separated from substantive issues so they don't drown the signal.

## Honesty rules (non-negotiable)

- Do **not** rubber-stamp. If you found nothing serious, say so plainly and state
  what you checked — but look hard first.
- Distinguish **confident** findings from **speculation**; never present a guess
  as a fact.
- Don't fabricate issues to appear thorough, and don't soften a real problem to
  be polite.
- It's fine — encouraged — to challenge the premise of the change itself, not
  just its execution.

## Posting (optional)

Default to delivering the review in chat. Only post to a PR if the user asks.
When posting to GitHub, be frugal: a single structured review comment, not a
swarm of inline nits.

## Related

For a pure code bug-hunt or auto-applied cleanups, the built-in `/code-review`
and `/simplify` skills are narrower tools. This skill is broader and
adversarial, and explicitly covers strategy/prose as well as code.
