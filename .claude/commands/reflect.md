# /reflect

Post-task reflection to extract durable lessons. Use after completing a task, PR, or debugging session — especially when something surprising happened.

> **Note**: This skill references Claude Code's auto-memory `MEMORY.md`, which is a persistent file managed outside the repository at `~/.claude/projects/<project>/memory/MEMORY.md`. It is not committed to the repo.

## Usage

- `/reflect` — Reflect on the most recent task
- `/reflect <topic>` — Reflect on a specific topic or incident

## When to use

Use when any of these are true:
- Something took longer than expected
- Something was unexpectedly easy (prior investment paid off)
- A mistake was made that could recur
- A pattern repeated from a previous session
- The approach changed mid-task

Do NOT use when the task was genuinely trivial with no surprises. Forced reflection on routine work produces noise, not signal.

## Instructions

### Step 1: What happened?

Summarize the task in 1-2 sentences. State the outcome (proved N axioms, fixed a bug, deleted unsound code, etc.).

### Step 2: What was hard vs. easy, and why?

For each significant subtask, classify it:

- **Easy because of prior investment**: Name the specific infrastructure, tool, or convention that made it easy. This validates past decisions and highlights compounding returns.
- **Easy because it was inherently simple**: Note this briefly and move on. Not everything has a lesson.
- **Hard because of missing infrastructure**: This is an action item. What tool, helper lemma, test, or convention would have made it easy? Could it be built now?
- **Hard because inherently complex**: Record the complexity for future reference. What made it irreducibly hard?
- **Hard because of a mistake**: What went wrong? Was the mistake novel or a repeat? (Check the memory file for prior instances.)

### Step 3: What pattern repeated?

Search the auto-memory directory for related entries:

```
Grep pattern="<keyword>" path="<auto_memory_dir>" glob="*.md"
```

(The auto-memory directory is Claude Code's persistent memory at `~/.claude/projects/<project>/memory/`. The exact path is shown in your system prompt as the "auto memory directory".)

If the current experience matches an existing memory entry:
- Did the entry help prevent a mistake? (Good — the system works.)
- Did the mistake happen anyway despite the entry? (The entry needs strengthening — maybe automation instead of documentation.)
- Is the entry outdated? (Update or remove it.)

If no match exists but the lesson is durable, draft a new entry.

### Step 4: What would have made this faster?

Not "what shortcut could I have taken" but "what missing tool, test, or convention would have eliminated a class of problems?"

Examples of high-leverage answers:
- "A helper lemma for X would have made 3 proofs trivial" → build it
- "A test that checks Y would have caught this before CI" → write it
- "A pre-commit hook that validates Z" → add it
- "A naming convention for W" → document it

Avoid low-leverage answers like "I should have read the file more carefully." That's not actionable.

### Step 5: What transfers?

Separate project-specific detail from general principle:

| Project-specific | General principle |
|-----------------|-------------------|
| `simp only [List.nil_append, List.map_id']` cleans up `[] ++ ·` | Infrastructure lemmas compound — each one makes the next proof easier |
| `join_comm_full` was unsound due to `lr ++ rr ≠ rr ++ lr` | Strict equality on ordered structures is almost always wrong for commutativity |
| Pre-commit hook catches unstaged axiom count updates | Automate what you forget to do manually |

Record both, but in different places and with different weight. General principles go in the "Working Principles" section of your auto-memory `MEMORY.md`. Project-specific tactics go in their relevant section (e.g., "Lean Proof Tactics", "Optimizer Soundness Patterns").

### Step 6: What should I stop doing?

The highest-leverage reflections are subtractive. Examples:
- "Stop speculating about elaborator behavior; use `trace_state`"
- "Stop fixing one instance; enumerate all instances mechanically"
- "Stop trying to prove blocked axioms; document the blocker and move on"

If nothing comes to mind, skip this step. Don't invent things to stop doing.

## Output Format

```
## Reflection: [task summary]

**Outcome**: [1 sentence]

**What was easy**: [what and why — name the infrastructure that helped]

**What was hard**: [what and why — missing infrastructure or inherent complexity]

**Repeated pattern**: [link to existing memory entry, or "novel"]

**Speed-up opportunity**: [actionable item, or "none identified"]

**Transferable principle**: [general lesson, if any]

**Stop doing**: [bad habit identified, if any]

**Memory update**: [what to add/update/remove in auto-memory MEMORY.md, or "none needed"]
```

## After reflecting

If the reflection identified:
- **A new working principle**: Add it to the "Working Principles" section of auto-memory `MEMORY.md`
- **A project-specific tactic**: Add it to the relevant section of auto-memory `MEMORY.md`
- **An outdated memory entry**: Update or remove it
- **A missing tool/test/hook**: Create a task or note it in Next Session TODO
- **Nothing**: That's fine. Not every task produces a lesson.

## Anti-patterns

- **Don't make it a ritual.** If the task was routine, say "nothing surprising" and stop. The moment reflection feels like filling out a form, it's lost its value.
- **Don't write aspirational notes.** "I should always check X" without a specific incident is noise. Tie every entry to a concrete event.
- **Don't over-record.** Five sharp observations beat twenty vague ones. Prune aggressively.
- **Don't confuse activity with insight.** "I read 5 files and wrote 3 theorems" is a summary, not a reflection. The insight is *why* it went well or poorly.
