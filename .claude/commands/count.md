# /count

Count axioms and theorems across the SqlEquiv codebase.

## Usage

- `/count` — Summary with per-file breakdown
- `/count names` — List every axiom and theorem name

## Instructions

1. **Run the counting tool:**
   ```bash
   python3 tools/count_axioms_theorems.py -v
   ```

   If the user runs `/count names`:
   ```bash
   python3 tools/count_axioms_theorems.py --names
   ```

2. **Show the output directly** — the tool formats its own table.

3. **Briefly note** any files where the axiom count is high relative to theorems — these are opportunities for proving work.
