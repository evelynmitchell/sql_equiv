# /mathlib

Search Mathlib for relevant lemmas and theorems.

## Usage

- `/mathlib <query>` - Search for lemmas matching query
- `/mathlib List filter` - Find lemmas about List.filter
- `/mathlib Nat add comm` - Find commutativity lemmas for Nat addition

## Instructions

Help the user find relevant Mathlib lemmas for their proofs.

### Steps

1. **Understand what the user needs:**
   - What type are they working with? (List, Nat, Int, etc.)
   - What operation? (filter, map, add, etc.)
   - What property? (comm, assoc, cancel, etc.)

2. **Search strategies:**
   - Use web search to find Mathlib docs
   - Check common naming patterns (see below)
   - Look in the project's existing imports for clues

3. **Provide results:**
   - Give the full lemma name
   - Show the type signature
   - Explain when to use it

### Mathlib Naming Conventions

- `*_comm` - Commutativity (e.g., `Nat.add_comm`)
- `*_assoc` - Associativity
- `*_left`, `*_right` - Left/right variants
- `*_zero`, `*_one` - Identity elements
- `*_cancel` - Cancellation properties
- `List.filter_*`, `List.map_*` - List operations

### Example

User: `/mathlib List filter filter`

Response:
```
List.filter_filter : filter p (filter q l) = filter (fun a => p a && q a) l

This lemma shows that two consecutive filters can be combined.
Use it when you have nested filter operations to simplify.
```
