#!/bin/bash
# Hook: ensure-fresh-branch.sh
# Fires on PreToolUse(Task) — filters for Plan subagent only.
# Ensures we're on a fresh branch before starting any new task planning.
#
# Behavior:
#   - Non-Plan subagent: no-op (exit 0 immediately)
#   - On master/main: fetches latest, creates claude/<slug> branch
#   - On a branch with a merged PR: switches to master, creates new branch
#   - On a clean unmerged branch: passes through (no-op)
#
# Output: JSON with additionalContext so Claude sees the branch state.

set -euo pipefail

# Read stdin JSON and filter: only act on Plan subagents
input=$(cat)
subagent_type=$(echo "$input" | jq -r '.tool_input.subagent_type // empty' 2>/dev/null)
[ "$subagent_type" != "Plan" ] && exit 0

# Not a git repo? Nothing to do.
git rev-parse --git-dir >/dev/null 2>&1 || exit 0

branch=$(git branch --show-current 2>/dev/null)
[ -z "$branch" ] && exit 0

# Determine the default branch (master or main)
default_branch="master"
if git show-ref --verify --quiet refs/heads/main 2>/dev/null; then
  if ! git show-ref --verify --quiet refs/heads/master 2>/dev/null; then
    default_branch="main"
  fi
fi

# Generate a slug from timestamp (human-readable, unique)
generate_slug() {
  date +"%Y%m%d-%H%M%S"
}

# Check if the current branch has a merged PR (prints PR number or empty)
has_merged_pr() {
  gh pr list --state merged --head "$1" --json number -q '.[0].number' 2>/dev/null || true
}

# Case 1: Already on default branch — need to branch off
if [ "$branch" = "$default_branch" ]; then
  git fetch origin "$default_branch" --quiet 2>/dev/null || true
  git merge --ff-only "origin/$default_branch" --quiet 2>/dev/null || true
  new_branch="claude/task-$(generate_slug)"
  git checkout -b "$new_branch" --quiet 2>/dev/null
  cat <<EOJSON
{
  "additionalContext": "Auto-created branch '$new_branch' from $default_branch. You were on $default_branch — never commit directly to it."
}
EOJSON
  exit 0
fi

# Case 2: On a branch that already has a merged PR — stale branch
merged_pr=$(has_merged_pr "$branch")
if [ -n "$merged_pr" ]; then
  # Check for uncommitted changes
  if ! git diff --quiet 2>/dev/null || ! git diff --cached --quiet 2>/dev/null; then
    echo "Branch '$branch' has merged PR #$merged_pr but you have uncommitted changes. Stash or commit them first." >&2
    exit 2
  fi

  git checkout "$default_branch" --quiet 2>/dev/null
  git fetch origin "$default_branch" --quiet 2>/dev/null || true
  git merge --ff-only "origin/$default_branch" --quiet 2>/dev/null || true
  new_branch="claude/task-$(generate_slug)"
  git checkout -b "$new_branch" --quiet 2>/dev/null
  cat <<EOJSON
{
  "additionalContext": "Branch '$branch' already had merged PR #$merged_pr. Auto-created fresh branch '$new_branch' from $default_branch."
}
EOJSON
  exit 0
fi

# Case 3: On a working branch with no merged PR — all good
exit 0
