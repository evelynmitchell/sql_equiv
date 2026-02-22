#!/usr/bin/env bash
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
# Dependencies: jq (JSON parsing), gh (GitHub CLI, merged-PR detection)
# Output: JSON with additionalContext so Claude sees the branch state.

set -euo pipefail

# Read stdin JSON and filter: only act on Plan subagents
input=$(cat)

if ! command -v jq >/dev/null 2>&1; then
  echo "jq not found — cannot parse task JSON. Install jq or remove this hook." >&2
  exit 2
fi

subagent_type=$(echo "$input" | jq -r '.tool_input.subagent_type // empty' 2>/dev/null)
[ "$subagent_type" != "Plan" ] && exit 0

# Not a git repo? Nothing to do.
git rev-parse --git-dir >/dev/null 2>&1 || exit 0

# gh CLI required for merged-PR detection
if ! command -v gh >/dev/null 2>&1; then
  echo "gh CLI not found — cannot check for merged PRs. Install gh or remove this hook." >&2
  exit 2
fi

branch=$(git branch --show-current 2>/dev/null)
if [ -z "$branch" ]; then
  echo "[ensure-fresh-branch] Detached HEAD (no current branch); skipping branch hygiene checks." >&2
  exit 0
fi

# Determine the default branch (prefer repo's configured default)
default_branch="master"
if origin_head=$(git symbolic-ref --quiet --short refs/remotes/origin/HEAD 2>/dev/null); then
  origin_head="${origin_head#origin/}"
  if [ -n "$origin_head" ]; then
    default_branch="$origin_head"
  fi
else
  if git show-ref --verify --quiet refs/heads/main 2>/dev/null; then
    if ! git show-ref --verify --quiet refs/heads/master 2>/dev/null; then
      default_branch="main"
    fi
  fi
fi

# Generate a slug from timestamp (human-readable, reasonably unique)
generate_slug() {
  # Avoid %N (nanoseconds) — not supported by BSD date on macOS.
  # Use seconds-level timestamp plus PID to reduce collision likelihood.
  date +"%Y%m%d-%H%M%S-$$"
}

# Fetch and fast-forward the default branch, failing hard if diverged
fetch_and_ff_default() {
  git fetch origin "$default_branch" --quiet 2>/dev/null || true
  if ! git merge --ff-only "origin/$default_branch" --quiet 2>/dev/null; then
    echo "Error: could not fast-forward '$default_branch' to 'origin/$default_branch'. Resolve the divergence and try again." >&2
    exit 2
  fi
}

# Check if the current branch has a merged PR (prints PR number or empty)
has_merged_pr() {
  gh pr list --state merged --head "$1" --json number -q '.[0].number' 2>/dev/null || true
}

# Case 1: Already on default branch — need to branch off
if [ "$branch" = "$default_branch" ]; then
  fetch_and_ff_default
  new_branch="claude/task-$(generate_slug)"
  if ! git checkout -b "$new_branch" --quiet; then
    echo "Error: could not create branch '$new_branch'. A branch or file with that name may already exist." >&2
    exit 2
  fi
  jq -n --arg msg "Auto-created branch '$new_branch' from $default_branch. You were on $default_branch — never commit directly to it." \
    '{additionalContext: $msg}'
  exit 0
fi

# Case 2: On a branch that already has a merged PR — stale branch
merged_pr=$(has_merged_pr "$branch")
if [ -n "$merged_pr" ]; then
  # Check for uncommitted or untracked changes
  if ! git diff --quiet 2>/dev/null || ! git diff --cached --quiet 2>/dev/null || [ -n "$(git ls-files --others --exclude-standard 2>/dev/null)" ]; then
    echo "Branch '$branch' has merged PR #$merged_pr but you have uncommitted or untracked changes. Stash, commit, or clean them first." >&2
    exit 2
  fi

  # Ensure the default branch exists locally before checking it out
  if git show-ref --verify --quiet "refs/heads/$default_branch" 2>/dev/null; then
    git checkout "$default_branch" --quiet
  elif git show-ref --verify --quiet "refs/remotes/origin/$default_branch" 2>/dev/null; then
    git checkout -b "$default_branch" "origin/$default_branch" --quiet
  else
    echo "Default branch '$default_branch' does not exist locally or on origin. Cannot create a fresh task branch." >&2
    exit 2
  fi
  fetch_and_ff_default
  new_branch="claude/task-$(generate_slug)"
  if ! git checkout -b "$new_branch" --quiet; then
    echo "Error: could not create branch '$new_branch'. A branch or file with that name may already exist." >&2
    exit 2
  fi
  jq -n --arg msg "Branch '$branch' already had merged PR #$merged_pr. Auto-created fresh branch '$new_branch' from $default_branch." \
    '{additionalContext: $msg}'
  exit 0
fi

# Case 3: On a working branch with no merged PR — all good
exit 0
