#!/bin/bash
#
# SessionStart hook for Claude Code on the web.
# Installs the Lean toolchain pinned in lean-toolchain, plus apt deps
# (zstd, sqlite3), and warms the lake build cache.
#
# Network policy notes (Claude Code on the web, default policy):
#   - elan.lean-lang.org and release.lean-lang.org return 403, so the
#     standard elan-init.sh / `elan toolchain install` paths DO NOT work.
#   - github.com release downloads DO work, so elan and the Lean toolchain
#     are fetched from GitHub releases and linked into ~/.elan manually.
set -euo pipefail

# Only needed in remote (web) sessions; local environments manage their own toolchain.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

REPO_DIR="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "$0")/../.." && pwd)}"
ELAN_BIN="$HOME/.elan/bin"
export PATH="$ELAN_BIN:$PATH"

# Pinned toolchain, e.g. "leanprover/lean4:v4.27.0"
TOOLCHAIN="$(tr -d '[:space:]' < "$REPO_DIR/lean-toolchain")"
TOOLCHAIN_DIR="$HOME/.elan/toolchains/$(echo "$TOOLCHAIN" | sed -e 's|/|--|g' -e 's|:|---|g')"
VERSION="${TOOLCHAIN##*:}"          # v4.27.0
VERSION_NUM="${VERSION#v}"          # 4.27.0

# --- apt deps: zstd (to unpack the Lean tarball), sqlite3 (differential tests),
# unzip (to unpack the duckdb CLI) ---
missing_pkgs=()
command -v zstd >/dev/null 2>&1 || missing_pkgs+=(zstd)
command -v sqlite3 >/dev/null 2>&1 || missing_pkgs+=(sqlite3)
command -v unzip >/dev/null 2>&1 || missing_pkgs+=(unzip)
if [ "${#missing_pkgs[@]}" -gt 0 ]; then
  echo "Installing apt packages: ${missing_pkgs[*]}"
  if ! apt-get update -qq 2>/dev/null; then sudo apt-get update -qq; fi
  apt-get install -y -qq "${missing_pkgs[@]}" || sudo apt-get install -y -qq "${missing_pkgs[@]}"
fi

# --- elan (from GitHub releases; elan.lean-lang.org is blocked) ---
# Pinned: `latest` would let elan behavior change under us with no repo-side diff.
ELAN_VERSION="v4.2.3"
if ! command -v elan >/dev/null 2>&1; then
  echo "Installing elan $ELAN_VERSION from GitHub releases..."
  curl -sSfL -o /tmp/elan.tar.gz \
    "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz"
  tar -xzf /tmp/elan.tar.gz -C /tmp
  /tmp/elan-init -y --default-toolchain none
  rm -f /tmp/elan.tar.gz /tmp/elan-init
fi

# --- Lean toolchain (from GitHub releases; release.lean-lang.org is blocked) ---
if [ ! -x "$TOOLCHAIN_DIR/bin/lean" ]; then
  echo "Downloading Lean $VERSION from GitHub releases (~500MB)..."
  curl -sSfL -o /tmp/lean.tar.zst \
    "https://github.com/leanprover/lean4/releases/download/$VERSION/lean-$VERSION_NUM-linux.tar.zst"
  tar --zstd -xf /tmp/lean.tar.zst -C /tmp
  mkdir -p "$HOME/.elan/toolchains"
  rm -rf "$TOOLCHAIN_DIR"
  mv "/tmp/lean-$VERSION_NUM-linux" "$TOOLCHAIN_DIR"
  rm -f /tmp/lean.tar.zst
fi

# --- duckdb CLI (differential-test oracle, #203; from GitHub releases) ---
DUCKDB_VERSION="v1.5.3"  # pinned: output parsing depends on -list format details
if ! command -v duckdb >/dev/null 2>&1; then
  echo "Installing duckdb CLI from GitHub releases..."
  curl -sSfL -o /tmp/duckdb.zip \
    https://github.com/duckdb/duckdb/releases/download/$DUCKDB_VERSION/duckdb_cli-linux-amd64.zip
  unzip -o -q /tmp/duckdb.zip -d /usr/local/bin 2>/dev/null \
    || sudo unzip -o -q /tmp/duckdb.zip -d /usr/local/bin
  rm -f /tmp/duckdb.zip
fi

# Persist PATH for the session so `lake` is directly available.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  # shellcheck disable=SC2016  # expand when the env file is sourced, not here
  echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
fi

# Run from the repo so elan resolves the pinned toolchain via lean-toolchain.
cd "$REPO_DIR"
echo "Lean: $(lean --version)"

# --- Warm the build cache (fetches batteries/LSpec from GitHub on first run; no-op when cached) ---
# Non-fatal: the toolchain is already installed at this point, and a transient
# fetch/build failure here shouldn't take down session setup.
if ! { lake build && lake build sql_equiv_test sql_equiv_lspec; }; then
  echo "warning: cache-warming build failed; toolchain is installed, build will retry in-session" >&2
fi

echo "Session setup complete."
