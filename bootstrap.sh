#!/usr/bin/env bash
#
# SOPS Bootstrap Script
# Detects environment and installs development tools idempotently.
#
# Usage:
#   ./bootstrap.sh           # Install all tools for detected environment
#   ./bootstrap.sh --check   # Check what's installed without changing anything
#
set -euo pipefail

# Colors for output (disabled if not a terminal)
if [[ -t 1 ]]; then
    GREEN='\033[0;32m'
    YELLOW='\033[0;33m'
    RED='\033[0;31m'
    RESET='\033[0m'
else
    GREEN=''
    YELLOW=''
    RED=''
    RESET=''
fi

log_ok()   { echo -e "${GREEN}✓${RESET} $1"; }
log_warn() { echo -e "${YELLOW}⚠${RESET} $1"; }
log_err()  { echo -e "${RED}✗${RESET} $1"; }
log_info() { echo "  $1"; }

# Detect environment
# Currently detected: claude-cli, claude-code, codespaces, github-actions,
#                     devcontainer, container, vscode, local
# Future candidates (not yet implemented):
#   - GitPod ($GITPOD_WORKSPACE_ID)
#   - WSL (/proc/version contains "microsoft")
#   - macOS (uname == Darwin) - uses brew instead of apt
#   - Replit ($REPL_ID)
#   - Coder ($CODER_WORKSPACE_ID)
detect_env() {
    # Claude CLI in Sprite VM (check first - most specific)
    if [[ -d "/.sprite" ]]; then
        echo "claude-cli"
    # Claude Code desktop
    elif [[ -n "${CLAUDE_CODE_EMIT_TOOL_USE_SUMMARIES:-}" ]] || [[ -n "${CLAUDE_CODE_ENTRYPOINT:-}" ]]; then
        echo "claude-code"
    elif [[ -n "${CODESPACES:-}" ]]; then
        echo "codespaces"
    elif [[ -n "${GITHUB_ACTIONS:-}" ]]; then
        echo "github-actions"
    elif [[ -n "${REMOTE_CONTAINERS:-}" ]]; then
        echo "devcontainer"
    elif [[ -f /.dockerenv ]] || [[ -f /run/.containerenv ]]; then
        echo "container"
    elif [[ "${TERM_PROGRAM:-}" == "vscode" ]]; then
        echo "vscode"
    else
        echo "local"
    fi
}

# Check if a command exists
has_cmd() {
    command -v "$1" &>/dev/null
}

# Get version of a tool (first line, numbers only)
get_version() {
    "$1" --version 2>/dev/null | head -1 | grep -oE '[0-9]+\.[0-9]+(\.[0-9]+)?' | head -1
}

# Install uv (Python package manager)
ensure_uv() {
    if has_cmd uv; then
        log_ok "uv $(get_version uv)"
        return 0
    fi

    if [[ "${CHECK_ONLY:-}" == "1" ]]; then
        log_warn "uv not installed"
        return 1
    fi

    log_info "Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh

    # Add to PATH for this session
    export PATH="$HOME/.local/bin:$PATH"

    if has_cmd uv; then
        log_ok "uv $(get_version uv) installed"
    else
        log_err "Failed to install uv"
        return 1
    fi
}

# Install ruff (Python linter)
ensure_ruff() {
    if has_cmd ruff; then
        log_ok "ruff $(get_version ruff)"
        return 0
    fi

    if [[ "${CHECK_ONLY:-}" == "1" ]]; then
        log_warn "ruff not installed"
        return 1
    fi

    log_info "Installing ruff..."
    if has_cmd uv; then
        uv tool install ruff
    elif has_cmd pip; then
        pip install --user ruff
    else
        log_err "Cannot install ruff: no uv or pip"
        return 1
    fi

    if has_cmd ruff; then
        log_ok "ruff $(get_version ruff) installed"
    else
        log_err "Failed to install ruff"
        return 1
    fi
}

# Install pre-commit (git hooks)
ensure_precommit() {
    local env="$1"

    # Skip in Claude Code - hooks don't run there
    if [[ "$env" == "claude-code" ]]; then
        log_info "pre-commit skipped (Claude Code environment)"
        return 0
    fi

    if has_cmd pre-commit; then
        log_ok "pre-commit $(get_version pre-commit)"
        return 0
    fi

    if [[ "${CHECK_ONLY:-}" == "1" ]]; then
        log_warn "pre-commit not installed"
        return 1
    fi

    log_info "Installing pre-commit..."
    if has_cmd uv; then
        uv tool install pre-commit
    elif has_cmd pip; then
        pip install --user pre-commit
    else
        log_err "Cannot install pre-commit: no uv or pip"
        return 1
    fi

    if has_cmd pre-commit; then
        log_ok "pre-commit $(get_version pre-commit) installed"
    else
        log_err "Failed to install pre-commit"
        return 1
    fi
}

# Install shellcheck (shell linter)
ensure_shellcheck() {
    if has_cmd shellcheck; then
        log_ok "shellcheck $(get_version shellcheck)"
        return 0
    fi

    if [[ "${CHECK_ONLY:-}" == "1" ]]; then
        log_warn "shellcheck not installed"
        return 1
    fi

    log_info "Installing shellcheck..."
    if has_cmd apt-get; then
        sudo apt-get update -qq && sudo apt-get install -y -qq shellcheck
    elif has_cmd brew; then
        brew install shellcheck
    else
        log_warn "Cannot install shellcheck: no apt or brew"
        return 1
    fi

    if has_cmd shellcheck; then
        log_ok "shellcheck $(get_version shellcheck) installed"
    else
        log_err "Failed to install shellcheck"
        return 1
    fi
}

# Main
main() {
    local check_only=0

    # Parse args
    for arg in "$@"; do
        case "$arg" in
            --check) check_only=1 ;;
            --help|-h)
                echo "Usage: $0 [--check]"
                echo "  --check  Check what's installed without changes"
                exit 0
                ;;
        esac
    done

    export CHECK_ONLY="$check_only"

    # Detect environment
    local env
    env=$(detect_env)
    echo "Environment: $env"
    echo ""

    # Track failures
    local failed=0

    # Install tools
    ensure_uv || ((++failed))
    ensure_ruff || ((++failed))
    ensure_precommit "$env" || ((++failed))
    ensure_shellcheck || ((++failed))

    echo ""
    if [[ $failed -gt 0 ]]; then
        if [[ "$check_only" == "1" ]]; then
            log_warn "$failed tool(s) not installed"
        else
            log_err "$failed tool(s) failed to install"
        fi
        return 1
    else
        log_ok "All tools ready"
    fi
}


# Install Claude Code
echo "Installing Claude Code..."
if command -v claude > /dev/null 2>&1; then
    CLAUDE_VERSION=$(claude --version 2>&1 | head -1)
    print_success "Claude Code already installed ($CLAUDE_VERSION)"
else
    curl -fsSL https://claude.ai/install.sh | bash
    # Add to PATH for current session
    export PATH="$HOME/.local/bin:$PATH"

    # Verify installation succeeded
    if command -v claude > /dev/null 2>&1; then
        CLAUDE_VERSION=$(claude --version 2>&1 | head -1)
        print_success "Claude Code installed ($CLAUDE_VERSION)"
    else
        print_warning "Claude Code installation may have failed - command not found"
    fi
fi
echo ""

main "$@"
