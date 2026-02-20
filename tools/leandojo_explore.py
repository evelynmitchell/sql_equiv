"""Explore the LeanDojo trace output from the cache."""

import json
import os
import subprocess
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT_DIR = PROJECT_ROOT / ".leandojo_trace"


def _ensure_github_token() -> None:
    """Set GITHUB_ACCESS_TOKEN if not already provided."""
    if os.environ.get("GITHUB_ACCESS_TOKEN"):
        return
    try:
        result = subprocess.run(
            ["gh", "auth", "token"],
            check=True, capture_output=True, text=True,
        )
        os.environ["GITHUB_ACCESS_TOKEN"] = result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        raise RuntimeError(
            "GITHUB_ACCESS_TOKEN not set and `gh auth token` failed. "
            "Set GITHUB_ACCESS_TOKEN or install/configure the GitHub CLI."
        ) from e


def _find_latest_cache_dir() -> Path:
    """Auto-detect the newest LeanDojo cache directory for sql_equiv."""
    cache_base = Path(os.path.expanduser("~/.cache/lean_dojo"))
    if not cache_base.exists():
        raise FileNotFoundError(f"LeanDojo cache not found at {cache_base}")
    candidates = sorted(
        cache_base.glob("gitpython-sql_equiv-*/sql_equiv"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    if not candidates:
        raise FileNotFoundError(
            f"No sql_equiv cache entries found in {cache_base}. "
            "Run leandojo_trace.py first."
        )
    return candidates[0]


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Explore LeanDojo trace cache")
    parser.add_argument(
        "--cache-dir",
        help="Path to the LeanDojo cache directory (default: auto-detect newest)",
    )
    parser.add_argument(
        "--output-dir", default=str(DEFAULT_OUTPUT_DIR),
        help="Output directory for trace_summary.json (default: .leandojo_trace/)",
    )
    args = parser.parse_args()

    _ensure_github_token()

    from lean_dojo_v2.lean_dojo.data_extraction.traced_data import TracedRepo

    cache_dir = Path(args.cache_dir) if args.cache_dir else _find_latest_cache_dir()
    output_dir = Path(args.output_dir)

    print(f"Loading traced repo from {cache_dir}...")
    traced_repo = TracedRepo.load_from_disk(cache_dir, build_deps=False)

    print(f"Number of traced files: {len(traced_repo.traced_files)}")

    # List all traced files
    print("\n=== Traced Files ===")
    for tf in sorted(traced_repo.traced_files, key=lambda f: str(f.path)):
        thms = list(tf.get_traced_theorems())
        print(f"  {tf.path}: {len(thms)} theorems")

    # Focus on key files
    key_files = [
        "SqlEquiv/SemanticsCore.lean",
        "SqlEquiv/Equiv/Decidable.lean",
        "SqlEquiv/Semantics.lean",
        "SqlEquiv/Equiv/ValueLemmas.lean",
        "SqlEquiv/Equiv/StatementAxioms.lean",
        "SqlEquiv/Equiv/Comparison.lean",
    ]

    for key_file in key_files:
        matches = [tf for tf in traced_repo.traced_files if str(tf.path).endswith(key_file)]
        if matches:
            tf = matches[0]
            thms = list(tf.get_traced_theorems())
            print(f"\n{'='*60}")
            print(f"=== {key_file} ({len(thms)} theorems) ===")
            print(f"{'='*60}")
            for tt in thms[:15]:
                stmt = tt.get_theorem_statement()
                print(f"\n  {stmt[:120]}...")
                tactics = list(tt.get_traced_tactics())
                if tactics:
                    print(f"    Tactics ({len(tactics)}):")
                    for tac in tactics[:5]:
                        print(f"      [{tac.tactic}]")
                        if tac.state_before:
                            print(f"        before: {tac.state_before[:100]}...")
                    if len(tactics) > 5:
                        print(f"      ... and {len(tactics) - 5} more tactics")

    # Save comprehensive summary
    summary = {
        "num_files": len(traced_repo.traced_files),
        "files": {}
    }
    total_theorems = 0
    total_tactics = 0

    for tf in traced_repo.traced_files:
        thms = list(tf.get_traced_theorems())
        file_info = {
            "num_theorems": len(thms),
            "theorems": [],
        }
        for tt in thms:
            tactics = list(tt.get_traced_tactics())
            total_theorems += 1
            total_tactics += len(tactics)
            thm_info = {
                "name": tt.get_theorem_statement()[:200],
                "num_tactics": len(tactics),
                "tactics": [
                    {
                        "tactic": t.tactic,
                        "state_before": t.state_before[:200] if t.state_before else None,
                        "state_after": t.state_after[:200] if t.state_after else None,
                    }
                    for t in tactics
                ],
            }
            file_info["theorems"].append(thm_info)
        summary["files"][str(tf.path)] = file_info

    summary["total_theorems"] = total_theorems
    summary["total_tactics"] = total_tactics

    summary_path = output_dir / "trace_summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)

    print(f"\n{'='*60}")
    print(f"TOTALS: {total_theorems} theorems, {total_tactics} tactics across {len(traced_repo.traced_files)} files")
    print(f"Summary saved to {summary_path}")


if __name__ == "__main__":
    main()
