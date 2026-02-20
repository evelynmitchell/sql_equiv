"""Trace the sql_equiv repo with LeanDojo-v2 to extract structured proof data."""

import json
import os
import subprocess
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DST_DIR = PROJECT_ROOT / ".leandojo_trace"


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


def main():
    import argparse

    parser = argparse.ArgumentParser(description="Trace sql_equiv with LeanDojo-v2")
    parser.add_argument(
        "--repo", default=str(PROJECT_ROOT),
        help="Path to the local repo (default: project root)",
    )
    parser.add_argument(
        "--commit", default="HEAD",
        help="Commit to trace (default: HEAD)",
    )
    parser.add_argument(
        "--dst", default=str(DEFAULT_DST_DIR),
        help="Output directory for trace data (default: .leandojo_trace/)",
    )
    args = parser.parse_args()

    dst_dir = Path(args.dst)

    _ensure_github_token()

    from lean_dojo_v2.lean_dojo import LeanGitRepo, trace

    # Clean up previous trace if it exists
    if dst_dir.exists():
        import shutil
        shutil.rmtree(dst_dir)

    print(f"Tracing local repo {args.repo} @ {args.commit}...")
    print(f"Output dir: {dst_dir}")

    repo = LeanGitRepo(args.repo, args.commit)
    print(f"Resolved commit: {repo.commit}")
    print(f"Lean version: {repo.lean_version}")

    traced_repo = trace(repo, dst_dir=str(dst_dir), build_deps=False)

    print(f"\nTrace complete!")
    print(f"Number of traced files: {len(traced_repo.traced_files)}")

    # List all traced files
    print("\n=== Traced Files ===")
    for tf in sorted(traced_repo.traced_files, key=lambda f: str(f.path)):
        theorems = list(tf.traced_theorems)
        print(f"  {tf.path}: {len(theorems)} theorems")

    # Focus on key files
    key_files = ["SqlEquiv/SemanticsCore.lean", "SqlEquiv/Decidable.lean", "SqlEquiv/Semantics.lean"]
    for key_file in key_files:
        matches = [tf for tf in traced_repo.traced_files if str(tf.path).endswith(key_file)]
        if matches:
            tf = matches[0]
            theorems = list(tf.traced_theorems)
            print(f"\n=== {key_file} ===")
            print(f"  Theorems: {len(theorems)}")
            for tt in theorems[:10]:
                print(f"    - {tt.theorem.full_name}")
                if tt.traced_tactics:
                    print(f"      Tactics: {len(tt.traced_tactics)}")
                    for tac in tt.traced_tactics[:3]:
                        print(f"        {tac.tactic}")

    # Save summary as JSON
    summary = {
        "repo": args.repo,
        "commit": repo.commit,
        "num_files": len(traced_repo.traced_files),
        "files": {}
    }
    for tf in traced_repo.traced_files:
        file_info = {
            "theorems": [],
        }
        for tt in tf.traced_theorems:
            thm_info = {
                "name": tt.theorem.full_name,
                "num_tactics": len(tt.traced_tactics),
                "tactics": [t.tactic for t in tt.traced_tactics[:5]],
            }
            file_info["theorems"].append(thm_info)
        summary["files"][str(tf.path)] = file_info

    summary_path = dst_dir / "trace_summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nSummary saved to {summary_path}")


if __name__ == "__main__":
    main()
