"""Trace the sql_equiv repo with LeanDojo-v2 to extract structured proof data."""

import os
import sys
import json
from pathlib import Path

# Set GitHub access token BEFORE importing (read at module level)
os.environ["GITHUB_ACCESS_TOKEN"] = os.popen("gh auth token").read().strip()

from lean_dojo_v2.lean_dojo import LeanGitRepo, trace

# Use the local copy of the repo
REPO_URL = "/workspaces/sql_equiv"
COMMIT = "HEAD"  # use current HEAD
DST_DIR = Path("/workspaces/sql_equiv/.leandojo_trace")

def main():
    # Clean up previous trace if it exists
    if DST_DIR.exists():
        import shutil
        shutil.rmtree(DST_DIR)

    print(f"Tracing local repo {REPO_URL} @ {COMMIT}...")
    print(f"Output dir: {DST_DIR}")

    repo = LeanGitRepo(REPO_URL, COMMIT)
    print(f"Resolved commit: {repo.commit}")
    print(f"Lean version: {repo.lean_version}")

    traced_repo = trace(repo, dst_dir=str(DST_DIR), build_deps=False)

    print(f"\nTrace complete!")
    print(f"Number of traced files: {len(traced_repo.traced_files)}")

    # List all traced files
    print("\n=== Traced Files ===")
    for tf in sorted(traced_repo.traced_files, key=lambda f: str(f.path)):
        n_thms = len([d for d in tf.traced_theorems])
        print(f"  {tf.path}: {n_thms} theorems")

    # Focus on key files
    key_files = ["SqlEquiv/SemanticsCore.lean", "SqlEquiv/Decidable.lean", "SqlEquiv/Semantics.lean"]
    for key_file in key_files:
        matches = [tf for tf in traced_repo.traced_files if str(tf.path).endswith(key_file)]
        if matches:
            tf = matches[0]
            print(f"\n=== {key_file} ===")
            print(f"  Theorems: {len(list(tf.traced_theorems))}")
            for tt in list(tf.traced_theorems)[:10]:
                print(f"    - {tt.theorem.full_name}")
                if tt.traced_tactics:
                    print(f"      Tactics: {len(tt.traced_tactics)}")
                    for tac in tt.traced_tactics[:3]:
                        print(f"        {tac.tactic}")

    # Save summary as JSON
    summary = {
        "repo": REPO_URL,
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

    summary_path = DST_DIR / "trace_summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\nSummary saved to {summary_path}")

if __name__ == "__main__":
    main()
