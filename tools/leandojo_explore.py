"""Explore the LeanDojo trace output from the cache."""

import os
import json
from pathlib import Path

os.environ["GITHUB_ACCESS_TOKEN"] = os.popen("gh auth token").read().strip()

from lean_dojo_v2.lean_dojo.data_extraction.traced_data import TracedRepo

CACHE_DIR = Path(os.path.expanduser(
    "~/.cache/lean_dojo/gitpython-sql_equiv-bc5c5847b3c8fb45b5878fd761a5bb4556108a9a/sql_equiv"
))
OUTPUT_DIR = Path("/workspaces/sql_equiv/.leandojo_trace")

def main():
    print(f"Loading traced repo from {CACHE_DIR}...")
    traced_repo = TracedRepo.load_from_disk(CACHE_DIR, build_deps=False)

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

    summary_path = OUTPUT_DIR / "trace_summary.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    with open(summary_path, "w") as f:
        json.dump(summary, f, indent=2)

    print(f"\n{'='*60}")
    print(f"TOTALS: {total_theorems} theorems, {total_tactics} tactics across {len(traced_repo.traced_files)} files")
    print(f"Summary saved to {summary_path}")

if __name__ == "__main__":
    main()
