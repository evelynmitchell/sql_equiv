#!/usr/bin/env python3
"""
CI duration sparkline viewer.

Fetches recent CI run timings from GitHub Actions and renders sparklines
to make duration deviations immediately visible.

Usage:
    python tools/ci_sparkline.py              # Last 20 CI runs
    python tools/ci_sparkline.py --runs 50    # Last 50 CI runs
    python tools/ci_sparkline.py --workflow "Axiom Coverage Validation"

Requires: gh CLI authenticated with repo access.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime


# Steps we care about tracking (CI workflow step names)
TRACKED_STEPS = [
    "Build library",
    "Build tests",
    "Run tests",
    "Build LSpec property tests",
    "Run LSpec property tests",
    "Check axiom coverage ratchet",
]

SPARK_CHARS = "▁▂▃▄▅▆▇█"


def get_repo_nwo() -> str:
    """Get the owner/repo string for the current repository."""
    result = subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        print(f"Error detecting repo: {result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout.strip()


def sparkline(values: list[float]) -> str:
    """Render a list of floats as a unicode sparkline."""
    if not values:
        return ""
    lo = min(values)
    hi = max(values)
    spread = hi - lo if hi != lo else 1
    return "".join(
        SPARK_CHARS[min(int((v - lo) / spread * (len(SPARK_CHARS) - 1)), len(SPARK_CHARS) - 1)]
        for v in values
    )


def fetch_runs(repo: str, workflow: str, count: int) -> list[int]:
    """Fetch recent workflow runs via gh CLI."""
    # Escape backslashes and double quotes for safe jq string interpolation
    safe_workflow = workflow.replace("\\", "\\\\").replace('"', '\\"')
    jq_filter = (
        f'.workflow_runs | map(select(.name == "{safe_workflow}" and .status == "completed"))'
        f' | .[:{count}] | .[].id'
    )
    result = subprocess.run(
        ["gh", "api", f"/repos/{repo}/actions/runs?per_page=100",
         "--jq", jq_filter],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        print(f"Error fetching runs: {result.stderr}", file=sys.stderr)
        sys.exit(1)

    return [int(rid) for rid in result.stdout.strip().split("\n") if rid.strip()]


def fetch_step_durations(repo: str, run_id: int) -> dict[str, float]:
    """Fetch step-level durations for a single run."""
    result = subprocess.run(
        ["gh", "api", f"/repos/{repo}/actions/runs/{run_id}/jobs",
         "--jq", ".jobs[0].steps | map({name, started_at, completed_at})"],
        capture_output=True, text=True,
    )
    if result.returncode != 0:
        return {}

    try:
        steps = json.loads(result.stdout)
    except json.JSONDecodeError:
        return {}

    if not isinstance(steps, list):
        return {}

    durations: dict[str, float] = {}
    for step in steps:
        if not isinstance(step, dict):
            continue
        name = step.get("name", "")
        started = step.get("started_at")
        completed = step.get("completed_at")
        if not started or not completed:
            continue
        try:
            t0 = datetime.fromisoformat(started.replace("Z", "+00:00"))
            t1 = datetime.fromisoformat(completed.replace("Z", "+00:00"))
            durations[name] = (t1 - t0).total_seconds()
        except (ValueError, TypeError):
            continue

    return durations


def fmt_duration(seconds: float) -> str:
    """Format seconds as a human-readable string."""
    if seconds < 60:
        return f"{seconds:.0f}s"
    minutes = int(seconds // 60)
    secs = int(seconds % 60)
    return f"{minutes}m{secs:02d}s"


def detect_anomalies(values: list[float], threshold: float = 2.0) -> list[int]:
    """Find indices where value deviates more than threshold * stdev from mean."""
    if len(values) < 3:
        return []
    mean = sum(values) / len(values)
    variance = sum((v - mean) ** 2 for v in values) / len(values)
    stdev = variance ** 0.5
    if stdev == 0:
        return []
    return [i for i, v in enumerate(values) if abs(v - mean) > threshold * stdev]


def main() -> None:
    parser = argparse.ArgumentParser(description="CI duration sparkline viewer")
    parser.add_argument("--runs", type=int, default=20,
                        help="Number of recent runs to fetch (default: 20)")
    parser.add_argument("--workflow", default="CI",
                        help="Workflow name to track (default: CI)")
    parser.add_argument("--all-steps", action="store_true",
                        help="Show all steps, not just tracked ones")
    args = parser.parse_args()

    repo = get_repo_nwo()
    print(f"Fetching last {args.runs} '{args.workflow}' runs for {repo}...", flush=True)
    run_ids = fetch_runs(repo, args.workflow, args.runs)

    if not run_ids:
        print("No completed runs found.")
        return

    print(f"Found {len(run_ids)} runs. Fetching step timings...", flush=True)

    # Collect durations per step across all runs
    all_durations: list[dict[str, float]] = []
    for rid in run_ids:
        durations = fetch_step_durations(repo, rid)
        if durations:
            all_durations.append(durations)

    if not all_durations:
        print("No timing data found.")
        return

    # Reverse so oldest is first (sparkline reads left-to-right = old-to-new)
    all_durations.reverse()

    # Collect all step names seen
    all_steps: set[str] = set()
    for d in all_durations:
        all_steps.update(d.keys())

    # Filter to tracked steps (or all)
    if args.all_steps:
        steps = sorted(all_steps)
    else:
        steps = [s for s in TRACKED_STEPS if s in all_steps]

    if not steps:
        print("No tracked steps found in run data.")
        return

    # Sum of tracked step durations per run (not wall-clock job time)
    totals = []
    for d in all_durations:
        total = sum(v for k, v in d.items() if k in all_steps)
        totals.append(total)

    # Print header
    max_name_len = max(len(s) for s in steps + ["SUM"])
    n_runs = len(all_durations)

    print()
    print(f"{'Step':<{max_name_len}}  {'Sparkline':<{n_runs}}  {'Last':>6}  {'Avg':>6}  {'Min':>6}  {'Max':>6}  Notes")
    print("─" * (max_name_len + n_runs + 40))

    for step in steps:
        values = [d.get(step) for d in all_durations]

        # Compute stats only from runs where this step existed
        present_indices = [i for i, v in enumerate(values) if v is not None]
        present_values = [values[i] for i in present_indices]

        if not present_values:
            continue

        avg = sum(present_values) / len(present_values)
        last = present_values[-1]
        lo = min(present_values)
        hi = max(present_values)

        # For sparkline rendering, use 0 for missing runs
        spark_values = [v if v is not None else 0 for v in values]
        spark = sparkline(spark_values)

        # Run anomaly detection only on runs where this step exists
        anomalies_in_present = detect_anomalies(present_values)
        anomalies = [present_indices[i] for i in anomalies_in_present]

        notes = ""
        if anomalies:
            latest_anomaly = max(anomalies)
            if latest_anomaly == len(values) - 1:
                notes = "⚠ latest run is anomalous"
            else:
                notes = f"⚠ spike at run #{latest_anomaly + 1}"

        print(f"{step:<{max_name_len}}  {spark:<{n_runs}}  "
              f"{fmt_duration(last):>6}  {fmt_duration(avg):>6}  "
              f"{fmt_duration(lo):>6}  {fmt_duration(hi):>6}  {notes}")

    # Total row
    if totals:
        avg = sum(totals) / len(totals)
        spark = sparkline(totals)
        anomalies = detect_anomalies(totals)
        notes = ""
        if anomalies and max(anomalies) == len(totals) - 1:
            notes = "⚠ latest run is anomalous"

        print("─" * (max_name_len + n_runs + 40))
        print(f"{'SUM':<{max_name_len}}  {spark:<{n_runs}}  "
              f"{fmt_duration(totals[-1]):>6}  {fmt_duration(avg):>6}  "
              f"{fmt_duration(min(totals)):>6}  {fmt_duration(max(totals)):>6}  {notes}")

    print()


if __name__ == "__main__":
    main()
