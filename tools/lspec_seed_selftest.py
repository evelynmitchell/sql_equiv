#!/usr/bin/env python3
"""
End-to-end self-test of the LSpec run seed (#395).

A property runner that ignores its seed still passes every test, so this checks, on the built
executable, that:
  1. `sql_equiv_lspec --must-fail` (one deliberately false property) exits non-zero;
  2. the same LSPEC_SEED fails at the same sample with the same output (replay);
  3. different seeds fail at different samples (the variable is read);
  4. the failure output names the seed in a replay command;
  5. an LSPEC_SEED that is not a number is an error, not a silent default;
  6. no property under LSpecTests/ uses LSpec's own `check`, which ignores the seed.

Usage: python3 tools/lspec_seed_selftest.py   (after `lake build sql_equiv_lspec`)
Stdlib only.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

EXE = Path(__file__).resolve().parent.parent / ".lake" / "build" / "bin" / "sql_equiv_lspec"


def run(seed: str | None, *args: str) -> tuple[int, str]:
    env = dict(os.environ, LSPEC_SAMPLES="2000")
    env.pop("LSPEC_SEED", None)
    if seed is not None:
        env["LSPEC_SEED"] = seed
    p = subprocess.run([str(EXE), *args], env=env, capture_output=True, text=True, timeout=300)
    return p.returncode, p.stdout + p.stderr


def failing_sample(out: str) -> int:
    m = re.search(r"Found problems at sample (\d+)!", out)
    if not m:
        sys.exit(f"error: no failing sample reported in:\n{out}")
    return int(m.group(1))


def main() -> None:
    if not EXE.exists():
        sys.exit(f"error: {EXE} not built — run `lake build sql_equiv_lspec` first")
    errors: list[str] = []

    rc1, out1 = run("1", "--must-fail")
    rc1b, out1b = run("1", "--must-fail")
    if rc1 == 0 or rc1b == 0:
        errors.append("the deliberately false property did not fail the run (exit code 0)")
    if out1 != out1b:
        errors.append("the same seed gave different output on two runs (no replay)")
    if "LSPEC_SEED=1 " not in out1:
        errors.append("the failure output does not name the seed in a replay command")

    samples = {1: failing_sample(out1)}
    for seed in range(2, 9):
        rc, out = run(str(seed), "--must-fail")
        if rc == 0:
            errors.append(f"seed {seed}: the deliberately false property did not fail the run")
        samples[seed] = failing_sample(out)
    if len(set(samples.values())) < 3:
        errors.append(f"seeds 1..8 fail at nearly the same sample {samples}: is LSPEC_SEED read?")

    rc0, out0 = run(None, "--must-fail")
    rc0b, out0b = run("0", "--must-fail")
    if rc0 == 0 or out0 != out0b:
        errors.append("an unset LSPEC_SEED is not the same run as LSPEC_SEED=0")

    rcbad, outbad = run("abc", "--must-fail")
    if rcbad == 0 or "LSPEC_SEED must be a natural number" not in outbad:
        errors.append("a non-numeric LSPEC_SEED was accepted")

    rcarg, _ = run("1", "--no-such-flag")
    if rcarg == 0:
        errors.append("an unknown argument was accepted")

    root = EXE.parent.parent.parent.parent / "LSpecTests"
    unseeded = [
        f"{f.name}:{i}"
        for f in sorted(root.glob("*.lean"))
        for i, line in enumerate(f.read_text(encoding="utf-8").splitlines(), 1)
        if re.search(r"(?<![\w.`])check\s*(\(cfg|\")", line)
    ]
    if unseeded:
        errors.append(f"unseeded LSpec `check` (use `checkS`): {', '.join(unseeded)}")
    seeded = sum(f.read_text(encoding="utf-8").count("checkS (cfg := cfg)") for f in root.glob("*.lean"))
    if seeded < 100:
        errors.append(f"only {seeded} seeded properties found under LSpecTests/ (expected over 100)")

    if errors:
        sys.exit("LSpec seed self-test FAILED:\n  " + "\n  ".join(errors))
    print(f"LSpec seed self-test passed: failing sample by seed {samples}")


if __name__ == "__main__":
    main()
