#!/usr/bin/env python3
"""gate-baseline-fresh pre-commit check (hashing only, no Lean).

Fails when a tracked `ArmadaLean/**/*.lean` file outside `ArmadaLean/Lint/`
has a sha256 that differs from `scripts/gate-baseline.json`'s
`file_hashes`, or is missing from it. A stale hash means the gate's
`decisionScope` check (`scripts/gate_extra.py:check_decision_scope`)
will rescan that file on the next gate run even though no fix changed
its findings — the rescan that this hook catches before commit, not
after a merge finds it (ruling 2026-11-02, armada-lean).

Runs at both the `pre-commit` and the `manual` stage
(.pre-commit-config.yaml), so a local commit and the merge-boundary gate
(`pre-commit run --all-files --hook-stage manual`) both catch a stale
hash. Only hashes files: no `lake build`, so it stays fast enough to run
on every commit.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_extra  # noqa: E402


def _tracked_lean_files(root: Path) -> list[str]:
    """Every tracked `ArmadaLean/**/*.lean` file outside `ArmadaLean/Lint/`,
    repo-relative, forward-slash. `git ls-files` so a file staged for
    deletion or not yet added never trips this check."""
    proc = subprocess.run(
        ["git", "ls-files", "ArmadaLean"],
        cwd=root, capture_output=True, text=True, check=True,
    )
    return sorted(
        line for line in proc.stdout.splitlines()
        if line.endswith(".lean") and "ArmadaLean/Lint/" not in line
    )


def main() -> int:
    root = Path.cwd()
    baseline = gate_extra.load_baseline(root)
    base_hashes: dict[str, str] = baseline["file_hashes"]

    stale = []
    for relpath in _tracked_lean_files(root):
        actual = gate_extra._file_sha256(root / relpath)
        if base_hashes.get(relpath) != actual:
            stale.append(relpath)

    if not stale:
        return 0

    print(f"{gate_extra.BASELINE_REL} is stale for {len(stale)} file(s):")
    for relpath in stale:
        print(f"  {relpath}")
    print("Run: python3 scripts/update_gate_baseline.py --hashes-only")
    return 1


if __name__ == "__main__":
    sys.exit(main())
