#!/usr/bin/env python3
"""Write `scripts/gate-baseline.json` from the current tree.

Usage: python3 scripts/update_gate_baseline.py
Run from the repo root. Runs a full build, the type-lint driver, and a
`decisionScope` scan over every `ArmadaLean/**/*.lean` file outside
`ArmadaLean/Lint/` — the full-tree cost `gate_extra.check_decision_scope`
no longer pays on every gate run. Expect several minutes.

Run this in the SAME branch that lowers a `gate_extra.LINT_REGRESSION_FIELDS`
count or fixes a `decisionScope` finding, and commit the result alongside
that fix. Never run it to raise a count or add a finding without a fix:
the gate (`gate_extra.check_lint`/`check_decision_scope`) compares the
tree against this committed file, so a baseline raised without a
matching fix shows up in the branch's own diff for review (`AGENTS.md`,
"Lean work: standing rules").
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_extra  # noqa: E402


def main() -> int:
    root = Path.cwd()
    baseline = gate_extra.compute_baseline(root)
    gate_extra.write_baseline(root, baseline)
    print(
        f"wrote {gate_extra.BASELINE_REL}: "
        f"{len(baseline['file_hashes'])} files, "
        f"{len(baseline['decision_findings'])} decisionScope findings"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
