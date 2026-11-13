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
matching fix shows up in the branch's own diff for review.

Usage: python3 scripts/update_gate_baseline.py --hashes-only
Rewrites only `file_hashes`. Keeps `lint_summary` and `decision_findings`
as the committed file already has them. Hashing only, no `lake build` and
no `decisionScope` scan: seconds, not minutes. Use this after a merge
changes a file's bytes without changing its lint counts or its
decisionScope findings, so `decisionScope` stops rescanning a file that
did not really change its findings.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gate_extra  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--hashes-only",
        action="store_true",
        help="Rewrite only file_hashes. Keep lint_summary and "
        "decision_findings as committed.",
    )
    args = parser.parse_args()
    root = Path.cwd()
    if args.hashes_only:
        existing = gate_extra.load_baseline(root)
        files = gate_extra._lean_files(root)
        file_hashes = {str(f): gate_extra._file_sha256(root / f) for f in files}
        baseline = {
            "lint_summary": existing["lint_summary"],
            "decision_findings": existing["decision_findings"],
            "file_hashes": file_hashes,
        }
    else:
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
