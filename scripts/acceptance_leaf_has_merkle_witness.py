#!/usr/bin/env python3
"""Acceptance probe for pebble aln-9b1.

Observes whether a named Lean theorem's own proof body still carries
`sorry`, per `scripts/check.sh --json`. Emits exactly one `stdout_json`
object and judges nothing itself (docs/ORACLES.md section 7) — the
derived spec's `then` predicates own the verdict
(contracts/specs/derived-aln-9b1.spec.json).

Usage: acceptance_leaf_has_merkle_witness.py THEOREM_NAME

Runs the real `scripts/check.sh --json THEOREM_NAME` (which builds the
project with `lake build`), parses its one JSON line, and reports whether
THEOREM_NAME appears in the `sorry` array it names back as
`theorem_under_test`.
"""
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: acceptance_leaf_has_merkle_witness.py THEOREM_NAME", file=sys.stderr)
        return 2
    theorem = sys.argv[1]
    proc = subprocess.run(
        ["scripts/check.sh", "--json", theorem],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    report = json.loads(proc.stdout)
    theorem_in_sorry = report["theorem_under_test"] in report["sorry"]
    print(json.dumps({"theorem_in_sorry": theorem_in_sorry}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
