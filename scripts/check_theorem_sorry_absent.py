#!/usr/bin/env python3
"""Acceptance probe for pebble aln-c57.

Observes whether a named Lean theorem's own proof body still carries
`sorry`, per `scripts/check.sh --json`. Emits exactly one `stdout_json`
object and judges nothing itself (docs/ORACLES.md section 7) — the
derived spec's `then` predicates own the verdict
(contracts/specs/derived-aln-c57.spec.json).

Usage: check_theorem_sorry_absent.py THEOREM_NAME

Runs the real `scripts/check.sh --json THEOREM_NAME` (which builds the
project with `lake build`), parses its one JSON line, and relays the
`theorem_in_sorry` fact it already computes (check.sh's own header:
"true when THEOREM_NAME ... is in `sorry`") as `contains_sorry`, the
field name contracts/specs/derived-aln-c57.spec.json's `then` predicate
checks for equality against `false`.
"""
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_theorem_sorry_absent.py THEOREM_NAME", file=sys.stderr)
        return 2
    theorem = sys.argv[1]
    proc = subprocess.run(
        ["scripts/check.sh", "--json", theorem],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    report = json.loads(proc.stdout)
    print(json.dumps({
        "contains_sorry": report["theorem_in_sorry"],
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
