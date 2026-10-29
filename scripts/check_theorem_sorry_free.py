#!/usr/bin/env python3
"""Acceptance probe for pebble aln-91b.

Observes whether a named Lean theorem's own proof body still carries
`sorry`, per `scripts/check.sh --json`. Emits exactly one `stdout_json`
object and judges nothing itself (docs/ORACLES.md section 7) — the
derived spec's `then` predicates own the verdict
(contracts/specs/derived-aln-91b.spec.json).

Usage: check_theorem_sorry_free.py THEOREM_NAME

Runs the real `scripts/check.sh --json THEOREM_NAME` (which builds the
project with `lake build`), parses its one JSON line, and reports two
plain facts: `sorry_free`, true exactly when THEOREM_NAME is absent from
the `sorry` array check.sh reports back (the negation of check.sh's own
`theorem_in_sorry`, since the spec's `then` predicate wants the positive
"it is proved" fact rather than the negative "it is still sorry" one),
and `build_ok`, relayed straight from check.sh's own field of that name.
"""
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_theorem_sorry_free.py THEOREM_NAME", file=sys.stderr)
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
        "sorry_free": not report["theorem_in_sorry"],
        "build_ok": report["build_ok"],
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
