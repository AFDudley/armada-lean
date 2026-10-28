#!/usr/bin/env python3
"""Acceptance probe for pebble aln-a48.

Observes whether a named Lean theorem's own proof body still carries
`sorry`, per `scripts/check.sh --json`. Emits exactly one `stdout_json`
object and judges nothing itself (docs/ORACLES.md section 7) — the
derived spec's `then` predicates own the verdict
(contracts/specs/derived-aln-a48.spec.json).

Usage: verify_owned_spend_witness_sorry_closed.py THEOREM_NAME

Runs the real `scripts/check.sh --json THEOREM_NAME` (which builds the
project with `lake build`), parses its one JSON line, and reports two
plain facts: whether THEOREM_NAME appears in the `sorry` array it names
back as `theorem_under_test` (`theorem_under_test_in_sorry`), and the
exit code `check.sh` itself returned (`check_exit_code`). This is the
member-family predicate check.sh's own header names
(`{"op": "not_member", "elem": "theorem_under_test", "collection":
"sorry"}`) flattened into a single boolean observation, because the
`behavior` oracle grammar available to this derivation restricts `then`
predicates to scalar comparisons (ge/le/gt/lt/eq/ne) and cannot express
array non-membership directly.
"""
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: verify_owned_spend_witness_sorry_closed.py THEOREM_NAME", file=sys.stderr)
        return 2
    theorem = sys.argv[1]
    proc = subprocess.run(
        ["scripts/check.sh", "--json", theorem],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    report = json.loads(proc.stdout)
    theorem_under_test_in_sorry = report["theorem_under_test"] in report["sorry"]
    print(json.dumps({
        "theorem_under_test_in_sorry": theorem_under_test_in_sorry,
        "check_exit_code": proc.returncode,
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
