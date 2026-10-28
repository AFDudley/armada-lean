#!/usr/bin/env python3
"""Acceptance probe for pebble aln-46f.

Observes whether a named Lean theorem's own proof body still carries
`sorry`, per `scripts/check.sh --json`, and whether the project builds.
Emits exactly one `stdout_json` object and judges nothing itself
(docs/ORACLES.md section 7) — the derived spec's `then` predicates own
the verdict (contracts/specs/derived-aln-46f.spec.json).

Usage: no_sorry_check.py THEOREM_NAME

Runs the real `scripts/check.sh --json THEOREM_NAME` (which builds the
project with `lake build`), parses its one JSON line, and reports two
plain facts: whether THEOREM_NAME appears in the `sorry` array it names
back as `theorem_under_test` (`target_in_sorry`), and the `build_ok`
flag `check.sh` itself computed from the `lake build` exit code. This is
the member-family predicate check.sh's own header names (`{"op":
"not_member", "elem": "theorem_under_test", "collection": "sorry"}`)
flattened into a single boolean observation, because the `behavior`
oracle grammar available to this derivation restricts `then` predicates
to scalar comparisons (ge/le/gt/lt/eq/ne) and cannot express array
non-membership directly.
"""
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: no_sorry_check.py THEOREM_NAME", file=sys.stderr)
        return 2
    theorem = sys.argv[1]
    proc = subprocess.run(
        ["scripts/check.sh", "--json", theorem],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    report = json.loads(proc.stdout)
    target_in_sorry = report["theorem_under_test"] in report["sorry"]
    print(json.dumps({
        "target_in_sorry": target_in_sorry,
        "build_ok": report["build_ok"],
    }))
    return 0


if __name__ == "__main__":
    sys.exit(main())
