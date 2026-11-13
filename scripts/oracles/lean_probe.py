#!/usr/bin/env python3
"""Run one Lean probe and print what Lean reported, as one JSON object.

Usage, from the repo root: python3 scripts/oracles/lean_probe.py PROBE.lean

A probe is a Lean file that elaborates only when the property it states holds. Lean
is the decision procedure; this script decides nothing. It runs
`lake env lean PROBE.lean` and prints:

- `elaborates`: Lean exited 0.
- `error_count`: the number of error messages.
- `errors`: the first line of each error message.
- `axioms`: one entry per `#print axioms` line, in probe order, as
  `{"decl": NAME, "axioms": [AXIOM, ...]}`. It is a list, not a map, because a
  declaration name holds dots and an oracle field path splits on dots.

The exit code is Lean's exit code. `lake env lean` reads the built `.olean` files, so
build the tree first (`lake build`, which `scripts/check.sh` runs).

The pool-execution probes are in `scripts/oracles/pool_exec/`; their rules are in
`docs/pool-executable.md`.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import spec_lib  # noqa: E402

ERROR = re.compile(r"^\S+:\d+:\d+: error(?:\([^)]*\))?: (.*)$", re.MULTILINE)
DEPENDS = re.compile(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", re.MULTILINE)
NO_AXIOMS = re.compile(r"^'([^']+)' does not depend on any axioms", re.MULTILINE)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: lean_probe.py PROBE.lean", file=sys.stderr)
        return 2
    run = subprocess.run([spec_lib.LAKE, "env", "lean", sys.argv[1]],
                         capture_output=True, text=True)
    out = run.stdout + run.stderr
    errors = ERROR.findall(out)
    printed = [(m.start(), m.group(1), [a.strip() for a in m.group(2).split(",")])
               for m in DEPENDS.finditer(out)]
    printed += [(m.start(), m.group(1), []) for m in NO_AXIOMS.finditer(out)]
    print(json.dumps({
        "elaborates": run.returncode == 0,
        "error_count": len(errors),
        "errors": errors,
        "axioms": [{"decl": d, "axioms": a} for _, d, a in sorted(printed)],
    }))
    return run.returncode


if __name__ == "__main__":
    sys.exit(main())
