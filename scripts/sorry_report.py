#!/usr/bin/env python3
"""Print one line per `theorem` whose own proof body carries a literal
`sorry`, plus a final count line.

Usage: sorry_report.py FILE.lean [FILE.lean ...]
Output: `SORRY <fully.qualified.name>` per matching theorem, sorted, then
`SORRY_COUNT <n>`. A pebble states its acceptance as a predicate over this
output, for example "the output has no line `SORRY
ArmadaLean.PoolSafety.leaf_has_merkle_witness`" (an intake-time
non-vacuity gap this closes: `exit_code eq 0` alone passes a no-op
program; this gives the derivation an observable line to name).

Reuses sigs.py's namespace-stack tracker, so a theorem declared inside two
nested `namespace` blocks gets both segments in its reported name, the
same as sigs.py's own FULLNAME column.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sigs import line_prefixes  # noqa: E402

_DECL_HEAD = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )?"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([\w.'?!]+)"
)
_SORRY = re.compile(r"(?<![\w'])sorry(?![\w'])")


def sorry_names(path: str) -> list[str]:
    lines = open(path, encoding="utf-8").read().split("\n")
    prefixes = line_prefixes(lines)
    starts = []
    for i, line in enumerate(lines):
        m = _DECL_HEAD.match(line)
        if m:
            starts.append((i, m.group(1), m.group(2)))
    out = []
    for k, (i, kind, name) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = "\n".join(lines[i:end])
        if kind == "theorem" and _SORRY.search(body):
            out.append(prefixes[i] + name)
    return out


def main() -> None:
    names: list[str] = []
    for path in sys.argv[1:]:
        names.extend(sorry_names(path))
    for n in sorted(names):
        print(f"SORRY {n}")
    print(f"SORRY_COUNT {len(names)}")


if __name__ == "__main__":
    main()
