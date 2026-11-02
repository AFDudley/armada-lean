#!/usr/bin/env python3
"""Print the size of every declaration in a Lean file.

Usage: declsizes.py FILE.lean [NAME ...]
Output: NAME<TAB>START_LINE<TAB>LINES. With NAME arguments, only those
declarations; a missing NAME prints `NAME<TAB>absent<TAB>0`.
A declaration runs from its keyword line to the line before the next
declaration keyword, so its doc comment counts toward the NEXT declaration.
"""
import re
import sys

decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )?"
                  r"(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([\w.']+)")
lines = open(sys.argv[1], encoding="utf-8").read().split("\n")
starts = [(i, m.group(2)) for i, l in enumerate(lines, 1) if (m := decl.match(l))]
sizes = {}
for k, (i, n) in enumerate(starts):
    end = starts[k + 1][0] - 1 if k + 1 < len(starts) else len(lines)
    sizes[n] = (i, end - i + 1)
names = sys.argv[2:] or [n for _, n in starts]
for n in names:
    if n in sizes:
        print(f"{n}\t{sizes[n][0]}\t{sizes[n][1]}")
    else:
        print(f"{n}\tabsent\t0")
