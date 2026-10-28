#!/usr/bin/env python3
"""Print the statement of every theorem in one or more Lean files.

Usage: sigs.py FILE.lean [FILE.lean ...]
Output: FILE<TAB>FULLNAME<TAB>SIGNATURE, sorted by (FILE, FULLNAME). A
signature is the text from the `theorem` keyword to the first `:=` at
nesting depth zero, with all whitespace collapsed. FULLNAME is the
declared name with every ENCLOSING `namespace` prefix added, tracked as a
stack over `namespace NAME` / `section` / `end` lines in source order (a
file here opens and closes several nested namespaces, e.g.
`ArmadaLean.Nitro` then `Balances` then `KeysNodup`-named theorems inside
it — a single whole-file namespace guess under-qualifies those names and
`#print axioms` then reports "unknown constant"). Compare two revisions
with `diff`, or feed two directories of output to a Python dict
comparison (see check.sh).
"""
import re
import sys

_NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
_SECTION = re.compile(r"^\s*section\b")
_END = re.compile(r"^\s*end\b")
# A theorem name: word characters, dots (nested-name projection), primes,
# and `?`/`!` anywhere, not just trailing (Lean identifiers use `?`/`!`
# mid-name, e.g. `getElem?_concat_eq`; a suffix-only class truncates that
# to `getElem?` and drops `_concat_eq`).
_NAME = r"[\w.'?!]+"
_THEOREM_HEAD = re.compile(r"^theorem\s+(" + _NAME + r")", re.M)


def line_prefixes(lines: list[str]) -> list[str]:
    """One namespace prefix (already dotted, possibly empty) per source line,
    reflecting the stack of `namespace`/`section` blocks open BEFORE that
    line runs. `section` pushes a frame with no name; `end` pops whichever
    frame (named or not) is innermost."""
    stack: list[str | None] = []
    out = []
    for line in lines:
        names = [n for n in stack if n is not None]
        out.append(".".join(names) + ("." if names else ""))
        m_ns = _NAMESPACE.match(line)
        m_sec = _SECTION.match(line)
        m_end = _END.match(line)
        if m_ns:
            stack.append(m_ns.group(1))
        elif m_sec:
            stack.append(None)
        elif m_end and stack:
            stack.pop()
    return out


def sigs_of(path: str) -> list[tuple[str, str]]:
    text = open(path, encoding="utf-8").read()
    lines = text.split("\n")
    # Byte offset of the start of each line, to map a regex match position
    # back to its line's namespace prefix.
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    prefixes = line_prefixes(lines)

    def prefix_at(pos: int) -> str:
        lo, hi = 0, len(lines) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if offsets[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return prefixes[lo]

    out = []
    for m in _THEOREM_HEAD.finditer(text):
        i = m.start()
        depth = 0
        j = i
        while j < len(text):
            c = text[j]
            if c in "([{⟨":
                depth += 1
            elif c in ")]}⟩":
                depth -= 1
            elif depth == 0 and text.startswith(":=", j):
                break
            j += 1
        sig = " ".join(text[i:j].split())
        out.append((prefix_at(i) + m.group(1), sig))
    return out


def main() -> None:
    rows = []
    for path in sys.argv[1:]:
        for name, sig in sigs_of(path):
            rows.append((path, name, sig))
    for path, name, sig in sorted(rows):
        print(f"{path}\t{name}\t{sig}")


if __name__ == "__main__":
    main()
