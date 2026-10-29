#!/usr/bin/env python3
"""Reachability gate: every approved theorem over a system state names its state domain.

Usage: reach.py SIGS_BASELINE SIGS_NOW REGISTRY EXEMPT
  SIGS_BASELINE  scripts/sigs-baseline.tsv (FILE<TAB>NAME<TAB>SIGNATURE): the approved theorem types.
  SIGS_NOW       sigs.py output for the current tree.
  REGISTRY       the stdout of `lake env lean ArmadaLean/Machines.lean` (MACHINE lines): the
                 machine registry (`ArmadaLean/Machines.lean`'s own doc comment explains why this
                 script reads a SCAN, not a list written into this file).
  EXEMPT         scripts/reach-exempt.tsv (NAME<TAB>REASON): theorems that hold for every state of
                 their machine, by review.

A system state type is the `S` of one `MACHINE name : S` line of REGISTRY, read down to its first
two whitespace-separated tokens (`PoolState`, `Adjudicator E`, `NetworkState E`, `Network E` as of
this writing): a state type built from a type parameter (`Adjudicator E`) is named that way in
every theorem that uses it, so two tokens is enough to recognize an occurrence without matching an
unrelated bound variable name the registry scan's own telescope happened to pick. This script does
not hard-code that list: a `Machine` declared over a new state type changes REGISTRY on the next
`lake env lean` run, and this script's scope grows with it with no edit here.

A theorem is in scope when it is in the baseline, its file is not ArmadaLean/Nitro/NonVacuity.lean
(witnesses are not claims), and its current signature names a system state type. An in-scope
theorem passes when its signature names a reachability predicate (an identifier that starts with
`Reachable`, covering `Machine.Reachable`, `.Reachable`, bare `Reachable`, and `ReachableSigned`)
or when EXEMPT lists it with a reason. An EXEMPT row whose theorem is out of scope, takes a
reachability predicate, or does not exist fails too, so the list cannot go stale.

Operator ruling 2026-10-29 (armada-laconic labbook/2026-10-29-nitro-reachability-ruling.md):
reachability is decided when a theorem is typed, not after it is proved. Exit 0 on pass, 1 on any
failure; failures go to stderr.
"""
import re
import sys

MACHINE_LINE = re.compile(r"^MACHINE\s+\S+\s*:\s*(.+)$")
REACH = re.compile(r"\bReachable\w*")
WITNESS_FILE = "ArmadaLean/Nitro/NonVacuity.lean"


def read_tsv(path: str, columns: int) -> list[list[str]]:
    rows = []
    for line in open(path, encoding="utf-8"):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != columns:
            raise SystemExit(f"{path}: expected {columns} tab-separated columns: {line!r}")
        rows.append(parts)
    return rows


def state_patterns(registry_path: str) -> list[re.Pattern]:
    """One compiled pattern per machine's state type, from REGISTRY's `MACHINE` lines."""
    patterns = []
    seen = set()
    for line in open(registry_path, encoding="utf-8"):
        m = MACHINE_LINE.match(line.rstrip("\n"))
        if not m:
            continue
        tokens = m.group(1).split()
        if not tokens:
            raise SystemExit(f"{registry_path}: empty state type: {line!r}")
        head = " ".join(tokens[:2]) if len(tokens) > 1 else tokens[0]
        if head in seen:
            continue
        seen.add(head)
        patterns.append(re.compile(r"\b" + re.escape(head) + r"\b"))
    if not patterns:
        raise SystemExit(f"{registry_path}: no MACHINE lines found; is ArmadaLean/Machines.lean "
                          "broken?")
    return patterns


def main() -> int:
    baseline_path, now_path, registry_path, exempt_path = sys.argv[1:5]
    state_res = state_patterns(registry_path)
    approved = {name for file, name, _ in read_tsv(baseline_path, 3) if file != WITNESS_FILE}
    now = {name: sig for _, name, sig in read_tsv(now_path, 3)}
    exempt = {}
    for name, reason in read_tsv(exempt_path, 2):
        if not reason.strip():
            raise SystemExit(f"{exempt_path}: {name} has no reason")
        exempt[name] = reason

    def names_state(sig: str) -> bool:
        return any(p.search(sig) for p in state_res)

    in_scope = {n for n in approved if n in now and names_state(now[n])}
    failures = []
    for name in sorted(in_scope):
        if REACH.search(now[name]) is None and name not in exempt:
            failures.append(f"no state domain: {name} names a system state but takes no Reachable* "
                             f"hypothesis and is not in {exempt_path}")
    for name in sorted(exempt):
        if name not in now:
            failures.append(f"stale exemption: {name} is not a theorem in the tree")
        elif name not in in_scope:
            failures.append(f"stale exemption: {name} is not an approved theorem over a system "
                             "state")
        elif REACH.search(now[name]):
            failures.append(f"stale exemption: {name} takes a Reachable* hypothesis")
    for line in failures:
        print(f"FAIL reach {line}", file=sys.stderr)
    print(f"reach: {len(in_scope)} in scope, {len(exempt)} exempt, {len(failures)} failures",
          file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
