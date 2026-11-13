#!/usr/bin/env python3
"""Failure tests for `spec_check.py`'s two gate decisions (review
ship-armada/armada-lean#1, finding 3). Run with:

    python3 scripts/test_check_gate.py

No Lean process runs. Each test calls the real decision function with the exact
JSON shape `scripts/spec_report.lean` produces for a `theorem`'s `axioms` list
(confirmed against a real build on 2026-11-12: the fields read here, `name` and
`axioms`, are unchanged by that confirmation).

1. `bad_axioms` used to pass any axiom whose type was not a `Prop`, so a
   declared `axiom x : Empty` passed unconditionally (`Empty : Type`, not a
   `Prop`) and proved anything. `test_axiom_allowlist_rejects_an_unlisted_axiom`
   stands for that axiom with a name outside `ALLOWED_AXIOMS` and checks that
   `bad_axioms` now rejects it.
2. `scripts/check.sh` used to exit 0 on any spec theorem with `sorryAx` in its
   axioms. `test_sorry_gate_rejects_an_unlisted_theorem` checks that
   `unapproved_sorry` now rejects one, and
   `test_sorry_gate_accepts_a_listed_theorem` checks that a theorem with its own
   row in `scripts/approved-open.tsv` still passes.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import spec_check  # noqa: E402

FAILURES: list[str] = []


def check(name: str, condition: bool, detail: str) -> None:
    if condition:
        print(f"PASS {name}")
    else:
        FAILURES.append(name)
        print(f"FAIL {name}: {detail}")


def test_axiom_allowlist_accepts_the_six() -> None:
    """The three Lean core axioms and the model's three declared primitives:
    the only axioms any spec theorem or witness ever needs."""
    allowed = sorted(spec_check.ALLOWED_AXIOMS) + ["sorryAx"]
    bad = spec_check.bad_axioms(allowed)
    check("axiom_allowlist_accepts_the_six", bad == [], f"bad_axioms({allowed!r}) = {bad!r}")


def test_axiom_allowlist_rejects_an_unlisted_axiom() -> None:
    """Stands for `axiom x : Empty`: a declared axiom outside `ALLOWED_AXIOMS`.
    The old rule ("passes when its type is not a Prop") let this through; the
    allowlist rejects it by name, whatever its type."""
    axioms = ["propext", "ArmadaLean.EmptyAxiom"]
    bad = spec_check.bad_axioms(axioms)
    check("axiom_allowlist_rejects_an_unlisted_axiom",
          bad == ["ArmadaLean.EmptyAxiom"], f"bad_axioms({axioms!r}) = {bad!r}")


def test_sorry_gate_rejects_an_unlisted_theorem() -> None:
    """A spec theorem with `sorryAx` and no row in `scripts/approved-open.tsv`
    fails. Before this gate, `scripts/check.sh` exited 0 on it."""
    members = [{"name": "ArmadaLean.Pool.unlisted_sorry_theorem",
                "axioms": ["propext", "sorryAx"]}]
    rejected = spec_check.unapproved_sorry(members, approved_open={})
    check("sorry_gate_rejects_an_unlisted_theorem",
          rejected == ["ArmadaLean.Pool.unlisted_sorry_theorem"], f"got {rejected!r}")


def test_sorry_gate_accepts_a_listed_theorem() -> None:
    """A spec theorem with `sorryAx` and its own row in
    `scripts/approved-open.tsv` passes."""
    name = "ArmadaLean.Pool.listed_open_theorem"
    members = [{"name": name, "axioms": [
        "propext", "Quot.sound", "sorryAx",
        "ArmadaLean.EdDSAVerify", "ArmadaLean.VerifyAccepts", "ArmadaLean.VerifyOwnedAccepts",
    ]}]
    approved = {name: {"approved": "2026-11-12", "reason": "listed"}}
    rejected = spec_check.unapproved_sorry(members, approved_open=approved)
    check("sorry_gate_accepts_a_listed_theorem", rejected == [], f"got {rejected!r}")


def test_sorry_gate_rejects_the_approved_name_on_a_different_theorem() -> None:
    """An approved-open row names one theorem, not a prefix or a pattern: a
    second theorem with `sorryAx` and no row of its own still fails."""
    members = [{"name": "ArmadaLean.Pool.apply_backward_refinement_run",
                "axioms": ["sorryAx"]},
               {"name": "ArmadaLean.Pool.apply_backward_refinement",
                "axioms": ["sorryAx"]}]
    approved = {"ArmadaLean.Pool.apply_backward_refinement_run":
                {"approved": "2026-11-12", "reason": "PE7"}}
    rejected = spec_check.unapproved_sorry(members, approved_open=approved)
    check("sorry_gate_rejects_the_approved_name_on_a_different_theorem",
          rejected == ["ArmadaLean.Pool.apply_backward_refinement"], f"got {rejected!r}")


def main() -> int:
    test_axiom_allowlist_accepts_the_six()
    test_axiom_allowlist_rejects_an_unlisted_axiom()
    test_sorry_gate_rejects_an_unlisted_theorem()
    test_sorry_gate_accepts_a_listed_theorem()
    test_sorry_gate_rejects_the_approved_name_on_a_different_theorem()
    if FAILURES:
        print(f"FAILED {len(FAILURES)}: {', '.join(FAILURES)}")
        return 1
    print("PASS all")
    return 0


if __name__ == "__main__":
    sys.exit(main())
