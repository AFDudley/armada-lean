# Handoff: armada-lean

Written 2026-11-21 by session `01a1f9a0`.

## What is to be done

1. **Qualify every use of "gate".** A gate is one check that runs; a decision that a person or an agent makes is a
   judgment, not a gate; "gate" is not a verb (`glossary.md`, "Gate" and "Judgment"). Uses at `integrated`
   `810600a1`: `docs/repair-pass.md` 4, `scripts/spec_check.py` 6 (for example "gated by"), `scripts/gate_extra.py`
   12. `docs/repair-pass.md` also still copies the old GATE of armada-laconic `docs/process.md`. That text changed in
   armada-laconic `f9e9199e`: lean-temper does the repair pass, and the gates of a merge are GRa, GRb and GRc.
2. **`lint_ok` is a ratchet.** It passes when no count is higher than `scripts/gate-baseline.json`, so an equal or a
   lower count passes (`scripts/gate_extra.py:214`). Gate GRc of armada-laconic `docs/process.md` depends on it. The
   goal of the lean-temper work is zero findings with no ratchet.

## State

- `integrated` is `810600a1`, on GitHub.
- The strict check is parked on branch `gate/lean-port` (`f489d01`, worktree `.scratch/gate-lean`). lean-temper
  `docs/design.md` §10 lists its four defects.
- Open pebble `aln-c67` (`spec_check` reports a witness as blocked when the proof never uses the primitive's field)
  is not part of this work.
- `.exophial/cache/dry-run/e6f0a40d…` (a spec written by hand for the proof-level alias rule) and the worktree
  `.scratch/base-ab5b476` came from a session that wrote them without agreement. Nothing depends on them, and they
  can be deleted.
