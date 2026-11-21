# Handoff: armada-lean

Written 2026-11-21 by session `01a1f9a0`.

## What is to be done

1. **`lint_ok` is a ratchet.** It passes when no count is higher than `scripts/gate-baseline.json`, so an equal or a
   lower count passes (`scripts/gate_extra.py:214`). Gate GRc of armada-laconic `docs/process.md` depends on it. The
   operator ruling of 2026-11-14 (`docs/repair-pass.md` §1) requires zero findings with no stored number.

## State

- `integrated` is on GitHub. `docs/repair-pass.md` §4 copies armada-laconic `docs/process.md` at `f9e9199e`.
- The strict check is parked on branch `gate/lean-port` (`f489d01`, worktree `.scratch/gate-lean`). lean-temper
  `docs/design.md` §10 lists its four defects.
- Open pebble `aln-c67` (`spec_check` reports a witness as blocked when the proof never uses the primitive's field)
  is not part of this work.
- `.exophial/cache/dry-run/e6f0a40d…` (a spec written by hand for the proof-level alias rule) and the worktree
  `.scratch/base-ab5b476` came from a session that wrote them without agreement. Nothing depends on them, and they
  can be deleted.
