# Agent context

This repository is operated under **exophial doctrine**, installed by
`exophial init` into `.claude/doctrine/`. The universal, load-bearing rules
every agent working here must respect are imported inline below. Role- and
surface-specific doctrine is linked with exact paths and **must be read before
that kind of work — it is not optional.**

@.claude/doctrine/codebase.md

## Read before you work

- **Any test — writing one OR judging one:** `.claude/doctrine/testing.md`,
  `.claude/doctrine/testing-base.md`, your language surface
  (`.claude/doctrine/testing-typescript.md` or
  `.claude/doctrine/testing-python.md`), and `docs/test-validity.md`. Note: a
  file named `*stub*`/`*fixture*` in this codebase is frequently a **real
  in-process server exercising real code**, not a mock — open it before you
  characterize it.
- **Coordinating / dispatching work:** `.claude/doctrine/coordinator.md`.
- **Executing a scoped task as a worker:** `.claude/doctrine/worker.md`.
- **Driving a stuck family to merged:** `.claude/doctrine/husband.md`.
- **Foundational behavioral norms (inherited by all of the above):**
  `.claude/doctrine/principal.md`.

When you dispatch a subagent into this repo, its task brief MUST point it at the
doctrine above: a subagent starts blank and will not read it otherwise.

## Lean work: standing rules

Every exophial-dispatched worker that edits Lean code in this repo
follows these rules.

**Setup.** Create a branch and a worktree from `integrated`. Put the
worktree under `.scratch/` in this repo. Symlink `.lake/packages` from
the main checkout. Never copy `.lake/build`.

**Lean commands.** Run every Lean command through
`/home/rix/bin/lean-run`. Run at most 4 `lean-run` commands at once. Use
absolute paths only. Put scratch files under `<worktree>/.scratch/`.

**Never run a bare `lake clean`.** Every worktree in this repo symlinks
the same `.lake/packages` directory. A bare `lake clean` run from one
worktree deletes the shared Mathlib build every other worktree depends
on (it happened on 2026-11-01: a several-GB build dropped to 166M). To
measure a clean build, delete only `<your worktree>/.lake/build`. If the
shared Mathlib build is missing, restore it with `lake exe cache get`
from the main checkout, never a source rebuild.

**Forbidden.** No `exophial` or `pb` command. No push. No change to
`integrated` by hand.

**Lean style.** The layer rule: a proof does not unfold a base
operation. Record each search: change `simp?` to `simp only`. Do not
leave a bare non-terminal `simp`. Call `omega` on a small context.
`native_decide` is forbidden.

**Commits.** Commit once per step, with a message.

**Acceptance.** Every task meets this before it is done:
`lean-run scripts/check.sh --json` gives `true` for every `_ok` field,
and the type-doctrine linter summary (`lint_ok`) and the decisionScope
findings (`decision_ok`) are no worse than `scripts/gate-baseline.json`
(`docs/lean/type-doctrine.md`, `armada-laconic`).

**Pre-merge gate-quality check.** Before a merge, run
`lean-run python3 scripts/gate_extra.py --json` on the branch's own
worktree. This runs the lint, decisionScope, and counterexample checks
alone, with no full `spec_check.py` build report needed. The
decisionScope check scans only the `ArmadaLean/**/*.lean` files whose
content differs from `scripts/gate-baseline.json`'s recorded hash.

The `gate-baseline-fresh` pre-commit hook (`.pre-commit-config.yaml`)
catches a stale hash before it reaches the decisionScope check. It
fails when a tracked `ArmadaLean/**/*.lean` file (outside
`ArmadaLean/Lint/`) has a sha256 that differs from
`scripts/gate-baseline.json`'s `file_hashes`, or is missing from it. It
only hashes files, so it runs in seconds on every commit and at the
merge-boundary gate (`stages: [pre-commit, manual]`). A merge that
changes one of these files without refreshing the hash is the common
cause: run `python3 scripts/update_gate_baseline.py --hashes-only` to
refresh `file_hashes` alone, without the full `lake build` and
decisionScope scan `scripts/update_gate_baseline.py` otherwise runs,
and commit the result.

**The gate baseline.** `scripts/gate-baseline.json` is tracked: the
type-lint summary counts, every `decisionScope` finding, and the sha256
of every `ArmadaLean/**/*.lean` file (outside `ArmadaLean/Lint/`), all
measured on `integrated`. The lint/decisionScope checks compare the
tree against this FILE, not a live `git merge-base`: exophial's gate
container ships the judged tree as a single commit with no other ref,
so it cannot run `git merge-base` against `integrated`. When a task
lowers a `gate_extra.LINT_REGRESSION_FIELDS` count or fixes a
`decisionScope` finding, run `lean-run python3
scripts/update_gate_baseline.py` and commit the updated
`scripts/gate-baseline.json` in the SAME branch. Never run it to raise
a count or add a finding without a fix: the gate refuses a raised
baseline the same way it refuses a raised count, by comparing the tree
against the committed file — so a raised baseline shows up in the
branch's own diff for review. One exception: a commit that only
corrects a linter's measure, with no change to the model code, may
raise a count. It is its own commit, and its message states the
defect and the counts before and after (coordinator decision
2026-11-02; `looseHypothesis` 122 → 228 in `af3b5938`).

**A spec theorem is finished** when `scripts/check.sh --json NAME`
prints both `theorem_in_sorry` false and `theorem_witness_open` false.
`sorry_count` counts proofs only; an open non-vacuity witness is listed
in `witness_open`. A witness in `witness_blocked` waits on a trusted
primitive (`EdDSAVerify`, `VerifyAccepts`, `VerifyOwnedAccepts`), not
on work: its theorem is finished as far as the model can go.
## Repair pass
A proved model that does not follow the strata of armada-laconic docs/process.md is brought to them by the repair pass in that file, steps R.1 to R.6, in the order R.6 gives; each operation equation is proved against its Spec statement.
