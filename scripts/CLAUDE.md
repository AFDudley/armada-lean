# scripts/

The gate's acceptance check (`.exophial/config.yaml` `gate.command`:
`lake build && scripts/check.sh`) and its helpers. Design record:
`docs/spec-module-design.md`. The check stores no list of names, counts or
signatures; every set it reports is computed on each run.

- `check.sh` — the gate entry point. It runs `spec_check.py` with its arguments
  (`--json [THEOREM]` prints one JSON object).
- `spec_check.py` — the check: `lake build`, then the report. It decides spec
  membership, and prints `PASS`/`FAIL` per check, one `SORRY <name>` line per
  open spec theorem and `SORRY_COUNT <n>`.
- `spec_report.lean` — the report: run with `lake env lean scripts/spec_report.lean`.
  It reads the checked environment (axioms, spec bindings, state types,
  witnesses) and prints one JSON object.
- `spec_lib.py` — the membership rule (doc-comment citations,
  `writing-lean.md` §11), the out-of-scope and "Every state" markers, and Lean
  text helpers.
- `convert_spec.py` — the conversion to the spec-module form. It runs on any
  branch that builds; a second run changes nothing.
- `declsizes.py` — docs/lean/verification.md section 1's declaration-size
  script (`worker-briefs.md` design check D5).
- `git-hooks/` — the pre-commit hook scripts; see its own `CLAUDE.md`.
- `oracles/` — committed acceptance oracles that pebble specs run (Lean
  probes); see its own `CLAUDE.md`.
