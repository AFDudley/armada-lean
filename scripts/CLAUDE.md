# scripts/

The gate's acceptance check (`.exophial/config.yaml` `gate.command`:
`lake build && scripts/check.sh`) and its helpers.

- `check.sh` — docs/lean/verification.md section 1, moved into the tracked
  tree and adapted for the whole `ArmadaLean` directory. Builds, checks the
  sorry count against a ceiling, checks every theorem's axioms, checks every
  approved theorem's statement text against `sigs-baseline.tsv`, and checks
  the Nitro non-vacuity witness module carries no sorry
  (docs/lean/verification.md section 5a).
- `sigs.py` — prints `FILE<TAB>FULLNAME<TAB>SIGNATURE` for every `theorem` in
  one or more Lean files. Tracks a namespace stack over nested
  `namespace`/`section` blocks, so a theorem declared inside two nested
  namespaces gets both segments in its `FULLNAME`.
- `declsizes.py` — docs/lean/verification.md section 1's declaration-size
  script (`worker-briefs.md` design check D5).
- `sigs-baseline.tsv` — a frozen `sigs.py` snapshot of every theorem in
  `ArmadaLean/` at this commit. `check.sh` compares against this COMMITTED
  file, never `git show`: the gate container's tree carries no `.git`
  (REPO_INIT.md), so a git-based baseline compare is unreachable there and
  silently passes every statement. Re-generate it (operator/coordinator
  only, when a new tag ratifies a changed approved statement):
  `python3 scripts/sigs.py $(find ArmadaLean -name '*.lean' | sort) > scripts/sigs-baseline.tsv`.
- `git-hooks/` — `exophial init`-installed pre-commit hook scripts; see its
  own `CLAUDE.md`.
