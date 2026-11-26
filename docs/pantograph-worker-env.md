# Pantograph worker interaction layer

Operator ruling (2026-11-26, armada-laconic `labbook/2026-11-26-pantograph-vintage-and-worker-repl.md`).

1. **Standard Lean interaction server:** Lean proof workers and step-search harnesses in `armada-lean`
   use **Pantograph** (`stanford-centaur/Pantograph`, `dev` branch, pinned at
   `6479c9bb8ce67e94b24ffba57f59633b3da9b344` for `leanprover/lean4:v4.35.0`), replacing
   `leanprover-community/repl`.
2. **Vintage constraint:** Pantograph's supported Lean version constrains `lean-toolchain` bumps.
   `armada-lean` does not advance `lean-toolchain` past Pantograph's supported Lean version, and no
   fallback REPL is maintained.
3. **Worker packaging (offline, pinned):** `armada-lean`'s Nix flake and Lean worker environment
   provide the vintage-pinned Pantograph binary built offline against `leanprover/lean4:v4.35.0` so
   proof workers can drive interactive goal states against `armada-lean`'s compiled `.olean`s with no
   runtime downloads.
4. **Gate separation:** The commit-boundary gate (`scripts/gate_no_recompile.sh && scripts/check.sh`)
   and `exophial.lean_oracle` remain batch-only. Pantograph never enters the gate or certification
   verdict path.
